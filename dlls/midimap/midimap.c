/*
 * Wine MIDI mapper driver
 *
 * Copyright 	1999, 2000, 2001 Eric Pouech
 * Copyright    2024 Junyu Long
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301, USA
 *
 * TODO:
 *	notification has to be implemented
 *	IDF file loading
 */

#include <stdarg.h>
#include <string.h>
#include <stdlib.h>
#include "windef.h"
#include "winbase.h"
#include "wingdi.h"
#include "winuser.h"
#include "mmddk.h"
#include "winreg.h"
#include "wine/debug.h"
#include "winsock2.h"

#define SERVER_PORT 7941
#define CLIENT_PORT 7942
#define CLIENT_IP "127.0.0.1"
#define BUFFER_SIZE 9

#define REQUEST_CODE_MIDI_SHORT 1
#define REQUEST_CODE_MIDI_LONG 2
#define REQUEST_CODE_MIDI_PREPARE 3
#define REQUEST_CODE_MIDI_UNPREPARE 4
#define REQUEST_CODE_MIDI_OPEN 5
#define REQUEST_CODE_MIDI_CLOSE 6
#define REQUEST_CODE_MIDI_RESET 7

static struct sockaddr_in* client_addr = NULL;
static SOCKET server_sock = INVALID_SOCKET;
static BOOL winsock_loaded = FALSE;
static BYTE* send_buffer;

static void close_server_socket(void);
static BOOL create_server_socket(void);
static void request_midi_data(char*);
static void request_midi_short(DWORD_PTR);
static void request_midi_long(LPMIDIHDR);
static void request_midi_prepare();
static void request_midi_unprepare();
static void request_midi_open();
static void request_midi_close();
static void request_midi_reset();

/*
 * Here's how Windows stores the midiOut mapping information.
 *
 * Windows XP form (in HKU) is:
 *
 * [Software\\Microsoft\\Windows\\CurrentVersion\\Multimedia\\MIDIMap]
 * "szPname"="TiMidity port 0"
 * (incomplete)
 *
 * szPname:             name of midiOut device to use.
 *
 * If szPname isn't defined, we use Windows 2000 form (also in HKU):
 *
 * [Software\\Microsoft\\Windows\\CurrentVersion\\Multimedia\\MIDIMap] 988836060
 * "AutoScheme"=dword:00000000
 * "ConfigureCount"=dword:00000004
 * "CurrentInstrument"="Wine OSS midi"
 * "CurrentScheme"="epp"
 * "DriverList"=""
 * "UseScheme"=dword:00000000
 *
 * AutoScheme: 		?
 * CurrentInstrument: 	name of midiOut device to use when UseScheme is 0. Wine uses an extension
 *			of the form #n to link to n'th midiOut device of the system
 * CurrentScheme:	when UseScheme is non null, it's the scheme to use (see below)
 * DriverList:		?
 * UseScheme:		trigger for simple/complex mapping
 *
 * A scheme is defined (in HKLM) as:
 *
 * [System\\CurrentControlSet\\Control\\MediaProperties\\PrivateProperties\\Midi\\Schemes\\<nameScheme>]
 * <nameScheme>:	one key for each defined scheme (system wide)
 * under each one of these <nameScheme> keys, there's:
 * [...\\<nameScheme>\\<idxDevice>]
 * "Channels"="<bitMask>"
 * (the default value of this key also refers to the name of the device).
 *
 * this defines, for each midiOut device (identified by its index in <idxDevice>), which
 * channels have to be mapped onto it. The <bitMask> defines the channels (from 0 to 15)
 * will be mapped (mapping occurs for channel <ch> if bit <ch> is set in <bitMask>
 *
 * Further mapping information can also be defined in:
 * [System\\CurrentControlSet\\Control\\MediaProperties\\PrivateProperties\\Midi\\Ports\\<nameDevice>\\Instruments\\<idx>]
 * "Definition"="<.idf file>"
 * "FriendlyName"="#for .idx file#"
 * "Port"="<idxPort>"
 *
 * This last part isn't implemented (.idf file support).
 */

WINE_DEFAULT_DEBUG_CHANNEL(midi);
WINE_DECLARE_DEBUG_CHANNEL(winediag);

typedef struct tagMIDIOUTPORT
{
    WCHAR		name[MAXPNAMELEN];
    int			loaded;
    HMIDIOUT		hMidi;
    unsigned short	uDevID;
    LPBYTE		lpbPatch;
    unsigned int	aChn[16];
} MIDIOUTPORT;

typedef	struct tagMIDIMAPDATA
{
    struct tagMIDIMAPDATA*	self;
    MIDIOUTPORT*	ChannelMap[16];
    MIDIOPENDESC	midiDesc;
    BYTE		runningStatus;
    WORD		wCbFlags;
} MIDIMAPDATA;

static	MIDIOUTPORT*	midiOutPorts;
static  unsigned	numMidiOutPorts;

static	BOOL	MIDIMAP_IsBadData(MIDIMAPDATA* mm)
{
    if (!IsBadReadPtr(mm, sizeof(MIDIMAPDATA)) && mm->self == mm)
	return FALSE;
    TRACE("Bad midimap data (%p)\n", mm);
    return TRUE;
}

static BOOL	MIDIMAP_FindPort(const WCHAR* name, unsigned* dev)
{
    for (*dev = 0; *dev < numMidiOutPorts; (*dev)++)
    {
	TRACE("%s\n", wine_dbgstr_w(midiOutPorts[*dev].name));
	if (lstrcmpW(midiOutPorts[*dev].name, name) == 0)
	    return TRUE;
    }
    /* try the form #nnn */
    if (*name == '#' && name[1] >= '0' && name[1] <= '9')
    {
        const WCHAR*  ptr = name + 1;
        *dev = 0;
        do 
        {
            *dev = *dev * 10 + *ptr - '0';
            ptr++;
        } while (*ptr >= '0' && *ptr <= '9');
	if (*dev < numMidiOutPorts)
	    return TRUE;
    }
    return FALSE;
}

static BOOL	MIDIMAP_LoadSettingsDefault(MIDIMAPDATA* mom, const WCHAR* port)
{
    unsigned i, dev = 0;

    if (port != NULL && !MIDIMAP_FindPort(port, &dev))
    {
	ERR("Registry glitch: couldn't find midi out (%s)\n", wine_dbgstr_w(port));
	dev = 0;
    }

    /* this is necessary when no midi out ports are present */
    if (dev >= numMidiOutPorts)
	return FALSE;
    /* sets default */
    for (i = 0; i < 16; i++) mom->ChannelMap[i] = &midiOutPorts[dev];

    return TRUE;
}

static BOOL	MIDIMAP_LoadSettingsScheme(MIDIMAPDATA* mom, const WCHAR* scheme)
{
    HKEY	hSchemesKey, hKey, hPortKey;
    unsigned	i, idx, dev;
    WCHAR       buffer[256], port[256];
    DWORD	type, size, mask;

    for (i = 0; i < 16; i++)	mom->ChannelMap[i] = NULL;

    if (RegOpenKeyA(HKEY_LOCAL_MACHINE,
		    "System\\CurrentControlSet\\Control\\MediaProperties\\PrivateProperties\\Midi\\Schemes",
		    &hSchemesKey))
    {
	return FALSE;
    }
    if (RegOpenKeyW(hSchemesKey, scheme, &hKey))
    {
	RegCloseKey(hSchemesKey);
	return FALSE;
    }

    for (idx = 0; !RegEnumKeyW(hKey, idx, buffer, ARRAY_SIZE(buffer)); idx++)
    {
	if (RegOpenKeyW(hKey, buffer, &hPortKey)) continue;

	size = sizeof(port);
	if (RegQueryValueExW(hPortKey, NULL, 0, &type, (void*)port, &size)) continue;

	if (!MIDIMAP_FindPort(port, &dev)) continue;

	size = sizeof(mask);
	if (RegQueryValueExA(hPortKey, "Channels", 0, &type, (void*)&mask, &size))
	    continue;

	for (i = 0; i < 16; i++)
	{
	    if (mask & (1 << i))
	    {
		if (mom->ChannelMap[i])
		    ERR("Quirks in registry, channel %u is mapped twice\n", i);
		mom->ChannelMap[i] = &midiOutPorts[dev];
	    }
	}
    }

    RegCloseKey(hSchemesKey);
    RegCloseKey(hKey);

    return TRUE;
}

static BOOL	MIDIMAP_LoadSettings(MIDIMAPDATA* mom)
{
    HKEY 	hKey;
    BOOL	ret;

    if (RegOpenKeyA(HKEY_CURRENT_USER,
		    "Software\\Microsoft\\Windows\\CurrentVersion\\Multimedia\\MIDIMap", &hKey))
    {
	ret = MIDIMAP_LoadSettingsDefault(mom, NULL);
    }
    else
    {
	DWORD	type, size, out;
	WCHAR	buffer[256];

	size = sizeof(buffer);
	if (!RegQueryValueExW(hKey, L"szPname", 0, &type, (void*)buffer, &size))
	{
	    ret = MIDIMAP_LoadSettingsDefault(mom, buffer);
	}
	else
	{
	    ret = 2;
	    size = sizeof(out);
	    if (!RegQueryValueExA(hKey, "UseScheme", 0, &type, (void*)&out, &size) && out)
	    {
		size = sizeof(buffer);
		if (!RegQueryValueExW(hKey, L"CurrentScheme", 0, &type, (void*)buffer, &size))
		{
		    if (!(ret = MIDIMAP_LoadSettingsScheme(mom, buffer)))
			ret = MIDIMAP_LoadSettingsDefault(mom, NULL);
		}
		else
		{
		    ERR("Wrong registry: UseScheme is active, but no CurrentScheme found\n");
		}
	    }
	    if (ret == 2)
	    {
		size = sizeof(buffer);
		if (!RegQueryValueExW(hKey, L"CurrentInstrument", 0, &type, (void*)buffer, &size) && *buffer)
		{
		    ret = MIDIMAP_LoadSettingsDefault(mom, buffer);
		}
		else
		{
		    ret = MIDIMAP_LoadSettingsDefault(mom, NULL);
		}
	    }
	}
    }
    RegCloseKey(hKey);

    if (ret && TRACE_ON(midi))
    {
	unsigned	i;

	for (i = 0; i < 16; i++)
	{
	    TRACE("chnMap[%2d] => %d\n",
		  i, mom->ChannelMap[i] ? mom->ChannelMap[i]->uDevID : -1);
	}
    }
    return ret;
}

static void MIDIMAP_NotifyClient(MIDIMAPDATA* mom, WORD wMsg,
				 DWORD_PTR dwParam1, DWORD_PTR dwParam2)
{
    DriverCallback(mom->midiDesc.dwCallback, mom->wCbFlags, (HDRVR)mom->midiDesc.hMidi,
		   wMsg, mom->midiDesc.dwInstance, dwParam1, dwParam2);
}

static DWORD modOpen(DWORD_PTR *lpdwUser, LPMIDIOPENDESC lpDesc, DWORD dwFlags)
{
    MIDIMAPDATA* mom = HeapAlloc(GetProcessHeap(), 0, sizeof(MIDIMAPDATA));

    TRACE("(%p %p %08lx)\n", lpdwUser, lpDesc, dwFlags);

    if (!mom)
        return MMSYSERR_NOMEM;

    if (!lpDesc) {
	    HeapFree(GetProcessHeap(), 0, mom);
	    return MMSYSERR_INVALPARAM;
    }

    if (MIDIMAP_LoadSettings(mom)) {
	    UINT chn;
	    *lpdwUser = (DWORD_PTR)mom;
	    mom->self = mom;
	    mom->wCbFlags = HIWORD(dwFlags & CALLBACK_TYPEMASK);
	    mom->midiDesc = *lpDesc;
	    mom->runningStatus = 0;

        for (chn = 0; chn < 16; chn++) {
            if (mom->ChannelMap[chn]->loaded)
                continue;
            mom->ChannelMap[chn]->loaded = 1;
            /* FIXME: should load here the IDF midi data... and allow channel and
            * patch mappings
            */
        }

        MIDIMAP_NotifyClient(mom, MOM_OPEN, 0L, 0L);
        request_midi_open();
        return MMSYSERR_NOERROR;
    }

    HeapFree(GetProcessHeap(), 0, mom);
    return MIDIERR_INVALIDSETUP;
}

static DWORD modClose(MIDIMAPDATA* mom)
{
    UINT i;

    if (MIDIMAP_IsBadData(mom))
        return MMSYSERR_ERROR;

    for (i = 0; i < 16; i++) {
	    DWORD t;

        if (mom->ChannelMap[i] && mom->ChannelMap[i]->loaded > 0)  {
                mom->ChannelMap[i]->loaded = 0;
                mom->ChannelMap[i]->hMidi = 0;
        }
    }

    MIDIMAP_NotifyClient(mom, MOM_CLOSE, 0L, 0L);
    HeapFree(GetProcessHeap(), 0, mom);
    request_midi_close();
    return MMSYSERR_NOERROR;
}

static DWORD modLongData(MIDIMAPDATA* mom, LPMIDIHDR lpMidiHdr, DWORD_PTR dwParam2)
{
    WORD chn;
    DWORD ret = MMSYSERR_NOERROR;
    MIDIHDR	mh;

    if (MIDIMAP_IsBadData(mom))
	    return MMSYSERR_ERROR;

    if (!(lpMidiHdr->dwFlags & MHDR_PREPARED))
	    return MIDIERR_UNPREPARED;

    if (lpMidiHdr->dwFlags & MHDR_INQUEUE)
	    return MIDIERR_STILLPLAYING;

    mh = *lpMidiHdr;
    lpMidiHdr->dwFlags &= ~MHDR_DONE;
    lpMidiHdr->dwFlags |= MHDR_INQUEUE;

    request_midi_long(lpMidiHdr);

    mom->runningStatus = 0;
    lpMidiHdr->dwFlags &= ~MHDR_INQUEUE;
    lpMidiHdr->dwFlags |= MHDR_DONE;

    MIDIMAP_NotifyClient(mom, MOM_DONE, (DWORD_PTR)lpMidiHdr, 0L);
    return ret;
}

static DWORD modData(MIDIMAPDATA* mom, DWORD_PTR dwParam)
{
    BYTE status = LOBYTE(LOWORD(dwParam));
    WORD chn;

    if (MIDIMAP_IsBadData(mom))
	    return MMSYSERR_ERROR;

    if (status < 0x80) {
        if (mom->runningStatus) {
            status = mom->runningStatus;
            dwParam = ((LOWORD(dwParam) << 8) | status);
        } else {
            FIXME("ooch %Ix\n", dwParam);
            return MMSYSERR_NOERROR;
        }
    }
    chn = status & 0x0F;

    if (!mom->ChannelMap[chn])
        return MMSYSERR_NOERROR;

    switch (status & 0xF0) {
        case 0x80:
        case 0x90:
        case 0xA0:
        case 0xB0:
        case 0xC0:
        case 0xD0:
        case 0xE0:
            if (mom->ChannelMap[chn]->loaded > 0)
            {
                /* change channel */
                dwParam &= ~0x0F;
                dwParam |= mom->ChannelMap[chn]->aChn[chn];

                if ((LOBYTE(LOWORD(dwParam)) & 0xF0) == 0xC0 /* program change */ &&
                mom->ChannelMap[chn]->lpbPatch) {
                    BYTE patch = HIBYTE(LOWORD(dwParam));

                    /* change patch */
                    dwParam &= ~0x0000FF00;
                    dwParam |= mom->ChannelMap[chn]->lpbPatch[patch];
                }
                request_midi_short(dwParam);
            }
            mom->runningStatus = status;
            break;
        case 0xF0:
            request_midi_short(dwParam);
            /* system common message */
            if (status <= 0xF7)
                mom->runningStatus = 0;
            break;
        default:
            FIXME("ooch %Ix\n", dwParam);
    }

    return MMSYSERR_NOERROR;
}

static DWORD modPrepare(MIDIMAPDATA* mom, LPMIDIHDR lpMidiHdr, DWORD_PTR dwSize)
{
    if (MIDIMAP_IsBadData(mom))
        return MMSYSERR_ERROR;

    if (dwSize < offsetof(MIDIHDR,dwOffset) || lpMidiHdr == 0 || lpMidiHdr->lpData == 0)
	    return MMSYSERR_INVALPARAM;

    request_midi_prepare();

    if (lpMidiHdr->dwFlags & MHDR_PREPARED)
        return MMSYSERR_NOERROR;

    lpMidiHdr->dwFlags |= MHDR_PREPARED;
    lpMidiHdr->dwFlags &= ~(MHDR_DONE|MHDR_INQUEUE); /* flags cleared since w2k */
    
    return MMSYSERR_NOERROR;
}

static DWORD modUnprepare(MIDIMAPDATA* mom, LPMIDIHDR lpMidiHdr, DWORD_PTR dwSize)
{
    if (MIDIMAP_IsBadData(mom))
        return MMSYSERR_ERROR;

    if (dwSize < offsetof(MIDIHDR,dwOffset) || lpMidiHdr == 0 || lpMidiHdr->lpData == 0)
	    return MMSYSERR_INVALPARAM;

    request_midi_unprepare();

    if (!(lpMidiHdr->dwFlags & MHDR_PREPARED))
	    return MMSYSERR_NOERROR;

    if (lpMidiHdr->dwFlags & MHDR_INQUEUE)
	    return MIDIERR_STILLPLAYING;

    lpMidiHdr->dwFlags &= ~MHDR_PREPARED;
    return MMSYSERR_NOERROR;
}

static DWORD modGetVolume(MIDIMAPDATA* mom, DWORD* lpdwVolume)
{
    if (!lpdwVolume) return MMSYSERR_INVALPARAM;
    *lpdwVolume = 0xFFFFFFFF; /* tests show this initial value */
    return MMSYSERR_NOERROR;
}

static DWORD modSetVolume(MIDIMAPDATA* mom, DWORD dwVolume)
{
    /* Native forwards it to some underlying device
     * GetVolume returns what was last set here. */
    FIXME("stub\n");
    return MMSYSERR_NOERROR;
}

static DWORD modGetDevCaps(UINT wDevID, MIDIMAPDATA* mom, LPMIDIOUTCAPSW lpMidiCaps, DWORD_PTR size)
{
    static const MIDIOUTCAPSW mappercaps = {
        0x00FF, 0x0001, 0x0100, /* Manufacturer and Product ID */
        L"Wine midi mapper", MOD_MAPPER, 0, 0, 0xFFFF,
        MIDICAPS_VOLUME|MIDICAPS_LRVOLUME /* Native returns volume caps of underlying device + MIDICAPS_STREAM */
    };

    if (lpMidiCaps == NULL)
        return MMSYSERR_INVALPARAM;

    if (!numMidiOutPorts)
        return MMSYSERR_BADDEVICEID;

    memcpy(lpMidiCaps, &mappercaps, min(size, sizeof(*lpMidiCaps)));
    return MMSYSERR_NOERROR;
}

static DWORD modReset(MIDIMAPDATA* mom)
{
    if (MIDIMAP_IsBadData(mom))
	    return MMSYSERR_ERROR;

    mom->runningStatus = 0;
    request_midi_reset();

    return MMSYSERR_NOERROR;
}

static BOOL create_server_socket(void)
{
    WSADATA wsa_data;
    struct sockaddr_in server_addr;
    const UINT reuse_addr = 1;
    ULONG non_blocking = 1;
    int res;

    close_server_socket();

    winsock_loaded = WSAStartup(MAKEWORD(2,2), &wsa_data) == NO_ERROR;
    if (!winsock_loaded) return FALSE;

    server_addr.sin_family = AF_INET;
    server_addr.sin_addr.s_addr = inet_addr("127.0.0.1");
    server_addr.sin_port = htons(SERVER_PORT);

    server_sock = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP);
    if (server_sock == INVALID_SOCKET) return FALSE;

    res = setsockopt(server_sock, SOL_SOCKET, SO_REUSEADDR, (const char *)&reuse_addr, sizeof(reuse_addr));
    if (res == SOCKET_ERROR) return FALSE;

    ioctlsocket(server_sock, FIONBIO, &non_blocking);

    res = bind(server_sock, (struct sockaddr*)&server_addr, sizeof(server_addr));
    if (res == SOCKET_ERROR) return FALSE;

    return TRUE;
}

static void close_server_socket(void)
{
    if (server_sock != INVALID_SOCKET)
    {
        closesocket(server_sock);
        server_sock = INVALID_SOCKET;
    }

    if (winsock_loaded)
    {
        WSACleanup();
        winsock_loaded = FALSE;
    }
}

static void request_midi_data(char* buffer) {
    if (client_addr == NULL) {
        client_addr = HeapAlloc(GetProcessHeap(), 0, sizeof(struct sockaddr_in));
        client_addr->sin_family = AF_INET;
        client_addr->sin_addr.s_addr = inet_addr(CLIENT_IP);
        client_addr->sin_port = htons(CLIENT_PORT);
    }

    sendto(server_sock, buffer, BUFFER_SIZE, 0, (struct sockaddr*)client_addr, sizeof(struct sockaddr_in));
}

static void request_midi_short(DWORD_PTR param) {
    send_buffer[0] = REQUEST_CODE_MIDI_SHORT;
    memcpy(send_buffer + 1, &param, sizeof(DWORD_PTR));
    request_midi_data(send_buffer);
}

static void request_midi_long(LPMIDIHDR param) {
    // TODO: implement long msg
    FIXME("long midi msg not supported yet!\n");
}

static void request_midi_prepare() {
    send_buffer[0] = REQUEST_CODE_MIDI_PREPARE;
    request_midi_data(send_buffer);
}

static void request_midi_unprepare() {
    send_buffer[0] = REQUEST_CODE_MIDI_UNPREPARE;
    request_midi_data(send_buffer);
}

static void request_midi_open() {
    send_buffer[0] = REQUEST_CODE_MIDI_OPEN;
    request_midi_data(send_buffer);
}

static void request_midi_close() {
    send_buffer[0] = REQUEST_CODE_MIDI_CLOSE;
    request_midi_data(send_buffer);
}

static void request_midi_reset() {
    send_buffer[0] = REQUEST_CODE_MIDI_RESET;
    request_midi_data(send_buffer);
}

static LRESULT MIDIMAP_drvOpen(void);
static LRESULT MIDIMAP_drvClose(void);

/**************************************************************************
 * 				modMessage (MIDIMAP.@)
 */
DWORD WINAPI MIDIMAP_modMessage(UINT wDevID, UINT wMsg, DWORD_PTR dwUser,
				DWORD_PTR dwParam1, DWORD_PTR dwParam2)
{
    TRACE("(%u, %04X, %08IX, %08IX, %08IX);\n",
	  wDevID, wMsg, dwUser, dwParam1, dwParam2);

    switch (wMsg)
    {
    case DRVM_INIT:
        return MIDIMAP_drvOpen();
    case DRVM_EXIT:
        return MIDIMAP_drvClose();
    case DRVM_ENABLE:
    case DRVM_DISABLE:
	/* FIXME: Pretend this is supported */
	return 0;

    case MODM_OPEN:
        return modOpen((DWORD_PTR *)dwUser, (LPMIDIOPENDESC)dwParam1, dwParam2);
    case MODM_CLOSE:
        return modClose((MIDIMAPDATA*)dwUser);
    case MODM_DATA:
        return modData((MIDIMAPDATA*)dwUser, dwParam1);
    case MODM_LONGDATA:
        return modLongData((MIDIMAPDATA*)dwUser, (LPMIDIHDR)dwParam1, dwParam2);
    case MODM_PREPARE:
        return modPrepare((MIDIMAPDATA*)dwUser, (LPMIDIHDR)dwParam1, dwParam2);
    case MODM_UNPREPARE:
        return modUnprepare((MIDIMAPDATA*)dwUser, (LPMIDIHDR)dwParam1, 	dwParam2);
    case MODM_RESET:
        return modReset((MIDIMAPDATA*)dwUser);
    case MODM_GETDEVCAPS:
        return modGetDevCaps(wDevID, (MIDIMAPDATA*)dwUser, (LPMIDIOUTCAPSW)dwParam1,dwParam2);
    case MODM_GETNUMDEVS:
        return 1;
    case MODM_GETVOLUME:
        return modGetVolume	((MIDIMAPDATA*)dwUser, (DWORD*)dwParam1);
    case MODM_SETVOLUME:
        return modSetVolume	((MIDIMAPDATA*)dwUser, dwParam1);
    default:
	    FIXME("unknown message %d!\n", wMsg);
    }
    return MMSYSERR_NOTSUPPORTED;
}

/*======================================================================*
 *                  Driver part                                         *
 *======================================================================*/

/**************************************************************************
 * 				MIDIMAP_drvOpen			[internal]
 */
static LRESULT MIDIMAP_drvOpen(void)
{
    MIDIOUTCAPSW moc;
    unsigned dev, i;
    BOOL found_valid_port = FALSE;

    if (midiOutPorts)
	    return 0;

    // we create a fake midi out port here.
    numMidiOutPorts = 1;
    midiOutPorts = HeapAlloc(GetProcessHeap(), 0,
			     numMidiOutPorts * sizeof(MIDIOUTPORT));

    MIDIOUTPORT* winlatorMidiOutPort = midiOutPorts;
    lstrcpyW(winlatorMidiOutPort->name, L"Midi Through Winlator");
    winlatorMidiOutPort->loaded = 0;
    winlatorMidiOutPort->hMidi = 0;
    winlatorMidiOutPort->uDevID = 0;
    winlatorMidiOutPort->lpbPatch = NULL;
    for (i = 0; i < 16; i++)
		winlatorMidiOutPort->aChn[i] = i;
    found_valid_port = TRUE;

    // start socket server
    create_server_socket();
    send_buffer = HeapAlloc(GetProcessHeap(), 0, BUFFER_SIZE * sizeof(BYTE));
    return 1;
}

/**************************************************************************
 * 				MIDIMAP_drvClose		[internal]
 */
static LRESULT MIDIMAP_drvClose(void)
{
    if (midiOutPorts) {
	    HeapFree(GetProcessHeap(), 0, midiOutPorts);
	    midiOutPorts = NULL;
	    return 1;
    }

    // close socket server
    close_server_socket();
    HeapFree(GetProcessHeap(), 0, client_addr);
    HeapFree(GetProcessHeap(), 0, send_buffer);
    return 0;
}

/**************************************************************************
 * 				DriverProc (MIDIMAP.@)
 */
LRESULT CALLBACK MIDIMAP_DriverProc(DWORD_PTR dwDevID, HDRVR hDriv, UINT wMsg,
                                    LPARAM dwParam1, LPARAM dwParam2)
{
    TRACE("(%08lX, %04X, %08lX, %08lX, %08lX)\n",
        dwDevID, hDriv, wMsg, dwParam1, dwParam2);

    switch (wMsg)
    {
    case DRV_LOAD:		return 1;
    case DRV_FREE:		return 1;
    case DRV_OPEN:		return 1;
    case DRV_CLOSE:		return 1;
    case DRV_ENABLE:		return 1;
    case DRV_DISABLE:		return 1;
    case DRV_QUERYCONFIGURE:	return 1;
    case DRV_CONFIGURE:		MessageBoxA(0, "MIDIMAP MultiMedia Driver !", "OSS Driver", MB_OK);	return 1;
    case DRV_INSTALL:		return DRVCNF_RESTART;
    case DRV_REMOVE:		return DRVCNF_RESTART;
    default:
	return DefDriverProc(dwDevID, hDriv, wMsg, dwParam1, dwParam2);
    }
}
