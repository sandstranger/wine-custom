/*  DirectInput Gamepad device
 *
 * Copyright 2024 BrunoSX
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
 */

#include <stdarg.h>
#include <string.h>
#include <math.h>

#include "windef.h"
#include "winbase.h"
#include "wingdi.h"
#include "winternl.h"
#include "winuser.h"
#include "winerror.h"
#include "winreg.h"
#include "dinput.h"
#include "winsock2.h"
#include "devguid.h"
#include "hidusage.h"

#include "dinput_private.h"
#include "device_private.h"
#include "wine/debug.h"

WINE_DEFAULT_DEBUG_CHANNEL(dinput);

#define SERVER_PORT 7948
#define CLIENT_PORT 7947
#define BUFFER_SIZE 64

#define REQUEST_CODE_GET_GAMEPAD 8
#define REQUEST_CODE_GET_GAMEPAD_STATE 9
#define REQUEST_CODE_RELEASE_GAMEPAD 10

#define FLAG_DINPUT_MAPPER_STANDARD 0x01
#define FLAG_DINPUT_MAPPER_XINPUT 0x02
#define FLAG_INPUT_TYPE_XINPUT 0x04
#define FLAG_INPUT_TYPE_DINPUT 0x08

#define LAUNCH_TYPE_XINPUTONLY 0
#define LAUNCH_TYPE_DINPUTONLY 1
#define LAUNCH_TYPE_MIXED 2

#define IDX_BUTTON_A 0
#define IDX_BUTTON_B 1
#define IDX_BUTTON_X 2
#define IDX_BUTTON_Y 3
#define IDX_BUTTON_L1 4
#define IDX_BUTTON_R1 5
#define IDX_BUTTON_L2 10
#define IDX_BUTTON_R2 11
#define IDX_BUTTON_SELECT 6
#define IDX_BUTTON_START 7
#define IDX_BUTTON_L3 8
#define IDX_BUTTON_R3 9

struct gamepad_state 
{
    short buttons;
    char dpad;
    short thumb_lx;
    short thumb_ly;
    short thumb_rx;
    short thumb_ry;
    unsigned char thumb_lz;
    unsigned char thumb_rz;    
};

struct gamepad
{
    struct dinput_device base;
    struct gamepad_state state;
};

static const struct dinput_device_vtbl gamepad_vtbl;
static SOCKET server_sock = INVALID_SOCKET;
static BOOL winsock_loaded = FALSE;
static int connected_gamepad_id = 0;
static char input_type = FLAG_DINPUT_MAPPER_XINPUT;

static inline struct gamepad *impl_from_IDirectInputDevice8W( IDirectInputDevice8W *iface )
{
    return CONTAINING_RECORD( CONTAINING_RECORD( iface, struct dinput_device, IDirectInputDevice8W_iface ), struct gamepad, base );
}

static void close_server_socket( void ) 
{
    if (server_sock != INVALID_SOCKET) 
    {
        closesocket( server_sock );
        server_sock = INVALID_SOCKET;
    }
    
    if (winsock_loaded) 
    {
        WSACleanup();
        winsock_loaded = FALSE;
    }    
}

static BOOL create_server_socket( void )
{    
    WSADATA wsa_data;
    struct sockaddr_in server_addr;
    const DWORD timeout = 2000;
    const UINT reuse_addr = 1;
    int res;
    
    close_server_socket();
    
    winsock_loaded = WSAStartup( MAKEWORD(2,2), &wsa_data ) == NO_ERROR;
    if (!winsock_loaded) return FALSE;
    
    server_addr.sin_family = AF_INET;
    server_addr.sin_addr.s_addr = inet_addr( "127.0.0.1" );
    server_addr.sin_port = htons( SERVER_PORT );
    
    server_sock = socket( AF_INET, SOCK_DGRAM, IPPROTO_UDP );
    if (server_sock == INVALID_SOCKET) return FALSE;
    
    res = setsockopt( server_sock, SOL_SOCKET, SO_REUSEADDR, (const char *)&reuse_addr, sizeof(reuse_addr) );
    if (res == SOCKET_ERROR) return FALSE;    
     
    res = setsockopt( server_sock, SOL_SOCKET, SO_RCVTIMEO, (const char *)&timeout, sizeof(timeout) );
    if (res < 0) return FALSE;    

    res = bind( server_sock, (struct sockaddr*)&server_addr, sizeof(server_addr) );
    if (res == SOCKET_ERROR) return FALSE;
    
    return TRUE;
}

static BOOL get_gamepad_request( BOOL notify, char* gamepad_name ) 
{
    int res, gamepad_id;
    char buffer[BUFFER_SIZE];
    struct sockaddr_in client_addr;
    unsigned char launchType;
    
    client_addr.sin_family = AF_INET;
    client_addr.sin_addr.s_addr = inet_addr( "127.0.0.1" );
    client_addr.sin_port = htons( CLIENT_PORT );
    
    buffer[0] = REQUEST_CODE_GET_GAMEPAD;
    buffer[1] = 0;
    buffer[2] = notify ? 1 : 0;
    res = sendto( server_sock, buffer, BUFFER_SIZE, 0, (struct sockaddr*)&client_addr, sizeof(client_addr) );
    if (res == SOCKET_ERROR) return FALSE;
    
    res = recvfrom( server_sock, buffer, BUFFER_SIZE, 0, NULL, 0 );
    if (res == SOCKET_ERROR || buffer[0] != REQUEST_CODE_GET_GAMEPAD) return FALSE;
    
    gamepad_id = *(int*)(buffer + 1);
    if (gamepad_id == 0) 
    {
        connected_gamepad_id = 0;
        return FALSE;
    }
    
    connected_gamepad_id = gamepad_id;
    input_type = buffer[5];
    if (!(input_type & FLAG_INPUT_TYPE_DINPUT)) {
        gamepad_id = 0;
        return FALSE;
    }
    
    if (gamepad_name != NULL) 
    {
        int name_len;
        name_len = *(int*)(buffer + 6);
        memcpy( gamepad_name, buffer + 10, name_len );
        gamepad_name[name_len] = '\0';
    }
    
    return TRUE;
}

static LONG scale_value( LONG value, struct object_properties *properties )
{
    LONG log_min, log_max, phy_min, phy_max;
    log_min = properties->logical_min;
    log_max = properties->logical_max;
    phy_min = properties->range_min;
    phy_max = properties->range_max;

    return phy_min + MulDiv( value - log_min, phy_max - phy_min, log_max - log_min );
}

static LONG scale_axis_value( LONG value, struct object_properties *properties )
{
    LONG log_ctr, log_min, log_max, phy_ctr, phy_min, phy_max;
    log_min = properties->logical_min;
    log_max = properties->logical_max;
    phy_min = properties->range_min;
    phy_max = properties->range_max;

    if (phy_min == 0) phy_ctr = phy_max >> 1;
    else phy_ctr = round( (phy_min + phy_max) / 2.0 );
    if (log_min == 0) log_ctr = log_max >> 1;
    else log_ctr = round( (log_min + log_max) / 2.0 );

    value -= log_ctr;
    if (value <= 0)
    {
        log_max = MulDiv( log_min - log_ctr, properties->deadzone, 10000 );
        log_min = MulDiv( log_min - log_ctr, properties->saturation, 10000 );
        phy_max = phy_ctr;
    }
    else
    {
        log_min = MulDiv( log_max - log_ctr, properties->deadzone, 10000 );
        log_max = MulDiv( log_max - log_ctr, properties->saturation, 10000 );
        phy_min = phy_ctr;
    }

    if (value <= log_min) return phy_min;
    if (value >= log_max) return phy_max;
    return phy_min + MulDiv( value - log_min, phy_max - phy_min, log_max - log_min );
}

static void gamepad_handle_input( IDirectInputDevice8W *iface, short thumb_lx, short thumb_ly, short thumb_rx, short thumb_ry, unsigned char thumb_lz, unsigned char thumb_rz, short buttons, char dpad ) 
{
    int i, j, index;
    DWORD time, seq;
    BOOL notify = FALSE;
    struct gamepad *impl = impl_from_IDirectInputDevice8W( iface );
    DIJOYSTATE *state = (DIJOYSTATE *)impl->base.device_state;
    
    time = GetCurrentTime();
    seq = impl->base.dinput->evsequence++;    
    
    if (input_type & FLAG_DINPUT_MAPPER_STANDARD) 
    {
        if (thumb_lx != impl->state.thumb_lx)
        {
            impl->state.thumb_lx = thumb_lx;
            index = dinput_device_object_index_from_id( iface, DIDFT_ABSAXIS | DIDFT_MAKEINSTANCE( 0 ) );
            state->lX = scale_axis_value( thumb_lx, impl->base.object_properties + index );
            queue_event( iface, index, state->lX, time, seq );
            notify = TRUE;
        }
        
        if (thumb_ly != impl->state.thumb_ly) 
        {
            impl->state.thumb_ly = thumb_ly;
            index = dinput_device_object_index_from_id( iface, DIDFT_ABSAXIS | DIDFT_MAKEINSTANCE( 1 ) );
            state->lY = scale_axis_value( thumb_ly, impl->base.object_properties + index );        
            queue_event( iface, index, state->lY, time, seq );
            notify = TRUE;
        }
        
        if (thumb_rx != impl->state.thumb_rx) 
        {
            impl->state.thumb_rx = thumb_rx;
            index = dinput_device_object_index_from_id( iface, DIDFT_ABSAXIS | DIDFT_MAKEINSTANCE( 2 ) );
            state->lZ = scale_axis_value( thumb_rx, impl->base.object_properties + index );
            queue_event( iface, index, state->lZ, time, seq );
            notify = TRUE;
        }
        
        if (thumb_ry != impl->state.thumb_ry) 
        {
            impl->state.thumb_ry = thumb_ry;
            index = dinput_device_object_index_from_id( iface, DIDFT_ABSAXIS | DIDFT_MAKEINSTANCE( 3 ) );
            state->lRz = scale_axis_value( thumb_ry, impl->base.object_properties + index );
            queue_event( iface, index, state->lRz, time, seq );
            notify = TRUE;
        }
        
        if (buttons != impl->state.buttons) 
        {
            impl->state.buttons = buttons;
            for (i = 0, j = 0; i < 12; i++)
            {
                switch (i)
                {
                case IDX_BUTTON_A: j = 1; break;
                case IDX_BUTTON_B: j = 2; break;
                case IDX_BUTTON_X: j = 0; break;
                case IDX_BUTTON_Y: j = 3; break;
                case IDX_BUTTON_L1: j = 4; break;
                case IDX_BUTTON_R1: j = 5; break;
                case IDX_BUTTON_L2: j = 6; break;
                case IDX_BUTTON_R2: j = 7; break;
                case IDX_BUTTON_SELECT: j = 8; break;
                case IDX_BUTTON_START: j = 9; break;
                case IDX_BUTTON_L3: j = 10; break;
                case IDX_BUTTON_R3: j = 11; break;                
                }
                
                state->rgbButtons[j] = (buttons & (1<<i)) ? 0x80 : 0x00;
                index = dinput_device_object_index_from_id( iface, DIDFT_BUTTON | DIDFT_MAKEINSTANCE( j ) );
                queue_event( iface, index, state->rgbButtons[j], time, seq );    
            }
            notify = TRUE;        
        }
        
        if (dpad != impl->state.dpad) 
        {
            impl->state.dpad = dpad;
            index = dinput_device_object_index_from_id( iface, DIDFT_POV | DIDFT_MAKEINSTANCE( 0 ) );
            state->rgdwPOV[0] = dpad != -1 ? dpad * 4500 : -1;
            queue_event( iface, index, state->rgdwPOV[0], time, seq );
            notify = TRUE;
        }        
    }
    else if (input_type & FLAG_DINPUT_MAPPER_XINPUT) 
    {
        if (thumb_lx != impl->state.thumb_lx) 
        {
            impl->state.thumb_lx = thumb_lx;
            index = dinput_device_object_index_from_id( iface, DIDFT_ABSAXIS | DIDFT_MAKEINSTANCE( 0 ) );
            state->lX = scale_axis_value( thumb_lx, impl->base.object_properties + index );
            queue_event( iface, index, state->lX, time, seq );
            notify = TRUE;
        }
        
        if (thumb_ly != impl->state.thumb_ly) 
        {
            impl->state.thumb_ly = thumb_ly;
            index = dinput_device_object_index_from_id( iface, DIDFT_ABSAXIS | DIDFT_MAKEINSTANCE( 1 ) );
            state->lY = scale_axis_value( thumb_ly, impl->base.object_properties + index );        
            queue_event( iface, index, state->lY, time, seq );
            notify = TRUE;
        }
        
        if (thumb_rx != impl->state.thumb_rx) 
        {
            impl->state.thumb_rx = thumb_rx;
            index = dinput_device_object_index_from_id( iface, DIDFT_ABSAXIS | DIDFT_MAKEINSTANCE( 3 ) );
            state->lRx = scale_axis_value( thumb_rx, impl->base.object_properties + index );
            queue_event( iface, index, state->lRx, time, seq );
            notify = TRUE;
        }
        
        if (thumb_ry != impl->state.thumb_ry) 
        {
            impl->state.thumb_ry = thumb_ry;
            index = dinput_device_object_index_from_id( iface, DIDFT_ABSAXIS | DIDFT_MAKEINSTANCE( 4 ) );
            state->lRy = scale_axis_value( thumb_ry, impl->base.object_properties + index );
            queue_event( iface, index, state->lRy, time, seq );
            notify = TRUE;
        }
        
        if (thumb_lz != impl->state.thumb_lz || thumb_rz != impl->state.thumb_rz)
        {
            LONG value;
            index = dinput_device_object_index_from_id( iface, DIDFT_ABSAXIS | DIDFT_MAKEINSTANCE( 2 ) );

            // if lz and rz changed at the same time, only deal with lz.
            if (thumb_lz != impl->state.thumb_lz)
                value = MulDiv(thumb_lz, -32768, 255);
            else
                value = MulDiv(thumb_rz, 32767, 255);
            state->lZ = scale_axis_value( value, impl->base.object_properties + index );
            queue_event( iface, index, state->lZ, time, seq );

            impl->state.thumb_lz = thumb_lz;
            impl->state.thumb_rz = thumb_rz;
            notify = TRUE;
        }
        
        if (buttons != impl->state.buttons) 
        {
            impl->state.buttons = buttons;
            for (i = 0; i < 10; i++)
            {
                state->rgbButtons[i] = (buttons & (1<<i)) ? 0x80 : 0x00;
                index = dinput_device_object_index_from_id( iface, DIDFT_BUTTON | DIDFT_MAKEINSTANCE( i ) );
                queue_event( iface, index, state->rgbButtons[i], time, seq );    
            }
            notify = TRUE;        
        }
        
        if (dpad != impl->state.dpad) 
        {
            impl->state.dpad = dpad;
            index = dinput_device_object_index_from_id( iface, DIDFT_POV | DIDFT_MAKEINSTANCE( 0 ) );
            state->rgdwPOV[0] = dpad != -1 ? dpad * 4500 : -1;
            queue_event( iface, index, state->rgdwPOV[0], time, seq );
            notify = TRUE;
        }        
    }
    
    if (notify && impl->base.hEvent) SetEvent( impl->base.hEvent );
}

static void release_gamepad_request( void ) 
{
    char buffer[BUFFER_SIZE];
    struct sockaddr_in client_addr;
    int client_addr_len;
    
    client_addr.sin_family = AF_INET;
    client_addr.sin_addr.s_addr = inet_addr( "127.0.0.1" );
    client_addr.sin_port = htons( CLIENT_PORT );
    client_addr_len = sizeof(client_addr);
    
    buffer[0] = REQUEST_CODE_RELEASE_GAMEPAD;
    sendto( server_sock, buffer, BUFFER_SIZE, 0, (struct sockaddr*)&client_addr, client_addr_len );
}

HRESULT gamepad_enum_device( DWORD type, DWORD flags, DIDEVICEINSTANCEW *instance, DWORD version )
{   
    DWORD size;
    char gamepad_name[64];

    TRACE( "type %#lx, flags %#lx, instance %p, version %#lx.\n", type, flags, instance, version );
    
    if (!create_server_socket() || !get_gamepad_request( FALSE, gamepad_name )) return DIERR_INPUTLOST;
    
    size = instance->dwSize;
    memset( instance, 0, size );
    instance->dwSize = size;
    instance->guidInstance = GUID_Joystick;
    instance->guidProduct = GUID_Joystick;
    instance->guidProduct.Data1 = MAKELONG( 0x045e, 0x028e );
    if (version >= 0x0800) instance->dwDevType = DIDEVTYPE_HID | DI8DEVTYPE_GAMEPAD | (DI8DEVTYPEGAMEPAD_STANDARD << 8);
    else instance->dwDevType = DIDEVTYPE_HID | DIDEVTYPE_JOYSTICK | (DIDEVTYPEJOYSTICK_GAMEPAD << 8);
    instance->wUsagePage = HID_USAGE_PAGE_GENERIC;
    instance->wUsage = HID_USAGE_GENERIC_GAMEPAD;
    MultiByteToWideChar( CP_ACP, 0, gamepad_name, -1, instance->tszInstanceName, MAX_PATH );
    MultiByteToWideChar( CP_ACP, 0, gamepad_name, -1, instance->tszProductName, MAX_PATH );
    
    return DI_OK;
}

static BOOL init_object_properties( struct dinput_device *device, UINT index, struct hid_value_caps *caps,
                                    const DIDEVICEOBJECTINSTANCEW *instance, void *data )
{
    struct object_properties *properties;
    
    if (index == -1) return DIENUM_STOP;
    properties = device->object_properties + index;

    properties->logical_min = -32768;
    properties->logical_max = 32767;
    properties->range_min = 0;
    properties->range_max = 65535;
    properties->saturation = 10000;
    properties->granularity = 1;

    return DIENUM_CONTINUE;
}

static void gamepad_release( IDirectInputDevice8W *iface )
{
    struct gamepad *impl = impl_from_IDirectInputDevice8W( iface );
    CloseHandle( impl->base.read_event );
}

static HRESULT gamepad_read( IDirectInputDevice8W *iface )
{   
    int res;
    char buffer[BUFFER_SIZE];
    
    if (server_sock == INVALID_SOCKET) return DI_OK;
    res = recvfrom( server_sock, buffer, BUFFER_SIZE, 0, NULL, 0 );
    if (res == SOCKET_ERROR) return DI_OK;
    
    if (buffer[0] == REQUEST_CODE_GET_GAMEPAD_STATE && buffer[1] == 1) 
    {
        int gamepad_id;
        char dpad;
        short buttons, thumb_lx, thumb_ly, thumb_rx, thumb_ry, thumb_lz, thumb_rz;        
        
        gamepad_id = *(int*)(buffer + 2);
        if (gamepad_id != connected_gamepad_id) return DI_OK;
    
        buttons = *(short*)(buffer + 6);
        dpad = buffer[8];
    
        thumb_lx = *(short*)(buffer + 9);
        thumb_ly = *(short*)(buffer + 11);
        thumb_rx = *(short*)(buffer + 13);
        thumb_ry = *(short*)(buffer + 15);
        thumb_lz = *(unsigned char*)(buffer + 17);
        thumb_rz = *(unsigned char*)(buffer + 18);

        gamepad_handle_input( iface, thumb_lx, thumb_ly, thumb_rx, thumb_ry, thumb_lz, thumb_rz, buttons, dpad );
    }
    return DI_OK;
}

static HRESULT gamepad_acquire( IDirectInputDevice8W *iface )
{
    struct gamepad *impl = impl_from_IDirectInputDevice8W( iface );
    get_gamepad_request( TRUE, NULL );
    SetEvent( impl->base.read_event );
    return DI_OK;
}

static HRESULT gamepad_unacquire( IDirectInputDevice8W *iface )
{
    struct gamepad *impl = impl_from_IDirectInputDevice8W( iface );
    WaitForSingleObject( impl->base.read_event, INFINITE );
    
    release_gamepad_request();
    close_server_socket();
    return DI_OK;
}

static BOOL try_enum_object( struct dinput_device *impl, const DIPROPHEADER *filter, DWORD flags, enum_object_callback callback,
                             UINT index, DIDEVICEOBJECTINSTANCEW *instance, void *data )
{
    if (flags != DIDFT_ALL && !(flags & DIDFT_GETTYPE( instance->dwType ))) return DIENUM_CONTINUE;

    switch (filter->dwHow)
    {
    case DIPH_DEVICE:
        return callback( impl, index, NULL, instance, data );
    case DIPH_BYOFFSET:
        if (filter->dwObj != instance->dwOfs) return DIENUM_CONTINUE;
        return callback( impl, index, NULL, instance, data );
    case DIPH_BYID:
        if ((filter->dwObj & 0x00ffffff) != (instance->dwType & 0x00ffffff)) return DIENUM_CONTINUE;
        return callback( impl, index, NULL, instance, data );
    }

    return DIENUM_CONTINUE;
}

static void get_device_objects( int *instance_count, DIDEVICEOBJECTINSTANCEW **out ) 
{
    int i, index = 0;
    
    *instance_count = 0;
    *out = NULL;

    if (input_type & FLAG_DINPUT_MAPPER_STANDARD) 
    {
        DIDEVICEOBJECTINSTANCEW instances[17];
        *instance_count = 17;
        
        instances[index].guidType = GUID_XAxis;
        instances[index].dwOfs = DIJOFS_X;
        instances[index].dwType = DIDFT_ABSAXIS | DIDFT_MAKEINSTANCE( 0 );
        instances[index].dwFlags = DIDOI_ASPECTPOSITION;
        swprintf( instances[index].tszName, MAX_PATH, L"X Axis" );
        instances[index].wUsagePage = HID_USAGE_PAGE_GENERIC;
        instances[index].wUsage = HID_USAGE_GENERIC_X;
        index++;
        
        instances[index].guidType = GUID_YAxis;
        instances[index].dwOfs = DIJOFS_Y;
        instances[index].dwType = DIDFT_ABSAXIS | DIDFT_MAKEINSTANCE( 1 );
        instances[index].dwFlags = DIDOI_ASPECTPOSITION;
        swprintf( instances[index].tszName, MAX_PATH, L"Y Axis" );
        instances[index].wUsagePage = HID_USAGE_PAGE_GENERIC;
        instances[index].wUsage = HID_USAGE_GENERIC_Y;    
        index++;
        
        instances[index].guidType = GUID_ZAxis;
        instances[index].dwOfs = DIJOFS_Z;
        instances[index].dwType = DIDFT_ABSAXIS | DIDFT_MAKEINSTANCE( 2 );
        instances[index].dwFlags = DIDOI_ASPECTPOSITION;
        swprintf( instances[index].tszName, MAX_PATH, L"Z Axis" );
        instances[index].wUsagePage = HID_USAGE_PAGE_GENERIC;
        instances[index].wUsage = HID_USAGE_GENERIC_Z;    
        index++;    

        instances[index].guidType = GUID_RzAxis;
        instances[index].dwOfs = DIJOFS_RZ;
        instances[index].dwType = DIDFT_ABSAXIS | DIDFT_MAKEINSTANCE( 3 );
        instances[index].dwFlags = DIDOI_ASPECTPOSITION;
        swprintf( instances[index].tszName, MAX_PATH, L"Rz Axis" );
        instances[index].wUsagePage = HID_USAGE_PAGE_GENERIC;
        instances[index].wUsage = HID_USAGE_GENERIC_RZ;    
        index++;
        
        for (i = 0; i < 12; i++) 
        {
            instances[index].guidType = GUID_Button,
            instances[index].dwOfs = DIJOFS_BUTTON( i ),
            instances[index].dwType = DIDFT_BUTTON | DIDFT_MAKEINSTANCE( i ),
            swprintf( instances[index].tszName, MAX_PATH, L"Button %d", i );
            instances[index].wUsagePage = HID_USAGE_PAGE_BUTTON;
            instances[index].wUsage = i + 1;
            index++;
        }
        
        instances[index].guidType = GUID_POV;
        instances[index].dwOfs = DIJOFS_POV( 0 );
        instances[index].dwType = DIDFT_POV | DIDFT_MAKEINSTANCE( 0 );
        swprintf( instances[index].tszName, MAX_PATH, L"POV" );
        instances[index].wUsagePage = HID_USAGE_PAGE_GENERIC;
        instances[index].wUsage = HID_USAGE_GENERIC_HATSWITCH;
        
        *out = instances;
    }
    else if (input_type & FLAG_DINPUT_MAPPER_XINPUT) 
    {
        DIDEVICEOBJECTINSTANCEW instances[16];
        *instance_count = 16;
        
        instances[index].guidType = GUID_XAxis;
        instances[index].dwOfs = DIJOFS_X;
        instances[index].dwType = DIDFT_ABSAXIS | DIDFT_MAKEINSTANCE( 0 );
        instances[index].dwFlags = DIDOI_ASPECTPOSITION;
        swprintf( instances[index].tszName, MAX_PATH, L"X Axis" );
        instances[index].wUsagePage = HID_USAGE_PAGE_GENERIC;
        instances[index].wUsage = HID_USAGE_GENERIC_X;
        index++;
        
        instances[index].guidType = GUID_YAxis;
        instances[index].dwOfs = DIJOFS_Y;
        instances[index].dwType = DIDFT_ABSAXIS | DIDFT_MAKEINSTANCE( 1 );
        instances[index].dwFlags = DIDOI_ASPECTPOSITION;
        swprintf( instances[index].tszName, MAX_PATH, L"Y Axis" );
        instances[index].wUsagePage = HID_USAGE_PAGE_GENERIC;
        instances[index].wUsage = HID_USAGE_GENERIC_Y;
        index++;
        
        instances[index].guidType = GUID_ZAxis;
        instances[index].dwOfs = DIJOFS_Z;
        instances[index].dwType = DIDFT_ABSAXIS | DIDFT_MAKEINSTANCE( 2 );
        instances[index].dwFlags = DIDOI_ASPECTPOSITION;
        swprintf( instances[index].tszName, MAX_PATH, L"Z Axis" );
        instances[index].wUsagePage = HID_USAGE_PAGE_GENERIC;
        instances[index].wUsage = HID_USAGE_GENERIC_Z;
        index++;

        instances[index].guidType = GUID_RxAxis;
        instances[index].dwOfs = DIJOFS_RX;
        instances[index].dwType = DIDFT_ABSAXIS | DIDFT_MAKEINSTANCE( 3 );
        instances[index].dwFlags = DIDOI_ASPECTPOSITION;
        swprintf( instances[index].tszName, MAX_PATH, L"Rx Axis" );
        instances[index].wUsagePage = HID_USAGE_PAGE_GENERIC;
        instances[index].wUsage = HID_USAGE_GENERIC_RX;
        index++;

        instances[index].guidType = GUID_RyAxis;
        instances[index].dwOfs = DIJOFS_RY;
        instances[index].dwType = DIDFT_ABSAXIS | DIDFT_MAKEINSTANCE( 4 );
        instances[index].dwFlags = DIDOI_ASPECTPOSITION;
        swprintf( instances[index].tszName, MAX_PATH, L"Ry Axis" );
        instances[index].wUsagePage = HID_USAGE_PAGE_GENERIC;
        instances[index].wUsage = HID_USAGE_GENERIC_RY;    
        index++;
        
        for (i = 0; i < 10; i++) 
        {
            instances[index].guidType = GUID_Button,
            instances[index].dwOfs = DIJOFS_BUTTON( i ),
            instances[index].dwType = DIDFT_BUTTON | DIDFT_MAKEINSTANCE( i ),
            swprintf( instances[index].tszName, MAX_PATH, L"Button %d", i );
            instances[index].wUsagePage = HID_USAGE_PAGE_BUTTON;
            instances[index].wUsage = i + 1;
            index++;
        }
        
        instances[index].guidType = GUID_POV;
        instances[index].dwOfs = DIJOFS_POV( 0 );
        instances[index].dwType = DIDFT_POV | DIDFT_MAKEINSTANCE( 0 );
        swprintf( instances[index].tszName, MAX_PATH, L"POV" );
        instances[index].wUsagePage = HID_USAGE_PAGE_GENERIC;
        instances[index].wUsage = HID_USAGE_GENERIC_HATSWITCH;
        
        *out = instances;
    }
}

static HRESULT gamepad_enum_objects( IDirectInputDevice8W *iface, const DIPROPHEADER *filter,
                                     DWORD flags, enum_object_callback callback, void *context )
{
    struct gamepad *impl = impl_from_IDirectInputDevice8W( iface );
    int instance_count;
    DIDEVICEOBJECTINSTANCEW* instances;
    BOOL ret;
    DWORD i;
    
    get_device_objects( &instance_count, &instances );

    for (i = 0; i < instance_count; i++)
    {
        DIDEVICEOBJECTINSTANCEW *instance = instances + i;
        instance->dwSize = sizeof(DIDEVICEOBJECTINSTANCEW);
        instance->wReportId = 1;
        
        ret = try_enum_object( &impl->base, filter, flags, callback, i, instance, context );
        if (ret != DIENUM_CONTINUE) return DIENUM_STOP;
    }

    return DIENUM_CONTINUE;
}

static HRESULT gamepad_get_property( IDirectInputDevice8W *iface, DWORD property,
                                     DIPROPHEADER *header, const DIDEVICEOBJECTINSTANCEW *instance )
{
    struct gamepad *impl = impl_from_IDirectInputDevice8W( iface );
    
    switch (property)
    {
    case (DWORD_PTR)DIPROP_PRODUCTNAME:
    {
        DIPROPSTRING *value = (DIPROPSTRING *)header;
        lstrcpynW( value->wsz, impl->base.instance.tszProductName, MAX_PATH );
        return DI_OK;
    }
    case (DWORD_PTR)DIPROP_INSTANCENAME:
    {
        DIPROPSTRING *value = (DIPROPSTRING *)header;
        lstrcpynW( value->wsz, impl->base.instance.tszInstanceName, MAX_PATH );
        return DI_OK;
    }
    case (DWORD_PTR)DIPROP_VIDPID:
    {
        DIPROPDWORD *value = (DIPROPDWORD *)header;
        value->dwData = MAKELONG( 0x045e, 0x028e );
        return DI_OK;
    }
    case (DWORD_PTR)DIPROP_JOYSTICKID:
    {
        DIPROPDWORD *value = (DIPROPDWORD *)header;
        value->dwData = connected_gamepad_id;
        return DI_OK;
    }
    case (DWORD_PTR)DIPROP_GUIDANDPATH:
    {
        DIPROPGUIDANDPATH *value = (DIPROPGUIDANDPATH *)header;
        value->guidClass = GUID_DEVCLASS_HIDCLASS;
        lstrcpynW( value->wszPath, L"virtual#vid_045e&pid_028e&ig_00", MAX_PATH );
        return DI_OK;
    }
    }

    return DIERR_UNSUPPORTED;
}

HRESULT gamepad_create_device( struct dinput *dinput, const GUID *guid, IDirectInputDevice8W **out )
{
    static const DIPROPHEADER filter =
    {
        .dwSize = sizeof(filter),
        .dwHeaderSize = sizeof(filter),
        .dwHow = DIPH_DEVICE,
    };
    struct gamepad *impl;
    HRESULT hr;
    
    TRACE( "dinput %p, guid %s, out %p.\n", dinput, debugstr_guid( guid ), out );

    *out = NULL;
    if (!IsEqualGUID( &GUID_Joystick, guid )) return DIERR_DEVICENOTREG;

    if (!(impl = calloc( 1, sizeof(*impl) ))) return E_OUTOFMEMORY;
    dinput_device_init( &impl->base, &gamepad_vtbl, guid, dinput );
    impl->base.crit.DebugInfo->Spare[0] = (DWORD_PTR)(__FILE__ ": struct gamepad*->base.crit");
    impl->base.read_event = CreateEventW( NULL, TRUE, FALSE, NULL );

    gamepad_enum_device( 0, 0, &impl->base.instance, dinput->dwVersion );
    impl->base.caps.dwDevType = impl->base.instance.dwDevType;
    impl->base.caps.dwFirmwareRevision = 100;
    impl->base.caps.dwHardwareRevision = 100;
    impl->base.dwCoopLevel = DISCL_NONEXCLUSIVE | DISCL_BACKGROUND;
    
    if (FAILED(hr = dinput_device_init_device_format( &impl->base.IDirectInputDevice8W_iface ))) goto failed;
    gamepad_enum_objects( &impl->base.IDirectInputDevice8W_iface, &filter, DIDFT_AXIS, init_object_properties, NULL );

    *out = &impl->base.IDirectInputDevice8W_iface;
    return DI_OK;
    
failed:
    IDirectInputDevice_Release( &impl->base.IDirectInputDevice8W_iface );
    return hr;    
}

static const struct dinput_device_vtbl gamepad_vtbl =
{
    gamepad_release,
    NULL,
    gamepad_read,
    gamepad_acquire,
    gamepad_unacquire,
    gamepad_enum_objects,
    gamepad_get_property,
    NULL,
    NULL,
    NULL,
    NULL,
    NULL,
};
