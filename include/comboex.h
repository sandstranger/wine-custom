/*
 * ComboBoxEx class extra info
 *
 * Copyright 1998 Eric Kohl
 */

#ifndef __WINE_COMBOEX_H
#define __WINE_COMBOEX_H


typedef struct tagCOMBOEX_INFO
{
    HIMAGELIST himl;
    HWND32     hwndCombo;
    DWORD      dwExtStyle;


} COMBOEX_INFO;


extern VOID COMBOEX_Register (VOID);
extern VOID COMBOEX_Unregister (VOID);

#endif  /* __WINE_COMBOEX_H */
