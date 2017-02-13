// ConsoleApplication1.cpp : Defines the entry point for the console application.
//

#include "stdafx.h"
#include <Windows.h>

//TCHAR buffer[] = _T("PC:\\windows\\notepad.exe");
TCHAR buffer[] = _T("ZC:\\winodws\\notepad.exe");

int _tmain(int argc, _TCHAR* argv[])
{
	__debugbreak();

	TCHAR *buf = buffer;
	TCHAR op = buf[0];
	HKEY testkey = NULL;
	LSTATUS st = RegCreateKeyEx(HKEY_CURRENT_USER, L"Test", 0, NULL, 0, KEY_WRITE, NULL, &testkey, 0);
	if(st != ERROR_SUCCESS || testkey == NULL ) {
		return -1;
	}

	switch(op) {
		case L'P':
			{
				PROCESS_INFORMATION psi;
				STARTUPINFO si;
				ZeroMemory(&si, sizeof(si));
				si.cb = sizeof(si);
				BOOL worked = CreateProcess(NULL, buf+1, NULL, NULL, FALSE, 0, NULL, NULL, &si, &psi);
				if(worked) {
					CloseHandle(psi.hThread);
					CloseHandle(psi.hProcess);
				}
			}
		case L'R':
			{
				HKEY key = NULL;
				LSTATUS s = RegOpenKeyEx(HKEY_CURRENT_USER, buf+1, 0, KEY_READ, &key);
				if(s == ERROR_SUCCESS && key != NULL) {
					RegCloseKey(key);
				}
			}
		case L'K':
			{
				HKEY key = NULL;
				LSTATUS s = RegCreateKeyEx(testkey, buf+1, 0, NULL, 0, KEY_WRITE, NULL, &key, 0);
				if(s == ERROR_SUCCESS && key != NULL) {
					RegCloseKey(key);
				}
			}
		default:
			printf("Unknown argument: %C\n", op);
	}
	return 0;
}

