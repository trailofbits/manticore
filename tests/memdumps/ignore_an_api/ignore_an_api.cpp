// Exactly like the 'Simple Buffer Overflow' example
// but with a CloseHandle call that must be ignored
// to trigger the bug

// build with: cl /Fe:ignore_an_api.exe ignore_an_api.cpp


#pragma once
#include <tchar.h>
#include <stdio.h>
#include <windows.h>

typedef struct {
	DWORD a;
	DWORD b;
	DWORD c;
	VOID(*d)(VOID);
} ITEM, *PITEM;

VOID greetings(VOID)
{
	printf("Hello, world!\n");
}

int main()
{
	PITEM pItem = NULL;
	DWORD dwBytesRead = 0;
	char buffer[32] = { 0 };

	pItem = (PITEM)HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, sizeof(*pItem));
	if (!pItem) {
		printf("Failed to allocate memory\n");
		return -1;
	}

	pItem->d = greetings;

	if (!ReadFile(GetStdHandle(STD_INPUT_HANDLE), &buffer, 32, &dwBytesRead, NULL)) {
		printf("Failed to read STDIN\n");
		HeapFree(GetProcessHeap(), 0, pItem);
		return -1;
	}

	strcpy((char *) pItem, buffer);
    // debug break to make taking memory dumps easier
    __debugbreak();


	if (pItem->d) {
        CloseHandle(GetStdHandle(STD_INPUT_HANDLE));
		pItem->d();
	}

	if (pItem) {
		HeapFree(GetProcessHeap(), 0, pItem);
	}
    return 0;
}

