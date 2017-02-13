// SimpleBufferOverflow.cpp : Defines the entry point for the console application.
//

// build with: cl /Fesimple_buffer_overflow.exe simple_buffer_overflow.cpp


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
		pItem->d();
	}

	if (pItem) {
		HeapFree(GetProcessHeap(), 0, pItem);
	}
    return 0;
}

