#include <windows.h>
#include <stdio.h>
#include <string.h>

// Windows
// cl.exe /arch:IA32 /Fe:win32_api_test.exe win32_api_test.c

void crash_me(HANDLE hFile, const char **inputs) {


	DWORD dwWritten;
	
	int i = 0;
	const char *line = NULL;
	int length = 0;
	
	DWORD *lengths[3] = {
		&dwWritten,
		(DWORD*)(0xAAAAAAAA),
		NULL,
	};

	__debugbreak();

        length = strlen(inputs[0]);
		
	while(inputs[i] != NULL) {
		line = inputs[i];
	
		// iteration 0: manticore should silently ignore this WriteFile
		// iteration 1: manticore should detect a crash, if the model is good enough
		if(FALSE == WriteFile(hFile, line, length, lengths[i], NULL)) {
			printf("WriteFile failed\n");
		}
		
		// make symbolic stuff actually matter. Need to generate a 'Z' to get
		// to the crashing input 
		if(line[0] != 'Z') {
			break;
		}
		i++;
	}
}

int main(int argc, const char *argv[])
{
	const char *inputs[3] = {
		"write me to a file", 
		"write me to zfiles",
		NULL};

	const char fname[] = "C:\\delete_me.txt";
	
	HANDLE hFile = CreateFile(fname, GENERIC_READ|GENERIC_WRITE, 0, NULL, CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
	if(hFile == INVALID_HANDLE_VALUE) {
		printf("CreateFile failed");
	}
	crash_me(hFile, inputs);

	CloseHandle(hFile);
	DeleteFile(fname);
	return 0;
}
