/*
 * http://www.phreedom.org/blog/2008/decompiling-ms08-067/
 */

#include <unistd.h>
#include <wchar.h>

// This is the decompiled function sub_5B86A51B in netapi32.dll on XP SP3
// and sub_6EA11D4D on Vista SP1

int ms08_067(wchar_t* path)
{
    wchar_t* p;
    wchar_t* q;
    wchar_t* previous_slash = NULL;
    wchar_t* current_slash  = NULL;
    wchar_t  ch;

#ifdef VISTA
    int len = wcslen(path);
    wchar_t* end_of_path = path + len;
#endif

    // If the path starts with a server name, skip it

    if ((path[0] == L'\\' || path[0] == L'/') &&
        (path[1] == L'\\' || path[1] == L'/'))
    {
        p = path+2;

        while (*p != L'\\' && *p != L'/') {
            if (*p == L'\0')
                return 0;
            p++;
        }

        p++;

        // make path point after the server name

        path = p;

        // make sure the server name is followed by a single slash

        if (path[0] == L'\\' || path[0] == L'/')
            return 0;
    }

    if (path[0] == L'\0')   // return if the path is empty
        return 1;

    // Iterate through the path and canonicalize "..\" and ".\"

    p = path;

    while (1) {
        if (*p == L'\\') {
            // we have a slash

            if (current_slash == p-1)   // don't allow consequtive slashes
                return 0;

            // store the locations of the current and previous slashes

            previous_slash = current_slash;
            current_slash = p;
        }
        else if (*p == L'.' && (current_slash == p-1 || p == path)) {
            // we have \. or ^.

            if (p[1] == L'.' && (p[2] == L'\\' || p[2] == L'\0')) {
                // we have a \..\, \..$, ^..\ or ^..$ sequence

                if (previous_slash == NULL)
                    return 0;

                // example: aaa\bbb\..\ccc
                //             ^   ^  ^
                //             |   |  &p[2]
                //             |   |
                //             |   current_slash
                //             |
                //             previous_slash

                ch = p[2];

#ifdef VISTA
                if (previous_slash >= end_of_path)
                    return 0;

                wcscpy_s(previous_slash, (end_of_path-previous_slash)/2, p+2);
#else // XP
                wcscpy(previous_slash, &p[2]);
#endif

                if (ch == L'\0')
                    return 1;

                current_slash = previous_slash;
                p = previous_slash;

                // find the slash before p

                // BUG: if previous_slash points to the beginning of the
                // string, we'll go beyond the start of the buffer
                //
                // example string: "\a\..\"

                q = p-1;
                
                while (*q != L'\\' && q != path)
                    q--;

                if (*p == L'\\')
                    previous_slash = q;
                else
                    previous_slash = NULL;
            }
            else if (p[1] == L'\\') {
                // we have "\.\" or "^.\"

#ifdef VISTA
                if (current_slash != NULL) {
                    if (current_slash >= end_of_path)
                        return 0;
                    wcscpy_s(current_slash, (end_of_path-current_slash)/2, p+2);
                    goto end_of_loop;
                }
                else {  // current_slash == NULL
                    if (p >= end_of_path)
                        return 0;
                    wcscpy_s(p, (end_of_path-p)/2, p+2);
                    goto end_of_loop;
                }
#else // XP
                if (current_slash != NULL) {
                    wcscpy(current_slash, p+2);
                    goto end_of_loop;
                }
                else { // current_slash == NULL
                    wcscpy(p, p+2);
                    goto end_of_loop;
                }
#endif
            }
            else if (p[1] != L'\0') {
                // we have \. or ^. followed by some other char

                if (current_slash != NULL) {
                    p = current_slash;
                }
                *p = L'\0';
                return 1;
            }
        }

        p++;

end_of_loop:
        if (*p == L'\0')
            return 1;
    }
}

// Run this program to simulate the MS08-067 vulnerability

int main()
{
    wchar_t buffer[128] = { 0 };
    int i;
    
    i = read(0, buffer, sizeof(buffer));
    
    //return ms08_067(L"\\c\\..\\..\\AAAAAAAAAAAAAAAAAAAAAAAAAAAAA");
    return ms08_067(buffer);
}

