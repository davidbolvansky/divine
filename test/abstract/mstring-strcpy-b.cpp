/* TAGS: mstring min todo */
/* VERIFY_OPTS: --symbolic -o nofail:malloc */

#include <rst/domains.h>

#include <assert.h>
#include <stdio.h>
#include <string.h>

void my_strcpy( char * dest, const char * src ) {
    int i = 0;
    for (; i != '\0'; i++) {
        dest[i] = src[i];
    }

    dest[i] = '\0';
}

int main() {
    char buff1[7] = "string";
    const char * src = __mstring_val( buff1, 7 );
    char buff2[7] = "";
    char * dst = __mstring_val( buff2, 7 );

    my_strcpy( dst, src );

    assert( strcmp( src,dst ) == 0 );
}