/* TAGS: mstring min sym */
/* VERIFY_OPTS: --symbolic -o nofail:malloc */

#include <rst/domains.h>

#include <assert.h>
#include <stdio.h>
#include <string.h>

int main() {
    char buff[7] = "string";
    const char * str = __mstring_val( buff, 7 );
    int len = strlen( str );
    assert( len == 6 );
}
