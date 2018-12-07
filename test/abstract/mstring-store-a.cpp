/* TAGS: mstring min */
/* VERIFY_OPTS: --symbolic -o nofail:malloc */

#include <rst/domains.h>

#include <assert.h>
#include <stdio.h>
#include <string.h>

int main() {
    char * a = __mstring_val( "aabb\0cc\0", 8 );
    a[ 4 ] = 'b';
    assert( strlen( a ) == 7 );
}
