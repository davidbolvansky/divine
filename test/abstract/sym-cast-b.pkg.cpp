/* TAGS: sym min c++ */
/* VERIFY_OPTS: --symbolic */
/* CC_OPTS: */

// V: v.O0 CC_OPT: -O0
// V: v.O1 CC_OPT: -O1
// V: v.O2 CC_OPT: -O2
// V: v.Os CC_OPT: -Os
#include <rst/domains.h>
#include <cassert>
#include <limits>

int main() {
    int x = static_cast< int >( __sym_val_i32() );
    if ( x < 0 )
        return 0;
    short y = x;
    ++y;
    assert( y != -32768 ); /* ERROR */
}
