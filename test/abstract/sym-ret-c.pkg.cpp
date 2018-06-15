/* TAGS: sym min c++ */
/* VERIFY_OPTS: --symbolic */
/* CC_OPTS: */

// V: v.O0 CC_OPT: -O0
// V: v.O1 CC_OPT: -O1
// V: v.O2 CC_OPT: -O2
// V: v.Os CC_OPT: -Os
#include <rst/domains.h>
#include <cassert>

int nondet() {
    return __sym_val_i32();
}

int foo( int y ) {
    int x = nondet() % 42;
    if ( y == 0 ) {
        return x;
    }
    return 42;
}

int main() {
    int x = foo( 16 );
    assert( x == 42 );
    x = foo( 0 );
    assert( x < 42 );
}
