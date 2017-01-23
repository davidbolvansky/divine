/* VERIFY_OPTS: --symbolic */

#include <cassert>
#define __sym __attribute__((__annotate__("lart.abstract.symbolic")))

int nondet() {
    __sym int x;
    return x;
}

int foo( int b ) {
    int x = nondet() % 42;
    int z = nondet() % 2 + 42;
    if ( b == 0 ) {
        return x;
    }
    return z;
}

int main() {
    int x = foo( 0 );
    assert( x < 42 );
    x = foo( 16 );
    assert( x == 42 || x == 43 );
    assert( x == 42 ); /* ERROR */
}
