/* VERIFY_OPTS: --symbolic */
#include <abstract/domains.h>
#include <cassert>

int x = 7;

int get() { return x; }

int main() {
    assert( x == 7 );

    _SYM int val;
    x = x + val;
    assert( val + 7 == x );
}
