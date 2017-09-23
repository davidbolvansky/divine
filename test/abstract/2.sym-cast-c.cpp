/* VERIFY_OPTS: --symbolic */
#include<abstract/domains.h>
#include <cassert>
#include <limits>

int main() {
    _SYM int x;
    if ( x < 0 )
        return 0;
    short y = x;
    ++y;
    assert( y != std::numeric_limits< short >::min() ); /* ERROR */
}
