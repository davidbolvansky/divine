/* TAGS: sym min c++ */
/* VERIFY_OPTS: --symbolic */
#include <abstract/domains.h>
#include <assert.h>

int main() {
    _SYM int x;
    long y = x;
    assert( y + 1 > y );
}
