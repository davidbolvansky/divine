/* VERIFY_OPTS: --symbolic */
#include <abstract/domains.h>
#include <cassert>

int nondet() {
    _SYM int x;
    return x;
}

int foo() {
    int x = nondet();
    return x + 1;
}

int main() {
    int x = foo();
    assert( x == 0 ); /* ERROR */
}
