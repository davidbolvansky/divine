/* TAGS: sym min c++ */
/* VERIFY_OPTS: --symbolic */
#include <abstract/domains.h>
#include <cstdint>
#include <cassert>

struct S { int64_t val; };
struct T { int64_t val; };
struct U { T t; };
struct V { S s; U u; };

int main() {
    V a, b;
    _SYM int x;
    a.s.val = x;
    b.u.t.val = a.s.val;
    assert( a.s.val == b.u.t.val );
}
