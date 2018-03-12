/* TAGS: sym todo min c++ */
/* VERIFY_OPTS: --symbolic */
#include <rst/domains.h>
#include <cassert>


struct T {
    int val;
    int padding;
};

struct S {
    int val;
    int padding;
};

int main() {
    S s; T t;
    _SYM int val;
    s.val = val;
    t.val = s.val;
    assert( s.val == t.val );
}
