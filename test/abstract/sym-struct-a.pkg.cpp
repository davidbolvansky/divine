/* TAGS: sym min c++ */
/* VERIFY_OPTS: --symbolic */
/* CC_OPTS: */

// V: v.O0 CC_OPT: -O0
// V: v.O1 CC_OPT: -O1
// V: v.O2 CC_OPT: -O2
// V: v.Os CC_OPT: -Os
#include <rst/domains.h>
#include <cassert>

struct S {
    int x;
};

int main() {
    int x = __sym_val_i32();
    S s;
    s.x = x;
    assert( s.x != 0 ); /* ERROR */
}
