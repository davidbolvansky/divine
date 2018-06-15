/* TAGS: sym min c++ */
/* VERIFY_OPTS: --symbolic */
/* CC_OPTS: */

// V: v.O0 CC_OPT: -O0
// V: v.O1 CC_OPT: -O1
// V: v.O2 CC_OPT: -O2
// V: v.Os CC_OPT: -Os
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
    int val = __sym_val_i32();
    s.val = val;
    t.val = s.val;
    assert( s.val == t.val );
}
