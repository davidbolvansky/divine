/* TAGS: sym c++ min todo */
/* VERIFY_OPTS: --symbolic */
/* CC_OPTS: */

// V: v.return V_OPT: --leakcheck return TAGS: todo
// V: v.state V_OPT: --leakcheck state
// V: v.exit V_OPT: --leakcheck exit
#include <sys/lamp.h>

#include <assert.h>

int first(int a, int b) { return a; }

int main() {
    int x = __lamp_any_i32();
    int y = __lamp_any_i32();

    int z = first(x, y);

    return 0;
}
