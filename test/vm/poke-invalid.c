/* TAGS: min c */
#include <sys/divm.h>
#include <assert.h>

int main()
{
    int *a;
    __vm_pointer_t ptr = __vm_pointer_split( a );
    __vm_poke( _VM_ML_User, ptr.obj, ptr.off, 1, 0 ); /* ERROR */
    return 0;
}
