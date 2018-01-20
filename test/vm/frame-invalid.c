/* TAGS: min c */
#include <assert.h>
#include <sys/divm.h>
#include <dios.h>

int main()
{
    struct _VM_Frame *frame = __vm_obj_make( sizeof( struct _VM_Frame ) );
    __vm_obj_free( frame );
    __vm_control( _VM_CA_Set, _VM_CR_Frame, frame ); /* ERROR */
    assert( 0 );
}
