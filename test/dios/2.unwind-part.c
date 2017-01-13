#include <assert.h>
#include <divine.h>
#include <stddef.h>
#include <dios.h>

volatile int wait = 1, end = 0;
volatile struct _VM_Frame *tframe = NULL;

void foo() __attribute__((__noinline__)) {
    tframe = __vm_control( _VM_CA_Get, _VM_CR_Frame );
    while ( wait ) { }
}

void bar() __attribute__((__noinline__)) {
    foo();
    assert( 0 );
}

void baz() __attribute__((__noinline__)) {
    bar();
    assert( 0 );
}

void thread( void *_ ) {
    baz();
    assert( 0 ); /* ERROR */
}

int main()
{
    __dios_start_thread( thread, NULL, 0 );
    while ( !tframe ) { }
    __dios_unwind( tframe, tframe->parent, tframe->parent->parent->parent );
    wait = 0;
    while ( 1 ) { }
}

