#include <sys/syscall.h>
#include <sys/divm.h>
#include <errno.h>
#include <stdint.h>

inline void __dios_trap( int syscode, int* err, void* ret, va_list *args )
{
    _DiOS_Syscall inst;
    inst._syscode = ( _DiOS_SC ) syscode;
    inst._ret = ret;
    inst._err = err;
    va_copy( inst._args, *args );
    __vm_control( _VM_CA_Set, _VM_CR_User1, &inst );
    __vm_control( _VM_CA_Bit, _VM_CR_Flags, _VM_CF_Mask | _VM_CF_Interrupted, _VM_CF_Interrupted );
    __vm_control( _VM_CA_Bit, _VM_CR_Flags, _VM_CF_Mask, _VM_CF_Mask );
    va_end( inst._args );
}

void __dios_syscall( int syscode, void* ret, ... )
{
    uintptr_t fl = ( uintptr_t )
        __vm_control( _VM_CA_Get, _VM_CR_Flags,
                      _VM_CA_Bit, _VM_CR_Flags, _VM_CF_Mask, _VM_CF_Mask );
    va_list vl;
    va_start( vl, ret );
    __dios_trap( syscode, ret,  &vl );
    while ( errno == EAGAIN2 )
    {
        errno = 0;
        __dios_trap( syscode, &err, ret, &vl );
    }

    va_end( vl );
    __vm_control( _VM_CA_Bit, _VM_CR_Flags,
                  _VM_CF_Mask | _VM_CF_Interrupted, fl | _VM_CF_Interrupted ); /*  restore */
}
