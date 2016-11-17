// -*- C++ -*- (c) 2016 Jan Mrázek <email@honzamrazek.cz>

#include <dios/syscall.hpp>
#include <dios/fault.hpp>
#include <dios/scheduling.hpp>
#include "fault.hpp"
#include <cerrno>

void __dios_syscall( int syscode, void* ret ... ) {
    uintptr_t fl = reinterpret_cast< uintptr_t >(
        __vm_control( _VM_CA_Get, _VM_CR_Flags,
                      _VM_CA_Bit, _VM_CR_Flags, _VM_CF_Mask, _VM_CF_Mask ) );
    va_list vl;
    va_start( vl, ret );
    int err = 0;
    __dios::Syscall::trap( syscode, &err, ret,  vl );
    while ( err == _DiOS_SYS_RETRY ) {
            err = 0;
         __dios::Syscall::trap( syscode, &err, ret,  vl );
    }
    if( err != 0) {
        errno = err;
    }
    va_end( vl );
    __vm_control( _VM_CA_Bit, _VM_CR_Flags, _VM_CF_Mask | _VM_CF_Interrupted, fl | _VM_CF_Interrupted ); /*  restore */
}

namespace __sc {
// Mapping of syscodes to implementations
#define SYSCALL(n,...) extern void n ( __dios::Context& ctx, int *err, void *retval, va_list vl );
    #include <dios/syscall.def>
} // namespace __sc

namespace __dios {

Syscall *Syscall::_inst;

void ( *_DiOS_SysCalls[ _SC_LAST ] ) ( Context& ctx, int *err, void* retval, va_list vl ) = {
    #define SYSCALL(n,...)  [ _SC_ ## n ] = __sc::n,
        #include <dios/syscall.def>
    #undef SYSCALL
};

const SchedCommand _DiOS_SysCallsSched[ _SC_LAST ] = {
    #define SYSCALL(n, sched,...) [ _SC_ ## n ] = sched,
        #include <dios/syscall.def>
    #undef SYSCALL
};

} // namespace _dios
