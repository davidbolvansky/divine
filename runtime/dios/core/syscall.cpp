// -*- C++ -*- (c) 2016 Jan Mrázek <email@honzamrazek.cz>

#include <signal.h>
#include <cerrno>

#include <dios/core/syscall.hpp>

namespace __dios {

#include <dios/macro/no_memory_tags>
#define SYSCALL( name, schedule, ret, arg ) \
    ret BaseContext:: name arg { \
        __dios_trace( 0, "Syscall " #name " not implemented in this configuration" ); \
        __dios_fault( (_VM_Fault) _DiOS_F_Assert, "Syscall not implemented" ); \
        __builtin_unreachable(); \
    }
#define SYSCALLSEP SYSCALL

#include <sys/syscall.def>

#include <dios/macro/no_memory_tags.cleanup>
#undef SYSCALL
#undef SYSCALLSEP

} // namespace _dios

