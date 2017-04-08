// -*- C++ -*- (c) 2016 Jan Mrázek <email@honzamrazek.cz>
//                 2016 Vladimir Still <xstill@fi.muni.cz>
//                 2016 Petr Rockai <me@mornfall.net>

extern "C" {
#include <sys/utsname.h>
}

#include <dios.h>
#include <sys/bitcode.h>
#include <divine/metadata.h>
#include <dios/core/main.hpp>
#include <dios/core/scheduling.hpp>
#include <dios/core/syscall.hpp>
#include <dios/core/trace.hpp>
#include <dios/core/fault.hpp>
#include <dios/core/monitor.hpp>
#include <dios/core/machineparams.hpp>
#include <dios/filesystem/fs-manager.h>
#include <dios/filesystem/fs-constants.h>

#include <sys/utsname.h>

#include <algorithm>

extern "C" {
#include <unistd.h>
char **environ;
}

namespace __dios {

bool useSyscallPassthrough( const SysOpts& o ) {
    for ( const auto& opt : o ) {
        if ( opt.first == "syscall" ) {
            if ( opt.second == "simulate" )
                return false;
            if ( opt.second == "passthrough" )
                return true;
            __dios_fault( _DiOS_F_Config,
                "DiOS boot configuration: invalid syscall option" );
        }
    }
    return false;
}

TraceDebugConfig getTraceDebugConfig( const SysOpts& o ) {
    TraceDebugConfig config;
    for( const auto& opt : o ) {
        String key;
        std::transform( opt.first.begin(), opt.first.end(),
            std::back_inserter( key ), ::tolower );

        if ( key == "notrace" || key == "trace" ) {
            bool trace = opt.first == "trace";
            String what;
            std::transform( opt.second.begin(), opt.second.end(),
                std::back_inserter( what ), ::tolower );

            if ( what == "threads" || what == "thread" )
                config.threads = trace;
            else
                __dios_trace_f( "Warning: uknown tracing param \"%s\"", opt.second.c_str() );
        }
        else if ( key == "debug" ) {
            String what;
            std::transform( opt.second.begin(), opt.second.end(),
                std::back_inserter( what ), ::tolower );

            if ( what == "help" )
                config.help = true;
            // ToDo: Trace binary blobs
            /*else if ( what == "rawenvironment" )
                config.raw = true;*/
            else if ( what == "machineparams" )
                config.machineParams = true;
            else if ( what == "mainargs" || what == "mainarg" )
                config.mainArgs = true;
            else if ( what == "faultcfg" )
                config.faultCfg = true;
            else
                __dios_trace_f( "Warning: uknown debug param \"%s\"", opt.second.c_str() );
        }
    }
    return config;
}

String extractDiosConfiguration( SysOpts& o ) {
    auto r = std::find_if( o.begin(), o.end(),
        []( const auto& opt ) {
            return opt.first == "configuration";
        } );
    String cfg( "standard" );
    if ( r != o.end() ) {
        cfg = r->second;
        o.erase( r );
    }
    return cfg;
}

void traceHelpOption( int i, String opt, String desc, const Vector<String>& args ) {
    __dios_trace_i( i, "- \"%s\":", opt.c_str() );
    __dios_trace_i( i + 2, "description: %s", desc.c_str() );
    __dios_trace_i( i + 2, "arguments:" );
    for ( const auto& arg : args )
        __dios_trace_i( i + 3, "- %s", arg.c_str() );
}

void traceHelp( int i ) {
    __dios_trace_i( i, "help:" );
    __dios_trace_i( i + 1, "supported commands:" );
    traceHelpOption( i + 2, "configuration", "run DiOS in given configuration",
        { "standard - threads, processes, vfs"
        });
    traceHelpOption( i + 2, "debug", "print debug information during boot",
        { "help - help and exit",
          // ToDo: trace binary blobs
          /*"rawenvironment - user DiOS boot parameters",*/
          "machineparams - specified by user, e.g. number of cpus",
          "mainargs - argv and envp",
          "faultcfg - fault and simfail configuration" } );
    traceHelpOption( i + 2, "{trace|notrace}",
        "report/not report item back to VM",
        { "threads - thread info during execution"} );
    traceHelpOption( i + 2, "[force-]{ignore|report|abort}",
        "configure fault, force disables program override",
        { "assert",
          "arithmetic",
          "memory",
          "control",
          "locking",
          "hypercall",
          "notimplemented",
          "diosassert" } );
    traceHelpOption( i + 2, "{nofail|simfail}",
        "enable/disable simulation of failure",
        { "malloc" } );
    traceHelpOption( i + 2, "ncpus", "specify number of cpu units (default 0)", { "<num>" } );
    traceHelpOption( i + 2, "{stdout|stderr}", "specify how to treat program output",
        { "notrace - ignore the stream",
          "unbuffered - trace each write",
          "trace - trace after each newline (default)"} );
    traceHelpOption( i + 2, "syscall", "specify how to treat standard syscalls",
        { "simulate - simulate syscalls, use virtual file system (can be used with verify and run)",
          "passthrough - use syscalls from the underlying host OS (cannot be used with verify) "} );
}

void traceEnv( int ind, const _VM_Env *env ) {
    __dios_trace_i( ind, "raw env options:" );
    for ( ; env->key; env++ ) {
        __dios_trace_i( ind + 1, "%s: \"%.*s\"", env->key, env->size, env->value );
    }
}

template < typename Configuration >
void boot( MemoryPool& pool, const _VM_Env *env, SysOpts& opts ) {
    auto *context = new_object< Configuration >();
    __vm_trace( _VM_T_StateType, context );
    __vm_control( _VM_CA_Set, _VM_CR_State, context );
    context->linkSyscall( Syscall< Configuration >::kernelHandle );
    context->setup( pool, env, opts );
}

void temporaryScheduler() {
    __vm_control( _VM_CA_Bit, _VM_CR_Flags, _VM_CF_Cancel, _VM_CF_Cancel );
}

void temporaryFaultHandler( _VM_Fault, _VM_Frame, void (*)(), ... ) { }

using DefaultConfiguration =
    Scheduler< Fault < fs::VFS < MachineParams < MonitorManager < BaseContext > > > > >;

void init( const _VM_Env *env )
{
    MemoryPool deterministicPool( 2 );

    __vm_control( _VM_CA_Set, _VM_CR_User1, nullptr );
    __vm_control( _VM_CA_Set, _VM_CR_FaultHandler, temporaryFaultHandler );
    __vm_control( _VM_CA_Set, _VM_CR_Scheduler, temporaryScheduler );

    SysOpts sysOpts;
    if ( !getSysOpts( env, sysOpts ) ) {
        __vm_control( _VM_CA_Bit, _VM_CR_Flags, _VM_CF_Error, _VM_CF_Error );
        return;
    }

    __dios_trace_i( 0, "DiOS boot info:" );
    if ( extractOpt( "help", "", sysOpts ) ) {
        traceHelp( 1 );
        __vm_control( _VM_CA_Bit, _VM_CR_Flags, _VM_CF_Cancel, _VM_CF_Cancel );
        return;
    }

    if ( extractOpt( "debug", "rawenvironment", sysOpts ) )
        traceEnv( 1, env );

    auto cfg = extractDiosConfiguration( sysOpts );
    if ( cfg == "standard" )
        boot< DefaultConfiguration >( deterministicPool, env, sysOpts );
    else {
        __dios_trace_f( 0, "Unknown DiOS configuration %s specified", cfg.c_str() );
        __vm_control( _VM_CA_Bit, _VM_CR_Flags, _VM_CF_Error, _VM_CF_Error );
        return;
    }
}

} // namespace __dios

/*
 * DiOS entry point. Defined weak to allow user to redefine it.
 */
extern "C" void  __attribute__((weak)) __boot( const _VM_Env *env ) {
    __dios::init( env );
}

int uname( struct utsname *__name ) {
    int ret;
    __dios_syscall( SYS_uname, &ret, __name );
    return ret;
}

int __dios_hardware_concurrency() noexcept {
    int ret;
    __dios_syscall( SYS_hardware_concurrency, &ret );
    return ret;
}

