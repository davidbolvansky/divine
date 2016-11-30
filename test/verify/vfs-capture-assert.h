using __dios::Set;
using __dios::String;

struct Context { const char *msg; };

void passSched() {
    __vm_control( _VM_CA_Bit, _VM_CR_Flags, _VM_CF_Cancel, _VM_CF_Cancel );
}

void failSched() {
    auto ctx = static_cast< Context * >( __vm_control( _VM_CA_Get, _VM_CR_State ) );
    __dios_trace_f( "Failed: %s", ctx->msg );
    __vm_control( _VM_CA_Bit, _VM_CR_Flags, _VM_CF_Error, _VM_CF_Error );
    __vm_control( _VM_CA_Bit, _VM_CR_Flags, _VM_CF_Cancel, _VM_CF_Cancel );
}

#define bAss( expr, ctx, message ) do { \
    if ( !(expr) ) { \
        ctx->msg = message; \
        __vm_control( _VM_CA_Set, _VM_CR_Scheduler, failSched ); \
        return; \
    } \
} while ( false )

bool isVfs( const char* name ) {
    int l = strlen( name );
    return memcmp( "vfs.", name, 4 ) == 0 &&
           memcmp( ".name", name + l - 5, 5 ) == 0;
}

std::pair< Set< String >, bool > collectVfsNames( const _VM_Env *env ) {
    Set< String > ret;
    bool unique = true;
    for (; env->key; env++ ) {
        if ( !isVfs( env->key ) )
            continue;

        String f( env->value, env->value + env->size );
        __dios_trace_f( "C: %s", f.c_str() );
        auto r = ret.insert( f );
        if ( !r.second )
            __dios_trace_f( "Multi-capture of an object: %s", f.c_str() );
        unique = unique && r.second;
    }

    return { ret, unique };
}

int main() {}
