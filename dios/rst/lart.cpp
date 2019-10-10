#include <rst/lart.h>
#include <sys/task.h>

#include <rst/common.hpp>
#include <rst/constant.hpp>

#include <string.h>

using namespace __dios::rst::abstract;

/* Abstract versions of arguments and return values are passed in a 'stash', a
 * global (per-thread) location. On 'unstash', we clear the stash for two
 * reasons: 1) it flags up otherwise hard-to-pin bugs where mismatched
 * stash/unstash reads an old value of the stash, and 2) when verification
 * encounters a possible diamond (the explicit content of the state is the
 * same, e.g.  after an if/else) and we leave old stashes around, it might so
 * happen that the stashed values in the candidate states are of different
 * types, leading to a type mismatch in the comparison.
 *
 * TODO The second problem might have to be tackled in the verification
 * algorithm anyway, since there might be other ways to trigger the same
 * problem. */

extern "C"
{
    _LART_INTERFACE void * __lart_unstash()
    {
        auto &stash = __dios_this_task()->__rst_stash;
        auto rv = stash;
        stash = nullptr;
        return rv;
    }

    _LART_INTERFACE void __lart_stash( void * val )
    {
        __dios_this_task()->__rst_stash = val;
    }

    _LART_INTERFACE void __lart_freeze( void * value, void * addr )
    {
        poke_object( value, addr );
    }

    _LART_INTERFACE void * __lart_thaw( void * addr )
    {
        return peek_object< void * >( addr );
    }

    _LART_NOINLINE_WEAK
    void * __lart_get_domain_operation( uint32_t /*domain*/, uint32_t /*op_index*/ ) {
        return nullptr; // implementation is generated by lart
    }
}

/* lifter templates */

using Ptr = void *;

using store_op = void ( Ptr /* val */, Ptr /* ptr */ );
using gep_op = Ptr ( Ptr /* ptr */, Ptr /* off */ );


_LART_INLINE
uint8_t domain( Ptr addr ) noexcept { return *static_cast< uint8_t * >( addr ); }

template< typename Op >
auto get_operation( uint8_t domain, uint32_t op_index ) noexcept
{
    return reinterpret_cast< Op * >( __lart_get_domain_operation( domain, op_index ) );
}

template< typename T >
struct Argument { bool tainted; T concrete; void * abstract; };

template< typename Value >
_LART_INLINE
void __lart_store_lifter_impl( Argument< Value > value, Argument< Ptr > addr, size_t op )
{
    if ( !addr.tainted ) { // therefore value is abstract
        __lart_freeze( value.abstract, addr.concrete );
        return;
    }

    auto store = get_operation< store_op >( domain( addr.abstract ), op );
    auto val = value.tainted ? value.abstract : Constant::lift( value.concrete );

    store( val, addr.abstract );
}

#define LART_STORE_LIFTER( name, T ) \
    __invisible \
    void __lart_store_lifter_ ##name( bool taint_value, T value, void * abstract_value \
                                   , bool taint_addr, void * addr, void * abstract_addr \
                                   , size_t op ) \
    { \
        __lart_store_lifter_impl< T >( { taint_value, value, abstract_value } \
                                     , { taint_addr, addr, abstract_addr } \
                                     , op ); \
    }

template< typename Value >
_LART_INLINE
Ptr __lart_gep_lifter_impl( Argument< Ptr > ptr, Argument< Value > off, size_t op )
{
    if ( !ptr.tainted ) { // offset is tainted
        __dios_fault( _VM_Fault::_VM_F_Control, "unsupported abstract offset of concrete pointer" );
        return nullptr;
    }

    auto gep = get_operation< gep_op >( domain( ptr.abstract ), op );
    auto offset = off.tainted ? off.abstract : Constant::lift( off.concrete );

    return gep( ptr.abstract, offset );
}

#define LART_GEP_LIFTER( Off ) \
    __invisible \
    Ptr __lart_gep_lifter( bool taint_ptr, Ptr ptr, Ptr abstract_ptr \
                         , bool taint_off, Off off, Ptr abstract_off \
                         , size_t op ) \
    { \
        return __lart_gep_lifter_impl< uint64_t >( { taint_ptr, ptr, abstract_ptr } \
                                                 , { taint_off, off, abstract_off } \
                                                 , op ); \
    }

extern "C" {

    LART_STORE_LIFTER(  i8, uint8_t )
    LART_STORE_LIFTER( i16, uint16_t )
    LART_STORE_LIFTER( i32, uint32_t )
    LART_STORE_LIFTER( i64, uint64_t )

    LART_GEP_LIFTER( uint64_t )
}
