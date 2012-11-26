// -*- C++ -*- (c) 2012 Petr Rockai

#define NO_RTTI

#include <wibble/exception.h>
#include <wibble/test.h>

#include <divine/llvm/machine.h>
#include <divine/llvm/program.h>

#include <llvm/Instructions.h>
#include <llvm/Constants.h>
#include <llvm/Support/GetElementPtrTypeIterator.h>
#include <llvm/Support/CallSite.h>
#include <llvm/Target/TargetData.h>

#include <algorithm>
#include <cmath>

#ifndef DIVINE_LLVM_EXECUTION_H
#define DIVINE_LLVM_EXECUTION_H

namespace llvm {
template<typename T> class generic_gep_type_iterator;
typedef generic_gep_type_iterator<User::const_op_iterator> gep_type_iterator;
}

namespace divine {
namespace llvm {

using ::llvm::dyn_cast;
using ::llvm::cast;
using ::llvm::isa;
using ::llvm::ICmpInst;
using ::llvm::FCmpInst;
namespace Intrinsic = ::llvm::Intrinsic;
using ::llvm::CallSite;
using ::llvm::Type;

template< int N, typename _T > struct Z;
template< int N, typename _T > struct NZ { typedef _T T; };

template< typename _T > struct Z< 0, _T > { typedef _T T; };
template< typename _T > struct NZ< 0, _T > {};

struct Nil {
    static const int length = 0;
};

template< int N > struct ConsAt;

template<>
struct ConsAt< 0 > {
    template< typename Cons >
    static auto get( Cons &c ) -> decltype( c.car ) {
        return c.car;
    }
};

template< int N >
struct ConsAt {
    template< typename Cons >
    static auto get( Cons &c ) -> decltype( ConsAt< N - 1 >::get( c.cdr ) )
    {
        return ConsAt< N - 1 >::get( c.cdr );
    }
};

template< int, int > struct Eq;
template< int i > struct Eq< i, i > { typedef int Yes; };

template< typename A, typename B >
struct Cons {
    typedef A Car;
    typedef B Cdr;
    A car;
    B cdr;
    static const int length = 1 + B::length;

    template< int N >
    auto get() -> decltype( ConsAt< N >::get( *this ) )
    {
        return ConsAt< N >::get( *this );
    }
};

template< typename A, typename B >
Cons< A, B > cons( A a, B b ) {
    Cons< A, B > r;
    r.car = a; r.cdr = b;
    return r;
}

template< typename As, typename A, typename B >
Cons< As *, B > consPtr( A *a, B b ) {
    Cons< As *, B > r;
    r.car = reinterpret_cast< As * >( a );
    r.cdr = b;
    return r;
}

template< typename X >
struct UnPtr {};
template< typename X >
struct UnPtr< X * > { typedef X T; };

template< int I, typename Cons >
auto decons( Cons c ) -> typename UnPtr< decltype( ConsAt< I >::get( c ) ) >::T &
{
    return *c.template get< I >();
}

#define MATCH(l, expr...) template< typename F, typename X > \
    auto match( F f, X x ) -> \
        typename wibble::TPair< typename Eq< l, X::length >::Yes, decltype( f( expr ) ) >::Second \
    { return f( expr ); }

MATCH( 0 )
MATCH( 1, decons< 0 >( x ) )
MATCH( 2, decons< 1 >( x ), decons< 0 >( x ) )
MATCH( 3, decons< 2 >( x ), decons< 1 >( x ), decons< 0 >( x ) )
MATCH( 4, decons< 3 >( x ), decons< 2 >( x ), decons< 1 >( x ), decons< 0 >( x ) )

#undef MATCH

/* Dummy implementation of a ControlContext, useful for Evaluator for
 * control-flow-free snippets (like ConstantExpr). */
struct ControlContext {
    bool jumped;
    int choice;
    void enter( int ) { assert_die(); }
    void leave() { assert_die(); }
    MachineState::Frame &frame( int depth = 0 ) { assert_die(); }
    MachineState::Flags &flags() { assert_die(); }
    PC &pc() { assert_die(); }
    int new_thread( PC ) { assert_die(); }
    int stackDepth() { assert_die(); }
    int threadId() { assert_die(); }
};

template< typename X >
struct Dummy {
    static X &v() { assert_die(); }
};

/*
 * A relatively efficient evaluator for the LLVM instruction set. Current
 * semantics are derived from C++ semantics, which is not always entirely
 * correct. TBD.
 *
 * EvalContext provides access to the register file and memory. It needs to
 * provide at least TargetData, dereference( Value ), dereference( Pointer )
 * and malloc( int ).
 */
template < typename EvalContext, typename ControlContext >
struct Evaluator
{
    ProgramInfo &info;
    EvalContext &econtext;
    ControlContext &ccontext;

    Evaluator( ProgramInfo &i, EvalContext &e, ControlContext &c )
        : info( i ), econtext( e ), ccontext( c )
    {}

    bool is_signed;

    typedef ::llvm::Instruction LLVMInst;
    ProgramInfo::Instruction instruction;
    std::vector< ProgramInfo::Value > values; /* a withValues stash */

    struct Implementation {
        typedef void T;
        Evaluator< EvalContext, ControlContext > *_evaluator;
        Evaluator< EvalContext, ControlContext > &evaluator() { return *_evaluator; }
        ProgramInfo::Instruction i() { return _evaluator->instruction; }
        EvalContext &econtext() { return _evaluator->econtext; }
        ControlContext &ccontext() { return _evaluator->ccontext; }
        ::llvm::TargetData &TD() { return econtext().TD; }
    };

    char *dereference( ProgramInfo::Value v, int frame = 0 ) {
        return econtext.dereference( v, frame ); /* we don't care about other threads */
    }
    char *dereference( Pointer p ) { return econtext.dereference( p ); }

    template< typename... X >
    static void declcheck( X... ) {}

    /******** Arithmetic & comparisons *******/

    struct Arithmetic : Implementation {
        template< typename X = int >
        auto operator()( X &r = Dummy< X >::v(),
                         X &a = Dummy< X >::v(),
                         X &b = Dummy< X >::v() )
            -> decltype( declcheck( a % b ) )
        {
            switch( this->i().opcode ) {
                case LLVMInst::FAdd:
                case LLVMInst::Add: r = a + b; return;
                case LLVMInst::FSub:
                case LLVMInst::Sub: r = a - b; return;
                case LLVMInst::FMul:
                case LLVMInst::Mul: r = a * b; return;
                case LLVMInst::FDiv:
                case LLVMInst::SDiv:
                case LLVMInst::UDiv: r = a / b; return;
                case LLVMInst::FRem: r = std::fmod( a, b ); return;
                case LLVMInst::URem:
                case LLVMInst::SRem: r = a % b; return;
                case LLVMInst::And:  r = a & b; return;
                case LLVMInst::Or:   r = a | b; return;
                case LLVMInst::Xor:  r = a ^ b; return;
                case LLVMInst::Shl:  r = a << b; return;
                case LLVMInst::AShr:  // XXX?
                case LLVMInst::LShr:  r = a >> b; return;
            }
            assert_die();
        }
    };

    struct Select : Implementation {
        template< typename R = int, typename C = int >
        auto operator()( R &r = Dummy< R >::v(),
                         C &a = Dummy< C >::v(),
                         R &b = Dummy< R >::v(),
                         R &c = Dummy< R >::v() )
            -> decltype( declcheck( r = a ? b : c ) )
        {
            r = a ? b : c;
        }
    };

    struct ICmp : Implementation {
        template< typename R = int, typename X = int >
        auto operator()( R &r = Dummy< R >::v(),
                         X &a = Dummy< X >::v(),
                         X &b = Dummy< X >::v() )
            -> decltype( declcheck( r = a < b ) )
        {
            switch (dyn_cast< ICmpInst >( this->i().op )->getPredicate()) {
                case ICmpInst::ICMP_EQ:  r = a == b; return;
                case ICmpInst::ICMP_NE:  r = a != b; return;
                case ICmpInst::ICMP_ULT:
                case ICmpInst::ICMP_SLT: r = a < b; return;
                case ICmpInst::ICMP_UGT:
                case ICmpInst::ICMP_SGT: r = a > b; return;
                case ICmpInst::ICMP_ULE:
                case ICmpInst::ICMP_SLE: r = a <= b; return;
                case ICmpInst::ICMP_UGE:
                case ICmpInst::ICMP_SGE: r = a >= b; return;
                default: assert_die();
            }
        }
    };

    struct FCmp : Implementation {
        template< typename R = int, typename X = int >
        auto operator()( R &r = Dummy< R >::v(),
                         X &a = Dummy< X >::v(),
                         X &b = Dummy< X >::v() )
            -> decltype( declcheck( r = isnan( a ) && isnan( b ) ) )
        {
            switch ( dyn_cast< FCmpInst >( this->i().op )->getPredicate() ) {
                case FCmpInst::FCMP_FALSE: r = false; return;
                case FCmpInst::FCMP_TRUE:  r = true;  return;
                case FCmpInst::FCMP_ORD:   r = !isnan( a ) && !isnan( b ); return;
                case FCmpInst::FCMP_UNO:   r = isnan( a ) || isnan( b );   return;

                case FCmpInst::FCMP_UEQ:
                case FCmpInst::FCMP_UNE:
                case FCmpInst::FCMP_UGE:
                case FCmpInst::FCMP_ULE:
                case FCmpInst::FCMP_ULT:
                case FCmpInst::FCMP_UGT:
                    if ( isnan( a ) || isnan( b ) ) {
                        r = true;
                        return;
                    }
                    break;
                default: assert_die();
            }

            switch ( dyn_cast< FCmpInst >( this->i().op )->getPredicate() ) {
                case FCmpInst::FCMP_OEQ:
                case FCmpInst::FCMP_UEQ: r = a == b; return;
                case FCmpInst::FCMP_ONE:
                case FCmpInst::FCMP_UNE: r = a != b; return;

                case FCmpInst::FCMP_OLT:
                case FCmpInst::FCMP_ULT: r = a < b; return;

                case FCmpInst::FCMP_OGT:
                case FCmpInst::FCMP_UGT: r = a > b; return;

                case FCmpInst::FCMP_OLE:
                case FCmpInst::FCMP_ULE: r = a <= b; return;

                case FCmpInst::FCMP_OGE:
                case FCmpInst::FCMP_UGE: r = a >= b; return;
                default: assert_die();
            }
        }
    };

    /******** Register access & conversion *******/

    struct Copy : Implementation {
        template< typename X = int, typename Y = int >
        auto operator()( X &r = Dummy< X >::v(),
                         Y &l = Dummy< Y >::v() )
            -> decltype( declcheck( r = l ) )
        {
            r = l;
        }
    };

    /*
     * NB. Tricksy bit. The argument values are INVALID in here, because they
     * may be coming from a function whose frame is not on the top of the
     * stack.  I.e. the Frame vs Values are mismatched. This is no big deal
     * because we never dereference l, instead we grab the value from the
     * correct frame using the "values" stash directly.
     */
    template< int out, int in >
    struct CopyOut : Implementation {
        template< typename X = int, typename Y = int >
        auto operator()( X &r = Dummy< X >::v(),
                         Y &l = Dummy< Y >::v() )
            -> decltype( declcheck( r = l ) )
        {
            *reinterpret_cast< X * >(
                this->econtext().dereference(
                    this->evaluator().values[ 0 ], out ) ) =
                *reinterpret_cast< Y * >(
                    this->econtext().dereference(
                        this->evaluator().values[ 1 ], in ) );
        }
    };

    typedef CopyOut< 0, 1 > CopyArg;
    typedef CopyOut< 1, 0 > CopyResult;

    struct BitCast : Implementation {
        template< typename R = int, typename L = int >
        void operator()( R &r = Dummy< R >::v(),
                         L &l = Dummy< L >::v() )
        {
            char *from = reinterpret_cast< char * >( &l );
            char *to = reinterpret_cast< char * >( &r );
            assert_eq( sizeof( R ), sizeof( L ) );
            std::copy( from, from + sizeof( R ), to );
        }
    };

    template< typename _T >
    struct Get : Implementation {
        typedef _T T;

        template< typename X = T >
        auto operator()( X &l = Dummy< X >::v() ) -> decltype( static_cast< T >( l ) )
        {
            return static_cast< T >( l );
        }
    };

    template< typename _T >
    struct Set : Implementation {
        typedef _T Arg;
        Arg v;

        template< typename X = int >
        auto operator()( X &r = Dummy< X >::v() )
            -> decltype( declcheck( static_cast< X >( v ) ) )
        {
            r = static_cast< X >( v );
        }

        Set( Arg v ) : v( v ) {}
    };

    typedef Get< bool > IsTrue;
    typedef Get< int > GetInt;
    typedef Set< int > SetInt;

    /******** Memory access & conversion ********/

    struct GetElement : Implementation {
        void operator()( Pointer &r = Dummy< Pointer >::v(),
                         Pointer &p = Dummy< Pointer >::v() )
        {
            int total = 0;

            ::llvm::gep_type_iterator
                  I = ::llvm::gep_type_begin( this->i().op ),
                  E = ::llvm::gep_type_end( this->i().op );

            int meh = 1;
            for (; I != E; ++I, ++meh) {
                if (::llvm::StructType *STy = dyn_cast< ::llvm::StructType >(*I)) {
                    const ::llvm::StructLayout *SLO = this->TD().getStructLayout(STy);
                    const ::llvm::ConstantInt *CPU = cast< ::llvm::ConstantInt >( I.getOperand() ); /* meh */
                    int index = CPU->getZExtValue();
                    total += SLO->getElementOffset( index );
                } else {
                    const ::llvm::SequentialType *ST = cast< ::llvm::SequentialType >( *I );
                    int index = this->evaluator().withValues( GetInt(), this->i().operand( meh ) );
                    total += index * this->TD().getTypeAllocSize( ST->getElementType() );
                }
            }

            r = p + total;
        }
    };

    struct Load : Implementation {
        template< typename R = int >
        void operator()( R &r = Dummy< R >::v(),
                         Pointer p = Dummy< Pointer >::v() )
        {
            r = *reinterpret_cast< R * >( this->econtext().dereference( p ) );
        }
    };

    struct Store : Implementation {
        template< typename L = int >
        void operator()( L &l = Dummy< L >::v(),
                         Pointer p = Dummy< Pointer >::v() )
        {
            *reinterpret_cast< L * >( this->econtext().dereference( p ) ) = l;
        }
    };

    void implement_alloca() {
        ::llvm::AllocaInst *I = cast< ::llvm::AllocaInst >( instruction.op );
        Type *ty = I->getType()->getElementType();  // Type to be allocated

        int count = withValues( GetInt(), instruction.operand( 0 ) );
        int size = econtext.TD.getTypeAllocSize(ty); /* possibly aggregate */

        unsigned alloc = std::max( 1, count * size );
        Pointer &p = *reinterpret_cast< Pointer * >(
            dereference( instruction.result() ) );
        p = econtext.malloc( alloc );
    }

    /******** Control flow ********/

    void jumpTo( ProgramInfo::Value v )
    {
        PC to = *reinterpret_cast< PC * >( dereference( v ) );
        jumpTo( to );
    }

    void jumpTo( PC to )
    {
        if ( ccontext.pc().function != to.function )
            throw wibble::exception::Consistency(
                "Evaluator::jumpTo",
                "Can't deal with cross-function jumps." );
        switchBB( to );
    }

    void implement_ret() {
        if ( ccontext.stackDepth() == 1 ) {
            ccontext.leave();
            return;
        }

        auto caller = info.instruction( ccontext.frame( 1 ).pc );
        if ( instruction.values.size() > 1 ) /* return value */
            withValues( CopyResult(), caller.result(), instruction.operand( 0 ) );

        ccontext.leave();

        if ( isa< ::llvm::InvokeInst >( caller.op ) )
            jumpTo( caller.operand( -2 ) );
    }

    void implement_br()
    {
        if ( instruction.values.size() == 2 )
            jumpTo( instruction.operand( 0 ) );
        else {
            if ( withValues( IsTrue(), instruction.operand( 0 ) ) )
                jumpTo( instruction.operand( 2 ) );
            else
                jumpTo( instruction.operand( 1 ) );
        }
    }

    void implement_switch() {
        assert_die();
    }

    void implement_indirectBr() {
        Pointer target = withValues( Get< Pointer >(), instruction.operand( 0 ) );
        jumpTo( *reinterpret_cast< PC * >( dereference( target ) ) );
    }

    /*
     * Two-phase PHI handler. This method does this because all of the PHI nodes
     * must be executed atomically, reading their inputs before any of the results
     * are updated.  Not doing this can cause problems if the PHI nodes depend on
     * other PHI nodes for their inputs.  If the input PHI node is updated before
     * it is read, incorrect results can happen.
     */

    void switchBB( PC target )
    {
        PC origin = ccontext.pc();
        ccontext.pc() = target;
        ccontext.jumped = true;

        instruction = info.instruction( ccontext.pc() );
        assert( instruction.op );

        if ( !isa< ::llvm::PHINode >( instruction.op ) )
            return;  // Nothing fancy to do

        MachineState::Frame &original = ccontext.frame();
        int framesize = original.framesize( info );
        Blob tmp( sizeof( MachineState::Frame ) + framesize );
        MachineState::Frame &copy = tmp.get< MachineState::Frame >();
        copy = ccontext.frame();

        std::copy( original.memory, original.memory + framesize, copy.memory );
        while ( ::llvm::PHINode *PN = dyn_cast< ::llvm::PHINode >( instruction.op ) ) {
            /* TODO use operands directly, avoiding valuemap lookup */
            auto v = info.valuemap[ PN->getIncomingValueForBlock( info.block( origin ).bb ) ];
            char *value = ( v.global || v.constant ) ?
                          econtext.dereference( v ) : original.dereference( info, v );
            char *result = copy.dereference( info, instruction.result() );
            std::copy( value, value + v.width, result );
            ccontext.pc().instruction ++;
            instruction = info.instruction( ccontext.pc() );
        }
        std::copy( copy.memory, copy.memory + framesize, original.memory );
    }

    void implement_call() {
        CallSite CS( cast< ::llvm::Instruction >( instruction.op ) );
        ::llvm::Function *F = CS.getCalledFunction();

        if ( F && F->isDeclaration() ) {

            switch (F->getIntrinsicID()) {
                case Intrinsic::not_intrinsic: break;
                case Intrinsic::vastart:
                case Intrinsic::trap:
                case Intrinsic::vaend:
                case Intrinsic::vacopy:
                    assert_die(); /* TODO */
                default:
                    assert_die(); /* We lowered everything in buildInfo. */
            }

            switch( instruction.builtin ) {
                case NotBuiltin: break;
                case BuiltinChoice:
                    ccontext.choice = withValues( GetInt(), instruction.operand( 0 ) );
                    return;
                case BuiltinAssert:
                    ccontext.flags().assert = !withValues( GetInt(), instruction.operand( 0 ) );
                    return;
                case BuiltinMask: ccontext.pc().masked = true; return;
                case BuiltinUnmask: ccontext.pc().masked = false; return;
                case BuiltinInterrupt: return; /* an observable noop, see interpreter.h */
                case BuiltinGetTID:
                    withValues( SetInt( ccontext.threadId() ), instruction.result() );
                    return;
                case BuiltinNewThread:
                    Pointer entry = withValues( Get< Pointer >(), instruction.operand( 0 ) );
                    /* As far as LLVM is concerned, entry is a Pointer, but in fact it's a PC. */
                    int tid = ccontext.new_thread( *reinterpret_cast< PC * >( &entry ) );
                    withValues( SetInt( tid ), instruction.result() );
                    return;
            }
        }

        assert ( !F->isDeclaration() );

        /* TODO (performance) Use an operand Value here instead. */
        int functionid = info.functionmap[ F ];
        ccontext.enter( functionid ); /* push a new frame */
        ccontext.jumped = true;

        /* Copy arguments to the new frame. */
        ProgramInfo::Function function = info.function( ccontext.pc() );
        for ( int i = 0; i < CS.arg_size(); ++i )
            withValues( CopyArg(), function.values[ i ], instruction.operand( i ) );

        /* TODO varargs */

        assert( !isa< ::llvm::PHINode >( instruction.op ) );
    }

    /******** Dispatch ********/

    void run() {
        is_signed = false;
        switch ( instruction.opcode ) {
            case LLVMInst::GetElementPtr:
                implement( GetElement(), 2 ); break;
            case LLVMInst::Select:
                implement< Select >(); break;
            case LLVMInst::ICmp:
                implement< ICmp >(); break;
            case LLVMInst::FCmp:
                implement< FCmp >(); break;
            case LLVMInst::ZExt:
            case LLVMInst::FPExt:
            case LLVMInst::UIToFP:
            case LLVMInst::FPToUI:
            case LLVMInst::PtrToInt:
            case LLVMInst::IntToPtr:
            case LLVMInst::FPTrunc:
            case LLVMInst::Trunc:
                implement< Copy >(); break;

            case LLVMInst::Br:
                implement_br(); break;
            case LLVMInst::IndirectBr:
                implement_indirectBr(); break;
            case LLVMInst::Switch:
                implement_switch(); break;
            case LLVMInst::Call:
            case LLVMInst::Invoke:
                implement_call(); break;
            case LLVMInst::Ret:
                implement_ret(); break;

            case LLVMInst::SExt:
            case LLVMInst::SIToFP:
            case LLVMInst::FPToSI:
                is_signed = true;
                implement< Copy >(); break;

            case LLVMInst::BitCast:
                implement< BitCast >(); break;

            case LLVMInst::Load:
                implement< Load >(); break;
            case LLVMInst::Store:
                implement< Store >(); break;
            case LLVMInst::Alloca:
                implement_alloca(); break;

            case LLVMInst::FAdd:
            case LLVMInst::Add:
            case LLVMInst::FSub:
            case LLVMInst::Sub:
            case LLVMInst::FMul:
            case LLVMInst::Mul:
            case LLVMInst::FDiv:
            case LLVMInst::SDiv:
            case LLVMInst::UDiv:
            case LLVMInst::FRem:
            case LLVMInst::URem:
            case LLVMInst::SRem:
            case LLVMInst::And:
            case LLVMInst::Or:
            case LLVMInst::Xor:
            case LLVMInst::Shl:
            case LLVMInst::AShr:
            case LLVMInst::LShr:
                implement< Arithmetic >(); break;

            default: assert_die();
        }
    }

    template< typename Fun, typename I, typename Cons >
    typename Fun::T implement( wibble::NotPreferred, I i, I e, Cons list, Fun = Fun() ) {
        assert_die(); /* could not match parameters */
    }

    template< typename Fun, typename I, typename Cons >
    auto implement( wibble::Preferred, I i, I e, Cons list, Fun fun = Fun() )
        -> typename wibble::TPair< decltype( match( fun, list ) ), typename Fun::T >::Second
    {
        typedef ProgramInfo::Value Value;
        wibble::Preferred p;

        if ( i == e ) {
            fun._evaluator = this;
            return match( fun, list );
        }

        Value v = *i++;
        char *mem = dereference( v );

        switch ( v.type ) {
            case Value::Integer: if ( is_signed ) switch ( v.width ) {
                    case 1: return implement( p, i, e, consPtr<  int8_t >( mem, list ), fun );
                    case 4: return implement( p, i, e, consPtr< int32_t >( mem, list ), fun );
                    case 2: return implement( p, i, e, consPtr< int16_t >( mem, list ), fun );
                    case 8: return implement( p, i, e, consPtr< int64_t >( mem, list ), fun );
                } else switch ( v.width ) {
                    case 1: return implement( p, i, e, consPtr<  uint8_t >( mem, list ), fun );
                    case 4: return implement( p, i, e, consPtr< uint32_t >( mem, list ), fun );
                    case 2: return implement( p, i, e, consPtr< uint16_t >( mem, list ), fun );
                    case 8: return implement( p, i, e, consPtr< uint64_t >( mem, list ), fun );
                }
            case Value::Pointer:
                return implement( p, i, e, consPtr< Pointer >( mem, list ), fun );
            case Value::CodePointer:
                return implement( p, i, e, consPtr< PC >( mem, list ), fun );
            case Value::Float: switch ( v.width ) {
                case sizeof(float):
                    return implement( p, i, e, consPtr< float >( mem, list ), fun );
                case sizeof(double):
                    return implement( p, i, e, consPtr< double >( mem, list ), fun );
            }
            case Value::Void:
                return implement( p, i, e, list, fun ); /* ignore void items */
        }

        assert_die();
    }

    template< typename Fun, int Limit = 3 >
    typename Fun::T implement( Fun fun = Fun(), int limit = 0 )
    {
        auto i = instruction.values.begin(), e = limit ? i + limit : instruction.values.end();
        return implement( wibble::Preferred(), i, e, Nil(), fun );
    }

    template< typename Fun >
    typename Fun::T _withValues( Fun fun ) {
        return implement< Fun >( wibble::Preferred(), values.begin(), values.end(), Nil(), fun );
    }

    template< typename Fun, typename... Values >
    typename Fun::T _withValues( Fun fun, ProgramInfo::Value v, Values... vs ) {
        values.push_back( v );
        return _withValues< Fun >( fun, vs... );
    }

    template< typename Fun, typename... Values >
    typename Fun::T withValues( Fun fun, Values... vs ) {
        values.clear();
        return _withValues< Fun >( fun, vs... );
    }
};


}
}

#endif
