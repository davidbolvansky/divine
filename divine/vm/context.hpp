// -*- mode: C++; indent-tabs-mode: nil; c-basic-offset: 4 -*-

/*
 * (c) 2016 Petr Ročkai <code@fixp.eu>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

#pragma once

#include <divine/vm/value.hpp>

#include <divine/vm/divm.h>

#include <brick-data>

#include <unordered_set>

namespace llvm { class Value; }

namespace divine {
namespace vm {

struct Interrupt
{
    enum Type { Mem, Cfl } type:1;
    uint32_t ictr:31;
    CodePointer pc;
};

static inline std::ostream &operator<<( std::ostream &o, Interrupt i )
{
    return o << ( i.type == Interrupt::Mem ? 'M' : 'C' ) << "/" << i.ictr
             << "/" << i.pc.function() << ":" << i.pc.instruction();
}

struct Choice
{
    int taken, total;
    Choice( int taken, int total ) : taken( taken ), total( total ) {}
};

static inline std::ostream &operator<<( std::ostream &o, Choice i )
{
    return o << i.taken << "/" << i.total;
}

struct Step
{
    std::deque< Interrupt > interrupts;
    std::deque< Choice > choices;
};

using Fault = ::_VM_Fault;

struct TraceText { GenericPointer text; };
struct TraceSchedChoice { value::Pointer list; };
struct TraceSchedInfo { int pid; int tid; };
struct TraceStateType { CodePointer pc; };
struct TraceInfo { GenericPointer text; };
struct TraceAlg { brick::data::SmallVector< divine::vm::GenericPointer > args; };
struct TraceTypeAlias { CodePointer pc; GenericPointer alias; };

template< typename _Program, typename _Heap >
struct Context
{
    using Program = _Program;
    using Heap = _Heap;
    using PointerV = value::Pointer;
    using HeapInternal = typename Heap::Internal;
    using Location = typename Program::Slot::Location;

    union Register
    {
        GenericPointer pointer;
        uint64_t integer;
        Register() : integer( 0 ) {}
    } _reg[ _VM_CR_Last ];

    /* indexed by _VM_ControlRegister */
    HeapInternal _ptr2i[ _VM_CR_Frame + 1 ];

    Program *_program;
    Heap _heap;
    std::vector< Interrupt > _interrupts;
    std::unordered_set< GenericPointer > _cfl_visited;
    std::unordered_set< int > _mem_loads;
    uint32_t _instruction_counter;
    bool _debug_mode = false;

    template< typename Ctx >
    void load( const Ctx &ctx )
    {
        clear();
        for ( int i = 0; i < _VM_CR_Last; ++i )
        {
            auto cr = _VM_ControlRegister( i );
            if ( cr == _VM_CR_Flags || cr == _VM_CR_User2 )
                set( cr, ctx.get( cr ).integer );
            else
                set( cr, ctx.get( cr ).pointer );
        }
        _heap = ctx.heap();
    }

    void reset_interrupted()
    {
        _cfl_visited.clear();
        _mem_loads.clear();
        set_interrupted( false );
    }

    void clear()
    {
        _interrupts.clear();
        reset_interrupted();
        flush_ptr2i();
        set( _VM_CR_User1, 0 );
        set( _VM_CR_User2, 0 );
        set( _VM_CR_ObjIdShuffle, 0 );
        _instruction_counter = 0;
    }

    void load( typename Heap::Snapshot snap ) { _heap.restore( snap ); clear(); }
    void reset() { _heap.reset(); clear(); }

    template< typename I >
    int choose( int, I, I ) { return 0; }

    void set( _VM_ControlRegister r, uint64_t v ) { _reg[ r ].integer = v; }
    void set( _VM_ControlRegister r, GenericPointer v )
    {
        _reg[ r ].pointer = v;
        if ( r <= _VM_CR_Frame )
            _ptr2i[ r ] = v.null() ? HeapInternal() : _heap.ptr2i( v );
    }

    Register get( _VM_ControlRegister r ) const { return _reg[ r ]; }
    Register get( Location l ) const { ASSERT_LT( l, Program::Slot::Invalid ); return _reg[ l ]; }
    Register &ref( _VM_ControlRegister r ) { return _reg[ r ]; }

    HeapInternal ptr2i( Location l )
    {
        ASSERT_LT( l, Program::Slot::Invalid );
        ASSERT_EQ( _heap.ptr2i( _reg[ l ].pointer ), _ptr2i[ l ] );
        return _ptr2i[ l ];
    }
    HeapInternal ptr2i( _VM_ControlRegister r ) { return ptr2i( Location( r ) ); }

    void ptr2i( Location l, HeapInternal i ) { if ( i ) _ptr2i[ l ] = i; else flush_ptr2i(); }
    void ptr2i( _VM_ControlRegister r, HeapInternal i ) { ptr2i( Location( r ), i ); }
    void flush_ptr2i()
    {
        for ( int i = 0; i <= _VM_CR_Frame; ++i )
            _ptr2i[ i ] = _heap.ptr2i( get( Location( i ) ).pointer );
    }

    Context( Program &p ) : Context( p, Heap() ) {}
    Context( Program &p, const Heap &h ) : _program( &p ), _heap( h )
    {
        for ( int i = 0; i < _VM_CR_Last; ++i )
            _reg[ i ].integer = 0;
    }
    virtual ~Context() { }

    Program &program() { return *_program; }
    Heap &heap() { return _heap; }
    const Heap &heap() const { return _heap; }
    HeapPointer frame() { return get( _VM_CR_Frame ).pointer; }
    HeapPointer globals() { return get( _VM_CR_Globals ).pointer; }
    HeapPointer constants() { return get( _VM_CR_Constants ).pointer; }

    typename Heap::Snapshot snapshot()
    {
        auto rv = _heap.snapshot();
        flush_ptr2i();
        return rv;
    }

    void push( PointerV ) {}

    template< typename X, typename... Args >
    void push( PointerV p, X x, Args... args )
    {
        heap().write_shift( p, x );
        push( p, args... );
    }

    bool enter_debug() { return false; }

    template< typename... Args >
    void enter( CodePointer pc, PointerV parent, Args... args )
    {
        auto frameptr = heap().make( program().function( pc ).framesize, 16 );
        set( _VM_CR_Frame, frameptr.cooked() );
        set( _VM_CR_PC, pc );
        heap().write_shift( frameptr, PointerV( pc ) );
        heap().write_shift( frameptr, parent );
        push( frameptr, args... );
    }

    bool set_interrupted( bool i )
    {
        auto &fl = ref( _VM_CR_Flags ).integer;
        bool rv = fl & _VM_CF_Interrupted;
        fl &= ~_VM_CF_Interrupted;
        fl |= i ? _VM_CF_Interrupted : 0;
        return rv;
    }

    void cfl_interrupt( CodePointer pc )
    {
        if( in_kernel() )
            return;

        if ( _cfl_visited.count( pc ) )
            trigger_interrupted( Interrupt::Cfl, pc );
        else
            _cfl_visited.insert( pc );
    }

    void entered( CodePointer ) {}
    void left( CodePointer pc )
    {
        std::unordered_set< GenericPointer > pruned;
        for ( auto check : _cfl_visited )
            if ( check.object() != pc.function() )
                pruned.insert( check );
        std::swap( pruned, _cfl_visited );
    }

    void trigger_interrupted( Interrupt::Type t, CodePointer pc )
    {
        if ( !set_interrupted( true ) )
            _interrupts.push_back( Interrupt{ t, _instruction_counter, pc } );
    }

    void mem_interrupt( CodePointer pc, GenericPointer ptr, int, int type )
    {
        if( in_kernel() )
            return;

        if ( ptr.heap() && !heap().shared( ptr ) )
            return;

        if ( type == _VM_MAT_Load )
        {
            if ( ptr.heap() )
                ptr.type( PointerType::Heap );
            if ( _mem_loads.count( ptr.object() ) )
                trigger_interrupted( Interrupt::Mem, pc );
            else
                _mem_loads.insert( ptr.object() );
        }
        else
            trigger_interrupted( Interrupt::Mem, pc );
    }

    void count_instruction()
    {
        if ( !_debug_mode )
            ++ _instruction_counter;
    }

    template< typename Eval >
    bool check_interrupt( Eval &eval )
    {
        if ( mask() || ( ref( _VM_CR_Flags ).integer & _VM_CF_Interrupted ) == 0 )
            return false;

        if( in_kernel() )
        {
            eval.fault( _VM_F_Control ) << " illegal interrupt in kernel mode";
            return false;
        }

        sync_pc();
        auto interrupted = get( _VM_CR_Frame ).pointer;
        set( _VM_CR_Frame, get( _VM_CR_IntFrame ).pointer );
        set( _VM_CR_IntFrame, interrupted );
        PointerV pc;
        heap().read( frame(), pc );
        set( _VM_CR_PC, pc.cooked() );
        reset_interrupted();
        ref( _VM_CR_Flags ).integer |= _VM_CF_Mask | _VM_CF_KernelMode;
        return true;
    }

    virtual void trace( TraceText ) {} // fixme?
    virtual void trace( TraceSchedInfo ) { NOT_IMPLEMENTED(); }
    virtual void trace( TraceSchedChoice ) { NOT_IMPLEMENTED(); }
    virtual void trace( TraceStateType ) { NOT_IMPLEMENTED(); }
    virtual void trace( TraceInfo ) { NOT_IMPLEMENTED(); }
    virtual void trace( TraceAlg ) { NOT_IMPLEMENTED(); }
    virtual void trace( TraceTypeAlias ) { NOT_IMPLEMENTED(); }

    virtual void doublefault()
    {
        _heap.rollback();
        flush_ptr2i();
        ref( _VM_CR_Flags ).integer |= _VM_CF_Error;
        set( _VM_CR_Frame, nullPointer() );
    }

    void fault( Fault f, HeapPointer frame, CodePointer pc )
    {
        auto fh = get( _VM_CR_FaultHandler ).pointer;
        if ( fh.null() )
            doublefault();
        else
            enter( fh, PointerV( get( _VM_CR_Frame ).pointer ),
                   value::Int< 32 >( f ), PointerV( frame ), PointerV( pc ), nullPointerV() );
    }

    bool mask( bool n )
    {
        auto &fl = ref( _VM_CR_Flags ).integer;
        bool rv = fl & _VM_CF_Mask;
        fl &= ~_VM_CF_Mask;
        fl |= n ? _VM_CF_Mask : 0;
        return rv;
    }

    void sync_pc()
    {
        auto frame = get( _VM_CR_Frame ).pointer;
        if ( frame.null() )
            return;
        auto pc = get( _VM_CR_PC ).pointer;
        ptr2i( _VM_CR_Frame,
               heap().write( frame, PointerV( pc ), ptr2i( _VM_CR_Frame ) ) );
    }

    bool mask() { return ref( _VM_CR_Flags ).integer & _VM_CF_Mask; }
    bool in_kernel() { return ref( _VM_CR_Flags ).integer & _VM_CF_KernelMode; }
};

template< typename Program, typename _Heap >
struct ConstContext : Context< Program, _Heap >
{
    void setup( int gds, int cds )
    {
        this->set( _VM_CR_Constants, this->heap().make( cds ).cooked() );
        if ( gds )
            this->set( _VM_CR_Globals, this->heap().make( gds ).cooked() );
    }

    ConstContext( Program &p ) : Context< Program, _Heap >( p ) {}
    ConstContext( Program &p, const _Heap &h ) : Context< Program, _Heap >( p, h ) {}
};

}
}
