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

#include <random>
#include <divine/vm/context.hpp>
#include <divine/vm/dbg-context.hpp>
#include <divine/vm/program.hpp>
#include <divine/vm/heap.hpp>

namespace divine {
namespace vm {

struct BitCode;

template< typename Super >
struct RunContext_ : Super
{
    std::mt19937 _rand;
    using Super::Super;
    using typename Super::Heap;
    std::vector< std::string > _trace;

    template< typename I >
    int choose( int o, I, I )
    {
        std::uniform_int_distribution< int > dist( 0, o - 1 );
        return dist( _rand );
    }

    void doublefault()
    {
        std::cerr << "E: Double fault, program terminated." << std::endl;
        this->set( _VM_CR_Frame, nullPointer() );
        this->ref( _VM_CR_Flags ).integer |= _VM_CF_Cancel;
    }

    void load( typename Heap::Snapshot ) { UNREACHABLE( "RunContext does not support load" ); }
    typename Heap::Snapshot snapshot() { UNREACHABLE( "RunContext does not support snapshots" ); }

    void trace( std::string s ) { std::cout << s << std::endl; }
    void trace( vm::TraceText tt ) { trace( this->heap().read_string( tt.text ) ); }
    void trace( vm::TraceSchedInfo ) { NOT_IMPLEMENTED(); }
    void trace( vm::TraceSchedChoice ) {}
    void trace( vm::TraceStateType ) {}
    void trace( vm::TraceInfo ti )
    {
        std::cout << this->heap().read_string( ti.text ) << std::endl;
    }
    void trace( vm::TraceAlg ) { }
    void trace( TraceTypeAlias ) { }
    void trace( TraceDebugPersist ) {} /* noop, since snapshots are not
                                        * restored here */
};

using RunContext = RunContext_< vm::Context< Program, MutableHeap<> > >;
using DbgRunContext = RunContext_< dbg::Context< MutableHeap<> > >;

struct Run
{
    using BC = std::shared_ptr< BitCode >;
    using Env = std::vector< std::string >;
    BC _bc;
    Run( BC bc ) : _bc( bc ) {}
    void run();
};

}
}
