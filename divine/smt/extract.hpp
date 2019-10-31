// -*- mode: C++; indent-tabs-mode: nil; c-basic-offset: 4 -*-

/*
 * (c) 2018 Petr Ročkai <code@fixp.eu>
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

#include <divine/vm/memory.hpp>
#include <divine/vm/memory.tpp>
#include <divine/smt/builder.hpp>
#include <divine/smt/rpn.hpp>

namespace divine::smt
{

template< typename Builder >
struct Extract : Builder
{
    using Node = typename Builder::Node;

    template< typename... Args >
    Extract( vm::CowHeap &heap, Args && ... args )
        : Builder( std::forward< Args >( args )... ), _heap( heap )
    {}

    RPN read( vm::HeapPointer ptr )
    {
        auto data = _heap.unsafe_bytes( ptr );
        return RPN{ data.begin(), data.end() };
    }

    RPN read_constraints( vm::HeapPointer ptr )
    {
        vm::PointerV map( ptr ), clause;
        RPN rpn;
        rpn.push_back( 0 ); /* FIXME domain identification byte */

        if ( !_heap.valid( ptr ) )
            return rpn;

        bool first = true;
        for ( int i = 0; i < _heap.size( ptr ); i += vm::PointerBytes )
        {
            _heap.read_shift( map, clause );
            if ( clause.pointer() && _heap.valid( clause.cooked() ) )
            {
                ASSERT_EQ( clause.cooked().type(), vm::PointerType::Marked );
                auto b = _heap.unsafe_bytes( clause.cooked() );
                std::copy( b.begin() + 1, b.end(), std::back_inserter( rpn ) );
                if ( first )
                    first = false;
                else
                    rpn.push_back( static_cast< uint8_t >( brick::smt::Op::And ) );
            }
        }

        TRACE( "constraints:", rpn );
        return rpn;
    }

    Node build( vm::HeapPointer p );
    Node convert( vm::HeapPointer p )
    {
        auto it = _values.find( p );
        if ( it == _values.end() )
            it = _values.emplace( p, build( p ) ).first;
        return it->second;
    }

    vm::CowHeap &_heap;
    std::unordered_map< vm::HeapPointer, Node > _values;
};

}

namespace divine::smt::extract
{

using SMTLib2 = Extract< builder::SMTLib2 >;
#if OPT_Z3
using Z3      = Extract< builder::Z3 >;
#endif

#if OPT_STP
using STP     = Extract< builder::STP >;
#endif

}
