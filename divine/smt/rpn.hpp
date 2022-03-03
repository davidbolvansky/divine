// -*- mode: C++; indent-tabs-mode: nil; c-basic-offset: 4 -*-

/*
 * (c) 2018 Petr Ročkai <code@fixp.eu>
 * (c) 2018-2019 Henrich Lauko <xlauko@mail.muni.cz>
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

#include <brick-smt>
#include <divine/vm/pointer.hpp>

#include <list>
#include <map>
#include <cassert>
#include <optional>

namespace divine::smt
{
    template< typename builder_t, typename expr_t >
    auto evaluate( builder_t &bld, const expr_t &expr )
    {
        using node_t = typename builder_t::Node;

        std::vector< std::pair< node_t, int > > stack;

        auto pop = [&]()
        {
            auto v = stack.back();
            TRACE( "pop", v );
            stack.pop_back();
            return v;
        };

        auto push = [&]( node_t n, int bw )
        {
            TRACE( "push", n, "bw", bw );
            stack.emplace_back( n, bw );
        };

        TRACE( "evaluate", expr );

        for ( auto &atom : expr )
        {
            auto op = atom.op;
            if ( atom.varid() )
            {
                push( bld.variable( atom.varid(), op ), atom.bw() );
            }
            else if ( atom.is_const() )
            {
                auto bw = atom.bw();
                if ( atom.is_integral() )
                {
                    push( bld.constant( atom.value(), bw ), bw );
                }
                else if ( atom.is_float() )
                {
                    switch ( bw )
                    {
                        case 32 :
                            push( bld.constant( atom.template fpa_value< float >() ) , bw ); break;
                        case 64 :
                            push( bld.constant( atom.template fpa_value< double >() ), bw ); break;
                        default : UNREACHABLE( "unsupported floating point constant" );
                    }
                } else
                {
                    UNREACHABLE( "unsupported constant type" );
                }
            }
            else if ( atom.is_array() )
            {
                auto type = atom.array_type();
                push( bld.array( type.id, type ), type.bitwidth );
            }
            else if ( op == brq::smt_op::load )
            {
                auto [ off, obw ] = pop();
                auto [ arr, abw ] = pop();
                push( bld.load( arr, off, atom.bw( abw ) ), atom.bw( abw ) );
            }
            else if ( op == brq::smt_op::store )
            {
                auto [ val, vbw ] = pop();
                auto [ off, obw ] = pop();
                auto [ arr, abw ] = pop();
                push( bld.store( arr, off, val, vbw ), atom.bw( abw ) );
            }
            else if ( atom.is_extract() )
            {
                auto [ arg, bw ] = pop();
                push( bld.extract( arg, atom.bounds() ), atom.bw( bw ) );
            }
            else if ( atom.arity() == 1 )
            {
                auto [ arg, bw ] = pop();
                push( bld.unary( op, arg, atom.bw( bw ) ), atom.bw( bw ) );
            }
            else if ( atom.arity() == 2 )
            {
                auto [ b, bbw ] = pop();
                auto [ a, abw ] = pop();
                push( bld.binary( op, a, b, atom.bw( abw, bbw ) ), atom.bw( abw, bbw ) );
            }
        }

        ASSERT_EQ( stack.size(), 1 );
        return stack.back().first;
    }
}
