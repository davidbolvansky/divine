// -*- mode: C++; indent-tabs-mode: nil; c-basic-offset: 4 -*-

/*
 * (c) 2018 Petr Ročkai <code@fixp.eu>
 * (c) 2018 Henrich Lauko <xlauko@mail.muni.cz>
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

#if OPT_Z3
#include <divine/smt/builder-common.hpp>
#include <z3++.h>

namespace divine::smt::builder
{

struct Z3
{
    using Node = z3::expr;
    using op_t = brq::smt_op;

    Z3( z3::context &c ) : _ctx( c ) {}

    Node unary( brq::smt_op, Node, int );
    Node extract( Node n, std::pair< int, int > );
    Node binary( brq::smt_op, Node, Node, int );

    Node constant( uint64_t value, int bw );
    Node constant( bool );
    Node constant( float );
    Node constant( double );

    Node variable( int id, brq::smt_op op );
    Node array( int id, brq::smt_array_type );

    Node load( Node array, Node offset, int bw );
    Node store( Node array, Node offset, Node value, int bw );

    z3::expr expr( Z3_ast );
    z3::sort fpa_sort( int bw );

    template< typename T >
    z3::expr make_fpa_val( T v, int bw );

    z3::context &_ctx;
};

} // namespace divine::smt::builder
#endif
