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

#if OPT_STP
#include <divine/smt/builder-common.hpp>
#include <stp/STPManager/STPManager.h>

namespace stp
{
    template< typename S >
    auto &operator<<( S &stream, const ASTNode &n )
    {
        std::stringstream str;
        n.nodeprint( str );
        return stream << str.str();
    }
}

namespace divine::smt::builder
{

struct STP
{
    using Node = stp::ASTNode;
    using op_t = brq::smt_op;

    STP( stp::STPMgr &stp ) : _stp( stp ) {}

    Node unary( brq::smt_op op, Node arg, int );
    Node binary( brq::smt_op op, Node, Node, int );
    Node extract( Node, std::pair< int, int > );
    Node constant( uint64_t value, int bw );
    Node constant( int val );
    Node constant( bool );

    Node constant( float );
    Node constant( double );

    Node variable( int id, brq::smt_op op );
    Node array( int id, brq::smt_array_type array_type );

    Node load( Node array, Node offset, int bw );
    Node store( Node array, Node offset, Node value, int bw );

    stp::STPMgr &_stp;
};

} // namespace divine::smt::builder
#endif
