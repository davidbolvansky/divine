// -*- mode: C++; indent-tabs-mode: nil; c-basic-offset: 4 -*-

/*
 * (c) 2016-2017 Petr Ročkai <code@fixp.eu>
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

#include <divine/vm/context.hpp>

namespace divine::sim
{

vm::Choice parse_choice( std::string s )
{
    auto i = s.find( '/' );
    if ( i == std::string::npos )
        throw std::runtime_error( "unexpected choice format: " + s );
    return vm::Choice( std::stoi( std::string( s, 0, i ) ),
                       std::stoi( std::string( s, i + 1, std::string::npos ) ) );
}

vm::Interrupt parse_interrupt( std::string s )
{
    auto i = s.find( '/' ), p = s.rfind( '/' );
    if ( i == std::string::npos || p == std::string::npos )
        throw std::runtime_error( "unexpected interrupt format: " + s );
    std::string type( s, 0, i ), ictr( s, i + 1, p ), pc( s, p + 1, std::string::npos );
    auto c = pc.find( ':' );
    if ( c == std::string::npos )
        throw std::runtime_error( "unexpected program counter format: " + pc );
    vm::Interrupt res;

    if ( type == "M" )
        res.type = vm::Interrupt::Mem;
    else if ( type == "C" )
        res.type = vm::Interrupt::Cfl;
    else
        throw std::runtime_error( "unexpected interrupt type: " + type );

    res.ictr = std::stoi( ictr );
    res.pc.function( std::stoi( std::string( pc, 0, c ) ) );
    res.pc.instruction( std::stoi( std::string( pc, c + 1, std::string::npos ) ) );

    return res;
}

}
