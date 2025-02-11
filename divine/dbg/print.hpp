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

#include <divine/vm/pointer.hpp>
#include <divine/vm/program.hpp>
#include <divine/vm/eval.hpp>
#include <divine/dbg/info.hpp>
#include <divine/rt/runtime.hpp>

DIVINE_RELAX_WARNINGS
#include <llvm/IR/Instructions.h>
DIVINE_UNRELAX_WARNINGS

#include <cxxabi.h>
#include <brick-fs>
#include <regex>

namespace divine::dbg::print
{

namespace lx = vm::lx;

static void pad( std::ostream &o, int &col, int target )
{
    while ( col < target )
        ++col, o << " ";
}

template< typename B >
void hexbyte( std::ostream &o, int &col, int index, B byte )
{
    o << std::setw( 2 ) << std::setfill( '0' ) << std::setbase( 16 ) << +byte;
    col += 2;
    if ( index % 2 == 1 )
        ++col, o << " ";
}

enum class DisplayVal { Name, Value, PreferName };

template< typename Ctx >
struct Print
{
    using Eval = vm::Eval< Ctx >;

    Eval &eval;
    Info &dbg;

    Print( Info &i, Eval &e ) : eval( e ), dbg( i ) {}

    std::string value( llvm::Value *val, DisplayVal disp = DisplayVal::PreferName );
    std::string dbginst( llvm::Instruction *I );
    std::string instruction( int padding = 0, int colmax = 80 );
};

template< typename Heap >
std::string raw( Heap &heap, vm::HeapPointer hloc, int sz );

static std::string demangle( std::string mangled )
{
    int stat;
    auto x = abi::__cxa_demangle( mangled.c_str(), nullptr, nullptr, &stat );
    auto ret = stat == 0 && x ? std::string( x ) : mangled;
    std::free( x );
    return ret;
}

template< typename Program, typename PP >
static std::string source( dbg::Info &dbg, llvm::DISubprogram *di, Program &program, vm::CodePointer pc,
                           PP postproc )
{
    brq::string_builder out;

    std::string src( rt::source( di->getFilename().str() ) );
    if ( src.empty() )
        src = brq::read_file( di->getFilename().str() );

    auto split_src = brq::splitter( src, '\n' );
    auto line = split_src.begin();
    unsigned lineno = 1, active = 0;
    while ( lineno < di->getLine() )
        ++ line, ++ lineno;
    unsigned endline = lineno;

    vm::CodePointer iter( pc.function(), 0 );

    /* figure out the source code span the function covers; painfully */
    for ( iter = program.nextpc( iter ); program.valid( iter ); iter = program.advance( iter ) )
    {
        if ( program.instruction( iter ).opcode == lx::OpArg ) continue;
        auto di = dbg.find( nullptr, iter ).first;
        auto dl = di ? di->getDebugLoc().get() : nullptr;
        if ( !dl )
            continue;
        while ( dl->getInlinedAt() )
            dl = dl->getInlinedAt();
        if ( iter >= pc && dl && !active )
            active = dl->getLine();
        endline = std::max( endline, dl->getLine() );
    }

    unsigned startline = lineno;
    brq::string_builder raw;

    /* print it */
    while ( line != split_src.end() && lineno++ <= endline )
        raw << *line++ << "\n";

    if ( line != split_src.end() )
    {
        std::regex endbrace( "^[ \t]*}", std::regex::extended );
        if ( std::regex_search( std::string( *line ), endbrace ) )
            ++lineno, raw << *line++ << "\n";
    }

    std::string txt = postproc( raw.buffer() );
    auto split_fun = brq::splitter( txt, '\n' );
    auto line_fun = split_fun.begin();
    endline = lineno;
    lineno = startline;

    while ( line_fun != split_fun.end() && lineno <= endline )
    {
        out << (lineno == active ? ">>" : "  ");
        out << brq::pad( 5 ) << lineno++ << brq::mark << " " << *line_fun++ << "\n";
    }

    return std::string( out.data() );
}

}

namespace divine::dbg
{

    template< typename Eval >
    using Print = print::Print< typename Eval::Context >;

    template< typename Eval >
    auto printer( Info &i, Eval &e ) { return Print< Eval >( i, e ); }

}
