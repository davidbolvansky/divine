// -*- mode: C++; indent-tabs-mode: nil; c-basic-offset: 4 -*-

/*
 * (c) 2017 Petr Ročkai <code@fixp.eu>
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

#include <divine/vm/dbg-info.hpp>

namespace divine::vm::dbg
{

std::pair< llvm::StringRef, int > fileline( const llvm::Instruction &insn )
{
    auto loc = insn.getDebugLoc().get();
    if ( loc && loc->getNumOperands() )
        return std::make_pair( loc->getFilename(),
                               loc->getLine() );
    auto prog = llvm::getDISubprogram( insn.getParent()->getParent() );
    if ( prog )
        return std::make_pair( prog->getFilename(),
                               prog->getScopeLine() );
    return std::make_pair( "", 0 );
}

std::string location( const llvm::Instruction &insn )
{
    return location( fileline( insn ) );
}

std::string location( std::pair< llvm::StringRef, int > fl )
{
    if ( fl.second )
        return fl.first.str() + ":" + brick::string::fmt( fl.second );
    return "(unknown location)";
}

}
