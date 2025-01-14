// -*- mode: C++; indent-tabs-mode: nil; c-basic-offset: 4 -*-

/*
 * (c) 2012-2016 Petr Ročkai <code@fixp.eu>
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

#include <divine/vm/program.hpp>
#include <divine/vm/eval.tpp>
#include <divine/cc/cc1.hpp>

namespace divine::t_vm
{

namespace {

auto testContext() {
    static std::shared_ptr< llvm::LLVMContext > ctx( new llvm::LLVMContext );
    return ctx;
}

auto mod2prog( std::unique_ptr< llvm::Module > m )
{
    auto p = std::make_shared< vm::Program >( llvm::DataLayout( m.get() ) );
    p->setupRR( m.get() );
    p->computeRR( m.get() );
    p->computeStatic( m.release() );
    return p;
}

template< typename Build >
auto ir2prog( Build build, std::string funcname, llvm::FunctionType *ft = nullptr )
{
    if ( !ft )
        ft = llvm::FunctionType::get( llvm::Type::getInt32Ty( *testContext() ), false );
    auto m = std::make_unique< llvm::Module >( "test.ll", *testContext() );
    auto f = llvm::cast< llvm::Function >( m->getOrInsertFunction( funcname, ft ).getCallee() );
    auto bb = llvm::BasicBlock::Create( *testContext(), "_entry", f );
    llvm::IRBuilder<> irb( bb );
    build( irb, f );
    return mod2prog( std::move( m ) );
}

auto c2prog( std::string s )
{
    divine::cc::CC1 c( testContext() );
    c.mapVirtualFile( "/main.c", s );
    return mod2prog( c.compile( "/main.c" ) );
}

}

struct Program
{
    llvm::LLVMContext ctx;
    Program() {}

    TEST( empty )
    {
        auto m = std::make_unique< llvm::Module >( "test", ctx );
        vm::Program p( llvm::DataLayout( m.get() ) );
    }

    TEST( simple )
    {
        auto m = c2prog( "int main() { return 0; }" );
    }
};

}
