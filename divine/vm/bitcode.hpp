// -*- mode: C++; indent-tabs-mode: nil; c-basic-offset: 4 -*-

/*
 * (c) 2015 Petr Ročkai <code@fixp.eu>
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
#include <brick-types>
#include <brick-except>

#include <memory>
#include <vector>

DIVINE_RELAX_WARNINGS
#include <llvm/IR/LLVMContext.h>
DIVINE_UNRELAX_WARNINGS

#include <divine/cc/clang.hpp>

namespace llvm {
class LLVMContext;
class Module;
}

namespace divine {
namespace vm {

struct Program;

enum class AutoTrace { Nothing, Calls };
using AutoTraceFlags = brick::types::StrongEnumFlags< AutoTrace >;

struct BCParseError : brick::except::Error { using brick::except::Error::Error; };

struct BitCode {
    std::shared_ptr< llvm::LLVMContext > _ctx; // the order of these members is important as
    std::unique_ptr< llvm::Module > _module;   // _program depends on _module which depends on _ctx
    std::unique_ptr< Program > _program;       // and they have to be destroyed in the right order
                                               // otherwise DIVINE will SEGV if exception is thrown
    using Env = std::vector< std::tuple< std::string, std::vector< uint8_t > > >;

    AutoTraceFlags _autotrace;
    bool _reduce = false;
    Env _env;
    std::vector< std::string > _lart;

    Program &program() { ASSERT( _program.get() ); return *_program.get(); }

    BitCode( std::string file );
    BitCode( std::unique_ptr< llvm::Module > m,
             std::shared_ptr< llvm::LLVMContext > ctx = nullptr );

    void autotrace( AutoTraceFlags fl ) { _autotrace = fl; }
    void reduce( bool r ) { _reduce = r; }
    void environment( Env env ) { _env = env; }
    void lart( std::vector< std::string > passes = {} ) { _lart = passes; }

    void init( bool verbose );
    ~BitCode();
};

}

namespace t_vm {

namespace {
auto c2bc( std::string s )
{
    static std::shared_ptr< llvm::LLVMContext > ctx( new llvm::LLVMContext );
    divine::cc::Compiler c( ctx );
    c.mapVirtualFile( "main.c", s );
    return std::make_shared< vm::BitCode >( c.compileModule( "main.c" ), ctx );
}
}

}

}
