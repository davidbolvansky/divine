/*
 * (c) 2020 Lukáš Korenčik <xkorenc1@fi.muni.cz>
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

#include <iostream>
#include <type_traits>
#include <unordered_map>
#include <unordered_set>
#include <vector>

DIVINE_RELAX_WARNINGS
#include <llvm/IR/Module.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IRBuilder.h>
DIVINE_UNRELAX_WARNINGS

#include <bricks/brick-assert>
#include <bricks/brick-llvm>

#include <lart/support/meta.h>
#include <lart/abstract/util.h>

namespace lart::mcsema
{

/* McSema generates entrypoints into lifted code in form of function
 * with fixed number of i64 arguments. Therefore we need to transform
 * callsites that do call these entrypoints indirectly to bitcast
 * callee to matching arity.
 */
struct libc_indirect_calls : abstract::LLVMUtil< libc_indirect_calls >
{
    llvm::Module *module;

    static constexpr const int explicit_args_count = 8;

    void run( llvm::Module &m )
    {
        module = &m;
        auto f = get_caller();

        // We did not find the function, it is possible it is not linked in
        // therefore there is not much left for us to do
        if ( !f )
            return;
        fill_arguments( *f, explicit_args_count );
    }

    // Finds indirect call in the functions and adds i64 undef arguments to it
    // up to args_size
    void fill_arguments( llvm::Function &f, uint64_t args_size )
    {
        auto indirect_calls =
            query::query( f )
            .flatten()
            .filter( []( auto &inst )
               {
                   auto *cb = llvm::dyn_cast< llvm::CallBase >( &inst );
                   return cb && cb->isIndirectCall();
               } )
            .map( []( auto &inst ){ return &inst; } )
            .freeze();

        for ( auto c_inst : indirect_calls )
        {
            auto &cb = llvm::cast< llvm::CallBase >( *c_inst );

            // It is indirect call -> called value is not function -> cannot use
            // getFunctionType() directly
            auto callee = cb.getCalledOperand();
            auto callee_p = llvm::dyn_cast< llvm::PointerType >( callee->getType() );
            auto callee_t = llvm::dyn_cast< llvm::FunctionType >(
                    callee_p->getElementType() );
            ASSERT( callee_t );

            std::vector< llvm::Type * > args{ callee_t->params() };
            for ( auto i = args.size(); i < args_size; ++i )
                args.push_back( i64Ty() );

            auto correct_type = llvm::FunctionType::get( callee_t->getReturnType(),
                                                         args, false );
            llvm::IRBuilder<> ir( c_inst );
            auto casted_callee = ir.CreateBitCast( callee, ptr( correct_type ) );

            std::vector< llvm::Value * > new_args{ cb.arg_begin(),
                                                   cb.arg_end() };
            for ( auto i = cb.arg_size(); i < args_size; ++i )
                new_args.push_back( undef( i64Ty() ) );

            auto new_call = ir.CreateCall( correct_type, casted_callee, new_args );
            c_inst->replaceAllUsesWith( new_call );
            c_inst->eraseFromParent();
        }

    }

    llvm::Function *get_caller()
    {
        return module->getFunction( "__pthread_start" );
    }

};


}// namespace lart::mcsema
