// -*- C++ -*- (c) 2018 Henrich Lauko <xlauko@mail.muni.cz>
#pragma once

DIVINE_RELAX_WARNINGS
#include <llvm/IR/Module.h>
#include <llvm/IR/Value.h>
DIVINE_UNRELAX_WARNINGS

#include <iostream>

#include <lart/abstract/domain.h>

namespace lart {
namespace abstract {

struct MDBuilder {
    MDBuilder( llvm::LLVMContext &ctx )
        : ctx( ctx )
    {}

    llvm::MDNode* domain_node( llvm::StringRef dom );
    llvm::MDNode* domain_node( Domain dom );
private:
    llvm::LLVMContext &ctx;
};


struct CreateAbstractMetadata {
    void run( llvm::Module &m );
};


struct MDValue {
    MDValue( llvm::Metadata * md )
        : _md( llvm::cast< llvm::ValueAsMetadata >( md ) )
    {}

    MDValue( llvm::Value * v )
        : _md( llvm::LocalAsMetadata::get( v ) )
    {}

    std::string name() const noexcept;
    llvm::Value * value() const noexcept;
    Domain domain() const noexcept;
private:
    llvm::ValueAsMetadata  *_md;
};


struct ArgMetadata {
    ArgMetadata( llvm::Metadata *data )
        : data( llvm::cast< llvm::MDNode >( data ) )
    {}

    Domain domain() const;
private:
    llvm::MDNode *data;
};


struct FunctionMetadata {
    FunctionMetadata( llvm::Function * fn )
        : fn( fn )
    {}

    void set_arg_domain( unsigned i, Domain dom );
    Domain get_arg_domain( unsigned i );

    void clear();
private:

    static constexpr char tag[] = "lart.function.domains";

    llvm::Function *fn;
};

void make_duals( llvm::Instruction *a, llvm::Instruction *b );
llvm::Value* get_dual( llvm::Instruction *i );

std::vector< MDValue > abstract_metadata( llvm::Module &m );
std::vector< MDValue > abstract_metadata( llvm::Function *fn );

void add_abstract_metadata( llvm::Instruction *inst, Domain dom );

} // namespace abstract
} // namespace lart
