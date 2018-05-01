// -*- C++ -*- (c) 2018 Henrich Lauko <xlauko@mail.muni.cz>
#pragma once

DIVINE_RELAX_WARNINGS
#include <llvm/IR/Module.h>
#include <llvm/IR/Instructions.h>
DIVINE_UNRELAX_WARNINGS

#include <lart/abstract/domains/common.h>
#include <lart/abstract/domains/domains.h>
#include <lart/abstract/domains/tristate.h>
#include <lart/abstract/domains/zero.h>
#include <lart/abstract/domains/sym.h>

#include <unordered_map>

namespace lart {
namespace abstract {

struct DomainsHolder {
    using Abstraction = std::shared_ptr< Common >;

    void init( llvm::Module * m ) {
        add_domain( std::make_shared< Tristate >() );
        add_domain( std::make_shared< Symbolic >() );
        add_domain( std::make_shared< Zero >() );
        module = m;
    }

    Abstraction get( Domain dom ) {
        return domains[ dom ];
    }

    llvm::Type * type( llvm::Type *ty, Domain dom ) {
        return domains[ dom ]->type( module, ty );
    }

    void add_domain( std::shared_ptr< Common > dom );
private:
    llvm::Module *module = nullptr;
    std::unordered_map< Domain, Abstraction > domains;
};

template< typename Pass >
struct PassWithDomains : CRTP< Pass > {

    void run( llvm::Module &m ) {
        domains.init( &m );
        this->self()._run( m );
    }

protected:
    DomainsHolder domains;
};


struct InDomainDuplicate : PassWithDomains< InDomainDuplicate > {
    void _run( llvm::Module& );
private:
    void process( llvm::Instruction* );
};


struct Tainting : PassWithDomains< Tainting > {
    void _run( llvm::Module& );
private:
    llvm::Value* process( llvm::Instruction* );
};


struct UnrepStores {
    void run( llvm::Module& );
    void process( llvm::StoreInst* );
private:
    DomainsHolder domains;
};

struct Synthesize : PassWithDomains< Synthesize > {
    void _run( llvm::Module& );
    void process( llvm::CallInst* );
};

} // namespace abstract
} // namespace lart

