// -*- C++ -*- (c) 2018 Henrich Lauko <xlauko@mail.muni.cz>
#include <lart/abstract/util.h>

DIVINE_RELAX_WARNINGS
#include <llvm/IR/Type.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/lib/IR/LLVMContextImpl.h>
DIVINE_UNRELAX_WARNINGS

#include <unordered_map>
#include <brick-llvm>
#include <brick-string>

namespace lart::abstract
{
    std::string llvm_name( llvm::Type * type ) {
        std::string buffer;
        llvm::raw_string_ostream rso( buffer );
        type->print( rso );
        return rso.str();
    }

    llvm::Type* abstract_type( llvm::Type * orig, Domain dom ) {
        std::string name;
        if ( dom == Domain::Tristate() )
            name = "lart." + dom.name();
        else
            name = "lart." + dom.name() + "." + llvm_name( orig );

        if ( auto aty = orig->getContext().pImpl->NamedStructTypes.lookup( name ) )
            return aty;
        return llvm::StructType::create( { orig }, name );
    }

    // Tries to find precise set of possible called functions.
    // Returns true if it succeeded.
    bool potentialy_called_functions( llvm::Value * called, Functions & fns ) {
        bool surrender = true;
        llvmcase( called,
            [&] ( llvm::Function * fn ) {
                fns.push_back( fn );
            },
            [&] ( llvm::PHINode * phi ) {
                for ( auto & iv : phi->incoming_values() ) {
                    if ( ( surrender = potentialy_called_functions( iv.get(), fns ) ) )
                        break;
                }
            },
            [&] ( llvm::LoadInst * ) { surrender = true; }, // TODO
            [&] ( llvm::Argument * ) { surrender = true; },
            [&] ( llvm::Value * val ) {
                UNREACHABLE( "Unknown parent instruction:", val );
            }
        );

        return !surrender;
    }

    std::vector< llvm::Function * > get_potentialy_called_functions( llvm::CallInst* call ) {
        auto val = call->getCalledValue();
        if ( auto fn = llvm::dyn_cast< llvm::Function >( val ) )
            return { fn };
        else if ( auto ce = llvm::dyn_cast< llvm::ConstantExpr >( val ) )
            return { llvm::cast< llvm::Function >( ce->stripPointerCasts() ) };

        auto m = call->getModule();
        auto type = call->getCalledValue()->getType();

        if ( !llvm::isa< llvm::Argument >( call->getCalledValue() ) ) {
            Functions fns;
            if ( potentialy_called_functions( call->getCalledValue(), fns) ) {
                return fns;
            }
        }

        // brute force all possible functions with correct signature
        return query::query( m->functions() )
            .filter( [type] ( auto & fn ) { return fn.getType() == type; } )
            .filter( [] ( auto & fn ) { return fn.hasAddressTaken(); } )
            .map( query::refToPtr )
            .freeze();
    }

    llvm::Function * get_some_called_function( llvm::CallInst * call ) {
        return get_potentialy_called_functions( call ).front();
    }

    bool is_terminal_intruction( llvm::Value * val ) {
        return llvm::isa< llvm::ReturnInst >( val ) ||
               llvm::isa< llvm::UnreachableInst >( val );
    }

} // namespace lart::abstract
