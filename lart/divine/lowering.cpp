// -*- C++ -*- (c) 2016 Vladimír Štill <xstill@fi.muni.cz>

DIVINE_RELAX_WARNINGS
#include <llvm/IR/Module.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/CodeGen/IntrinsicLowering.h>
DIVINE_UNRELAX_WARNINGS

#include <lart/support/pass.h>
#include <lart/support/meta.h>
#include <lart/support/query.h>
#include <lart/divine/cppeh.h>

namespace lart {
namespace divine {

struct LowerLLVM : lart::Pass {

    static PassMeta meta() {
        return passMeta< LowerLLVM >( "LowerLLVM", "Lower LLVM intrinsics." );
    }

    using lart::Pass::run;
    llvm::PreservedAnalyses run( llvm::Module &m ) override {

        llvm::IntrinsicLowering il( m.getDataLayout() );

        for ( auto &fn : m ) {
            auto toLower = query::query( fn ).flatten()
                            .map( query::refToPtr )
                            .map( query::llvmdyncast< llvm::IntrinsicInst > )
                            .filter( []( auto *x ) { return x && !keepForDIVINE( x->getIntrinsicID() ); } )
                            .freeze();
            for ( auto *call : toLower )
                il.LowerIntrinsicCall( call );
        }

        return llvm::PreservedAnalyses::none();
    }

    static bool keepForDIVINE( llvm::Intrinsic::ID id ) {
        switch ( id ) {
            case llvm::Intrinsic::eh_typeid_for:
            case llvm::Intrinsic::trap:
            case llvm::Intrinsic::vastart:
            case llvm::Intrinsic::vacopy:
            case llvm::Intrinsic::vaend:
            case llvm::Intrinsic::stacksave:
            case llvm::Intrinsic::stackrestore:
            case llvm::Intrinsic::umul_with_overflow:
            case llvm::Intrinsic::smul_with_overflow:
            case llvm::Intrinsic::uadd_with_overflow:
            case llvm::Intrinsic::sadd_with_overflow:
            case llvm::Intrinsic::usub_with_overflow:
            case llvm::Intrinsic::ssub_with_overflow:
            case llvm::Intrinsic::dbg_declare:
            case llvm::Intrinsic::dbg_value:
                return true;
            default:
                return false;
        }
    }

};

struct LowerEH : lart::Pass {

    static PassMeta meta() {
        return passMeta< LowerEH >( "LowerEH", "Lower resume instruction to _Unwind_Resume." );
    }

    using lart::Pass::run;
    llvm::PreservedAnalyses run( llvm::Module &m ) override {
        auto *resumeFn = m.getFunction( "_Unwind_Resume" );
        if ( !resumeFn )
            return llvm::PreservedAnalyses::all();
        auto *resumeFnT = resumeFn->getFunctionType();
        ASSERT_EQ( resumeFnT->getNumParams(), 1 );
        auto *exceptT = resumeFnT->getParamType( 0 );

        for ( auto &fn : m ) {
            for ( auto *r : query::query( fn ).flatten()
                                .map( query::refToPtr )
                                .map( query::llvmdyncast< llvm::ResumeInst > )
                                .filter( query::notnull ).freeze() )
            {
                llvm::IRBuilder<> irb( r );
                auto *ehtuple = r->getValue();
                auto *except = irb.CreateExtractValue( ehtuple, 0 );
                ASSERT( llvm::isa< llvm::PointerType >( except->getType() ) );
                auto *call = irb.CreateCall( resumeFn,
                                { irb.CreatePointerCast( except, exceptT, "exception" ) } );
                r->replaceAllUsesWith( call );
                irb.CreateUnreachable();
                r->eraseFromParent();
            }
            lart::divine::CppEhTab tab( fn );
            for ( auto *id : query::query( fn ).flatten()
                              .map( query::refToPtr )
                              .map( query::llvmdyncast< llvm::IntrinsicInst > )
                              .filter( []( auto *x ) { return x && x->getIntrinsicID() == llvm::Intrinsic::eh_typeid_for; } )
                              .freeze() )
            {
                auto *arg = id->getArgOperand( 0 )->stripPointerCasts();
                int i = 1;
                bool found = false;
                for ( auto &it : tab.typeInfos ) {
                    if ( it.self == arg ) {
                        found = true;
                        break;
                    }
                    i++;
                }
                ASSERT( found );
                auto *val = llvm::ConstantInt::get( id->getType(), i );
                id->replaceAllUsesWith( val );
                id->eraseFromParent();
            }
        }
        return llvm::PreservedAnalyses::none();
    }

};

PassMeta lowering() {
    return compositePassMeta< LowerLLVM, LowerEH >( "lowering",
            "Lower exception handling and LLVM intrinsics for the use in DIVINE." );
}

}
}
