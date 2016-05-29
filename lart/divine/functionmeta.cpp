// -*- C++ -*- (c) 2016 Vladimír Štill <xstill@fi.muni.cz>

DIVINE_RELAX_WARNINGS
#include <llvm/Pass.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
DIVINE_UNRELAX_WARNINGS

#include <brick-string>
#include <string>
#include <iostream>

#include <lart/support/pass.h>
#include <lart/support/meta.h>
#include <lart/support/query.h>
#include <lart/support/util.h>
#include <lart/support/metadata.h>

// used to calculate frame size & encode function types
#include <runtime/divine.h>
#include <runtime/native/vm.h>
#include <runtime/divine/metadata.h>

namespace lart {
namespace divine {

char encLLVMBasicType( llvm::Type *t ) {
    if ( t->isVoidTy() )
        return metadata::TypeSig::encodeOne< void >;
    if ( t->isPointerTy() )
        return metadata::TypeSig::encodeOne< void * >;
    if ( auto *it = llvm::dyn_cast< llvm::IntegerType >( t ) )
        return metadata::TypeSig::encodeIntTy( it->getBitWidth() );
    return metadata::TypeSig::unknownType;
}

std::string encLLVMFunType( llvm::FunctionType *ft ) {
    std::string enc;
    enc.push_back( encLLVMBasicType( ft->getReturnType() ) );
    for ( auto t : ft->params() )
        enc.push_back( encLLVMBasicType( t ) );
    return enc;
}

struct FunctionMeta {
    template< typename Index >
    explicit FunctionMeta( llvm::Function &fn, Index &index ) :
        entryPoint( &fn ),
        frameSize( sizeof( _VM_Frame ) + argsSize( fn, index ) + sizeof( nativeRuntime::FrameEx ) ), // re-filed by the loader
        argCount( fn.arg_size() ),
        isVariadic( fn.isVarArg() ),
        type( encLLVMFunType( fn.getFunctionType() ) ),
        // divine has 1 pc value for every instruction + one special at the
        // beginning of each basic block
        instTableSize( query::query( fn ).fold( 0,
                        []( int x, llvm::BasicBlock &bb ) { return x + bb.size() + 1; } ) )
    { }

    template< typename Index >
    static int argsSize( llvm::Function &fn, Index &index ) {
        auto tys = fn.getFunctionType()->params();
        return std::accumulate( tys.begin(), tys.end(), 0, [&]( int accum, llvm::Type *t ) {
                return accum + index._dl->getTypeStoreSize( t );
            } );
    }

    llvm::Function *entryPoint;
    int frameSize;
    int argCount;
    bool isVariadic;
    std::string type;
    int instTableSize;
};

struct IndexFunctions : lart::Pass {

    static PassMeta meta() {
        return passMeta< IndexFunctions >( "IndexFunctions", "Create function metadata tables" );
    }

    using lart::Pass::run;
    llvm::PreservedAnalyses run( llvm::Module &mod ) override {
        if ( !tagModuleWithMetadata( mod, "lart.divine.index.functions" ) )
            return llvm::PreservedAnalyses::all();

        _dl = std::make_unique< llvm::DataLayout >( &mod );

        llvm::GlobalVariable *mdRoot = mod.getGlobalVariable( "__md_functions" );
        ASSERT( mdRoot && "The bitcode must define __md_functions" );

        _funcMetaT = llvm::cast< llvm::StructType >( llvm::cast< llvm::ArrayType >(
                            mdRoot->getType()->getElementType() )->getElementType() );
        ASSERT( _funcMetaT && "The bitcode must define _MD_Function" );
        ASSERT( _funcMetaT->getNumElements() == 10 && "Incompatible _MD_Function" );

        _instMetaT = llvm::cast< llvm::StructType >( llvm::cast< llvm::PointerType >(
                            _funcMetaT->getElementType( 7 ) )->getElementType() );
        ASSERT( _instMetaT && "The bitcode must define _MD_InstInfo" );

        llvm::GlobalVariable *mdSize = mod.getGlobalVariable( "__md_functions_count" );
        ASSERT( mdSize && "The bitcode must define __md_functions_count" );

        for ( auto &fn : mod ) {
            if ( fn.isIntrinsic() )
                continue;
            auto r = _meta.emplace( fn.getName(), FunctionMeta( fn, *this ) );
            ASSERT( r.second );
        }

        // build metadata table
        std::vector< llvm::Constant * > metatable;
        metatable.reserve( _meta.size() );
        for ( auto &m : _meta ) {
            std::string funNameStr = m.second.entryPoint->getName().str();
            std::string funNameCStr = funNameStr;
            funNameCStr.push_back( 0 );

            auto *instArrayT = llvm::ArrayType::get( _instMetaT, m.second.instTableSize );
            auto *instTable = new llvm::GlobalVariable( mod, instArrayT, true,
                                llvm::GlobalValue::ExternalLinkage,
                                llvm::UndefValue::get( instArrayT ),
                                "lart.divine.index.table." + funNameStr );

            auto *funName = util::getStringGlobal( funNameCStr, mod );
            funName->setName( "lart.divine.index.name." + funNameStr );
            auto type = m.second.type;
            type.push_back( 0 );
            auto *funType = util::getStringGlobal( type, mod );
            auto *persT = llvm::cast< llvm::PointerType >( _funcMetaT->getElementType( 8 ) );
            auto *pers = m.second.entryPoint->hasPersonalityFn()
                            ? llvm::ConstantExpr::getPointerCast(
                                    m.second.entryPoint->getPersonalityFn(), persT )
                            : llvm::ConstantPointerNull::get( persT );
            auto *lsdaT = llvm::cast< llvm::PointerType >( _funcMetaT->getElementType( 9 ) );
            auto *lsda = llvm::ConstantPointerNull::get( lsdaT );

            metatable.push_back( llvm::ConstantStruct::get( _funcMetaT, {
                    llvm::ConstantExpr::getPointerCast( funName, _funcMetaT->getElementType( 0 ) ),
                    llvm::ConstantExpr::getPointerCast( m.second.entryPoint,
                            _funcMetaT->getElementType( 1 ) ),
                    mkint( _funcMetaT, 2, m.second.frameSize ),
                    mkint( _funcMetaT, 3, m.second.argCount ),
                    mkint( _funcMetaT, 4, m.second.isVariadic ),
                    llvm::ConstantExpr::getPointerCast( funType,
                                            _funcMetaT->getElementType( 5 ) ),
                    mkint( _funcMetaT, 6, m.second.instTableSize ),
                    llvm::ConstantExpr::getPointerCast( instTable,
                            llvm::PointerType::getUnqual( _instMetaT ) ),
                    pers, lsda
                } ) );
        }

        // insert metadata table to the module
        mdSize->setInitializer( llvm::ConstantInt::get(
                    llvm::cast< llvm::PointerType >( mdSize->getType() )->getElementType(),
                    metatable.size() ) );

        auto *mdRootT = llvm::ArrayType::get( _funcMetaT, metatable.size() );
        util::replaceGlobalArray( mdRoot, llvm::ConstantArray::get( mdRootT, metatable ) );

        return llvm::PreservedAnalyses::none();
    }

    llvm::Constant *mkint( llvm::StructType *st, int i, int64_t val ) {
        return llvm::ConstantInt::get( st->getElementType( i ), val );
    }

    std::map< llvm::StringRef, FunctionMeta > _meta;
    llvm::StructType *_funcMetaT;
    llvm::StructType *_instMetaT;
    std::unique_ptr< llvm::DataLayout > _dl;
};

PassMeta functionMetaPass() {
    return compositePassMeta< IndexFunctions >( "functionmeta",
            "Instrument bitcode with metadata of functions for DIVINE." );
}

}
}
