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

struct GlobalMeta {
    template< typename Index >
    GlobalMeta( llvm::GlobalVariable &g, Index &index ) :
        address( &g ), size( index._dl->getTypeStoreSize(
                    llvm::cast< llvm::PointerType >( g.getType() )->getElementType() ) )
    { }

    llvm::GlobalVariable *address;
    long size;
    bool isConstant() const { return address->isConstant(); }
    llvm::StringRef name() const { return address->getName(); }
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

        auto *funcMetaT = llvm::cast< llvm::StructType >( llvm::cast< llvm::ArrayType >(
                            mdRoot->getType()->getElementType() )->getElementType() );
        ASSERT( funcMetaT && "The bitcode must define _MD_Function" );
        ASSERT( funcMetaT->getNumElements() == 11 && "Incompatible _MD_Function" );

        auto *instMetaT = llvm::cast< llvm::StructType >( llvm::cast< llvm::PointerType >(
                            funcMetaT->getElementType( 7 ) )->getElementType() );
        ASSERT( instMetaT && "The bitcode must define _MD_InstInfo" );

        llvm::GlobalVariable *mdSize = mod.getGlobalVariable( "__md_functions_count" );
        ASSERT( mdSize && "The bitcode must define __md_functions_count" );

        llvm::GlobalVariable *mdGlobals = mod.getGlobalVariable( "__md_globals" );
        ASSERT( mdGlobals && "The bitcode must define __md_globals" );

        auto *gloMetaT = llvm::cast< llvm::StructType >( llvm::cast< llvm::ArrayType >(
                            mdGlobals->getType()->getElementType() )->getElementType() );
        ASSERT( gloMetaT && "The bitcode must define _MD_Global" );
        ASSERT( gloMetaT->getNumElements() == 4 && "Incompatible _MD_Global" );

        llvm::GlobalVariable *mdGlobalsCount = mod.getGlobalVariable( "__md_globals_count" );
        ASSERT( mdGlobalsCount && "The bitcode must define __md_globals_count" );

        std::map< llvm::StringRef, FunctionMeta > funMetaMap;
        for ( auto &fn : mod ) {
            if ( fn.isIntrinsic() )
                continue;
            auto r = funMetaMap.emplace( fn.getName(), FunctionMeta( fn, *this ) );
            ASSERT( r.second );
        }

        // build metadata table
        std::vector< llvm::Constant * > metatable;
        metatable.reserve( funMetaMap.size() );
        for ( auto &m : funMetaMap ) {
            std::string funNameStr = m.second.entryPoint->getName().str();
            std::string funNameCStr = funNameStr;
            funNameCStr.push_back( 0 );

            auto *funName = util::getStringGlobal( funNameCStr, mod );
            funName->setName( "lart.divine.index.name." + funNameStr );
            auto type = m.second.type;
            type.push_back( 0 );
            auto *funType = util::getStringGlobal( type, mod );
            auto *persT = llvm::cast< llvm::PointerType >( funcMetaT->getElementType( 8 ) );
            auto *pers = m.second.entryPoint->hasPersonalityFn()
                            ? llvm::ConstantExpr::getPointerCast(
                                    m.second.entryPoint->getPersonalityFn(), persT )
                            : llvm::ConstantPointerNull::get( persT );

            auto *lsdaT = llvm::cast< llvm::PointerType >( funcMetaT->getElementType( 9 ) );
            auto *lsdam = m.second.entryPoint->getMetadata( "lart.lsda" );
            auto *lsda = lsdam
                            ? llvm::cast< llvm::ConstantAsMetadata >( lsdam->getOperand( 0 ) )->getValue()
                            : llvm::ConstantPointerNull::get( lsdaT );

            metatable.push_back( llvm::ConstantStruct::get( funcMetaT, {
                    llvm::ConstantExpr::getPointerCast( funName, funcMetaT->getElementType( 0 ) ),
                    llvm::ConstantExpr::getPointerCast( m.second.entryPoint,
                            funcMetaT->getElementType( 1 ) ),
                    mkint( funcMetaT, 2, m.second.frameSize ),
                    mkint( funcMetaT, 3, m.second.argCount ),
                    mkint( funcMetaT, 4, m.second.isVariadic ),
                    llvm::ConstantExpr::getPointerCast( funType,
                                            funcMetaT->getElementType( 5 ) ),
                    mkint( funcMetaT, 6, m.second.instTableSize ),
                    llvm::ConstantPointerNull::get( llvm::PointerType::getUnqual( instMetaT ) ),
                    pers,
                    lsda,
                    mkint( funcMetaT, 10, m.second.entryPoint->hasFnAttribute( llvm::Attribute::NoUnwind ) )
                } ) );
        }

        // insert metadata table to the module
        mdSize->setInitializer( llvm::ConstantInt::get(
                    llvm::cast< llvm::PointerType >( mdSize->getType() )->getElementType(),
                    metatable.size() ) );

        auto *mdRootT = llvm::ArrayType::get( funcMetaT, metatable.size() );
        util::replaceGlobalArray( mdRoot, llvm::ConstantArray::get( mdRootT, metatable ) );

        // now build global variable metadata
        std::map< llvm::StringRef, GlobalMeta > gloMetaMap;
        for ( auto &g : mod.globals() ) {
            if ( g.hasName() ) {
                auto r = gloMetaMap.emplace( g.getName(), GlobalMeta( g, *this ) );
                ASSERT( r.second || (g.dump(), false) );
            }
        }

        std::vector< llvm::Constant * > glometa;
        for ( auto &m : gloMetaMap ) {
            std::string name = m.second.name().str();
            name.push_back( 0 );
            auto *llvmname = util::getStringGlobal( name, mod );
            llvmname->setName( "lart.divine.index.globalname." + m.second.name().str() );

            glometa.push_back( llvm::ConstantStruct::get( gloMetaT, {
                        llvm::ConstantExpr::getPointerCast( llvmname,
                                                            gloMetaT->getElementType( 0 ) ),
                        llvm::ConstantExpr::getPointerCast( m.second.address,
                                                            gloMetaT->getElementType( 1 ) ),
                        mkint( gloMetaT, 2, m.second.size ),
                        mkint( gloMetaT, 3, m.second.isConstant() )
                    } ) );
        }

        mdGlobalsCount->setInitializer( llvm::ConstantInt::get(
                    llvm::cast< llvm::PointerType >( mdGlobalsCount->getType() )->getElementType(),
                    glometa.size() ) );
        auto *gloArrayT = llvm::ArrayType::get( gloMetaT, glometa.size() );
        util::replaceGlobalArray( mdGlobals, llvm::ConstantArray::get( gloArrayT, glometa ) );

        return llvm::PreservedAnalyses::none();
    }

    llvm::Constant *mkint( llvm::StructType *st, int i, int64_t val ) {
        return llvm::ConstantInt::get( st->getElementType( i ), val );
    }

    std::unique_ptr< llvm::DataLayout > _dl;
};

PassMeta functionMetaPass() {
    return compositePassMeta< IndexFunctions >( "functionmeta",
            "Instrument bitcode with metadata of functions for DIVINE." );
}

}
}
