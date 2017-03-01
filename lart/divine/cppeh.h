// -*- mode: C++; indent-tabs-mode: nil; c-basic-offset: 4 -*-

/*
 * (c) 2016-2017 Vladimír Štill <xstill@fi.muni.cz>
 * (c)      2017 Petr Ročkai <code@fixp.eu>
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

/* see libcxxabi/src/cxa_personality.cpp for detailed info on LSDA layout  */

DIVINE_RELAX_WARNINGS
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/Support/Dwarf.h>
DIVINE_UNRELAX_WARNINGS
#include <brick-types>
#include <brick-query>
#include <brick-data>
#include <brick-mem>
#include <vector>
#include <set>

namespace lart {
namespace divine {

namespace dwarf = llvm::dwarf;

struct CppEhTab {

    using Actions = std::vector< llvm::Constant * >;

    struct CallSite {
        CallSite( llvm::Instruction *pc, llvm::BasicBlock *lb, Actions act, bool cleanup ) :
            invoke( pc->getParent() ), landing( lb ), actions( act ), cleanup( cleanup )
        { }

        llvm::BasicBlock *invoke, *landing;
        Actions actions;
        bool cleanup;
    };

    auto block_addr( llvm::BasicBlock *bb )
    {
        auto *intptrT = _dl.getIntPtrType( _ctx );
        if ( bb == bb->getParent()->begin() )
            return llvm::ConstantExpr::getPtrToInt( bb->getParent(), intptrT );
        return llvm::ConstantExpr::getPtrToInt( llvm::BlockAddress::get( bb ), intptrT );
    }

    explicit CppEhTab( llvm::Function &fn ) :
        _ctx( fn.getParent()->getContext() ),
        _dl( fn.getParent() ),
        _startaddr( fn.isDeclaration() ? nullptr : block_addr( fn.begin() ) )
    {
        build( fn );
    }

    void build( llvm::Function &fn )
    {
        for ( auto &i : brick::query::flatten( fn ) )
            if ( auto *invoke = llvm::dyn_cast< llvm::InvokeInst >( &i ) )
                build( invoke );
    }

    void build( llvm::InvokeInst *invoke )
    {
        llvm::BasicBlock *unw = invoke->getUnwindDest();
        auto *lp = invoke->getLandingPadInst();

        Actions actions;
        for ( int i = 0, end = lp->getNumClauses(); i < end; ++i )
            if ( lp->isCatch( i ) )
            {
                auto *ti = lp->getClause( i )->stripPointerCasts();
                addID( ti );
                actions.emplace_back( ti );
            }
            else if ( lp->isFilter( i ) )
            {
                std::vector< llvm::Constant * > filter;
                auto *clause = lp->getClause( i )->stripPointerCasts();
                iterateFilter( clause, [&]( auto *ti )
                               {
                                   addID( ti );
                                   filter.emplace_back( ti );
                               } );
                addSpec( clause );
                actions.emplace_back( clause );
            }
        _callSites.emplace_back( invoke, unw, actions, lp->isCleanup() );
    }

    using ConstVec = std::vector< llvm::Constant * >;
    using ValueVec = std::vector< llvm::Value * >;
    using ConstIL = std::initializer_list< llvm::Constant * >;

    auto const_int( llvm::Type *t, int v ) { return llvm::ConstantInt::get( t, v ); };
    auto const_struct( ConstVec v, bool p ) { return llvm::ConstantStruct::getAnon( _ctx, v, p ); };
    auto const_struct( ConstIL il, bool p ) { return const_struct( ConstVec( il ), p ); }
    auto const_str( std::string v ) { return llvm::ConstantDataArray::getString( _ctx, v, false ); };
    auto const_leb( int val, int size = -1 )
    {
        std::string str;
        pushLeb_n( str, val, size );
        return const_str( str );
    };

    llvm::Constant *getLSDAConst()
    {
        if ( _callSites.empty() )
            return nullptr;

        auto i8 = llvm::Type::getInt8Ty( _ctx ), i32 = llvm::Type::getInt32Ty( _ctx ),
            i64 = llvm::Type::getInt64Ty( _ctx );

        brick::data::RMap< llvm::Constant *, int > typeIndex;
        brick::data::RMap< const Actions *, int > actionIndex;

        ConstVec callSiteTable, typeTable;
        std::string actionTable, specifierTable;

        for ( auto *ti : _typeInfos )
            typeIndex[ ti ] = typeID( ti );

        // type infos are reversed as they are indexed by negated index
        typeTable = _typeInfos;
        std::reverse( typeTable.begin(), typeTable.end() );

        for ( auto *es : _exceptSpecs ) {
            typeIndex[ es ] = -( specifierTable.size() + 1 ); // indices start with 1 and are negativea
            iterateFilter( es, [&]( auto *ti ) { pushLeb_n( specifierTable, typeIndex[ ti ] ); } );
            pushLeb_n( specifierTable, 0, 1 ); // end of record
        }

        for ( auto &cs : _callSites ) {
            actionIndex[ &cs.actions ] = actionTable.size() + 1;
            for ( auto *h : cs.actions ) {
                ASSERT_NEQ( typeIndex[ h ], 0 );
                pushLeb_n( actionTable, typeIndex[ h ] );

                // push next action offset for this call site
                if ( h == cs.actions.back() && !cs.cleanup )
                    pushLeb_n( actionTable, 0, 1 ); // end
                else
                    pushLeb_n( actionTable, 1, 1 ); // offset is relative to the offset entry
            }
            if ( cs.cleanup ) {
                pushLeb_n( actionTable, 0, 1 ); // cleanup is id 0
                pushLeb_n( actionTable, 0, 1 ); // terminate the actions entry
            }
        }

        auto const_sub32 = [=]( llvm::Constant *a, llvm::Constant *b )
        {
            return llvm::ConstantExpr::getTrunc( llvm::ConstantExpr::getNUWSub( a, b ), i32 );
        };

        for ( auto &ci : _callSites )
            callSiteTable.emplace_back(
                const_struct(
                    { const_sub32( block_addr( ci.invoke ), _startaddr ), /* pc */
                      const_int( i32, 1 ), /* index, i32 for alignment reasons */
                      const_sub32( block_addr( ci.landing ), _startaddr ), /* relative lp address */
                      const_leb( actionIndex[ &ci.actions ], 4 ) /* action */
                    }, true ) );

        int hdr_padding = 0;
        auto lsda = [&]( int class_info_off, int call_site_table_len )
        {
            return const_struct( {
                    const_struct( { const_int( i8, dwarf::DW_EH_PE_omit ),   /* lpstart encoding */
                                    const_int( i8, dwarf::DW_EH_PE_absptr ), /* type_info encoding */
                                    const_leb( class_info_off, 4 ),
                                    const_int( i8, dwarf::DW_EH_PE_udata4 ), /* call site encoding */
                                    const_leb( call_site_table_len, 4 + hdr_padding ) }, true ),
                    const_struct( { const_struct( callSiteTable, true ),
                                    const_str( actionTable ),
                                    const_struct( typeTable, false ),
                                    const_str( specifierTable ) }, false ) }, true );
        };

        auto offset = [&]( int idx1, int idx2 ) -> int
        {
            auto t = lsda( 0, 0 )->getType();
            ValueVec idx{ const_int( i64, 0 ), const_int( i32, idx1 ), const_int( i32, idx2 ) };
            return _dl.getIndexedOffset( llvm::PointerType::get( t, 0 ), idx );
        };

        int hdr_size = offset( 1, 0 );
        hdr_padding = brick::bitlevel::align( hdr_size, 8 ) - hdr_size;

        return lsda( offset( 1, 3 ) - offset( 0, 3 ), offset( 1, 1 ) - offset( 1, 0 ) );
    }

    static void pushLeb_n( std::string &str, int32_t data, int n = -1 )
    {
        if ( n < 0 && data < 0 ) n = 4;
        if ( n < 0 ) n = std::max( (brick::bitlevel::MSB( data ) + 6) / 7, 1u );

        ASSERT_LEQ( data, (1 << (4 * 7)) - 1 ); // maximum value which fits 4 bytes
        // taken and modified from LLVM
        int todo = n;
        do {
            uint8_t byte = data & 0x7f;
            // NOTE: this assumes that this signed shift is an arithmetic right shift.
            data >>= 7;
            if ( --todo > 0 )
                byte |= 0x80; // Mark this byte to show that more bytes will follow.
            str.push_back( byte );
        } while ( todo > 0 );
    }

    int typeID( llvm::Constant *c ) {
        auto it = std::find( _typeInfos.begin(), _typeInfos.end(), c );
        return it == _typeInfos.end() ? 0 : it - _typeInfos.begin() + 1;
    }

    void addID( llvm::Constant *ti ) {
        if ( !typeID( ti ) )
            _typeInfos.emplace_back( ti );
    }

    void addSpec( llvm::Constant *spec ) {
        auto it = std::find( _exceptSpecs.begin(), _exceptSpecs.end(), spec );
        if ( it == _exceptSpecs.end() )
            _exceptSpecs.emplace_back( spec );
    }

    template< typename Yield >
    void iterateFilter( llvm::Constant *clause, Yield yield )
    {
        if( auto *array = llvm::dyn_cast< llvm::ConstantArray >( clause ) )
        {
            auto cnt = array->getType()->getNumElements();
            for ( unsigned j = 0; j < cnt; ++j )
                yield( array->getOperand( j )->stripPointerCasts() );
        }
        else if ( llvm::isa< llvm::ConstantAggregateZero >( clause ) )
        {
            /* throw () */
        }
        else {
            clause->dump();
            UNREACHABLE( "Unexpected landingpad clause type" );
        }
    }

    llvm::LLVMContext &_ctx;
    llvm::DataLayout _dl;
    llvm::Constant *_startaddr;

    std::vector< CallSite > _callSites;
    ConstVec _typeInfos, _exceptSpecs;
};

}
}
