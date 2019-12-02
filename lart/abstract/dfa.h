// -*- C++ -*- (c) 2016-2019 Henrich Lauko <xlauko@mail.muni.cz>
#pragma once

DIVINE_RELAX_WARNINGS
#include <llvm/IR/Module.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/InstVisitor.h>
DIVINE_UNRELAX_WARNINGS

#include <deque>
#include <memory>
#include <brick-types>

#include <lart/abstract/util.h>
#include <lart/abstract/domain.h>

namespace lart::abstract
{
    struct tristate : brick::types::Eq
    {
        enum { no, yes, maybe } value;
        tristate( bool v ) : value( v ? yes : no ) {}
        tristate( decltype( value ) v ) : value( v ) {}
        bool operator==( const tristate &o ) const { return value == o.value; }

        template< typename stream >
        friend auto operator<<( stream &s, tristate t ) -> decltype( s << "" )
        {
            switch ( t.value )
            {
                case no: return s << "no";
                case yes: return s << "yes";
                case maybe: return s << "maybe";
            }
        }
    };

    inline tristate join( tristate a, tristate b )
    {
        if ( a.value == b.value )
            return a;
        else
            return tristate( tristate::maybe );
    }

    struct type_layer : brick::types::Eq
    {
        tristate is_pointer;
        tristate is_aggregate;
        tristate is_abstract;

        type_layer( bool p, bool g, bool a )
            : is_pointer( p ), is_aggregate( g ), is_abstract( a )
        {}

        type_layer( tristate p, tristate g, tristate a )
            : is_pointer( p ), is_aggregate( g ), is_abstract( a )
        {}

        bool operator==( const type_layer &o ) const
        {
            return std::tie( is_pointer, is_aggregate, is_abstract )
                == std::tie( o.is_pointer, o.is_aggregate, o.is_abstract );
        }

        template< typename stream >
        friend auto operator<<( stream &s, type_layer t ) -> decltype( s << "" )
        {
            return s << "ptr:" << t.is_pointer
                    << " agg:" << t.is_aggregate
                    << " abs:" << t.is_abstract;
        }
    };

    inline type_layer join( type_layer a, type_layer b )
    {
        return { join( a.is_pointer, b.is_pointer ),
                 join( a.is_aggregate, b.is_aggregate ),
                 join( a.is_abstract, b.is_abstract ) };
    }

    using type_vector = std::vector< type_layer >;

    struct type_onion : type_vector
    {
        type_onion( int ptr_nest )
            : type_vector( ptr_nest + 1, type_layer( true, false, false ) )
        {
            front() = type_layer( false, false, false );
        }

        type_onion( const type_vector &l ) : type_vector( l ) {}
        type_onion( std::initializer_list< type_layer > il ) : type_vector( il ) {}

        type_onion make_abstract() const
        {
            auto rv = *this;
            rv.back().is_abstract = true;
            return rv;
        }

        type_onion make_abstract_aggregate() const
        {
            auto rv = make_abstract();
            rv.back().is_aggregate = true;
            return rv;
        }

        bool maybe_abstract() const
        {
            tristate r( false );
            for ( auto a : *this )
                r = join( r, a.is_abstract );
            return r.value != tristate::no;
        }

        bool maybe_aggregate() const
        {
            tristate r( false );
            for ( auto a : *this )
                r = join( r, a.is_aggregate );
            return r.value != tristate::no;
        }

        bool maybe_pointer() const
        {
            tristate r( false );
            for ( auto a : *this )
                r = join( r, a.is_pointer );
            return r.value != tristate::no;
        }


        type_onion wrap() const
        {
            auto rv = *this;
            rv.emplace_back( true, false, false );
            return rv;
        }

        type_onion peel() const
        {
            auto rv = *this;
            if ( size() == 1 )
                rv.front().is_pointer = tristate::maybe;
            else
            {
                ASSERT_NEQ( back().is_pointer, tristate( false ) );
                rv.pop_back();
            }
            return rv;
        }
    };

    inline type_onion join( type_onion a, type_onion b )
    {
        if ( a.size() > b.size() )
            std::swap( a, b );

        if ( a.size() < b.size() )
        {
            for ( size_t i = 0; i < b.size() - a.size(); ++i )
                a.front() = join( a.front(), b[ i ] );
            a.front().is_pointer = tristate::maybe;
        }

        for ( size_t i = 0; i < a.size(); ++i )
            a[ i ] = join( a[ i ], b[ i + b.size() - a.size() ] );

        return a;
    }

    struct type_map
    {
        int pointer_nesting( llvm::Type *t ) const noexcept
        {
            int rv = 0;
            while ( t->isPointerTy() )
                ++ rv, t = t->getPointerElementType();
            return rv;
        }

        type_onion get( llvm::Value *v ) const noexcept
        {
            if ( _map.count( v ) )
                return _map.at( v );
            else
                return type_onion( pointer_nesting( v->getType() ) );
        }

        void set( llvm::Value *v, type_onion o )
        {
            if ( auto it = _map.find( v ); it != _map.end() )
                it->second = o;
            else
                _map.emplace( v, o );
        }

        decltype(auto) begin() { return _map.begin(); }
        decltype(auto) begin() const { return _map.begin(); }

        decltype(auto) end() { return _map.end(); }
        decltype(auto) end() const { return _map.end(); }

        void add( llvm::Value * val )
        {
            auto meta = meta::abstract::get( val );
            ASSERT( meta.has_value() );

            auto kind = meta.value();
            if ( kind == "scalar" )
                set( val, get( val ).make_abstract() );
            else if ( kind == "aggregate" )
                set( val, get( val ).make_abstract_aggregate() );
            else if ( kind == "pointer" )
                UNREACHABLE( "not implemented" );
            else
                UNREACHABLE( "unsupported abstract kind" );
        }

        static inline type_map get( llvm::Module & m )
        {
            type_map types;
            for ( auto * val : meta::enumerate( m ) )
                types.add( val );
            return types;
        }

        std::map< llvm::Value *, type_onion > _map;
    };

    template< typename Self >
    struct type_map_query : crtp< Self, type_map_query >
    {
        decltype(auto) map() const noexcept { return this->self()._types; }

        type_onion type( llvm::Value * val ) const noexcept
        {
            return map().get( val );
        }

        bool maybe_abstract( llvm::Value * val ) const noexcept
        {
            return type( val ).maybe_abstract();
        }

        bool maybe_aggregate( llvm::Value * val ) const noexcept
        {
            return type( val ).maybe_aggregate();
        }

        bool maybe_pointer( llvm::Value * val ) const noexcept
        {
            return type( val ).maybe_pointer();
        }

        type_onion wrap( llvm::Value * val ) const noexcept
        {
            return type( val ).wrap();
        }

        type_onion peel( llvm::Value * val ) const noexcept
        {
            return type( val ).peel();
        }
    };

    struct AddAbstractMetaVisitor
        : llvm::InstVisitor< AddAbstractMetaVisitor >,
          type_map_query< AddAbstractMetaVisitor >
    {
        const type_map & _types;
        static constexpr char op_prefix[] = "lart.abstract.op_";


        AddAbstractMetaVisitor( const type_map & types  )
            : _types( types )
        {}

        DomainKind kind( llvm::Value * value )
        {
            if ( maybe_aggregate( value ) )
                return DomainKind::aggregate;
            if ( maybe_pointer( value ) )
                return DomainKind::pointer;
            return DomainKind::scalar;
        }

        void add_meta( llvm::Instruction *val, const std::string &operation, DomainKind kind )
        {
            meta::abstract::set( val, to_string( kind ) );

            auto m = val->getModule();
            if ( auto op = m->getFunction( operation ) )
            {
                auto index = op->getMetadata( meta::tag::operation::index );
                val->setMetadata( meta::tag::operation::index, index );
            }
        }

        void visitStoreInst( llvm::StoreInst &store )
        {
            if ( maybe_aggregate( store.getPointerOperand() ) ) {
                auto op = std::string( op_prefix ) + "store";
                add_meta( &store, op, DomainKind::aggregate );
            } else {
                meta::set( &store, meta::tag::operation::freeze );
            }
        }

        void visitLoadInst( llvm::LoadInst &load )
        {
            if ( maybe_aggregate( load.getPointerOperand() ) ) {
                auto op = std::string( op_prefix ) + "load";
                add_meta( &load, op, DomainKind::aggregate );
            } else {
                meta::set( &load, meta::tag::operation::thaw );

                auto op = std::string( op_prefix ) + "thaw";
                add_meta( &load, op, DomainKind::scalar );
            }
        }

        void visitCmpInst( llvm::CmpInst &cmp )
        {
            auto op = std::string( op_prefix )
                    + PredicateTable.at( cmp.getPredicate() );
            add_meta( &cmp, op, kind( &cmp ) );
        }

        void visitBitCastInst( llvm::BitCastInst & ) { /* skip */ }
        void visitIntToPtrInst( llvm::IntToPtrInst & ) { /* skip */ }
        void visitPtrToIntInst( llvm::PtrToIntInst & ) { /* skip */ }

        void visitCastInst( llvm::CastInst &cast )
        {
            auto op = std::string( op_prefix )
                    + std::string( cast.getOpcodeName() );
            add_meta( &cast, op, kind( &cast ) );
        }

        void visitBinaryOperator( llvm::BinaryOperator &bin )
        {
            auto op = std::string( op_prefix )
                    + std::string( bin.getOpcodeName() );
            add_meta( &bin, op, kind( &bin ) );
        }

        void visitReturnInst( llvm::ReturnInst &ret )
        {
            meta::set( &ret, meta::tag::abstract_return );
        }

        void visitCallInst( llvm::CallInst &call )
        {
            if ( meta::abstract::has( &call ) )
                return;

            /* TODO what happens if there is more than one? */
            for ( auto fn : resolve_call( &call ) )
            {
                ASSERT( fn->hasName() );
                auto op = std::string( op_prefix ) + fn->getName().str();
                add_meta( &call, op, kind( &call ) );
            }
        }

        void visitPHINode( llvm::PHINode &phi )
        {
            meta::set( &phi, meta::tag::operation::phi );
        }

        void visitGetElementPtrInst( llvm::GetElementPtrInst &gep )
        {
            auto ptr = gep.getPointerOperand();
            if ( maybe_aggregate( ptr ) ) {
                auto op = std::string( op_prefix ) + "gep";
                add_meta( &gep, op, DomainKind::aggregate );
            }
        }

        void visitExtractValueInst( llvm::ExtractValueInst &ev )
        {
            auto op = std::string( op_prefix ) + "extractvalue";
            add_meta( &ev, op, DomainKind::aggregate );
        }

        void visitInsertValueInst( llvm::InsertValueInst &iv )
        {
            auto op = std::string( op_prefix ) + "insertvalue";
            add_meta( &iv, op, DomainKind::aggregate );
        }
    };

    struct DataFlowAnalysis : type_map_query< DataFlowAnalysis >
    {
        using Task = std::function< void() >;

        void run( llvm::Module & );

        void preprocess( llvm::Function * fn ) noexcept;

        void propagate( llvm::Value * inst ) noexcept;

        void propagate_in( llvm::Function *fn, llvm::CallSite call ) noexcept;
        void propagate_out( llvm::ReturnInst * ret ) noexcept;

        bool propagate_wrap( llvm::Value * lhs, llvm::Value * rhs ) noexcept;
        bool propagate_identity( llvm::Value * lhs, llvm::Value * rhs ) noexcept;

        void propagate_back( llvm::Argument * arg ) noexcept;

        inline void push( llvm::Value *v ) noexcept
        {
            TRACE( "push", _todo.size(), *v );
            if ( !_queued.count( v ) && !_blocked.count( v ) )
            {
                _queued.emplace( v );
                _blocked.emplace( v );
                _todo.push_back( v );
            }
        }

        bool propagate( llvm::Value *to, const type_onion& from ) noexcept;
        void add_meta( llvm::Value *value ) noexcept;

        type_map _types;
        std::deque< llvm::Value * > _todo;
        std::set< llvm::Value * > _queued, _blocked;
    };

} // namespace lart::abstract
