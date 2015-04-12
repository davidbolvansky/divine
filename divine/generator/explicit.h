// -*- C++ -*- (c) 2013,2015 Vladimír Štill <xstill@fi.muni.cz>

#if GEN_EXPLICIT

#include <functional>
#include <brick-types.h>
#include <brick-assert.h>
#include <divine/generator/common.h>
#include <divine/explicit/explicit.h>
#include <divine/graph/probability.h>

#undef Yield

#ifndef DIVINE_GENERATOR_COMPACT_H
#define DIVINE_GENERATOR_COMPACT_H

namespace divine {
namespace generator {

using brick::types::Unit;

namespace {
    template< typename Label >
    static inline void showLabel( std::stringstream &ss, const Label &l ) {
        ss << " [ " << l << " ]";
    }

    template<>
    inline void showLabel< Unit >( std::stringstream &, const Unit & ) { }
}

template< typename _Label >
struct _Explicit : public Common< Blob > {

    using IsExplicit = Unit;

    using Node = Blob;
    using Label = _Label;
    using Common = generator::Common< Blob >;

    struct EdgeSpec : public std::tuple< int64_t, Label > {
        int64_t node() { return std::get< 0 >( *this ); };
        Label label() { return std::get< 1 >( *this ); };

        EdgeSpec() = default;
        EdgeSpec( Node n, Label l ) : std::tuple< Node, Label >( n, l ) { }
    };

    brick::data::SmallVector< short > goalFlags;

    dess::Capabilities capabilities() {
        return dess.header->capabilities;
    }

    std::string explicitInfo() {
        return "DESS (DIVINE Explicit State Space) version "
            + std::to_string( dess.header->compactVersion ) + "\n"
            + "Saved features: " + std::to_string( capabilities() );
    }

    int64_t &index( Node n ) {
        return this->pool().template get< int64_t >( n, this->slack() );
    }

    void read( std::string file, std::vector< std::string > /* definitions */,
            _Explicit *c = nullptr )
    {
        if ( c )
            dess = c->dess;
        else {
            dess.open( file );
            if ( dess.stateFlags.flagCount >= 1 &&
                    dess.stateFlags.map()[ 0 ] != "o:accepting" )
                std::cerr << "WARNING: unexpected value of reserved flag 0 "
                          << "(expected 'o:accepting', found '"
                          << dess.stateFlags.map()[ 0 ] << "')" << std::endl;
        }
    }

    template< typename Alloc, typename Yield >
    void successors( Alloc alloc, Node from, Yield yield ) {
        ASSERT( this->pool().valid( from ) );
        _successors( alloc, index( from ), yield );
    }

    template< typename Alloc, typename Yield >
    void initials( Alloc alloc, Yield yield ) {
        _successors( alloc, 0, std::bind( yield, Node(),
                    std::placeholders::_1, std::placeholders::_2 ) );
    }

    template< typename Yield >
    void enumerateFlags( Yield yield ) {
        for ( int i = 0; i < dess.stateFlags.flagCount; ++i )
            if ( !dess.stateFlags.map()[ i ].empty() ) {
                auto f = graph::flags::parseFlagName( dess.stateFlags.map()[ i ] );
                yield( f.first, i, f.second );
            }
    }

    template< typename QueryFlags >
    graph::FlagVector stateFlags( Node n, QueryFlags flags ) {
        graph::FlagVector out;
        uint64_t nf = dess.stateFlags[ index( n ) ];
        for ( auto f : flags ) {
            if ( f >= 0 && (nf & (1 << f)) )
                out.emplace_back( f );
            else if ( f == graph::flags::goal )
                for ( auto gf : goalFlags )
                    if ( nf & (1 << gf) )
                        out.emplace_back( gf );
        }
        return out;
    }

    std::string showNode( Node n ) {
        std::stringstream ss;
        ss << index( n );
        return ss.str();
    }

    std::string showTransition( Node from, Node to, Label l ) {
        std::stringstream ss;
        ASSERT( this->pool().valid( to ) );
        if ( this->pool().valid( from ) )
            ss << index( from ) << " -> " << index( to );
        else
            ss << "-> " << index( to );
        showLabel( ss, l );
        return ss.str();
    }

    template< typename Alloc >
    void release( Alloc alloc, Node s ) { alloc.drop( pool(), s ); }

    void useProperties( PropertySet s ) {
        auto flmap = graph::flags::flagMap( *this );

        for ( auto p : s ) {
            if ( p == "deadlock" )
                continue;
            if ( p == "safety" ) {
                for ( auto pair : flmap.left() )
                    if ( pair.second[ 0 ] == 'G' )
                        goalFlags.emplace_back( pair.first );
            } else if ( p == "goals" ) {
                for ( auto pair : flmap.left() )
                    if ( pair.second[ 0 ] == 'G' || pair.second[ 0 ] == 'g' )
                        goalFlags.emplace_back( pair.first );
            } else if ( flmap.right().count( p ) )
                goalFlags.emplace_back( flmap[ p ] );
            else
                throw std::logic_error( "Invalid property " + p );
        }
    }

    template< typename Yield >
    void properties( Yield yield ) {
        yield( "deadlock", "deadlock freedom", PT_Deadlock );
        yield( "safety", "unreachability of all G:* flags", PT_Goal );
        yield( "goals", "unreachability of all G:* and g:* flags", PT_Goal );
        enumerateFlags( [&]( std::string name, int, graph::flags::Type t ) {
                auto fname = graph::flags::flagName( name, t );
                yield( fname, "unreachability of " + fname + " flag", PT_Goal );
            } );
    }

  private:
    template< typename Alloc, typename Yield >
    void _successors( Alloc alloc, int64_t ix, Yield yield ) {
        dess.forward.map< EdgeSpec >( ix )( [&]( EdgeSpec *succs, int64_t cnt ) {
                for ( int64_t i = 0; i < cnt; ++i )
                    yield( _mkNode( alloc, succs[ i ].node() ), succs[ i ].label() );
            } );
    }

    template< typename Alloc >
    Node _mkNode( Alloc alloc, int64_t ix ) {
        Node n = this->makeBlobCleared( alloc, sizeof( int64_t ) );
        index( n ) = ix;
        return n;
    }

    dess::Explicit dess;
};

using Explicit = _Explicit< Unit >;
using ProbabilisticExplicit = _Explicit< graph::Probability >;

}
}

#endif // DIVINE_GENERATOR_COMPACT_H
#endif
