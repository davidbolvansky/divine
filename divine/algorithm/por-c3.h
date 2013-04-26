// -*- C++ -*- (c) 2009 Petr Rockai <me@mornfall.net>

#include <divine/algorithm/common.h>
#include <divine/graph/por.h>

#ifndef DIVINE_ALGORITHM_POR_C3_H
#define DIVINE_ALGORITHM_POR_C3_H

namespace divine {
namespace algorithm {

// Implements a (parallel) check of the POR cycle proviso.
template< typename G, typename Store, typename Statistics >
struct PORGraph : graph::Transform< G > {
    typedef PORGraph< G, Store, Statistics > This;
    typedef typename G::Node Node;
    typedef typename G::Label Label;
    typedef typename Store::Vertex Vertex;
    typedef typename Store::VertexId VertexId;
    typedef typename Store::QueueVertex QueueVertex;

    struct IdCompare {
        bool operator()( VertexId a, VertexId b) {
            return a.weakId() < b.weakId();
        }
    };

    int m_algslack;

    struct Extension {
        int predCount:29;
        bool full:1;
        bool done:1;
        bool remove:1;
    };

    typedef void (*PredCount)( Pool&, VertexId, int );
    PredCount _predCount;

    BlobComparerLT bcomp;
    std::set< VertexId, IdCompare > to_expand;
    bool finished;

    void updatePredCount( Vertex t, int v, int* pc ) {
        extension( t ).predCount = v;
        if ( pc )
            *pc = v;
    }

    void updatePredCount( Vertex t, int v ) {
        updatePredCount( t.getVertexId(), v );
    }

    void updatePredCount( VertexId t, int v ) {
        extension( t ).predCount = v;
        if ( _predCount )
            _predCount( this->pool(), t, v );
    }

    PORGraph() : _predCount( 0 ), bcomp( this->pool() ) {
        this->base().initPOR();
    }

    int setSlack( int s ) {
        m_algslack = s;
        return graph::Transform< G >::setSlack( s + sizeof( Extension ) );
    }

    Extension &extension( VertexId n ) {
        return n.template extension< Extension >( this->pool(), m_algslack );
    }

    Extension &extension( Vertex n ) {
        return extension( n.getVertexId() );
    }

    template < typename T >
    int predCount( T n ) {
        return extension( n ).predCount;
    }

    template < typename T >
    bool full( T n ) {
        return extension( n ).full;
    }

    template< typename Yield >
    void successors( Vertex st, Yield yield ) {
        if ( extension( st ).full )
            this->base().successors( st.getNode( this->pool() ), yield );
        else
            this->base().ample( st.getNode( this->pool() ), yield );
    }

    void porTransition( Vertex f, Vertex t, int* pc ) {

        if ( extension( t ).done )
            return; // ignore

        // increase predecessor count
        if ( this->pool().valid( f.getNode() ) )
            updatePredCount( t, predCount( t ) + 1, pc );
    }

    template< typename Setup >
    struct POREliminate : algorithm::Visit< This, Setup >
    {
        static_assert( wibble::TSame< typename Setup::Vertex, Vertex >::value,
                "Invalid setup provided for POREliminate: Vertex type of PORGraph does not match Vertex type of Setup" );

        static visitor::ExpansionAction expansion( This &, Vertex n ) {
            return visitor::ExpansionAction::Expand;
        }

        static visitor::TransitionAction transition( This &t, Vertex, Vertex to, Label ) {
            if ( t.extension( to ).done )
                return visitor::TransitionAction::Forget;

            assert( t.predCount( to ) );
            t.updatePredCount( to, t.predCount( to ) - 1 );
            t.extension( to ).remove = true;
            if ( t.predCount( to ) == 0 ) {
                t.extension( to ).done = true;
                return visitor::TransitionAction::Expand;
            }
            return visitor::TransitionAction::Forget;
        }

        template< typename V >
        static void init( This &t, V &v )
        {
            t.finished = true;

            for ( auto n : v.store() )
            {
                if ( t.extension( n ).done )
                    continue;

                t.finished = false;

                if ( !t.predCount( n ) || t.extension( n ).remove ) {
                    if ( t.predCount( n ) ) {
                        t.to_expand.insert( n );
                    }
                    Node node = v.store().fetchByVertexId( n ).getNode();
                    t.updatePredCount( n, 1 ); // ...
                    v.queue( Vertex(), node, Label() ); // coming from "nowhere"
                }
            }
        }
    };

    template< typename Algorithm >
    void _porEliminate( Algorithm &a, PredCount pc ) {
        _predCount = pc;
        typedef POREliminate< typename Algorithm::Setup > Elim;
        typename Elim::Visitor::template Implementation< Elim, Algorithm >
            visitor( *this, a, *this, a.store(), a.data );

        Elim::init( *this, visitor );
        visitor.processQueue();
    }

    void breakStalemate( Store &store ) { // this is NOT deterministic :/
        for ( auto n : store ) {
            if ( !extension( n ).done ) {
                updatePredCount( n, 0 );
                to_expand.insert( n );
                break;
            }
        }
    }

    // gives true iff there are nodes that need expanding
    template< typename Domain, typename Alg >
    bool porEliminate( Domain &d, Alg &a ) {

        to_expand.clear();

        while ( true ) {
            d.parallel( &Alg::_por_worker ); // calls _porEliminate

            if ( finished )
                break;

            breakStalemate( a.store() );
        }

        return to_expand.size() > 0;
    }

    template< typename Algorithm >
    bool porEliminateLocally( Algorithm &a, PredCount pc ) {
        _predCount = pc;
        typedef POREliminate< typename Algorithm::Setup > Elim;
        visitor::BFV< Elim > visitor( *this, *this, a.store() );

        to_expand.clear();

        while ( true ) {
            Elim::init( *this, visitor );
            visitor.processQueue();

            if ( finished )
                break;

            breakStalemate( a.store() );
        }

        return to_expand.size() > 0;
    }

    template< typename Yield >
    void porExpand( Store& store, Yield yield )
    {
        for ( auto n : to_expand ) {
            Vertex v = store.fetchByVertexId( n );
            fullexpand( yield, v );
        }
    }

    template< typename Yield >
    void fullexpand( Yield yield, Vertex v ) {
        extension( v ).full = true;
        Node n = v.getNode();
        BlobComparerLT bcomp( this->pool() );
        std::set< std::pair< Node, Label >, BlobComparerLT > all( bcomp ) , ample( bcomp ), out( bcomp );
        std::vector< std::pair< Node, Label > > extra;

        this->base().successors( n, [&]( Node x, Label l ) { all.insert( std::make_pair( x, l ) ); } );
        this->base().ample( n, [&]( Node x, Label l ) { ample.insert( std::make_pair( x, l ) ); } );

        std::set_difference( all.begin(), all.end(), ample.begin(), ample.end(),
                             std::inserter( out, out.begin() ), bcomp );

        // accumulate all the extra states we have generated
        std::copy( ample.begin(), ample.end(), std::back_inserter( extra ) );
        std::set_intersection( all.begin(), all.end(), ample.begin(), ample.end(),
                               std::back_inserter( extra ), bcomp );

        // release the states that we aren't going to use
        for ( auto i : extra )
            this->base().release( i.first );

        for ( auto i : out )
            yield( n, i.first, i.second );
    }
};

}
}

#endif
