// -*- C++ -*- (c) 2009-2013 Petr Rockai <me@mornfall.net>

#include <divine/generator/common.h>

#ifndef DIVINE_GENERATOR_DUMMY_H
#define DIVINE_GENERATOR_DUMMY_H

namespace divine {
namespace generator {

#ifndef __divine__
// size is (dummy_size_param + 1) ^ 2
const int dummy_size = 512;
#else
const int dummy_size = 2;
#endif

struct Dummy : Common< Blob > {
    typedef std::pair< short, short > Content;
    typedef Blob Node;

    struct Label {
        short probability;
        Label( short p = 0 ) : probability( p ) {}
    };

    Content &content( Blob b ) {
        return pool().get< Content >( b, slack() );
    }

    template< typename Alloc, typename Yield >
    void initials( Alloc alloc, Yield yield ) {
        Blob b = this->makeBlob( alloc, sizeof( Content ) );
        content( b ) = std::make_pair( 0, 0 );
        yield( Node(), b, Label() );
    }

    template< typename Alloc, typename N, typename Yield >
    void successors( Alloc alloc, N st, Yield yield )
    {
        return successors( alloc, st.node(), yield );
    }

    template< typename Alloc, typename Yield >
    void successors( Alloc alloc, Node st, Yield yield ) {
        Node r;

        if ( !pool().valid( st ) )
            return;

        if ( content( st ).first < dummy_size ) {
            r = this->makeBlob( alloc, sizeof( Content ) );
            content( r ) = content( st );
            content( r ).first ++;
            yield( r, Label( 7 ) );
        }

        if ( content( st ).second < dummy_size ) {
            r = this->makeBlob( alloc, sizeof( Content ) );
            content( r ) = content( st );
            content( r ).second ++;
            yield( r, Label( 3 ) );
        }
    }

    template< typename Alloc >
    void release( Alloc alloc, Node s ) {
        alloc.drop( pool(), s );
    }

    template< typename Yield >
    void enumerateFlags( Yield ) { } // no flags supported beyond implicit accepting and goal

    template< typename QueryFlags >
    graph::FlagVector stateFlags( Node s, QueryFlags qf ) {
        Content cont = pool().get< Content >( s, this->slack() );
        for ( auto f : qf )
            if ( f == graph::flags::goal && cont.first == dummy_size )
                return { f };
        return { };
    }

    std::string showNode( Node s ) {
        if ( !pool().valid( s ) )
            return "[]";
        Content f = pool().get< Content >( s, this->slack() );
        std::stringstream stream;
        stream << "[" << f.first << ", " << f.second << "]";
        return stream.str();
    }

    /// currently only dummy method
    std::string showTransition( Node, Node, Label act ) {
        if (act.probability == 3)
	  return "3";
	else
	  return "7";
    }

    void read( std::string, std::vector< std::string >, Dummy * = nullptr ) {}
};

template< typename BS >
typename BS::bitstream &operator<<( BS &bs, Dummy::Label l ) { return bs << l.probability; }

template< typename BS >
typename BS::bitstream &operator>>( BS &bs, Dummy::Label &l ) { return bs >> l.probability; }

}
}

#endif
