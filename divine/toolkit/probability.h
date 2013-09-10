// -*- C++ -*- (c) 2013 Petr Rockai <me@mornfall.net>

#include <divine/toolkit/bitstream.h>
#include <cmath>

#ifndef DIVINE_TOOLKIT_PROBABILITY_H
#define DIVINE_TOOLKIT_PROBABILITY_H

namespace divine {
namespace toolkit {

constexpr bool isprime( int i, int f ) {
    return (f * f > i) ? true : ( i % f == 0 ) ? false : isprime( i, f + 1 );
}
constexpr bool isprime( int i ) {
    return isprime( i, 2 );
}
constexpr int prime( int i, int p ) {
    return i == 0 ? ( isprime( p ) ? p : prime( i, p + 1 ) )
                  : ( isprime( p ) ? prime( i - 1, p + 1 ) : prime( i, p + 1 ) );
}
constexpr int prime( int i ) {
    return prime( i, 1 );
}

static_assert( prime( 1 ) ==  2, "x" );
static_assert( prime( 2 ) ==  3, "x" );
static_assert( prime( 3 ) ==  5, "x" );
static_assert( prime( 4 ) ==  7, "x" );
static_assert( prime( 5 ) == 11, "x" );

struct Probability {
    unsigned cluster:16;
    int numerator:16;
    unsigned denominator;
    Probability() : Probability( 0 ) {}
    Probability( int c ) : Probability( c, 1, 1 ) {}
    Probability( int c, int x, int y ) : cluster( c ), numerator( x ), denominator( y ) {}
    Probability operator*( std::pair< int, int > x ) {
        auto p = *this;
        p.numerator *= x.first;
        p.denominator *= x.second;
        // p.normalize();
        return p;
    }
    Probability levelup( int i ) {
        auto p = *this;
        int l;
        assert( i );
        for ( l = 1; p.cluster % prime( l ) == 0; ++l );
        p.cluster *= std::pow( prime( l ), i );
        return p;
    }
    std::string text() {
        std::stringstream s;
        if ( numerator ) {
            s << cluster << ": " << numerator << "/" << denominator;
        }
        return s.str();
    }
};

template< typename BS >
typename BS::bitstream &operator<<( BS &bs, const Probability &p )
{
    return bs << p.cluster << p.numerator << p.denominator;
}

template< typename BS >
typename BS::bitstream &operator>>( BS &bs, Probability &p )
{
    int x, y;
    auto &r = bs >> x >> y >> p.denominator;
    p.cluster = x;
    p.numerator = y;
    return r;
}

}
}

#endif
