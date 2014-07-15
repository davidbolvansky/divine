// -*- C++ -*- (c) 2014 Vladimír Štill <xstill@fi.muni.cz>

#include <vector>
#include <wibble/sfinae.h> // Unit
#include <divine/graph/probability.h>

#ifndef DIVINE_TOOLKIT_LABEL_H
#define DIVINE_TOOLKIT_LABEL_H

namespace divine {
namespace graph {

using NoLabel = wibble::Unit;

struct ControlLabel {
    ControlLabel() : tid( -1 ) { }
    ControlLabel( int tid ) : tid( tid ) { }
    int tid;
};

template< typename BS >
typename BS::bitstream &operator<<( BS &bs, const ControlLabel &cl ) {
    bs << cl.tid;
    return bs;
}
template< typename BS >
typename BS::bitstream &operator>>( BS &bs, ControlLabel &cl ) {
    bs >> cl.tid;
    return bs;
}

/* unified label data structure, can be converted to Probability,
 * ControlLabel or NoLablel
 */
struct Label {

    Label() : Label( 0 ) { }
    Label( int tid ) : Label( tid, 0, 0, { } ) { }
    Label( int tid, int numerator, int denominator, std::vector< int > choices ) :
        tid( tid ), numerator( numerator ), denominator( denominator ),
        choices( choices )
    { }

    Label operator*( std::pair< int, int > x ) const {
        return Label( tid, numerator * x.first, denominator * x.second, choices );
    }

    Label levelup( int c ) const {
        Label l = *this;
        l.choices.push_back( c );
        return l;
    }

    explicit operator NoLabel() const { return NoLabel(); }

    explicit operator ControlLabel() const {
        return ControlLabel( tid );
    }

    explicit operator Probability() const {
        assert_leq( 0, denominator );
        Probability p{ int( pow( 2, tid + 1 ) ), numerator, denominator };
        assert_leq( p.numerator, numerator );
        assert_eq( int( p.denominator ), denominator );
        for ( int c : choices )
            p = p.levelup( c + 1 );
        return p;
    }

    int tid;
    int numerator;
    int denominator;
    std::vector< int > choices;
};


static inline std::string showLabel( NoLabel ) { return ""; }
static inline std::string showLabel( ControlLabel cl ) {
    return "tid = " + std::to_string( cl.tid );
}
static inline std::string showLabel( Probability p ) { return p.text(); }

} // namespace toolkit
} // namespace divine

#endif // DIVINE_TOOLKIT_LABEL_H
