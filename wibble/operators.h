// -*- C++ -*-

#include <set>
#include <algorithm>

#ifndef WIBBLE_OPERATORS_H
#define WIBBLE_OPERATORS_H

namespace wibble {
namespace operators {

/*
template< typename S, typename VT > struct IsContainer {
    typedef S T;
};

template< typename S >
typename IsContainer< S, typename S::value_type >::T operator &&( const S &a, const S &b ) {
    S ret;
    std::set_intersection( a.begin(), a.end(), b.begin(), b.end(),
                           std::inserter( ret, ret.begin() ) );
    return ret;
}
*/

template< typename T >
std::set< T > operator &( const std::set< T > &a, const std::set< T > &b ) {
    std::set< T > ret;
    std::set_intersection( a.begin(), a.end(), b.begin(), b.end(),
                           std::inserter( ret, ret.begin() ) );
    return ret;
}

template< typename T >
std::set< T > operator |( const std::set< T > &a, const std::set< T > &b ) {
    std::set< T > ret;
    std::set_union( a.begin(), a.end(), b.begin(), b.end(),
                    std::inserter( ret, ret.begin() ) );
    return ret;
}

template< typename T >
std::set< T > &operator |=( std::set< T > &a, const std::set< T > &b ) {
    std::set< T > ret;
    ret = a | b;
    return a = ret;
}

template< typename T >
std::set< T > &operator &=( std::set< T > &a, const std::set< T > &b ) {
    std::set< T > ret;
    ret = a & b;
    return a = ret;
}

}
}

#endif
