// -*- C++ -*- (c) 2013 Vladimir Still <xstill@fi.muni.cz>
//             (c) 2013 Petr Ročkai <me@mornfall.net>

#include <wibble/test.h> // assert
#include <tuple>
#include <algorithm>
#include <cstring>
#include <queue>
#include <cstdint>
#include <vector>
#include <numeric>
#include <divine/toolkit/hashset.h>
#include <divine/toolkit/pool.h>

#ifndef N_TREE_HASH_SET_H
#define N_TREE_HASH_SET_H

namespace divine {

enum class Recurse : uint8_t { Yes, No };

template< typename T >
struct NewtypeHasher {
    Pool &p;
    NewtypeHasher( Pool &p ) : p( p ) {}
    hash128_t hash( T t ) const { return p.hash( t.unwrap() ); }
    bool valid( T t ) const { return p.valid( t.unwrap() ); }
    bool equal( T a, T b ) const { return p.equal( a.unwrap(), b.unwrap() ); }
};

template< typename T, typename Self >
struct NewTypeTag {
    static const int tagBits = T::tagBits;
    Self &self() { return *static_cast< Self * >( this ); }
    int tag() { return self().unwrap().tag(); }
    void setTag( int t ) { return self().unwrap().setTag( t ); }
};

// NTreeHashSet :: ( * -> * -> * ) -> * -> * -> *
// Item can be any type with same interface as Blob
template< template< typename, typename > class HashSet, typename T, typename Hasher >
struct NTreeHashSet
{
    struct Root;

    using insert_type = T;
    using value_type = Root;

    typedef NTreeHashSet< HashSet, T, Hasher > This;

    NTreeHashSet() : NTreeHashSet( Hasher() ) { }
    NTreeHashSet( Hasher _hasher ) : _d( _hasher )
    {}

    struct Leaf : NewType< Blob >, NewTypeTag< Blob, Leaf > {
        Leaf() = default;
        Leaf( Blob b ) : NewType( b ) {}
        Leaf( int32_t size, char* source, Pool& pool )
        {
            assert_leq( 1, size );
            this->unwrap() = pool.allocate( size );
            std::copy( source, source + size, pool.dereference( this->unwrap() ) );
        }
        char *data( Pool &p ) { return p.dereference( this->unwrap() ); }
        int32_t size( Pool &p ) { return p.size( this->unwrap() ); }
        operator bool() { return !!this->unwrap(); }
    };

    template < typename Fork >
    struct LeafOr : NewType< Blob >, NewTypeTag< Blob, LeafOr< Fork > > {
        LeafOr() = default;

        const Blob &b() const { return this->unwrap(); }
        Blob &b() { return this->unwrap(); }

        LeafOr( Fork f ) : NewType< Blob >( f.unwrap() ) {
            assert_eq( b().tag(), 0UL );
            b().setTag( 1 );
        }

        LeafOr( Leaf l ) : NewType< Blob >( l.unwrap() ) {
            assert_eq( b().tag(), 0UL );
        }

        Blob blob() const { Blob blob( b() ); blob.setTag( 0 ); return blob; }
        bool isLeaf() const { return !isFork(); }
        bool isFork() const { assert( b().tag() == 1 || b().tag() == 0 ); return b().tag(); }
        int32_t size( Pool &p ) const { return p.size( blob() ); }
        bool isNull( Pool &p ) const { return !p.valid( blob() ); }

        Fork fork() {
            assert( isFork() );
            return Fork( blob() );
        }

        Leaf leaf() {
            assert( isLeaf() );
            return Leaf( blob() );
        }
    };

    template< typename Self, typename Fork >
    struct WithChildren
    {
        Self &self() { return *static_cast< Self * >( this ); }

        template< typename Yield >
        void forChildren( Pool &p, Yield yield ) {
            assert( self().forkcount( p ) );
            for ( int32_t i = 0; i < self().forkcount( p ); ++i )
                yield( self().forkdata( p )[ i ] );
        }

        // emit all leafs until false is returned from yield
        template< typename Yield >
        bool forAllLeaves( Pool& p, Yield yield ) {
            bool result = false;
            self().forChildren( p, [&]( LeafOrFork lof ) {
                    if ( lof.isLeaf() ) {
                        if ( !yield( lof.leaf() ) )
                            return false;
                    } else {
                        if ( !lof.fork().forAllLeaves( p, yield ) )
                            return false;
                    }
                    return result = true;
                } );
            return result;
        }

        std::vector< LeafOr< Fork > > childvector( Pool &p ) {
            std::vector< LeafOrFork > lof;
            forChildren( p, [&lof]( LeafOr< Fork > x ) { lof.push_back( x ); } );
            return lof;
        }
    };

    struct Fork : WithChildren< Fork, Fork >, NewType< Blob >, NewTypeTag< Blob, Fork > {
        Fork() = default;
        Fork( Blob b ) : NewType< Blob >( b ) {}
        Fork( int32_t children, Pool& pool ) {
            assert_leq( 2, children );
            int32_t size = children * sizeof( LeafOr< Fork > );
            this->unwrap() = pool.allocate( size );
            pool.clear( this->unwrap() );
        }

        int32_t forkcount( Pool &p ) {
            return p.size( this->unwrap() ) / sizeof( LeafOr< Fork > );
        }
        LeafOr< Fork > *forkdata( Pool &p ) {
            return p.dereference< LeafOrFork >( this->unwrap() );
        }
        operator bool() { return !!this->unwrap(); }
    };

    typedef LeafOr< Fork > LeafOrFork;

    struct Root : WithChildren< Root, Fork >, NewType< Blob >, NewTypeTag< Blob, Root > {
        struct Header { int32_t forks; };

        Blob &b() { return this->unwrap(); }

        Root() = default;
        explicit Root( Blob b ) : NewType< Blob >( b ) {}
        Header &header( Pool &p ) { return *p.dereference< Header >( b() ); }
        bool leaf( Pool &p ) { return header( p ).forks == 0; }
        int32_t forkcount( Pool &p ) { return header( p ).forks; }
        char *rawdata( Pool &p ) { return p.dereference( b() ) + sizeof( Header ); }

        operator bool() { return !!this->unwrap(); }

        char *data( Pool &p ) {
            assert( leaf( p ) );
            return rawdata( p );
        }

        LeafOrFork *forkdata( Pool &p ) {
            assert( !leaf( p ) );
            return reinterpret_cast< LeafOrFork *> ( rawdata( p ) );
        }

        int32_t dataSize( Pool &p, int32_t slack ) {
            return p.size( b() ) - sizeof( Header ) - slack;
        }

        int32_t slackoffset( Pool &p ) { return sizeof( LeafOrFork ) * forkcount( p ); }
        char *slack( Pool &p ) { return rawdata( p ) + slackoffset( p ); }

        Blob reassemble( Pool& p )
        {
            assert( p.valid( b() ) );
            if ( leaf( p ) ) {
                int32_t size = p.size( b() ) - sizeof( Header );
                assert_leq( 0, size );
                Blob out = p.allocate( size );
                std::copy( data( p ), data( p ) + size, p.dereference( out ) );
                return out;
            }

            std::vector< Leaf > leaves;
            int32_t size = 0;

            this->forAllLeaves( p, [ &p, &leaves, &size ]( Leaf leaf ) -> bool {
                    leaves.push_back( leaf );
                    size += leaf.size( p );
                    return true; // demand all
                } );

            char* slackptr = slack( p );
            int32_t slacksize = p.size( b() ) - sizeof( Header ) - slackoffset( p );
            size += slacksize;
            Blob out = p.allocate( size );
            char* outptr = p.dereference( out );
            outptr = std::copy( slackptr, slackptr + slacksize, outptr );
            for ( auto l : leaves ) {
                assert_leq( outptr - p.dereference( out ), p.size( out ) );
                outptr = std::copy( l.data( p ), l.data( p ) + p.size( l.unwrap() ), outptr );
            }
            assert_eq( outptr - p.dereference( out ), p.size( out ) );
            return out;
        }

        static Root createFlat( insert_type it, Pool& pool ) {
            assert( pool.valid( it ) );
            Root r;
            r.unwrap() = pool.allocate( sizeof( Header ) + pool.size( it ) );
            r.header( pool ).forks = 0;
            std::copy( pool.dereference( it ), pool.dereference( it ) + pool.size( it ),
                       pool.dereference( r.unwrap() ) + sizeof( Header ) );
            return r;
        }

        static Root create( insert_type it, int32_t children, int32_t slack, Pool& pool ) {
            assert_leq( 2, children );
            assert_leq( 0, slack );
            uintptr_t size = sizeof( Header ) + slack + sizeof( LeafOrFork ) * children;
            Root root;
            root.unwrap() = pool.allocate( size );
            root.header( pool ).forks = children;
            std::memset( root.rawdata( pool ), 0, sizeof( LeafOrFork ) * children );
            std::memcpy( pool.dereference( root.unwrap() ) + size - slack,
                         pool.dereference( it ), slack );
            return root;
        }
    };

    struct Uncompressed { insert_type i; Uncompressed( insert_type i ) : i( i ) {} };

    using ForkHasher = NewtypeHasher< Fork >;
    using LeafHasher = NewtypeHasher< Leaf >;

    struct RootHasher {
        Hasher uhasher;
        uint32_t salt;

        RootHasher( Hasher uhasher ) : RootHasher( uhasher, 0 ) { }
        RootHasher( Hasher uhasher, uint32_t salt )
            : uhasher( uhasher), salt( salt )
        { }

        Pool &pool() { return uhasher.pool(); }
        int32_t slack() { return uhasher.slack; }

        hash128_t hash( Uncompressed u ) { return uhasher.hash( u.i ); }
        hash128_t hash( Root r ) {
            if ( r.leaf( pool() ) ) {
                auto offset = sizeof( typename Root::Header ) + uhasher.slack;
                return pool().hash( r.unwrap(), offset, offset + r.dataSize( pool(), uhasher.slack ) );
            } else {
                SpookyState state( salt, salt );
                r.forAllLeaves( pool(), [ this, &state ]( Leaf l ) {
                            state.update( l.data( this->pool() ), l.size( this->pool() ) );
                            return true;
                        } );
                return state.finalize();
            }
        }

        bool valid( Root r ) { return pool().valid( r.unwrap() ); }
        bool valid( Uncompressed r ) { return pool().valid( r.i ); }
        void setSeed( hash64_t s ) { uhasher.setSeed( s ); }

        bool equal( Root r1, Root r2 ) {
            if ( r1.unwrap().raw() == r2.unwrap().raw() )
                return true;
            if ( r1.leaf( pool() ) && r2.leaf( pool() ) )
                return pool().equal( r1.unwrap(), r2.unwrap(), sizeof( typename Root::Header )
                        + uhasher.slack );
            else if ( !r1.leaf( pool() ) && !r2.leaf( pool() ) ) {
                int32_t s1 = pool().size( r1.unwrap() );
                int32_t s2 = pool().size( r2.unwrap() );
                return s1 == s2
                    && pool().equal( r1.unwrap(), r2.unwrap(), sizeof( typename Root::Header ),
                            sizeof( typename Root::Header ) + r1.slackoffset( pool() ) );
            }

            /*
             * Note on root equality: Leaves and forks are cononical, that is
             * only one instance of leaf/fork representing same subnode exists
             * per HashSet, and instances from diffent HashSets can't represent
             * same nodes (as they differ in hash).  Therefore roots can be
             * compared trivially (on pointers to leafs/forks.
             */
            return false;
        }

        bool equal( Root root, Uncompressed item ) {
            return equal( item, root );
        }

        bool equal( Uncompressed item, Root root ) {
            int32_t itSize = pool().size( item.i ) - slack();
            char* itemPtr = pool().dereference( item.i ) + slack();
            if ( root.leaf( pool() ) ) {
                return itSize == root.dataSize( pool(), slack() )
                    && std::memcmp( itemPtr,
                                    root.data( pool() ) + slack(), itSize ) == 0;
            }

            itSize += slack();
            int32_t pos = slack();
            bool equal = true;

            root.forAllLeaves( pool(), [&] ( Leaf leaf ) {
                    assert( equal );
                    assert( this->pool().valid( leaf.unwrap() ) );
                    assert( itemPtr != nullptr );
                    assert_leq( 0, pos );

                    Pool &p = this->pool();
                    assert_leq( pos + leaf.size( p ), itSize );
                    equal = std::memcmp( itemPtr, leaf.data( p ),
                                         leaf.size( p ) ) == 0;
                    itemPtr += leaf.size( p );
                    pos += leaf.size( p );
                    return equal;
                } );
            assert_leq( 0, pos );
            return equal;
        }

        bool equal( Uncompressed i1, Uncompressed i2 ) const {
            return uhasher.equal( i1.i, i2.i );
        }
    };

    using RootSet = HashSet< Root, RootHasher >;
    using ForkSet = HashSet< Fork, ForkHasher >;
    using LeafSet = HashSet< Leaf, LeafHasher >;

    using iterator = typename RootSet::iterator;

    template< typename Splitter >
    struct ThreadData {
        typename RootSet::ThreadData roots;
        typename ForkSet::ThreadData forks;
        typename LeafSet::ThreadData leaves;
        Splitter *_splitter;
        Pool *_pool;
        Splitter &splitter() { assert( _splitter ); return *_splitter; }
        Pool &pool() { assert( _pool ); return *_pool; }

        ThreadData() : _splitter( nullptr ), _pool( nullptr ) {}
        ThreadData( Pool &p, Splitter &sp )
            : _splitter( &sp ), _pool( &p )
        {}
    };

    struct Data
    {
        Data( Hasher h ) :
            pool( h.pool() ), // FIXME
            slack( h.slack ),
            roots( RootHasher( h ) ),
            forks( ForkHasher( h.pool() ) ),
            leaves( LeafHasher( h.pool() ) )
        {}

        Pool &pool;
        int slack; // FIXME
        RootSet roots; // stores slack and roots of tree
                        // (also in case when root leaf)
        ForkSet forks; // stores intermediate nodes
        LeafSet leaves; // stores leaves if they are not root
    };

    /* struct NoSplitter
    {
        template< typename Yield >
        void splitHint( Blob, intptr_t, intptr_t length, Yield yield ) {
            yield( Recurse::No, length, 0 );
        }

        template< typename Yield >
        void splitHint( Blob n, Yield yield ) {
            splitHint( n, 0, pool().size( n ), yield );
        }
    }; */

    Pool& pool() { return _d.pool; }
    int32_t slack() { return _d.slack; }
    char* slackPtr( insert_type item ) { return pool().dereference( item ); }

    void copySlack( insert_type slackSource, insert_type root ) {
        pool().copy( slackSource, root, slack() );
    }

    size_t size() { return _d.roots.size(); }
    bool empty() { return _d.roots.empty(); }
    hash64_t hash( const value_type &t ) { return _d.roots.hash( t ); }

    Data _d;
    // ThreadData< NoSplitter > _global; /* for single-thread access */

    template< typename Splitter >
    struct WithTD
    {
        using iterator = typename RootSet::iterator;
        using insert_type = T;
        using value_type = Root;

        Data &_d;
        ThreadData< Splitter > &_td;

        WithTD( Data &d, ThreadData< Splitter > &td )
            : _d( d ), _td( td )
        {}

        iterator insertHinted( insert_type item, hash64_t hash )
        {
            Root root;

            LeafOrFork* ptr = nullptr;
            char* from = _td.pool().dereference( item ) + _d.slack;
            _td.splitter().splitHint( item, [&]( Recurse rec, intptr_t length, intptr_t remaining ) {
                    if ( rec == Recurse::No ) {
                        root = Root::createFlat( item, _td.pool() );
                        assert_eq( remaining, 0 );
                    } else {
                        if ( !_td.pool().valid( root.unwrap() ) ) {
                            root = Root::create( item, remaining + 1, _d.slack, _td.pool() );
                            ptr = root.forkdata( _td.pool() );
                            assert_leq( 1, remaining );
                        }
                        assert( ptr != nullptr );

                        *ptr = createChild( item, from, length, _td.pool() );
                        ++ptr;
                    }

                    assert( _td.pool().valid( root.unwrap() ) );
                    from += length;
                } );

            assert( _td.pool().valid( root.unwrap() ) );
            assert_eq( size_t( from ), size_t( _td.pool().dereference( item ) + _td.pool().size( item ) ) );

            auto tr = _d.roots.withTD( _td.roots ).insertHinted( root, hash );
            if ( !tr.isnew() )
                _td.pool().free( root.unwrap() );

            return tr;
        }

        LeafOrFork createChild( insert_type item, char* from, intptr_t length, Pool &pool )
        {
            assert_leq( pool.dereference( item ) + _d.slack, from );
            assert_leq( from, pool.dereference( item ) + pool.size( item ) );

            LeafOrFork child;
            LeafOrFork* ptr = nullptr;
            _td.splitter().splitHint( item, from - pool.dereference( item ), length,
                                 [&]( Recurse rec, intptr_t length, intptr_t remaining ) {
                    if ( rec == Recurse::No ) {
                        assert( child.isNull( pool ) );
                        assert( ptr == nullptr );
                        assert_eq( remaining, 0 );
                        child = Leaf( length, from, pool );
                    } else {
                        if ( child.isNull( pool ) ) {
                            child = Fork( remaining + 1, pool );
                            ptr = child.fork().forkdata( pool );
                        }
                        assert( !child.isNull( pool ) );
                        assert( ptr != nullptr );

                        *ptr = createChild( item, from, length, pool );
                        ++ptr;
                    }
                    from += length;
                } );

            if ( child.isLeaf() ) {
                auto c = _d.leaves.withTD( _td.leaves ).insert( child.leaf() );
                if ( !c.isnew() )
                    pool.free( child.blob() );
                return c.copy();
            } else {
                auto c = _d.forks.withTD( _td.forks ).insert( child.fork() );
                if ( !c.isnew() )
                    pool.free( child.blob() );
                return c.copy();
            }
        }

        iterator find( insert_type item ) {
            return findHinted( item, _d.hasher.hash( item ).first );
        }

        iterator findHinted( insert_type i, hash64_t h ) {
            return _d.roots.withTD( _td.roots ).findHinted( Uncompressed( i ), h );
        }

        bool has( insert_type i ) {
            return get( i ).valid();
        }
    };

    template< typename Splitter >
    WithTD< Splitter > withTD( ThreadData< Splitter > &td ) {
        return WithTD< Splitter >( _d, td );
    }

    void setSize( size_t s ) {
        _d.roots.setSize( s );
        _d.forks.setSize( s );
        _d.leaves.setSize( s );
    }

    void clear() {
        _d.roots.clear();
        _d.forks.clear();
        _d.leaves.clear();
    }

    Root operator[]( intptr_t off ) {
        assert_leq( 0, off );
        assert_leq( off, intptr_t( size() ) - 1 );
        return _d.roots[ off ];
    }

    bool valid( intptr_t off ) {
        return _d.roots.valid( off );
    }

    /* iterator insertHinted( value_type item, hash64_t hash ) {
        return withTD( _global ).insertHinted( item, hash );
     } */
};

}
#endif
