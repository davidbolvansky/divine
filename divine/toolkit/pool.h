// -*- C++ -*- (c) 2007-2013 Petr Rockai <me@mornfall.net>
#include <vector>
#ifndef NVALGRIND
#include <iostream>
#include <iomanip>
#endif
#include <memory>
#include <map>
#include <atomic>
#include <tuple>

#ifndef NVALGRIND
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wold-style-cast"
#include <memcheck.h>
#pragma GCC diagnostic pop
#endif

#include <brick-types.h>
#include <brick-string.h>
#include <brick-hash.h>
#include <brick-shmem.h>
#include <brick-mmap.h>

#ifndef DIVINE_POOL_H
#define DIVINE_POOL_H

namespace divine {

constexpr inline int align( int v, int a ) {
    return (v % a) ? (v + a - (v % a)) : v;
}

/*
 * A lake keeps track of memory in a compact, fast, thread-optimised fashion.
 * It is organised into blocks of objects of a single size. The Pointer type
 * can be cheaply converted into an actual pointer or to the size of the object
 * it points to. Both pointers and their dereferences are stable (no object
 * moving happens). Freelists are inline and used in LIFO order, to minimise
 * cache turnaround. Excess free memory is linked into a global freelist which
 * is used when the thread-local lists and partial blocks run out.
 *
 * A single item is limited to 2^24 bytes (16M). Total memory use is capped at
 * roughly 16T (more if you use big objects), but can be easily extended. If
 * compiled in debug mode, (without -DNVALGRIND), destroying a Lake will give
 * you some usage statistics. During runtime, valgrind will be kept up to date
 * about memory use and accessibility.
 */
struct Lake {

    struct Pointer : brick::types::Comparable {
        using Raw = uint64_t;
        static const unsigned blockBits = 20;
        static const unsigned offsetBits = 19;
        static const unsigned tagBits = 64 - blockBits - offsetBits;
        uint64_t _tag:tagBits;
        uint64_t block:blockBits;
        uint64_t offset:offsetBits;
        Pointer() noexcept : _tag( 0 ), block( 0 ), offset( 0 ) {}
        // XXX: Pointer() : block( 0xFFFFFFFFFF ), offset( 0 ) {}
        uint64_t raw() const { return *reinterpret_cast< const uint64_t * >( this ); }
        uint64_t raw_address() const { return offset | (block << offsetBits); }

        unsigned tag() const { return _tag; }
        void setTag( unsigned v ) { _tag = v; }

        static Pointer fromRaw( uint64_t r ) {
            union {
                uint64_t r;
                Pointer p;
            } c = { r };
            return c.p;
        }
        explicit operator bool() const { return raw(); }
        bool operator!() const { return !raw(); }
        bool operator<=( const Pointer &p ) const { return raw() <= p.raw(); }
    } __attribute__((packed));

    struct BlockHeader {
        uint64_t total:20;
        uint64_t allocated:20;
        uint64_t itemsize:24;
    };

    struct FreeList {
        Pointer head;
        FreeList *next;
        int32_t count;
        FreeList() : next( nullptr ), count( 0 ) {}
    };

    static void nukeList( FreeList *f ) {
        while ( f ) {
            auto d = f;
            f = f->next;
            delete d;
        }
    }

    static const int blockcount = 1 << Pointer::blockBits;
    static const int blocksize  = 4 << Pointer::offsetBits;

    char *block[ blockcount ]; /* 8M, each block is 2M -> up to 16T of memory */
    std::atomic< int > usedblocks;

    typedef std::atomic< FreeList * > FreeListPtr;
    FreeListPtr _freelist[ 4096 ];
    std::atomic< FreeListPtr * >_freelist_big[ 4096 ];

#ifndef NVALGRIND
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wold-style-cast"

    struct VHandle {
        int handle;
        bool allocated;
        VHandle() : handle( -1 ), allocated( false ) {}
    };

    std::atomic< VHandle * > _vhandles[ blockcount ]; /* one for each block */

    void valgrindInit() {
        for ( int i = 0; i < blockcount; ++i )
            _vhandles[ i ] = nullptr;
    }

    void valgrindAllocated( Pointer p ) {
        VALGRIND_MEMPOOL_ALLOC( block[ p.block ], dereference( p ), size( p ) );
        VALGRIND_MAKE_MEM_UNDEFINED( dereference( p ), size( p ) );

        VHandle *h = _vhandles[ p.block ], *alloc;
        if ( !h ) {
            if ( _vhandles[ p.block ].compare_exchange_strong(
                     h, alloc = new VHandle[ header( p ).total ]) )
                h = alloc;
            else
                delete[] alloc;
        }

        ASSERT( h );
        ASSERT( !h[ p.offset ].allocated );
        VALGRIND_DISCARD( h[ p.offset ].handle );
        h[ p.offset ].handle =
            VALGRIND_CREATE_BLOCK( dereference( p ), size( p ),
                                   brick::string::fmtf( "blob %llu:%llu @ %p",
                                                        p.block, p.offset,
                                                        dereference( p ) ).c_str() );
        h[ p.offset ].allocated = true;
    }

    void valgrindDeallocated( Pointer p ) {
        VALGRIND_MEMPOOL_FREE( block[ p.block ], dereference( p ) );
        VALGRIND_MAKE_MEM_NOACCESS( dereference( p ), size( p ) );

        ASSERT( _vhandles[ p.block ].load() );
        ASSERT( _vhandles[ p.block ][ p.offset ].allocated );

        VALGRIND_DISCARD( _vhandles[ p.block ][ p.offset ].handle );
        _vhandles[ p.block ][ p.offset ].handle =
            VALGRIND_CREATE_BLOCK( dereference( p ), size( p ),
                                   brick::string::fmtf( "blob %llu:%llu @ %p [DELETED]",
                                                        p.block, p.offset,
                                                        dereference( p ) ).c_str() );
        _vhandles[ p.block ][ p.offset ].allocated = false;
    }

    void valgrindNewBlock( int b, int bytes ) {
        VALGRIND_MAKE_MEM_NOACCESS( block[ b ] + sizeof( BlockHeader ), bytes );
        VALGRIND_CREATE_MEMPOOL( block[ b ], 0, 0 );
    }

    void bump( std::vector< int64_t > &v, size_t cnt ) {
        v.resize( std::max( v.size(), cnt + 1 ), 0 );
    }

    void valgrindFini() {
        int64_t count = 0;
        int64_t bytes = 0;
        int64_t wasted = 0;
        std::vector< int64_t > sizecount;
        std::vector< int64_t > sizebytes;

        if ( !RUNNING_ON_VALGRIND && !getenv( "DIVINE_LAKE_STATS" ) )
            return ;

        for ( int i = 0; i < blockcount; ++i )
            if ( _vhandles[ i ] ) {
                for ( int j = 0; j < header( i ).total; ++j ) {
                    bool allocd = _vhandles[ i ][ j ].allocated;
                    count += allocd;
                    bump( sizecount, header( i ).itemsize );
                    sizecount[ header( i ).itemsize ] += allocd;
                }
                delete[] _vhandles[ i ].load();
            }

        for ( int i = 0; i < blockcount; ++i )
            if ( block[ i ] ) {
                int64_t is = header( i ).itemsize;
                int64_t b = header( i ).total * align( is, sizeof( Pointer ) );
                bytes += b;
                bump( sizebytes, is + 1 );
                sizebytes[ is ] += b;
                VALGRIND_DESTROY_MEMPOOL( block[ i ] );
            }

        bump( sizecount, sizebytes.size() - 1 );
        bump( sizebytes, sizecount.size() - 1 );

        std::cerr << "~Lake(): " << count << " objects not freed:" << std::endl;
        for ( size_t i = 0; i < sizecount.size(); ++ i )
            if ( sizecount[i] || sizebytes[ i ] ) {
                int64_t c = sizecount[i];
                int64_t b = c * i;
                int64_t t = sizebytes[i];
                wasted += (t - b);
                std::cerr << "   " << std::setw(8) << c << " object(s) of size " << i
                          << " for " << b / 1024 << "/" << t / 1024 << "kB" << std::endl;
            }
        std::cerr << " " << (bytes / 1024) << " kbytes held; " << wasted / 1024 << "kB wasted" << std::endl;
    }
#pragma GCC diagnostic pop
#else
#define VALGRIND_MAKE_MEM_DEFINED(x, y)
#define VALGRIND_MAKE_MEM_NOACCESS(x, y)
#define VALGRIND_MAKE_MEM_UNDEFINED(x, y)
    void valgrindAllocated( Pointer ) {}
    void valgrindDeallocated( Pointer ) {}
    void valgrindNewBlock( int, int ) {}
    void valgrindFini() {}
    void valgrindInit() {}
#endif

    /*
     * NB. We set usedblocks to 8, so that we both keep reasonable alignment
     * and make (0, 0) Pointer invalid; this may change in the future, when
     * Extensions, which tend to contain Pointers, are no longer zeroed, but
     * constructed instead (as they should)
     */
    Lake() : usedblocks( 8 ) {
        for ( int i = 0; i < 4096; ++i )
            _freelist[ i ] = nullptr;
        for ( int i = 0; i < 4096; ++i )
            _freelist_big[ i ] = nullptr;
        for ( int i = 0; i < blockcount; ++i )
            block[ i ] = nullptr;
        valgrindInit();
    }
    Lake( const Lake & ) = delete;

    ~Lake() {
        valgrindFini();
        for ( int i = 0; i < 4096; ++i ) {
            nukeList( _freelist[ i ] );
            if ( _freelist_big[ i ] ) {
                for ( int j = 0; j < 4096; ++j )
                    nukeList( _freelist_big[ i ][ j ] );
                delete[] _freelist_big[ i ].load();
            }
        }
        for ( int i = 0; i < blockcount; ++i ) {
            if ( !block[ i ] )
                continue;
            auto size =
                header( i ).total ?
                header( i ).total * align( header( i ).itemsize,
                                           sizeof( Pointer ) ) +
                sizeof( BlockHeader ) : blocksize;
            brick::mmap::MMap::drop( block[ i ], size );
        }
    }

    std::atomic< FreeList * > &freelist( int size )
    {
        if ( size < 4096 )
            return _freelist[ size ];

        std::atomic< FreeList * > *chunk, *newchunk;
        if ( !( chunk = _freelist_big[ size / 4096 ] ) ) {
            if ( _freelist_big[ size / 4096 ].compare_exchange_strong(
                     chunk, newchunk = new FreeListPtr[ 4096 ]() ) )
                chunk = newchunk;
            else
                delete newchunk;
        }
        ASSERT( chunk );
        return chunk[ size % 4096 ];
    }

    /*
     * A wharf is a thread's interface to the Lake above. Use it to create, destroy
     * and dereference objects.
     */
    struct Wharf {
        std::shared_ptr< Lake > lake;

        struct SizeInfo {
            int active;
            int blocksize;
            FreeList touse;
            FreeList tofree;
            SizeInfo() : active( -1 ), blocksize( 4096 ) {}
            ~SizeInfo() {}
        };

        std::vector< int > _emptyblocks;
        SizeInfo _size[ 4096 ];
        SizeInfo *_size_big[ 4096 ];
        std::vector< std::pair< int, int > > ephemeral;
        int ephemeral_block;

        Pointer ephemeralAllocate( int sz ) {
            ASSERT_LEQ( 0, ephemeral_block );
            int off = 0;

            /* first-fit allocation */
            auto i = ephemeral.begin();
            for ( ; i != ephemeral.end(); ++i ) {
                if ( off + sz <= i->first )
                    break;
                off = align( i->second, 4 );
            }
            ASSERT_LEQ( off + sz, blocksize );
            ephemeral.emplace( i, off, off + sz );

            Pointer p;
            p.block = ephemeral_block;
            ASSERT_EQ( off % 4, 0 );
            p.offset = off / 4;
            return p;
        }

        void ephemeralFree( Pointer p ) {
            if ( !valid( p ) )
                return;

            ASSERT_EQ( int( p.block ), ephemeral_block );
            auto i = ephemeral.begin();
            for ( ; i != ephemeral.end(); ++i )
                if ( i->first == p.offset * 4 )
                    break;
            ASSERT( i != ephemeral.end() );
            ephemeral.erase( i );
        }

        char *dereference( Pointer p ) { return lake->dereference( p ); }
        const char *dereference( Pointer p ) const { return lake->dereference( p ); }
        bool valid( Pointer p ) { return p.block; /* != 0xFFFFFFFFFF*/; }
        int size( Pointer p ) {
            if( p.block == ephemeral_block )
                for ( auto e : ephemeral )
                    if ( e.first == p.offset * 4 )
                        return e.second - e.first;
            ASSERT_NEQ( int( p.block ), ephemeral_block );

            ASSERT( lake->header( p ).total > 0 && "invalid size() on foreign ephemeral block" );
            ASSERT( lake->size( p) );
            return lake->size( p );
        }

        bool alias( Pointer a, Pointer b ) {
            return a.block == b.block && a.offset == b.offset;
        }

        Wharf( std::shared_ptr< Lake > l ) : lake( l ), ephemeral_block( -1 ) {
            for ( int i = 0; i < 4096; ++i )
                _size_big[ i ] = nullptr;
            _size[ 0 ].blocksize = blocksize;
            if ( l ) {
                ephemeral_block = newblock( 0 );
                l->header( ephemeral_block ).itemsize = 4;
            }
        }

        Wharf() : Wharf( std::make_shared< Lake >() ) {}
        Wharf( const Wharf &w ) : Wharf( w.lake ) {}

        ~Wharf() {
            for ( int i = 0; i < 4096; ++i )
                delete[] _size_big[ i ];
        }

        Pointer &freechunk( Pointer p ) {
            return *reinterpret_cast< Pointer * >( dereference( p ) );
        }

        Pointer fromFreelist( SizeInfo &si ) {
            ASSERT( si.touse.count );
            ASSERT( valid( si.touse.head ) );
            -- si.touse.count;
            Pointer p = si.touse.head;
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wold-style-cast"
            VALGRIND_MAKE_MEM_DEFINED( dereference( p ), sizeof( Pointer ) );
            si.touse.head = freechunk( p );
            VALGRIND_MAKE_MEM_NOACCESS( dereference( p ), sizeof( Pointer ) );
#pragma GCC diagnostic pop
            return p;
        }

        Pointer allocate( int size )
        {
            Pointer p;

            auto &si = sizeinfo( size );
            /* try our private freelist first */

            if ( !si.touse.count && si.tofree.count ) {
                si.touse = si.tofree;
                si.tofree = FreeList();
            }

            if ( si.touse.count )
                p = fromFreelist( si );
            else { /* nope. try a partially filled block */
                if ( si.active >= 0 && usable( si.active ) ) {
                    p.block = si.active;
                    p.offset = lake->header( p ).allocated ++;
                } else { /* still nothing. try nicking something from the shared freelist */
                    std::atomic< FreeList * > &fhead = lake->freelist( size );
                    FreeList *fb = fhead;
                    while ( fb && !fhead.compare_exchange_weak( fb, fb->next ) );
                    if ( fb ) {
                        si.touse = *fb;
                        si.touse.next = nullptr;
                        delete fb;
                        p = fromFreelist( si );
                    } else { /* give up and allocate a fresh block */
                        p.block = newblock( size );
                        p.offset = lake->header( p ).allocated ++;
                    }
                }

            }

            lake->valgrindAllocated( p );
            return p;
        }

        void free( Pointer p )
        {
            if ( !valid( p ) )
                return;

            ASSERT( lake->header( p ).total > 0 && "trying to free ephemeral block" );

            auto &si = sizeinfo( size( p ) );
            FreeList *fl = si.touse.count < 4096 ? &si.touse : &si.tofree;
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wold-style-cast"
            VALGRIND_MAKE_MEM_UNDEFINED( dereference( p ), sizeof( Pointer ) );
#pragma GCC diagnostic pop
            freechunk( p ) = fl->head;
            fl->head = p;
            ++ fl->count;

            lake->valgrindDeallocated( p );

            /* If there's a lot on our freelists, donate part of them to the Lake */
            if ( fl == &si.tofree && fl->count >= 4096 ) {
                std::atomic< FreeList * > &fhead = lake->freelist( size( p ) );
                fl = new FreeList( *fl );
                fl->next = fhead;
                while ( !fhead.compare_exchange_weak( fl->next, fl ) );
                si.tofree = FreeList();
            }
        }

        bool usable( int b )
        {
            return lake->block[ b ] &&
                lake->header( b ).allocated < lake->header( b ).total;
        }

        SizeInfo &sizeinfo( int index )
        {
            if ( index < 4096 )
                return _size[ index ];
            if ( !_size_big[ index / 4096 ] )
                _size_big[ index / 4096 ] = new SizeInfo[ 4096 ];
            return _size_big[ index / 4096 ][ index % 4096 ];
        }

        int newblock( int size )
        {
            int b = 0;

            if ( _emptyblocks.empty() ) {
                b = lake->usedblocks.fetch_add( 16 );
                for ( int i = b + 1; i < b + 16; ++i )
                    _emptyblocks.push_back( i );
            } else {
                b = _emptyblocks.back();
                _emptyblocks.pop_back();
            }

            auto &si = sizeinfo( size );

            const int overhead = sizeof( BlockHeader );
            const int allocsize = align( size, sizeof( Pointer ) );
            si.blocksize = std::max( allocsize + overhead, si.blocksize );
            const int total = allocsize ? ( si.blocksize - overhead ) / allocsize : 0;
            const int allocate = allocsize ? overhead + total * allocsize : blocksize;

            auto mem = brick::mmap::MMap::alloc( allocate );
            lake->block[ b ] = static_cast< char * >( mem );
            lake->header( b ).itemsize = size;
            lake->header( b ).total = total;
            lake->header( b ).allocated = 0;
            lake->valgrindNewBlock( b, total );
            si.blocksize = std::min( 4 * si.blocksize, int( blocksize ) );
            return si.active = b;
        }

    };

    BlockHeader &header( Pointer p ) { return header( p.block ); }
    BlockHeader &header( int b ) {
        return *reinterpret_cast< BlockHeader * >( block[ b ] );
    }

    char *dereference( Pointer p ) {
        return block[ p.block ] + sizeof( BlockHeader ) +
            p.offset * align( header( p ).itemsize, sizeof( Pointer ) );
    }

    int size( Pointer p ) {
        return header( p ).itemsize;
    }

};

/*
 * A Lake-like thing, but forward everything to the system allocator. Comes
 * with substantially more overhead.
 */
struct Pond {

    struct PtrHeader {
        uint32_t size;

    };

    struct Pointer : brick::types::Comparable {
        using Raw = uintptr_t;
        static constexpr int tagBits = 2;
        static constexpr Raw tagMask = 0x3;

        Pointer() : _ptr( nullptr ) { }
        Pointer( void *ptr ) : _ptr( ptr ) {
            ASSERT_EQ( tag(), 0u );
        }

        Raw raw() const { return _ptr.raw; }

        static Pointer fromRaw( Raw r ) {
            Pointer p;
            p._ptr.raw = r;
            return p;
        }

        Pointer untagged() const {
            Pointer p( *this );
            p.setTag( 0 );
            return p;
        }
        void *raw_ptr() const { return untagged()._ptr.ptr; }
        Raw raw_address() const { return untagged()._ptr.raw; }

        unsigned tag() const { return _ptr.raw & tagMask; }
        void setTag( unsigned tag ) {
            ASSERT_EQ( tag & 0x3u, tag );
            _ptr.raw &= ~tagMask;
            _ptr.raw |= tag & tagMask;
        }

        explicit operator bool() const { return untagged()._ptr.ptr; }
        bool operator!() const { return !bool( *this ); }
        bool operator<=( const Pointer &p ) const { return raw() <= p.raw(); }

        char *ptr() const { return static_cast< char * >( raw_ptr() ) + sizeof( PtrHeader ); }

        PtrHeader &header() { return *static_cast< PtrHeader * >( raw_ptr() ); }

        static Pointer allocate( int n ) {
            Pointer p( ::operator new( n + sizeof( PtrHeader ) ) );
            p.header().size = n;
            ASSERT_EQ( p.tag(), 0u );
            return p;
        }
        void free() {
            ::operator delete( raw_ptr() );
            _ptr.ptr = nullptr;
        }

        union _Ptr {
            _Ptr( void *ptr ) : ptr( ptr ) { }
            void *ptr;
            Raw raw;
        } _ptr;
    };

    Pond() {}
    Pond( const Pond & ) = delete;

    struct Wharf {

        Wharf( std::shared_ptr< Pond > ) {}
        Wharf() {}

        char *dereference( Pointer p ) { return p.ptr(); }
        const char *dereference( Pointer p ) const { return p.ptr(); }
        bool valid( Pointer p ) { return bool( p ); }
        int size( Pointer p ) { return p.header().size; }
        bool alias( Pointer a, Pointer  b ) { return a.raw() == b.raw(); }
        void free( Pointer p ) { p.free(); }
        Pointer allocate( size_t s ) { return Pointer::allocate( s ); }
    };
};

using brick::hash::hash128_t;
using brick::hash::hash64_t;

template< typename MM >
struct Dereference {
    using Blob = typename MM::Pointer;
    using Wharf = typename MM::Wharf;
    using Shared = MM;

    Wharf wharf;

    Dereference() {}
    Dereference( std::shared_ptr< Shared > s ) : wharf( s ) {}


    template< typename T = char >
    T *dereference( Blob b ) {
        return reinterpret_cast< T * >( wharf.dereference( b ) );
    }

    template< typename T = char >
    const T *dereference( Blob b ) const {
        return reinterpret_cast< T * >( wharf.dereference( b ) );
    }

    Blob allocate( int size ) { return wharf.allocate( size ); }
    Blob ephemeralAllocate( int size ) { return wharf.ephemeralAllocate( size ); }
    void free( Blob b ) { wharf.free( b ); }
    void ephemeralFree( Blob b ) { wharf.ephemeralFree( b ); }
    int size( Blob b ) { return wharf.size( b ); }
    bool valid( Blob b ) { return wharf.valid( b ); }
    bool alias( Blob a, Blob b ) { return wharf.alias( a, b ); }

    template< typename T > T &get( T &x, int offset = 0 ) {
        ASSERT( !offset );
        return x;
    }

    template< typename T > T &get( Blob b, int offset = 0 ) {
        return *reinterpret_cast< T * >( wharf.dereference( b ) + offset );
    }

    template< typename T > T get( Blob b, int offset = 0 ) const {
        return *reinterpret_cast< const T * >( wharf.dereference( b ) + offset );
    }

    void copy( Blob from, Blob to ) {
        ASSERT_LEQ( size( to ), size( from ) );
        std::copy( dereference( from ), dereference( from ) + size( from ),
                   dereference( to ) );
    }

    void copy( Blob from, Blob to, int length ) {
        ASSERT_LEQ( length, size( from ) );
        ASSERT_LEQ( length, size( to ) );
        std::copy( dereference( from ), dereference( from ) + length,
                   dereference( to ) );
    }

    void clear( Blob b, int from = 0, int to = 0, char pattern = 0 ) {
        if ( to == 0 )
            to = size( b );
        std::fill( dereference( b ) + from, dereference( b ) + to, pattern );
    }

    bool lessthan( Blob a, Blob b ) {
        return std::lexicographical_compare(
            dereference( a ), dereference( a ) + size( a ),
            dereference( b ), dereference( b ) + size( b ) );
    }

    bool equal( Blob a, Blob b, int from = 0, int to = 0 ) {
        if ( to == 0 ) {
            if ( size( a ) != size( b ) )
                return false;
            to = size( a );
        }
        ASSERT_LEQ( from, to );
        ASSERT_LEQ( to, size( a ) );
        ASSERT_LEQ( to, size( b ) );
        return std::equal( dereference( a ) + from, dereference( a ) + to,
                           dereference( b ) + from );
    }

    hash128_t hash( Blob b ) { return hash( b, 0, size( b ), 0 ); }
    hash128_t hash( Blob b, int from, int to, uint64_t salt = 0 ) {
        if ( !valid( b ) )
            return std::make_pair( 0, 0 );
        ASSERT_LEQ( from, to );
        ASSERT_LEQ( to, size( b ) );
        return brick::hash::spooky( dereference( b ) + from, to - from, salt, salt );
    }

    void acquireLock( Blob ) { ASSERT_UNIMPLEMENTED(); }
    void releaseLock( Blob ) { ASSERT_UNIMPLEMENTED(); }
};

#if DEV_NOPOOLS
typedef Dereference< Pond > Pool;
#else
typedef Dereference< Lake > Pool;
#endif

typedef Pool::Blob Blob;

struct UnBlob {
    Blob b;
    Pool &p;
    UnBlob( Pool &p, Blob b ) : b( b ), p( p ) {}
};


// Since < and == operator of blob is to be removed, we want comparer which will work with STL
struct BlobComparerBase {
protected:
    Pool *_pool;

    BlobComparerBase( Pool& pool ) : _pool( &pool )
    { }
};

struct BlobComparerEQ : public BlobComparerBase {

    BlobComparerEQ( Pool& pool ) : BlobComparerBase( pool )
    { }

    bool operator()( Blob a, Blob b ) const {
        return _pool->equal( a, b );
    }

    template< typename T >
    bool operator()( const std::pair<Blob, T>& a, const std::pair<Blob, T>& b) const {
        return _pool->equal( a.first, b.first ) && a.second == b.second;
    }

    bool operator()( const std::tuple<>&, const std::tuple<>& ) const {
        return true;
    }

    template< typename... TS >
    bool operator()( const std::tuple< TS... >& a, const std::tuple< TS... >& b ) const {
        return compareTuple< sizeof...( TS ), 0, TS... >( a, b );
    }

    template< size_t size, size_t i, typename... TS >
    typename std::enable_if< ( size > i ), bool >::type compareTuple(
            const std::tuple< TS... >& a, const std::tuple< TS... >& b ) const
    {
        bool x = (*this)( std::get< i >( a ), std::get< i >( b ) );
        return x
            ? compareTuple< size, i + 1, TS... >( a, b )
            : false;
    }

    template< size_t size, size_t i, typename... TS >
    typename std::enable_if< ( size <= i ), bool >::type compareTuple(
            const std::tuple< TS... >&, const std::tuple< TS... >& ) const
    {
        return true;
    }

    template< typename T >
    bool operator()( const T& a, const T& b ) const {
        return a == b;
    }
};

struct BlobComparerLT : public BlobComparerBase {
    BlobComparerEQ eq;

    BlobComparerLT( Pool& pool ) : BlobComparerBase( pool ), eq( pool )
    { }

    bool operator()( const Blob& a, const Blob& b ) const {
        return _pool->lessthan( a, b );
    }

    // lexicongraphic tuple ordering
    template< typename T >
    bool operator()( const std::pair<Blob, T>& a, const std::pair<Blob, T>& b) const {
        if ( _pool->lessthan( a.first, b.first ) )
            return true;
        else
            return eq( a.first, b.first ) ? a.second < b.second : false;
    }

    bool operator()( const std::tuple<>&, const std::tuple<>& ) const {
        return false;
    }

    template< typename... TS >
    bool operator()( const std::tuple< TS... >& a, const std::tuple< TS... >& b ) const {
        return compareTuple< sizeof...( TS ), 0, TS... >( a, b );
    }

    template< size_t size, size_t i, typename... TS >
    typename std::enable_if< ( size > i ), bool >::type compareTuple(
            const std::tuple< TS... >& a, const std::tuple< TS... >& b ) const
    {
        bool x = eq( std::get< i >( a ), std::get< i >( b ) );
        return x
            ? compareTuple< size, i + 1, TS... >( a, b )
            : (*this)( std::get< i >( a ), std::get< i >( b ) );
    }

    template< size_t size, size_t i, typename... TS >
    typename std::enable_if< ( size <= i ), bool >::type compareTuple(
            const std::tuple< TS... >&, const std::tuple< TS... >& ) const
    {
        return false;
    }

    template< typename T >
    bool operator()( const T& a, const T& b ) const {
        return a < b;
    }
};


std::ostream &operator<<( std::ostream &o, const Pool &p );

struct LongTerm {
    Blob get( Pool &p, int sz ) { return p.allocate( sz ); }
    void drop( Pool &p, Blob ptr ) { return p.free( ptr ); }
};

#if DEV_NOPOOLEPHEMERAL
using Ephemeral = LongTerm;
#else
struct Ephemeral {
    Blob get( Pool &p, int sz ) { return p.ephemeralAllocate( sz ); }
    void drop( Pool &p, Blob ptr ) { return p.ephemeralFree( ptr ); }
};
#endif

}

namespace divine_test {
using namespace divine;

struct TestPool {

    struct Checker : brick::shmem::Thread
    {
        char padding[128];
        divine::Pool m_pool;
        std::deque< Blob > ptrs;
        int limit;
        unsigned seedp;
        int terminate;
        char padding2[128];

        Pool &pool() {
            return m_pool;
        }

        bool decide( int i ) {
            int j = rand() % limit;
            if ( i + j > limit )
                return false;
            return true;
        }

        void main()
        {
            limit = 32*1024;
            int state = 0;
            for ( int i = 0; i < limit; ++i ) {
                ASSERT( state >= 0 );
                if ( decide( i ) || ptrs.empty() ) {
                    ++ state;
                    ptrs.push_back( pool().allocate( 32 ) );
                } else {
                    -- state;
                    pool().free( ptrs.front() );
                    ptrs.pop_front();
                }
            }
            while ( !ptrs.empty() ) {
                pool().free( ptrs.front() );
                ptrs.pop_front();
            }
        }

        Checker()
            : terminate( 0 ) {}
    };

    TEST(stress) {
        std::vector< Checker > c;
        c.resize( 3 );
        for ( int j = 0; j < 5; ++j ) {
            for ( auto &t : c ) t.start();
            for ( auto &t : c ) t.join();
        }
    }
};

}

#endif
