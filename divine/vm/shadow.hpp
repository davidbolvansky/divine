// -*- mode: C++; indent-tabs-mode: nil; c-basic-offset: 4 -*-

/*
 * (c) 2016 Petr Ročkai <code@fixp.eu>
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

#include <brick-types>
#include <utility>

#include <divine/vm/value.hpp>

namespace divine {
namespace vm {

/* ET = EntryType */
enum class ShadowET { Pointer, GhostSh, GhostOI, Direct, InitRun, UninitRun };

/*
 * Shadow entries track initialisation status and pointer locations. The shadow
 * map (see below) is made up of ShadowEntries that cover the entire object.
 * Non-pointer data is covered by Direct/InitRun/UninitRun entries, each
 * pointer, on the other hand, must be covered by a Pointer entry.
 *
 * The shadow map supports tracking fragmented pointers (this can happen during
 * byte-level copies, for example). However, such pointers are *expensive*:
 * each such pointer needs a pair of Ghost entries, and up to 8 fragment
 * entries (that is 80 bytes for a single pointer in the worst case). Each
 * fragmented pointer in a given shadow map comes with an 8 bit ID. For Ghost
 * entries, the ID is stored in the bit offset field, in the fragments, it is
 * stored in the type-specific area. The GhostSh entry holds the Shadow
 * object for the pointer, while the GhostOI holds the original object part of
 * the pointer. Each fragment contains a single byte of the fragmented pointer
 * (which byte this is is stored in the 'type or fragment id' field). The
 * content of that byte
 *
 * A normal (continuous) Pointer entry only needs 2 bits for tracking
 * definedness (object id, offset), the remaining 30 bits of the
 * 'type-specific' field are used to store the shadowmap object id that goes
 * along with this pointer.
 *
 * Since we only use 28 bits for the bit offset field, a single shadowmap can
 * cover at most 32M (this means that objects larger than 32M need a different
 * shadowmap representation).
 */

struct ShadowEntry
{
    using Bits = bitlevel::BitTuple<
        bitlevel::BitField< bool, 1 >, // fragmented?
        bitlevel::BitField< uint32_t, 3 >, // type or fragment
        bitlevel::BitField< uint32_t, 28 >, // bit offset
        bitlevel::BitField< uint32_t, 32 > >; // type-specific
    Bits _bits;
    auto fragmented() { return bitlevel::get< 0 >( _bits ); }
    auto type() { return bitlevel::get< 1 >( _bits ); }
    auto offset() { return bitlevel::get< 2 >( _bits ); }
    auto data() { return bitlevel::get< 3 >( _bits ); }

    int size()
    {
        switch ( ShadowET( type().get() ) )
        {
            case ShadowET::Pointer: return PointerBits;
            case ShadowET::UninitRun:
            case ShadowET::InitRun: return data();
            case ShadowET::Direct: return 32;
            default: NOT_IMPLEMENTED();
        }
    }

    friend std::ostream &operator<<( std::ostream &o, ShadowEntry e )
    {
        return o << "[shadow @" << e.offset().get() << ", " << "t = " << e.type().get()
                 << ", data = " << e.data() << "]";
    }
};

/*
 * An object shadow is an offset-sorted vector (for now, at least) of shadow
 * entries (see above). For now, all operations scan through the entire vector,
 * although for shadowmaps larger than ~8 entries, binary searching would be
 * more suitable (some objects can be hundreds of kilobytes).
 *
 * The Shadow structure does not hold any shadow data itself, the actual
 * entries are stored by the Heap object in an implementation-specific manner
 * and provided via an STL container interface of Entries.
 */

template< typename Entries, typename PointerV >
struct Shadow
{
    Entries _e;

    Shadow( const Shadow & ) = default;
    Shadow( Shadow & ) = default;
    Shadow( Shadow && ) = default;

    template< typename... Args >
    Shadow( Args&&... args ) : _e( std::forward< Args >( args )...  ) {}

    template< typename V >
    void update( int offset, V v ) {}

    template< typename V > /* value::_ */
    void query( int offset, V &v )
    {
    }

    void update_entry( ShadowEntry &e, int offset, PointerV v )
    {
        e.type() = int( ShadowET::Pointer );
        e.offset() = offset;
        e.data() = v._s.raw() & ~3;
        e.data() |= (v._obj_defined & 1);
        e.data() |= (v._off_defined & 1) << 1;
    }

    void update( int offset, PointerV v )
    {
        for ( auto &s : _e )
        {
            if ( s.offset() == offset && s.type() == int( ShadowET::Pointer ) )
            {
                std::cerr << "update " << s << " to " << std::flush;
                update_entry( s, offset, v );
                std::cerr << s << ", size = " << _e.size() << std::endl;
                return;
            }
        }
        _e.emplace_back();
        update_entry( _e.back(), offset, v );
    }

    void query( int offset, PointerV &v )
    {
        v._s = decltype( v._s )();
        v._obj_defined = v._off_defined = false;
        for ( auto &s : _e )
        {
            if ( s.offset() == offset && s.type() == int( ShadowET::Pointer ) )
            {
                v._obj_defined = s.data() & 1;
                v._off_defined = s.data() & 2;
                v._s = s.data() & ~3;
            }
            if ( s.offset() > offset )
                return;
        }
    }

    void update( Shadow from, int from_off, int to_off, int bytes )
    {
        auto f = from._e.begin(), f_end = from._e.end(),
             t = _e.begin(), t_end = _e.end();
        std::vector< ShadowEntry > merged;
        int index = 0;
        int diff = from_off - to_off;

        while ( f != f_end && f->offset() < from_off )
            ++ f;

        while ( t != t_end && t->offset() < to_off )
        {
            ++ t; ++ index;
        }

        while ( true )
        {
            if ( t < t_end && f < f_end )
            {
                if ( f->offset() + diff == t->offset() )
                {
                    merged.push_back( *f );
                    merged.back().offset() += diff;
                    ++ f; ++ t;
                }
                else if ( f->offset() + diff < t->offset() && f->offset() < from_off + bytes )
                {
                    merged.push_back( *f++ );
                    merged.back().offset() += diff;
                }
                else
                    merged.push_back( *t++ );
            }
            else if ( t < t_end )
                merged.push_back( *t++ );
            else
                break;
        }

        _e.reserve( index + merged.size() );
        std::copy( merged.begin(), merged.end(), _e.begin() + index );
    }

};

}

namespace t_vm {

struct Shadow
{
    using PointerV = vm::value::Pointer<>;
    using Entries = std::vector< vm::ShadowEntry >;
    using Sh = vm::Shadow< Entries, PointerV >;

    TEST( query )
    {
        vm::ShadowEntry e;
        e.offset() = 0;
        e.type().set( int( vm::ShadowET::Pointer ) );
        e.data() = 3;
        Entries es;
        es.push_back( e );
        Sh s( es );
        PointerV p( vm::nullPointer(), false );
        ASSERT( !p.defined() );
        s.query( 0, p );
        ASSERT( p.defined() );
    }

    TEST( update )
    {
        vm::ShadowEntry e;
        e.offset() = 0;
        e.type().set( int( vm::ShadowET::Pointer ) );
        e.data() = 0;
        Sh s;
        PointerV p;
        ASSERT( p.defined() );
        s.update( 0, p );
        ASSERT_EQ( s._e.size(), 1 );
        ASSERT_EQ( s._e[ 0 ].data(), 3 );
        s.query( 0, p );
        ASSERT( p.defined() );
    }

    TEST( shadowptr )
    {
        vm::ShadowEntry e;
        e.offset() = 0;
        e.type().set( int( vm::ShadowET::Pointer ) );
        e.data() = 0;
        Sh s;
        PointerV p;
        p._s = 255 << 2;
        ASSERT( p.defined() );
        s.update( 0, p );
        p._s = 0;
        ASSERT_EQ( s._e.size(), 1 );
        ASSERT_EQ( s._e[ 0 ].data(), 3 | (255 << 2) );
        s.query( 0, p );
        ASSERT( p.defined() );
        ASSERT( p.defined() );
        ASSERT_EQ( p._s.raw(), 255 << 2 );
    }
};

}

}
