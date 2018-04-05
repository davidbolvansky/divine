// -*- mode: C++; indent-tabs-mode: nil; c-basic-offset: 4 -*-

/*
 * (c) 2018 Adam Matoušek <xmatous3@fi.muni.cz>
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

#include <divine/vm/mem-shadow-common.hpp>

namespace divine {
namespace vm::mem {

namespace bitlevel = brick::bitlevel;

struct DataException
{
    union {
        uint8_t bitmask[ 4 ];
        uint32_t bitmask_word;
    };

    bool valid() const { return bitmask_word != 0; }
    void invalidate() { bitmask_word = 0; }

    bool operator==( const DataException &o ) const { return bitmask_word == o.bitmask_word; }
    bool operator!=( const DataException &o ) const { return bitmask_word != o.bitmask_word; }
    bool operator-( const DataException &o ) const { return bitmask_word - o.bitmask_word; }

    bool bitmask_is_trivial() const {
        return bitmask_is_trivial( bitmask );
    }

    static bool bitmask_is_trivial( const uint8_t *m ) {
        for ( int i = 0; i < 4; ++i )
            if ( m[ i ] != 0x00 && m[ i ] != 0xff )
                return false;
        return true;
    }
};

inline std::ostream &operator<<( std::ostream &o, const DataException &e )
{
    if ( ! e.valid() )
    {
        o << "INVALID ";
    }

    o << " data exc.: ";
    for ( int i = 0; i < 4; ++i )
        o << std::hex << std::setw( 2 ) << std::internal
            << std::setfill( '0' ) << int( e.bitmask[ i ] ) << std::dec;

    return o;
}

/*
 * Shadow layer for tracking definedness of data
 * Required fields in Expanded:
 *      defined : 4 (less significant bits correspond to bytes on lower addresses)
 *      data_exception : 1
 *      pointer : 1
 *      pointer_exception : 1 (if set, data_exception shall be set as well)
 */

template< typename NextLayer >
struct DefinednessLayer : public NextLayer
{
    using Internal = typename NextLayer::Internal;
    using Loc = typename NextLayer::Loc;
    using Expanded = typename NextLayer::Expanded;

    class DataExceptions : public ExceptionMap< DataException, Internal >
    {
    public:
        using Base = ExceptionMap< DataException, Internal >;

    private:
        using Lock = typename Base::Lock;
        using Base::_exceptions;
        using Base::_mtx;

    public:
        void dump() const
        {
            std::cout << "exceptions: {\n";
            for ( auto &e : _exceptions )
            {
                std::cout << "  {" << e.first.object._raw << " + "
                   << e.first.offset << ": " << e.second << "}\n";
            }
            std::cout << "}\n";
        }

        using Base::set;

        void set( Internal obj, int wpos, const uint8_t *mask )
        {
            ASSERT_EQ( wpos % 4, 0 );

            Lock lk( _mtx );
            auto & exc = _exceptions[ Loc( obj, wpos ) ];
            std::copy( mask, mask + 4, exc.bitmask );
        }

        void get( Internal obj, int wpos, uint8_t *mask_dst )
        {
            ASSERT_EQ( wpos % 4, 0 );

            Lock lk( _mtx );

            auto it = _exceptions.find( Loc( obj, wpos ) );

            ASSERT( it != _exceptions.end() );
            ASSERT( it->second.valid() );

            std::copy( it->second.bitmask, it->second.bitmask + 4, mask_dst );
        }

        /** Which bits of 'pos'th byte in pool object 'obj' are initialized */
        uint8_t defined( Internal obj, int pos )
        {
            Lock lk( _mtx );

            int wpos = ( pos / 4 ) * 4;
            auto it = _exceptions.find( Loc( obj, wpos ) );
            if ( it != _exceptions.end() && it->second.valid() )
            {
                return it->second.bitmask[ pos % 4 ];
            }
            return 0x00;
        }
    };

    std::shared_ptr< DataExceptions > _def_exceptions;
    uint8_t current_def_from[ 4 ];
    uint8_t current_def_to[ 4 ];

    DefinednessLayer() : _def_exceptions( new DataExceptions ) {}

    template< typename OtherSh >
    int compare_word( OtherSh &a_sh, typename OtherSh::Loc a, Expanded exp_a, Loc b, Expanded exp_b )
    {
        // This function assumes that it is called only if there is a data exception, which
        // currently holds. Should it cease to, it will be necessary to rewrite this code.
        ASSERT( exp_a.data_exception );
        ASSERT( exp_b.data_exception );

        union {
            uint8_t def_bytes[ 4 ];
            uint32_t def_word;
        } da, db;

        a_sh._def_exceptions->get( a.object, a.offset, da.def_bytes );
        _def_exceptions->get( b.object, b.offset, db.def_bytes );

        int cmp = da.def_word - db.def_word;
        if ( cmp )
            return cmp;

        return NextLayer::compare_word( a_sh, a, exp_a, b, exp_b );
    }

    void free( Internal p )
    {
        _def_exceptions->free( p );

        NextLayer::free( p );
    }

    template< typename V >
    void write( Loc l, V value, Expanded *exp )
    {
        NextLayer::write( l, value, exp );

        constexpr int sz = sizeof( typename V::Raw );

        auto obj = l.object;

        union
        {
            typename V::Raw _def_mask;
            uint8_t _def_bytes[ sz ];
        };

        _def_mask = value.defbits();

        int off = 0,
            w = 0;

        if ( sz >= 4 )
            for ( ; off < bitlevel::downalign( sz, 4 ); off += 4, ++w )
                _write_def( _def_bytes + off, obj, l.offset + off, exp[ w ] );

        if ( sz % 4 )
        {
            auto tail_off = bitlevel::downalign( l.offset + off, 4 );
            _read_def( current_def_to, obj, tail_off, exp[ w ] );
            std::copy( _def_bytes + off, _def_bytes + sz,
                       current_def_to + ( ( l.offset + off ) % 4 ) );
            _write_def( current_def_to, obj, tail_off, exp[ w ] );
        }
    }

    template< typename V >
    void read( Loc l, V &value, Expanded *exp )
    {
        constexpr int sz = sizeof( typename V::Raw );

        auto obj = l.object;

        union
        {
            typename V::Raw _def_mask;
            uint8_t _def_bytes[ sz ];
        };

        int off = 0,
            w = 0;

        if ( sz >= 4 )
            for ( ; off < bitlevel::downalign( sz, 4 ); off += 4, ++w )
                _read_def( _def_bytes + off, obj, l.offset + off, exp[ w ] );

        if ( sz % 4 )
        {
            auto tail_off = bitlevel::downalign( l.offset + off, 4 );
            _read_def( current_def_to, obj, tail_off, exp[ w ] );
            std::copy( current_def_to + ( ( l.offset + off ) % 4 ),
                       current_def_to + ( ( l.offset + off ) % 4 ) + sz % 4,
                       _def_bytes + off );
        }

        value.defbits( _def_mask );

        NextLayer::read( l, value, exp );
    }

    // Fast copy
    template< typename FromSh >
    void copy_word( FromSh &from_sh, typename FromSh::Loc from, Expanded exp_src,
                    Loc to, Expanded exp_dst )
    {
        if ( exp_src.data_exception )
            _def_exceptions->set( to.object, to.offset,
                                  from_sh._def_exceptions->at( from.object, from.offset ) );
        else if ( exp_dst.data_exception )
            _def_exceptions->at( to.object, to.offset ).invalidate();

        NextLayer::copy_word( from_sh, from, exp_src, to, exp_dst );
    }

    // Slow copy
    template< typename FromSh, typename FromHeapReader >
    void copy_init_src( FromSh &from_sh, typename FromSh::Internal obj, int off,
                        const Expanded &exp, FromHeapReader fhr )
    {
        NextLayer::copy_init_src( from_sh, obj, off, exp, fhr );

        from_sh._read_def( current_def_from, obj, off, exp );
    }

    template< typename ToHeapReader >
    void copy_init_dst( Internal obj, int off, const Expanded &exp, ToHeapReader thr )
    {
        NextLayer::copy_init_dst( obj, off, exp, thr );

        _read_def( current_def_to, obj, off, exp );
    }

    template< typename FromSh, typename FromHeapReader, typename ToHeapReader >
    void copy_byte( FromSh &from_sh, typename FromSh::Loc from, const Expanded &exp_src,
                    FromHeapReader fhr, Loc to, Expanded &exp_dst, ToHeapReader thr )
    {
        NextLayer::copy_byte( from_sh, from, exp_src, fhr, to, exp_dst, thr );

        current_def_to[ to.offset % 4 ] = current_def_from[ from.offset % 4 ];
    }

    void copy_done( Internal obj, int off, Expanded &exp )
    {
        NextLayer::copy_done( obj, off, exp );
        _write_def( current_def_to, obj, off, exp );
    }

    void _read_def( uint8_t *dst, Internal obj, int off, const Expanded &exp )
    {
        ASSERT_EQ( off % 4, 0 );

        if ( exp.data_exception )
            _def_exceptions->get( obj, off, dst );
        /*
        else if ( exp.pointer )
        {
            for ( int i = 0; i < 4; ++i )
                dst[ i ] = 0xff;
        }
        */
        else
        {
            ASSERT_LT( exp.defined, 0x10 );

            alignas( 4 ) const unsigned char mask_table[] = {
                0x00, 0x00, 0x00, 0x00,
                0xff, 0x00, 0x00, 0x00,
                0x00, 0xff, 0x00, 0x00,
                0xff, 0xff, 0x00, 0x00,
                0x00, 0x00, 0xff, 0x00,
                0xff, 0x00, 0xff, 0x00,
                0x00, 0xff, 0xff, 0x00,
                0xff, 0xff, 0xff, 0x00,
                0x00, 0x00, 0x00, 0xff,
                0xff, 0x00, 0x00, 0xff,
                0x00, 0xff, 0x00, 0xff,
                0xff, 0xff, 0x00, 0xff,
                0x00, 0x00, 0xff, 0xff,
                0xff, 0x00, 0xff, 0xff,
                0x00, 0xff, 0xff, 0xff,
                0xff, 0xff, 0xff, 0xff,
            };

            auto mask = mask_table + 4 * exp.defined;
            std::copy( mask, mask + 4, dst );
        }
    }

    void _write_def( uint8_t *src, Internal obj, int off, Expanded &exp )
    {
        ASSERT_EQ( off % 4, 0 );

        bool was_exc = exp.data_exception;

        uint8_t def = 0x00;

        for ( int i = 0; i < 4; ++i )
            def |= ( src[ i ] == 0xff ? ( 0x1 << i ) : 0x00 );

        exp.defined = def;

        exp.data_exception = exp.pointer_exception || ! DataException::bitmask_is_trivial( src );

        if ( exp.data_exception )
            _def_exceptions->set( obj, off, src );
        else if ( was_exc )
            _def_exceptions->at( obj, off ).invalidate();
    }


};

}
}

