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

#include <divine/vm/context.hpp>
#include <divine/vm/heap.hpp>
#include <divine/vm/program.hpp>

namespace divine::vm
{

template< typename P, typename H >
bool Context< P, H >::enter_debug()
{
    if ( !debug_allowed() )
        -- _instruction_counter; /* dbg.call does not count */

    if ( debug_allowed() && !debug_mode() )
    {
        -- _instruction_counter;
        ASSERT( !_debug_depth );
        std::copy( _reg, _reg + _VM_CR_Last, _debug_reg );
        _reg[ _VM_CR_Flags ].integer |= _VM_CF_DebugMode;
        with_snap( [&]( auto &h ) { _debug_snap = h.snapshot(); } );
        return true;
    }
    else
        return false;
}

template< typename P, typename H >
void Context< P, H >::leave_debug()
{
    ASSERT( debug_allowed() );
    ASSERT( debug_mode() );
    ASSERT( !_debug_depth );
    std::copy( _debug_reg, _debug_reg + _VM_CR_Last, _reg );
    if ( _debug_persist.ptr.null() )
        with_snap( [&]( auto &h ) { h.restore( _debug_snap ); } );
    else
    {
        Heap from = heap();
        with_snap( [&]( auto &h ) { h.restore( _debug_snap ); } );
        vm::heap::clone( from, heap(), _debug_persist.ptr,
                            vm::heap::CloneType::SkipWeak, true );
        _debug_persist.ptr = nullPointer();
    }
}

}
