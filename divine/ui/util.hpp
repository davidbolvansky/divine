// -*- mode: C++; indent-tabs-mode: nil; c-basic-offset: 4 -*-

/*
 * (c) 2017 Petr Ročkai <code@fixp.eu>
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
#include <chrono>

namespace divine::ui
{

using Clock = std::chrono::steady_clock;
using MSecs = std::chrono::milliseconds;

static std::string interval_str( MSecs i, bool subsec = false )
{
    using std::chrono::duration_cast;
    auto h = duration_cast< std::chrono::hours >( i );
    auto m = duration_cast< std::chrono::minutes >( i - h );
    auto s = duration_cast< std::chrono::seconds >( i - h - m );
    auto ms = i - h - m -s;
    std::stringstream t;
    t << std::setfill( '0' );
    if ( h.count() )
        t << h.count() << ":" << std::setw( 2 ) << m.count() << ":" << std::setw( 2 ) << s.count();
    else
        t << m.count() << ":" << std::setw( 2 ) << s.count();
    if ( subsec )
        t << "." << std::setw( 4 ) << ms.count();
    return t.str();
}

}
