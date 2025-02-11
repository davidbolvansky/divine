// -*- mode: C++; indent-tabs-mode: nil; c-basic-offset: 4 -*-

/*
 * (c) 2020 Henrich Lauko <xlauko@mail.muni.cz>
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

#include <map>
#include <string>
#include <cstdint>
#include <variant>

namespace divine::smt
{
    struct Model
    {
        using var = std::string;
        using value = std::variant< std::uint64_t, double, std::string >;

        std::map< var, value > assignment;

        value& operator[](const var &v) { return assignment[v]; }

        template< typename stream >
        friend auto operator<<( stream &o, const Model &m )
            -> decltype( o << "" )
        {
            if ( m.assignment.empty() )
                return o << "empty model";
            for ( const auto &[name, val] : m.assignment )
                o << name << ":" << val << "\n";
            return o;
        }
    };
}
