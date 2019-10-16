/* TAGS: c++ fin */
/* CC_OPTS: -std=c++2a */
/* VERIFY_OPTS: -o nofail:malloc */
//===----------------------------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

// <set>

// class set

// set(const set& m, const allocator_type& a);

#include <set>
#include <cassert>

#include "test_macros.h"
#include "test_compare.h"
#include "test_allocator.h"

int main(int, char**)
{
    typedef int V;
    V ar[] =
    {
        1,
        1,
        1,
        2,
        2,
        2,
        3,
        3,
        3
    };
    typedef test_compare<std::less<int> > C;
    typedef test_allocator<V> A;
    std::set<int, C, A> mo(ar, ar+sizeof(ar)/sizeof(ar[0]), C(5), A(7));
    std::set<int, C, A> m(mo, A(3));
    assert(m.get_allocator() == A(3));
    assert(m.key_comp() == C(5));
    assert(m.size() == 3);
    assert(distance(m.begin(), m.end()) == 3);
    assert(*m.begin() == 1);
    assert(*next(m.begin()) == 2);
    assert(*next(m.begin(), 2) == 3);

    assert(mo.get_allocator() == A(7));
    assert(mo.key_comp() == C(5));
    assert(mo.size() == 3);
    assert(distance(mo.begin(), mo.end()) == 3);
    assert(*mo.begin() == 1);
    assert(*next(mo.begin()) == 2);
    assert(*next(mo.begin(), 2) == 3);

  return 0;
}
