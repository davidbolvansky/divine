/* TAGS: c++ */
/* VERIFY_OPTS: -o nofail:malloc */
//===----------------------------------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is dual licensed under the MIT and the University of Illinois Open
// Source Licenses. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

// <deque>

// deque& operator=(initializer_list<value_type> il);

#include <deque>
#include <cassert>

#include "min_allocator.h"

int main()
{
#ifndef _LIBCPP_HAS_NO_GENERALIZED_INITIALIZERS
    {
    std::deque<int> d;
    d = {3, 4, 5, 6};
    assert(d.size() == 4);
    assert(d[0] == 3);
    assert(d[1] == 4);
    assert(d[2] == 5);
    assert(d[3] == 6);
    }
#if __cplusplus >= 201103L
    {
    std::deque<int, min_allocator<int>> d;
    d = {3, 4, 5, 6};
    assert(d.size() == 4);
    assert(d[0] == 3);
    assert(d[1] == 4);
    assert(d[2] == 5);
    assert(d[3] == 6);
    }
#endif
#endif  // _LIBCPP_HAS_NO_GENERALIZED_INITIALIZERS
}
