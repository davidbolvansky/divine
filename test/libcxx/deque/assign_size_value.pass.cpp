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

// void assign(size_type n, const value_type& v);

#include <deque>
#include <cassert>

#include "test_iterators.h"
#include "min_allocator.h"

template <class C>
C
make(int size, int start = 0 )
{
    const int b = 4096 / sizeof(int);
    int init = 0;
    if (start > 0)
    {
        init = (start+1) / b + ((start+1) % b != 0);
        init *= b;
        --init;
    }
    C c(init, 0);
    for (int i = 0; i < init-start; ++i)
        c.pop_back();
    for (int i = 0; i < size; ++i)
        c.push_back(i);
    for (int i = 0; i < start; ++i)
        c.pop_front();
    return c;
}

template <class C>
void
test(C& c1, int size, int v)
{
    typedef typename C::const_iterator CI;
    std::size_t c1_osize = c1.size();
    c1.assign(size, v);
    assert(c1.size() == size);
    assert(distance(c1.begin(), c1.end()) == c1.size());
    for (CI i = c1.begin(); i != c1.end(); ++i)
        assert(*i == v);
}

template <class C>
void
testN(int start, int N, int M)
{
    typedef typename C::iterator I;
    typedef typename C::const_iterator CI;
    C c1 = make<C>(N, start);
    test(c1, M, -10);
}

int main()
{
    {
    int rng[] = {0, 1, 2, 3};
    const int N = sizeof(rng)/sizeof(rng[0]);
    for (int i = 0; i < N; ++i)
        for (int j = 0; j < N; ++j)
            for (int k = 0; k < N; ++k)
                testN<std::deque<int> >(rng[i], rng[j], rng[k]);
    }
#if __cplusplus >= 201103L
    {
    int rng[] = {0, 1, 2, 3};
    const int N = sizeof(rng)/sizeof(rng[0]);
    for (int i = 0; i < N; ++i)
        for (int j = 0; j < N; ++j)
            for (int k = 0; k < N; ++k)
                testN<std::deque<int, min_allocator<int>> >(rng[i], rng[j], rng[k]);
    }
#endif
}
