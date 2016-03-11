/* $Id$ */

/* memcpy( void *, const void *, size_t )

   This file is part of the Public Domain C Library (PDCLib).
   Permission is granted to use, modify, and / or redistribute at will.
*/

#include <string.h>
#include <assert.h>

#ifndef REGTEST

void * memcpy( void * _PDCLIB_restrict s1, const void * _PDCLIB_restrict s2, size_t n )
{
    size_t distance = s1 > s2 ? s1 - s2 : s2 - s1;
    assert( distance >= n );
    return __divine_memcpy( s1, (void *)s2, n );
}

#endif

#ifdef TEST
#include <_PDCLIB_test.h>

int main( void )
{
    char s[] = "xxxxxxxxxxx";
    TESTCASE( memcpy( s, abcde, 6 ) == s );
    TESTCASE( s[4] == 'e' );
    TESTCASE( s[5] == '\0' );
    TESTCASE( memcpy( s + 5, abcde, 5 ) == s + 5 );
    TESTCASE( s[9] == 'e' );
    TESTCASE( s[10] == 'x' );
    return TEST_RESULTS;
}
#endif
