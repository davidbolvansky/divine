/* $Id$ */

/* strerror_r( int, char * , size_t )

   This file is part of the Public Domain C Library (PDCLib).
   Permission is granted to use, modify, and / or redistribute at will.
*/

#include <string.h>

#ifndef REGTEST

#include <_PDCLIB_locale.h>

#define MIN( a, b ) ( (a) < (b) ? (a) : (b) )

char * strerror_r( int errnum, char *buf, size_t buflen )
{
    if ( errnum == 0 || errnum >= _PDCLIB_ERRNO_MAX )
    {
        return (char *)"Unknown error";
    }
    else
    {
        char *src = _PDCLIB_threadlocale()->_ErrnoStr[errnum];
        int len = MIN( buflen - 1, strlen( src ) );
        memcpy( buf, src, len );
        buf[ len ] = '\0';
        return buf;
    }
}

#endif

#ifdef TEST
#include <_PDCLIB_test.h>

#include <stdio.h>
#include <errno.h>

int main( void )
{
    TESTCASE( strerror_r( ERANGE ) != strerror_r( EDOM ) );
    return TEST_RESULTS;
}
#endif
