/* $Id$ */

/* remove( const char * )

   This file is part of the Public Domain C Library (PDCLib).
   Permission is granted to use, modify, and / or redistribute at will.
*/

/* This is an example implementation of remove() fit for use with POSIX kernels.
*/

#include <stdio.h>

#ifndef REGTEST
#include <_PDCLIB_io.h>
#include <string.h>
#include <threads.h>
#include <_PDCLIB_glue.h>

#include <unistd.h>
#include <sys/stat.h>

extern FILE * _PDCLIB_filelist;
extern mtx_t _PDCLIB_filelist_lock;

int remove( const char * pathname )
{
    FILE * current = _PDCLIB_filelist;
    mtx_lock( &_PDCLIB_filelist_lock );
    while ( current != NULL )
    {
        if ( ( current->filename != NULL ) && ( strcmp( current->filename, pathname ) == 0 ) )
        {
            mtx_unlock( &_PDCLIB_filelist_lock );
            return EOF;
        }
        current = current->next;
    }
    mtx_unlock( &_PDCLIB_filelist_lock );

    struct stat st;
    stat( pathname, &st );
    if ( S_ISDIR( st.st_mode ) )
        return rmdir( pathname );
    return unlink( pathname );
}

#endif

#ifdef TEST
#include <_PDCLIB_test.h>

int main( void )
{
    /* Testing covered by ftell.c (and several others) */
    return TEST_RESULTS;
}

#endif

