// -*- C++ -*- (c) 2013 Petr Rockai <me@mornfall.net>

#include <limits.h>
#include <unistd.h>
#include <cstdlib>
#include <_PDCLIB_aux.h>
#include <divine.h>

/*
 * Glue code that ties various bits of C and C++ runtime to the divine runtime
 * support. It's not particularly pretty. Other bits of this code are also
 * exploded over external/ which is even worse.
 */

/* Memory allocation */
__attribute__((noinline)) void * malloc( size_t size ) _PDCLIB_nothrow {
    __divine_interrupt_mask();
    if ( __divine_choice( 2 ) )
        return __divine_malloc( size ); // success
    else
        return NULL; // failure
}

#define MIN( a, b )   ((a) < (b) ? (a) : (b))

__attribute__((noinline)) void *realloc( void *orig, size_t size ) _PDCLIB_nothrow {
    __divine_interrupt_mask();
    if ( !size ) {
        __divine_free( orig );
        return NULL;
    }
    if ( __divine_choice( 2 ) ) {
        void *n = __divine_malloc( size );
        if ( orig ) {
            ::memcpy( n, orig, MIN( size, __divine_heap_object_size( orig ) ) );
            __divine_free( orig );
        }
        return n;
    } else
        return NULL; // failure
}

/* TODO malloc currently gives zeroed memory */
void *calloc( size_t n, size_t size ) _PDCLIB_nothrow { return malloc( n * size ); }
void free( void * p) _PDCLIB_nothrow { return __divine_free( p ); }

/* IOStream */

void *__dso_handle; /* this is emitted by clang for calls to __cxa_exit for whatever reason */

extern "C" int __cxa_atexit( void ( *func ) ( void * ), void *arg, void *dso_handle ) {
    // TODO
    ( void ) func;
    ( void ) arg;
    ( void ) dso_handle;
    return 0;
}

extern "C" void *dlsym( void *, void * ) { __divine_problem( 9, 0 ); return 0; }
extern "C" void *__errno_location() { __divine_problem( 9, 0 ); return 0; }

extern "C" { /* POSIX kernel APIs */

    void raise( int ) { __divine_problem( 9, 0 ); }

}

extern "C" { /* pdclib glue functions */

    void _PDCLIB_Exit( int rv ) {
        if ( rv )
            __divine_problem( 1, "exit called with non-zero value" );
        __divine_unwind( INT_MIN );
    }
}

extern "C" int nanosleep(const struct timespec *req, struct timespec *rem) {
    // I believe we will do nothing wrong if we verify nanosleep as NOOP,
    // it does not guearantee anything anyway
    return 0;
}

extern "C" unsigned int sleep( unsigned int seconds ) {
    // same as nanosleep
    return 0;
}

extern "C" int usleep( useconds_t usec ) { return 0; }

extern "C" void _exit( int rv ) {
    _PDCLIB_Exit( rv );
}
