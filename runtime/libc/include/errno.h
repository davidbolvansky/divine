/* Errors <errno.h>

   This file is part of the Public Domain C Library (PDCLib).
   Permission is granted to use, modify, and / or redistribute at will.
*/

#ifndef _PDCLIB_ERRNO_H
#define _PDCLIB_ERRNO_H _PDCLIB_ERRNO_H

#include "_PDCLIB_aux.h"
#include <_PDCLIB_errno.h>

#ifdef __divine__

#include <dios.h>
#define errno (*__dios_get_errno())

#else

_PDCLIB_EXTERN_C
extern int *__errno_location (void) __attribute__ ((__const__));
#define errno (*__errno_location ())
_PDCLIB_EXTERN_END

#endif

#endif
