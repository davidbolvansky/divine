#pragma once
#include <stdint.h>
#include <sys/cdefs.h>

#define _LART_IGNORE_RET __attribute__((__annotate__("lart.transform.ignore.ret")))
#define _LART_IGNORE_ARG __attribute__((__annotate__("lart.transform.ignore.arg")))
#define _LART_FORBIDDEN __attribute__((__annotate__("lart.transform.forbidden")))
#define _LART_INTERFACE \
    __attribute__((__used__,__nothrow__, __noinline__, __flatten__)) __invisible

#ifdef __cplusplus
extern "C" {
#endif
    _LART_INTERFACE void __lart_stash( void * );
    _LART_INTERFACE void * __lart_unstash();
#ifdef __cplusplus
}
#endif