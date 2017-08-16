// -*- C++ -*- (c) 2015,2017 Vladimír Štill <xstill@fi.muni.cz>

#ifndef __LART_WEAKMEM_H_
#define __LART_WEAKMEM_H_
#include <stdint.h>
#include <stdlib.h>

#if __cplusplus
#if __cplusplus >= 201103L
#define _WM_NOTHROW noexcept
#else
#define _WM_NOTHROW throw()
#endif
#else
#define _WM_NOTHROW __attribute__((__nothrow__))
#endif
#define _WM_INTERFACE _WM_NOTHROW __attribute__((__noinline__, __flatten__))

#ifdef __cplusplus
extern "C" {
#endif

volatile extern int __lart_weakmem_buffer_size;
volatile extern int __lart_weakmem_min_ordering;

enum __lart_weakmem_order {
    __lart_weakmem_order_unordered = 0,
    __lart_weakmem_order_monotonic = 0x1,
    __lart_weakmem_order_acquire = 0x2 | __lart_weakmem_order_monotonic,
    __lart_weakmem_order_release = 0x4 | __lart_weakmem_order_monotonic,
    __lart_weakmem_order_acq_rel = __lart_weakmem_order_acquire | __lart_weakmem_order_release,
    __lart_weakmem_order_seq_cst = 0x8 | __lart_weakmem_order_acq_rel,
    __lart_weakmem_order_atomic_op = 0x10
};

#ifdef __divine__
void __lart_weakmem_store( char *addr, uint64_t value, uint32_t bitwidth, __lart_weakmem_order ord ) _WM_INTERFACE;
uint64_t __lart_weakmem_load( char *addr, uint32_t bitwidth, __lart_weakmem_order ord ) _WM_INTERFACE;

void __lart_weakmem_fence( __lart_weakmem_order ord ) _WM_INTERFACE;
uint64_t __lart_weakmem_cas( char *addr, uint64_t expected, uint64_t value, uint32_t bitwidth,
                             __lart_weakmem_order _ordSucc, __lart_weakmem_order _ordFail ) _WM_INTERFACE;
void __lart_weakmem_cleanup( int32_t cnt, ... ) _WM_INTERFACE;
void __lart_weakmem_resize( char *addr, uint32_t newsize ) _WM_INTERFACE;

void __lart_weakmem_flusher_main( void * );
#endif

#ifdef __cplusplus
} // extern "C"
#endif

#ifdef __cplusplus

namespace lart {
namespace weakmem {

enum class MemoryOrder : uint32_t {
    Unordered = __lart_weakmem_order_unordered,
    Monotonic = __lart_weakmem_order_monotonic,
    Acquire = __lart_weakmem_order_acquire,
    Release = __lart_weakmem_order_release,
    AcqRel = __lart_weakmem_order_acq_rel,
    SeqCst = __lart_weakmem_order_seq_cst,
    AtomicOp = __lart_weakmem_order_atomic_op
};

}
}

#endif // __cplusplus
#endif // __LART_WEAKMEM_H_
