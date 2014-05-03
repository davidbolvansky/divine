#ifndef USR_PTHREAD_H
#define USR_PTHREAD_H

/* Includes */

#include <time.h>
#include <sys/types.h>

/* Macros */

// internal macros
#define _INITIALIZED_RWLOCK ( 1 << 17 )

// pthread-specified macros
#define PTHREAD_CREATE_JOINABLE        0
#define PTHREAD_CREATE_DETACHED        1

#define PTHREAD_PRIO_INHERIT           0 /* TODO */
#define PTHREAD_PRIO_NONE              0 /* TODO */
#define PTHREAD_PRIO_PROTECT           0 /* TODO */

#define PTHREAD_SCOPE_PROCESS          0 /* TODO */
#define PTHREAD_SCOPE_SYSTEM           0 /* TODO */

#define PTHREAD_EXPLICIT_SCHED         0 /* TODO */
#define PTHREAD_INHERIT_SCHED          0 /* TODO */

  /* Single UNIX Specification v. 2  and later */
#define PTHREAD_MUTEX_NORMAL           0
#define PTHREAD_MUTEX_RECURSIVE        1
#define PTHREAD_MUTEX_ERRORCHECK       2
#define PTHREAD_MUTEX_DEFAULT          PTHREAD_MUTEX_NORMAL

  /* for compatibility (prior to SUS v.2) */
#define PTHREAD_MUTEX_TIMED_NP         PTHREAD_MUTEX_NORMAL
#define PTHREAD_MUTEX_RECURSIVE_NP     PTHREAD_MUTEX_RECURSIVE
#define PTHREAD_MUTEX_ERRORCHECK_NP    PTHREAD_MUTEX_ERRORCHECK
#define PTHREAD_MUTEX_FAST_NP          PTHREAD_MUTEX_NORMAL
#define PTHREAD_MUTEX_ADAPTIVE_NP      PTHREAD_MUTEX_FAST_NP

#define PTHREAD_MUTEX_INITIALIZER      { .once = 0, .owner = 0, .lockCounter = 0, .initialized = 1, .type = 0 }

#define PTHREAD_COND_INITIALIZER       { .mutex = NULL, .counter = 0, .initialized = 1, ._pad = 0 }

#define PTHREAD_ONCE_INIT              { .mtx = { .once = 1, .owner = 0, .lockCounter = 0, .initialized = 1, .type = 0 } }

#define PTHREAD_DESTRUCTOR_ITERATIONS  8

#define PTHREAD_CANCELED               ( (void *) -1 )
#define PTHREAD_CANCEL_ENABLE          0
#define PTHREAD_CANCEL_DISABLE         1
#define PTHREAD_CANCEL_DEFERRED        0
#define PTHREAD_CANCEL_ASYNCHRONOUS    1

#define PTHREAD_PROCESS_PRIVATE        0
#define PTHREAD_PROCESS_SHARED         1

#define PTHREAD_RWLOCK_INITIALIZER     { .wlock = ( PTHREAD_PROCESS_PRIVATE << 16  ) | _INITIALIZED_RWLOCK, \
                                         .rlocks = NULL }
#define PTHREAD_RWLOCK_WRITER_NONRECURSIVE_INITIALIZER_NP   PTHREAD_RWLOCK_INITIALIZER

#define PTHREAD_BARRIER_SERIAL_THREAD  1

#if __has_attribute( error ) && __has_attribute( warning )
#define _PTHREAD_UNSUPPORTED  __attribute__(( error("this function is not yet implemented") ))
#define _PTHREAD_NO_EFFECT    __attribute__(( warning("this function currently has no effect") ))
#else
#define _PTHREAD_UNSUPPORTED
#define _PTHREAD_NO_EFFECT
#endif

#define _PTHREAD_NOINLINE     __attribute__(( noinline ))

/* Data types */

typedef int pthread_attr_t;

typedef int pthread_t;
typedef union {
    struct {
        unsigned short gtid;
        unsigned short ltid:15;
        unsigned short initialized:1;
    };
    int asint;
} real_pthread_t;

typedef struct {
    unsigned short owner:16; // global thread id + 1
    unsigned short initialized:1;
    unsigned short once:1;
    unsigned short type:2;
    unsigned short lockCounter:12; // change _mutex_adjust_count if bitfield size changes
} pthread_mutex_t;

typedef struct {
    unsigned type; // just 2 bits needed
} pthread_mutexattr_t;

typedef pthread_mutex_t pthread_spinlock_t;

typedef struct {
    pthread_mutex_t * mutex;
    unsigned short counter;
    unsigned short initialized:1;
    unsigned short _pad:15;
} pthread_cond_t;

typedef int pthread_condattr_t;
typedef struct { pthread_mutex_t mtx; } pthread_once_t;

typedef struct _PerThreadData {
    void ** data;
    void ( *destructor )( void* );
    struct _PerThreadData *next, *prev;
} _PerThreadData;

typedef _PerThreadData* pthread_key_t;

typedef struct _ReadLock {
   int rlock;
   struct _ReadLock *next;
} _ReadLock;

typedef struct {
    int wlock;
    _ReadLock* rlocks;
} pthread_rwlock_t;
typedef int pthread_rwlockattr_t;

typedef struct {
    unsigned short counter;
    unsigned short initialized:1;
    unsigned short nthreads:15;
} pthread_barrier_t;

typedef int pthread_barrierattr_t;

struct sched_param {
    int sched_priority;
#if defined(_POSIX_SPORADIC_SERVER) || defined(_POSIX_THREAD_SPORADIC_SERVER)
    int sched_ss_low_priority;
    struct timespec sched_ss_repl_period;
    struct timespec sched_ss_init_budget;
    int sched_ss_max_repl;
#endif
};

/* Function prototypes */

#ifdef __cplusplus
extern "C" {
#endif

int pthread_atfork( void (*)(void), void (*)(void), void(*)(void) ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;

int pthread_create( pthread_t *, const pthread_attr_t *, void *(*)(void *), void * ) _PTHREAD_NOINLINE;
void pthread_exit( void * ) _PTHREAD_NOINLINE /* XXX _PTHREAD_UNSUPPORTED */;
int pthread_join( pthread_t, void ** ) _PTHREAD_NOINLINE;
int pthread_detach( pthread_t thread ) _PTHREAD_NOINLINE;

int pthread_attr_destroy( pthread_attr_t * ) _PTHREAD_NOINLINE;
int pthread_attr_init( pthread_attr_t * ) _PTHREAD_NOINLINE;
int pthread_attr_getdetachstate( const pthread_attr_t *, int * ) _PTHREAD_NOINLINE;
int pthread_attr_getguardsize( const pthread_attr_t *, size_t *) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_attr_getinheritsched( const pthread_attr_t *, int * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_attr_getschedparam( const pthread_attr_t *, struct sched_param * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_attr_getschedpolicy( const pthread_attr_t *, int * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_attr_getscope( const pthread_attr_t *, int * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_attr_getstack( const pthread_attr_t *, void **, size_t * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_attr_getstackaddr( const pthread_attr_t *, void ** ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_attr_getstacksize( const pthread_attr_t *, size_t * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_attr_setdetachstate( pthread_attr_t *, int ) _PTHREAD_NOINLINE;
int pthread_attr_setguardsize( pthread_attr_t *, size_t ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_attr_setinheritsched( pthread_attr_t *, int ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_attr_setschedparam( pthread_attr_t *, const struct sched_param * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_attr_setschedpolicy( pthread_attr_t *, int ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_attr_setscope( pthread_attr_t *, int ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_attr_setstack( pthread_attr_t *, void *, size_t ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_attr_setstackaddr( pthread_attr_t *, void * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_attr_setstacksize( pthread_attr_t *, size_t ) _PTHREAD_NOINLINE _PTHREAD_NO_EFFECT;

int pthread_getconcurrency( void ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_getcpuclockid( pthread_t, clockid_t * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_getschedparam( pthread_t, int *, struct sched_param * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_setconcurrency( int ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_setschedparam( pthread_t, int, const struct sched_param * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_setschedprio( pthread_t, int ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;

pthread_t pthread_self( void ) _PTHREAD_NOINLINE;
int pthread_equal( pthread_t, pthread_t ) _PTHREAD_NOINLINE;

int pthread_mutex_destroy( pthread_mutex_t * ) _PTHREAD_NOINLINE;
int pthread_mutex_init( pthread_mutex_t *, const pthread_mutexattr_t * ) _PTHREAD_NOINLINE;
int pthread_mutex_lock( pthread_mutex_t * ) _PTHREAD_NOINLINE;
int pthread_mutex_trylock( pthread_mutex_t * ) _PTHREAD_NOINLINE;
int pthread_mutex_unlock( pthread_mutex_t * ) _PTHREAD_NOINLINE;
int pthread_mutex_getprioceiling( const pthread_mutex_t *, int * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_mutex_setprioceiling( pthread_mutex_t *, int, int * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_mutex_timedlock( pthread_mutex_t *, const struct timespec * ) _PTHREAD_NOINLINE;

int pthread_mutexattr_destroy( pthread_mutexattr_t * ) _PTHREAD_NOINLINE;
int pthread_mutexattr_init( pthread_mutexattr_t * ) _PTHREAD_NOINLINE;
int pthread_mutexattr_gettype( const pthread_mutexattr_t *, int * ) _PTHREAD_NOINLINE;
int pthread_mutexattr_getprioceiling( const pthread_mutexattr_t *, int * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_mutexattr_getprotocol( const pthread_mutexattr_t *, int * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_mutexattr_getpshared( const pthread_mutexattr_t *, int * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_mutexattr_settype( pthread_mutexattr_t *, int ) _PTHREAD_NOINLINE;
int pthread_mutexattr_setprioceiling( pthread_mutexattr_t *, int ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_mutexattr_setprotocol( pthread_mutexattr_t *, int ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_mutexattr_setpshared( pthread_mutexattr_t *, int ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;

int pthread_spin_destroy( pthread_spinlock_t * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_spin_init( pthread_spinlock_t *, int ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_spin_lock( pthread_spinlock_t * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_spin_trylock( pthread_spinlock_t * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_spin_unlock( pthread_spinlock_t * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;

int pthread_key_create( pthread_key_t *, void (*)(void *) ) _PTHREAD_NOINLINE;
int pthread_key_delete( pthread_key_t ) _PTHREAD_NOINLINE;
int pthread_setspecific( pthread_key_t, const void * ) _PTHREAD_NOINLINE;
void *pthread_getspecific( pthread_key_t ) _PTHREAD_NOINLINE;

int pthread_cond_destroy( pthread_cond_t * ) _PTHREAD_NOINLINE;
int pthread_cond_init( pthread_cond_t *, const pthread_condattr_t * ) _PTHREAD_NOINLINE;
int pthread_cond_signal( pthread_cond_t * ) _PTHREAD_NOINLINE;
int pthread_cond_broadcast( pthread_cond_t * ) _PTHREAD_NOINLINE;
int pthread_cond_wait( pthread_cond_t *, pthread_mutex_t * ) _PTHREAD_NOINLINE;
int pthread_cond_timedwait( pthread_cond_t *, pthread_mutex_t *, const struct timespec * ) _PTHREAD_NOINLINE;

int pthread_condattr_destroy( pthread_condattr_t * ) _PTHREAD_NOINLINE _PTHREAD_NO_EFFECT;
int pthread_condattr_getclock( const pthread_condattr_t *, clockid_t * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_condattr_getpshared( const pthread_condattr_t *, int * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_condattr_init( pthread_condattr_t * ) _PTHREAD_NOINLINE _PTHREAD_NO_EFFECT;
int pthread_condattr_setclock( pthread_condattr_t *, clockid_t ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_condattr_setpshared( pthread_condattr_t *, int ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;

int pthread_once( pthread_once_t *, void (*)(void) ) _PTHREAD_NOINLINE;

int pthread_setcancelstate( int, int * ) _PTHREAD_NOINLINE;
int pthread_setcanceltype( int, int * ) _PTHREAD_NOINLINE _PTHREAD_NO_EFFECT;
int pthread_cancel( pthread_t ) _PTHREAD_NOINLINE _PTHREAD_NO_EFFECT;
void pthread_testcancel( void ) _PTHREAD_NOINLINE;
void pthread_cleanup_push( void (*)(void *), void * ) _PTHREAD_NOINLINE;
void pthread_cleanup_pop( int ) _PTHREAD_NOINLINE;

int pthread_rwlock_destroy( pthread_rwlock_t * ) _PTHREAD_NOINLINE;
int pthread_rwlock_init( pthread_rwlock_t *, const pthread_rwlockattr_t * ) _PTHREAD_NOINLINE;
int pthread_rwlock_rdlock( pthread_rwlock_t * ) _PTHREAD_NOINLINE;
int pthread_rwlock_wrlock( pthread_rwlock_t * ) _PTHREAD_NOINLINE;
int pthread_rwlock_tryrdlock( pthread_rwlock_t * ) _PTHREAD_NOINLINE;
int pthread_rwlock_trywrlock( pthread_rwlock_t * ) _PTHREAD_NOINLINE;
int pthread_rwlock_unlock( pthread_rwlock_t * ) _PTHREAD_NOINLINE;

int pthread_rwlockattr_destroy( pthread_rwlockattr_t * ) _PTHREAD_NOINLINE;
int pthread_rwlockattr_getpshared( const pthread_rwlockattr_t *, int * ) _PTHREAD_NOINLINE _PTHREAD_NO_EFFECT;
int pthread_rwlockattr_init( pthread_rwlockattr_t * ) _PTHREAD_NOINLINE;
int pthread_rwlockattr_setpshared( pthread_rwlockattr_t *, int ) _PTHREAD_NOINLINE _PTHREAD_NO_EFFECT;

int pthread_barrier_destroy( pthread_barrier_t * ) _PTHREAD_NOINLINE;
int pthread_barrier_init( pthread_barrier_t *, const pthread_barrierattr_t *, unsigned ) _PTHREAD_NOINLINE;
int pthread_barrier_wait( pthread_barrier_t * ) _PTHREAD_NOINLINE;

int pthread_barrierattr_destroy( pthread_barrierattr_t * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_barrierattr_getpshared( const pthread_barrierattr_t *, int * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_barrierattr_init( pthread_barrierattr_t * ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;
int pthread_barrierattr_setpshared( pthread_barrierattr_t *, int ) _PTHREAD_NOINLINE _PTHREAD_UNSUPPORTED;

int sched_get_priority_max(int) _PTHREAD_NOINLINE _PTHREAD_NO_EFFECT;
int sched_get_priority_min(int) _PTHREAD_NOINLINE _PTHREAD_NO_EFFECT;
int sched_getparam(pid_t, struct sched_param *) _PTHREAD_NOINLINE _PTHREAD_NO_EFFECT;
int sched_getscheduler(pid_t) _PTHREAD_NOINLINE _PTHREAD_NO_EFFECT;
int sched_rr_get_interval(pid_t, struct timespec *) _PTHREAD_NOINLINE _PTHREAD_NO_EFFECT;
int sched_setparam(pid_t, const struct sched_param *) _PTHREAD_NOINLINE _PTHREAD_NO_EFFECT;
int sched_setscheduler(pid_t, int, const struct sched_param *) _PTHREAD_NOINLINE _PTHREAD_NO_EFFECT;
int sched_yield(void) _PTHREAD_NOINLINE _PTHREAD_NO_EFFECT;

#ifdef __cplusplus
}
#endif
#endif
