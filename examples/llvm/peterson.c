/*
 * Peterson
 * ========
 *  Peterson's mutual exclusion algorithm.
 *
 *  *tags*: mutual exclusion, C99
 *
 * Description
 * -----------
 *
 *  This program implements the Peterson's mutual exclusion algorithm. When
 *  compiled with `-DBUG`, the algorithm is incorrect but runs without tripping
 *  assertions more often than not.
 *
 * Parameters
 * ----------
 *
 *  - `BUG`: if defined than the algorithm is incorrect and violates the safety and the exclusion property
 *
 * LTL Properties
 * --------------
 *
 *  - `progress`: if a thread requests to enter a critical section, it will eventually be allowed to do so
 *  - `exclusion`: critical section can only be executed by one process at a time
 *
 * Verification
 * ------------
 *
 *  - all available properties with the default values of parameters:
 *
 *         $ divine compile --llvm peterson.c
 *         $ divine verify -p assert peterson.bc -d
 *         $ divine verify -p deadlock peterson.bc -d
 *         $ divine verify -p progress peterson.bc -f -d
 *         $ divine verify -p exclusion peterson.bc -d
 *
 *  - introducing a bug:
 *
 *         $ divine compile --llvm --cflags="-DBUG" peterson.c -o peterson-bug.bc
 *         $ divine verify -p assert peterson-bug.bc -d
 *         $ divine verify -p exclusion peterson-bug.bc -d
 *
 * Execution
 * ---------
 *
 *       $ clang -lpthread -o peterson.exe peterson.c
 *       $ ./peterson.exe
 */

#include <pthread.h>
#include <stdlib.h>
#include <assert.h>

#ifdef __divine__    // verification
#include "divine.h"

LTL(progress, G(wait1 -> F(critical1)) && G(wait2 -> F(critical2)));
/* TODO: progress fails due to lack of fairness */
LTL(exclusion, G(!(critical1 && critical2))); // OK

#else                // native execution
#define AP( x )

#endif

struct state {
    int flag[2];
    int turn;
    volatile int in_critical[2];
};

struct p {
    int id;
    pthread_t ptid;
    struct state *s;
};

enum APs { wait1, critical1, wait2, critical2 };

void * thread( void *in ) __attribute__((noinline));
void * thread( void *in ) {
	struct p* p = (struct p*) in;
#ifdef BUG
    p->s->flag[p->id] = 0;
#else // correct
    p->s->flag[p->id] = 1;
#endif
    p->s->turn = 1 - p->id;

    AP( p->id ? wait1 : wait2 );
    while ( p->s->flag[1 - p->id] == 1 && p->s->turn == 1 - p->id ) ;

    p->s->in_critical[p->id] = 1;
    AP( p->id ? critical1 : critical2 );
    assert( !p->s->in_critical[1 - p->id] );
    p->s->in_critical[p->id] = 0;

    p->s->flag[p->id] = 0;
    
    return NULL;
}

int main() {
    struct state *s = (struct state *) malloc( sizeof( struct state ) );
    struct p *one = (struct p*) malloc( sizeof( struct p ) ),
             *two = (struct p*) malloc( sizeof( struct p ) );
    if (!s || !one || !two)
        return 1;

    one->s = two->s = s;
    one->id = 0;
    two->id = 1;

    s->flag[0]   = 0;
    s->flag[1]   = 0;
    s->in_critical[0] = 0;
    s->in_critical[1] = 0;
    pthread_create( &one->ptid, NULL, thread, one );
    pthread_create( &two->ptid, NULL, thread, two );
    pthread_join( one->ptid, NULL );
    pthread_join( two->ptid, NULL );
    return 0;
}
