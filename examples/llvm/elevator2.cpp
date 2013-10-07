/*
 * Name
 * ====================
 *  Elevator2
 *
 * Category
 * ====================
 *  Controller
 *
 * Short description
 * ====================
 *  Another elevator controller.
 *
 * Long description
 * ====================
 *  Motivated by model elevator2.dve (from the *BEEM database*), written by
 *  _Jiri Barnat_.
 *  Original idea comes from the elevator promela model from the *SPIN*
 *  distribution, but actually implements *LEGO* elevator model built in the
 *  Paradise laboratory.
 *
 *  The elevator is quite simple. There are no buttons inside the cabin,
 *  instead the elevator is completely controlled from outside
 *  (including destination selection). At each floor there is a button for
 *  calling the elevator. When the button is pressed, a new request carrying
 *  the floor number is created. Hopefully the elevator controller
 *  will eventually serve this request by sending the elevator to the floor
 *  from which the request originates.
 *  When the elevator arrives, doors opens for a short time and then
 *  the controller selects request from another floor to process next.
 *  Naive controller chooses the next floor to be served randomly, clever
 *  controller chooses the next floor with a pending request in the direction
 *  of the last cab movement to be served, if there is no
 *  such floor then in direction oposite to the direction of the last cab
 *  movement.
 *
 * Verification
 * ====================
 *     $ divine compile --llvm --cflags="-std=c++11 < other flags >" elevator2.cpp
 *     $ divine verify -p assert elevator2.bc [-d]
 *
 * Execution
 * ====================
 *     $ clang++ -std=c++11 [ < flags > ] -lpthread -lstdc++ -o elevator2.exe elevator2.cpp
 *     $ ./elevator2.exe
 *
 * Standard
 * ====================
 *  C++11
 */

// A number of served floors, should be >= 1.
#define FLOORS  5

// 1 = naive, 2 = clever
#define CONTROLLER  1

// Number of requests.
// -1 = infinite.
#define NUM_OF_REQUESTS  -1

#include <pthread.h>
#include <stdlib.h>
#include <unistd.h>
#include <assert.h>

#ifdef __divine__    // verification
#include "divine.h"
\
// If level 1 is requested, it is served eventually.
LTL(property1, G(r1 -> (F(c1 && open))));

// If level 1 is requested, it is served as soon as the cab passes.
LTL(property2, G(r1 -> (!c1 U (c1 U (c1 && open)))));

// If level 1 is requested, the cab passes the level without serving it at most once.
LTL(property3, G(r1 -> (!c1 U (c1 U (!c1 U (c1 U (c1 && open)))))));

// If level 2 is requested, the cab passes the level without serving it at most once.
LTL(property4, G(r2 -> (!c2 U (c2 U (!c2 U (c2 U (c2 && open)))))));

// The cab will remain at level 1 forever from some moment.
LTL(property5, F(G c1));

#else                // native execution
#include <iostream>

#define AP( x )

#define __divine_choice( x ) ( rand() % ( x ) )

pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

template <typename T>
void _info(const T& value) {
    std::cout << value << std::endl;
}

template <typename U, typename... T>
void _info(const U& head, const T&... tail) {
    std::cout << head;
    _info( tail... );
}
#endif

template <typename... T>
void info( const T&... args) {
#ifndef __divine__
    pthread_mutex_lock( &mutex );
    _info( args... );
    pthread_mutex_unlock( &mutex );
#endif
}

enum atoms { r1, r2, c1, c2, open };

struct Elevator;

struct Controller {

    virtual int next( Elevator * ) = 0;
};

struct Elevator {
    pthread_t thread;
    bool terminated;

    Controller *controller;
    int current; // Floor the elevator is currently in.

    bool request[ FLOORS ];
    int req_count;
    pthread_mutex_t mutex;

    int ldir; // Direction of the last cab movement (1 = up, -1 = down).

    int call( int floor ) {
#ifndef __divine__
        usleep( 500000 );
#endif
        assert( floor > 0 && floor <= FLOORS );
        if ( !request[ floor-1 ] ) {
            request[ floor-1 ] = true;
            _adjust_req_count( 1 );
            return 1;
        } else
            return 0;
    }

    void _move( int direction ) { // 1 = up, -1 = down
#ifndef __divine__
        usleep( 500000 );
#endif
        assert( direction == 1 || direction == -1 );
        current += direction;
        assert( current >= 1 && current <= FLOORS );
        if ( current == 1 )
            AP( c1 );
        if ( current == 2 )
            AP( c2 );
    }

    void _adjust_req_count( int inc ) {
        pthread_mutex_lock( &mutex );
        req_count += inc;
        pthread_mutex_unlock( &mutex );
    }

    static void *run( void *_self ) {
        Elevator *self = reinterpret_cast< Elevator* >( _self );
        int next;

        while ( !self->terminated ) {
            next = self->controller->next( self );
            if ( !next ) continue;
            assert( self->request[next-1] );
            self->ldir = ( next < self->current ? -1 : 1 );

            info( "Elevator is going to the ", next, ". floor.");
            while ( next < self->current )
                self->_move( -1 );
            while ( next > self->current )
                self->_move( 1 );
            AP( open ); // the doors are open
            info( "Elevator arrived at the ", self->current, ". floor.");

            self->request[next-1] = false;
            self->_adjust_req_count( -1 );
        }

        return NULL;
    }

    void terminate() {
        terminated = true;
        pthread_join( thread, NULL );
    }

    void start() {
        pthread_create( &thread, NULL, Elevator::run, reinterpret_cast< void* >( this ) );
    }

    Elevator( Controller *controller )
        : terminated( false ), controller( controller ), current( 1 ), req_count( 0 ),
          ldir( 1 ) {
        pthread_mutex_init( &mutex, NULL );
        for ( int i = 0; i < FLOORS; i++ )
            request[i] = false;
    }
};

struct Naive : public Controller {

    virtual int next( Elevator *elevator ) {
        if ( !elevator->req_count )
            return 0;

        int floor = __divine_choice( elevator->req_count ) + 1;
        int idx = -1;
        while ( floor ) {
            ++idx;
            if ( elevator->request[idx] )
                --floor;
        }
        return idx+1;
    }
};

struct Clever : public Controller  {

    virtual int next( Elevator *elevator ) {
        if ( !elevator->req_count )
            return 0;

        int i = elevator->current;
        int ldir = elevator->ldir;
        do {
            if ( ( i == 1 && ldir == -1 ) || ( i == FLOORS && ldir == 1 ) )
                ldir *= -1;
            i += ldir;
            assert( i > 0 && i <= FLOORS );
        } while( !elevator->request[i-1] );
        return i;
    }
};

struct Environment {

    Elevator* elevator;

    void start() {
#if ( NUM_OF_REQUESTS > -1 )
        for ( int i = 0; i < NUM_OF_REQUESTS; i++ ) {
#else
        for (;;) {
#endif
            // Randomly create new request.
            int dest = __divine_choice( FLOORS  ) + 1;
            info( "Calling for the elevator at the ", dest, ". floor." );
            if ( elevator->call( dest ) ) {
                if ( dest == 1 )
                    AP( r1 );
                if ( dest == 2 )
                    AP( r2 );
            }
        }
    }

    Environment ( Elevator* elevator ) : elevator( elevator ) {}

};

int main() {
    // Create a controller.
#if ( CONTROLLER == 1 )
    Naive controller;
#else
    Clever controller;
#endif

    // Create and start an elevator.
    Elevator elevator( &controller );
    elevator.start();

    // Create an environment.
    Environment env( &elevator );
    env.start();

#if ( NUM_OF_REQUESTS > -1 )
    while ( elevator.req_count );
    elevator.terminate();
#endif

    return 0;
}
