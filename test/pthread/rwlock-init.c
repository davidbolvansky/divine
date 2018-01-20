/* TAGS: min threads c */
#include <pthread.h>
#include <assert.h>
#include <errno.h>

int main() {
    pthread_rwlock_t rwlock;
    int r = pthread_rwlock_init( &rwlock, NULL );
    assert( r == 0 );
    r = pthread_rwlock_init( &rwlock, NULL );
    assert( r == EBUSY );
    r = pthread_rwlock_destroy( &rwlock );
    assert( r == 0 );
    r = pthread_rwlock_init( &rwlock, NULL );
    assert( r == 0 );
}
