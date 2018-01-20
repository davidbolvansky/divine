/* TAGS: min c */
#include <sys/vmutil.h>
#include <pthread.h>
#include <assert.h>

int x;

void *thr( void *ignored ) {
    int m = __vmutil_mask( 1 );
    assert( m == 0 );
    m = __vmutil_mask( 1 );
    assert( m == 1 );

    ++x;
    ++x;

    m = __vmutil_mask( 0 );
    assert( m == 1 );
    m = __vmutil_mask( 0 );
    assert( m == 0 );
    return NULL;
}

int main() {
    pthread_t tid;
    pthread_create( &tid, NULL, thr, NULL );
    assert( x == 0 || x == 2 );
    pthread_join( tid, NULL );
}
