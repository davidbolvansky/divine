#include <sys/types.h>
#include <unistd.h>
#include <assert.h>

int main() {
    assert( getsid( 0 ) == 1 );

    pid_t pid = fork();

    if ( pid == 0 )
        assert( getsid( getpid() ) == 1 );
}
