#include <assert.h>
#include <dirent.h>
#include <unistd.h>
#include <errno.h>
#include <sys/stat.h>

int main() {
    assert( mkdir( "dir", 0644 ) == 0 );
    errno = 0;
    DIR *d = opendir( "dir" );
    assert( d == NULL );
    assert( errno == EACCES );
    return 0;
}
