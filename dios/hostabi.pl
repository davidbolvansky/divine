use POSIX;
my $cc = $ARGV[0];
my $preproc = `echo '#include <sys/syscall.h>' | $cc -E -Wp,-dM -`;
my @sc;

for ( split /\n/, $preproc )
{
    push @sc, $1 if /^#define SYS_([a-zA-Z_0-9]*)/;
}

my $prog =<<'EOF';
#define _POSIX_C_SOURCE 200809
#define _DEFAULT_SOURCE 1
#define _BSD_SOURCE 1

#include <stdio.h>
#include <string.h>
#include <assert.h>

#include <dirent.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <signal.h>
#include <unistd.h>
#include <setjmp.h>
#include <locale.h>
#include <pthread.h>

void output( const char *name, int offset, int size, const char *type )
{
    printf( "        struct { char __pad_%s[%d]; ", name, offset );

    if ( !strcmp( type, "uint" ) )
        printf( "__uint%d_t %s;", size * 8, name );
    else if ( !strcmp( type, "int" ) )
        printf( "__int%d_t %s;", size * 8, name );
    else if ( !strcmp( type, "buffer" ) )
        printf( "char %s[%d];", name, size );
    else
        printf( "%s %s;", type, name );
    printf( " };\n" );
}

#define FIELD(n, t) output( #n, (char *)&s.n - (char *)&s, sizeof( s.n ), #t )

int main()
{
EOF

sub print_struct
{
    my $name = shift;
    my $fields = shift;

    $prog .= <<EOF
    {
        printf("#ifdef _HOST_$name\\n");
        struct $name s;
        printf("struct _HOST_$name\\n{\\n    union\\n    {\\n");
        printf("        char __pad_struct[%zd];\\n", sizeof( s ) );
        $fields
        printf( "    };\\n} __attribute__((packed));\\n" );
        printf("#endif\\n\\n");
    }
EOF
}

print_struct( "stat", <<EOF );
    FIELD( st_mode,    uint );
    FIELD( st_dev,     uint );
    FIELD( st_ino,     uint );
    FIELD( st_nlink,   uint );
    FIELD( st_uid,     uint );
    FIELD( st_gid,     uint );
    FIELD( st_rdev,    uint );
    FIELD( st_atim,    struct timespec );
    FIELD( st_mtim,    struct timespec );
    FIELD( st_ctim,    struct timespec );
    FIELD( st_size ,   uint );
    FIELD( st_blocks , uint );
    FIELD( st_blksize, uint );
    // FIELD( st_flags, uint );
    // FIELD( st_gen, uint );
    // FIELD( __st_birthtim, TIME );
EOF

print_struct( "dirent", <<EOF );
    FIELD( d_ino,  uint );
    FIELD( d_name, buffer );
EOF

print_struct( "sigaction", <<EOF );
    FIELD( sa_handler,   __sa_handler_t );
    FIELD( sa_sigaction, __sa_sigaction_t );
    FIELD( sa_mask,      sigset_t );
    FIELD( sa_flags,     int );
    FIELD( sa_restorer,  __sa_restorer_t );
EOF

sub fmt
{
    my ( $def, $val, $fmt ) = @_;
    $val = $def unless ( scalar @_ > 1 );
    $fmt = "%d" unless ( $fmt );
    $prog .= "    printf(\"#define _HOST_$def $fmt\\n\", $val);\n";
}

sub line
{
    $prog .= "    printf(\"%s\\n\", \"$_[0]\");\n";
}

sub fail
{
    print $prog;
    die $@;
}

line("#ifndef _HOSTABI_H");
line("#define _HOSTABI_H");
line("");
fmt( "SYS_$_", "SYS_$_" ) for ( @sc );
fmt( "O_RDONLY" );
fmt( "O_WRONLY" );
fmt( "O_RDWR" );
fmt( "O_EXCL" );
fmt( "O_TRUNC" );
fmt( "O_APPEND" );
fmt( "O_NONBLOCK" );
fmt( "O_CREAT" );
fmt( "O_NOCTTY" );
fmt( "O_DIRECTORY" );
fmt( "O_NOFOLLOW" );

fmt( "SOCK_NONBLOCK" );
fmt( "SOCK_CLOEXEC" );

fmt( "MSG_PEEK" );
fmt( "MSG_DONTWAIT" );
fmt( "MSG_WAITALL" );

fmt( "S_ISUID" );
fmt( "S_ISGID" );

fmt( "S_IRWXU" );
fmt( "S_IRUSR" );
fmt( "S_IWUSR" );
fmt( "S_IXUSR" );

fmt( "S_IRWXG" );
fmt( "S_IRGRP" );
fmt( "S_IWGRP" );
fmt( "S_IXGRP" );

fmt( "S_IRWXO" );
fmt( "S_IROTH" );
fmt( "S_IWOTH" );
fmt( "S_IXOTH" );

fmt( "S_IFMT" );
fmt( "S_IFIFO" );
fmt( "S_IFCHR" );
fmt( "S_IFDIR" );
fmt( "S_IFBLK" );
fmt( "S_IFREG" );
fmt( "S_IFLNK" );
fmt( "S_IFSOCK" );
fmt( "S_ISVTX" );

fmt( "RLIMIT_CPU" );
fmt( "RLIMIT_FSIZE" );
fmt( "RLIMIT_DATA" );
fmt( "RLIMIT_STACK" );
fmt( "RLIMIT_CORE" );
fmt( "RLIMIT_RSS" );
fmt( "RLIMIT_MEMLOCK" );
fmt( "RLIMIT_NPROC" );
fmt( "RLIMIT_NOFILE" );
fmt( "RLIM_NLIMITS" );

fmt( "SIGABRT" );
fmt( "SIGFPE" );
fmt( "SIGILL" );
fmt( "SIGINT" );
fmt( "SIGSEGV" );
fmt( "SIGPIPE" );
fmt( "SIGTERM" );
fmt( "SIGQUIT" );
fmt( "SIGBUS" );
fmt( "SIGSYS" );
fmt( "SIGTRAP" );
fmt( "SIGXCPU" );
fmt( "SIGXFSZ" );
fmt( "SIGKILL" );
fmt( "SIGSTOP" );
fmt( "SIGALRM" );
fmt( "SIGHUP" );
fmt( "SIGTSTP" );
fmt( "SIGUSR1" );
fmt( "SIGUSR2" );
fmt( "SIGCHLD" );

fmt( "SIG_BLOCK" );
fmt( "SIG_UNBLOCK" );
fmt( "SIG_SETMASK" );
fmt( "_NSIG" );

fmt( "_SC_CLK_TCK" );

fmt( "F_DUPFD" );
fmt( "F_DUPFD_CLOEXEC" );
fmt( "F_GETFD" );
fmt( "F_SETFD" );
fmt( "F_GETFL" );
fmt( "F_SETFL" );
fmt( "F_GETOWN" );
fmt( "F_SETOWN" );

fmt( "F_GETLK" );
fmt( "F_SETLK" );
fmt( "F_SETLKW" );

fmt( "HOST_NAME_MAX" );

fmt( "_PC_LINK_MAX" );
fmt( "_PC_MAX_CANON" );
fmt( "_PC_MAX_INPUT" );
fmt( "_PC_NAME_MAX" );
fmt( "_PC_PATH_MAX" );
fmt( "_PC_PIPE_BUF" );
fmt( "_PC_CHOWN_RESTRICTED" );
fmt( "_PC_NO_TRUNC" );
fmt( "_PC_VDISABLE" );
fmt( "_PC_2_SYMLINKS" );
fmt( "_PC_ALLOC_SIZE_MIN" );
fmt( "_PC_ASYNC_IO" );
fmt( "_PC_FILESIZEBITS" );
fmt( "_PC_PRIO_IO" );
fmt( "_PC_REC_INCR_XFER_SIZE" );
fmt( "_PC_REC_MAX_XFER_SIZE" );
fmt( "_PC_REC_MIN_XFER_SIZE" );
fmt( "_PC_REC_XFER_ALIGN" );
fmt( "_PC_SYMLINK_MAX" );
fmt( "_PC_SYNC_IO" );
# fmt( "_PC_TIMESTAMP_RESOLUTION" );

fmt( "LC_ALL" );
fmt( "LC_COLLATE" );
fmt( "LC_CTYPE" );
fmt( "LC_MONETARY" );
fmt( "LC_NUMERIC" );
fmt( "LC_TIME" );
fmt( "LC_MESSAGES" );

my $uname = (POSIX::uname())[0];
fmt( "uname", '"' . $uname . '"', "\\\"%s\\\"" );

fmt( "is_linux",   $uname eq "Linux" ? 1 : 0);
fmt( "is_openbsd", $uname eq "OpenBSD" ? 1 : 0);
fmt( "mode_t", "(int) (8*sizeof(mode_t))", "__uint%d_t" );
fmt( "jmp_buf_size", "sizeof(jmp_buf)", "%zd" );
fmt( "pthr_mutex_t_size", "sizeof(pthread_mutex_t)", "%zd" );

$prog .= "#ifdef __GNU_LIBRARY__\n";
fmt( "is_glibc", 1 );
$prog .= "#else\n";
fmt( "is_glibc", 0 );
$prog .= "#endif\n";

line("");
line( "#endif" );

$prog .= "}\n";

print STDERR "|$cc -x c -o printabi -\n";
open CC, "|$cc -x c -o printabi -";
print CC $prog;
close CC or fail( "compile error" );
system("./printabi") == 0 or die "error running printabi";
