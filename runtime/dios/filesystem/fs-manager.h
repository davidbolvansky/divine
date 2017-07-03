// -*- C++ -*- (c) 2015 Jiří Weiser

#include <tuple>
#include <memory>
#include <algorithm>
#include <utility>
#include <array>
#include <divine/stat.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <dios/core/main.hpp>
#include <bits/types.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <dios.h>


#include "fs-utils.h"
#include "fs-inode.h"
#include "fs-constants.h"
#include "fs-file.h"
#include "fs-directory.h"
#include "fs-snapshot.h"
#include "fs-descriptor.h"
#include "fs-path.h"

#ifndef _FS_MANAGER_H_
#define _FS_MANAGER_H_

namespace __dios {
namespace fs {

struct Manager {

    Manager() :
        Manager( true )
    {
        _standardIO[ 0 ]->assign( new( __dios::nofail ) StandardInput() );
    }

    Manager( const char *in, size_t length ) :
        Manager( true )
    {
        _standardIO[ 0 ]->assign( new( __dios::nofail ) StandardInput( in, length ) );
    }

    explicit Manager( std::initializer_list< SnapshotFS > items ) :
        Manager()
    {
        for ( const auto &item : items )
            _insertSnapshotItem( item );
    }

    Manager( const char *in, size_t length, std::initializer_list< SnapshotFS > items ) :
        Manager( in, length )
    {
        for ( const auto &item : items )
            _insertSnapshotItem( item );
    }

    void setOutputFile(FileTrace trace);

    void setErrFile(FileTrace trace);

    Node findDirectoryItem( __dios::String name, bool followSymLinks = true );
    void initializeFromSnapshot(const _VM_Env *env);

    void createHardLinkAt( int newdirfd, __dios::String name, int olddirfd, const __dios::String &target, Flags< flags::At > fl );
    void createSymLinkAt( int dirfd, __dios::String name, __dios::String target );
    template< typename... Args >
    Node createNodeAt( int dirfd, __dios::String name, mode_t mode, Args &&... args );

    ssize_t readLinkAt( int dirfd, __dios::String name, char *buf, size_t count );

    void accessAt( int dirfd, __dios::String name, Flags< flags::Access > mode, Flags< flags::At > fl );
    int openFileAt( int dirfd, __dios::String name, Flags< flags::Open > fl, mode_t mode );
    void closeFile( int fd );
    int duplicate( int oldfd, int lowEdge = 0 );
    int duplicate2( int oldfd, int newfd );
    std::shared_ptr< FileDescriptor > &getFile( int fd );
    std::shared_ptr< SocketDescriptor > getSocket( int sockfd );

    std::pair< int, int > pipe();

    void removeFile( __dios::String name );
    void removeDirectory( __dios::String name );
    void removeAt( int dirfd, __dios::String name, flags::At fl );

    void renameAt( int newdirfd, __dios::String newpath, int olddirfd, __dios::String oldpath );

    void truncate( Node inode, off_t length );

    off_t lseek( int fd, off_t offset, Seek whence );

    template< typename DirPre, typename DirPost, typename File >
    void traverseDirectoryTree( const __dios::String &root, DirPre pre, DirPost post, File file ) {
        Node current = findDirectoryItem( root );
        if ( !current || !current->mode().isDirectory() )
            return;
        if ( pre( root ) ) {
            for ( auto &i : *current->data()->as< Directory >() ) {

                if ( i.name() == "." || i.name() == ".." )
                    continue;

                __dios::String pathname = path::joinPath( root, i.name() );
                if ( i.inode()->mode().isDirectory() )
                    traverseDirectoryTree( pathname, pre, post, file );
                else
                    file( pathname );
            }

            post( root );
        }
    }

    Node currentDirectory() {
        return _currentDirectory.lock();
    }

    void getCurrentWorkingDir( char *buff, size_t size );

    void changeDirectory( __dios::String pathname );
    void changeDirectory( int dirfd );

    void chmodAt( int dirfd, __dios::String name, mode_t mode, Flags< flags::At > fl );
    void chmod( int fd, mode_t mode );

    mode_t umask() const {
        return _umask;
    }
    void umask( mode_t mask ) {
        _umask = Mode::GRANTS & mask;
    }

    int socket( SocketType type, Flags< flags::Open > fl );
    std::pair< int, int > socketpair( SocketType type, Flags< flags::Open > fl );
    void bind( int sockfd, Socket::Address address );
    void connect( int sockfd, const Socket::Address &address );
    int accept( int sockfd, Socket::Address &address );
    Node resolveAddress( const Socket::Address &address );
    bool wasError() const {
        return _error == 0;
    }

    int getError() const {
        return _error;
    }

    void setError(int code) {
        _error = code;
    }

private:
    Node _root;
    int _error;
    WeakNode _currentDirectory;
    std::array< Node, 3 > _standardIO;
    __dios::Vector< std::shared_ptr< FileDescriptor > > _openFD;

    unsigned short _umask;

    Manager( bool );// private default ctor

    std::pair< Node, __dios::String > _findDirectoryOfFile( __dios::String name );

    template< typename I >
    Node _findDirectoryItem( __dios::String name, bool followSymLinks, I itemChecker );

    int _getFileDescriptor( std::shared_ptr< FileDescriptor > f, int lowEdge = 0 );
    void _insertSnapshotItem( const SnapshotFS &item );

    void _checkGrants( Node inode, unsigned grant ) const;

    void _chmod( Node inode, mode_t mode );

};

#ifdef __divine__

# define FS_MALLOC( x ) __vm_obj_make( x )
# define FS_PROBLEM( msg ) __dios_fault( _VM_Fault::_VM_F_Assert, msg )
# define FS_FREE( x ) __dios::delete_object( x )

#else
# define FS_MALLOC( x ) std::malloc( x )
# define FS_PROBLEM( msg )
# define FS_FREE( x ) std::free( x )

#endif

namespace conversion {

    using namespace __dios::fs::flags;

    static inline __dios::fs::Flags <Open> open( int fls ) {
        __dios::fs::Flags <Open> f = Open::NoFlags;
        // special behaviour - check for access rights but do not grant them
        if (( fls & 3 ) == 3 )
            f |= Open::NoAccess;
        if ( fls & O_RDWR ) {
            f |= Open::Read;
            f |= Open::Write;
        }
        else if ( fls & O_WRONLY )
            f |= Open::Write;
        else
            f |= Open::Read;

        if ( fls & O_CREAT ) f |= Open::Create;
        if ( fls & O_EXCL ) f |= Open::Excl;
        if ( fls & O_TRUNC ) f |= Open::Truncate;
        if ( fls & O_APPEND ) f |= Open::Append;
        if ( fls & O_NOFOLLOW ) f |= Open::SymNofollow;
        if ( fls & O_NONBLOCK ) f |= Open::NonBlock;
        return f;
    }

    static inline int open( __dios::fs::Flags <Open> fls ) {
        int f;
        if ( fls.has( Open::NoAccess ))
            f = 3;
        else if ( fls.has( Open::Read ) && fls.has( Open::Write ))
            f = O_RDWR;
        else if ( fls.has( Open::Write ))
            f = O_WRONLY;
        else
            f = O_RDONLY;

        if ( fls.has( Open::Create )) f |= O_CREAT;
        if ( fls.has( Open::Excl )) f |= O_EXCL;
        if ( fls.has( Open::Truncate )) f |= O_TRUNC;
        if ( fls.has( Open::Append )) f |= O_APPEND;
        if ( fls.has( Open::SymNofollow )) f |= O_NOFOLLOW;
        if ( fls.has( Open::NonBlock )) f |= O_NONBLOCK;
        return f;
    }

    static inline __dios::fs::Flags <Message> message( int fls ) {
        __dios::fs::Flags <Message> f = Message::NoFlags;

        if ( fls & MSG_DONTWAIT ) f |= Message::DontWait;
        if ( fls & MSG_PEEK ) f |= Message::Peek;
        if ( fls & MSG_WAITALL ) f |= Message::WaitAll;
        return f;
    }

    static_assert( AT_FDCWD == __dios::fs::CURRENT_DIRECTORY,
                   "mismatch value of AT_FDCWD and __dios::fs::CURRENT_DIRECTORY" );
}

template < typename Next >
struct VFS: public Next {
    VFS() {
        // __divine_interrupt_mask();
        _manager = new( __dios::nofail ) Manager{};
    }
    VFS( const char *in, size_t length ) {
        // __divine_interrupt_mask();
        _manager = new( __dios::nofail ) Manager{ in, length };
    }
    explicit VFS( std::initializer_list< SnapshotFS > items ) {
        // __divine_interrupt_mask();
        _manager = new( __dios::nofail ) Manager{ items };
    }
    VFS( const char *in, size_t length, std::initializer_list< SnapshotFS > items ) {
        // __divine_interrupt_mask();
        _manager = new( __dios::nofail ) Manager{ in, length, items };
    }
    ~VFS() {
        if ( _manager )
            delete _manager;
    }

    Manager &instance() {
        __FS_assert( _manager );
        return *_manager;
    }


    void setup( Setup s ) {
        instance().setOutputFile( getFileTraceConfig( s.opts, "stdout" ) );
        instance().setErrFile( getFileTraceConfig( s.opts, "stderr" ) );
        instance().initializeFromSnapshot( s.env );

        Next::setup( s );
    }

     void getHelp( Map< String, HelpOption >& options ) {
        const char *opt1 = "{stdout|stderr}";
        if ( options.find( opt1 ) != options.end() ) {
            __dios_trace_f( "Option %s already present", opt1 );
            __dios_fault( _DiOS_F_Config, "Option conflict" );
        };

        options[ { opt1 } ] = { "specify how to treat program output",
          { "notrace - ignore the stream",
            "unbuffered - trace each write",
            "trace - trace after each newline (default)"} };

        const char *opt2 = "syscall";
        if ( options.find( opt2 ) != options.end() ) {
            __dios_trace_f( "Option %s already present", opt2 );
            __dios_fault( _DiOS_F_Config, "Option conflict" );
        };

        options[ { opt2 } ] = { "specify how to treat standard syscalls",
          { "simulate - simulate syscalls, use virtual file system (can be used with verify and run)",
            "passthrough - use syscalls from the underlying host OS (cannot be used with verify) " } };

        Next::getHelp( options );
    }

    void finalize()
    {
        delete _manager;
        _manager = nullptr;
        Next::finalize();
    }

    static FileTrace getFileTraceConfig( SysOpts& o, String stream ) {
        auto r = std::find_if( o.begin(), o.end(), [&]( const auto& o ) {
            return o.first == stream;
        } );
        if ( r == o.end() )
            return FileTrace::TRACE;
        String s = r->second;
        o.erase( r );
        if ( s == "notrace" )
            return FileTrace::NOTRACE;
        if ( s == "unbuffered" )
            return FileTrace::UNBUFFERED;
        if ( s == "trace" )
            return FileTrace::TRACE;
        __dios_trace_f( "Invalid configuration for file %s", stream.c_str() );
        __dios_fault( _DiOS_F_Config, "Invalid file tracing configuration" );
        __builtin_unreachable();
    }

    /*int _mknodat( int dirfd, const char *path, mode_t mode, dev_t dev );
    int _linkat(int olddirfd, const char *target, int newdirfd, const char *linkpath, int flags );
    static void _initStat( struct stat *buf );
    static int _fillStat( const __dios::fs::Node item, struct stat *buf );
    ssize_t _recvfrom(int sockfd, void *buf, size_t n, int flags, struct sockaddr *addr, socklen_t *len );
    int _accept4( int sockfd, struct sockaddr *addr, socklen_t *len, int flags );
    int _renameitemat( int olddirfd, const char *oldpath, int newdirfd, const char *newpath );*/


    /*#define GENERATE_VFS
    #include <dios/macro/syscall_component_header>
        #include <sys/syscall.def>
    #include <dios/macro/syscall_component_header.cleanup>
    #undef GENERATE_VFS*/

    static void _initStat( struct stat *buf )
    {
        buf->st_dev = 0;
        buf->st_rdev = 0;
        buf->st_atime = 0;
        buf->st_mtime = 0;
        buf->st_ctime = 0;
    }

    static int _fillStat( const __dios::fs::Node item, struct stat *buf )
    {
        if ( !item )
            return -1;
        _initStat( buf );
        buf->st_ino = item->ino( );
        buf->st_mode = item->mode( );
        buf->st_nlink = item.use_count( );
        buf->st_size = item->size( );
        buf->st_uid = item->uid( );
        buf->st_gid = item->gid( );
        buf->st_blksize = 512;
        buf->st_blocks = ( buf->st_size + 1 ) / buf->st_blksize;
        return 0;
    }

    int _mknodat( int dirfd, const char *path, mode_t mode, dev_t dev )
    {
            if ( dev != 0 )
                throw Error( EINVAL );
            if ( !S_ISCHR( mode ) && !S_ISBLK( mode ) && !S_ISREG( mode ) && !S_ISFIFO( mode ) && !S_ISSOCK( mode ))
                throw Error( EINVAL );
            instance().createNodeAt( dirfd, path, mode );
            return  0;
    }

    int creat( const char *path, mode_t mode  )
    {
        try {
            return _mknodat( AT_FDCWD, path, mode | S_IFREG, 0 );
        }catch( Error &e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int open( const char *path, int flags, mode_t mode )
    {
        using namespace __dios::fs::flags;
        __dios::fs::Flags <Open> f = Open::NoFlags;
        if (( flags & 3 ) == 3 )
            f |= Open::NoAccess;
        if ( flags & O_RDWR ) {
            f |= Open::Read;
            f |= Open::Write;
        }
        else if ( flags & O_WRONLY )
            f |= Open::Write;
        else
            f |= Open::Read;

        if ( flags & O_CREAT )
            f |= __dios::fs::flags::Open::Create;

        if ( flags & O_EXCL )
            f |= __dios::fs::flags::Open::Excl;
        if ( flags & O_TRUNC )
            f |= __dios::fs::flags::Open::Truncate;
        if ( flags & O_APPEND )
            f |= __dios::fs::flags::Open::Append;
        if ( flags & O_NOFOLLOW )
            f |= __dios::fs::flags::Open::SymNofollow;
        if ( flags & O_NONBLOCK )
            f |= __dios::fs::flags::Open::NonBlock;
        if ( flags & O_DIRECTORY )
            f |= __dios::fs::flags::Open::Directory;


        try {
            return instance( ).openFileAt( AT_FDCWD, path, f, mode );
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int openat( int dirfd, const char *path, int flags, mode_t mode )
    {
        using namespace __dios::fs::flags;
        __dios::fs::Flags <Open> f = Open::NoFlags;
        // special behaviour - check for access rights but do not grant them
        if (( flags & 3 ) == 3 )
            f |= Open::NoAccess;
        if ( flags & O_RDWR ) {
            f |= Open::Read;
            f |= Open::Write;
        }
        else if ( flags & O_WRONLY )
            f |= Open::Write;
        else
            f |= Open::Read;

        if ( flags & O_CREAT )
            f |= __dios::fs::flags::Open::Create;

        if ( flags & O_EXCL )
            f |= __dios::fs::flags::Open::Excl;
        if ( flags & O_TRUNC )
            f |= __dios::fs::flags::Open::Truncate;
        if ( flags & O_APPEND )
            f |= __dios::fs::flags::Open::Append;
        if ( flags & O_NOFOLLOW )
            f |= __dios::fs::flags::Open::SymNofollow;
        if ( flags & O_NONBLOCK )
            f |= __dios::fs::flags::Open::NonBlock;

        try {
            return instance( ).openFileAt( dirfd, path, f, mode );
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int fcntl( int fd, int cmd, va_list *vl )
    {
        try {
            auto f = instance( ).getFile( fd );

            switch ( cmd ) {
                case F_SETFD: {
                    if ( !vl )
                            FS_PROBLEM( "command F_SETFD requires additional argument" );
                    va_end( *vl );
                }
                case F_GETFD:
                    return 0;
                case F_DUPFD_CLOEXEC: // for now let assume we cannot handle O_CLOEXEC
                case F_DUPFD: {
                    if ( !vl )
                            FS_PROBLEM( "command F_DUPFD requires additional argument" );
                    int lowEdge = va_arg(  *vl, int );
                    va_end( *vl );
                    return instance( ).duplicate( fd, lowEdge );
                }
                case F_GETFL:
                    va_end( *vl );
                    return conversion::open( f->flags( ));
                case F_SETFL: {
                    if ( !vl )
                            FS_PROBLEM( "command F_SETFL requires additional argument" );
                    int mode = va_arg(  *vl, int );

                    if ( mode & O_APPEND )
                        f->flags( ) |= __dios::fs::flags::Open::Append;
                    else if ( f->flags( ).has( __dios::fs::flags::Open::Append ))
                        throw Error( EPERM );

                    if ( mode & O_NONBLOCK )
                        f->flags( ) |= __dios::fs::flags::Open::NonBlock;
                    else
                        f->flags( ).clear( __dios::fs::flags::Open::NonBlock );

                    va_end( *vl );
                    return 0;
                }
                default:
                    FS_PROBLEM( "the requested command is not implemented" );
                    va_end( *vl );
                    return 0;
            }

        } catch ( Error & e ) {
            va_end( *vl );
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int close( int fd )
    {
        try {
            instance().closeFile( fd );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    ssize_t write( int fd, const void *buf, size_t count )
    {
        try {
            auto f = instance( ).getFile( fd );
            return f->write( buf, count );
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    ssize_t read( int fd, void* buf, size_t count )
    {
        try {
            auto f = instance( ).getFile( fd );
            return f->read( buf, count );
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int pipe( int *pipefd )
    {
        try {
            std::tie( pipefd[ 0 ], pipefd[ 1 ] ) = instance( ).pipe( );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    off_t lseek( int fd, off_t offset, int whence )
    {
        try {
            __dios::fs::Seek w = __dios::fs::Seek::Undefined;
            switch ( whence ) {
                case SEEK_SET:
                    w = __dios::fs::Seek::Set;
                    break;
                case SEEK_CUR:
                    w = __dios::fs::Seek::Current;
                    break;
                case SEEK_END:
                    w = __dios::fs::Seek::End;
                    break;
            }
            return instance( ).lseek( fd, offset, w );
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int dup( int fd )
    {
       try {
            return instance( ).duplicate( fd );
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int dup2( int oldfd, int newfd )
    {
        try {
            return instance( ).duplicate2( oldfd, newfd );
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int ftruncate( int fd, off_t length )
    {
        try {
            auto item = instance( ).getFile( fd );
            if ( !item->flags( ).has( __dios::fs::flags::Open::Write ))
                throw Error( EINVAL );
            instance( ).truncate( item->inode( ), length );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int truncate( const char *path, off_t length )
    {
        try {
            auto item = instance( ).findDirectoryItem( path );
            instance( ).truncate( item, length );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int unlink( const char *path )
    {
        try {
            instance( ).removeFile( path );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int rmdir( const char *path )
    {
        try {
            instance( ).removeDirectory( path );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int unlinkat( int dirfd, const char *path, int flags )
    {
        __dios::fs::flags::At f;
        switch ( flags ) {
            case 0:
                f = __dios::fs::flags::At::NoFlags;
                break;
            case AT_REMOVEDIR:
                f = __dios::fs::flags::At::RemoveDir;
                break;
            default:
                f = __dios::fs::flags::At::Invalid;
                break;
        }
        try {
            instance( ).removeAt( dirfd, path, f );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int _linkat(int olddirfd, const char *target, int newdirfd, const char *linkpath, int flags )
    {

        __dios::fs::Flags <__dios::fs::flags::At> fl = __dios::fs::flags::At::NoFlags;
        if ( flags & AT_SYMLINK_FOLLOW ) fl |= __dios::fs::flags::At::SymFollow;
        if (( flags | AT_SYMLINK_FOLLOW ) != AT_SYMLINK_FOLLOW )
            fl |= __dios::fs::flags::At::Invalid;
            instance( ).createHardLinkAt( newdirfd, linkpath, olddirfd, target, fl );
            return 0;
    }

    int linkat( int olddirfd, const char *target, int newdirfd, const char * linkpath, int flags )
    {
        try {
            return _linkat( olddirfd, target, newdirfd, linkpath, flags );
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int link( const char *target, const char *linkpath )
    {
        try {
            return _linkat(AT_FDCWD, target, AT_FDCWD, linkpath, 0 );
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int symlinkat( const char *target, int dirfd, const char *linkpath )
    {
        try {
            instance( ).createSymLinkAt( dirfd, linkpath, target );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int symlink( const char *target, const char *linkpath )
    {
        try {
            instance( ).createSymLinkAt( AT_FDCWD, linkpath, target );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    ssize_t readlinkat( int dirfd, const char *path, char *buf, size_t count )
    {
        try {
            return instance( ).readLinkAt( dirfd, path, buf, count );
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    ssize_t readlink( const char *path, char *buf, size_t count )
    {
        try {
            return instance( ).readLinkAt( AT_FDCWD, path, buf, count );
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int faccessat( int dirfd, const char *path, int mode, int flags )
    {
        __dios::fs::Flags <__dios::fs::flags::Access> m = __dios::fs::flags::Access::OK;
        if ( mode & R_OK ) m |= __dios::fs::flags::Access::Read;
        if ( mode & W_OK ) m |= __dios::fs::flags::Access::Write;
        if ( mode & X_OK ) m |= __dios::fs::flags::Access::Execute;
        if (( mode | R_OK | W_OK | X_OK ) != ( R_OK | W_OK | X_OK ))
            m |= __dios::fs::flags::Access::Invalid;

        __dios::fs::Flags <__dios::fs::flags::At> fl = __dios::fs::flags::At::NoFlags;
        if ( flags & AT_EACCESS ) fl |= __dios::fs::flags::At::EffectiveID;
        if ( flags & AT_SYMLINK_NOFOLLOW ) fl |= __dios::fs::flags::At::SymNofollow;
        if (( flags | AT_EACCESS | AT_SYMLINK_NOFOLLOW ) != ( AT_EACCESS | AT_SYMLINK_NOFOLLOW ))
            fl |= __dios::fs::flags::At::Invalid;

        try {
            instance( ).accessAt( dirfd, path, m, fl );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int access( const char *path, int mode )
    {
        __dios::fs::Flags <__dios::fs::flags::Access> m = __dios::fs::flags::Access::OK;
        if ( mode & R_OK ) m |= __dios::fs::flags::Access::Read;
        if ( mode & W_OK ) m |= __dios::fs::flags::Access::Write;
        if ( mode & X_OK ) m |= __dios::fs::flags::Access::Execute;
        if (( mode | R_OK | W_OK | X_OK ) != ( R_OK | W_OK | X_OK ))
            m |= __dios::fs::flags::Access::Invalid;

        __dios::fs::Flags <__dios::fs::flags::At> fl = __dios::fs::flags::At::NoFlags;

        try {
            instance( ).accessAt( AT_FDCWD, path, m, fl );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int chdir( const char *path )
    {
        try {
            instance( ).changeDirectory( path );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int fchdir( int dirfd )
    {
        try {
            instance( ).changeDirectory( dirfd );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int fdatasync( int fd  )
    {
        try {
            instance( ).getFile( fd );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int fsync( int fd )
    {
        try {
            instance( ).getFile( fd );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int syncfs( int fd )
    {
        try {
            instance( ).getFile( fd );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    void sync()
    {
    }

    int stat( const char *path, struct stat *buf )
    {
        try {
            auto item = instance( ).findDirectoryItem( path );
            if ( !item )
                throw Error( ENOENT );
            return _fillStat( item, buf );
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int lstat( const char *path, struct stat *buf  )
    {
        try {
            auto item = instance( ).findDirectoryItem( path, false );
            if ( !item )
                throw Error( ENOENT );
            return _fillStat( item, buf );
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int fstat( int fd, struct stat *buf )
    {
        try {
            auto item = instance( ).getFile( fd );
            return _fillStat( item->inode( ), buf );
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int fstatfs( int, struct statfs* )
    {
        FS_PROBLEM("Fstatfs not implemented");
        return -1;
    }

    int statfs( const char *, struct statfs * )
    {
        FS_PROBLEM("statfs not implemented");
        return -1;
    }

    int fchmodat( int dirfd, const char *path, mode_t mode, int flags )
    {
        __dios::fs::Flags <__dios::fs::flags::At> fl = __dios::fs::flags::At::NoFlags;
        if ( flags & AT_SYMLINK_NOFOLLOW ) fl |= __dios::fs::flags::At::SymNofollow;
        if (( flags | AT_SYMLINK_NOFOLLOW ) != AT_SYMLINK_NOFOLLOW )
            fl |= __dios::fs::flags::At::Invalid;

        try {
            instance( ).chmodAt( dirfd, path, mode, fl );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int chmod( const char *path, mode_t mode )
    {
        __dios::fs::Flags <__dios::fs::flags::At> fl = __dios::fs::flags::At::NoFlags;

        try {
            instance( ).chmodAt( AT_FDCWD, path, mode, fl );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int fchmod( int fd, mode_t mode )
    {
        try {
            instance( ).chmod( fd, mode );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int mkdirat( int dirfd, const char *path, mode_t mode )
    {
        try {
            instance( ).createNodeAt( dirfd, path, ( ACCESSPERMS & mode ) | S_IFDIR );
            return  0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return  -1;
        }
    }

    int mkdir( const char *path, mode_t mode )
    {
        try {
            instance( ).createNodeAt( AT_FDCWD, path, ( ACCESSPERMS & mode ) | S_IFDIR );
            return  0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return  -1;
        }
    }

    int mknodat( int dirfd, const char *path, mode_t mode, dev_t dev )
    {
        try {
            return _mknodat( dirfd, path, mode, dev );
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return  -1;
        }
    }

    int mknod( const char *path, mode_t mode, dev_t dev )
    {
         try {
            if ( dev != 0 )
                throw Error( EINVAL );
            if ( !S_ISCHR( mode ) && !S_ISBLK( mode ) && !S_ISREG( mode ) && !S_ISFIFO( mode ) && !S_ISSOCK( mode ))
                throw Error( EINVAL );
            instance( ).createNodeAt( AT_FDCWD, path, mode );
            return  0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return  -1;
        }
    }

    mode_t umask( mode_t mask )
    {
        mode_t result = instance( ).umask( );
        instance( ).umask( mask & 0777 );
        return result;
    }

    int socket( int domain, int t, int protocol )
    {
        using SocketType = __dios::fs::SocketType;
        using namespace __dios::fs::flags;
        try {
            if ( domain != AF_UNIX )
                throw Error( EAFNOSUPPORT );

            SocketType type;
            switch ( t & __SOCK_TYPE_MASK ) {
                case SOCK_STREAM:
                    type = SocketType::Stream;
                    break;
                case SOCK_DGRAM:
                    type = SocketType::Datagram;
                    break;
                default:
                    throw Error( EPROTONOSUPPORT );
            }
            if ( protocol )
                throw Error( EPROTONOSUPPORT );

            return instance( ).socket( type, t & SOCK_NONBLOCK ? Open::NonBlock : Open::NoFlags );

        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int socketpair( int domain, int t, int protocol, int *fds )
    {
        using namespace conversion;
        try {

            if ( domain != AF_UNIX )
                throw Error( EAFNOSUPPORT );

            SocketType type;
            switch ( t & __SOCK_TYPE_MASK ) {
                case SOCK_STREAM:
                    type = SocketType::Stream;
                    break;
                case SOCK_DGRAM:
                    type = SocketType::Datagram;
                    break;
                default:
                    throw Error( EPROTONOSUPPORT );
            }
            if ( protocol )
                throw Error( EPROTONOSUPPORT );

            std::tie( fds[ 0 ], fds[ 1 ] ) = instance( ).socketpair( type, t & SOCK_NONBLOCK ? Open::NonBlock
                                                                                                 : Open::NoFlags );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int getsockname( int sockfd, struct sockaddr *addr, socklen_t *len )
    {
        try {
            if ( !len )
                throw Error( EFAULT );

            auto s = instance( ).getSocket( sockfd );
            struct sockaddr_un *target = reinterpret_cast< struct sockaddr_un * >( addr );

            auto &address = s->address( );

            if ( address.size( ) >= *len )
                throw Error( ENOBUFS );

            if ( target ) {
                target->sun_family = AF_UNIX;
                char *end = std::copy( address.value( ).begin( ), address.value( ).end( ), target->sun_path );
                *end = '\0';
            }
            *len = address.size( ) + 1 + sizeof( target->sun_family );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int bind( int sockfd, const struct sockaddr * addr, socklen_t )
    {
        using Address = __dios::fs::Socket::Address;

        try {

            if ( !addr )
                throw Error( EFAULT );
            if ( addr->sa_family != AF_UNIX )
                throw Error( EINVAL );

            const struct sockaddr_un *target = reinterpret_cast< const struct sockaddr_un * >( addr );
            Address address( target->sun_path );

            instance( ).bind( sockfd, std::move( address ));
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int connect( int sockfd, const struct sockaddr *addr, socklen_t )
    {
        using Address = __dios::fs::Socket::Address;

        try {

            if ( !addr )
                throw Error( EFAULT );
            if ( addr->sa_family != AF_UNIX )
                throw Error( EAFNOSUPPORT );

            const struct sockaddr_un *target = reinterpret_cast< const struct sockaddr_un * >( addr );
            Address address( target->sun_path );

            instance( ).connect( sockfd, address );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int getpeername( int sockfd, struct sockaddr *addr, socklen_t *len )
    {
        try {
            if ( !len )
                throw Error( EFAULT );

            auto s = instance( ).getSocket( sockfd );
            struct sockaddr_un *target = reinterpret_cast< struct sockaddr_un * >( addr );

            auto &address = s->peer( ).address( );

            if ( address.size( ) >= *len )
                throw Error( ENOBUFS );

            if ( target ) {
                target->sun_family = AF_UNIX;
                char *end = std::copy( address.value( ).begin( ), address.value( ).end( ), target->sun_path );
                *end = '\0';
            }
            *len = address.size( ) + 1 + sizeof( target->sun_family );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    ssize_t sendto( int sockfd, const void *buf, size_t n, int flags, const struct sockaddr * addr, socklen_t )
    {
        using Address = __dios::fs::Socket::Address;

        if ( !addr ) {
            try {
                auto s = instance( ).getSocket( sockfd );
                return s->send( static_cast< const char * >( buf ), n, conversion::message( flags ));
            } catch ( Error & e ) {
                *__dios_get_errno() = e.code();
                return -1;
            }
        }

        try {
            if ( addr->sa_family != AF_UNIX )
                throw Error( EAFNOSUPPORT );

            auto s = instance( ).getSocket( sockfd );
            const struct sockaddr_un *target = reinterpret_cast< const struct sockaddr_un * >( addr );
            Address address( target ? target->sun_path : __dios::String( ));

            return s->sendTo( static_cast< const char * >( buf ), n, conversion::message( flags ),
                              instance( ).resolveAddress( address ));
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    ssize_t _recvfrom(int sockfd, void *buf, size_t n, int flags, struct sockaddr *addr, socklen_t *len )
    {
        using Address = __dios::fs::Socket::Address;
        Address address;
        struct sockaddr_un *target = reinterpret_cast< struct sockaddr_un * >( addr );
        if ( target && !len )
            throw Error( EFAULT );

        auto s = instance( ).getSocket( sockfd );
        n = s->receive( static_cast< char * >( buf ), n, conversion::message( flags ), address );

        if ( target ) {
            target->sun_family = AF_UNIX;
            char *end = std::copy( address.value( ).begin( ), address.value( ).end( ), target->sun_path );
            *end = '\0';
            *len = address.size( ) + 1 + sizeof( target->sun_family );
        }
        return n;
    }

    ssize_t recv( int sockfd, void *buf, size_t n, int flags )
    {
        try {
             return _recvfrom( sockfd, buf, n, flags, nullptr, nullptr );
        }catch( Error & e ){
             *__dios_get_errno() = e.code();
            return -1;
        }
    }

    ssize_t recvfrom( int sockfd, void *buf, size_t n, int flags, struct sockaddr *addr, socklen_t *len )
    {
        try {
             return _recvfrom( sockfd, buf, n, flags, addr, len );
        }catch( Error & e ){
             *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int listen( int sockfd, int n )
    {
        try {
            auto s = instance( ).getSocket( sockfd );
            s->listen( n );
            return 0;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int _accept4( int sockfd, struct sockaddr *addr, socklen_t *len, int flags )
    {
        using Address = __dios::fs::Socket::Address;

        if ( addr && !len )
            throw Error( EFAULT );

        if (( flags | SOCK_NONBLOCK | SOCK_CLOEXEC ) != ( SOCK_NONBLOCK | SOCK_CLOEXEC ))
            throw Error( EINVAL );

        Address address;
        int newSocket = instance( ).accept( sockfd, address );

        if ( addr ) {
            struct sockaddr_un *target = reinterpret_cast< struct sockaddr_un * >( addr );
            target->sun_family = AF_UNIX;
            char *end = std::copy( address.value( ).begin( ), address.value( ).end( ), target->sun_path );
            *end = '\0';
            *len = address.size( ) + 1 + sizeof( target->sun_family );
        }
        if ( flags & SOCK_NONBLOCK )
            instance( ).getSocket( newSocket )->flags( ) |= __dios::fs::flags::Open::NonBlock;

        return newSocket;
    }

    int accept( int sockfd, struct sockaddr *addr, socklen_t *len )
    {
        try {
            return _accept4( sockfd, addr, len, 0 );
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int accept4( int sockfd, struct sockaddr *addr, socklen_t *len, int flags )
    {
        try {
            return _accept4( sockfd, addr, len, flags );
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int _renameitemat( int olddirfd, const char *oldpath, int newdirfd, const char *newpath )
    {
        instance( ).renameAt( newdirfd, newpath, olddirfd, oldpath );
        return 0;
    }

    int renameat( int olddirfd, const char *oldpath, int newdirfd, const char *newpath )
    {
        try {
            return _renameitemat(olddirfd, oldpath, newdirfd, newpath );
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    int rename( const char *oldpath, const char *newpath )
    {
        try {
            return _renameitemat( AT_FDCWD, oldpath, AT_FDCWD, newpath );
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return -1;
        }
    }

    //char *getcwd(char *buf, size_t size);
    char *getcwd( char *buff, size_t size ) {
        try {
            instance( ).getCurrentWorkingDir( buff, size );
            return buff;
        } catch ( Error & e ) {
            *__dios_get_errno() = e.code();
            return nullptr;
        }
    }

private:
    Manager *_manager;
};

} // namespace fs
} // namespace __dios

#endif
