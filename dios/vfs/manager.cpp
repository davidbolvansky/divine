// -*- C++ -*- (c) 2015 Jiří Weiser

#include "manager.h"
#include <dios/sys/memory.hpp>

namespace __dios {
namespace fs {

Manager::Manager( bool ) :
    _root( new( __dios::nofail ) Directory() ),
    _standardIO{ { make_shared< StandardInput >(), nullptr, nullptr } }
{
    _root->mode( S_IFDIR | ACCESSPERMS );
}

void Manager::setOutputFile( FileTrace trace )
{
    switch (trace) {
        case FileTrace::UNBUFFERED:
            _standardIO[ 1 ].reset( new( __dios::nofail ) VmTraceFile() );
            break;
        case FileTrace::TRACE:
             _standardIO[ 1 ].reset( new( __dios::nofail ) VmBuffTraceFile() );
             break;
        default :
            break;
    }
}

void Manager::setErrFile(FileTrace trace) {
    switch (trace) {
        case FileTrace::UNBUFFERED:
            _standardIO[ 2 ].reset( new( __dios::nofail ) VmTraceFile() );
            break;
        case FileTrace::TRACE:
             _standardIO[ 2 ].reset( new( __dios::nofail ) VmBuffTraceFile() );
             break;
        default :
            break;
    }
}


void Manager::closeFile( int fd )
{
    __dios_assert( fd >= 0 && fd < int( _proc->_openFD.size() ) );
    _proc->_openFD[ fd ].reset();
}

int Manager::duplicate( int oldfd, int lowEdge ) {
    return _getFileDescriptor( getFile( oldfd ), lowEdge );
}

int Manager::duplicate2( int oldfd, int newfd ) {
    if ( oldfd == newfd )
        return newfd;
    auto f = getFile( oldfd );
    if ( newfd < 0 || newfd > FILE_DESCRIPTOR_LIMIT )
        throw Error( EBADF );
    if ( newfd >= int( _proc->_openFD.size() ) )
        _proc->_openFD.resize( newfd + 1 );
    _proc->_openFD[ newfd ] = f;
    return newfd;
}

std::shared_ptr< FileDescriptor > Manager::getFile( int fd )
{
    if ( fd >= 0 && fd < int( _proc->_openFD.size() ) && _proc->_openFD[ fd ] )
        return _proc->_openFD[ fd ];
    return nullptr;
}

std::shared_ptr< Socket > Manager::getSocket( int sockfd ) {
    auto f = std::dynamic_pointer_cast< Socket >( getFile( sockfd )->inode() );
    if ( !f )
        throw Error( ENOTSOCK );
    return f;
}

std::pair< int, int > Manager::pipe()
{
    Node node( new ( nofail ) Pipe() );
    node->mode( S_IRWXU | S_IFIFO );
    auto fd1 = _getFileDescriptor( node, O_RDONLY | O_NONBLOCK );
    auto fd2 =  _getFileDescriptor( node, O_WRONLY | O_NONBLOCK );
    return { fd1, fd2 };
}

off_t Manager::lseek( int fd, off_t offset, Seek whence ) {
    auto f = getFile( fd );
    if ( f->inode()->mode().is_fifo() )
        throw Error( ESPIPE );

    switch( whence ) {
    case Seek::Set:
        if ( offset < 0 )
            throw Error( EINVAL );
        f->offset( offset );
        break;
    case Seek::Current:
        if ( offset > 0 && std::numeric_limits< size_t >::max() - f->offset() < size_t( offset ) )
            throw Error( EOVERFLOW );
        if ( int( f->offset() ) < -offset )
            throw Error( EINVAL );
        f->offset( offset + f->offset() );
        break;
    case Seek::End:
        if ( offset > 0 && std::numeric_limits< size_t >::max() - f->size() < size_t( offset ) )
            throw Error( EOVERFLOW );
        if ( offset < 0 && int( f->size() ) < -offset )
            throw Error( EINVAL );
        f->offset( f->size() + offset );
        break;
    default:
        throw Error( EINVAL );
    }
    return f->offset();
}

int Manager::socket( SocketType type, OFlags fl )
{
    Socket *s = nullptr;
    switch ( type ) {
    case SocketType::Stream:
        s = new( __dios::nofail ) SocketStream;
        break;
    case SocketType::Datagram:
        s = new( __dios::nofail ) SocketDatagram;
        break;
    default:
        throw Error( EPROTONOSUPPORT );
    }

    Node socket( s );
    socket->mode( ACCESSPERMS | S_IFSOCK );

    return _getFileDescriptor( socket, fl );
}

std::pair< int, int > Manager::socketpair( SocketType type, OFlags fl )
{
    if ( type != SocketType::Stream )
        throw Error( EOPNOTSUPP );

    SocketStream *cl = new( __dios::nofail ) SocketStream;
    Node client( cl );
    client->mode( ACCESSPERMS | S_IFSOCK );

    Node server( new( __dios::nofail ) SocketStream );
    server->mode( ACCESSPERMS | S_IFSOCK );

    cl->connect( client, server );

    return {
        _getFileDescriptor( server, fl ),
        _getFileDescriptor( client, fl )
    };
}

int Manager::_getFileDescriptor( Node node, OFlags flags, int lowEdge )
{
    return _getFileDescriptor( fs::make_shared< FileDescriptor >( node, flags ), lowEdge );
}

int Manager::_getFileDescriptor( std::shared_ptr< FileDescriptor > f, int lowEdge /* = 0*/ )
{
    int i = 0;

    if ( lowEdge < 0 || lowEdge >= FILE_DESCRIPTOR_LIMIT )
        throw Error( EINVAL );

    if ( lowEdge >= int( _proc->_openFD.size() ) )
        _proc->_openFD.resize( lowEdge + 1 );

    for ( auto &fd : utils::withOffset( _proc->_openFD, lowEdge ) )
    {
        if ( !fd )
        {
            fd = f;
            return i;
        }
        ++i;
    }

    if ( _proc->_openFD.size() >= FILE_DESCRIPTOR_LIMIT )
        throw Error( ENFILE );

    _proc->_openFD.push_back( f );
    return i;
}

} // namespace fs
} // namespace __dios
