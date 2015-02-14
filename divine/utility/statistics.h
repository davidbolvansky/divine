// -*- C++ -*- (c) 2010 Petr Rockai <me@mornfall.net>

#ifndef DIVINE_STATISTICS_H
#define DIVINE_STATISTICS_H

#include <memory>

#include <brick-shmem.h>
#include <divine/toolkit/mpi.h>
#include <divine/toolkit/pool.h>

#include <divine/utility/meta.h>
#include <divine/utility/sysinfo.h>
#include <divine/utility/output.h>

#define TAG_STATISTICS 128

namespace divine {

struct NoStatistics {
    void enqueue( int , int64_t ) {}
    void dequeue( int , int64_t ) {}
    void hashsize( int , int64_t ) {}
    void hashadded( int , int64_t ) {}
    void sent( int, int, int64_t ) {}
    void received( int, int, int64_t ) {}
    void idle( int ) {}
    void busy( int ) {}

    std::shared_ptr< std::ostream > output;

    static NoStatistics _global;
    static NoStatistics &global() {
        return _global;
    }

    template< typename D >
    void useDomain( D & ) {}
    void start() {}
};

#ifndef __divine__

struct TrackStatistics : brick::shmem::Thread, MpiMonitor {
    struct PerThread {
        std::vector< int64_t > sent;
        std::vector< int64_t > received;
        int64_t enq, deq;
        int64_t hashsize;
        int64_t hashused;
        int64_t memQueue;
        int64_t memHashes;
        int64_t idle;
        int64_t cputime;
        std::vector< int64_t > memSent;
        std::vector< int64_t > memReceived;
    };

    struct Baseline {
        int64_t vm;
        int64_t rss;
    };

    std::vector< PerThread * > threads;
    divine::Mpi mpi;
    int pernode, localmin;

    const Baseline baseline;

    bool shared;
    std::shared_ptr< std::ostream > output;

    Output::Token out_token;

    void enqueue( int id , int64_t size ) {
        thread( id ).enq ++;
        thread( id ).memQueue += size;
    }

    void dequeue( int id , int64_t size ) {
        thread( id ).deq ++;
        thread( id ).memQueue -= size;
    }

    void hashsize( int id , int64_t s ) {
        thread( id ).hashsize = s;
    }

    void hashadded( int id , int64_t nodeSize ) {
        thread( id ).hashused ++;
        thread( id ).memHashes += nodeSize;
    }

    void idle( int id  ) {
        ++ thread( id ).idle;
    }

    void busy( int id );

    PerThread &thread( int id ) {
        ASSERT_LEQ( size_t( id ), threads.size() );
        if ( !threads[ id ] )
            threads[ id ] = new PerThread;
        return *threads[ id ];
    }

    void sent( int from, int to, int64_t nodeSize ) {
        ASSERT_LEQ( 0, to );

        PerThread &f = thread( from );
        if ( f.sent.size() <= size_t( to ) )
            f.sent.resize( to + 1, 0 );
        ++ f.sent[ to ];
        f.memSent[ to ] += nodeSize;
    }

    void received( int from, int to, int64_t nodeSize ) {
        ASSERT_LEQ( 0, from );

        PerThread &t = thread( to );
        if ( t.received.size() <= size_t( from ) )
            t.received.resize( from + 1, 0 );
        ++ t.received[ from ];
        t.memReceived[ from ] += nodeSize;
    }

    static int64_t first( int64_t a, int64_t ) { return a; }
    static int64_t second( int64_t, int64_t b ) { return b; }
    static int64_t diff( int64_t a, int64_t b ) { return a - b; }

    int64_t vmPeak() { return sysinfo::Info().peakVmSize() - baseline.vm; }
    int64_t vmNow() { return sysinfo::Info().peakVmSize() - baseline.vm; }

    int64_t residentMemPeak() { return sysinfo::Info().peakResidentMemSize() - baseline.rss; }
    int64_t residentMemNow() { return sysinfo::Info().residentMemSize() - baseline.rss; }

    void resize( int s );

    virtual void format( std::ostream & ) { }
    virtual void startHeader( std::ostream & ) { } // to be printed before first format()
    void snapshot();
    void main();

    void send();
    Loop process( std::unique_lock< std::mutex > &, MpiStatus &status );

    void setup( const Meta &m );

    static Baseline getBaseline() {
        sysinfo::Info i;
        Baseline b;
        b.vm = i.peakVmSize();
        b.rss = i.peakResidentMemSize();
        return b;
    }

    TrackStatistics( Baseline b ) :
        pernode( 1 ), localmin( 0 ), baseline( b ), shared( false ),
        output( nullptr ), out_token( Output::hold() ), meta( nullptr )
    {
        resize( 1 );
    }

    virtual ~TrackStatistics();

    static void makeGlobalGnuplot( Baseline, std::string file );
    static void makeGlobalDetailed( Baseline );
    static void makeGlobalSimple( Baseline, std::vector< std::string > selectors );

    static TrackStatistics &global() {
        if ( !_global() )
            _global().reset( new TrackStatistics( Baseline() ) );
        return *_global();
    }

    static void killGlobal() {
        _global()->stop();
        _global().reset();
    }

  protected:
    const Meta *meta;

  private:
    static std::unique_ptr< TrackStatistics > &_global() {
        static std::unique_ptr< TrackStatistics > g;
        return g;
    }
};
#endif // !__divine__

template <typename Ty>
int64_t memSize( Ty x, Pool& ) {
    return sizeof(x);
}

template <>
inline int64_t memSize<Blob>(Blob x, Pool& pool) {
    return sizeof( Blob ) + ( pool.valid( x ) ? align( pool.size( x ), sizeof( void * ) ) : 0 );
}


}

#endif
