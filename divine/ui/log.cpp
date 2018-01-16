// -*- mode: C++; indent-tabs-mode: nil; c-basic-offset: 4 -*-

/*
 * (c) 2017 Petr Ročkai <code@fixp.eu>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

#include <divine/ui/log.hpp>
#include <divine/ui/version.hpp>
#include <divine/ui/sysinfo.hpp>
#include <divine/ui/util.hpp>

namespace divine::ui
{

struct CompositeSink : LogSink
{
    std::vector< SinkPtr > _slaves;

    template< typename L >
    void each( L l )
    {
        for ( auto sink: _slaves )
            l( sink );
    }

    void progress( std::pair< int64_t, int64_t > x, int y, bool l ) override
    { each( [&]( auto s ) { s->progress( x, y, l ); } ); }

    void memory( const mc::Job::PoolStats &st, bool l ) override
    { each( [&]( auto s ) { s->memory( st, l ); } ); }

    void backtrace( DbgContext &c, int lim ) override
    { each( [&]( auto s ) { s->backtrace( c, lim ); } ); }

    void info( std::string i, bool detail ) override
    { each( [&]( auto s ) { s->info( i, detail ); } ); }

    void loader( Phase p ) override
    { each( [&]( auto s ) { s->loader( p ); } ); }

    void result( mc::Result res, const mc::Trace &tr ) override
    { each( [&]( auto s ) { s->result( res, tr ); } ); }

    void start() override
    { each( [&]( auto s ) { s->start(); } ); }
};


template< typename S >
std::string printitem( S s )
{
    std::stringstream str;
    str << "{ items: " << s.count.used << ", used: " << s.bytes.used
        << ", held: " << s.bytes.held << " }";
    return str.str();
}

void printpool( std::ostream &ostr, std::string name, const brick::mem::Stats &s )
{
    ostr << name << ":" << std::endl;
    ostr << "  total: " << printitem( s.total ) << std::endl;
    for ( auto i : s )
        if ( i.count.held )
            ostr << "  " << i.size << ": " << printitem( i ) << std::endl;
}

template< typename T >
std::string fmt_list( const std::deque< T > &v )
{
    if ( v.empty() )
        return " \"\"";
    return brick::string::fmt_container( v, "", "", " " );
}

/* format a yaml report */
struct YamlSink : TimedSink
{
    bool _detailed;
    mc::Job::PoolStats latest;
    SysInfo _sysinfo;
    std::ostream &_out;

    YamlSink( std::ostream &o, bool detailed ) : _detailed( detailed ), _out( o ) {}

    void progress( std::pair< int64_t, int64_t > stat, int q, bool last ) override
    {
        TimedSink::progress( stat, q, last );

        if ( !last )
            return;

        _out << "states per second: " << timeavg( stat.first, _time_search ) << std::endl
             << "state count: " << stat.first << std::endl;

        if ( !_detailed )
            _out << std::setprecision( 2 );

        _out << "mips: " << timeavg( stat.second / 1000000.0, _time_search ) << std::endl;

        if ( !_detailed )
            return;

        _out << std::endl << "version: " << version()
             << std::endl;
        _sysinfo.report( [this]( auto k, auto v )
                         { _out << k << ": " << v << std::endl; } );
    }

    void memory( const mc::Job::PoolStats &st, bool last ) override
    {
        if ( !last || !_detailed )
            return;
        _out << std::endl;
        for ( auto p : st )
            printpool( _out, p.first, p.second );
    }

    void result( mc::Result result, const mc::Trace &trace ) override
    {
        TimedSink::result( result, trace );
        if ( _detailed )
        {
            _out << "timers:";
            _out << std::setprecision( 3 );
            _out << std::endl << "  lart: " << double( _time_lart.count() ) / 1000
                 << std::endl << "  loader: " << double( _time_rr.count() + _time_const.count() ) / 1000
                 << std::endl << "  boot: " << double( _time_boot.count() ) / 1000
                 << std::endl << "  search: " << double( _time_search.count() ) / 1000
                 << std::endl << "  ce: " << double( _time_ce.count() ) / 1000 << std::endl;
        }

        _out << result << std::endl;
        if ( result == mc::Result::None || result == mc::Result::Valid )
            return;
        _out << "error trace: |" << std::endl;
        for ( auto l : trace.labels )
            _out << "  " << l << std::endl;
        if ( !trace.bootinfo.empty() )
            _out << "boot info:\n" << trace.bootinfo << std::endl;
        _out << std::endl;
        if ( _detailed )
        {
            _out << "machine trace:" << std::endl;
            for ( auto &s : trace.steps )
            {
                _out << "  - choices:" << fmt_list( s.choices ) << std::endl;
                _out << "    interrupts:" << fmt_list( s.interrupts ) << std::endl;
            }
            _out << std::endl;
        }
    }

    void backtrace( DbgContext &ctx, int lim ) override
    {
        std::stringstream active;
        std::ostream *str = &active;
        auto bt = [&]( int id ) { str = &_out; _out << "stack " << id << ":" << std::endl;  };
        auto fmt = [&]( auto dn )
        {
            *str << "  - symbol: " << dn.attribute( "symbol" ) << std::endl
                 << "    location: " << dn.attribute( "location" ) << std::endl;
            if ( _detailed )
                *str << "    pc: " << dn.attribute( "pc" ) << std::endl
                     << "    address: " << dn.attribute( "address" )
                     << std::endl << std::endl;
        };
        mc::backtrace( bt, fmt, ctx, ctx.snapshot(), _detailed ? 10000 : lim );
        _out << "active stack:" << std::endl;
        _out << active.str();
    }

    void info( std::string str, bool detail ) override
    {
        if ( !detail || _detailed )
            _out << str;
    }
};

/* print progress updates to stderr */
struct InteractiveSink : TimedSink
{
    virtual void progress( std::pair< int64_t, int64_t > stat, int queued, bool last ) override
    {
        TimedSink::progress( stat, queued, last );
        if ( last )
            std::cerr << "\r                                     "
                      << "                                     \r"
                      << std::flush;
        else
            std::cerr << "\rsearching: " << stat.first
                      << " states in " << interval_str( interval() )
                      << ", avg " << timeavg_str( stat.first, interval() )
                      << "/s @ " << timeavg_str( stat.second / 1000000.0, interval() )
                      << " mips, queued: " << queued << "          ";
    }

    void loader( Phase p ) override
    {
        switch ( p )
        {
            case Phase::LART:      std::cerr << "loading bitcode … LART … " << std::flush; break;
            case Phase::RR:        std::cerr << "RR … " << std::flush; break;
            case Phase::Constants: std::cerr << "constants … " << std::flush; break;
            case Phase::Done:      std::cerr << "done" << std::endl << "booting … "; break;
        }
    }

    virtual void start() override
    {
        TimedSink::start();
        std::cerr << "done" << std::endl;
    }
};

struct NullSink : LogSink {};

SinkPtr nullsink()
{
    static SinkPtr global;
    if ( !global )
        global = std::make_shared< NullSink >();
    return global;
}

SinkPtr make_yaml( std::ostream &o, bool d ) { return std::make_shared< YamlSink >( o, d ); }
SinkPtr make_interactive()
{
    if ( ::isatty( 2 ) )
        return std::make_shared< InteractiveSink >();
    return nullsink();
}

SinkPtr make_composite( std::vector< SinkPtr > s )
{
    auto rv = std::make_shared< CompositeSink >();
    rv->_slaves = s;
    return rv;
}

}
