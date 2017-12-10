// -*- mode: C++; indent-tabs-mode: nil; c-basic-offset: 4 -*-

/*
 * (c) 2016 Petr Ročkai <code@fixp.eu>
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

#include <divine/mc/liveness.hpp>
#include <divine/mc/safety.hpp>
#include <divine/mc/trace.hpp>
#include <divine/vm/dbg-stepper.hpp>
#include <divine/ui/cli.hpp>
#include <divine/ui/sysinfo.hpp>

namespace divine {
namespace ui {

void Verify::setup_report_file()
{
    std::random_device rd;
    std::uniform_int_distribution< char > dist( 'a', 'z' );
    std::string rand;
    int fd;

    for ( int i = 0; i < 6; ++i )
        rand += dist( rd );

    _report_filename = outputName( _file, "report." + rand );
    if ( ( fd = open( _report_filename.c_str(), O_CREAT | O_EXCL, 0666 ) ) < 0 )
        return setup_report_file();
    close( fd );
}

void Verify::setup()
{
    if ( _log == nullsink() )
    {
        std::vector< SinkPtr > log;

        if ( _interactive )
            log.push_back( make_interactive() );

        if ( _report != Report::None )
            log.push_back( make_yaml( std::cout, _report == Report::YamlLong ) );

        if ( !_no_report_file )
        {
            if ( _report_filename.empty() )
                setup_report_file();
            _report_file.reset( new std::ofstream( _report_filename ) );

            log.push_back( make_yaml( *_report_file.get(), true ) );
        }

        _log = make_composite( log );
    }

    WithBC::setup();
}

void Check::setup()
{
    _systemopts.push_back( "nofail:malloc" );
    Verify::setup();
}

void Verify::run()
{
    if ( _liveness )
        liveness();
    else
        safety();
}

void Verify::safety()
{
    vm::explore::State error;

    if ( !_threads )
        _threads = std::min( 4u, std::thread::hardware_concurrency() );

    auto safety = mc::make_safety( bitcode(), ss::passive_listen(), _symbolic );

    SysInfo sysinfo;
    sysinfo.setMemoryLimitInBytes( _max_mem );

    _log->start();

    safety->start( _threads, [&]( bool last )
                   {
                       _log->progress( safety->statecount(),
                                       safety->queuesize(), last );
                       _log->memory( safety->poolstats(), last );
                       if ( !last )
                           sysinfo.updateAndCheckTimeLimit( _max_time );
                   } );
    safety->wait();
    report_options();

    if ( safety->result() == mc::Result::Valid )
        return _log->result( safety->result(), mc::Trace() );

    vm::dbg::Context< vm::CowHeap > dbg( bitcode()->program(), bitcode()->debug() );
    vm::setup::dbg_boot( dbg );

    _log->info( "\n" ); /* makes the output prettier */

    auto trace = safety->ce_trace();

    if ( safety->result() == mc::Result::BootError )
        trace.bootinfo = dbg._info, trace.labels = dbg._trace;

    _log->result( safety->result(), trace );

    if ( safety->result() == mc::Result::Error )
    {
        safety->dbg_fill( dbg );
        dbg.load( trace.final );
        dbg._lock = trace.steps.back();
        dbg._lock_mode = decltype( dbg )::LockBoth;
        vm::setup::scheduler( dbg );
        using Stepper = vm::dbg::Stepper< decltype( dbg ) >;
        Stepper step;
        step._stop_on_error = true;
        step._ff_kernel = true;
        step.run( dbg, Stepper::Quiet );
        _log->backtrace( dbg, _num_callers );
    }

    if ( !_report_filename.empty() )
        std::cerr << "a report was written to " << _report_filename << std::endl;
}

void Verify::liveness()
{
    auto liveness = mc::make_liveness( bitcode(), ss::passive_listen(), _symbolic );

    liveness->start( 1 ); // threadcount
    liveness->wait();
    _log->result( liveness->result(), mc::Trace() );
}

}
}
