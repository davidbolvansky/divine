// -*- mode: C++; indent-tabs-mode: nil; c-basic-offset: 4 -*-

/*
 * (c) 2017 Vladimir Still <xstill@fi.muni.cz>
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

#include <tools/benchmark.hpp>

#include <divine/ui/odbc.hpp>

#include <iostream>
#include <fstream>
#include <vector>
#include <brick-string>
#include <brick-types>
#include <brick-fs>
#include <brick-cmd>
#include <brick-proc>
#include <brick-yaml>

namespace benchmark
{

namespace fs = brick::fs;
namespace proc = brick::proc;
namespace ui = divine::ui;
namespace yaml = brick::yaml;
using divine::mc::Result;

Result toResult( std::string val, bool inverted ) {
    if ( val == "yes" || val == "Yes" )
        return inverted ? Result::Error : Result::Valid;
    if ( val == "no" || val == "No" )
        return inverted ? Result::Valid : Result::Error;
    return Result::None;
}

int External::get_build( nanodbc::connection conn )
{
    auto r = proc::spawnAndWait( proc::CaptureStdout | proc::ShowCmd, _driver );
    if ( !r )
        throw brick::except::Error( "benchmark driver failed: exitcode " + std::to_string( r.exitcode() )
                                    + ", signal " + std::to_string( r.signal() ) );
    yaml::Parser yinfo( r.out() );

    odbc::ExternalBuildInfo info;
    info.driver = yinfo.getOr< std::string >( { "driver" }, "{unknown driver}" );
    info.driver_checksum = yinfo.getOr< std::string >( { "driver checksum" }, "0" );
    info.checksum = yinfo.getOr< std::string >( { "checksum" }, "0" );
    info.version = yinfo.getOr< std::string >( { "version" }, "0" );
    info.build_type = yinfo.getOr< std::string >( { "build type" }, "unknown" );

    return odbc::get_external_build( conn, info );
}

void RunExternal::execute( int job_id )
{
    fs::TempDir workdir( "_divbench_run_external.XXXXXX",
                         fs::AutoDelete::Yes,
                         fs::UseSystemTemp::Yes );
    fs::ChangeCwd cwd( workdir.path );

    for ( const auto &f : _files ) {
        fs::mkFilePath( f.first );
        std::ofstream file( f.first );
        file << f.second;
    }

    {
        std::ofstream script( "script" );
        script << _script;
    }

    log_start( job_id );

    auto log = std::dynamic_pointer_cast< ui::TimedSink >( _log );
    ASSERT( log );

    auto r = proc::spawnAndWait( proc::ShowCmd, _driver, "script" );
    if ( !r )
        throw brick::except::Error( "benchmark driver failed: exitcode " + std::to_string( r.exitcode() )
                                    + ", signal " + std::to_string( r.signal() ) );

    std::string report = fs::readFile( "report.yaml" );
    std::cerr << "REPORT: " << std::endl << report << std::endl;

    yaml::Parser yreport( report );
    for ( auto &&i : { "lart", "rr", "const", "load", "boot", "search", "ce" } ) {
        try {
            log->set_time( i, yreport.get< double >( { "timers", i } ) * 1000 );
        } catch ( std::runtime_error & ) { }
    }

    auto states = yreport.getOr< long >( { "states count" }, 0 );
    auto result = toResult( yreport.getOr< std::string >( { "error found" }, "null" ), true );
    if ( result == Result::None )
        result = toResult( yreport.getOr< std::string >( { "property holds" }, "null" ), false );
    log->set_result( result, states );

    log_done( job_id );
}

} // namespace benchmark
