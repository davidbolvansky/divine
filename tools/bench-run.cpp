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

#include <tools/benchmark.hpp>

#include <divine/ui/sysinfo.hpp>
#include <divine/ui/log.hpp>
#include <divine/ui/odbc.hpp>
#include <tools/divcheck.hpp>

#include <iostream>
#include <vector>
#include <brick-string>
#include <brick-types>
#include <brick-cmd>

namespace benchmark
{

void Run::prepare( int model )
{
    _files.clear();

    std::cerr << "loading model " << model << std::endl;
    std::stringstream q;
    q << "select filename, text from model "
      << "left join model_srcs on model_srcs.model  = model.id "
      << "left join source     on model_srcs.source = source.id "
      << " where model.id = ?";

    auto sel = nanodbc::statement( _conn, q.str() );
    sel.bind( 0, &model );
    auto file = sel.execute();

    while ( file.next() )
        _files.emplace_back( file.get< std::string >( 0 ),
                             file.get< std::string >( 1 ) );

    auto scr_q = "select text from model join source on model.script = source.id where model.id = ?";
    auto scr = nanodbc::statement( _conn, scr_q );

    scr.bind( 0, &model );
    auto script = scr.execute();
    script.first();
    _script = script.get< std::string >( 0 );
    _log = ui::make_odbc( *this, _odbc );
}

void Run::execute( int job_id )
{
    _done = false;

    auto prepare = [&]( auto &cmd )
    {
        if ( _done )
            throw brick::except::Error( "only one model checker run is allowed per model" );
        _done = true;
        cmd._interactive = false;
        cmd._report = ui::Report::None;
        cmd._log = _log;
        cmd.setup();
    };

    log_start( job_id );
    divcheck::execute( _script,
                       [&]( ui::Cc &cc ) { cc._files = _files; },
                       [&]( ui::Verify &v ) { prepare( v ); },
                       [&]( ui::Check &c ) { prepare( c ); } );
    log_done( job_id );
}

void Run::log_start( int job_id )
{
    int exec_id = _log->log_id();

    nanodbc::statement exec( _conn, "update job set execution = ? where id = ?" );
    exec.bind( 0, &exec_id );
    exec.bind( 1, &job_id );
    exec.execute();
}

void Run::log_done( int job_id )
{
    nanodbc::statement done( _conn, "update job set status = 'D' where id = ?" );
    done.bind( 0, &job_id );
    done.execute();
}

int Run::get_instance() {
    return odbc::get_instance( *this, _conn );
}

void Run::run()
{
    std::stringstream q;
    int inst = get_instance();
    std::cerr << "instance = " << inst << std::endl;
    q << "select job.id, job.model from job";
    if ( !_tag.empty() )
        q << " join model on job.model = model.id"
          << " join model_tags on model_tags.model = model.id"
          << " join tag on model_tags.tag = tag.id";
    q << " where job.instance = ?";
    if ( !_tag.empty() )
        q << " and tag.name = ?";
    auto sel = nanodbc::statement( _conn, q.str() );
    sel.bind( 0, &inst );
    if ( !_tag.empty() )
        sel.bind( 1, _tag.c_str() );
    auto job = nanodbc::execute( sel );

    while ( job.next() )
    {
        int job_id = job.get< int >( 0 );
        /* claim the job */
        nanodbc::statement claim( _conn, "update job set status = 'R'"
                                         " where id = ? and status = 'P'" );
        claim.bind( 0, &job_id );
        auto res = claim.execute();
        if ( !res || res.affected_rows() != 1 )
            continue; /* somebody beat us to this one */

        try {
            prepare( job.get< int >( 1 ) );
            execute( job_id );
        } catch ( std::exception &e )
        {
            std::cerr << "W: job " << job_id << " failed: " << e.what() << std::endl;
            nanodbc::statement fail( _conn, "update job set status = 'F' where id = ?" );
            fail.bind( 0, &job_id );
            fail.execute();
        }
        if ( _single )
            break;
    }
}

}
