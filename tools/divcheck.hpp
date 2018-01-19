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

#include <divine/ui/cli.hpp>
#include <divine/ui/parser.hpp>
#include <divine/cc/compile.hpp>

#include <iostream>
#include <vector>
#include <brick-string>
#include <brick-types>
#include <brick-cmd>

namespace divcheck
{

using namespace divine;

struct Unexpected : std::exception
{
    std::string _err;
    Unexpected( std::string s ) : _err( "unexpected result from: " + s ) {}
    const char *what() const noexcept { return _err.c_str(); }
};

struct Expect : ui::LogSink
{
    bool _ok, _setup = false, _armed = false;
    mc::Result _result;
    std::string _cmd;

    void check()
    {
        if ( !_armed || !_setup ) return;

        _setup = _armed = false;
        if ( !_ok )
            throw Unexpected( _cmd );
    }

    void arm( std::string cmd ) { _ok = false; _armed = true; _cmd = cmd; }
    void setup( const Expect &src ) { *this = src; _setup = true; }

    virtual void backtrace( ui::DbgContext &, int ) {}
    virtual void result( mc::Result r, const mc::Trace & )
    {
        ASSERT( _armed );
        _ok = r == _result;
    }
};

std::vector< std::string > parse( std::string txt )
{
    std::vector< std::string > script;
    brick::string::Splitter split( "\n", std::regex::extended );
    for( auto it = split.begin( txt ); it != split.end(); ++ it )
    {
        auto line = it->str();
        if ( line.empty() || line.at( 0 ) == '#' )
            continue;
        if ( line.at( 0 ) == ' ' && !script.empty() )
            script.back() += line;
        else
            script.push_back( line );
    }
    return script;
}

template< typename... F >
void execute( std::string script_txt, F... prepare )
{
    auto script = parse( script_txt );
    brick::string::Splitter split( "[ \t\n]+", std::regex::extended );

    std::shared_ptr< Expect > expect( new Expect );

    for ( auto cmdstr : script )
    {
        std::vector< std::string > tok;
        std::copy( split.begin( cmdstr ), split.end(), std::back_inserter( tok ) );
        ui::CLI cli( tok );

        auto check_expect = [=]( auto &cmd )
        {
            std::vector< ui::SinkPtr > log{ expect, cmd._log };
            cmd._log = ui::make_composite( log );
            expect->arm( cmdstr );
        };

        auto o_expect = ui::cmd::make_option_set< Expect >( cli.validator() )
            .option( "--result {result}", &Expect::_result, "verification result" );

        auto parser = cli.commands().command< Expect >( o_expect );
        auto cmd = cli.parse( parser );

        cmd.match( prepare..., [&]( ui::Command &c ) { c.setup(); } );
        cmd.match( [&]( ui::Verify &v ) { check_expect( v ); },
                   [&]( ui::Check &c )  { check_expect( c ); } );
        cmd.match( [&]( ui::Command &c ) { c.run(); },
                   [&]( Expect &e ) { expect->setup( e ); } );

        expect->check();
    }
}

}
