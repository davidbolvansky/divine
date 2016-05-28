#pragma once

#include <divine/vm/bitcode.hpp>
#include <divine/vm/run.hpp>
#include <divine/cc/compile.hpp>

#include <divine/ui/common.hpp>
#include <divine/ui/curses.hpp>
#include <divine/ui/die.hpp>
#include <brick-cmd>
#include <brick-fs>
#include <brick-llvm>

namespace divine {
namespace ui {

using namespace std::literals;
namespace cmd = brick::cmd;

struct Command
{
    virtual void run() = 0;
    virtual void setup() {}
};

struct WithBC : Command
{
    std::string _file;
    std::vector< std::string > _env;

    std::shared_ptr< vm::BitCode > _bc;
    void setup()
    {
        _bc = std::make_shared< vm::BitCode >( _file );
    }
};

struct Help
{
    std::string _cmd = std::string("");

    template< typename P >
    void run( P cmds )
    {
        std::string description = cmd::get_desc_by_name( cmds, _cmd );
        if ( description.compare( "" ) == 0)
        {
            if ( _cmd.compare("") != 0 )
            {
                std::cerr << "Command '" << _cmd << "' not recognized.\n\n";
                _cmd = std::string( "" );
            }
        }
        else
            std::cerr << description << std::endl;
        if ( _cmd.compare( "" ) == 0 )
        {
            std::cerr << "To print details about specific command write 'divine help [command]'.\n\n";
            std::cerr << cmd::describe( cmds ) << std::endl;
        }
    }
};

struct Verify : WithBC
{
    int _max_mem = 256; // MB
    int _max_time = 100;  // seconds
    int _jobs = 1;
    bool _no_counterexample = false;
    std::string _report;
    std::string _statistics;

    void print_args()
    {
        std::cerr << "Verify model " << _file << " with given options:" << std::endl;
        std::cerr << "Max. memory allowed [MB]: " << _max_mem << std::endl;
        std::cerr << "Max. time allowed [sec]: " << _max_time << std::endl;
        std::cerr << "Number of jobs: " << _jobs << std::endl;
        if ( _no_counterexample )
            std::cerr << "Do not print counter example." << std::endl;
        else
            std::cerr << "If program fails, print counter example." << std::endl;
        std::cerr << "Give report in format: " << _report << std::endl;
        std::cerr << "Give statistics in format: " << _statistics << std::endl;
    }

    void run()
    {
        print_args();
    }
};

struct Run : WithBC
{
    void run() { vm::Run( _bc, _env ).run(); }
};

struct Draw   : WithBC
{
    int _number = 0;
    int _distance = 0;
    enum { All, None, Trace } _labels = None;
    bool _bfs = false;
    std::string _render = std::string( "dot -Tx11" );

    void print_args()
    {
        std::cerr << "(" << _number << ") Draw model " << _file << " with given options:" << std::endl;
        if ( _labels == All )
            std::cerr << "Draw all node labels." << std::endl;
        if ( _labels == None )
            std::cerr << "Do not draw any labels." << std::endl;
        if ( _labels == Trace )
            std::cerr << "Draw only trace labels." << std::endl;
        std::cerr << "Node distance [cm]: " <<  _distance << std::endl;
        if ( _bfs )
            std::cerr << "Draw as BFS." << std::endl;
        std::cerr << "Render with " << _render << std::endl;
    }

    void run()
    {
        print_args();
    }
};

struct Cc     : Command
{
    cc::Compile::Opts _drv;
    std::vector< std::string > _files, _flags;
    std::string _precompiled;
    std::string _output;

    void print_args()
    {
        std::cerr << "Files to compile: " << brick::string::fmt( _files ) << std::endl;
        std::cerr << "Number of jobs: " << _drv.num_threads << std::endl;
        std::cerr << "Precompiled: " << _drv.precompiled << std::endl;

        std::cerr << "Flags:";
        for ( std::string flag : _flags )
            std::cerr << " " << flag;
        std::cerr << std::endl;

        if (_drv.libs_only)
            std::cerr << "Libraries only." << std::endl;
        if (_drv.dont_link)
            std::cerr << "Do not link" << std::endl;
    }

    void run()
    {
        print_args();

        if ( !_drv.libs_only && _files.empty() )
            die( "Either a file to build or --libraries-only is required." );
        if ( _drv.libs_only && !_files.empty() )
            die( "Cannot specify both --libraries-only and files to compile." );

        if ( _output.empty() ) {
            if ( _drv.libs_only )
                _output = "libdivinert.bc";
            else {
                _output = _files.front();
                auto pos = _output.rend() - std::find( _output.rbegin(), _output.rend(), '.' );
                _output = _output.substr( 0, pos - 1 ) + ".bc";
            }
        }

        cc::Compile driver( _drv );

        for ( auto &x : _flags )
            x = "-"s + x; /* put back the leading - */

        for ( auto &x : _files )
            driver.compileAndLink( x, _flags );

        if ( !_drv.dont_link && !_drv.libs_only )
            driver.prune( { "__sys_init", "main", "memmove", "memset",
                            "memcpy", "llvm.global_ctors", "__lart_weakmem_buffer_size",
                            "__md_get_function_meta", "__sys_env" } );

        driver.writeToFile( _output );
    }
};

struct Info   : WithBC
{
    void run() { NOT_IMPLEMENTED(); }
};

std::vector< std::string > fromArgv( int argc, const char **argv ) {
    std::vector< std::string > args;
    std::copy( argv + 1, argv + argc, std::back_inserter( args ) );
    return args;
}

struct CLI : Interface
{
    bool _batch;
    std::vector< std::string > _args;

    CLI( int argc, const char **argv ) :
        _batch( true ), _args( fromArgv( argc, argv ) )
    { }

    CLI( std::vector< std::string > args ) :
        _batch( true ), _args( args )
    { }

    auto validator()
    {
        return cmd::make_validator()->
            add( "file", []( std::string s, auto good, auto bad )
                 {
                     if ( s[0] == '-' ) /* FIXME! zisit, kde sa to rozbije */
                         return bad( cmd::BadFormat, "file must not start with -" );
                     if ( !brick::fs::access( s, F_OK ) )
                         return bad( cmd::BadContent, "file " + s + " does not exist");
                     if ( !brick::fs::access( s, R_OK ) )
                         return bad( cmd::BadContent, "file " + s + " is not readable");
                     return good( s );
                 } ) ->
            add( "label", []( std::string s, auto good, auto bad )
                {
                    if ( s.compare("none") == 0 )
                        return good( Draw::None );
                    if ( s.compare("all") == 0 )
                        return good( Draw::All );
                    if ( s.compare("trace") == 0 )
                        return good( Draw::Trace );
                    return bad( cmd::BadContent, s + " is not a valid label type" );
                });
    }

    // @return ParserT
    auto commands()
    {
        auto v = validator();

        auto helpopts = cmd::make_option_set< Help >( v )
                .add( "[{string}]", &Help::_cmd, "print man to specified command"s );

        auto bcopts = cmd::make_option_set< WithBC >( v )
                .add( "[-D {string}|-D{string}]", &WithBC::_env, "add to the environment"s )
                .add( "{file}", &WithBC::_file, "the bitcode file to load"s, true );

        using DrvOpt = cc::Compile::Opts;
        auto ccdrvopts = cmd::make_option_set< DrvOpt >( v )
            .add( "[--precompiled {file}]", &DrvOpt::precompiled, "path to a prebuilt libdivinert.bc"s )
            .add( "[-j {int}]", &DrvOpt::num_threads, "number of jobs"s )
            .add( "[--dont-link]", &DrvOpt::dont_link, "do not link"s )
            .add( "[--libraries-only]", &DrvOpt::libs_only, "build libdivinert.bc for later use"s );

        auto ccopts = cmd::make_option_set< Cc >( v )
            .add( ccdrvopts, &Cc::_drv )
            .add( "[-o {string}]", &Cc::_output, "the name of the output file"s )
            .add( "[-{string}]", &Cc::_flags, "any cc1 options"s )
            .add( "[{file}]", &Cc::_files, "input file(s) to compile (C or C++)"s );

        auto vrfyopts = cmd::make_option_set< Verify >( v )
                .add( "[--max-memory {int}]", &Verify::_max_mem, "max memory allowed to use [in MB]"s )
                .add( "[--max-time {int}]", &Verify::_max_time, "max time allowed to take [in sec]"s )
                .add( "[--no-counterexample]", &Verify::_no_counterexample,
                        "do not print counterexamples"s )
                .add( "[--report {string}]", &Verify::_report, "print a report with given options"s )
                .add( "[--statistics {string}]", &Verify::_statistics,
                      "print statistics with given options"s );

        auto drawopts = cmd::make_option_set< Draw >( v )
                .add( "[--distance {int}|-d {int}]", &Draw::_distance, "node distance"s )
                .add( "[--labels {label}]", &Draw::_labels, "label all, none or only trace"s )
                .add( "[--bfs-layout]", &Draw::_bfs, "draw in bfs layout (levels)"s );

        auto parser = cmd::make_parser( v )
                .add< Verify >( vrfyopts, bcopts )
                .add< Run >( bcopts )
                .add< Draw >( drawopts, bcopts )
                .add< Info >( bcopts )
                .add< Cc >( ccopts )
                .add< Help >( helpopts );
        return parser;
    }

    template< typename P >
    auto parse( P p )
    {
        return p.parse( _args.begin(), _args.end() );
    }

    std::shared_ptr< Interface > resolve() override
    {
        if ( _batch )
            return Interface::resolve();
        else
            return std::make_shared< ui::Curses >( /* ... */ );
    }

    virtual int main() override
    {
        try {
            auto cmds = commands();
            auto cmd = parse( cmds );

            if ( cmd.empty()  )
            {
                Help help;
                help.run( cmds );
                return 0;
            }

            cmd.match( [&]( Help &help )
                       {
                           help.run( cmds );
                       },
                       [&]( Command &c )
                       {
                           c.setup();
                           c.run();
                       } );
            return 0;
        }
        catch ( brick::except::Error &e )
        {
            std::cerr << "ERROR: " << e.what() << std::endl;
            exception( e );
            return e._exit;
        }
    }
};

}
}
