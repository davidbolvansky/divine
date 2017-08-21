// -*- mode: C++; indent-tabs-mode: nil; c-basic-offset: 4 -*-

/*
 * (c) 2016 Petr Ročkai <code@fixp.eu>
 * (c) 2016 Viktória Vozárová <>
 * (c) 2016 Vladimír Štill <xstill@fi.muni.cz>
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

#pragma once

#include <divine/vm/bitcode.hpp>
#include <divine/cc/options.hpp>

#include <divine/ui/common.hpp>
#include <divine/ui/curses.hpp>
#include <divine/ui/die.hpp>
#include <divine/ui/version.hpp>
#include <divine/ui/log.hpp>

#include <brick-cmd>
#include <brick-fs>
#include <brick-string>
#include <cctype>
#include <regex>

#include <divine/vm/divm.h>

namespace divine {
namespace ui {

using namespace std::literals;
namespace cmd = brick::cmd;

struct Command
{
    virtual void run() = 0;
    virtual void setup() {}
    virtual ~Command() {}
};

struct WithBC : Command
{
    struct VfsDir {
        std::string capture;
        std::string mount;
        bool followSymlink;
    };

    std::string _file, _std, _stdin;
    std::vector< std::string > _env;
    std::vector< std::string > _useropts;
    std::vector< std::string > _systemopts;
    std::vector< std::string > _lartPasses;
    std::vector< std::string > _linkLibs;
    std::vector< std::vector< std::string > > _ccOpts;
    std::vector< VfsDir > _vfs;
    size_t _vfsSizeLimit;
    vm::AutoTraceFlags _autotrace;
    bool _disableStaticReduction = false;
    bool _symbolic = false, _sequential = false;
    std::string _solver;
    bool _init_done = false;
    SinkPtr _log = nullsink();
    std::string _relaxed;

    vm::BitCode::Env _bc_env;
    std::vector< std::string > _ccopts_final;

    virtual void process_options();
    void report_options();
    void setup();
    void init();

    std::shared_ptr< vm::BitCode > bitcode()
    {
        if ( !_init_done )
            init();
        _init_done = true;
        return _bc;
    }

    WithBC() : _vfsSizeLimit( 16 * 1024 * 1024 ) {}

private:
    std::shared_ptr< vm::BitCode > _bc;
};

struct Help
{
    std::string _cmd = std::string("");

    template< typename P >
    void run( P cmds )
    {
        std::string description = cmds.describe( _cmd );
        if ( description.empty() && !_cmd.empty() )
            die( "Unknown command '" + _cmd + "'. Available commands are:\n" + cmds.describe() );
        if ( _cmd.empty() )
        {
            std::cerr << "To print details about a specific command, run 'divine help {command}'.\n\n";
            std::cerr << cmds.describe() << std::endl;
        }
        else std::cerr << description << std::endl;
    }
};

struct Version : Command {

    void run() override;
};

enum class Report { None, Yaml, YamlLong };

struct Verify : WithBC
{
    int64_t _max_mem = 0; // bytes
    int _max_time = 0;  // seconds
    int _threads = 0;
    int _num_callers = 10;
    bool _no_counterexample = false;
    bool _interactive = true;
    bool _liveness = false;
    bool _no_report_file = false;
    Report _report = Report::Yaml;

    std::shared_ptr< std::ostream > _report_file;
    std::string _report_filename;
    void setup_report_file();

    void setup() override;
    void run() override;
    void safety();
    void liveness();
};

struct Check : Verify
{
    void setup() override;
};

struct Run : WithBC {
    bool _trace = false;

    void run();
    void trace();
};

namespace sim { struct Trace; }

struct Sim : WithBC
{
    bool _batch = false, _skip_init = false, _load_report = false;
    std::shared_ptr< sim::Trace > _trace;

    void process_options() override;
    void run() override;
};

struct Draw : WithBC
{
    int _number = 0;
    int _distance = 32;
    enum { All, None, Trace } _labels = None;
    bool _bfs = false, _raw = false;
    std::string _render = "dot -Tx11"s;
    std::string _output = "-"s;

    void run();
};

struct Cc : Command
{
    cc::Options _drv;
    std::vector< std::string > _flags;
    std::vector< std::vector< std::string > > _passThroughFlags;
    std::string _output;
    std::vector< std::pair< std::string, std::string > > _files;

    void run();
};

struct DivineCc : Command
{
    void run() override;

    std::string _output;
    bool _dontLink = false, _splitCompilation = false;
    std::vector< std::string > _flags;
    std::vector< std::string > _libPaths;
};

struct DivineLd : Command
{
    void run() override;

    std::string _output;
    bool _incremental = false, _merge = false;
    std::vector< std::string > _flags;
};

struct Info   : Run
{
    Info() {
        _systemopts.push_back( "help" );
    }

    void run() override;
};

namespace {

size_t memFromString( std::string s )
{
    size_t pos;
    size_t base = stoull( s, &pos );
    std::string r = s.substr( pos );
    if ( r.empty() )
        return base;
    std::string rem;
    std::transform( r.begin(), r.end(), std::back_inserter( rem ), ::tolower );
    if ( rem == "k" || rem == "kb" )
        base *= 1000;
    else if ( rem == "ki" || rem == "kib" )
        base *= 1024;
    else if ( rem == "m" || rem == "mb" )
        base *= 1000'000;
    else if ( rem == "mi" || rem == "mib" )
        base *= 1024 * 1024;
    else if ( rem == "g" || rem == "gb" )
        base *= 1'000'000'000;
    else if ( rem == "gi" || rem == "gib" )
        base *= 1024 * 1024 * 1024;
    else
        throw std::invalid_argument( "unknown suffix " + r );
    return base;
}

std::string outputName( std::string path, std::string ext )
{
    return brick::fs::replaceExtension( brick::fs::basename( path ), ext );
}

}

std::shared_ptr< Interface > make_cli( std::vector< std::string > args );

}
}
