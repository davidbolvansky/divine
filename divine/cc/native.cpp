// -*- mode: C++; indent-tabs-mode: nil; c-basic-offset: 4 -*-

/*
 * (c) 2019 Zuzana Baranová <xbaranov@fi.muni.cz>
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

#include <divine/cc/driver.hpp>
#include <divine/cc/codegen.hpp>
#include <divine/cc/link.hpp>
#include <divine/cc/native.hpp>
#include <divine/cc/options.hpp>
#include <iterator> // std::next

DIVINE_RELAX_WARNINGS
#include "lld/Common/Driver.h"
DIVINE_UNRELAX_WARNINGS

#include <brick-proc>

namespace divine::cc
{
    Native::Native( const std::vector< std::string >& opts )
    {
        auto driver = std::make_unique< cc::Driver >( _clang.context() );
        _po = cc::parseOpts( opts );
        _po.opts.insert( _po.opts.end(),
                         driver->commonFlags.begin(),
                         driver->commonFlags.end() );
        _clang.allowIncludePath( "/" );
    }

    // Compile all files that are neither libraries nor already object files
    int Native::compile_files()
    {
        for ( auto file : _files )
        {
            if ( file.first == "lib" )
                continue;
            if ( cc::is_object_type( file.first ) )
                continue;
            auto drv_args = _po.cc1_args;
            add( drv_args, _po.opts );
            TRACE( "compile:", file.first, drv_args );
            auto mod = _clang.compile( file.first, drv_args );
            cc::emit_obj_file( *mod, file.second, _po.pic );
        }
        return 0;
    }

    void Native::preprocess_only()
    {
        for ( auto srcFile : _po.files )
        {
            std::string ifn = srcFile.get< cc::File >().name;
            if ( cc::is_object_type( ifn ) )
                continue;
            std::cout << _clang.preprocess( ifn, _po.opts );
        }
    }

    // Initialize linker CLI arguments
    void Native::init_ld_args()
    {
        if ( _ld_args.empty() )
            _ld_args = cc::ld_args( _po, _files ); // The linker needs information about files...
        if ( _cxx )
            _ld_args.push_back( "--driver-mode=g++" ); // ... and whether it's linking C or C++...
        if ( _po.shared )
            _ld_args.push_back( "-shared" );
    }

    // Link the files (using either LLD or a native linker), then link the bitcode representation
    // of the files and insert it into the newly created object file
    void Native::link()
    {
        init_ld_args();

        auto drv = std::make_unique< cc::Driver >( _clang.context() );
        std::vector< const char * > ld_args_c;

        ld_args_c.reserve( _ld_args.size() );
        for ( size_t i = 0; i < _ld_args.size(); ++i )
            ld_args_c.push_back( _ld_args[i].c_str() );

        auto ld_job = drv->getJobs( ld_args_c ).back();
        TRACE( "link:", ld_job.args );

        if ( _po.use_lld )
        {
            ld_job.args.insert( ld_job.args.begin(), tool_name() );
            std::vector< const char * > lld_job_c;
            lld_job_c.reserve( ld_job.args.size() );
            for ( size_t i = 0; i < ld_job.args.size(); ++i )
                lld_job_c.push_back( ld_job.args[i].c_str() );

            bool linked = lld::elf::link( lld_job_c, false, llvm::outs(), llvm::errs() );
            if ( !linked )
                throw cc::CompileError( "lld failed, not linked" );
        }
        else
        {
            ld_job.args.insert( ld_job.args.begin(), ld_job.name );
            auto r = brq::spawn_and_wait( brq::capture_stderr, ld_job.args );
            if ( !r )
                throw cc::CompileError( "failed to link, ld exited with " + to_string( r ) );
        }

        _po.libSearchPath.clear();
        for ( auto it = ld_job.args.begin(); it != ld_job.args.end(); ++it )
        {
            if ( brq::starts_with( *it, "-L"  ) )
                _po.libSearchPath.push_back( it->length() > 2 ?
                                             it->substr( 2 ) : *std::next( it ) );
        }

        std::unique_ptr< llvm::Module > mod = link_bitcode();
        std::string file_out = _po.outputFile != "" ? _po.outputFile : "a.out";
	// Add the .llvmbc section with the serialized bitcode
        cc::add_section( file_out, cc::llvm_section_name, _clang.serializeModule( *mod ) );
    }

    // Run the compiler - i.e preprocces the files, compile, and link them.
    // It is also possible to stop after preprocessing or compilation
    int Native::run()
    {
        // count files, i.e. not libraries
        auto num_files = std::count_if( _po.files.begin(), _po.files.end(),
                                        []( cc::FileEntry f ){ return f.is< cc::File >(); } );

        if ( num_files == 0 )
        {
            std::vector< const char* > args = { tool_name() };
            for ( auto& s : _po.opts )
                args.push_back( s.c_str() );
            print_info( args );
            return 0;
        }

        if ( num_files > 1 && _po.outputFile != ""
             && ( _po.preprocessOnly || _po.toObjectOnly ) )
        {
            std::cerr << "Cannot specify -o with multiple files" << std::endl;
            return 1;
        }

        if ( _po.preprocessOnly )
        {
            preprocess_only();
            return 0;
        }

        construct_paired_files();

        if ( _po.toObjectOnly )
            return compile_files();
        else
        {
            compile_files();
            link();
            return 0;
        }
    }

    std::unique_ptr< llvm::Module > Native::link_bitcode()
    {
        return do_link_bitcode< cc::Driver >();
    }

    // For every file given, construct the name of its output
    void Native::construct_paired_files()
    {
        for ( auto srcFile : _po.files )
        {
            if ( srcFile.is< cc::File >() )
            {
                std::string ifn = srcFile.get< cc::File >().name;
                std::string ofn( brq::drop_extension( ifn ) );
                ofn = brq::split_filename( ofn ).second;
                if ( _po.outputFile != "" && _po.toObjectOnly )
                    ofn = _po.outputFile;
                else
                {
                    if ( !_po.toObjectOnly )
                    {
                        ofn += ".divcc.";
                        ofn += std::to_string( getpid() );
                    }
                    ofn += ".o";
                }

                // Input files that are already object files are paired as [<name>, <name>]
                if ( cc::is_object_type( ifn ) )
                    ofn = ifn;
                _files.emplace_back( ifn, ofn );
            }
            else
            {
                // Libraries are special, they are paired as ["lib", <name>]
                assert( srcFile.is< cc::Lib >() );
                _files.emplace_back( "lib", srcFile.get< cc::Lib >().name );
            }
        }
    }

    /* Passing secondary options to clang, it knows what to do with them. */
    void Native::print_info( std::string_view version )
    {
        if ( _po.hasVersion )
            std::cout << "divine version: " << version << "\n";
        std::vector< const char* > v = { tool_name(), _po.hasHelp ? "--help" : "--version" };
        print_info( v );
    }

    void Native::print_info( std::vector< const char *>& args )
    {
        cc::ClangDriver drv( tool_name() );
        delete drv.BuildCompilation( args );
    }

    // Clean up all the temporary files
    Native::~Native()
    {
        if ( !_po.toObjectOnly )
            for ( auto file : _files )
            {
                if ( cc::is_object_type( file.first ) )
                    continue;
                std::string ofn = file.second;
                unlink( ofn.c_str() );
            }
    }
}
