// -*- mode: C++; indent-tabs-mode: nil; c-basic-offset: 4 -*-

/*
 * (c) 2016 Vladimír Štill
 * (c) 2018-2019 Zuzana Baranová
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

DIVINE_RELAX_WARNINGS
#include <clang/CodeGen/CodeGenAction.h> // EmitLLVMAction
#include <clang/Frontend/FrontendActions.h>
#include <clang/Frontend/CompilerInstance.h> // CompilerInvocation
#include <clang/Frontend/DependencyOutputOptions.h>
#include <clang/Frontend/Utils.h>
#include <llvm/Bitcode/BitcodeWriter.h>
DIVINE_UNRELAX_WARNINGS

#include <brick-assert>
#include <iostream>

#include <divine/cc/cc1.hpp>
#include <lart/divine/vaarg.h>

namespace divine::str
{
    struct stringtable { std::string n; std::string_view c; };
    extern stringtable cc_list[];
}

namespace divine::cc
{
    class GetPreprocessedAction : public clang::PreprocessorFrontendAction
    {
      public:
        std::string output;
      protected:
        void ExecuteAction() override
        {
            clang::CompilerInstance &CI = getCompilerInstance();
            llvm::raw_string_ostream os( output );
            clang::DoPrintPreprocessedInput(CI.getPreprocessor(), &os,
                                CI.getPreprocessorOutputOpts());
        }

        bool hasPCHSupport() const override { return true; }
    };

    template < typename Action >
    auto buildAction( llvm::LLVMContext *ctx )
        -> decltype( std::enable_if_t< std::is_base_of< clang::CodeGenAction, Action >::value,
            std::unique_ptr< Action > >{} )
    {
        return std::make_unique< Action >( ctx );
    }

    template < typename Action >
    auto buildAction( llvm::LLVMContext * )
        -> decltype( std::enable_if_t< !std::is_base_of< clang::CodeGenAction, Action >::value,
            std::unique_ptr< Action > >{} )
    {
        return std::make_unique< Action >();
    }

    CC1::CC1( std::shared_ptr< llvm::LLVMContext > ctx ) :
        divineVFS( new VFS() ),
        overlayFS( new llvm::vfs::OverlayFileSystem( llvm::vfs::getRealFileSystem() ) ),
        ctx( ctx )
    {
        if ( !ctx )
            this->ctx = std::make_shared< llvm::LLVMContext >();
        // setup VFS
        overlayFS->pushOverlay( divineVFS );
        if ( !ctx )
            ctx.reset( new llvm::LLVMContext );

        for ( auto src = str::cc_list; !src->n.empty(); ++src )
            mapVirtualFile( brq::join_path( "/builtin/", src->n ), src->c );
    }

    CC1::~CC1() { }

    void CC1::mapVirtualFile( std::string path, std::string contents )
    {
        divineVFS->addFile( path, std::move( contents ) );
    }

    void CC1::mapVirtualFile( std::string path, std::string_view contents )
    {
        divineVFS->addFile( path, llvm::StringRef( contents.data(), contents.size() ) );
    }

    std::vector< std::string > CC1::filesMappedUnder( std::string path )
    {
        return divineVFS->filesMappedUnder( path );
    }

    void CC1::allowIncludePath( std::string path )
    {
        divineVFS->allowPath( path );
    }

    // This builds and runs a Clang CC1 invocation (bypassing the GCC-like
    // Clang driver and allowing us to fine-tune the behaviour)
    template< typename CodeGenAction >
    std::unique_ptr< CodeGenAction > CC1::cc1( std::string filename,
                                FileType type, std::vector< std::string > args,
                                llvm::IntrusiveRefCntPtr< llvm::vfs::FileSystem > vfs,
                                std::string depfile )
    {
        if ( !vfs )
            vfs = overlayFS;

        // Build an invocation
        auto invocation = std::make_shared< clang::CompilerInvocation >();
        std::vector< std::string > cc1args = { "-cc1",
                                               "-triple", "x86_64-unknown-none-elf",
                                               "-emit-obj",
                                               "-mrelax-all",
                                               // "-disable-free",
                                               // "-disable-llvm-verifier",
                                               "-mthread-model", "posix",
                                               // "-mdisable-fp-elim",
                                               "-mframe-pointer=all",
                                               "-fmath-errno",
                                               // "-masm-verbose", (on by default)
                                               "-mconstructor-aliases",
                                               "-munwind-tables",
                                               // "-fuse-init-array", (on by default)
                                               "-target-cpu", "x86-64",
                                               // "-dwarf-column-info", (on by default)
                                               "-ferror-limit", "19",
                                               "-fmessage-length=212",
                                               "-mstackrealign",
                                               "-fobjc-runtime=gcc",
                                               "-fgnuc-version=4.2.1",
                                                // "-fdiagnostics-show-option", (on by default)
                                               "-fcolor-diagnostics",
                                               "-isystem", "/builtin"
                                             };
        bool exceptions = type == FileType::Cpp || type == FileType::CppPreprocessed;
        bool reloc_model_present = false;

        for ( auto &a : args )
        {
            if ( a == "-fno-exceptions" )
                exceptions = false;
            if ( a == "-mrelocation-model" )
                reloc_model_present = true;
        }

        if ( !reloc_model_present )
            add( args, { "-mrelocation-model", "static" } );

        add( args, cc1args );
        if ( exceptions )
            add( args, { "-fcxx-exceptions", "-fexceptions" } );
        add( args, argsOfType( type ) );
        args.push_back( filename );

        std::vector< const char * > cc1a;

        for ( auto &a : args )
            if ( a != "-fno-exceptions" )
                cc1a.push_back( a.c_str() );

        TRACE( "cc1", cc1a );
        Diagnostics diag;
        bool succ = clang::CompilerInvocation::CreateFromArgs(*invocation, cc1a, diag.engine);
        if ( !succ )
            throw CompileError( "Failed to create a compiler invocation for " + filename );

        auto &depopt = invocation->getDependencyOutputOpts() = clang::DependencyOutputOptions();
        depopt.OutputFile = depfile;
        depopt.Targets.push_back( "out" );
        depopt.IncludeSystemHeaders = true;

        // actually run the compiler invocation
        clang::CompilerInstance compiler( std::make_shared< clang::PCHContainerOperations >() );
        auto fmgr = std::make_unique< clang::FileManager >( clang::FileSystemOptions(), vfs );
        compiler.setFileManager( fmgr.get() );
        compiler.setInvocation( invocation );
        ASSERT( compiler.hasInvocation() );
        compiler.createDiagnostics( &diag.printer, false );
        ASSERT( compiler.hasDiagnostics() );
        compiler.createSourceManager( *fmgr.release() );
        compiler.getPreprocessorOutputOpts().ShowCPP = 1; // Allows for printing preprocessor
        auto emit = buildAction< CodeGenAction >( ctx.get() );
        succ = compiler.ExecuteAction( *emit );
        if ( !succ )
            throw CompileError( "Error building " + filename );

        return emit;
    }

    std::string CC1::preprocess( std::string filename,
                                 FileType type, std::vector< std::string > args, std::string depfile )
    {
        auto prep = cc1< GetPreprocessedAction >( filename, type, args, nullptr, depfile );
        return prep->output;
    }

    std::unique_ptr< llvm::Module > CC1::compile( std::string filename,
                                                  FileType type, std::vector< std::string > args,
                                                  std::string depfile )
    {
        // EmitLLVMOnlyAction emits module in memory, does not write it into a file
        auto emit = cc1< clang::EmitLLVMOnlyAction >( filename, type, args, nullptr, depfile );
        auto mod = emit->takeModule();
        // We want to emit the va_arg instruction when working with ellipsis arguments instead of
        // Clang's default behaviour of emitting architecture-specific instruction sequence
        lart::divine::VaArgInstr().run( *mod );
        return mod;
    }

    // Write a module bitcode into a string
    std::string CC1::serializeModule( llvm::Module &m )
    {
        std::string str;
        {
            llvm::raw_string_ostream os( str );
            llvm::WriteBitcodeToFile( m, os );
            os.flush();
        }
        return str;
    }

    bool CC1::fileExists( llvm::StringRef file )
    {
        auto stat = overlayFS->status( file );
        return stat && stat->exists();
    }

    std::unique_ptr< llvm::MemoryBuffer > CC1::getFileBuffer( llvm::StringRef file, int64_t size )
    {
        auto buf = overlayFS->getBufferForFile( file, size );
        return buf ? std::move( buf.get() ) : nullptr;
    }

} // namespace divine
