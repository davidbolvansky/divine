// -*- C++ -*- (c) 2016 Vladimír Štill
#pragma once

DIVINE_RELAX_WARNINGS
#include <llvm/Support/Signals.h>
#include <clang/Tooling/Tooling.h> // ClangTool
#include <clang/CodeGen/CodeGenAction.h> // EmitLLVMAction
#include <clang/Basic/DiagnosticOptions.h>
#include <clang/Frontend/TextDiagnosticPrinter.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/LLVMContext.h>
#include <clang/Driver/Driver.h>
#include <clang/Driver/Compilation.h>
#include <clang/Frontend/CompilerInstance.h> // CompilerInvocation
#include <clang/Frontend/DependencyOutputOptions.h>
#include <llvm/Support/Errc.h> // for VFS
#include <llvm/Bitcode/ReaderWriter.h>
DIVINE_UNRELAX_WARNINGS

#include <brick-fs>
#include <brick-assert>
#include <brick-query>
#include <brick-except>

#include <iostream>

namespace divine {
namespace cc {

template< typename Contailer >
void dump( const Contailer &c ) {
    std::copy( c.begin(), c.end(),
               std::ostream_iterator< std::decay_t< decltype( *c.begin() ) > >( std::cerr, " " ) );
}

template< typename Contailer >
void dump( const Contailer *c ) {
    std::cerr << static_cast< const void * >( c ) << "= @( ";
    dump( *c );
    std::cerr << ")" << std::endl;
}

enum class DivineVFSError {
    InvalidIncludePath = 1000 // avoid clash with LLVM's error codes, they don't check category
};

struct DivineVFSErrorCategory : std::error_category {
    const char *name() const noexcept override { return "DIVINE VFS error"; }
    std::string message( int condition ) const override {
        switch ( DivineVFSError( condition ) ) {
            case DivineVFSError::InvalidIncludePath:
                return "Invalid include path, not accessible in DIVINE";
        }
    }
};

static std::error_code make_error_code( DivineVFSError derr ) {
    return std::error_code( int( derr ), DivineVFSErrorCategory() );
}

}
}

namespace std {
    template<>
    struct is_error_code_enum< divine::cc::DivineVFSError > : std::true_type { };
}

namespace divine {
namespace cc {

struct CompileError : brick::except::Error
{
    using brick::except::Error::Error;
};

struct DivineVFS : clang::vfs::FileSystem {
  private:
    // just a wrapper over const char *
    struct CharMemBuf : llvm::MemoryBuffer {
        BufferKind getBufferKind() const override { return BufferKind( 2 ); } // meh
        CharMemBuf( const char *data ) {
            init( data, data + std::strlen( data ), false );
        }
    };

    // adapt file map to the expectations of LLVM's VFS
    struct File : clang::vfs::File {
        File( const char *content, clang::vfs::Status stat ) :
            content( content ), stat( stat )
        { }

        llvm::ErrorOr< clang::vfs::Status > status() override { return stat; }

        auto getBuffer( const llvm::Twine &/* path */, int64_t /* fileSize */ = -1,
                        bool /* requiresNullTerminator */ = true,
                        bool /* IsVolatile */ = false ) ->
            llvm::ErrorOr< std::unique_ptr< llvm::MemoryBuffer > > override
        {
            return { std::make_unique< CharMemBuf >( content ) };
        }

        void setName( llvm::StringRef ) override { }

        std::error_code close() override { return std::error_code(); }

      private:
        const char *content;
        clang::vfs::Status stat;
    };

    static auto doesNotExits() { // forward to real FS
        return std::error_code( llvm::errc::no_such_file_or_directory );
    }
    static auto blockAccess( const llvm::Twine & ) {
        return std::error_code( DivineVFSError::InvalidIncludePath );
    };

    clang::vfs::Status statpath( const std::string &path, clang::vfs::Status stat ) {
        stat.setName( path );
        return stat;
    }

  public:

    auto status( const llvm::Twine &_path ) ->
        llvm::ErrorOr< clang::vfs::Status > override
    {
        auto path = brick::fs::normalize( _path.str() );
        auto it = filemap.find( path );
        if ( it != filemap.end() )
            return statpath( path, it->second.second );
        else if ( allowed( path ) )
            return { doesNotExits() };
        return { blockAccess( path ) };
    }

    auto openFileForRead( const llvm::Twine &_path ) ->
        llvm::ErrorOr< std::unique_ptr< clang::vfs::File > > override
    {
        auto path = brick::fs::normalize( _path.str() );

        auto it = filemap.find( path );
        if ( it != filemap.end() )
            return mkfile( it, statpath( path, it->second.second ) );
        else if ( allowed( path ) )
            return { doesNotExits() };
        return { blockAccess( path ) };
    }

    auto dir_begin( const llvm::Twine &_path, std::error_code & ) ->
        clang::vfs::directory_iterator override
    {
        auto path = brick::fs::normalize( _path.str() );
        std::cerr << "DVFS:dir_begin " << path << std::endl;
        NOT_IMPLEMENTED();
    }

    void allowPath( std::string path ) {
        path = brick::fs::normalize( path );
        allowedPrefixes.insert( path );
        auto parts = brick::fs::splitPath( path );
        addDir( parts.begin(), parts.end() );
    }

    void addFile( std::string name, std::string contents, bool allowOverride = false ) {
        storage.emplace_back( std::move( contents ) );
        addFile( name, storage.back().c_str(), allowOverride );
    }

    void addFile( std::string path, const char *contents, bool allowOverride = false ) {
        ASSERT( allowOverride || !filemap.count( path ) );
        auto &ref = filemap[ path ];
        ref.first = contents;
        auto name = llvm::sys::path::filename( path );
        ref.second = clang::vfs::Status( name, name,
                        clang::vfs::getNextVirtualUniqueID(),
                        llvm::sys::TimeValue(), 0, 0, std::strlen( contents ),
                        llvm::sys::fs::file_type::regular_file,
                        llvm::sys::fs::perms::all_all );
        auto parts = brick::fs::splitPath( path );
        if ( !parts.empty() )
            addDir( parts.begin(), parts.end() - 1 );
    }

    template< typename It >
    void addDir( It begin, It end ) {
        for ( auto it = begin; it < end; ++it ) {
            auto path = brick::fs::joinPath( begin, std::next( it ) );
            filemap[ path ] = { "", clang::vfs::Status( *it, *it,
                    clang::vfs::getNextVirtualUniqueID(),
                    llvm::sys::TimeValue(), 0, 0, 0,
                    llvm::sys::fs::file_type::directory_file,
                    llvm::sys::fs::perms::all_all ) };
        }
    }

    std::vector< std::string > filesMappedUnder( std::string path ) {
        auto prefix = brick::fs::splitPath( path );
        return brick::query::query( filemap )
            .filter( []( auto &pair ) { return !pair.second.second.isDirectory(); } )
            .map( []( auto &pair ) { return pair.first; } )
            .filter( [&]( auto p ) {
                    auto split = brick::fs::splitPath( p );
                    return split.size() >= prefix.size()
                           && std::equal( prefix.begin(), prefix.end(), split.begin() );
                } )
            .freeze();
    }

  private:

    bool allowed( std::string path ) {
        if ( path.empty() || brick::fs::isRelative( path ) )
            return true; // relative or .

        auto parts = brick::fs::splitPath( path );
        for ( auto it = std::next( parts.begin() ); it < parts.end(); ++it )
            if ( allowedPrefixes.count( brick::fs::joinPath( parts.begin(), it ) ) )
                return true;
        return false;
    }

    template< typename It >
    std::unique_ptr< clang::vfs::File > mkfile( It it, clang::vfs::Status stat ) {
        return std::make_unique< File >( it->second.first, stat );
    }

    std::map< std::string, std::pair< const char *, clang::vfs::Status > > filemap;
    std::vector< std::string > storage;
    std::set< std::string > allowedPrefixes;
};

/*
 A compiler, cabaple of compiling single file into LLVM module

 The compiler is not thread safe, and all modules are bound to its context (so
 they will not be usable when the compiler is destructed. However, as each
 compiler has its own context, multiple compilers in different threads will
 work
 */
struct Compiler {

    enum class FileType {
        Unknown,
        C, Cpp, CPrepocessed, CppPreprocessed, IR, BC
    };

    FileType typeFromFile( std::string name ) {
        auto ext = brick::fs::takeExtension( name );
        if ( ext == ".c" )
            return FileType::C;
        for ( auto &x : { ".cpp", ".cc", ".C", ".CPP", ".c++", ".cp", ".cxx" } )
            if ( ext == x )
                return FileType::Cpp;
        if ( ext == ".i" )
            return FileType::CPrepocessed;
        if ( ext == ".ii" )
            return FileType::CppPreprocessed;
        if ( ext == ".bc" )
            return FileType::BC;
        if ( ext == ".ll" )
            return FileType::IR;
        return FileType::Unknown;
    }

    void setupStacktracePrinter() {
        llvm::sys::PrintStackTraceOnErrorSignal();
    }

    std::vector< std::string > argsOfType( FileType t ) {
        std::vector< std::string > out { "-x" };
        switch ( t ) {
            case FileType::Cpp:
                add( out, { "c++" } );
                break;
            case FileType::C:
                add( out, { "c" } );
                break;
            case FileType::CppPreprocessed:
                add( out, { "c++cpp-output" } );
                break;
            case FileType::CPrepocessed:
                add( out, { "cpp-output" } );
                break;
            case FileType::BC:
            case FileType::IR:
                add( out, { "ir" } );
                break;
            case FileType::Unknown:
                UNREACHABLE( "Unknown file type" );
        }
        switch ( t ) {
            case FileType::Cpp:
            case FileType::CppPreprocessed:
                add( out, { "-fcxx-exceptions", "-fexceptions" } );
                break;
            default: ;
        }
        return out;
    }

    explicit Compiler( std::shared_ptr< llvm::LLVMContext > ctx = nullptr ) :
        divineVFS( new DivineVFS() ),
        overlayFS( new clang::vfs::OverlayFileSystem( clang::vfs::getRealFileSystem() ) ),
        ctx( ctx )
    {
        if ( !ctx )
            this->ctx = std::make_shared< llvm::LLVMContext >();
        // setup VFS
        overlayFS->pushOverlay( divineVFS );
        if ( !ctx )
            ctx.reset( new llvm::LLVMContext );
    }

    template< typename T >
    Compiler &mapVirtualFile( std::string path, const T &contents ) {
        divineVFS->addFile( path, contents );
        return *this;
    }

    template< typename T >
    Compiler &reMapVirtualFile( std::string path, const T &contents ) {
        divineVFS->addFile( path, contents, true );
        return *this;
    }

    template< typename T >
    Compiler &mapVirtualFiles( std::initializer_list< std::pair< std::string, const T & > > files ) {
        for ( auto &x : files )
            mapVirtualFile( x.first, x.second );
        return *this;
    }

    std::vector< std::string > filesMappedUnder( std::string path ) {
        return divineVFS->filesMappedUnder( path );
    }

    Compiler &allowIncludePath( std::string path ) {
        divineVFS->allowPath( path );
        return *this;
    }

    std::unique_ptr< llvm::Module > compileModule( std::string filename,
                                FileType type, std::vector< std::string > args )
    {
        // Build an invocation
        auto invocation = std::make_unique< clang::CompilerInvocation >();
        std::vector< std::string > cc1args = { "-cc1",
                                                "-triple", "x86_64-unknown-none-elf",
                                                "-emit-obj",
                                                "-mrelax-all",
                                                // "-disable-free",
                                                // "-disable-llvm-verifier",
//                                                "-main-file-name", "test.c",
                                                "-mrelocation-model", "static",
                                                "-mthread-model", "posix",
                                                "-mdisable-fp-elim",
                                                "-fmath-errno",
                                                "-masm-verbose",
                                                "-mconstructor-aliases",
                                                "-munwind-tables",
                                                "-fuse-init-array",
                                                "-target-cpu", "x86-64",
                                                "-dwarf-column-info",
                                                // "-coverage-file", "/home/xstill/DiVinE/clangbuild/test.c", // ???
                                                // "-resource-dir", "../lib/clang/3.7.1", // ???
                                                // "-internal-isystem", "/usr/local/include",
                                                // "-internal-isystem", "../lib/clang/3.7.1/include",
                                                // "-internal-externc-isystem", "/include",
                                                // "-internal-externc-isystem", "/usr/include",
                                                // "-fdebug-compilation-dir", "/home/xstill/DiVinE/clangbuild", // ???
                                                "-ferror-limit", "19",
                                                "-fmessage-length", "212",
                                                "-mstackrealign",
                                                "-fobjc-runtime=gcc",
                                                "-fdiagnostics-show-option",
                                                "-fcolor-diagnostics",
                                                // "-o", "test.o",
                                                };
        add( cc1args, args );
        add( cc1args, argsOfType( type ) );
        cc1args.push_back( filename );


        std::vector< const char * > cc1a;
        std::transform( cc1args.begin(), cc1args.end(),
                        std::back_inserter( cc1a ),
                        []( std::string &str ) { return str.c_str(); } );

        clang::TextDiagnosticPrinter diagprinter( llvm::errs(), new clang::DiagnosticOptions() );
        clang::DiagnosticsEngine diag(
                llvm::IntrusiveRefCntPtr< clang::DiagnosticIDs >( new clang::DiagnosticIDs() ),
                new clang::DiagnosticOptions(), &diagprinter, false );
        bool succ = clang::CompilerInvocation::CreateFromArgs(
                            *invocation, &cc1a[ 0 ], &*cc1a.end(), diag );
        if ( !succ )
            throw CompileError( "Failed to create a compiler invocation for " + filename );
        invocation->getDependencyOutputOpts() = clang::DependencyOutputOptions();

        // actually run the compiler invocation
        clang::CompilerInstance compiler( std::make_shared< clang::PCHContainerOperations>() );
        auto fmgr = std::make_unique< clang::FileManager >( clang::FileSystemOptions(), overlayFS );
        compiler.setFileManager( fmgr.get() );
        compiler.setInvocation( invocation.release() );
        ASSERT( compiler.hasInvocation() );
        compiler.createDiagnostics( &diagprinter, false );
        ASSERT( compiler.hasDiagnostics() );
        compiler.createSourceManager( *fmgr.release() );
        // emits module in memory, does not write it info a file
        auto emit = std::make_unique< clang::EmitLLVMOnlyAction >( ctx.get() );
        succ = compiler.ExecuteAction( *emit );
        if ( !succ )
            throw CompileError( "Error building " + filename );

        return emit->takeModule();
    }

    auto compileModule( std::string filename, std::vector< std::string > args = { } )
    {
        return compileModule( filename, typeFromFile( filename ), args );
    }

    static std::string serializeModule( llvm::Module &m ) {
        std::string str;
        {
            llvm::raw_string_ostream os( str );
            llvm::WriteBitcodeToFile( &m, os );
            os.flush();
        }
        return str;
    }

    template< typename ... Args >
    std::string compileAndSerializeModule( Args &&... args ) {
        auto mod = compileModule( std::forward< Args >( args )... );
        return serializeModule( mod.get() );
    }

    std::unique_ptr< llvm::Module > materializeModule( llvm::StringRef str ) {
        return std::move( llvm::parseBitcodeFile(
                    llvm::MemoryBufferRef( str, "module.bc" ), *ctx ).get() );
    }

    std::shared_ptr< llvm::LLVMContext > context() { return ctx; }

  private:

    template< typename A, typename B = std::initializer_list< std::decay_t<
                            decltype( *std::declval< A & >().begin() ) > > >
    static void add( A &a, B b ) {
        std::copy( b.begin(), b.end(), std::back_inserter( a ) );
    }

    llvm::IntrusiveRefCntPtr< DivineVFS > divineVFS;
    llvm::IntrusiveRefCntPtr< clang::vfs::OverlayFileSystem > overlayFS;
    std::shared_ptr< llvm::LLVMContext > ctx;
};
} // namespace cc
} // namespace divine
