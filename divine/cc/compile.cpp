// -*- C++ -*- (c) 2016-2017 Vladimír Štill

#include <divine/cc/compile.hpp>
#include <divine/rt/runtime.hpp>

DIVINE_RELAX_WARNINGS
#include <llvm/Support/raw_os_ostream.h>
#include <brick-llvm>
DIVINE_UNRELAX_WARNINGS

#include <brick-fs>
#include <brick-string>
#include <brick-types>

namespace divine {
namespace cc {

using brick::fs::joinPath;
using namespace std::literals;

static std::string getWrappedMDS( llvm::NamedMDNode *meta, int i = 0, int j = 0 ) {
    auto *op = llvm::cast< llvm::MDTuple >( meta->getOperand( i ) );
    auto *str = llvm::cast< llvm::MDString >( op->getOperand( j ).get() );
    return str->getString().str();
}

struct MergeFlags_ { // hide in clas so they can be mutually recursive
    void operator()( std::vector< std::string > & ) { }

    template< typename ... Xs >
    void operator()( std::vector< std::string > &out, std::string first, Xs &&... xs ) {
        out.emplace_back( std::move( first ) );
        (*this)( out, std::forward< Xs >( xs )... );
    }

    template< typename C, typename ... Xs >
    auto operator()( std::vector< std::string > &out, C &&c, Xs &&... xs )
        -> decltype( void( (c.begin(), c.end()) ) )
    {
        out.insert( out.end(), c.begin(), c.end() );
        (*this)( out, std::forward< Xs >( xs )... );
    }
};

template< typename ... Xs >
static std::vector< std::string > mergeFlags( Xs &&... xs ) {
    std::vector< std::string > out;
    MergeFlags_()( out, std::forward< Xs >( xs )... );
    return out;
}

Compile::Compile( Options opts, std::shared_ptr< llvm::LLVMContext > ctx ) :
    opts( opts ), compiler( ctx ), linker( new brick::llvm::Linker() )
{
    commonFlags = { "-D__divine__=4"
                  , "-isystem", rt::includeDir
                  , "-isystem", joinPath( rt::includeDir, "libcxx/include" )
                  , "-isystem", joinPath( rt::includeDir, "libcxxabi/include" )
                  , "-isystem", joinPath( rt::includeDir, "libunwind/include" )
                  , "-isystem", joinPath( rt::includeDir, "libc/include" )
                  , "-isystem", joinPath( rt::includeDir, "libc/internals" )
                  , "-isystem", joinPath( rt::includeDir, "libm/include" )
                  , "-D_POSIX_C_SOURCE=2008098L"
                  , "-D_LITTLE_ENDIAN=1234"
                  , "-D_BYTE_ORDER=1234"
                  , "-g"
                  , "-U__x86_64"
                  , "-U__x86_64__"
                  };
}

Compile::~Compile() { }

void Compile::compileAndLink( std::string path, std::vector< std::string > flags )
{
    linker->link( compile( path, flags ) );
}

void Compile::compileAndLink( std::string path, Compiler::FileType type, std::vector< std::string > flags )
{
    linker->link( compile( path, type, flags ) );
}

std::unique_ptr< llvm::Module > Compile::compile( std::string path,
                                    std::vector< std::string > flags )
{
    return compile( path, Compiler::typeFromFile( path ), flags );
}

std::unique_ptr< llvm::Module > Compile::compile( std::string path,
                                    Compiler::FileType type,
                                    std::vector< std::string > flags )
{
    std::vector< std::string > allFlags;
    std::copy( commonFlags.begin(), commonFlags.end(), std::back_inserter( allFlags ) );
    std::copy( flags.begin(), flags.end(), std::back_inserter( allFlags ) );
    if ( opts.verbose )
        std::cerr << "compiling " << path << std::endl;
    if ( path[0] == '/' )
        compiler.allowIncludePath( std::string( path, 0, path.rfind( '/' ) ) );
    auto mod = compiler.compileModule( path, type, allFlags );

    return mod;
}

ParsedOpts parseOpts( std::vector< std::string > rawCCOpts ) {
    using FT = Compiler::FileType;
    FT xType = FT::Unknown;
    ParsedOpts po;

    for ( auto it = rawCCOpts.begin(), end = rawCCOpts.end(); it != end; ++it )
    {
        std::string isystem = "-isystem", inc = "-inc";
        if ( brick::string::startsWith( *it, "-I" ) ) {
            std::string val;
            if ( it->size() > 2 )
                val = it->substr( 2 );
            else
                val = *++it;
            po.allowedPaths.emplace_back( val );
            po.opts.emplace_back( "-I" + val );
        }
        else if ( brick::string::startsWith( *it, isystem ) ) {
            std::string val;
            if ( it->size() > isystem.size() )
                val = it->substr( isystem.size() );
            else
                val = *++it;
            po.allowedPaths.emplace_back( val );
            po.opts.emplace_back( isystem + val );
        }
        else if ( *it == "-include" )
            po.opts.emplace_back( *it ), po.opts.emplace_back( *++it );
        else if ( brick::string::startsWith( *it, "-x" ) ) {
            std::string val;
            if ( it->size() > 2 )
                val = it->substr( 2 );
            else
                val = *++it;
            if ( val == "none" )
                xType = FT::Unknown;
            else {
                xType = Compiler::typeFromXOpt( val );
                if ( xType == FT::Unknown )
                    throw std::runtime_error( "-x value not recognized: " + val );
            }
            // this option is propagated to CC by xType, not directly
        }
        else if ( brick::string::startsWith( *it, "-l" ) ) {
            std::string val = it->size() > 2 ? it->substr( 2 ) : *++it;
            po.files.emplace_back( Lib::InPlace(), val );
        }
        else if ( brick::string::startsWith( *it, "-L" ) ) {
            std::string val = it->size() > 2 ? it->substr( 2 ) : *++it;
            po.allowedPaths.emplace_back( val );
            po.libSearchPath.emplace_back( std::move( val ) );
        }
        else if ( brick::string::startsWith( *it, "-o" )) {
            std::string val;
            if ( it->size() > 2 )
                val = it->substr( 2 );
            else
                val = *++it;
            po.outputFile = val;
        }
        else if ( !brick::string::startsWith( *it, "-" ) )
            po.files.emplace_back( File::InPlace(), *it, xType == FT::Unknown ? Compiler::typeFromFile( *it ) : xType );
        else
            po.opts.emplace_back( *it );
    }

    return po;
}

void Compile::runCC( std::vector< std::string > rawCCOpts,
                     std::function< ModulePtr( ModulePtr &&, std::string ) > moduleCallback )
{
    using FT = Compiler::FileType;
    auto po = parseOpts( rawCCOpts );

    for ( auto path : po.allowedPaths )
        compiler.allowIncludePath( path );

    if ( !moduleCallback )
        moduleCallback = []( ModulePtr &&m, std::string ) -> ModulePtr {
            return std::move( m );
        };

    for ( auto &f : po.files )
        f.match(
            [&]( const File &f ) {
                if ( f.type == FT::Unknown )
                    throw std::runtime_error( "cannot detect file format for file '" + f.name + "', please supply -x option for it" );
                auto m = moduleCallback( compile( f.name, f.type, po.opts ), f.name );
                if ( m )
                    linker->link( std::move( m ) );
            },
            [&]( const Lib &l ) {
                linkLib( l.name, po.libSearchPath );
            } );
    if ( linker->hasModule() ) {
        linkEssentials();
        linkLibs( defaultDIVINELibs );
    }
}

llvm::Module *Compile::getLinked() {
    brick::llvm::verifyModule( linker->get() );
    return linker->get();
}

void Compile::writeToFile( std::string filename ) {
    writeToFile( filename, linker->get() );
}

void Compile::writeToFile( std::string filename, llvm::Module *mod )
{
    brick::llvm::writeModule( mod, filename );
}

std::string Compile::serialize() {
    return compiler.serializeModule( *getLinked() );
}

void Compile::addDirectory( std::string path ) {
    compiler.allowIncludePath( path );
}

void Compile::addFlags( std::vector< std::string > flags ) {
    std::copy( flags.begin(), flags.end(), std::back_inserter( commonFlags ) );
}

std::shared_ptr< llvm::LLVMContext > Compile::context() { return compiler.context(); }

void Compile::linkLibs( std::vector< std::string > ls, std::vector< std::string > searchPaths ) {
    for ( auto lib : ls )
        linkLib( lib, searchPaths );
}

brick::llvm::ArchiveReader Compile::getLib( std::string lib, std::vector< std::string > searchPaths ) {
    using namespace brick::fs;

    std::string name;
    searchPaths.push_back( "/lib" );
    for ( auto p : searchPaths ) {
        for ( auto suf : { "a", "bc" } ) {
            auto n = joinPath( p, "lib" + lib + "."s + suf );
            if ( compiler.fileExists( n ) ) {
                name = n;
                break;
            }
        }
    }

    if ( name.empty() )
        throw std::runtime_error( "Library not found: " + lib );

    auto buf = compiler.getFileBuffer( name );
    if ( !buf )
        throw std::runtime_error( "Cannot open library file: " + name );

    return brick::llvm::ArchiveReader( std::move( buf ), context() );
}

void Compile::linkLib( std::string lib, std::vector< std::string > searchPaths ) {
    auto archive = getLib( lib, std::move( searchPaths ) );
    linker->linkArchive( archive );
}

void Compile::linkEssentials() {
    for ( auto e : { "dios", "abstract" } ) {
        auto archive = getLib( e );
        auto modules = archive.modules();
        for ( auto it = modules.begin(); it != modules.end(); ++it )
            linker->link( it.take() );
    }

    // these functions are implemented as intrinsics in LLVM so they don't have
    // declarations and aren't linked unless explicitly added
    llvm::Module mem( "divine-mem.ll", *context() );
    mem.setDataLayout( linker->get()->getDataLayoutStr() );
    auto *vptrt = llvm::Type::getInt8PtrTy( *context() );
    auto *sizet = llvm::Type::getInt64Ty( *context() );
    auto *intt = llvm::Type::getInt32Ty( *context() );
    auto *mct = llvm::FunctionType::get( vptrt, { vptrt, vptrt, sizet }, false );
    mem.getOrInsertFunction( "memcpy", mct );
    mem.getOrInsertFunction( "memmove", mct );
    mem.getOrInsertFunction( "memset", llvm::FunctionType::get( vptrt, { vptrt, intt, sizet }, false ) );
    linker->link( mem );
}

const std::vector< std::string > Compile::defaultDIVINELibs = { "cxx", "cxxabi", "c" };

}
}
