#include <divine/cc/clang.hpp>
#include <divine/rt/runtime.hpp>
#include <llvm/Bitcode/ReaderWriter.h>
#include <lart/divine/debugpaths.hpp>
#include <brick-string>
#include <brick-fs>
#include <iostream>

using namespace divine;
using namespace brick;

/* usage: runtime-cc srcdir bindir source.c output.bc [flags] */
int main( int argc, const char **argv )
{
    try {
        cc::Compiler clang;
        std::string srcDir = argv[1], binDir = argv[2];
        clang.allowIncludePath( srcDir );
        clang.allowIncludePath( binDir );
        std::vector< std::string > opts;
        std::copy( argv + 5, argv + argc, std::back_inserter( opts ) );
        auto mod = clang.compileModule( argv[3], opts );

        lart::divine::rewriteDebugPaths( *mod, [=]( auto p ) {
                std::string relpath;
                if ( string::startsWith( p, srcDir ) )
                    relpath = p.substr( srcDir.size() );
                else if ( string::startsWith( p, binDir ) )
                    relpath = p.substr( binDir.size() );
                if ( !relpath.empty() ) {
                    while ( fs::isPathSeparator( relpath[0] ) )
                        relpath.erase( relpath.begin() );
                    return fs::joinPath( rt::directory( relpath ), relpath );
                }
                return p;
            } );

        std::error_code err;
        llvm::raw_fd_ostream outs( argv[4], err, llvm::sys::fs::F_None );
        llvm::WriteBitcodeToFile( mod.get(), outs );
        return 0;
    } catch ( cc::CompileError &err ) {
        std::cerr << err.what() << std::endl;
        return 1;
    }
}
