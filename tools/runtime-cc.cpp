#include <divine/cc/cc1.hpp>
#include <divine/rt/paths.hpp>

DIVINE_RELAX_WARNINGS
#include <llvm/Bitcode/BitcodeWriter.h>
DIVINE_UNRELAX_WARNINGS

#include <lart/divine/debugpaths.hpp>
#include <brick-string>
#include <brick-fs>
#include <brick-llvm>
#include <iostream>

using namespace divine;

/* usage: runtime-cc srcdir bindir source.c output.bc [flags] */
int main( int argc, const char **argv )
{
    try {
        cc::CC1 clang;
        std::string srcDir = argv[1], binDir = argv[2];
        clang.allowIncludePath( srcDir );
        clang.allowIncludePath( binDir );
        std::vector< std::string > opts;
        std::copy( argv + 5, argv + argc, std::back_inserter( opts ) );

        std::string depfile;

        auto end = std::remove_if( opts.begin(), opts.end(),
                                   []( auto s ) { return brq::starts_with( s, "-M" ); } );

        for ( auto i = end; i != opts.end(); ++i )
            if ( brq::starts_with( *i, "-MF" ) )
                depfile = i->substr( 3 );

        opts.erase( end, opts.end() );
        auto mod = clang.compile( argv[3], opts, depfile );

        TRACE( "bindir =", binDir, "srcdir =", srcDir );
        lart::divine::rewriteDebugPaths( *mod, [=]( auto p )
        {
            auto n = p;
            if ( brq::starts_with( p, srcDir ) )
                n = p.substr( srcDir.size() );
            if ( brq::starts_with( p, binDir ) )
                n = p.substr( binDir.size() );
            TRACE( "rewrite", p, "to", n );
            return n;
        } );

        brick::llvm::writeModule( mod.get(), argv[4] );

        return 0;
    } catch ( cc::CompileError &err ) {
        std::cerr << err.what() << std::endl;
        return 1;
    }
}
