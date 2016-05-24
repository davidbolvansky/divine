#include <lart/driver.h>

#include <iostream>
#include <cassert>

#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Support/FileSystem.h>

#include <llvm/Bitcode/ReaderWriter.h>
#include <llvm/Support/raw_os_ostream.h>

#include <llvm/IR/LLVMContext.h>

int main( int argc, char **argv ) {
    lart::Driver driver;

    if ( argc < 3 ) {
        std::cerr << "usage: lart in.bc out.bc [pass:options] ..." << std::endl
                  << std::endl
                  << "pass aa (alias analysis), options:" << std::endl
                  << "    andersen: andersen-style, flow- and context-insensitive" << std::endl
                  << std::endl
                  << "example: lart in.bc out.bc aa:andersen" << std::endl << std::endl;
        for ( auto pass : driver.passes() ) {
            pass.description( std::cerr );
            std::cerr << std::endl;
        }
        return 1;
    }

    const char *from = argv[1], *to = argv[2];
    assert( from );
    assert( to );

    llvm::LLVMContext *ctx = new llvm::LLVMContext();

    std::unique_ptr< llvm::MemoryBuffer > input;
    input = std::move( llvm::MemoryBuffer::getFile( from ).get() );
    assert( input );

    llvm::Module *module;
#if LLVM_MAJOR == 3 && LLVM_MINOR <= 5
    auto inputData = input.get();
#else
    auto inputData = input->getMemBufferRef();
#endif
    auto parsed = parseBitcodeFile( inputData, *ctx );
    if ( !parsed )
        throw std::runtime_error( "Error parsing input model; probably not a valid bitcode file." );
#if LLVM_MAJOR == 3 && LLVM_MINOR < 7
    module = parsed.get();
#else
    module = parsed.get().get();
#endif

#if LLVM_MAJOR == 3 && LLVM_MINOR <= 5
    std::string serr;
#else
    std::error_code serr;
#endif
    ::llvm::raw_fd_ostream outs( to, serr, ::llvm::sys::fs::F_None );

    for ( char **arg = argv + 3; *arg; ++arg )
        driver.setup( *arg );
    driver.process( module );
    lart::Driver::assertValid( module );

    WriteBitcodeToFile( module, outs );
}
