// -*- C++ -*- (c) 2016 Henrich Lauko <xlauko@mail.muni.cz>
#include <lart/abstract/intrinsic.h>

#include <sstream>

namespace lart {
namespace abstract {

namespace intrinsic {

namespace {
    std::vector< std::string > parse( const llvm::CallInst * call ) {
        if ( !call->getCalledFunction()->hasName() )
            return {};
        auto name = call->getCalledFunction()->getName();
        std::istringstream ss(name);

        std::string part;
        std::vector< std::string > parts;
        while( std::getline( ss, part, '.' ) ) {
            parts.push_back( part );
        }

        return parts;
    }
}

// intrinsic format: lart.<domain>.<name>.<spec>.<type1>.<type2>

const std::string domain( const llvm::CallInst * call ) {
    auto parts = parse( call );
    return parts.size() > 2 ? parts[1] : "";
}

const std::string name( const llvm::CallInst * call ) {
    auto parts = parse( call );
    return parts.size() > 2 ? parts[2] : "";
}

const std::string ty1( const llvm::CallInst * call ) {
    auto parts = parse( call );
    return parts.size() >= 3 ? parts[3] : "";
}

const std::string ty2( const llvm::CallInst * call ) {
    auto parts = parse( call );
    return parts.size() >= 4 ? parts[4] : "";
}

const std::string tag( const llvm::Instruction * i ) {
    //todo args

    return tag( i, Domain::Abstract );
}

const std::string tag( const llvm::Instruction * i, Domain d  ) {
    //todo args
    return std::string("lart.") + domainName( d ) +
           "." + i->getOpcodeName( i->getOpcode() );
}

llvm::Function * get( llvm::Module * m,
                      llvm::Type * rty,
                      const std::string & tag,
                      llvm::ArrayRef < llvm::Type * > types )
{
	auto fty = llvm::FunctionType::get( rty, types, false );
    return llvm::cast< llvm::Function >( m->getOrInsertFunction( tag, fty ) );
}

llvm::CallInst * build( llvm::Module * m,
                        llvm::IRBuilder<> & irb,
                        llvm::Type * rty,
                        const std::string & tag,
                        std::vector< llvm::Value * > args )
{
    std::vector< llvm::Type * > argTypes ;
    for ( auto arg : args )
        argTypes.push_back( arg->getType() );
    auto call = get( m, rty, tag, argTypes );
    return irb.CreateCall( call, args );
}

llvm::CallInst * anonymous( llvm::Module * m,
                            llvm::IRBuilder<> & irb,
                            llvm::Type * rty,
                            std::vector< llvm::Value * > args )
{
	/*auto fty = llvm::FunctionType::get( rty, types( args ), false );
    using Linkage = llvm::GlobalValue::LinkageTypes;
    auto call = llvm::Fun::Create( fty, Linkage::ExternalLinkage, "", i->getModule() );
	return irb.CreateCall( call, args );*/
    return build( m, irb, rty, "", args );
}

//helpers
bool isLift( const llvm::CallInst * call ) {
    return intrinsic::name( call ) == "lift";
}

bool isLower( const llvm::CallInst * call ) {
    return intrinsic::name( call ) == "lower";
}

} // namespace intrinsic

} // namespace abstract
} // namespace lart
