// -*- C++ -*- (c) 2016 Vladimír Štill <xstill@fi.muni.cz>

#include <stdexcept>
#include <utility>
#include <brick-types>
DIVINE_RELAX_WARNINGS
#include <llvm/Support/raw_ostream.h>
DIVINE_UNRELAX_WARNINGS

namespace lart {

struct UnexpectedValue : std::runtime_error {
    using std::runtime_error::runtime_error;
};

struct UnexpectedLlvmIr : UnexpectedValue {
    using UnexpectedValue::UnexpectedValue;

    template< typename... Vals >
    UnexpectedLlvmIr( std::string msg, Vals &&... toDump ) :
        UnexpectedValue( megeMsg( std::move( msg ), std::forward< Vals >( toDump )... ) )
    { }

  private:
    template< typename V >
    static auto dump( llvm::raw_string_ostream &str, V &v, brick::types::Preferred )
        -> decltype( v.print( str ) )
    { v.print( str ); }

    template< typename V >
    static auto dump( llvm::raw_string_ostream &str, V *v, brick::types::Preferred )
        -> decltype( v->print( str ) )
    { v->print( str ); }


    template< typename V >
    static void dump( llvm::raw_string_ostream &, V &&, brick::types::NotPreferred )
    { }

    template< typename... Vals >
    static std::string megeMsg( std::string msg, Vals &&... toDump ) {
        std::string buffer;
        llvm::raw_string_ostream str( buffer );
        str << msg;
        str << "\nrelevant values:\n";
        ( dump( str, std::forward< Vals >( toDump ), brick::types::Preferred() ), ... );
        return str.str();
    }
};

#define ENSURE_LLVM( X, ... ) \
    if ( !( X ) ) { \
        throw ::lart::UnexpectedLlvmIr( \
                std::string( "Failed ENSURE: " #X " at " __FILE__ ":" ) + std::to_string( __LINE__ ), \
                ##__VA_ARGS__ ); \
    } else ((void)0)

} // namespace llvm
