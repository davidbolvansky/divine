#ifdef __divine__
#include "formula.h"
#include <cstdint>
#include <cstdarg>
#include <sys/divm.h>
#include <new>

using namespace std::literals;
using namespace sym;

template< typename T, typename ... Args >
static T *__new( Args &&...args ) {
    void *ptr = __vm_obj_make( sizeof( T ) );
    new ( ptr ) T( std::forward< Args >( args )... );
    return static_cast< T * >( ptr );
}

namespace sym {

std::string toString( Type t ) {
    std::string str;
    if ( t.type() == Type::Int )
        str = "i";
    else if ( t.type() == Type::Float )
        str = "fp";
    str += std::to_string( t.bitwidth() );
    return str;
}

std::string toString( const Formula *root ) {
    if ( root->op() == Op::Variable )
        return "[v "s + std::to_string( root->var.id ) + ":"s + toString( root->type() ) + "]"s;
    else if ( root->op() == Op::Constant )
        return "[c "s + std::to_string( root->con.value ) + ":"s + toString( root->type() ) + "]"s;
    else if ( isUnary( root->op() ) )
        return toString( root->op() ) + "("s + toString( root->unary.child ) + ") :"s
                + toString( root->type() );
    else if ( isBinary( root->op() ) )
        return toString( root->op() ) + "("s + toString( root->binary.left ) + ", "s
                + toString( root->binary.right ) + ") : "s + toString( root->type() );
    else if ( root->op() == Op::Assume )
        return "assume("s + toString( root->assume.value ) + ", "s
                + toString( root->assume.constraint ) + ")"s;

    UNREACHABLE_F( "unknown operation in to_string: %d", root->op() );
}

std::string toString( Op x ) {
    switch ( x ) {

        case Op::Variable: return "var";
        case Op::Constant: return "con";

        case Op::BitCast: return "bitcast";

        case Op::SExt: return "sext";
        case Op::ZExt: return "zext";
        case Op::Trunc: return "trunc";

        case Op::IntToPtr: return "inttoptr";
        case Op::PtrToInt: return "ptrtoint";

        case Op::FPExt: return "fpext";
        case Op::FPTrunc: return "fptrunc";
        case Op::FPToSInt: return "fptosint";
        case Op::FPToUInt: return "fptouint";
        case Op::SIntToFP: return "sinttofp";
        case Op::UIntToFP: return "uinttofp";

        case Op::Add: return "+";
        case Op::Sub: return "-";
        case Op::Mul: return "*";
        case Op::UDiv: return "/u";
        case Op::SDiv: return "/s";
        case Op::URem: return "%u";
        case Op::SRem: return "%s";

        case Op::FAdd: return "+f";
        case Op::FSub: return "-f";
        case Op::FMul: return "*f";
        case Op::FDiv: return "/f";
        case Op::FRem: return "%f";

        case Op::Shl: return "<<";
        case Op::LShr: return ">>l";
        case Op::AShr: return ">>a";
        case Op::And: return "&";
        case Op::Or: return "|";
        case Op::Xor: return "^";

        // case Op::Icmp
        case Op::EQ: return "==";
        case Op::NE: return "!=";
        case Op::UGT: return ">u";
        case Op::UGE: return ">=u";
        case Op::ULT: return "<u";
        case Op::ULE: return "<=u";
        case Op::SGT: return ">s";
        case Op::SGE: return ">=s";
        case Op::SLT: return "<s";
        case Op::SLE: return "<=s";

        // case Op::Fcmp
        case Op::FcFalse: return "fcfalse"; // no comparison: always returns false
        case Op::FcOEQ: return "==fo"; // ordered and equal
        case Op::FcOGT: return ">fo"; // ordered and greater than
        case Op::FcOGE: return ">=fo"; // ordered and greater than or equal
        case Op::FcOLT: return "<fo"; // ordered and less than
        case Op::FcOLE: return "<=fo"; // ordered and less than or equal
        case Op::FcONE: return "!=fo"; // ordered and not equal
        case Op::FcORD: return "ford"; // ordered (no nans)
        case Op::FcUEQ: return "==fu"; // unordered or equal
        case Op::FcUGT: return ">fu"; // unordered or greater than
        case Op::FcUGE: return ">=fu"; // unordered or greater than or equal
        case Op::FcULT: return "<fu"; // unordered or less than
        case Op::FcULE: return "<=fu"; // unordered or less than or equal
        case Op::FcUNE: return "!=fu"; // unordered or not equal
        case Op::FcUNO: return "funo"; // unordered (either nans)
        case Op::FcTrue: return "fctrue"; // no comparison: always returns true

        default:
            UNREACHABLE_F( "Unknown formula operation %d", int( x ) );
    }
}

}

#if 0
void *__sym_mk_op( int _op, int type, int bitwidth ... ) {

    Op op = Op( _op );
    Type t( Type::T( type ), bitwidth );
    va_list vl;
    va_start( vl, bitwidth );

    if ( op == Op::Variable ) {
        VarID varid = va_arg( vl, VarID );
        va_end( vl );
        return __new< Variable >( t, varid );
    }

    if ( op == Op::Constant ) {
        ValueU val;
        if ( type == Type::Int ) {
            if ( bitwidth <= 32 )
                val.i32 = va_arg( vl, int32_t );
            else if ( bitwidth <= 64 )
                val.i64 = va_arg( vl, int64_t );
            else
                UNREACHABLE_F( "Integer too long: %d bits", bitwidth );
        } else {
            switch ( bitwidth ) {
                case 32:
                    val.fp32 = va_arg( vl, float );
                    break;
                case 64:
                    val.fp64 = va_arg( vl, double );
                    break;
                    /*
                case 80:
                    val.fp80 = va_arg( vl, long double );
                    break;
                    */
                default:
                    UNREACHABLE_F( "Unknow float of size: %d bits", bitwidth );
            }
        }
        va_end( vl );
        return __new< Constant >( t, val.raw );
    }

    if ( isUnary( op ) ) {
        Formula *child = va_arg( vl, Formula * );
        va_end( vl );
        return __new< Unary >( op, t, child );
    }

    if ( isBinary( op ) ) {
        Formula *left = va_arg( vl, Formula * );
        Formula *right = va_arg( vl, Formula * );
        va_end( vl );
        return __new< Binary >( op, t, left, right );
    }

    UNREACHABLE_F( "Unknown op in __sym_mk_op: %d", _op );
}
#endif

char *__sym_formula_to_string( void *root ) {
    auto form = toString( static_cast< sym::Formula * >( root ) );
    char *out = static_cast< char * >( __vm_obj_make( form.size() + 1 ) );
    *std::copy( form.begin(), form.end(), out ) = 0;
    return out;
}


#endif
