// -*- mode: C++; indent-tabs-mode: nil; c-basic-offset: 4 -*-

/*
 * (c) 2018 Henrich Lauko <xlauko@mail.muni.cz>
 * (c) 2017-2018 Petr Ročkai <code@fixp.eu>
 * (c) 2017 Vladimír Štill <xstill@fi.muni.cz>
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

#include <divine/smt/builder-z3.hpp>

#include <cmath>

#if OPT_Z3
namespace divine::smt::builder
{

using namespace std::literals;

size_t bitwidth( const z3::sort & sort )
{
    if ( sort.is_bv() )
        return sort.bv_size();
    if ( sort.is_fpa() )
        return sort.fpa_ebits() + sort.fpa_sbits();
    ASSERT( sort.is_bool() );
    return 1; // bool
}

z3::expr Z3::expr( Z3_ast ast )
{
    return z3::expr( _ctx, ast );
}

z3::sort Z3::fpa_sort( int bw )
{
    if ( bw == 32 )
        return _ctx.fpa_sort< 32 >();
    if ( bw == 64 )
        return _ctx.fpa_sort< 64 >();
    UNREACHABLE( "unsupported fpa sort type of bitwidth ", bw );
}

z3::expr Z3::constant( bool v )
{
    return _ctx.bool_val( v );
}

template< typename T >
z3::expr Z3::make_fpa_val( T v, int bw )
{
    auto sort = fpa_sort( bw );
    switch( std::fpclassify( v ) )
    {
        case FP_INFINITE:
            return expr( Z3_mk_fpa_inf( _ctx, sort, std::signbit( v ) ) );
        case FP_NAN:
            return expr( Z3_mk_fpa_nan( _ctx, sort ) );
        case FP_ZERO:
            return expr( Z3_mk_fpa_zero( _ctx, sort, std::signbit( v ) ) );
        default:
            return _ctx.fpa_val( v );
    }
}

z3::expr Z3::constant( float v )  { return make_fpa_val( v, 32 ); }
z3::expr Z3::constant( double v ) { return make_fpa_val( v, 64 ); }

z3::expr Z3::constant( uint64_t value, int bw )
{
    return _ctx.bv_val( value, bw );
}

z3::expr Z3::variable( int id, brq::smt_op op )
{
    auto name = "var_"s + std::to_string( id );
    auto traits = brq::smt_traits( op );
    if ( traits.is_integral() )
    {
        return _ctx.bv_const( name.c_str(), traits.bitwidth );
    }
    else if ( traits.is_float() )
    {
        if ( traits.bitwidth == 32 )
            return _ctx.fpa_const( name.c_str(), 8, 24 );
        if ( traits.bitwidth == 64 )
            return _ctx.fpa_const( name.c_str(), 11, 53 );
        UNREACHABLE( "Unsupported floating point bitwidth." );
    }
    UNREACHABLE( "Unsupported variable type." );
}

z3::expr Z3::array( int id, brq::smt_array_type array )
{
    auto name = "arr_"s + std::to_string( id );
    auto idx = _ctx.bv_sort( 32 );
    auto val = [&] {
        using array_type = brq::smt_array_type::type_t;
        switch ( array.type )
        {
            case array_type::bitvector:
                return _ctx.bv_sort( array.bitwidth );
            case array_type::floating:
                return fpa_sort( array.bitwidth );
            case array_type::array:
                UNREACHABLE( "Unsupported array of arrays." );

        }
    } ();
    return _ctx.constant( name.c_str(), _ctx.array_sort( idx, val ) );
}

z3::expr Z3::load( Node arr, Node off, int /* bw */ )
{
    return z3::select( arr, off );
}

z3::expr Z3::store( Node arr, Node off, Node val, int /* bw */ )
{
    return z3::store( arr, off, val );
}

z3::expr Z3::unary( brq::smt_op op, Node arg, int bw )
{
    int childbw = arg.is_bv() ? arg.get_sort().bv_size() : 1;
    if ( op == op_t::bv_zfit ) {
        if ( arg.get_sort().is_fpa() )
            op = bw > childbw ? op_t::fp_ext : op_t::fp_trunc;
        else
            op = bw > childbw ? op_t::bv_zext : op_t::bv_trunc;
    }

    switch ( op )
    {
        case op_t::bv_trunc:
            ASSERT_LEQ( bw, childbw );
            ASSERT( arg.is_bv() );
            if ( bw == childbw )
                return arg;
            return arg.extract( bw - 1, 0 );
        case op_t::bv_zext:
            ASSERT_LEQ( childbw, bw );
            if ( bw == childbw )
                return arg;
            return arg.is_bv()
                ? z3::zext( arg, bw - childbw )
                : z3::ite( arg, _ctx.bv_val( 1, bw ), _ctx.bv_val( 0, bw ) );
        case op_t::bv_sext:
            ASSERT_LEQ( childbw, bw );
            if ( bw == childbw )
                return arg;
            return arg.is_bv()
                ? z3::sext( arg, bw - childbw )
                : z3::ite( arg, ~_ctx.bv_val( 0, bw ), _ctx.bv_val( 0, bw ) );

        case op_t::fp_ext:
            ASSERT_LT( childbw, bw );
            ASSERT( arg.is_fpa() );
            if ( bw == childbw )
                return arg;
            return expr(
                Z3_mk_fpa_to_fp_float( _ctx, _ctx.fpa_rounding_mode(), arg, fpa_sort( bw ) )
            );
        case op_t::fp_trunc:
            ASSERT_LT( bw, childbw );
            ASSERT( arg.is_fpa() );
            if ( bw == childbw )
                return arg;
            return expr(
                Z3_mk_fpa_to_fp_float( _ctx, _ctx.fpa_rounding_mode(), arg, fpa_sort( bw ) )
            );
        case op_t::fp_tosbv:
            ASSERT_EQ( childbw, bw );
            return expr(
                Z3_mk_fpa_to_sbv( _ctx, _ctx.fpa_rounding_mode(), arg, bw )
            );
        case op_t::fp_toubv:
            ASSERT_EQ( childbw, bw );
            return expr(
                Z3_mk_fpa_to_ubv( _ctx, _ctx.fpa_rounding_mode(), arg, bw )
            );
        case op_t::bv_stofp:
            ASSERT_EQ( childbw, bw );
            return expr(
                Z3_mk_fpa_to_fp_signed( _ctx, _ctx.fpa_rounding_mode(), arg, fpa_sort( bw ) )
            );
        case op_t::bv_utofp:
            ASSERT_EQ( childbw, bw );
            return expr(
                Z3_mk_fpa_to_fp_unsigned( _ctx, _ctx.fpa_rounding_mode(), arg, fpa_sort( bw ) )
            );
        case op_t::bv_not:
        case op_t::bool_not:
            ASSERT_EQ( childbw, bw );
            ASSERT_EQ( bw, 1 );
            return arg.is_bv() ? ~arg : !arg;
        default:
            UNREACHABLE( "unknown unary operation", op );
    }
}

z3::expr Z3::extract( Node arg, std::pair< int, int > bounds )
{
    ASSERT( arg.is_bv() );
    return arg.extract( bounds.second, bounds.first );
}

z3::expr Z3::binary( brq::smt_op op, Node a, Node b, int )
{
    if ( smt_traits( op ).is_integral() )
    {
        auto bw = bitwidth( a.get_sort() );
        auto rm = _ctx.fpa_rounding_mode();
        if ( a.is_fpa() )
            a = expr( Z3_mk_fpa_to_ubv( _ctx, rm, a, bw ) );
        if ( b.is_fpa() )
            b = expr( Z3_mk_fpa_to_ubv( _ctx, rm, b, bw ) );
    }

    if ( smt_traits( op ).is_float() )
    {
        auto sort = fpa_sort( bitwidth( a.get_sort() ) );
        if ( a.is_bv() )
            a = expr( Z3_mk_fpa_to_fp_bv( _ctx, a, sort ) );
        if ( b.is_bv() )
            b = expr( Z3_mk_fpa_to_fp_bv( _ctx, b, sort ) );

        assert( a.is_fpa() && b.is_fpa() );
    }

    if ( a.is_bv() && b.is_bv() )
    {
        switch ( op )
        {
            case op_t::bv_add:  return a + b;
            case op_t::bv_sub:  return a - b;
            case op_t::bv_mul:  return a * b;
            case op_t::bv_sdiv: return a / b;
            case op_t::bv_udiv: return z3::udiv( a, b );
            case op_t::bv_srem: return z3::srem( a, b );
            case op_t::bv_urem: return z3::urem( a, b );
            case op_t::bv_shl:  return z3::shl( a, b );
            case op_t::bv_ashr: return z3::ashr( a, b );
            case op_t::bv_lshr: return z3::lshr( a, b );
            case op_t::bool_and:
            case op_t::bv_and:  return a & b;
            case op_t::bv_or:   return a | b;
            case op_t::bv_xor:  return a ^ b;

            case op_t::bv_ule:  return z3::ule( a, b );
            case op_t::bv_ult:  return z3::ult( a, b );
            case op_t::bv_uge:  return z3::uge( a, b );
            case op_t::bv_ugt:  return z3::ugt( a, b );
            case op_t::bv_sle:  return a <= b;
            case op_t::bv_slt:  return a < b;
            case op_t::bv_sge:  return a >= b;
            case op_t::bv_sgt:  return a > b;
            case op_t::eq:   return a == b;
            case op_t::neq:   return a != b;
            case op_t::bv_concat: return z3::concat( a, b );
            default:
                UNREACHABLE( "unknown binary operation", op );
        }
    }
    else if ( a.is_fpa() && b.is_fpa() )
    {
        switch ( op )
        {
            case op_t::fp_add: return a + b;
            case op_t::fp_sub: return a - b;
            case op_t::fp_mul: return a * b;
            case op_t::fp_div: return a / b;
            case op_t::fp_rem:
                UNREACHABLE( "unsupported operation fp_rem" );
            case op_t::fp_oeq: return expr( Z3_mk_fpa_eq( _ctx, a, b ) );
            case op_t::fp_ogt: return a > b;
            case op_t::fp_oge: return expr( Z3_mk_fpa_geq( _ctx, a, b ) );
            case op_t::fp_olt: return a < b;
            case op_t::fp_ole: return a <= b;
            case op_t::fp_one: return a != b;
            case op_t::fp_ord:
                UNREACHABLE( "unsupported operation fp_ord" );
            case op_t::fp_ueq: return expr( Z3_mk_fpa_eq( _ctx, a, b ) );
            case op_t::fp_ugt: return a > b;
            case op_t::fp_uge: return expr( Z3_mk_fpa_geq( _ctx, a, b ) );
;
            case op_t::fp_ult: return a < b;
            case op_t::fp_ule: return a <= b;
            case op_t::fp_une: return a != b;
            case op_t::fp_uno:
                UNREACHABLE( "unknown binary operation fp_uno" );
            default:
                UNREACHABLE( "unknown floating binary operation", op );
        }
    }
    else
    {
        if ( a.is_bv() )
        {
            ASSERT_EQ( a.get_sort().bv_size(), 1 );
            a = ( a == _ctx.bv_val( 1, 1 ) );
        }

        if ( b.is_bv() )
        {
            ASSERT_EQ( b.get_sort().bv_size(), 1 );
            b = ( b == _ctx.bv_val( 1, 1 ) );
        }

        switch ( op )
        {
            case op_t::bool_xor:
            case op_t::bv_xor:
            case op_t::bv_sub:
                return a != b;
            case op_t::bv_add:
                return a && b;
            case op_t::bv_udiv:
            case op_t::bv_sdiv:
                return a;
            case op_t::bv_urem:
            case op_t::bv_srem:
            case op_t::bv_shl:
            case op_t::bv_lshr:
                return constant( false );
            case op_t::bv_ashr:
                return a;
            case op_t::bool_or:
            case op_t::bv_or:
                return a || b;
            case op_t::bool_and:
            case op_t::bv_and:
                return a && b;
            case op_t::bv_uge:
            case op_t::bv_sle:
                return a || !b;
            case op_t::bv_ule:
            case op_t::bv_sge:
                return b || !a;
            case op_t::bv_ugt:
            case op_t::bv_slt:
                return a && !b;
            case op_t::bv_ult:
            case op_t::bv_sgt:
                return b && !a;
            case op_t::eq:
                return a == b;
            case op_t::neq:
                return a != b;
            default:
                UNREACHABLE( "unknown boolean binary operation", op );
        }
    }
}


} // namespace divine::smt::builder
#endif
