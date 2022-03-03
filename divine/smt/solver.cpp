#include <divine/smt/solver.hpp>
#include <divine/smt/builder.hpp>
#include <divine/vm/memory.hpp>
#include <brick-proc>
#include <brick-bitlevel>

using namespace divine::smt::builder;

namespace divine::smt::solver
{

using op_t = brq::smt_op;

Result SMTLib::solve()
{
    auto b = builder( 'z' - 'a' );
    auto q = b.constant( true );

    for ( auto clause : _asserts )
        q = builder::mk_bin( b, brq::smt_op::bv_and, 1, q, clause );

    auto r = brq::spawn_and_wait( brq::stdin_string( _ctx.query( q ) ) | brq::capture_stdout |
                                  brq::capture_stderr, _opts );

    std::string_view result = r.out();
    if ( result.substr( 0, 5 ) == "unsat" )
        return Result::False;
    if ( result.substr( 0, 3 ) == "sat" )
        return Result::True;
    if ( result.substr( 0, 7 ) == "unknown" )
        return Result::Unknown;

    std::cerr << "E: The SMT solver produced an error: " << r.out() << std::endl
              << "E: The input formula was: " << std::endl
              << _ctx.query( q ) << std::endl;
    UNREACHABLE( "Invalid SMT reply" );
}

template< typename Core, typename Node >
op_t equality( const Node& node ) noexcept
{
#if OPT_STP
    if constexpr ( std::is_same_v< Core, STP > )
        return op_t::eq;
    else
#endif
        return node.is_bv() || node.is_bool() ? op_t::eq : op_t::fp_oeq;
}

template< typename Core >
bool Simple< Core >::equal( vm::HeapPointer path, SymPairs &sym_pairs,
                            vm::CowHeap &h_1, vm::CowHeap &h_2 )
{
    equality_timer _t;
    this->reset();
    auto e_1 = this->extract( h_1, 1 ), e_2 = this->extract( h_2, 2 );
    auto b = this->builder();

    auto v_eq = b.constant( true );
    auto c_1_rpn = e_1.read_constraints( path ),
         c_2_rpn = e_2.read_constraints( path );
    auto c_1 = c_1_rpn.empty() ? b.constant( true ) : evaluate( e_1, c_1_rpn ),
         c_2 = c_2_rpn.empty() ? b.constant( true ) : evaluate( e_2, c_2_rpn );

    for ( auto [lhs, rhs] : sym_pairs )
    {
        auto f_1 = e_1.read( lhs );
        auto f_2 = e_2.read( rhs );

        auto v_1 = evaluate( e_1, f_1 );
        auto v_2 = evaluate( e_2, f_2 );

        brq::smt_op op = equality< Core >( v_1 );
        auto pair_eq = mk_bin( b, op, 1, v_1, v_2 );
        v_eq = mk_bin( b, op_t::bool_and, 1, v_eq, pair_eq );
    }

    /* we already know that both constraint sets are sat */
    auto c_eq = mk_bin( b, op_t::eq, 1, c_1, c_2 ),
      pc_fail = mk_un(  b, op_t::bool_not, 1, c_1 ),
       v_eq_c = mk_bin( b, op_t::bool_or, 1, pc_fail, v_eq ),
           eq = mk_bin( b, op_t::bool_and, 1, c_eq, v_eq_c );

    this->add( mk_un( b, op_t::bool_not, 1, eq ) );
    auto r = this->solve();
    this->reset();
    return r == Result::False;
}

template< typename Core >
bool Simple< Core >::feasible( vm::CowHeap & heap, vm::HeapPointer ptr )
{
    feasibility_timer _t;
    this->reset();
    auto e = this->extract( heap, 1 );
    auto b = this->builder();
    auto query = evaluate( e, e.read( ptr ) );
    this->add( mk_bin( b, op_t::eq, 1, query, b.constant( 1, 1 ) ) );
    return this->solve() != Result::False;
}

template< typename Core >
Model Simple< Core >::model( vm::CowHeap &heap, vm::HeapPointer path )
{
    this->reset();
    auto e = this->extract( heap, 1 );
    auto b = this->builder();
    auto rpn = e.read_constraints( path );
    auto constraints = rpn.empty() ? b.constant( true ) : evaluate( e, rpn );
    this->add( mk_bin( b, op_t::eq, 1, constraints, b.constant( 1, 1 ) ) );
    return Core::model();
}

template< typename Core >
bool Caching< Core >::feasible( vm::CowHeap &heap, vm::HeapPointer ptr )
{
    feasibility_timer _t;
    auto extract = this->extract( heap, 1 );
    auto expr = extract.read( ptr );

    if ( auto hit = _cache.find( item{ expr, 0, 0 } ); hit.valid() )
        return ++ hit->hits, hit->sat;

    this->reset();
    auto b = this->builder();
    auto query = evaluate( extract, expr );
    this->add( mk_bin( b, op_t::eq, 1, query, b.constant( 1, 1 ) ) );
    bool rv = this->solve() != Result::False;
    _cache.insert( item{ expr, 0, rv } );
    return rv;
}

template< typename Core >
bool Incremental< Core >::feasible( vm::CowHeap &/*heap*/, vm::HeapPointer /*ptr*/ )
{
#if 0
    auto e = this->extract( heap );
    auto query = e.constant( true );
    std::unordered_set< vm::HeapPointer > in_context{ _inc.begin(), _inc.end() };
    auto head = ptr;

    while ( !ptr.null() && !in_context.count( ptr ) )
    {
        auto f = e.read( ptr );
        auto clause = e.convert( f->binary.left );
        query = mk_bin( e, Op::And, 1, query, clause );
        ptr = f->binary.right;
    }

    if ( head == ptr ) /* no new fragments */
        return true;

    while ( !_inc.empty() && _inc.back() != ptr )
    {
        _inc.pop_back();
        this->pop();
        this->pop();
    }

    this->push();
    this->add( query );
    auto result = this->solve();

    if ( result == Result::True )
    {
        this->push();
        _inc.push_back( head );
    }
    else
        this->pop();

    return result != Result::False;
    #endif
}

#if OPT_Z3

Model Z3::model()
{
    Model model;

    _solver.check();
    auto z3_model = _solver.get_model();

    for ( unsigned int i = 0; i < z3_model.size(); ++i )
    {
        auto val = z3_model.get_const_interp( z3_model[i] );
        auto var = z3_model[i].name().str();
        if ( val.is_bv() ) {
            model[var] = val.get_numeral_uint64();
        } else if ( val.is_fpa() ) {
            // TODO parse string to double
            model[var] =  Z3_get_numeral_string( _ctx, val );
        } else {
            UNREACHABLE( "unknown sort" );
        }
    }
    return model;
}

#endif


#if OPT_STP

void STP::pop()
{
    _mgr.Pop();
    clear();
}

void STP::push()
{
    _mgr.Push();
}

void STP::reset()
{
    while ( _mgr.getAssertLevel() )
        _mgr.Pop();
    clear();
}

Result STP::solve()
{
    stp::ASTNode top;
    auto vec = _mgr.GetAsserts();
    switch ( vec.size() )
    {
        case 0: top = _mgr.ASTTrue; break;
        case 1: top = vec[ 0 ]; break;
        default: top = _mgr.CreateNode( stp::AND, vec ); break;
    }
    switch ( _stp.TopLevelSTP( top, _mgr.ASTFalse ) )
    {
        case stp::SOLVER_UNSATISFIABLE: return Result::False;
        case stp::SOLVER_SATISFIABLE: return Result::True;
        default: return Result::Unknown;
    }
}

void STP::clear()
{
    _mgr.ClearAllTables();
    _stp.ClearAllTables();
}

Model STP::model()
{
    Model model;

    auto get_value = [&] ( auto node ) -> uint64_t {
        auto type = node.GetType();
        if ( type == stp::BITVECTOR_TYPE )
        {
            auto val = _ce.GetCounterExample( node );
            assert(val.isConstant());

            auto bv = val.GetBVConst();
            return std::atoi( reinterpret_cast< char * >( CONSTANTBV::BitVector_to_Dec( bv ) ) );
        }

        UNREACHABLE( "unknown smt type" );
    };

    if ( solve() == Result::True )
    {
        auto map = _ce.GetCompleteCounterExample();
        for ( const auto &[term, repr] : map )
        {
            if ( _mgr.FoundIntroducedSymbolSet( term ) )
                continue; // skip introduced symbols
            if ( term.GetKind() == stp::SYMBOL )
                model[ term.GetName() ] = get_value(repr);
        }
    }
    return model;
}

#endif

template struct Simple< SMTLib >;
template struct Caching< SMTLib >;

#if OPT_Z3
template struct Simple< Z3 >;
template struct Incremental< Z3 >;
template struct Caching< Z3 >;
#endif

#if OPT_STP
template struct Simple< STP >;
template struct Incremental< STP >;
template struct Caching< STP >;
#endif

}
