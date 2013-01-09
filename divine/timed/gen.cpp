#include "gen.h"
#include <string>
#include <algorithm>
#include <stdexcept>
#include <sstream>
#include <limits>

void TAGen::EdgeInfo::assignSubst( const EdgeInfo& ei, const UTAP::symbol_t& sym, const UTAP::expression_t& expr ) {
    guard = ei.guard.subst( sym, expr );
    assign = ei.assign.subst( sym, expr );
    sync = ei.sync.subst( sym, expr );
    syncType = ei.syncType;
    dstId = ei.dstId;
    procId = ei.procId;
}

void TAGen::processEdge( int procId, const UTAP::edge_t& e, std::vector< EdgeInfo >& out ) {
    EdgeInfo einf;
    einf.guard = e.guard;
    einf.assign = e.assign;
    if ( !e.sync.empty() ) {
        einf.syncType = e.sync.getSync();
        einf.sync = e.sync[ 0 ];    // e.sync is SYNC expression with single subexpression evaluating to a channel
    } else {
        einf.syncType = -1;
        einf.sync = UTAP::expression_t();
    }
    einf.dstId = e.dst->locNr;
    einf.procId = procId;

    out.push_back( einf );
    int pushed = 1;
    // for select edges, make one copy for each possible combination of the select variables
    for ( uint32_t v = 0; v < e.select.getSize(); ++v ) {
        auto r = eval.evalRange( procId, e.select[ v ].getType() );
        int base = out.size() - pushed;
        out.resize( base + pushed * ( r.second - r.first + 1 ) );
        // copy every edge we already pushed to _out_ for every possible assignment to this variable
        for ( int i = 0; i < pushed; ++i ) {
            for ( int cur = r.second; cur >= r.first; --cur ) {
                out[ base + i + (cur - r.first) * pushed ].assignSubst(
                    out[ base + i ], e.select[ v ], UTAP::expression_t::createConstant( cur ) );
            }
        }
        pushed = out.size() - base;
    }
}

void TAGen::processInstance( const UTAP::instance_t& inst, std::vector< UTAP::instance_t >& out ) {
    out.push_back( inst );
    int pushed = 1;
    // for partial instances, make one copy for each possible combination of unbound parameters
    for ( uint32_t v = 0; v < inst.unbound; ++v ) {
        // unbound parameters are listed first in the _parameters_ array
        auto r = eval.evalRange( -1, inst.parameters[ v ].getType() );
        int base = out.size() - pushed;
        out.resize( base + pushed * ( r.second - r.first + 1 ) );
        // copy every instance we already pushed to _out_ for every possible assignment to this parameter
        for ( int i = 0; i < pushed; ++i ) {
            for ( int cur = r.second; cur >= r.first; --cur ) {
                unsigned int index = base + i + (cur - r.first) * pushed;
                out[ index ] = out[ base + i ];
                out[ index ].mapping[ inst.parameters[ v ] ] = UTAP::expression_t::createConstant( cur );
            }
        }
        pushed = out.size() - base;
    }
}

bool TAGen::evalInv() {
    int nInst = 0;
    for ( auto proc = states.begin(); proc != states.end(); ++proc, ++nInst ) {
        StateInfo& s = (*proc)[ locs.get( nInst ) ];
        if ( !eval.evalBool( nInst, s.inv ) )
            return false;
    }
    return true;
}

void TAGen::listEnabled( char* source, BlockList &bl, EnabledList &einf, bool &urgent ) {
    assert( bl.size() == einf.size() + 1 );

    std::vector< EdgeInfo* > trans; // non-synchronizing transitions and sending ends of synchronizations
    std::map< chan_id, std::vector< EdgeInfo* > > sync; // receiving ends
    bool inUrgent = false;
    std::set< int > commit;   // set of processes in a commited location

    setData( source );
    // find possible transitions and synchronizations
    int nInst = 0;
    for ( auto proc = states.begin(); proc != states.end(); ++proc, ++nInst ) {
        StateInfo& s = (*proc)[ locs.get( nInst ) ];
        inUrgent = inUrgent || s.urgent;
        if ( s.commit )
            commit.insert( nInst );
        for ( auto tr = s.edges.begin(); tr != s.edges.end(); ++tr ) {
            if ( tr->syncType == UTAP::Constants::SYNC_QUE ) {
                assert( !tr->sync.empty() );
                try {
                    chan_id chan = eval.evalChan( nInst, tr->sync );
                    sync[ chan ].push_back( &*tr );
                } catch ( EvalError& ) {
                    // invalid receiving end is not an error, just ignore it
                }
            } else {
                trans.push_back( &*tr );
            }
        }
    }

    for ( auto itr = trans.begin(); itr != trans.end(); ++itr ) {
        try {
            newSucc( bl.back(), source );
            if ( !evalGuard( *itr ) ) continue;

            if ( (*itr)->syncType == UTAP::Constants::SYNC_BANG ) {
                assert( !(*itr)->sync.empty() );
                chan_id chan = eval.evalChan( (*itr)->procId, (*itr)->sync );

                if ( eval.isChanBcast( chan ) ) {
                    // n-ary synchronization
                    bool fromCommit = commit.empty() || commit.count( (*itr)->procId );
                    std::vector< std::vector< EdgeInfo* > > receivers;  // enabled receiving edges for each process
                    int lastPID = -1;
                    for ( auto recv = sync[ chan ].begin(); recv != sync[ chan ].end(); ++recv ) {
                        if ( (*itr)->procId == (*recv)->procId ) continue;  // prevent synchronization with itself
                        assert( (*recv)->assign.getType().isIntegral() );
                        if ( !evalGuard( *recv ) ) continue;    // this does not change the state, because broadcast guards can not contain clocks
                        if ( (*recv)->procId != lastPID ) { // edges in _sync_ are sorted by process id
                            receivers.push_back( std::vector< EdgeInfo* >() );
                            lastPID = (*recv)->procId;
                            fromCommit = fromCommit || commit.count( (*recv)->procId );
                        }
                        receivers.back().push_back( *recv );
                    }
                    if ( !fromCommit ) continue;    // skip if system is in commited state, but no participant is in commited location

                    // at this point, the transition is considered to be enabled
                    std::vector< unsigned int > sel( receivers.size() );    // combination of edges from _receivers_
                    do {
                        inUrgent = inUrgent || eval.isChanUrgent( chan );
                        einf.emplace_back( *itr, eval.getChanPriority( chan ), edgePrio( *itr ) );
                        for ( unsigned int i = 0; i < sel.size(); i++ ) {
                            const EdgeInfo *edge = receivers[ i ][ sel[ i ] ];
                            einf.back().addEdge( edge, edgePrio( edge ) );
                        }
                        bl.duplicate_back();
                    } while ( nextSelection( sel, receivers ) );
                } else {
                    // binary synchronization
                    for ( auto recv = sync[ chan ].begin(); recv != sync[ chan ].end(); ++recv ) {
                        if ( (*itr)->procId == (*recv)->procId ) continue;  // prevent synchronization with itself
                        newSucc( bl.back(), source );
                        evalGuard( *itr );  // already evaluated earlier, needed here to properly constrain zone
                        if ( !evalGuard( *recv ) ) continue;
                        // if in commited state, at least one synchronizing process has to be in commited location
                        if ( !commit.empty() && !commit.count( (*itr)->procId ) && !commit.count( (*recv)->procId ) ) continue;
                        // at this point, the transition is considered to be enabled
                        inUrgent = inUrgent || eval.isChanUrgent( chan );
                        einf.emplace_back( *itr, eval.getChanPriority( chan ), edgePrio( *itr ) );
                        einf.back().addEdge( *recv, edgePrio( *recv ) );
                        bl.push_back();
                    }
                }
            } else {
                // no synchronization
                if ( !commit.empty() && !commit.count( (*itr)->procId ) ) continue;
                // at this point, the transition is considered to be enabled
                einf.emplace_back( *itr, sys.getTauPriority(), edgePrio( *itr ) );
                bl.push_back();
            }
        } catch ( EvalError& e ) {
            einf.emplace_back( *itr, sys.getTauPriority(), edgePrio( *itr ) );
            makeErrState( bl.back(), e.getErr() );
            bl.push_back();
        }
        assert( bl.size() == einf.size() + 1 );
    }

    urgent = inUrgent || !commit.empty();
}

void TAGen::read( const std::string& path ) {
    // clear internal containers
    states.clear();
    procs.clear();
    cutClocks.clear();
    sys.~TimedAutomataSystem(); // this is the only functional way to reset TimedAutomataSystem
    new (&sys) UTAP::TimedAutomataSystem;
    eval = Evaluator();

    // read model
    parseXMLFile( path.c_str(), &sys, true );
    if ( sys.hasErrors() ) {
        std::cerr << "Errors in the input file:" << std::endl;
        for ( auto err = sys.getErrors().begin(); err != sys.getErrors().end(); ++err )
            std::cerr << *err << std::endl;
        throw std::runtime_error( "Error reading input model." );
    }

    std::vector< UTAP::instance_t > instances;
    // initialize evaluator
    try {
        eval.processDeclGlobals( sys );

        for ( auto inst = sys.getProcesses().begin(); inst != sys.getProcesses().end(); ++inst ) {
            processInstance( *inst, instances );
        }

        eval.processDecl( instances );
    } catch ( EvalError& e ) {
        throw std::runtime_error( std::string( "Error when processing declarations: " ) + e.what() );
    }

    // fill internal structures
    int nInst = 0;
    for ( auto inst = instances.begin(); inst != instances.end(); ++inst, ++nInst ) {
        UTAP::template_t *tmp = inst->templ;
        ProcessInfo pi;
        pi.prio = sys.getProcPriority( inst->uid.getName().c_str() );
        pi.initial = ( static_cast< UTAP::state_t* >( tmp->init.getData() ) )->locNr;
        procs.push_back( pi );
        states.push_back( std::vector< StateInfo >( tmp->states.size() ) );
        for ( auto st = tmp->states.begin(); st != tmp->states.end(); ++st ) {
            assert( st->locNr < states.back().size() );
            StateInfo& stinf = states.back()[ st->locNr ];
            UTAP::type_t type = st->uid.getType();
            stinf.urgent = type.is( UTAP::Constants::URGENT );
            stinf.commit = type.is( UTAP::Constants::COMMITTED );
            stinf.inv = st->invariant;
            stinf.name = st->uid.getName();
        }
        for ( auto ed = tmp->edges.begin(); ed != tmp->edges.end(); ++ed ) {
            processEdge( nInst, *ed, states.back()[ ed->src->locNr ].edges );
        }
    }
    propertyId = procs.size();
    // compute required space for locations (including property automaton and error state)
    offVar = Locations::getReqSize( procs.size() + 2 );
    // add required space for variables and clocks
    size = offVar + eval.getReqSize();
}

void TAGen::initial( char* d ) {
    memset( d, 0, stateSize() );
    setData( d );
    for ( auto proc = procs.begin(); proc != procs.end(); ++proc )
        locs.set( proc - procs.begin(), proc->initial );

    eval.initial();
    if ( !evalInv() ) {
        makeErrState( d, EvalError::INVARIANT );
    } else {
        eval.extrapolate();
    }
}

// set _a_ to be (_a_ && _b_)
void addConj( UTAP::expression_t& a, const UTAP::expression_t& b ) {
    if ( a.empty() )
        a = b;
    else
        a = UTAP::expression_t::createBinary( UTAP::Constants::AND, a, b, UTAP::position_t(), b.getType() );
}

bool isClockExpr( const UTAP::expression_t& e ) {
    return (e.getType().isGuard() && !e.getType().isIntegral());
}

bool isDiffExpr( const UTAP::expression_t& e ) {
    assert( isClockExpr( e ) );
    assert( e.getSize() == 2 );
    return e[ 0 ].getType().is( UTAP::Constants::DIFF ) || e[ 1 ].getType().is( UTAP::Constants::DIFF );
}

TAGen::PropGuard TAGen::buildPropGuard( const std::vector< std::pair< bool, std::string > >& clause, const std::map< std::string, std::string >& defs ) {
    PropGuard g;
    for ( auto lit = clause.begin(); lit != clause.end(); ++lit ) {
        auto found = defs.find( lit->second );
        const std::string& strLit = ( found == defs.end() ) ? lit->second : found->second;  // substitute definitions

        UTAP::expression_t tmp = parseExpression( strLit.c_str(), &sys, true );
        if ( tmp.getType().isBoolean() ) {  // predicate on variables
            if ( !lit->first )  // negated literal
                tmp = UTAP::expression_t::createUnary( UTAP::Constants::NOT, tmp, UTAP::position_t(), tmp.getType() );
            addConj( g.expr, tmp );
        } else if ( isClockExpr( tmp ) ) {  // clock comparison
            if ( isDiffExpr( tmp ) ) {  // evaluator manages its own collection of all difference constraints
                eval.setClockLimits( -1, tmp );
            } else {
                if ( addCut( tmp, -1, cutClocks ) ) {   // remember the expression for slicing
                    eval.setClockLimits( -1, cutClocks.back().pos );        // adjust clock limits if necessary
                    eval.setClockLimits( -1, cutClocks.back().neg );
                }
            }
            addConj( g.expr, lit->first ? tmp : negIneq( tmp ) );
        } else {
            throw std::runtime_error( "Unsupported expression type: \"" + tmp.toString() + "\"" );
        }
    }

    if ( sys.hasErrors() ) {
        std::cerr << "Errors in LTL proposition:" << std::endl;
        for ( auto err = sys.getErrors().begin(); err != sys.getErrors().end(); ++err )
            std::cerr << *err << std::endl;
        throw std::runtime_error( "Error reading LTL formula." );
    }
    return g;
}

bool TAGen::evalPropGuard( char* d, const TAGen::PropGuard& g ) {
    setData( d );
    if ( g.expr.empty() )
        return true;
    try {
        return eval.evalBool( -1, g.expr );
    } catch ( EvalError& e ) {
        throw std::runtime_error( std::string( "Error while evaluating property: " ) + e.what() );
    }
}

std::string TAGen::showNode( char* d ) {
    int err = isErrState( d );
    if ( err ) {
        return std::string( "Error:" ) + EvalError::reason( err );
    } else {
        std::stringstream str;
        setData( d );
        for ( unsigned int inst = 0; inst < procs.size(); ++inst )
            str << eval.getProcessName( inst ) << " = " << states[ inst ][ locs.get( inst ) ].name << ", ";
        str << "prop = " << getPropLoc( d ) << "\n";
        str << eval;
        return str.str();
    }
}

void TAGen::makeErrState( char* d, int err ) {
    assert( err != 0 );
    memset( d, 0, stateSize() );
    locs.setSource( d );
    locs.set( propertyId+1, err );
}

int TAGen::isErrState( char* d ) {
    locs.setSource( d );
    return locs.get( propertyId+1 );
}
