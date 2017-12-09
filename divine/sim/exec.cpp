// -*- mode: C++; indent-tabs-mode: nil; c-basic-offset: 4 -*-

/*
 * (c) 2016-2017 Petr Ročkai <code@fixp.eu>
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

#include <divine/sim/cli.hpp>

namespace divine::sim
{

void CLI::run( Stepper &step, bool verbose )
{
    check_running();
    return run( step, verbose ? Stepper::PrintInstructions : Stepper::TraceOnly );
}

void CLI::run( Stepper &step, Stepper::Verbosity verbose )
{
    _sigint = &step._sigint;
    brick::types::Defer _( [](){ _sigint = nullptr; } );

    auto initial = location( _ctx.get( _VM_CR_PC ).pointer );
    if ( !step._breakpoint )
        step._breakpoint = [&]( auto a, auto b ) { return check_bp( initial, a, b ); };

    step.run( _ctx, verbose );
}

Stepper CLI::stepper()
{
    Stepper step;
    step._ff_kernel = !_debug_kernel;
    step._sched_policy = [this]() { sched_policy(); };
    step._yield_state = [this]( auto snap ) { return newstate( snap ); };
    return step;
}

Stepper CLI::stepper( command::WithSteps s, bool jmp )
{
    auto step = stepper();
    check_running();
    if ( jmp )
        step.jumps( 1 );
    if ( s.over || s.out )
        step.frame( get( s.var ).address() );
    return step;
}

void CLI::reach_user()
{
    if ( _debug_kernel )
        return;
    Stepper step;
    step._instructions = std::make_pair( 1, 1 );
    step._ff_kernel = true;
    run( step, false ); /* make 0 (user mode) steps */
}

void CLI::reach_error()
{
    Stepper step;
    step._stop_on_error = true;
    run( step, false );
}

void CLI::bplist( command::Break b )
{
    std::deque< decltype( _bps )::iterator > remove;
    int id = 1;
    if ( _bps.empty() )
        out() << "no breakpoints defined" << std::endl;
    for ( auto bp : _bps )
    {
        out() << std::setw( 2 ) << id << ": ";
        bool del_this = !b.del.empty() && id == b.del;
        bp.match(
            [&]( vm::CodePointer pc )
            {
                auto fun = _bc->debug().function( pc )->getName().str();
                out() << fun << " +" << pc.instruction()
                        << " (at " << dbg::location( location( pc ) ) << ")";
                if ( !b.del.empty() && !pc.instruction() && b.del == fun )
                    del_this = true;
            },
            [&]( Location loc )
            {
                out() << loc.first << ":" << loc.second;
            } );

        if ( del_this )
        {
            remove.push_front( _bps.begin() + id - 1 );
            out() << " [deleted]";
        }
        out() << std::endl;
        ++ id;
    }

    for ( auto r : remove ) /* ordered from right to left */
        _bps.erase( r );
}

Snapshot CLI::newstate( Snapshot snap, bool update_choices, bool terse )
{
    snap = _explore.start( _ctx, snap );
    _explore.pool().sync();
    _ctx.load( snap );

    bool isnew = false;
    std::string name;

    if ( _state_names.count( snap ) )
    {
        name = _state_names[ snap ];
        if ( update_choices )
            update_lock( snap );
    }
    else
    {
        isnew = true;
        name = _state_names[ snap ] = "#" + brick::string::fmt( ++_state_count );
        _state_refs[ snap ] = RefCnt( _ctx._refcnt, snap );
        DN state( _ctx, snap );
        state.address( dbg::DNKind::Object, _ctx.get( _VM_CR_State ).pointer );
        state.type( _ctx._state_type );
        state.di_type( _ctx._state_di_type );
        set( name, state );
    }

    set( "#last", name );

    if ( terse )
        out() << " " << name << std::flush;
    else if ( isnew )
        out() << "# a new program state was stored as " << name << std::endl;
    else if ( _trace.count( snap ) )
        out() << "# program follows the trace at " << name
                << " (the scheduler is locked)"<< std::endl;
    else
        out() << "# program entered state " << name << " (already seen)" << std::endl;

    return snap;
}

void CLI::sched_policy()
{
    auto &proc = _ctx._proc;
    auto &choices = _ctx._lock.choices;

    if ( proc.empty() )
        return;

    std::uniform_int_distribution< int > dist( 0, proc.size() - 1 );
    vm::Choice choice( -1, proc.size() );

    if ( _sched_random )
        choice.taken = dist( _rand );
    else
        for ( auto pi : proc )
            if ( pi.first == _sticky_tid )
                choice.taken = pi.second;

    if ( choice.taken < 0 )
    {
        /* thread is gone, pick a replacement at random */
        int seq = dist( _rand );
        _sticky_tid = proc[ seq ].first;
        choice.taken = proc[ seq ].second;
    }

    if ( _ctx._lock_mode == Context::LockScheduler )
    {
        ASSERT( choices.empty() );
        choices.push_back( choice );
    }

    out() << "# active threads:";
    for ( auto pi : proc )
    {
        bool active = pi.second == choices.front().taken;
        out() << ( active ? " [" : " " )
                    << pi.first.first << ":" << pi.first.second
                    << ( active ? "]" : "" );
    }
    proc.clear();
    out() << std::endl;
}

bool CLI::update_lock( Snapshot snap )
{
    if ( _trace.count( snap ) )
    {
        _ctx._lock = _trace[ snap ];
        _ctx._lock_mode = Context::LockBoth;
        return true;
    }
    else
    {
        _ctx._lock_mode = Context::LockScheduler;
        return false;
    }
}

bool CLI::check_bp( RefLocation initial, vm::CodePointer pc, bool ch )
{
    if ( ch && initial.second )
        if ( location( pc ) != initial )
            initial = std::make_pair( "", 0 );

    auto match_pc = [&]( vm::CodePointer bp_pc )
    {
        if ( pc != bp_pc )
            return false;
        auto name = _bc->debug().function( pc )->getName();
        out() << "# stopped at breakpoint " << name.str()
        << std::endl;
        return true;
    };

    auto match_loc = [&]( Location l )
    {
        RefLocation rl = l;
        if ( initial.second == rl.second && rl.first == initial.first )
            return false;
        auto current = location( pc );
        if ( rl.second != current.second )
            return false;
        if ( !brick::string::endsWith( current.first, l.first ) )
            return false;
        out() << "# stopped at breakpoint "
        << l.first << ":" << l.second << std::endl;
        return true;
    };

    for ( auto bp : _bps )
        if ( bp.match( match_pc, match_loc ) )
            return true;
    return false;
}

}
