// -*- mode: C++; indent-tabs-mode: nil; c-basic-offset: 4 -*-

/*
 * (c) 2016 Petr Ročkai <code@fixp.eu>
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

#include <divine/vm/explore.hpp>
#include <divine/vm/bitcode.hpp>
#include <divine/vm/debug.hpp>
#include <divine/ss/search.hpp>
#include <divine/ui/cli.hpp>

namespace divine {
namespace ui {

std::string escape( std::string s )
{
    std::string buf;
    buf.resize( s.length() * 2 );
    int i = 0, j = 0;
    while ( i < int( s.length() ) ) {
        char c = s[ i ++ ];
        if ( c == '\\' || c == '\n' || c == '"' )
            buf[ j++ ] = '\\';
        if ( c == '\n' )
            buf[ j++ ] = 'l';
        else
            buf[ j++ ] = c;
    }
    return std::string( buf, 0, j );
}

using DNMap = std::map< vm::DNKey, int >;

template< typename DN >
int dump( bool raw, DN dn, DNMap &dumped, int &seq, std::string prefix )
{
    if ( dn._address.type() != vm::PointerType::Heap )
        return 0;
    if ( dumped.find( dn.sortkey() ) != dumped.end() )
        return dumped[ dn.sortkey() ];
    int hid = ++seq;
    dumped.emplace( dn.sortkey(), hid );

    auto related =
        [&]( std::string k, auto rel )
        {
            if ( int t = dump( raw, rel, dumped, seq, prefix ) )
                std::cout << prefix << hid << " -> "  << prefix << t
                          << " [ label=\"" << k << "\" ]" << std::endl;
        };

    std::function< void( std::string, DN ) > component =
        [&]( std::string ck, auto comp )
        {
            comp.related( [&]( std::string rk, auto rel )
                          { related( ck + "." + rk, rel ); }, false );
            comp.components( [&]( std::string sk, auto scomp )
                             { component( ck + "." + sk, scomp ); } );
        };

    std::stringstream str;
    dn.format( str, 0, false, 0 );
    std::cout << prefix << hid << " [ shape=rectangle label=\"" << escape( str.str() )
              << "\" ]" << std::endl;

    dn.related( related, false );
    dn.components( component );

    return hid;
}

void Draw::run()
{
    vm::Explore ex( bitcode() );
    ex.start();

    vm::DebugContext< vm::Program, vm::CowHeap > dbg( bitcode()->program() );
    vm::setup::boot( dbg );
    vm::Eval< vm::Program, decltype( dbg ), vm::value::Void > dbg_eval( dbg.program(), dbg );
    dbg_eval.run();

    int edgecount = 0, statecount = 0;

    brick::mem::SlavePool< typename vm::CowHeap::SnapPool > ext( ex.pool() );

    int seq = 0;

    std::cout << "digraph { node [ fontname = Courier ]\n";

    ss::search(
        ss::Order::PseudoBFS, ex, 1, ss::passive_listen(
            [&]( auto f, auto t, auto trace )
            {
                ext.materialise( f.snap, sizeof( int ) );
                ext.materialise( t.snap, sizeof( int ) );
                int *f_id = ext.machinePointer< int >( f.snap ),
                    *t_id = ext.machinePointer< int >( t.snap );

                if ( !*t_id )
                    *t_id = ++seq;
                std::cout << *f_id << " -> " << *t_id
                          << " [ label = \"" << escape( brick::string::fmt( trace.first ) ) << "\"]"
                          << std::endl;
                ++statecount;
            },
            [&]( auto st )
            {
                ext.materialise( st.snap, sizeof( int ) );
                int *id = ext.machinePointer< int >( st.snap );
                vm::DebugNode< vm::Program, vm::CowHeap > dn( ex._ctx, st.snap );
                dn.address( vm::DNKind::Object, ex._ctx.get( _VM_CR_State ).pointer );
                dn.type( dbg._state_type );
                dn.di_type( dbg._state_di_type );
                DNMap _dumped;
                int hseq = 0;
                std::cerr << "# new state" << std::endl;
                std::cout << *id << " [ style=filled fillcolor=" << ( st.error ? "red" : "yellow" ) << " ]" << std::endl;
                std::cout << *id << " -> " << *id << ".1 [ label=root ]" << std::endl;
                dump( _raw, dn, _dumped, hseq, brick::string::fmt( *id ) + "." );
                ++edgecount;
            } ) );
    std::cout << "}";
    std::cerr << "found " << statecount << " states and " << edgecount << " edges" << std::endl;
}

}
}
