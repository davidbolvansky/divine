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

#include <divine/mc/exec.hpp>
#include <divine/mc/bitcode.hpp>
#include <divine/vm/eval.hpp>
#include <divine/vm/setup.hpp>

#include <divine/vm/eval.tpp>
#include <divine/vm/context.tpp>
#include <divine/vm/dbg-stepper.tpp>

namespace divine::mc
{

void Run::run()
{
    using Eval = vm::Eval< RunContext >;
    auto &program = _bc->program();
    RunContext _ctx( program );
    Eval eval( _ctx );

    vm::setup::boot( _ctx );
    _ctx.enable_debug();
    eval.run();
    if ( !(_ctx.get( _VM_CR_Flags ).integer & _VM_CF_Cancel ) )
        ASSERT( !_ctx.get( _VM_CR_State ).pointer.null() );

    while ( !( _ctx.get( _VM_CR_Flags ).integer & _VM_CF_Cancel ) )
    {
        vm::setup::scheduler( _ctx );
        eval.run();
    }
}

}

namespace divine::vm::dbg { template struct Stepper< mc::DbgRunContext >; }
namespace divine::vm      { template struct Eval<    mc::DbgRunContext >; }
