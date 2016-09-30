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

#include <divine/vm/debug.hpp>
#include <divine/vm/print.hpp>
#include <divine/vm/eval.hpp>

namespace divine {
namespace vm {

std::pair< std::string, int > fileline( const llvm::Instruction &insn )
{
    auto loc = insn.getDebugLoc().get();
    if ( loc && loc->getNumOperands() )
        return std::make_pair( loc->getFilename().str(),
                               loc->getLine() );
    auto prog = llvm::getDISubprogram( insn.getParent()->getParent() );
    if ( prog )
        return std::make_pair( prog->getFilename().str(),
                               prog->getScopeLine() );
    return std::make_pair( "", 0 );
}

std::string location( const llvm::Instruction &insn )
{
    auto fl = fileline( insn );
    if ( fl.second )
        return fl.first + ":" + brick::string::fmt( fl.second );
    return "(unknown location)";
}

template< typename Prog, typename Heap >
using DNEval = Eval< Prog, ConstContext< Prog, Heap >, value::Void >;

template< typename Prog, typename Heap >
int DebugNode< Prog, Heap >::size()
{
    int sz = INT_MAX;
    DNEval< Prog, Heap > eval( _ctx.program(), _ctx );
    if ( _type )
        sz = _ctx.program().TD.getTypeAllocSize( _type );
    if ( !_address.null() )
        sz = std::min( sz, eval.ptr2sz( PointerV( _address ) ) - _offset );
    return sz;
}

template< typename Prog, typename Heap >
llvm::DIDerivedType *DebugNode< Prog, Heap >::di_derived( uint64_t tag, llvm::DIType *t )
{
    t = t ?: _di_type;
    if ( !t )
        return nullptr;
    auto derived = llvm::dyn_cast< llvm::DIDerivedType >( t );
    if ( derived && derived->getTag() == tag )
        return derived;
    return nullptr;
}

template< typename Prog, typename Heap >
llvm::DIDerivedType *DebugNode< Prog, Heap >::di_member( llvm::DIType *t )
{
    return di_derived( llvm::dwarf::DW_TAG_member, t );
}

template< typename Prog, typename Heap >
llvm::DIDerivedType *DebugNode< Prog, Heap >::di_pointer( llvm::DIType *t )
{
    return di_derived( llvm::dwarf::DW_TAG_pointer_type, t );
}

template< typename Prog, typename Heap >
llvm::DIType *DebugNode< Prog, Heap >::di_base( llvm::DIType *t )
{
    t = t ?: di_resolve();
    if ( auto deriv = llvm::dyn_cast< llvm::DIDerivedType >( t ) )
        return deriv->getBaseType().resolve( _ctx.program().ditypemap );
    if ( auto comp = llvm::dyn_cast< llvm::DICompositeType >( t ) )
        return comp->getBaseType().resolve(  _ctx.program().ditypemap );
    return nullptr;
}

template< typename Prog, typename Heap >
llvm::DICompositeType *DebugNode< Prog, Heap >::di_composite( uint64_t tag, llvm::DIType *t )
{
    t = t ?: di_resolve();
    if ( t->getTag() == tag )
        return llvm::dyn_cast< llvm::DICompositeType >( t );
    return nullptr;
}

template< typename Prog, typename Heap >
int DebugNode< Prog, Heap >::width()
{
    if ( di_member() )
        return di_member()->getSizeInBits();
    return 8 * size();
}

template< typename Prog, typename Heap >
int DebugNode< Prog, Heap >::bitoffset()
{
    int rv = 0;
    if ( di_member() )
        rv = di_member()->getOffsetInBits() - 8 * _offset;
    ASSERT_LEQ( rv, 8 * size() );
    ASSERT_LEQ( rv + width(), 8 * size() );
    return rv;
}

template< typename Prog, typename Heap >
bool DebugNode< Prog, Heap >::boundcheck( PointerV ptr, int size )
{
    DNEval< Prog, Heap > eval( _ctx.program(), _ctx );
    return eval.boundcheck( []( auto ) { return std::stringstream(); }, ptr, size, false );
}

template< typename Prog, typename Heap >
bool DebugNode< Prog, Heap >::valid()
{
    if ( _address.null() )
        return false;
    if ( _address.type() == PointerType::Heap && !_ctx.heap().valid( _address ) )
        return false;

    DNEval< Prog, Heap > eval( _ctx.program(), _ctx );
    PointerV addr( _address );
    if ( !boundcheck( addr, 1 ) )
        return false;
    if ( !boundcheck( addr, size() ) )
        return false;
    return true;
}

template< typename Prog, typename Heap >
void DebugNode< Prog, Heap >::value( YieldAttr yield )
{
    DNEval< Prog, Heap > eval( _ctx.program(), _ctx );
    PointerV loc( _address + _offset );
    if ( _type && _type->isIntegerTy() )
        eval.template type_dispatch< IsIntegral >(
            _type->getPrimitiveSizeInBits(), Prog::Slot::Integer,
            [&]( auto v )
            {
                auto raw = v.get( loc );
                using V = decltype( raw );
                if ( bitoffset() || width() != size() * 8 )
                {
                    yield( "@raw_value", brick::string::fmt( raw ) );
                    auto val = raw >> value::Int< 32 >( bitoffset() );
                    val = val & V( bitlevel::ones< typename V::Raw >( width() ) );
                    ASSERT_LEQ( bitoffset() + width(), size() * 8 );
                    yield( "@value", brick::string::fmt( val ) );
                }
                else
                    yield( "@value", brick::string::fmt( raw ) );
            } );

    if ( _type && _di_type && ( di_name() == "char*" ||  di_name() == "const char*" ) )
    {
        PointerV str_v;
        auto hloc = eval.ptr2h( PointerV( _address ) ) + _offset;
        _ctx.heap().read( hloc, str_v );
        auto str = eval.ptr2h( str_v );
        if ( _ctx.heap().valid( str ) )
                yield( "@string", "\"" + _ctx.heap().read_string( str ) + "\"" ); /* TODO escape */
    }

    if ( _type && _type->isPointerTy() )
        eval.template type_dispatch< Any >(
            PointerBytes, Prog::Slot::Pointer,
            [&]( auto v ) { yield( "@value", brick::string::fmt( v.get( loc ) ) ); } );

}

template< typename Prog, typename Heap >
std::string DebugNode< Prog, Heap >::di_scopename( llvm::DIScope *scope )
{
    std::string n;
    if ( !scope )
        scope = _di_var->getScope();

    auto parent = scope->getScope().resolve( _ctx.program().ditypemap );

    if ( parent && llvm::isa< llvm::DINamespace >( parent ) )
        n = di_scopename( parent ) + "::";

    if ( auto ns = llvm::dyn_cast< llvm::DINamespace >( scope ) )
        n += ns->getName() == "" ? "<anon>" : ns->getName();
    else if ( auto file = llvm::dyn_cast< llvm::DICompileUnit >( scope ) )
        n += "<static in " + file->getFilename().str() + ">";
    else
        n += scope->getName();

    return n;
}

template< typename Prog, typename Heap >
std::string DebugNode< Prog, Heap >::di_name( llvm::DIType *t )
{
    if ( !t )
        t = _di_type;
    if ( di_member( t ) )
        return di_name( di_base( t ) );
    if ( !di_base( t ) ||
         di_derived( llvm::dwarf::DW_TAG_typedef, t ) ||
         di_composite( llvm::dwarf::DW_TAG_enumeration_type ) )
        return t->getName().str();
    if ( di_pointer( t ) )
        return di_name( di_base( t ) ) + "*";
    if ( di_derived( llvm::dwarf::DW_TAG_reference_type, t ) )
        return di_name( di_base( t ) ) + "&";
    if ( di_derived( llvm::dwarf::DW_TAG_const_type, t ) )
        return "const " + di_name( di_base( t ) );
    if ( di_derived( llvm::dwarf::DW_TAG_restrict_type, t ) )
        return di_name( di_base( t ) ) + " restrict";
    if ( di_derived( llvm::dwarf::DW_TAG_volatile_type, t ) )
        return "volatile " + di_name( di_base( t ) );
    if ( di_composite( llvm::dwarf::DW_TAG_array_type, t ) )
        return di_name( di_base( t ) ) + "[]";
    t->dump();
    UNREACHABLE( "unexpected debuginfo metadata" );
}

template< typename Prog, typename Heap >
void DebugNode< Prog, Heap >::attributes( YieldAttr yield )
{
    DNEval< Prog, Heap > eval( _ctx.program(), _ctx );
    Prog &program = _ctx.program();

    yield( "@address", brick::string::fmt( _address ) + "+" +
           brick::string::fmt( _offset ) );

    if ( _di_type )
        yield( "@type", di_name() );

    if ( !valid() )
        return;

    auto hloc = eval.ptr2h( PointerV( _address ) );
    value( yield );

    yield( "@raw", print::raw( _ctx.heap(), hloc + _offset, size() ) );

    if ( _address.type() == PointerType::Const || _address.type() == PointerType::Global )
        yield( "@slot", brick::string::fmt( eval.ptr2s( _address ) ) );

    if ( _di_var )
    {
        yield( "@scope", di_scopename() );
        yield( "@definition", _di_var->getFilename().str() + ":" +
                              std::to_string( _di_var->getLine() ) );
    }

    if ( _kind == DNKind::Frame )
    {
        yield( "@pc", brick::string::fmt( pc() ) );
        if ( pc().null() || pc().type() != PointerType::Code )
            return;
        auto *insn = &program.instruction( pc() );
        if ( insn->op )
        {
            eval._instruction = insn;
            yield( "@instruction", print::instruction( eval ) );
        }
        if ( !insn->op )
            insn = &program.instruction( pc() + 1 );
        ASSERT( insn->op );
        auto op = llvm::cast< llvm::Instruction >( insn->op );
        yield( "@location", location( *op ) );

        auto sym = op->getParent()->getParent()->getName().str();
        yield( "@symbol", print::demangle( sym ) );
    }
}

template< typename Prog, typename Heap >
void DebugNode< Prog, Heap >::bitcode( std::ostream &out )
{
    ASSERT_EQ( _kind, DNKind::Frame );
    DNEval< Prog, Heap > eval( _ctx.program(), _ctx );
    CodePointer iter = pc();
    iter.instruction( 0 );
    auto &instructions = _ctx.program().function( iter ).instructions;
    for ( auto &i : instructions )
    {
        eval._instruction = &i;
        out << ( iter == CodePointer( pc() ) ? ">>" : "  " );
        if ( i.op )
            out << "  " << print::instruction( eval, 4 ) << std::endl;
        else
        {
            auto iop = llvm::cast< llvm::Instruction >( instructions[ iter.instruction() + 1 ].op );
            out << print::value( eval, iop->getParent() ) << ":" << std::endl;
        }
        iter = iter + 1;
    }
}

template< typename Prog, typename Heap >
void DebugNode< Prog, Heap >::source( std::ostream &out )
{
    ASSERT_EQ( _kind, DNKind::Frame );
    out << print::source( subprogram(), _ctx.program(), pc() );
}

template< typename Prog, typename Heap >
void DebugNode< Prog, Heap >::related( YieldDN yield )
{
    if ( !valid() )
        return;

    DNEval< Prog, Heap > eval( _ctx.program(), _ctx );

    PointerV ptr;
    auto hloc = eval.ptr2h( PointerV( _address ) );
    int hoff = hloc.offset();

    _related_ptrs.clear();
    _related_count.clear();

    if ( _kind == DNKind::Frame )
        framevars( yield );

    if ( _kind == DNKind::Globals )
        globalvars( yield );

    if ( _type && _di_type && _type->isPointerTy() )
    {
        PointerV addr;
        _ctx.heap().read( hloc + _offset, addr );
        _related_ptrs.insert( addr.cooked() );
        auto kind = DNKind::Object;
        if ( di_name() == "_VM_Frame*" )
            kind = DNKind::Frame;
        DebugNode rel( _ctx, _snapshot );
        rel.address( kind, addr.cooked() );
        rel.type( _type->getPointerElementType() );
        rel.di_type( di_base() );
        yield( "@deref", rel );
    }

    if ( _type && _di_type &&
         di_composite( llvm::dwarf::DW_TAG_structure_type ) &&
         _type->isStructTy() )
        struct_fields( hloc, yield );

    if ( _type && _di_type && di_composite( llvm::dwarf::DW_TAG_array_type ) )
        array_elements( yield );

    for ( auto ptroff : _ctx.heap().pointers( hloc, hoff + _offset, size() ) )
    {
        hloc.offset( hoff + _offset + ptroff->offset() );
        if ( ptroff->offset() + ptroff->size() > size() )
            continue;
        _ctx.heap().read( hloc, ptr );
        auto pp = ptr.cooked();
        if ( pp.type() == PointerType::Code || pp.null() )
            continue;
        if ( _related_ptrs.find( pp ) != _related_ptrs.end() )
            continue;
        pp.offset( 0 );
        DebugNode deref( _ctx, _snapshot );
        deref.address( DNKind::Object, pp );
        yield( "@" + brick::string::fmt( ptroff->offset() ), deref );
    }
}

template< typename Prog, typename Heap >
llvm::DIType *DebugNode< Prog, Heap >::di_resolve( llvm::DIType *t )
{
    llvm::DIType *base = t ?: _di_type;
    llvm::DIDerivedType *DT = nullptr;

    while ( true )
        if ( ( DT = llvm::dyn_cast< llvm::DIDerivedType >( base ) ) &&
             ( DT->getTag() == llvm::dwarf::DW_TAG_typedef ||
               DT->getTag() == llvm::dwarf::DW_TAG_member ||
               DT->getTag() == llvm::dwarf::DW_TAG_restrict_type ||
               DT->getTag() == llvm::dwarf::DW_TAG_volatile_type ||
               DT->getTag() == llvm::dwarf::DW_TAG_const_type ) )
            base = DT->getBaseType().resolve( _ctx.program().ditypemap );
        else return base;
}

template< typename Prog, typename Heap >
void DebugNode< Prog, Heap >::struct_fields( HeapPointer hloc, YieldDN yield )
{
    auto CT = llvm::cast< llvm::DICompositeType >( di_resolve() );
    auto ST = llvm::cast< llvm::StructType >( _type );
    auto STE = ST->element_begin();
    auto SLO = _ctx.program().TD.getStructLayout( ST );
    int idx = 0;
    for ( auto subtype : CT->getElements() )
        if ( auto CTE = llvm::dyn_cast< llvm::DIDerivedType >( subtype ) )
        {
            if ( idx + 1 < int( ST->getNumElements() ) &&
                 CTE->getOffsetInBits() >= 8 * SLO->getElementOffset( idx + 1 ) )
                idx ++, STE ++;

            int offset = SLO->getElementOffset( idx );
            if ( (*STE)->isPointerTy() )
            {
                PointerV ptr;
                _ctx.heap().read( hloc + offset, ptr );
                _related_ptrs.insert( ptr.cooked() );
            }

            DebugNode field( _ctx, _snapshot );
            field.address( DNKind::Object, _address );
            field.offset( _offset + offset );
            field.type( *STE );
            field.di_type( CTE );
            yield( CTE->getName().str(), field );
        }
}

template< typename Prog, typename Heap >
void DebugNode< Prog, Heap >::array_elements( YieldDN yield )
{
    auto subtype = _type->getSequentialElementType();
    int size = _ctx.program().TD.getTypeAllocSize( subtype );
    PointerV addr( _address + _offset );

    for ( int idx = 0; boundcheck( addr + idx * size, size ); ++ idx )
    {
        DebugNode elem( _ctx, _snapshot );
        elem.address( DNKind::Object, _address );
        elem.offset( _offset + idx * size );
        elem.type( subtype );
        elem.di_type( di_base() );
        yield( "[" + std::to_string( idx ) + "]", elem );
    }
}

template< typename Prog, typename Heap >
void DebugNode< Prog, Heap >::localvar( YieldDN yield, llvm::DbgDeclareInst *DDI )
{
    DNEval< Prog, Heap > eval( _ctx.program(), _ctx );

    auto divar = DDI->getVariable();
    auto ditype = divar->getType().resolve( _ctx.program().ditypemap );
    auto var = DDI->getAddress();
    auto &vmap = _ctx.program().valuemap;
    if ( vmap.find( var ) == vmap.end() )
        return;

    PointerV ptr;
    _ctx.heap().read( eval.s2ptr( _ctx.program().valuemap[ var ].slot ), ptr );
    _related_ptrs.insert( ptr.cooked() );

    auto type = var->getType()->getPointerElementType();
    auto name = divar->getName().str();

    if ( divar->getScope() != subprogram() )
        name += "$" + brick::string::fmt( ++ _related_count[ name ] );

    DebugNode lvar( _ctx, _snapshot );
    lvar.address( DNKind::Object, ptr.cooked() );
    lvar.type( type );
    lvar.di_type( ditype );
    yield( name, lvar );
}

template< typename Prog, typename Heap >
void DebugNode< Prog, Heap >::localvar( YieldDN yield, llvm::DbgValueInst *DDV )
{
    DNEval< Prog, Heap > eval( _ctx.program(), _ctx );

    auto divar = DDV->getVariable();
    auto var = DDV->getValue();
    auto &vmap = _ctx.program().valuemap;
    if ( vmap.find( var ) == vmap.end() )
        return;

    auto sref = _ctx.program().valuemap[ var ];
    auto ptr = sref.slot.location == Prog::Slot::Local ?
               eval.s2ptr( sref.slot ) :
               _ctx.program().s2ptr( sref );
    PointerV deref;
    if ( boundcheck( PointerV( ptr ), PointerBytes ) )
        _ctx.heap().read( eval.ptr2h( PointerV( ptr ) ), deref );
    if ( deref.pointer() )
        _related_ptrs.insert( deref.cooked() );

    auto type = var->getType();
    auto name = divar->getName().str();

    if ( divar->getScope() != subprogram() )
        name += "$" + brick::string::fmt( ++ _related_count[ name ] );

    DebugNode lvar( _ctx, _snapshot );
    lvar.address( DNKind::Object, ptr );
    lvar.type( type );
    lvar.di_var( divar );
    yield( name, lvar );
}

template< typename Prog, typename Heap >
void DebugNode< Prog, Heap >::framevars( YieldDN yield )
{
    PointerV fr( _address );
    _ctx.heap().skip( fr, PointerBytes );
    _ctx.heap().read( fr.cooked(), fr );
    if ( !fr.cooked().null() )
    {
        _related_ptrs.insert( fr.cooked() );
        DebugNode parent( _ctx, _snapshot );
        parent.address( DNKind::Frame, fr.cooked() );
        yield( "@parent", parent );
    }

    if ( pc().type() != PointerType::Code )
        return;

    auto *insn = &_ctx.program().instruction( pc() );
    if ( !insn->op )
        insn = &_ctx.program().instruction( pc() + 1 );
    auto op = llvm::cast< llvm::Instruction >( insn->op );
    auto F = op->getParent()->getParent();

    for ( auto &BB : *F )
        for ( auto &I : BB )
            if ( auto DDI = llvm::dyn_cast< llvm::DbgDeclareInst >( &I ) )
                localvar( yield, DDI );
            else if ( auto DDV = llvm::dyn_cast< llvm::DbgValueInst >( &I ) )
                localvar( yield, DDV );
}

template< typename Prog, typename Heap >
void DebugNode< Prog, Heap >::globalvars( YieldDN yield )
{
    DNEval< Prog, Heap > eval( _ctx.program(), _ctx );
    llvm::DebugInfoFinder finder;
    finder.processModule( *_ctx.program().module );
    auto &map = _ctx.program().globalmap;
    for ( auto GV : finder.global_variables() )
    {
        auto var = GV->getVariable();
        if ( !map.count( var ) )
            continue;
        auto ptr = _ctx.program().s2ptr( map[ var ] );

        PointerV deref;
        if ( boundcheck( PointerV( ptr ), PointerBytes ) )
            _ctx.heap().read( eval.ptr2h( PointerV( ptr ) ), deref );
        if ( deref.pointer() )
            _related_ptrs.insert( deref.cooked() );

        DebugNode dn( _ctx, _snapshot );
        dn.address( DNKind::Object, ptr );
        dn.di_var( GV );
        dn.type( var->getType()->getPointerElementType() );
        std::string name = GV->getName();
        if ( llvm::isa< llvm::DINamespace >( GV->getScope() ) )
            name = dn.di_scopename() + "::" + name;
        yield( name, dn );
    }
}

static std::string rightpad( std::string s, int i )
{
    while ( int( s.size() ) < i )
        s += ' ';
    return s;
}

template< typename Prog, typename Heap >
void DebugNode< Prog, Heap >::format( std::ostream &out, int depth, bool compact, int indent )
{
    std::string ind( indent, ' ' );
    std::set< std::string > ck{ "@value", "@type", "@location", "@symbol" };

    attributes(
        [&]( std::string k, auto v )
        {
            if ( k == "@raw" || ( compact && ck.count( k ) == 0 ) )
                return;
            out << ind << rightpad( k + ": ", 14 - indent ) << v << std::endl;
        } );

    int col = 0, relrow = 0;

    std::stringstream rels;

    if ( depth > 0 )
        related(
            [&]( std::string n, auto sub )
            {
                std::stringstream str;
                if ( depth > 0 )
                    sub.format( str, depth - 1, true, indent + 4 );
                if ( !str.str().empty() && n != "@parent" && depth > 0 )
                    out << ind << n << ":" << std::endl << str.str();
                else
                {
                    if ( indent + col + n.size() >= 68 )
                    {
                        if ( relrow <= 3 )
                            col = 0, rels << std::endl << ind
                                          << rightpad( "", 13 - indent )
                                          << ( relrow == 3 ? " [...]" : "" );
                        ++ relrow;
                    }
                    if ( relrow <= 3 )
                    {
                        rels << " " << n;
                        col += n.size();
                    }
                }
            } );
    if ( !rels.str().empty() )
        out << rightpad( "related:", 13 - indent ) << rels.str() << std::endl;
}

template< typename Prog, typename Heap >
std::string DebugNode< Prog, Heap >::attribute( std::string key )
{
    std::string res = "-";
    attributes( [&]( auto k, auto v )
                {
                    if ( k == key )
                        res = v;
                } );
    return res;
}

template struct DebugNode< Program, CowHeap >;

}
}
