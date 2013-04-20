// -*- C++ -*- (c) 2012 Petr Rockai <me@mornfall.net>

#define NO_RTTI

#include <wibble/exception.h>

#include <divine/llvm/program.h>

#include <llvm/Type.h>
#include <llvm/GlobalVariable.h>
#include <llvm/CodeGen/IntrinsicLowering.h>
#include <llvm/Support/CallSite.h>
#include <llvm/Constants.h>
#include <llvm/Module.h>
#include <llvm/ADT/StringMap.h>

using namespace divine::llvm;
using ::llvm::isa;
using ::llvm::dyn_cast;
using ::llvm::cast;

static bool isCodePointer( ::llvm::Value *val )
{
    if ( auto ty = dyn_cast< ::llvm::PointerType >( val->getType() ) )
        return ty->getElementType()->isFunctionTy();

    return isa< ::llvm::Function >( val ) ||
           isa< ::llvm::BlockAddress >( val ) ||
           isa< ::llvm::BasicBlock >( val );
}

void ProgramInfo::initValue( ::llvm::Value *val, ProgramInfo::Value &result )
{
    if ( val->getType()->isVoidTy() ) {
        result.width = 0;
        result.type = Value::Void;
    } else if ( isCodePointer( val ) ) {
        result.width = TD.getTypeAllocSize( val->getType() );
        result.type = Value::CodePointer;
    } else if ( val->getType()->isPointerTy() ) {
        result.width = TD.getTypeAllocSize( val->getType() );
        result.type = Value::Pointer;
    } else {
        result.width = TD.getTypeAllocSize( val->getType() );
        if ( val->getType()->isIntegerTy() )
            result.type = Value::Integer;
        else if ( val->getType()->isFloatTy() || val->getType()->isDoubleTy() )
            result.type = Value::Float;
        else
            result.type = Value::Aggregate;
    }

    if ( auto CDS = dyn_cast< ::llvm::ConstantDataSequential >( val ) ) {
        result.type = Value::Aggregate;
        result.width = CDS->getNumElements() * CDS->getElementByteSize();
    }
}

ProgramInfo::Value ProgramInfo::insert( int function, ::llvm::Value *val )
{
    if ( valuemap.find( val ) != valuemap.end() )
        return valuemap.find( val )->second;

    makeFit( functions, function );

    Value result; /* not seen yet, needs to be allocated */
    initValue( val, result );

    if ( result.width % framealign )
        return Value(); /* ignore for now, later pass will assign this one */

    if ( auto B = dyn_cast< ::llvm::BasicBlock >( val ) )
        makeConstant( result, blockmap[ B ] );
    else if ( auto B = dyn_cast< ::llvm::BlockAddress >( val ) )
        makeConstant( result, blockmap[ B->getBasicBlock() ] );
    else if ( auto F = dyn_cast< ::llvm::Function >( val ) )
        makeConstant( result, PC( functionmap[ F ], 0, 0 ) );
    else if ( auto C = dyn_cast< ::llvm::Constant >( val ) ) {
        result.global = true;
        if ( auto G = dyn_cast< ::llvm::GlobalVariable >( val ) ) {
            Value pointee;
            if ( !G->hasInitializer() )
                throw wibble::exception::Consistency(
                    "ProgramInfo::insert",
                    std::string( "Unresolved symbol (global variable): " ) + G->getValueName()->getKey().str() );
            assert( G->hasInitializer() );
            initValue( G->getInitializer(), pointee );
            if ( (pointee.constant = G->isConstant()) )
                makeLLVMConstant( pointee, G->getInitializer() );
            else
                allocateValue( 0, pointee );
            globals.push_back( pointee );
            Pointer p( false, globals.size() - 1, 0 );
            if ( G->hasInitializer() ) {
                ( G->isConstant() ? constinfo[ p ] : globalinfo[ p ] )
                    = std::make_pair( G->getInitializer()->getType(),
                                      G->getValueName()->getKey() );
            }
            makeConstant( result, p );
        } else makeLLVMConstant( result, C );
    } else allocateValue( function, result );

    if ( function && !result.global && !result.constant ) {
        if ( result.width )
            this->functions[ function ].values.push_back( result );
    } else
        globals.push_back( result );

    valuemap.insert( std::make_pair( val, result ) );
    return result;
}

/* This is silly. */
ProgramInfo::Position ProgramInfo::lower( Position p )
{
    auto BB = p.I->getParent();
    bool first = p.I == BB->begin();
    auto insert = p.I;

    if ( !first ) --insert;
    IL->LowerIntrinsicCall( cast< ::llvm::CallInst >( p.I ) );
    if ( first )
        insert = BB->begin();
    else
        insert ++;

    return Position( p.pc, insert );
}

void ProgramInfo::builtin( Position p )
{
    ProgramInfo::Instruction &insn = instruction( p.pc );
    ::llvm::CallSite CS( p.I );
    ::llvm::Function *F = CS.getCalledFunction();
    std::string name = F->getName().str();
    if ( name == "__divine_interrupt_mask" )
        insn.builtin = BuiltinMask;
    else if ( name == "__divine_interrupt_unmask" )
        insn.builtin = BuiltinUnmask;
    else if ( name == "__divine_interrupt" )
        insn.builtin = BuiltinInterrupt;
    else if ( name == "__divine_get_tid" )
        insn.builtin = BuiltinGetTID;
    else if ( name == "__divine_new_thread" )
        insn.builtin = BuiltinNewThread;
    else if ( name == "__divine_choice" )
        insn.builtin = BuiltinChoice;
    else if ( name == "__divine_assert" )
        insn.builtin = BuiltinAssert;
    else if ( name == "__divine_ap" )
        insn.builtin = BuiltinAp;
    else if ( name == "__divine_malloc" )
        insn.builtin = BuiltinMalloc;
    else if ( name == "__divine_free" )
        insn.builtin = BuiltinFree;
    else if ( name == "memcpy" )
        insn.builtin = BuiltinMemcpy;
    else throw wibble::exception::Consistency(
        "ProgramInfo::builtin",
        "Can't call an undefined function <" + name + ">" );
}

template< typename Insn >
void ProgramInfo::insertIndices( Position p )
{
    Insn *I = cast< Insn >( p.I );
    ProgramInfo::Instruction &insn = instruction( p.pc );

    int shift = insn.values.size();
    insn.values.resize( shift + I->getNumIndices() );

    for ( unsigned i = 0; i < I->getNumIndices(); ++i ) {
        Value v;
        v.width = sizeof( unsigned );
        makeConstant( v, I->getIndices()[ i ] );
        insn.values[ shift + i ] = v;
    }
}

ProgramInfo::Position ProgramInfo::insert( Position p )
{
    makeFit( functions, p.pc.function );
    makeFit( function( p.pc ).blocks, p.pc.block );
    makeFit( function( p.pc ).block( p.pc ).instructions, p.pc.instruction );
    ProgramInfo::Instruction &insn = instruction( p.pc );

    if ( !block( p.pc ).bb )
        block( p.pc ).bb = p.I->getParent();

    if ( p.I == block( p.pc ).bb->end() )
        return p; /* nowhere further to go */

    insn.opcode = p.I->getOpcode();
    insn.op = &*p.I;

    if ( dyn_cast< ::llvm::CallInst >( p.I ) ||
         dyn_cast< ::llvm::InvokeInst >( p.I ) )
    {
        ::llvm::CallSite CS( p.I );
        ::llvm::Function *F = CS.getCalledFunction();
        if ( F && F->isDeclaration() )
            switch ( F->getIntrinsicID() ) {
                case ::llvm::Intrinsic::not_intrinsic: builtin( p ); break;
                case ::llvm::Intrinsic::trap:
                case ::llvm::Intrinsic::vastart:
                case ::llvm::Intrinsic::vacopy:
                case ::llvm::Intrinsic::vaend: break;
                case ::llvm::Intrinsic::dbg_declare:
                case ::llvm::Intrinsic::dbg_value: p.I++; return p;
                default: return lower( p );
            }
    }

    insn.values.resize( 1 + p.I->getNumOperands() );
    for ( int i = 0; i < int( p.I->getNumOperands() ); ++i ) {
        ::llvm::Value *v = p.I->getOperand( i );
        insert( p.pc.function, v ); /* use-before-def can actually happen */
        if ( valuemap.count( v ) )
            insn.values[ i + 1 ] = valuemap[ v ];
    }

    if ( isa< ::llvm::ExtractValueInst >( p.I ) )
        insertIndices< ::llvm::ExtractValueInst >( p );

    pcmap.insert( std::make_pair( p.I, p.pc ) );
    insn.result() = insert( p.pc.function, &*p.I );

    p.pc.instruction ++; p.I ++; /* next please */
    return p;
}

void ProgramInfo::build()
{
    /* null pointers are heap = 0, segment = 0, where segment is an index into
     * the "globals" vector */
    Value nullpage;
    nullpage.offset = 0;
    nullpage.width = 0;
    nullpage.global = true;
    nullpage.constant = false;
    globals.push_back( nullpage );

    framealign = 1;

    for ( auto var = module->global_begin(); var != module->global_end(); ++ var )
        insert( 0, &*var );

    codepointers = true;
    pass();
    codepointers = false;

    framealign = 4;
    pass();

    framealign = 1;
    pass();
}

void ProgramInfo::pass()
{
    PC pc( 1, 0, 0 );
    int _framealign = framealign;

    for ( auto function = module->begin(); function != module->end(); ++ function )
    {
        if ( function->isDeclaration() )
            continue; /* skip */
        ++ pc.function;

        if ( function->begin() == function->end() )
            throw wibble::exception::Consistency(
                "ProgramInfo::build",
                "Can't deal with empty functions." );

        makeFit( functions, pc.function );
        functionmap[ function ] = pc.function;
        pc.block = 0;

        if ( !codepointers ) {
            framealign = 1; /* force all args to go in in the first pass */

            /* TODO: va_args; implement as a Pointer */
            for ( auto arg = function->arg_begin(); arg != function->arg_end(); ++ arg ) {
                insert( pc.function, &*arg );
            }

            framealign = _framealign;

            this->function( pc ).datasize =
                align( this->function( pc ).datasize, framealign );
        }

        int blockid = 0;
        for ( auto block = function->begin(); block != function->end(); ++block, ++blockid )
            blockmap[ &*block ] = PC( pc.function, blockid, 0 );

        if ( codepointers )
            continue;

        for ( auto block = function->begin(); block != function->end();
              ++ block, ++ pc.block )
        {
            if ( block->begin() == block->end() )
                throw wibble::exception::Consistency(
                    "ProgramInfo::build",
                    "Can't deal with an empty BasicBlock" );

            pc.instruction = 0;
            ProgramInfo::Position p( pc, block->begin() );
            while ( p.I != block->end() )
                p = insert( p );
            p = insert( p ); // end of block
        }
    }

    globalsize = align( globalsize, 4 );
}

