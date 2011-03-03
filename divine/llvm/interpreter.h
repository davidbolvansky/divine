//===-- Interpreter.h ------------------------------------------*- C++ -*--===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This header file defines the interpreter structure
//
//===----------------------------------------------------------------------===//

#ifndef LLI_INTERPRETER_H
#define LLI_INTERPRETER_H

#include "llvm/Function.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/GenericValue.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/DataTypes.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/InstVisitor.h"
#include "llvm/Support/raw_ostream.h"

#define NO_RTTI

#include <divine/llvm/arena.h>

namespace llvm {

class IntrinsicLowering;
struct FunctionInfo;
template<typename T> class generic_gep_type_iterator;
class ConstantExpr;
typedef generic_gep_type_iterator<User::const_op_iterator> gep_type_iterator;

}

namespace divine {
namespace llvm {

using namespace ::llvm;

typedef std::vector<GenericValue> ValuePlaneTy;

template< typename A, typename B >
struct BiMap {
    std::map< A, B > _left;
    std::map< B, A > _right;

    void insert( A a, B b ) {
        std::cerr << "bimap: adding (" << a << ", " << b << ")" << std::endl;
        _left.insert( std::make_pair( a, b ) );
        _right.insert( std::make_pair( b, a ) );
    }

    A left( B b ) {
        assert( _right.count( b ) );
        std::cerr << "bimap: getting (" << _right.find( b )->second << " <- " << b << ")" << std::endl;
        return _right.find( b )->second;
    }

    B right( A a ) {
        assert( _left.count( a ) );
        std::cerr << "bimap: getting (" << a << " -> " << _left.find( a )->second << ")" << std::endl;
        return _left.find( a )->second;
    }
};

struct Location {
    Function             *function; // The currently executing function
    BasicBlock           *block;    // The currently executing BB
    BasicBlock::iterator  insn;     // The next instruction to execute
    bool operator<( Location l ) const {
        if ( function < l.function )
            return true;
        if ( function > l.function )
            return false;
        if ( block < l.block )
            return true;
        if ( block > l.block )
            return false;
        if ( &*insn < &*l.insn )
            return true;
        return false;
    }

    Location( Function *f, BasicBlock *b, BasicBlock::iterator i )
        : function( f ), block( b ), insn( i ) {}
};

std::ostream &operator<<( std::ostream &ostr, Location );

// ExecutionContext struct - This struct represents one stack frame currently
// executing.
//
struct ExecutionContext {
    typedef std::map<int, GenericValue> Values;
    typedef std::vector<Arena::Index> Allocas;
    typedef std::vector<GenericValue> VarArgs;

    int pc;          // program counter
    Values values;   // LLVM values used in this invocation
    VarArgs varArgs; // Values passed through an ellipsis
    CallSite caller; // Holds the call that called subframes.
                     // NULL if main func or debugger invoked fn
    Allocas allocas;

    int size() {
        return sizeof( int ) +
               sizeof( size_t ) * 3 +
               sizeof( GenericValue ) * varArgs.size() +
               sizeof( GenericValue ) * values.size() +
               sizeof( int ) * values.size() +
               sizeof( Arena::Index ) * allocas.size();
    }

    int put( int o, Blob b ) {
        o = b.put( o, pc );
        o = b.put( o, values.size() );
        for ( Values::iterator i = values.begin(); i != values.end(); ++i ) {
            o = b.put( o, i->first );
            o = b.put( o, i->second );
        }
        o = b.put( o, varArgs.size() );
        for ( VarArgs::iterator i = varArgs.begin(); i != varArgs.end(); ++i )
            o = b.put( o, *i );
        o = b.put( o, allocas.size() );
        for ( Allocas::iterator i = allocas.begin(); i != allocas.end(); ++i )
            o = b.put( o, *i );
        return o;
    }

    int get( int o, Blob b ) {
        varArgs.clear();
        values.clear();
        allocas.clear();

        size_t count;
        o = b.get( o, pc );
        o = b.get( o, count );
        for ( int i = 0; i < count; ++i ) {
            int k; GenericValue v;
            o = b.get( o, k );
            o = b.get( o, v );
            values[ k ] = v;
        }
        o = b.get( o, count );
        for ( int i = 0; i < count; ++i ) {
            GenericValue v;
            o = b.get( o, v );
            varArgs.push_back( v );
        }
        o = b.get( o, count );
        for ( int i = 0; i < count; ++i ) {
            Arena::Index v;
            o = b.get( o, v );
            allocas.push_back( v );
        }
        return o;
    }
};

// Interpreter - This class represents the entirety of the interpreter.
//
class Interpreter : public ::llvm::ExecutionEngine, public ::llvm::InstVisitor<Interpreter> {
    GenericValue ExitValue;          // The return value of the called function
    TargetData TD;
    IntrinsicLowering *IL;

    Arena arena;
    BiMap< int, Location > locationIndex;
    BiMap< int, Value * > valueIndex;

    // The runtime stack of executing code.  The top of the stack is the current
    // function record.
    std::vector<ExecutionContext> stack;

    void leave() {
        for ( std::vector< Arena::Index >::iterator i = SF().allocas.begin();
              i != SF().allocas.end(); ++i )
            arena.free( *i );
        // arena.free( stack.back() );
        stack.pop_back();
    }

    ExecutionContext &enter() {
        stack.push_back( ExecutionContext() );
        return SF();
    }

    ExecutionContext &SF() {
        return stack.back(); // *(ExecutionContext *) arena.translate( stack.back() );
    }

    ExecutionContext &SFat( int i ) {
        return stack[ i ]; // *(ExecutionContext *) arena.translate( stack[ i ] );
    }

  // AtExitHandlers - List of functions to call when the program exits,
  // registered with the atexit() library function.
  std::vector<Function*> AtExitHandlers;
  void SetValue(Value *V, GenericValue Val, ExecutionContext &SF);

public:

    Blob snapshot( int extra, Pool &p ) {
        int need = 4;
        for ( int i = 0; i < stack.size(); ++i )
            need += SFat( i ).size();

        Blob b = arena.compact( extra + need, p );

        int offset = extra;
        offset = b.put( offset, stack.size() );

        for ( int i = 0; i < stack.size(); ++i )
            offset = SFat( i ).put( offset, b );

        // std::cerr << "snapshotted LLVM: stack at " << extra << ", arena at " << offset << ", total " << b.size() << std::endl;
        return b;
    }

    void restore( Blob b, int extra ) {
        int depth;
        int offset = b.get( extra, depth );
        stack.resize( depth );
        for ( int i = 0; i < depth; ++i )
            offset = stack[ i ].get( offset, b );
        std::cerr << "expanding LLVM: stack at " << extra << ", arena at " << offset << ", total " << b.size() << std::endl;
        arena.expand( b, offset );
    }

    void buildIndex( Module *m );

    explicit Interpreter(Module *M);
    ~Interpreter();

  /// runAtExitHandlers - Run any functions registered by the program's calls to
  /// atexit(3), which we intercept and store in AtExitHandlers.
  ///
  void runAtExitHandlers();

  /// create - Create an interpreter ExecutionEngine. This can never fail.
  ///
  static ExecutionEngine *create(Module *M, std::string *ErrorStr = 0);

  /// run - Start execution with the specified function and arguments.
  ///
  virtual GenericValue runFunction(Function *F,
                                   const std::vector<GenericValue> &ArgValues);

  /// recompileAndRelinkFunction - For the interpreter, functions are always
  /// up-to-date.
  ///
  virtual void *recompileAndRelinkFunction(Function *F) {
    return getPointerToFunction(F);
  }

  /// freeMachineCodeForFunction - The interpreter does not generate any code.
  ///
  void freeMachineCodeForFunction(Function *F) { }

  // Methods used to execute code:
  // Place a call on the stack
  void callFunction(Function *F, const std::vector<GenericValue> &ArgVals);
  void run();                // Execute instructions until nothing left to do
  void step();               // Execute the next instruction
  bool done();               // Is there anything left to do?

    Location location( ExecutionContext & );
    void setLocation( ExecutionContext &, Location );
    void setInstruction( ExecutionContext &, BasicBlock::iterator );
    Instruction &nextInstruction();

  // Opcode Implementations
  void visitReturnInst(ReturnInst &I);
  void visitBranchInst(BranchInst &I);
  void visitSwitchInst(SwitchInst &I);
  void visitIndirectBrInst(IndirectBrInst &I);

  void visitBinaryOperator(BinaryOperator &I);
  void visitICmpInst(ICmpInst &I);
  void visitFCmpInst(FCmpInst &I);
  void visitAllocaInst(AllocaInst &I);
  void visitLoadInst(LoadInst &I);
  void visitStoreInst(StoreInst &I);
  void visitGetElementPtrInst(GetElementPtrInst &I);
  void visitPHINode(PHINode &PN) { 
    llvm_unreachable("PHI nodes already handled!"); 
  }
  void visitTruncInst(TruncInst &I);
  void visitZExtInst(ZExtInst &I);
  void visitSExtInst(SExtInst &I);
  void visitFPTruncInst(FPTruncInst &I);
  void visitFPExtInst(FPExtInst &I);
  void visitUIToFPInst(UIToFPInst &I);
  void visitSIToFPInst(SIToFPInst &I);
  void visitFPToUIInst(FPToUIInst &I);
  void visitFPToSIInst(FPToSIInst &I);
  void visitPtrToIntInst(PtrToIntInst &I);
  void visitIntToPtrInst(IntToPtrInst &I);
  void visitBitCastInst(BitCastInst &I);
  void visitSelectInst(SelectInst &I);


  void visitCallSite(CallSite CS);
  void visitCallInst(CallInst &I) { visitCallSite (CallSite (&I)); }
  void visitInvokeInst(InvokeInst &I) { visitCallSite (CallSite (&I)); }
  void visitUnwindInst(UnwindInst &I);
  void visitUnreachableInst(UnreachableInst &I);

  void visitShl(BinaryOperator &I);
  void visitLShr(BinaryOperator &I);
  void visitAShr(BinaryOperator &I);

  void visitVAArgInst(VAArgInst &I);
  void visitInstruction(Instruction &I) {
    errs() << I;
    llvm_unreachable("Instruction not interpretable yet!");
  }

    // GenericValue callExternalFunction(Function *F,
    //                                 const std::vector<GenericValue> &ArgVals);
  void exitCalled(GenericValue GV);

  void addAtExitHandler(Function *F) {
    AtExitHandlers.push_back(F);
  }

  GenericValue *getFirstVarArg () {
      return &(SF().varArgs[0]);
  }

private:  // Helper functions
  GenericValue executeGEPOperation(Value *Ptr, gep_type_iterator I,
                                   gep_type_iterator E, ExecutionContext &SF);

  // SwitchToNewBasicBlock - Start execution in a new basic block and run any
  // PHI nodes in the top of the block.  This is used for intraprocedural
  // control flow.
  //
  void SwitchToNewBasicBlock(BasicBlock *Dest, ExecutionContext &SF);

  void *getPointerToFunction(Function *F) { return (void*)F; }
  void *getPointerToBasicBlock(BasicBlock *BB) { return (void*)BB; }

  void initializeExecutionEngine() { }
    // void initializeExternalFunctions();
  GenericValue getConstantExprValue(ConstantExpr *CE, ExecutionContext &SF);
  GenericValue getOperandValue(Value *V, ExecutionContext &SF);
  GenericValue executeTruncInst(Value *SrcVal, const Type *DstTy,
                                ExecutionContext &SF);
  GenericValue executeSExtInst(Value *SrcVal, const Type *DstTy,
                               ExecutionContext &SF);
  GenericValue executeZExtInst(Value *SrcVal, const Type *DstTy,
                               ExecutionContext &SF);
  GenericValue executeFPTruncInst(Value *SrcVal, const Type *DstTy,
                                  ExecutionContext &SF);
  GenericValue executeFPExtInst(Value *SrcVal, const Type *DstTy,
                                ExecutionContext &SF);
  GenericValue executeFPToUIInst(Value *SrcVal, const Type *DstTy,
                                 ExecutionContext &SF);
  GenericValue executeFPToSIInst(Value *SrcVal, const Type *DstTy,
                                 ExecutionContext &SF);
  GenericValue executeUIToFPInst(Value *SrcVal, const Type *DstTy,
                                 ExecutionContext &SF);
  GenericValue executeSIToFPInst(Value *SrcVal, const Type *DstTy,
                                 ExecutionContext &SF);
  GenericValue executePtrToIntInst(Value *SrcVal, const Type *DstTy,
                                   ExecutionContext &SF);
  GenericValue executeIntToPtrInst(Value *SrcVal, const Type *DstTy,
                                   ExecutionContext &SF);
  GenericValue executeBitCastInst(Value *SrcVal, const Type *DstTy,
                                  ExecutionContext &SF);
  GenericValue executeCastOperation(Instruction::CastOps opcode, Value *SrcVal, 
                                    const Type *Ty, ExecutionContext &SF);
  void popStackAndReturnValueToCaller(const Type *RetTy, GenericValue Result);

};

}
}

#endif
