// -*- C++ -*- (c) 2012 Petr Rockai

#include <wibble/mixin.h>
#include <wibble/test.h>
#include <divine/toolkit/blob.h> // for align

#include <divine/llvm/wrap/Function.h>

#include <llvm/Config/config.h>
#if ( LLVM_VERSION_MAJOR == 3 && LLVM_VERSION_MINOR < 2 )
  #include <llvm/Target/TargetData.h>
#else
  #include <divine/llvm/wrap/DataLayout.h>
  #define TargetData DataLayout
#endif

#include <llvm/CodeGen/IntrinsicLowering.h>

#include <map>

#ifndef DIVINE_LLVM_PROGRAM_H
#define DIVINE_LLVM_PROGRAM_H

namespace llvm {
class IntrinsicLowering;
}

namespace divine {
namespace llvm {

struct MachineState;
struct Pointer;

struct PC : wibble::mixin::Comparable< PC >
{
    uint32_t function:12;
    uint32_t block:10;
    uint32_t instruction:8;
    bool masked:1;
    uint32_t code:1;

    PC( int f, int b, int i )
        : function( f ), block( b ), instruction( i ), masked( false ), code( 1 )
    {}
    PC() : PC( 0, 0, 0 ) {}

    bool operator<= ( PC o ) const {
        /* masked is irrelevant for equality! */
        return std::make_tuple( int( function ), int( block ), int( instruction ) )
            <= std::make_tuple( int( o.function ), int( o.block ), int( o.instruction ) );
    }

    explicit PC( const uint32_t &x ) { *this = *reinterpret_cast< const PC * >( &x ); }
    explicit PC( const Pointer &p ) { *this = *reinterpret_cast< const PC * >( &p ); }
};

/*
 * We use a *non-overlapping* segmented memory scheme, with *variable-sized
 * segments*. Each allocation creates a new segment. Pointers cannot cross
 * segment boundaries through pointer arithmetic or any other manipulation.
 */
struct Pointer : wibble::mixin::Comparable< Pointer >
{
    uint32_t offset:14;// TODO use a bittuple for guaranteed layout; offset
                       // *must* be stored in the lowest 14 bits
    uint32_t segment:16;
    bool heap:1; /* make a (0, 0) pointer different from NULL */
    uint32_t code:1;
    Pointer operator+( int relative ) {
        return Pointer( heap, segment, offset + relative );
    }
    Pointer( bool heap, int segment, int offset )
        : offset( offset ), segment( segment ), heap( heap ), code( 0 )
    {}
    Pointer() : Pointer( false, 0, 0 ) {}
    bool null() { return !heap && !segment && !offset; }

    operator uint32_t() const {
        return *reinterpret_cast< const uint32_t * >( this );
    }

    explicit Pointer( uint32_t x ) {
        union U {
            uint32_t x;
            Pointer p;
            U( uint32_t x ) : x( x ) {}
        } u( x );
        *this = u.p;
    }
    explicit Pointer( const PC &x ) { *this = *reinterpret_cast< const Pointer * >( &x ); }

    bool operator<=( Pointer o ) const {
        return std::make_tuple( int( heap ), int( segment ), int( offset ) )
            <= std::make_tuple( int( o.heap ), int( o.segment ), int( o.offset ) );
    }
};

enum Builtin {
    NotBuiltin = 0,
    BuiltinIntrinsic = 1,
    BuiltinChoice,
    BuiltinMask,
    BuiltinUnmask,
    BuiltinInterrupt,
    BuiltinGetTID,
    BuiltinNewThread,
    BuiltinAssert,
    BuiltinMalloc,
    BuiltinFree,
    BuiltinAp,
    BuiltinMemcpy,
    BuiltinVaStart,
    BuiltinUnwind,
    BuiltinLandingPad
};

struct Choice {
    int options;
    // might be empty or contain probability for each option
    std::vector< int > p;
};

struct ProgramInfo {
    ::llvm::IntrinsicLowering *IL;
    ::llvm::Module *module;
    ::llvm::TargetData TD;

    struct Value {
        enum { Void, Pointer, Integer, Float, Aggregate, CodePointer } type:3;
        uint32_t width:29;
        bool constant:1;
        bool global:1;
        uint32_t offset:30;

        bool operator<( Value v ) const {
            return static_cast< uint32_t >( *this )
                 < static_cast< uint32_t >( v );
        }

        bool pointer() { return type == Pointer; }
        bool integer() { return type == Integer; }
        bool isfloat() { return type == Float; }
        bool aggregate() { return type == Aggregate; }
        bool codePointer() { return type == CodePointer; }

        operator uint32_t() const {
            return *reinterpret_cast< const uint32_t * >( this );
        }

        Value()
            : type( Integer ), width( 0 ), constant( false ), global( false ), offset( 0 )
        {}
    };

    struct Instruction {
        unsigned opcode;
        std::vector< Value > values;
        Value &result() { return values[0]; }
        Value &operand( int i ) { return values[ (i >= 0) ? (i + 1) : (i + values.size()) ]; }
        void dump( ProgramInfo &info, MachineState &state );

        int builtin; /* non-zero if this is a call to a builtin */
        ::llvm::User *op; /* the actual operation; Instruction or ConstantExpr */
        Instruction() : builtin( NotBuiltin ), op( nullptr ) {}
        /* next instruction is in the same BB unless op == NULL */
    };

    struct BB {
        std::vector< Instruction > instructions;
        ::llvm::BasicBlock *bb;
        Instruction &instruction( PC pc ) {
            assert_leq( int( pc.instruction ), int( instructions.size() ) - 1 );
            return instructions[ pc.instruction ];
        }
        BB() : bb( nullptr ) {}
    };

    struct Function {
        int datasize;
        int argcount:31;
        bool vararg:1;
        std::vector< Value > values;
        std::vector< BB > blocks;
        std::vector< Pointer > typeIDs; /* for landing pads */
        int typeID( Pointer p )
        {
            auto found = std::find( typeIDs.begin(), typeIDs.end(), p );
            return found == typeIDs.end() ? 0 : 1 + (found - typeIDs.begin());
        }
        BB &block( PC pc ) {
            assert_leq( int( pc.block ), int( blocks.size() ) - 1 );
            return blocks[ pc.block ];
        }
        Function() : datasize( 0 ) {}
    };

    std::vector< Function > functions;
    std::vector< Value > globals;
    std::vector< std::pair< ::llvm::Type *, std::string > > globalinfo, constinfo;
    std::vector< char > constdata;
    std::vector< char > globaldata; /* initial values! */
    int globalsize, constdatasize;
    int framealign;
    bool codepointers;

    std::map< const ::llvm::Value *, Value > valuemap;
    std::map< const ::llvm::Instruction *, PC > pcmap;

    std::map< const ::llvm::BasicBlock *, PC > blockmap;
    std::map< const ::llvm::Function *, int > functionmap;

    template< typename Container >
    static void makeFit( Container &c, int index ) {
        c.resize( std::max( index + 1, int( c.size() ) ) );
    }

    Instruction &instruction( PC pc ) {
        assert_leq( int( pc.block ), int( function( pc ).blocks.size() ) - 1 );
        return block( pc ).instruction( pc );
    }

    BB &block( PC pc ) {
        assert_leq( int( pc.block ), int( function( pc ).blocks.size() ) - 1 );
        return function( pc ).block( pc );
    }

    Function &function( PC pc ) {
        assert_leq( int( pc.function ), int( functions.size() ) - 1 );
        return functions[ pc.function ];
    }

    template< typename T >
    T &constant( Value v ) {
        return *reinterpret_cast< T * >( &constdata[ v.offset ] );
    }

    char *allocateConstant( Value &result ) {
        result.constant = true;
        result.offset = constdatasize;
        constdatasize += result.width;
        constdata.resize( constdata.size() + result.width, 0 );
        return &constdata[ result.offset ];
    }

    void allocateValue( int fun, Value &result ) {
        result.constant = false;
        if ( fun ) {
            result.global = false;
            result.offset = functions[ fun ].datasize;
            functions[ fun ].datasize += result.width;
        } else {
            result.global = true;
            result.offset = globalsize;
            globalsize += result.width;
            globaldata.resize( globalsize );
        }
    }

    template< typename T >
    void makeConstant( Value &result, T value ) {
        assert_leq( sizeof( T ), result.width );
        allocateConstant( result );
        constant< T >( result ) = value;
    }

    void makeLLVMConstant( Value &result, ::llvm::Constant *c )
    {
        allocateConstant( result );
        /* break loops in initializer dependencies */
        valuemap.insert( std::make_pair( c, result ) );
        storeConstant( result, c );
    }

    bool isCodePointer( ::llvm::Value *val );
    bool isCodePointerConst( ::llvm::Value *val );
    PC getCodePointer( ::llvm::Value *val );

    void storeConstant( Value result, ::llvm::Constant *, bool global = false );

    bool globalPointerInBounds( Pointer p ) {
        assert_leq( int( p.segment ), int( globals.size() ) - 1 );
        return p.offset < globals[ p.segment ].width;
    }

    int globalPointerOffset( Pointer p ) {
        assert_leq( int( p.segment ), int( globals.size() ) - 1 );
        assert( globalPointerInBounds( p ) );
        return globals[ p.segment ].offset + p.offset;
    }

    struct Position {
        PC pc;
        ::llvm::BasicBlock::iterator I;
        Position( PC pc, ::llvm::BasicBlock::iterator I ) : pc( pc ), I( I ) {}
    };

    template< typename Insn > void insertIndices( Position p );
    Position insert( Position );
    Position lower( Position ); // convert intrinsic into normal insns
    Builtin builtin( ::llvm::Function *f );
    void builtin( Position );
    void initValue( ::llvm::Value *val, Value &result );
    Value insert( int function, ::llvm::Value *val );
    void build();
    void pass();

    ProgramInfo( ::llvm::Module *m ) : module( m ), TD( m )
    {
        constdatasize = 0;
        globalsize = 0;
        IL = new ::llvm::IntrinsicLowering( TD );
        build();
    }
};

struct ValueRef {
    ProgramInfo::Value v;
    int frame;
    int tid;
    int offset;
    ValueRef( ProgramInfo::Value v = ProgramInfo::Value(),
              int frame = 0, int tid = -1, int off = 0 )
        : v( v ), frame( frame ), tid( tid ), offset( off )
    {}
};

struct GlobalContext {
    ProgramInfo &info;
    ::llvm::TargetData &TD;
    bool allow_global;

    Pointer malloc( int ) { assert_die(); }
    bool free( Pointer ) { assert_die(); }

    bool isPointer( ValueRef ) { return false; }
    bool isPointer( Pointer ) { return false; }
    void setPointer( ValueRef, bool ) {}
    void setPointer( Pointer, bool ) {}

    /* TODO */
    bool inBounds( ValueRef, int ) { return true; }
    bool inBounds( Pointer, int ) { return true; }

    char *dereference( Pointer p ) {
        if ( !p.heap && allow_global )
            return &info.globaldata[ info.globalPointerOffset( p ) ];
        assert_die();
    }

    char *dereference( ValueRef v ) {
        if( v.v.constant )
            return &info.constdata[ v.v.offset + v.offset ];
        else if ( v.v.global && allow_global )
            return &info.globaldata[ v.v.offset + v.offset ];
        else
            assert_unreachable( "dereferencing invalid value in GlobalContext" );
    }

    GlobalContext( ProgramInfo &i, ::llvm::TargetData &TD, bool global )
        : info( i ), TD( TD ), allow_global( global )
    {}
};

std::ostream &operator<<( std::ostream &o, PC p );
std::ostream &operator<<( std::ostream &o, Pointer p );
std::ostream &operator<<( std::ostream &o, ProgramInfo::Value p );
std::ostream &operator<<( std::ostream &o, ValueRef p );

}
}

#endif
