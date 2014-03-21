// -*- C++ -*- (c) 2014 Petr Rockai

#define NO_RTTI

#include <wibble/parse.h>
#include <wibble/union.h>

#ifndef DIVINE_LLVM_SILK_PARSE_H
#define DIVINE_LLVM_SILK_PARSE_H

namespace divine {

/*
 * A language of predicates over individual program states. Supports mapping
 * and folding over threads, stacks and frames.
 */

namespace silk {

namespace parse {

enum class TI {
    Invalid, Comment, Newline, Application, Identifier, Constant,
    Map, Fold, SubScope, LambdaParen, Bind,
    ParenOpen, ParenClose,
    If, Then, Else,
    Bool_Or, Bool_And, Bool_Not,
    LEq, Lt, GEq, Gt, Eq, NEq,
    Plus, Minus, Mult, Div, Mod, Or, And, Xor, LShift, RShift,
    Semicolon, BlockDef, BlockEnd, BraceOpen, BraceClose
};

const int TI_End = int( TI::BraceClose ) + 1;

struct Token : wibble::Token< TI >
{
    static const TI Comment = TI::Comment;
    static const std::string tokenName[TI_End];

    static const std::string frag[6];

    static const int precedences = 6;

    bool leftassoc() const {
        return true;
    }

    int precedence() const
    {
        if ( id == TI::And || id == TI::Or || id == TI::Xor ||
             id == TI::LShift || id == TI::RShift )
            return 5;

        if ( id == TI::Mult || id == TI::Div || id == TI::Mod )
            return 4;

        if ( id == TI::Plus || id == TI::Minus )
            return 3;

        if ( id == TI::Eq || id == TI::NEq || id == TI::LEq ||
             id == TI::Lt || id == TI::Gt || id == TI::GEq )
            return 2;

        if ( id == TI::Bool_And || id == TI::Bool_Or )
            return 1;

        return 0;
    }

    Token( TI id, std::string data ) : wibble::Token< TI >( id, data ) {}
    Token() = default;
};

template< typename Stream >
struct Lexer : wibble::Lexer< Token, Stream >
{
    static int space( int c ) { return isspace( c ) && c != '\n'; }
    static int firstident( int c ) { return isalpha( c ) || c == '_'; }
    static int restident( int c ) {
        return isprint( c ) && !isspace( c ) &&
            c != '|' && c != '#' && c != ':' && c != '(' && c != ')' &&
            c != '{' && c != '}' && c != '.';
    }

    static constexpr const std::string * const frag = Token::frag;
    enum Frag { HASH, NL, AND, OR, TRUE, FALSE };

    Token remove() {
        this->skipWhile( space );

        this->match( frag[ NL ], TI::Newline );
        this->match( frag[ HASH ], frag[ NL ], TI::Comment );

        this->match( frag[ TRUE ], TI::Constant );
        this->match( frag[ FALSE ], TI::Constant );

        for ( int i = static_cast< int >( TI::Map ); i < TI_End; ++i )
            this->match( Token::tokenName[i], static_cast< TI >( i ) );

        this->match( frag[ OR ], TI::Bool_Or );
        this->match( frag[ AND ], TI::Bool_And );

        this->match( firstident, restident, TI::Identifier );
        this->match( isdigit, isdigit, TI::Constant );

        return this->decide();
    }

    Lexer( Stream &s )
        : wibble::Lexer< Token, Stream >( s )
    {}
};

struct Buffer {
    std::string buf;

    std::string remove() {
        std::string ret;
        std::swap( ret, buf );
        return ret;
    }

    bool eof() { return buf.empty(); }
    Buffer( std::string s ) : buf( s ) {}
};

typedef wibble::Parser< Token, Lexer< Buffer > > Parser;

struct Expression;
using ExpressionPtr = std::shared_ptr< Expression >;

struct Scope;
using ScopePtr = std::shared_ptr< Scope >;

struct Identifier : Parser {
    std::string name;
    Identifier() = default;
    Identifier( Context &c ) : Parser( c ) {
        auto t = eat( TI::Identifier );
        name = t.data;
    }
    Identifier( std::string n ) : name( n ) {}
};

struct Constant : Parser
{
    int value;
    ScopePtr scope;

    Constant() = default;
    Constant( Context &c ) : Parser( c ) {
        if ( next( TI::BraceOpen ) ) {
            scope = std::make_shared< Scope >( c );
            eat( TI::BraceClose );
        } else if ( next( TI::BlockDef ) ) {
            scope = std::make_shared< Scope >( c );
            eat( TI::BlockEnd );
        } else {
            auto t = eat( TI::Constant );
            value = atoi( t.data.c_str() );
        }
    }
};

struct Lambda : Parser {
    Identifier bind;
    ExpressionPtr body;

    Lambda() = default;
    Lambda( Context &c );
    Lambda( Identifier i, ExpressionPtr b )
        : bind( i ), body( b )
    {}
};

struct IfThenElse : Parser {
    ExpressionPtr cond, yes, no;

    IfThenElse() = default;
    IfThenElse( Context &c );
};

struct BinOp {
    ExpressionPtr lhs, rhs;
    TI op;
    BinOp( ExpressionPtr lhs, Token op, ExpressionPtr rhs )
        : lhs( lhs ), rhs( rhs ), op( op.id )
    {}
};

struct SubScope {
    ExpressionPtr lhs, rhs;
    SubScope( ExpressionPtr lhs, ExpressionPtr rhs )
        : lhs( lhs ), rhs( rhs )
    {}
};

struct Application {
    ExpressionPtr lhs, rhs;
    Application( ExpressionPtr lhs, ExpressionPtr rhs )
        : lhs( lhs ), rhs( rhs )
    {}
};

struct Expression : Parser {

    using E = wibble::Union< BinOp, SubScope, Lambda, Constant, Identifier, IfThenElse, Application >;
    E e;

    struct Atom {};

    void lambda() { e = Lambda( context() ); }
    void variable() { e = Identifier( context() ); }
    void constant() { e = Constant( context() ); }
    void ifthenelse() { e = IfThenElse( context() ); }

    Expression() = default;
    Expression( E e ) : e( e ) {}
    Expression( Context &c, Atom ) : Parser( c ) {
        if ( next( TI::ParenOpen ) ) {
            e = Expression( c ).e;
            eat( TI::ParenClose );
        } else
            either( &Expression::constant,
                    &Expression::variable );
    }

    Expression( Context &c, int min_prec = 0 )
        : Parser( c )
    {
        if ( !min_prec ) {
            if ( !maybe( &Expression::lambda,
                         &Expression::ifthenelse ) )
                e = Expression( c, 1 ).e;
            return;
        }

        int next_min_prec;
        bool done = false;

        e = Expression( c, Atom() ).e;

        do {
            Token op = eat( false );

            if ( op.valid() && op.precedence() >= min_prec ) {
                next_min_prec = op.precedence() + op.leftassoc();
                auto rhs = std::make_shared< Expression >( c, next_min_prec );
                e = BinOp( std::make_shared< Expression >( e ), op, rhs );
            } else if ( op.valid() && op.id == TI::SubScope && Token::precedences + 1 >= min_prec ) {
                auto rhs = std::make_shared< Expression >( c, Token::precedences + 2 );
                next_min_prec = Token::precedences + 2;
                e = SubScope( std::make_shared< Expression >( e ), rhs );
            } else {
                c.rewind( 1 ); // put back op
                done = true;
                if ( op.valid() && !op.precedence() && Token::precedences + 1 >= min_prec &&
                     maybe( [&]() {
                             auto rhs = std::make_shared< Expression >( c, Token::precedences + 2 );
                             next_min_prec = Token::precedences + 2;
                             this->e = Application( std::make_shared< Expression >( e ), rhs );
                         } ) )
                    done = false;
            }
        } while ( !done );
    }
};

struct PrintTo {
    std::ostream &o;
    template< typename T >
    auto operator()( T t ) -> decltype( o << t ) { return o << t; }
    PrintTo( std::ostream &o ) : o( o ) {}
};

inline std::ostream &operator<<( std::ostream &o, Expression e );

inline std::ostream &operator<<( std::ostream &o, Identifier i ) { return o << i.name; }
inline std::ostream &operator<<( std::ostream &o, Constant c ) { return o << c.value; }
inline std::ostream &operator<<( std::ostream &o, Application ap ) {
    return o << *ap.lhs << " " << *ap.rhs;
}

inline std::ostream &operator<<( std::ostream &o, Lambda l ) {
    return o << "(|" << l.bind.name << "| " << *l.body << ")";
}

inline std::ostream &operator<<( std::ostream &o, BinOp op ) {
    return o << "(" << *op.lhs << " " << Token::tokenName[ int( op.op ) ] << " " << *op.rhs << ")";
}

inline std::ostream &operator<<( std::ostream &o, Expression e )
{
    if ( e.e.apply( PrintTo( o ) ).isNothing() )
        o << "<unknown expression>";
    return o;
}

inline Lambda::Lambda( Context &c ) : Parser( c ) {
    eat( TI::LambdaParen );
    bind = Identifier( c );
    eat( TI::LambdaParen );
    body = std::make_shared< Expression >( c );
}

inline IfThenElse::IfThenElse( Context &c ) : Parser( c ) {
    eat( TI::If );
    cond = std::make_shared< Expression >( c );
    eat( TI::Then );
    yes = std::make_shared< Expression >( c );
    eat( TI::Else );
    no = std::make_shared< Expression >( c );
}

struct Binding : Parser {
    Identifier name;
    Expression value;

    Binding() = default;
    Binding( Context &c ) : Parser( c ) {
        name = Identifier( c );
        eat( TI::Bind );
        value = Expression( c );
    }
};

struct Scope : Parser {
    std::vector< Binding > bindings;

    void separator() {
        Token t = eat( true );

        if ( t.id == TI::Newline )
            return separator(); /* eat all of them */
        if ( t.id == TI::Semicolon )
            return separator(); /* eat all of them */

        rewind( 1 ); /* done */
    }

    Scope() = default;
    Scope( Context &c ) : Parser( c ) {
        list< Binding >( std::back_inserter( bindings ), &Scope::separator );
    }
};

}

}
}

#endif
