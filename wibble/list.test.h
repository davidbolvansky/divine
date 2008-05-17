// -*- C++ -*-

#include <wibble/list.h>
#include <wibble/test.h>

using namespace wibble;

struct TestList {
    struct My {
        typedef int Type;
        int i, max;
        int head() { return i; }

        My tail() const {
            My t = *this;
            if ( i < max )
                t.i ++;
            if ( i > max )
                t.i --;
            return t;
        }

        bool empty() const { return i == max; }

        My( int j = 0, int m = 0 ) : i( j ), max( m ) {}
    };

    struct My2 {
        typedef int Type;
        int i, max, rep, repmax;
        int head() { return i; }

        My2 tail() const {
            My2 t = *this;
            if ( rep > 0 )
                t.rep --;
            else {
                t.rep = repmax;
                if ( i < max )
                    t.i ++;
                if ( i > max )
                    t.i --;
            }
            return t;
        }

        bool empty() const { return i == max; }

        My2( int j = 0, int m = 0, int r = 0 ) : i( j ), max( m ),
                                                 rep( r ), repmax( r ) {}
    };

    static bool odd( int i ) {
        return i % 2 == 1;
    }

    template< typename List >
    void checkOddList( List l ) {
        int i = 0;
        while ( !l.empty() ) {
            assert( odd( l.head() ) );
            l = l.tail();
            ++ i;
        }
        assert_eq( i, 512 );
    }

    template< typename List >
    void checkListSorted( List l )
    {
        if ( l.empty() )
            return;
        typename List::Type last = l.head();
        while ( !l.empty() ) {
            assert( last <= l.head() );
            last = l.head();
            l = l.tail();
        }
    }

    Test count() {
        My list( 512, 1024 );
        assert_eq( list::count( list ), 512 );
        list = My( 0, 1024 );
        assert_eq( list::count( list ), 1024 );
    }

    Test filtered() {
        My list( 1, 1024 );
        checkOddList( list::filter( list, odd ) );
        assert_eq( list::count( list::filter( list, odd ) ), 512 );
    }

    Test sorted() {
        My list( 1, 1024 );
        assert_eq( list::count( list ), list::count( list::sort( list ) ) );
        checkListSorted( list );
        checkListSorted( list::sort( list ) );
        {
            AssertFailure fail;
            checkListSorted( My( 100, 0 ) );
        }
        checkListSorted( list::sort( My( 100, 0 ) ) );
    }

    Test take() {
        My list( 0, 1024 );
        assert_eq( list::count( list ), 1024 );
        assert_eq( list::count( list::take( 50, list ) ), 50 );
    }

    Test unique() {
        My2 list( 0, 20, 3 );
        assert_eq( list::count( list ), 80 );
        assert_eq( list::count( list::unique( list ) ), 20 );
        assert_eq( list::unique( list ).head(), 0 );
        assert_eq( list::unique( list ).tail().head(), 1 );
    }

    Test stl() {
        My list( 0, 1024 );
        std::vector< int > vec;
        std::copy( list::begin( list ), list::end( list ),
                   std::back_inserter( vec ) ); 
        for ( int i = 0; i < 1024; ++i )
            assert_eq( vec[i], i );
    }

    static int mul2add1( int a ) {
        return a * 2 + 1;
    }

    Test map() {
        My list( 0, 512 );
        checkOddList( 
            list::map( list, std::ptr_fun( mul2add1 ) ) );
    }
};
