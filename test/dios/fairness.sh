# TAGS: min
. lib/testcase

tee fairness.cpp <<EOF
#include <dios.h>
#include <thread>
#include <atomic>
#include <sys/monitor.h>
#include <sys/vmutil.h>

bool checkX();

void __buchi_accept();
void __buchi_cancel();
unsigned __buchi_choose(unsigned);

struct BuchiAutomaton : public __dios::Monitor
{
  BuchiAutomaton() : state(0) {}
  void step()
  {
    switch(state)
    {
      case 0: {
        unsigned nd0 = __buchi_choose(2);
        if ((nd0 == 0) && true)
        {
          state = 0;
        }
        else if ((nd0 == 1) && !checkX())
        {
          state = 1;
        }
        break;
      }
      case 1: {
        if (!checkX())
        {
          __buchi_accept();
          state = 1;
        }
        else
        {
          __buchi_cancel();
        }
        break;
      }
    }
  }

  unsigned state;
};

void __buchi_accept() {
    __vm_control( _VM_CA_Bit, _VM_CR_Flags, _VM_CF_Accepting, _VM_CF_Accepting );
}

void __buchi_cancel() {
    __vm_control( _VM_CA_Bit, _VM_CR_Flags, _VM_CF_Cancel, _VM_CF_Cancel );
}

unsigned __buchi_choose( unsigned n ) {
    return __vm_choose( n );
}

std::atomic_int x;

bool checkX() { return x == 1; }

int main() {
    __dios::register_monitor( new BuchiAutomaton() );

    __dios_trace_t( "Monitor registered" );

    auto t = std::thread( [&]{
        while ( true ) {
            __dios_trace_t( "Set 1" );
            x = 1;
            __vmutil_interrupt();
        }
    } );

    __dios_trace_t( "Thread started" );

    while ( true ) {
        __dios_trace_t( "Set 0" );
        x = 0;
        __vmutil_interrupt();
    }
}
EOF

divine verify --liveness -std=c++1z -onofail:malloc fairness.cpp > trace1.out
if ! grep "error found: yes" trace1.out; then
    echo "No error was found, but one was expected"
    cat trace1.out
    result=1
fi

divine verify --liveness -std=c++1z -onofail:malloc -oconfig:fair fairness.cpp > trace2.out
if ! grep "error found: no" trace2.out; then
    echo "Error was found, but none was expected"
    cat trace2.out
    result=1
fi

exit $result
