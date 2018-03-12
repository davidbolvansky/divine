/* TAGS: min c++ */
/* VERIFY_OPTS: -o nofail:malloc */
#include <sys/monitor.h>
#include <sys/interrupt.h>

volatile int glob;

bool isZero() { return glob == 0; }

struct DummyMon : public __dios::Monitor
{
    void step() { }
};

struct GlobMon : public __dios::Monitor
{
    void step()  {
        if ( !isZero() )
            __vm_control( _VM_CA_Bit, _VM_CR_Flags, _VM_CF_Error, _VM_CF_Error ); /* ERROR */
    }
};

int main()
{
    for ( int i = 0; i != 2; i++ )
        glob = glob ? 0 : 1;

    __dios::register_monitor( new DummyMon() );
    __dios::register_monitor( new GlobMon() );

    for ( int i = 0; i != 2; i++ )
    {
        glob = glob ? 0 : 1;
        __dios_interrupt();
    }
}
