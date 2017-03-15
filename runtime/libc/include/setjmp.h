// -*- C++ -*- (c) 2016 Vladimír Štill <xstill@fi.muni.cz>

#include <stdint.h>
#include <divine/metadata.h>
#include <sys/divm.h>

#ifndef _SETJMP_H_
#define _SETJMP_H_

#ifdef __cplusplus
extern "C" {
#endif

// minimal implementation
struct __jmp_buf_tag
{
    struct _VM_Frame *__jumpFrame;
    _VM_CodePointer __jumpPC;
    const _MD_Function *__jumpFunctionMeta;
};

typedef struct __jmp_buf_tag jmp_buf[1];

int setjmp( jmp_buf env ) __attribute__((__noinline__, __returns_twice__, __nothrow__));
// int sigsetjmp( sigjmp_buf env, int savesigs );

void longjmp( jmp_buf env, int val ) __attribute__((__nothrow__));
// void siglongjmp( sigjmp_buf env, int val );

#ifdef __cplusplus
} // extern "C"
#endif

#endif // _SETJMP_H_
