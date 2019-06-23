// -*- mode: C++; indent-tabs-mode: nil; c-basic-offset: 4 -*-

/*
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

#ifndef _STDARG_H
#define _STDARG_H

#ifdef __cplusplus
extern "C" {
#endif

typedef __builtin_va_list va_list;

  // this will be replaced by the va_arg instruction using LART
#ifdef __cplusplus
  void *__lart_llvm_va_arg( va_list va ) throw();
  #define va_arg( ap, type ) (static_cast< type >( \
        *reinterpret_cast< type * >(__lart_llvm_va_arg( (ap) ))))
#else
  void *__lart_llvm_va_arg( va_list va ) __attribute__((__nothrow__));
  #define va_arg( ap, type ) ((type)(*(type *)__lart_llvm_va_arg( (ap) )))
#endif

#define va_copy( dest, src ) (__builtin_va_copy( (dest), (src) ))
#define va_end( ap ) (__builtin_va_end( ap ) )
#define va_start( ap, parmN ) (__builtin_va_start( (ap), (parmN) ))

#ifdef __cplusplus
}
#endif

#endif
