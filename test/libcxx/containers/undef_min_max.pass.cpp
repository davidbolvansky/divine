/* TAGS: c++ fin */
/* CC_OPTS: -std=c++2a */
/* VERIFY_OPTS: -o nofail:malloc */
//===----------------------------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#if defined(__GNUC__) || defined(__clang__)
#pragma GCC diagnostic ignored "-W#warnings"
#endif

#define min THIS IS A NASTY MACRO!
#define max THIS IS A NASTY MACRO!

#include <map>

#include "test_macros.h"

int main(int, char**) {
  std::map<int, int> m;
  ((void)m);

  return 0;
}
