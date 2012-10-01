#!/bin/sh
mkdir -p "`dirname "$1"`"
set -e
sed -e '1i \
namespace murphi { const char *'"`basename ${1}`"'_str = "\\' \
    -e 's,\\,\\\\,g' \
    -e 's,$,\\n\\,' \
    -e 's,",\\",g' \
    -e 's,wibble/test.h,cassert,' \
    -e '$a \
\"\; }' \
    < "$2" > "${1}_str.cpp"
