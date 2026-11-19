#!/bin/sh
# Builds this directory's objects: glibc 2.43's `sysdeps/x86_64/multiarch/memrchr-evex.S` and `memrchr-avx2.S`, each
# with its patch (`memrchr-evex.patch`: the page-crossing path's `sub edx, esi` made 64-bit; `memrchr-avx2.patch`: a `jb`
# to the null return after each of the three subtractions that can borrow), assembled as glibc's build of `libc.a` does
# for x86-64 Linux with CET enabled. Each is assembled once as it is too: its function's section must have the bytes
# of the same object in `../libc.a` (Ubuntu's file), so that the build is the one that made the library; the script
# fails otherwise. The patched objects go to OUTDIR (default a fresh temporary directory) as `memrchr-evex-fixed.o` and
# `memrchr-avx2-fixed.o`; `--check` compares them with this directory's, which the statements load by their SHA-256
# (`Glibc243Ubuntu/MemrchrFixedObjs.lean`). The assembler's flags are glibc's (`Makeconfig`, `Makerules`,
# `sysdeps/x86_64/Makefile`): the include path of the configured sysdeps directories, `-include libc-modules.h -include
# libc-symbols.h`, `-DMODULE_NAME=libc`, `-DASSEMBLER`, and for CET `-fcf-protection -include cet.h`; the files configure
# would generate are stubs written below (the files use none of their contents but the module numbers). Needs gcc, GNU
# binutils (`ar`, `objcopy`) and glibc 2.43's source (`GLIBC_SRC`). Toolchain of the recorded objects: gcc 15.2, GNU as
# 2.46.
#   build.sh [--check] [OUTDIR]
set -eu
here=$(cd "$(dirname "$0")" && pwd)
check=0
if [ "${1:-}" = "--check" ]; then check=1; shift; fi
out=${1:-$(mktemp -d)}
mkdir -p "$out"
G=${GLIBC_SRC:?set GLIBC_SRC to a checkout of glibc 2.43 (the tag glibc-2.43 of glibc's git repository)}
[ -f "$G/sysdeps/x86_64/multiarch/memrchr-evex.S" ] || { echo "no glibc 2.43 source at $G (GLIBC_SRC)" >&2; exit 1; }
mkdir -p "$out/gen/misc/bits"
: > "$out/gen/config.h"
printf '#define MODULE_testsuite 1\n#define MODULE_LIBS_BEGIN 2\n#define MODULE_libc 3\n' > "$out/gen/libc-modules.h"
: > "$out/gen/misc/bits/syscall.h"
inc="-I$G/include -I$out/gen"
for d in unix/sysv/linux/x86_64/64 unix/sysv/linux/x86_64 unix/sysv/linux/x86 x86/nptl unix/sysv/linux/wordsize-64 \
    x86_64/nptl unix/sysv/linux nptl pthread gnu unix/inet unix/sysv unix/x86_64 unix posix x86_64/64 \
    x86_64/fpu/multiarch x86_64/fpu x86/fpu x86_64/multiarch x86_64 x86 ieee754/float128 ieee754/ldbl-96 \
    ieee754/dbl-64 ieee754/flt-32 wordsize-64 ieee754 generic; do
  [ -d "$G/sysdeps/$d/include" ] && inc="$inc -I$G/sysdeps/$d/include"
  inc="$inc -I$G/sysdeps/$d"
done
inc="$inc -I$G -I$G/libio -I$G/string"
asm() {
  gcc -c -fcf-protection -include cet.h -include "$out/gen/config.h" -include "$out/gen/libc-modules.h" \
    -include "$G/include/libc-symbols.h" -DMODULE_NAME=libc -DTOP_NAMESPACE=glibc -D_LIBC_REENTRANT -DASSEMBLER \
    $inc -o "$1" "$2"
}
# one VARIANT SECTION: the unpatched build's SECTION against libc.a's member's, then the patched object
one() {
  v=$1; sec=$2
  mkdir -p "$out/src-$v/sysdeps/x86_64/multiarch"
  cp "$G/sysdeps/x86_64/multiarch/memrchr-$v.S" "$out/src-$v/sysdeps/x86_64/multiarch/"
  (cd "$out/src-$v" && patch -s -p1 < "$here/memrchr-$v.patch")
  asm "$out/orig-$v.o" "$G/sysdeps/x86_64/multiarch/memrchr-$v.S"
  (cd "$out" && ar p "$here/../libc.a" "memrchr-$v.o" > "libc-$v.o")
  objcopy -O binary -j "$sec" "$out/orig-$v.o" "$out/orig-$v.bin"
  objcopy -O binary -j "$sec" "$out/libc-$v.o" "$out/libc-$v.bin"
  cmp -s "$out/orig-$v.bin" "$out/libc-$v.bin" || { echo "the unpatched memrchr-$v.S differs from libc.a's" >&2; exit 1; }
  asm "$out/memrchr-$v-fixed.o" "$out/src-$v/sysdeps/x86_64/multiarch/memrchr-$v.S"
  sha256sum "$out/memrchr-$v-fixed.o"
  if [ $check = 1 ]; then
    cmp -s "$out/memrchr-$v-fixed.o" "$here/memrchr-$v-fixed.o" || { echo "memrchr-$v-fixed.o differs from $here's" >&2; exit 1; }
  fi
}
one evex .text.evex
one avx2 .text.avx
[ $check = 1 ] && echo "the unpatched builds as libc.a's; the patched objects as recorded"
exit 0
