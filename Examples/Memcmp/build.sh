#!/bin/sh
# Builds memcmp.c five ways into OUTDIR (default: a temporary directory), each linked as a static
# ELF with `.text` at 0x401000, and prints the bytes of `memcmp` from each, one line per build:
# "<name> <first 16 digits of the sha256 of the hex> <hex bytes>"; each build is also linked at
# 0x10000000 and must have the same bytes there. `code.txt` records these lines
# and `Code.lean` holds the same bytes; `--check` compares the build with `code.txt`, and
# `code.txt` with `Code.lean`, and fails on a difference.
# Toolchain of the recorded bytes: gcc 15.2, clang 21, GNU ld 2.46 (x86-64 Linux).
set -eu
here=$(cd "$(dirname "$0")" && pwd)
check=0
if [ "${1:-}" = "--check" ]; then check=1; shift; fi
out=${1:-$(mktemp -d)}
mkdir -p "$out"
flags="-ffreestanding -fno-builtin -fno-stack-protector -fcf-protection=none -fno-pic -fno-asynchronous-unwind-tables"
build() { # name compiler...
  name=$1; shift
  "$@" $flags -c "$here/memcmp.c" -o "$out/$name.o"
  ld -static -e memcmp -Ttext=0x401000 --build-id=none -o "$out/$name" "$out/$name.o"
  addr=$(nm "$out/$name" | awk '$3 == "memcmp" { print $1 }')
  size=$(nm -S "$out/$name" | awk '$4 == "memcmp" { print $2 }')
  [ "$addr" = "0000000000401000" ] || { echo "$name: memcmp at $addr" >&2; exit 1; }
  # `memcmp` is the first function of `.text`, at its start
  objcopy -O binary -j .text "$out/$name" "$out/$name.text"
  hex=$(od -A n -t x1 -v -N $((0x$size)) "$out/$name.text" | tr -d ' \n')
  # the bytes do not depend on the address (`holds` is for any): the same when linked elsewhere
  ld -static -e memcmp -Ttext=0x10000000 --build-id=none -o "$out/$name-at" "$out/$name.o"
  objcopy -O binary -j .text "$out/$name-at" "$out/$name-at.text"
  hexAt=$(od -A n -t x1 -v -N $((0x$size)) "$out/$name-at.text" | tr -d ' \n')
  [ "$hexAt" = "$hex" ] || { echo "$name: bytes differ when linked at 0x10000000" >&2; exit 1; }
  sum=$(printf '%s' "$hex" | sha256sum | cut -c1-16)
  echo "$name $sum $hex"
}
{
  build gccO2 gcc -O2
  build clangO2 clang -O2
  build gccOs gcc -Os
  build gccO1 gcc -O1
  build clangOs clang -Os
} > "$out/code.txt"
cat "$out/code.txt"
if [ $check = 1 ]; then
  diff "$here/code.txt" "$out/code.txt"
  while read -r name _ hex; do
    lean=$(sed -n "/^def $name : List Byte :=/,/]/p" "$here/Code.lean" | tail -n +2 | tr -d ' \n[],' | sed 's/0x//g')
    [ "$lean" = "$hex" ] || { echo "Code.lean: $name differs from code.txt" >&2; exit 1; }
  done < "$here/code.txt"
  echo "bytes as recorded, in code.txt and in Code.lean"
fi
