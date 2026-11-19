#!/bin/sh
# Builds the programs here (`admin`, `admin2`, `memrchr`: each from its `.c` file that this directory holds) with
# `gcc -O2 -static`, and prints the SHA-256 of the static C library and of libgcc's `libgcc_eh.a` they are linked
# against, and of the programs. Without arguments it writes the programs here; `--check` builds them into a temporary
# directory and compares them with the files here, and compares `../libc.a` with the static C library gcc links.
#
# The files here were built on Ubuntu 26.04 (amd64) with gcc 15.2 (15.2.0-16ubuntu1) and GNU ld 2.46, against
# `libc6-dev` 2.43-2ubuntu2.4, whose inputs have these SHA-256:
#   2a277b999268f100c5f838689704b7432e9b1fdac76bf0cbda83cdbbaecc89e2  libc.a
#   050160c9613ecf99b449bb34743fb8b2f4aafb3ae03a38a63e69a6926f956140  libgcc_eh.a
# Another toolchain or C library gives other bytes. The theorems are about the files here and `../libc.a`, whose
# SHA-256 the statements fix (`../Glibc243UbuntuClients/Files/*.lean`, `../Glibc243Ubuntu/LibcA.lean`), however they
# were made.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
check=0
if [ "${1:-}" = "--check" ]; then check=1; fi
out=$here
if [ $check = 1 ]; then out=$(mktemp -d); fi
programs=$(cd "$here" && ls *.c | sed 's/\.c$//')
for p in $programs; do
  gcc -O2 -static -w "$here/$p.c" -o "$out/$p"
done
sha256sum "$(gcc -print-file-name=libc.a)" "$(gcc -print-file-name=libgcc_eh.a)"
(cd "$out" && sha256sum $programs)
if [ $check = 1 ]; then
  for p in $programs; do cmp "$here/$p" "$out/$p"; done
  rm -r "$out"
  if [ -f "$here/../libc.a" ]; then cmp "$here/../libc.a" "$(gcc -print-file-name=libc.a)"; fi
  echo "the programs here (and ../libc.a, where present) are the ones this toolchain builds (links)"
fi
