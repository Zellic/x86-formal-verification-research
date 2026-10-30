# Third-party material

Most of this repository is Zellic's work, licensed under the MIT License or the Apache License 2.0 at your option
(README, "License"). The material listed here is not: it is copied from, or contains, the GNU C Library (glibc) or
the Linux kernel, and it keeps its own license. The license texts are in `LICENSES/`.

## The GNU C Library (glibc 2.43, Ubuntu 26.04's build)

glibc is Copyright (C) the Free Software Foundation, Inc., and others, and is licensed under the GNU Lesser General
Public License, version 2.1 or (at your option) any later version (`LICENSES/LGPL-2.1.txt`; version 3:
`LICENSES/LGPL-3.0.txt`, which incorporates `LICENSES/GPL-3.0.txt`). It has NO WARRANTY.

- **`glibc-2.43-ubuntu-26.04-amd64/clients/admin` and `clients/admin2`**: programs statically linked against glibc
  2.43's static library (`libc.a`, startup files `crt1.o`, `crti.o`, `crtn.o`) from Ubuntu 26.04's package `libc6-dev`
  2.43-2ubuntu2.4 (amd64). Each contains parts of glibc, which remain under its license. The programs' own code is
  `clients/admin.c` and `clients/admin2.c`; with `clients/build.sh` they can be relinked against a modified glibc.
  They also contain parts of GCC's runtime (`crtbeginT.o`, `libgcc_eh.a` from GCC 15.2), which the GCC Runtime Library
  Exception covers.
- **The proof exports** (`exports/`, downloaded separately): they contain the bytes of `clients/admin` and
  `clients/admin2`.

**Source code.** The Corresponding Source of the glibc build these files come from is Ubuntu's source package
`glibc` 2.43-2ubuntu2.4: https://launchpad.net/ubuntu/+source/glibc/2.43-2ubuntu2.4 (the upstream release, without
Ubuntu's changes: https://ftp.gnu.org/gnu/glibc/glibc-2.43.tar.xz).

## The Linux kernel (6.18.35)

- **`ZellicX86/Spec/VdsoImages.lean`**: the first 1368 bytes of the vDSO image of a Linux 6.18.35 kernel for x86-64,
  as a running process sees it: its ELF header, program headers, hash, symbol and version tables and dynamic section
  (no code). The vDSO is part of the Linux kernel (`arch/x86/entry/vdso/`), Copyright (C) its authors, licensed
  under the GNU General Public License, version 2 (`LICENSES/GPL-2.0.txt`), with NO WARRANTY. Source:
  https://cdn.kernel.org/pub/linux/kernel/v6.x/linux-6.18.35.tar.xz.
