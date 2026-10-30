import ZellicX86.Spec.Statement
/-!
# Statement vocabulary: the C library's `errno`

A library layer over the statement vocabulary (`Spec/Statement.lean`): the first component of the C library
as a C program sees it, the calling thread's `errno`, for contracts of library functions that say what they
do to it (`Spec/Lib/C/Malloc.lean`).

What C and POSIX say of `errno`: it is a modifiable lvalue of type `int` with thread-local storage duration,
whose value in the initial thread is zero at program startup and which no library function sets to zero; a
library function may set it to a nonzero value whether or not there is an error, unless its description
says otherwise (C17 7.5). A function's description says when it sets it and to what, as POSIX does for
`malloc` (`ENOMEM` on failure), and some functions do not change it at all (POSIX.1-2024's `free`).

Where it lies is the library's choice. glibc 2.43 defines it as an initial-exec thread-local variable
(`__thread int errno attribute_tls_model_ie`, `csu/errno.c`, `include/errno.h`): 4 bytes at a fixed offset
from the thread pointer, the `FS` base on x86-64 (psABI, "Thread-Local Storage"), which the linker fixes
for each program (for example, `fs:-0x10` means `errnoOff = 2 ^ 64 - 16`) and the
dynamic loader for `libc.so.6`. `__errno_location` returns its address (`csu/errno-loc.c`). So a C library
instance has a parameter `errnoOff`, the offset of its `errno` from the `FS` base, which a statement
quantifies over or fixes:

- where it lies, as a region of the thread of a state (`errnoLoc`, `errnoAt` for an `FS` base);
- its value in a state (`errno`), an unsigned 32-bit number (a negative `int` is its two's complement;
  every error number is positive);
- what a function does to it: sets it to an error number (`Errno.set`), or leaves it as it was
  (`Errno.keeps`). A contract that says neither, but lists `errno` among what the function writes, lets the
  function leave any value there.

Error numbers are those of Linux (`ENOMEM`, `include/uapi/asm-generic/errno-base.h`), which glibc's
`<errno.h>` takes from the kernel's headers.
-/
namespace ZellicX86.C

/-- `errno` of a thread whose `FS` base is `fs`, for a C library whose `errno` lies `errnoOff` bytes from
the `FS` base (modulo `2 ^ 64`): the 4 bytes at `fs + errnoOff`. -/
abbrev errnoAt (errnoOff : Nat) (fs : Addr) : Rgn := ⟨fs.add errnoOff, 4⟩

/-- `errno` of the thread of `s`, for a C library whose `errno` lies `errnoOff` bytes from the `FS` base:
the region `errnoAt` at the thread's `FS` base (`Segs.fsBase`). -/
abbrev errnoLoc (errnoOff : Nat) (s : State) : Rgn := errnoAt errnoOff s.cpu.seg.fsBase

/-- The value of `errno` in `s` for a C library whose `errno` lies `errnoOff` bytes from the `FS` base:
the 4-byte little-endian number at `errnoLoc errnoOff s` (`readNat`, `State.byte`). -/
def errno (errnoOff : Nat) (s : State) : Nat := readNat s.byte (errnoLoc errnoOff s).base 4

/-- At `X`, `errno` (of a C library whose `errno` lies `errnoOff` bytes from the `FS` base) holds the error
number `e`: what a function that "sets `errno` to `e`" leaves. -/
def Errno.set (errnoOff : Nat) (e : Nat) (X : State) : Prop := errno errnoOff X = e

/-- From `s` to `X`, `errno` (of a C library whose `errno` lies `errnoOff` bytes from the `FS` base) kept
its value: what a function that "does not modify `errno`" leaves. -/
def Errno.keeps (errnoOff : Nat) (s X : State) : Prop := errno errnoOff X = errno errnoOff s

end ZellicX86.C
