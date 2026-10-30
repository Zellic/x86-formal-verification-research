import ZellicX86.Spec.Statement
import Examples.Memcmp.Spec
import Examples.Memcmp.Code
/-!
# Statement: `memcmp`, compiled by GCC and Clang, meets the C standard's contract

The theorems `Memcmp.gccO2_holds`, `clangO2_holds`, `gccOs_holds`, `gccO1_holds` and `clangOs_holds` (proved by
the exports `memcmp-gcc-o2`, …, checked by `checks/memcmp-*/`) each state `holds` of the machine code of one build of `memcmp.c` (`Code.lean`: the bytes
`gcc -O2`, `clang -O2`, `gcc -Os`, `gcc -O1` and `clang -Os` produce; `build.sh` rebuilds them).

In words, for each build: wherever the bytes are placed in memory, every call of them under the System V calling
convention returns, with `eax` an `int` whose sign is the order of the two byte strings (`cmpBytes`: as the C
standard's `memcmp` returns, C17 7.24.4.1), having written no memory but the slot of its return address, made
no system call, kept the callee-saved registers, and executed no byte outside the code it was given.

What it assumes (`contract`, `holds`):
- the call follows the System V x86-64 calling convention (`sysv`: `a`, `b`, `n` in `rdi`, `rsi`, `rdx`, the
  stack aligned, the return address pushed);
- the `n` bytes at `a` and the `n` bytes at `b` are readable memory (`reads`), and neither overlaps the return
  address's slot (`pre`); the two strings may overlap each other or coincide, and `n` may be 0;
- no one disturbs the run from outside: no signal arrives, no other agent writes the process's memory
  (`Undisturbed`, the default environment of a contract).
It assumes nothing about the processor (`∀ prof`): the code uses only base x86-64 instructions.

`holds code` quantifies over where the code lies: for every list `L` of code segments that holds `code` at address
`e` (`CodeIn`), the code at `e` implements `contract` over `L` (`ImplementsCall`). The bytes contain no absolute
address, so one theorem covers every placement.
-/
namespace Memcmp
open ZellicX86

/-- The two strings `memcmp` compares, as regions of the entry state `s`. -/
def strings (s : State) : List Rgn :=
  [⟨s.cpu.gpr.rdi, s.cpu.gpr.rdx.toNat⟩, ⟨s.cpu.gpr.rsi, s.cpu.gpr.rdx.toNat⟩]

/-- `memcmp`'s contract: the sign of `eax` is the order of the two strings; it writes no memory but its return
address's slot (`frame s 0`: no stack frame of its own) and makes no system call. -/
def contract : Contract where
  conv := sysv
  reads := strings
  writes s := [frame s 0]
  pre s := Apart [frame s 0] (strings s)
  post s X :=
    compare (X.cpu.gpr.rax.setWidth 32).toInt 0 =
      cmpBytes (readBytes s.proc.mm.mem s.cpu.gpr.rdi s.cpu.gpr.rdx.toNat)
        (readBytes s.proc.mm.mem s.cpu.gpr.rsi s.cpu.gpr.rdx.toNat)
  events _ _ evs := evs = []

/-- `code`, at any address in any list of code segments that holds it, implements `memcmp`'s contract, on every
processor. -/
def holds (code : List Byte) : Prop := ∀ L prof e, CodeIn L e code → ImplementsCall prof e L contract

end Memcmp
