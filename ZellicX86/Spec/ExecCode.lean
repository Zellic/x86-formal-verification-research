import ZellicX86.Spec.Elf
import ZellicX86.Spec.Word
/-!
# The code of an executable, and the code without a function's bytes

What a statement about a program names as the code it confines a run to (`InCode` in `ImplementsCallUptoIf`,
`C.CStart.startup`'s code lists): the file's executable segments (`execSegments`: each loadable program header with the
execute flag, its bytes from the file at its address), and those segments without one function's bytes (`codeWithout`:
the code a C library's startup runs before it calls `main`; a startup confined to it executes no byte of `main` before
that call, where `main`'s bytes lie in one of the segments).
-/
namespace ZellicX86

/-- The executable segments of the file whose bytes are `img` and whose program headers are `phs` (ELF, `Spec/Elf.lean`):
each loadable program header (`PT_LOAD`) with the execute flag (`PF_X`, bit 0), its file part's bytes (`p_filesz` of
them from `p_offset`) at its address (`p_vaddr`), as `execve` maps them: the code a statement confines a run of the
program to (`InCode`). -/
def execSegments (img : Nat → Byte) (phs : List Phdr) : List (Addr × List Byte) :=
  (phs.filter fun ph => ph.type == PT_LOAD && ph.hasFlag 1).map fun ph =>
    (BitVec.ofNat 64 ph.vaddr, (List.range ph.filesz).map fun i => img (ph.offset + i))

/-- The code segment `c` without the bytes `m` (an address and its bytes): if they lie in `c`, its part before them and
its part after them, otherwise `c` whole. -/
def segWithout (m c : Addr × List Byte) : List (Addr × List Byte) :=
  if c.1.toNat ≤ m.1.toNat ∧ m.1.toNat + m.2.length ≤ c.1.toNat + c.2.length then
    [(c.1, c.2.take (m.1.toNat - c.1.toNat)), (m.1.add m.2.length, c.2.drop (m.1.toNat - c.1.toNat + m.2.length))]
  else [c]

/-- The code segments `code` without the bytes `m` (`segWithout` of each): the code a C library's startup runs before
it calls `main` where `m` is `main`'s address and bytes (`Exe.seg`). -/
def codeWithout (code : List (Addr × List Byte)) (m : Addr × List Byte) : List (Addr × List Byte) :=
  code.flatMap (segWithout m)

end ZellicX86
