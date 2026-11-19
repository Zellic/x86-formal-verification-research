import Glibc243Ubuntu.LibcA
import Glibc243Ubuntu.MemrchrFixedObjs
import ZellicX86.Spec.Lib.C.String
import ZellicX86.Spec.Executable
/-!
# What glibc's `memrchr` is proved to do: the statements

Seven statements about glibc 2.43's `memrchr` (`ZellicX86.C.memrchr`: `memrchr(s, c, n)` returns in `rax` the address
of the last byte equal to `c` among the `n` bytes at `s`, or null; the object readable and apart from the return
address's slot, nothing written but that slot, no system call), each of one function of one object, all in one form,
`FnHolds o "fn" needs C`: every link places the object's function, and at every link that places it at an address, in
any code holding its bytes there, on every processor with the features `needs`, the code implements `C` there. This
file imports only the model, the vocabulary and the loader, so that a reader of the statements needs none of the proofs.

The four variants in the build's `libc.a` (`LibcA.blob`, the Ubuntu package's file by its SHA-256), each with what
it is proved for, named here:
- `__memrchr_evex` (`evexHolds`): the calls with `n < 2 ^ 32` (`evexOk`); for larger objects its result can be wrong
  (`evexBug`);
- `__memrchr_avx2` and `__memrchr_avx2_rtm` (`avx2Holds`, `avx2RtmHolds`): the objects that start at or past address 32
  (`avx2Ok`); below, where page 0 is mapped, its address arithmetic wraps and it returns `(void *) -1` for a byte not
  found;
- `__memrchr_sse2` (`sse2Holds`): every call, the code reading the 16 bytes before `s` in a call with `n = 0` where
  `s mod 4096 ≥ 16` (`sse2Reads`: so those must be readable then; the code loads them there and ignores them, a load
  glibc's source documents as deliberate; C asks `s` to be valid even at `n = 0`, which gives less than this). Where
  `s mod 4096 < 16` a call with `n = 0` reads nothing (`s` may be 0…15, or a page's start after an unmapped page).

The two variants with their bugs fixed (`MemrchrFixedObjs.lean`: glibc's source with a patch, assembled as glibc's build
does), each for every call, so that each differs from its shipped statement only in the object and the dropped
carve-out: `evexFixedHolds`, `avx2FixedHolds`.

And the evex bug itself (`evexBug`): the shipped `__memrchr_evex` does not implement `memrchr`'s contract for every
call.
-/
open ZellicX86

namespace Glibc243Ubuntu.Memrchr

/-- `__memrchr_evex`'s carve-out: the calls with `n < 2 ^ 32` (`rdx`). -/
abbrev evexOk (s : State) : Prop := s.cpu.gpr.rdx.toNat < 2 ^ 32

/-- `__memrchr_avx2`'s carve-out: the objects that start at or past address 32 (`rdi`). -/
abbrev avx2Ok (s : State) : Prop := 32 ≤ s.cpu.gpr.rdi.toNat

/-- The 16 bytes before `s` (`rdi`). -/
def before16 (s : State) : Rgn := ⟨s.cpu.gpr.rdi - 16, 16⟩

/-- What `__memrchr_sse2` reads besides the object: the 16 bytes before `s` in a call with `n = 0` where `s` does not
lie in the first 16 bytes of a page, `s mod 4096 ≥ 16` (the code's own branch: it tests `(s + n) mod 4096 < 16` first
and loads the 16 bytes before `s + n` only where that fails). -/
def sse2Reads (s : State) : List Rgn :=
  if s.cpu.gpr.rdx.toNat = 0 ∧ 16 ≤ s.cpu.gpr.rdi.toNat % 4096 then [before16 s] else []

/-- The features `__memrchr_evex`'s instructions need: AVX-512F, AVX-512VL, AVX-512BW, LZCNT and BMI2. -/
def evexNeeds (f : Features) : Prop :=
  f.avx512f = true ∧ f.avx512vl = true ∧ f.avx512bw = true ∧ f.lzcnt = true ∧ f.bmi2 = true

/-- The features `__memrchr_avx2`'s instructions need: AVX, AVX2, LZCNT and BMI2. -/
def avx2Needs (f : Features) : Prop := f.avx = true ∧ f.avx2 = true ∧ f.lzcnt = true ∧ f.bmi2 = true

/-- The features `__memrchr_avx2_rtm`'s instructions need: those of `avx2Needs` and RTM. -/
def avx2RtmNeeds (f : Features) : Prop := avx2Needs f ∧ f.rtm = true

/-- **`__memrchr_evex`** of `libc.a`'s `memrchr-evex.o` implements `memrchr`'s contract for the calls with
`n < 2 ^ 32`. -/
def evexHolds : Prop :=
  FnHolds (Ar.member LibcA.blob "memrchr-evex.o") "__memrchr_evex" evexNeeds (C.memrchrWith (pre := evexOk))

/-- **`__memrchr_avx2`** of `libc.a`'s `memrchr-avx2.o` implements `memrchr`'s contract for the objects that start at or
past address 32. -/
def avx2Holds : Prop :=
  FnHolds (Ar.member LibcA.blob "memrchr-avx2.o") "__memrchr_avx2" avx2Needs (C.memrchrWith (pre := avx2Ok))

/-- **`__memrchr_avx2_rtm`** of `libc.a`'s `memrchr-avx2-rtm.o` implements `memrchr`'s contract for the objects that start
at or past address 32. -/
def avx2RtmHolds : Prop :=
  FnHolds (Ar.member LibcA.blob "memrchr-avx2-rtm.o") "__memrchr_avx2_rtm" avx2RtmNeeds
    (C.memrchrWith (pre := avx2Ok))

/-- **`__memrchr_sse2`** of `libc.a`'s `memrchr-sse2.o` implements `memrchr`'s contract for every call, on every
processor, reading the 16 bytes before `s` in a call with `n = 0` where `s mod 4096 ≥ 16`. -/
def sse2Holds : Prop :=
  FnHolds (Ar.member LibcA.blob "memrchr-sse2.o") "__memrchr_sse2" (fun _ => True)
    (C.memrchrWith (alsoReads := sse2Reads))

/-- **`__memrchr_evex` with its bug fixed** (`fixed/memrchr-evex-fixed.o`) implements `memrchr`'s contract for every
call. -/
def evexFixedHolds : Prop := FnHolds MemrchrEvexFixedO.blob "__memrchr_evex" evexNeeds C.memrchr

/-- **`__memrchr_avx2` with its bug fixed** (`fixed/memrchr-avx2-fixed.o`) implements `memrchr`'s contract for every
call. -/
def avx2FixedHolds : Prop := FnHolds MemrchrAvx2FixedO.blob "__memrchr_avx2" avx2Needs C.memrchr

/-- **The evex bug**: `libc.a`'s `__memrchr_evex` does not implement `memrchr`'s contract for every call. A negation of
`FnHolds` means something only beside a proof that every link places the function, which `evexHolds` gives (and
`evexFixedHolds` for the same code with the fix): together they say that the code itself fails the contract on some call
(its proof exhibits one: an object of `2 ^ 32` bytes whose last byte, in a page's first 32 bytes, is the byte looked
for). -/
def evexBug : Prop :=
  ¬ FnHolds (Ar.member LibcA.blob "memrchr-evex.o") "__memrchr_evex" evexNeeds C.memrchr

end Glibc243Ubuntu.Memrchr
