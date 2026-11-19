import ZellicX86.Spec.Statement
/-!
# Statement vocabulary: the C library's `memrchr`

A library layer over the statement vocabulary (`Spec/Statement.lean`): what a C library's `memrchr(s, c, n)` does, as a
contract any library's code can be held to. `memrchr` is a GNU extension (glibc's manual, "Search Functions"): "The
function `memrchr` is like `memchr`, except that it searches backwards from the end of the block defined by `block` and
`size` (instead of forwards from the front)". So, as C17 7.24.5.1 says of `memchr`, it looks at the `n` bytes at `s`
(each as an `unsigned char`) for the value `c` converted to an `unsigned char`, and returns a pointer to the last such
byte, or a null pointer if there is none: the meaning glibc's manual and C17's `memchr` give it. (Code need not keep it
for every call: a variant's contract may narrow it or let it read more, `memrchrWith`.)

The contract (`memrchr`):
- the call follows the System V x86-64 calling convention (`sysv`): `s`, `c`, `n` in `rdi`, `rsi` (its low byte is
  `c`), `rdx` (a `size_t`, any 64-bit value);
- the `n` bytes at `s` (`memrchrObject`) are readable memory and do not overlap the slot of the return address (as at
  every call, `CallOf.frameApart`);
- it returns, with `rax` the address of the last byte equal to `c` among them, or 0 if there is none (`memrchrResult`,
  `lastIndex`); it writes no memory but the slot of its return address and makes no system call;
- no one disturbs the run from outside (`Undisturbed`, a contract's default environment).

Nothing is said about bytes outside the object: code may read them where it cannot fault (a vector load that stays on the
object's pages), but its result may not depend on them, and a call must not need them readable.

`memrchrWith (pre := p) (alsoReads := r)` is the same contract with two changes, each named at its use and absent unless
given (`memrchr` is `memrchrWith` with neither):
- `pre`: for the calls whose entry state satisfies `p` only. A statement about code that meets the contract only on some
  calls names those calls by `p` (glibc 2.43's `__memrchr_evex` for `n < 2 ^ 32`: a bug's carve-out);
- `alsoReads`: the regions `r s` the code may read besides the object, which a call must then have readable with every
  condition a region read has (`Contract.probes`: readable, not the kernel's, no alias; not required apart from the
  return address's slot), while the result still depends on the object's bytes only (glibc 2.43's `__memrchr_sse2`
  loads the 16 bytes before `s` in a call with `n = 0` where `s mod 4096 ≥ 16`, deliberately; C asks `s` to be valid
  even at `n = 0`, which gives less than these conditions).
-/
namespace ZellicX86.C

/-- The index of the last byte `c` in `bs`, if there is one: the first in the reversed list, counted from the
front. -/
def lastIndex (bs : List Byte) (c : Byte) : Option Nat :=
  (bs.reverse.findIdx? (· == c)).map (bs.length - 1 - ·)

/-- The object `memrchr` searches in a call from `s`: the `n` bytes at `s` (`rdx` bytes at `rdi`). -/
def memrchrObject (s : State) : Rgn := ⟨s.cpu.gpr.rdi, s.cpu.gpr.rdx.toNat⟩

/-- `memrchr`'s result for a call from `s`: the address of the last byte equal to `c` (the low byte of `rsi`) among the
`n` bytes at `s`, or null. -/
def memrchrResult (s : State) : Addr :=
  match lastIndex (readBytes s.proc.mm.mem s.cpu.gpr.rdi s.cpu.gpr.rdx.toNat) (s.cpu.gpr.rsi.setWidth 8) with
  | some i => s.cpu.gpr.rdi + BitVec.ofNat 64 i
  | none => 0

/-- `memrchr`'s contract for the calls from a state satisfying `pre` (every call unless given), the code reading the
regions `alsoReads` (none unless given) besides the object: the object readable (and apart from the return address's
slot, as at every call: `CallOf`), the regions `alsoReads` readable as probed regions (`Contract.probes`); `rax` is
`memrchrResult`; it writes only that slot and makes no system call. -/
def memrchrWith (pre : State → Prop := fun _ => True) (alsoReads : State → List Rgn := fun _ => []) : Contract where
  conv := sysv
  reads s := [memrchrObject s]
  stack := fun _ => 0
  writes _ := []
  probes := alsoReads
  pre := pre
  post s X := X.cpu.gpr.rax = memrchrResult s
  events _ _ evs := evs = []

/-- `memrchr`'s contract, for every call, reading nothing besides the object. -/
abbrev memrchr : Contract := memrchrWith

end ZellicX86.C
