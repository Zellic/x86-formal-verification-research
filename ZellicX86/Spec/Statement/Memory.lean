import ZellicX86.Spec.Step
/-!
# Statement vocabulary: regions and memory facts

The first part of the statement vocabulary (`Spec/Statement.lean` imports it): regions of virtual addresses and what
a statement says about the memory behind them, in the model's terms of pages, backings and files (`Spec/Memory.lean`).

- Regions (`Rgn`, `Rgn.Mem`, `Rgn.Fits`, `EndsBeforeLastPage`), the addresses of a list of them (`Foot`), regions apart (`Disjoint`, `Apart`).
- Facts about the memory behind regions in a state: accessible (`Accessible`), where a byte is stored (`byteLoc`,
  `byteAt`), no aliasing (`NoAliasOver`), not in a page the kernel owns or may drop (`NotKernel`), not shared
  (`NotShared`), not in a page whose unmapping is not modelled (`NotFixed`); their contents (`Bytes`, `SameBytes`,
  `Word`, `CodeBytes`), read as numbers and addresses (`State.byte`, `readNat`, `readAddr`).
- What changed between two states: only the memory behind given regions (`ChangesOnly`), and a backing as stores
  change it (`Backing.Refines`).

Addresses are virtual. Aliasing is excluded only where a statement says so
(`NoAliasOver`): two virtual pages may share a backing.
-/
namespace ZellicX86

/-! ## Regions and memory facts -/

/-- The virtual addresses `base, ..., base + len - 1`, as numbers: a region does not wrap
around `2 ^ 64` (one that would is cut there). -/
structure Rgn where
  base : Addr
  len : Nat

/-- `a` lies in region `r`. -/
def Rgn.Mem (r : Rgn) (a : Addr) : Prop :=
  r.base.toNat ≤ a.toNat ∧ a.toNat < r.base.toNat + r.len

/-- Region `r` does not reach past the top of the address space, so it holds all of
`base, ..., base + len - 1` (a region is cut at `2 ^ 64`, whereas address arithmetic wraps). -/
def Rgn.Fits (r : Rgn) : Prop := r.base.toNat + r.len ≤ 2 ^ 64

/-- The `n` bytes from `a` end before the 64-bit address space's last page, at `2 ^ 64 - 4096`. Linux maps no page of a
process there: its mappings end at `TASK_SIZE` (`taskSize`), and the page of the legacy vsyscall area (`vsyscallPage`,
above `TASK_SIZE`) ends below it too. Code that computes the start of the page after a buffer's (a string function's
page-cross path) relies on it, since there that start would wrap around `2 ^ 64`. A contract may ask it of a region its
function reads at no cost to its callers: every byte a call reads is on a mapped page (`Footprint.Ok`, `Accessible`), and
every mapped page lies below it (`LayoutOk`, `Ready`). -/
def EndsBeforeLastPage (a : Addr) (n : Nat) : Prop := a.toNat + n ≤ 2 ^ 64 - 4096

/-- `a` lies in one of the regions `rs`. -/
def Foot (rs : List Rgn) (a : Addr) : Prop := ∃ r ∈ rs, r.Mem a

instance (r : Rgn) (a : Addr) : Decidable (r.Mem a) := inferInstanceAs (Decidable (_ ∧ _))

instance (rs : List Rgn) (a : Addr) : Decidable (Foot rs a) :=
  inferInstanceAs (Decidable (∃ r ∈ rs, r.Mem a))

/-- No address lies in both regions. -/
def Disjoint (r q : Rgn) : Prop := ∀ a, r.Mem a → ¬ q.Mem a

/-- Every region of `rs` is disjoint from every region of `qs`. -/
def Apart (rs qs : List Rgn) : Prop := ∀ r ∈ rs, ∀ q ∈ qs, Disjoint r q

/-- Every byte of `r` is canonical and allows access `acc` in `s` on a processor with
features `feat` (`Memory.check`, with the thread's `PKRU`). -/
def Accessible (feat : Features) (s : State) (acc : Access) (r : Rgn) : Prop :=
  ∀ a, r.Mem a → a.canonical feat.la57 = true ∧ s.proc.mm.mem.check feat s.cpu.pkru acc a = none

/-- Where the byte at virtual address `a` is stored in `s`, if its page is mapped. -/
def byteLoc (s : State) (a : Addr) : Option ByteLoc :=
  (s.proc.mm.mem.map (pageOf a)).map fun m => ⟨m.backing, pageOffset a⟩

/-- Among the addresses of the regions `rs`, distinct virtual pages have distinct backings,
and if one of them is a shared mapping of a file page, no other is a mapping of the same file
page, shared or private and not yet copied (a private mapping reads the file page until its
first store, `Backing.cow`). So a store to one of these addresses changes no other of them. -/
def NoAliasOver (s : State) (rs : List Rgn) : Prop :=
  ∀ a b, Foot rs a → Foot rs b → pageOf a ≠ pageOf b →
    ∀ m n, s.proc.mm.mem.map (pageOf a) = some m → s.proc.mm.mem.map (pageOf b) = some n →
      m.backing ≠ n.backing ∧
      ∀ fp, s.proc.mm.mem.backings m.backing = .file fp →
        s.proc.mm.mem.backings n.backing ≠ .file fp ∧ s.proc.mm.mem.backings n.backing ≠ .cow fp

/-- No byte of the regions `rs` is stored in a page the kernel owns (`Backing.kernel`, such as
the vDSO data page) or may drop (`Backing.freed`, lazily freed by `madvise(MADV_FREE)`). The kernel
may rewrite or drop such pages between any two instructions (`EnvEvent.kernelData`,
`EnvEvent.reclaim`), also in a run that is `Undisturbed`, so facts about the contents of `rs` hold
over a run only where this does. -/
def NotKernel (s : State) (rs : List Rgn) : Prop :=
  ∀ a, Foot rs a → ∀ m, s.proc.mm.mem.map (pageOf a) = some m →
    (∀ f, s.proc.mm.mem.backings m.backing ≠ .kernel f) ∧ ∀ f, s.proc.mm.mem.backings m.backing ≠ .freed f

/-- No byte of the regions `rs` is stored in a shared mapping (`MAP_SHARED`, `Backing.file`):
they are anonymous memory or private file mappings. A store to a shared mapping writes the file
page, and so changes every other mapping of that page too, inside `rs` or not. -/
def NotShared (s : State) (rs : List Rgn) : Prop :=
  ∀ a, Foot rs a → ∀ m, s.proc.mm.mem.map (pageOf a) = some m →
    ∀ fp, s.proc.mm.mem.backings m.backing ≠ .file fp

/-- No byte of the regions `rs` lies in a page of a special mapping the kernel installs (the vDSO's,
`Mapping.special`) or in the initial stack's first page as `execve` mapped it (`Memory.growsDown`; the
stack's growth maps pages below it, which are not such pages): pages whose unmapping or remapping the model
leaves not modelled (`Memory.touchesFixed`). What
an allocator owns is ordinary memory it may give back (`munmap`, lowering the break). -/
def NotFixed (s : State) (rs : List Rgn) : Prop :=
  ∀ a, Foot rs a → (∀ m, s.proc.mm.mem.map (pageOf a) = some m → m.special = false) ∧
    pageOf a ∉ s.proc.mm.mem.growsDown

/-- The bytes at `a` in `s` are `bs` (as memory holds them; whether they are accessible is
a separate fact, `Accessible`). -/
def Bytes (s : State) (a : Addr) (bs : List Byte) : Prop :=
  readBytes s.proc.mm.mem a bs.length = bs

/-- Every byte of the regions `rs` is in `s` as it was in `s₀` (as memory holds them, read at
their virtual addresses). -/
def SameBytes (s₀ s : State) (rs : List Rgn) : Prop :=
  ∀ a, Foot rs a → s.proc.mm.mem.readByte a = s₀.proc.mm.mem.readByte a

/-- The 8-byte little-endian word at `a` in `s` is `v` (as memory holds it, `0` for a byte no page
maps, addresses modulo `2 ^ 64`; whether it is accessible is a separate fact, `Accessible`). -/
def Word (s : State) (a : Addr) (v : BitVec 64) : Prop :=
  ofBytesLE 64 (readBytes s.proc.mm.mem a 8) = v

/-- The byte at `a` in `s`, as memory holds it, and `0` at an address no page maps (`Memory.readByte`):
the bytes of a state for `readNat` and `readAddr` (`readNat s.byte a n`). Whether it is mapped and
accessible is a separate fact, so a statement that reads memory this way pairs it with `Accessible` (or
a region `ImplementsCall` assumes readable) for the bytes it reads. -/
def State.byte (s : State) (a : Addr) : Byte := s.proc.mm.mem.readByte a

/-- The `n`-byte little-endian number at `a` in the bytes `v`: of the bytes at `a`, `a + 1`, …,
`a + n - 1` (addresses modulo `2 ^ 64`), the first the least significant. `v` is the bytes of a state
(`State.byte`) or what an allocator's invariant sees of them (`Heap.View.bytes`). How C code reads an
unsigned integer field of `n` bytes on x86-64; a bit field is read from the bytes that hold it. -/
def readNat (v : Addr → Byte) (a : Addr) (n : Nat) : Nat := (ofBytesLE (8 * n) ((byteAddrs a n).map v)).toNat

/-- The address stored in the 8 bytes at `a` in the bytes `v`, little-endian (a pointer field, as
`readNat v a 8`, as an address). -/
def readAddr (v : Addr → Byte) (a : Addr) : Addr := ofBytesLE 64 ((byteAddrs a 8).map v)

/-- The code at `base` is `code`: those bytes are executable and hold `code` (for example, taken
from the ELF file). -/
def CodeBytes (feat : Features) (s : State) (base : Addr) (code : List Byte) : Prop :=
  Accessible feat s .fetch ⟨base, code.length⟩ ∧ Bytes s base code

/-- The byte stored at `l` in `s`. -/
def byteAt (s : State) (l : ByteLoc) : Byte :=
  (s.proc.mm.mem.backings l.backing).frame s.proc.mm.mem.files l.offset

/-- From `s₀` to `s`, only memory behind the addresses of `foot` (under `s₀`'s page map)
changed: every other byte of every backing some page maps in `s₀` and the kernel neither owns nor
may drop, and every file page a backing of `s` maps, is as in `s₀`. Pages the kernel owns
(`Backing.kernel`) or may drop (`Backing.freed`) may change in any run (`EnvEvent.kernelData`,
`EnvEvent.reclaim`), so no statement about them is made. Backings no page maps in `s₀` are no
address's: the bytes of a mapping made since (`mmap`, `brk`) are in new backings (`Memory.fresh`),
which are not the caller's concern. A byte is read as its backing holds it: a private file mapping
not yet copied reads its file page, so it changes when the file page does. -/
def ChangesOnly (s₀ s : State) (foot : List Rgn) : Prop :=
  (∀ l, (∃ a, byteLoc s₀ a = some l) → (∀ f, s₀.proc.mm.mem.backings l.backing ≠ .kernel f) →
      (∀ f, s₀.proc.mm.mem.backings l.backing ≠ .freed f) →
      (∀ a, Foot foot a → byteLoc s₀ a ≠ some l) → byteAt s l = byteAt s₀ l) ∧
  (∀ fp o, (∃ j, (s.proc.mm.mem.backings j).filePage = some fp) →
    (∀ a, Foot foot a → ∀ m, s₀.proc.mm.mem.map (pageOf a) = some m →
      s₀.proc.mm.mem.backings m.backing ≠ .file fp ∨ pageOffset a ≠ o) →
    s.proc.mm.mem.files.page fp o = s₀.proc.mm.mem.files.page fp o)

/-- `Backing.Refines fs b' b`: backing `b'` can arise from `b` (with files `fs`) by the process's
stores and the kernel's updates, without `mmap`, `munmap` or `mremap`: the same kind and, for a file page, the same page,
for a kernel page with or without a source as before, except that a private file mapping not yet written becomes a private copy at its first store
(copy on write, `mm/memory.c` `do_wp_page`), which happens only for a page within the file, since
an access to one beyond the end raises `SIGBUS` (`Files.beyondEof`), and that a lazily freed page
becomes private memory again at a store or when the kernel drops it (`EnvEvent.reclaim`). -/
def Backing.Refines (fs : Files) : Backing → Backing → Prop
  | .priv _, .priv _ => True
  | .priv _, .freed _ => True
  | .freed _, .freed _ => True
  | .kernel f', .kernel f => f'.isSome = f.isSome
  | .priv _, .cow fp => fs.beyondEof fp = false
  | .cow fp', .cow fp => fp' = fp
  | .file fp', .file fp => fp' = fp
  | _, _ => False

end ZellicX86
