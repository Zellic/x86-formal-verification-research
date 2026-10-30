import ZellicX86.Spec.Word
import ZellicX86.Spec.Profile
/-!
# Memory

The process's virtual address space as the processor and Linux let user code observe it.

- A **page map** sends each 4 KiB virtual page to a *mapping* (permissions, protection key,
  backing) or to nothing.
- Contents are stored per **backing**, not per virtual page. Two virtual pages with the same
  backing alias: a store through one is visible through the other.
- A private file mapping gets its own backing when it is created. That backing follows
  the file page (it sees other writers' changes to the file) until it becomes a private copy
  (copy-on-write, `mm/memory.c` `do_wp_page`): at the process's first write to it, or earlier
  when the kernel makes the copy for another reason (`EnvEvent.cowBreak`). The copy happens
  inside the backing store, so a store never changes the page map. When the file is truncated, the
  copies of its pages beyond the new end are dropped (`Memory.truncate`).
- A shared mapping's pages are file pages (shared anonymous memory too: Linux backs it by a
  shmem file of its own, `FileId.shmem`). File contents and sizes are part of the state, since
  other agents may change them, and so may the process (stores to shared mappings, `write(2)`).
- New mappings (`mmap`, `brk`) get backings no page uses yet (`Memory.fresh`), so they share
  nothing with existing ones.
- Private anonymous memory freed lazily (`madvise(MADV_FREE)`) keeps its contents until the kernel
  drops it (`Backing.freed`).

Page tables, demand paging and page-cache details are not visible to user code and are not
modelled. Sources: Linux v6.18 `mm/mmap.c`, `mm/memory.c`, `mm/filemap.c`, `mm/shmem.c`;
Intel SDM Vol. 3A, 5.6 "Access Rights", 5.6.2 "Protection Keys", 5.7 "Page-Fault Exceptions".
-/
namespace ZellicX86

/-- A virtual page number: bits 63–12 of a linear address. -/
abbrev PageNum := BitVec 52

/-- The page containing address `a`. -/
def pageOf (a : Addr) : PageNum := a.extractLsb' 12 52

/-- The offset of address `a` within its page. -/
def pageOffset (a : Addr) : BitVec 12 := a.extractLsb' 0 12

/-- The contents of one 4 KiB page. -/
abbrev Frame := BitVec 12 → Byte

/-- The identity of a file whose pages can be mapped. -/
inductive FileId
  /-- A file of the file systems (a regular file, a tmpfs or memfd file, a block device), identified
  by an opaque number (its device and inode number). -/
  | inode (n : Nat)
  /-- The shmem file the kernel creates for a shared anonymous mapping of this process
  (`mm/shmem.c` `shmem_zero_setup`), on the kernel's internal mount, which no path reaches: it is
  no file of the file systems. Numbered by `Memory.fresh` when it is created. Other agents may
  still write it (`EnvEvent.fileWrite`): an agent privileged to open it through
  `/proc/PID/map_files` (`CAP_CHECKPOINT_RESTORE`) can. -/
  | shmem (n : Nat)
  deriving DecidableEq, Repr

/-- Page `index` (bytes `4096 * index` to `4096 * index + 4095`) of the file `file`. -/
structure FilePage where
  file : FileId
  index : Nat
  deriving DecidableEq, Repr

/-- The protection a mapping was created or last changed with (`PROT_READ`, `PROT_WRITE`,
`PROT_EXEC` of `mmap(2)`/`mprotect(2)`). What the hardware then allows is `Mapping.allows`. -/
structure Prot where
  read : Bool
  write : Bool
  exec : Bool
  deriving DecidableEq, Repr

/-- Whether protection `p` asks for nothing `max` lacks. -/
def Prot.within (p max : Prot) : Bool :=
  (!p.read || max.read) && (!p.write || max.write) && (!p.exec || max.exec)

/-- What a mapped virtual page refers to. -/
structure Mapping where
  prot : Prot
  /-- The backing holding the page's contents (an index into `Memory.backings`). -/
  backing : Nat
  /-- The protection key of the page (`pkey_mprotect(2)`; 0 unless assigned). -/
  pkey : BitVec 4
  /-- A page the kernel installs specially (vDSO code/data or the legacy vsyscall gate).
  For the vDSO (`_install_special_mapping`, `mm/mmap.c`), the kernel neither splits nor grows it
  (`special_mapping_split`, `VM_DONTEXPAND`), and with `CONFIG_MSEAL_SYSTEM_MAPPINGS` seals it, so
  system calls that change its layout are not modelled. The vsyscall gate is outside the ordinary
  VMA tree (`vsyscall_64.c`); VMA operations treat its page as unmapped. -/
  special : Bool
  /-- For a page of a file mapping, the file page it maps (the mapping's file and offset,
  `vm_file` and `vm_pgoff`), also after the process's first write made the page a private copy:
  `madvise(MADV_DONTNEED)` drops the copy, so that the page shows the file page again, and growing
  the mapping (`mremap(2)`) maps the file pages after it. `none` for anonymous memory and the
  vDSO. -/
  origin : Option FilePage
  /-- The area the page belongs to: contiguous pages with the same area are in one VMA, the kernel's
  unit of mapping (`struct vm_area_struct`); pages of different areas may or may not be, as the
  kernel merges adjacent VMAs of the same kind at its discretion (`mm/vma.c`). A new mapping is a
  new area; a change that may split a VMA (`mprotect`, `madvise` advice that changes VMA flags, a
  move) gives the pages it covers new areas (`Memory.renumber`); `mremap` growing a mapping in place
  extends its area. What `mremap` may do depends on it. -/
  area : Nat
  /-- The protection `mprotect(2)` may give the page (`VM_MAYREAD`, `VM_MAYWRITE`, `VM_MAYEXEC`):
  every protection for anonymous memory and private file mappings; a shared mapping of a file not
  open for writing, or of a write-sealed memfd, may not be made writable, a mapping of a file on a
  `noexec` mount not executable (`mm/mmap.c` `do_mmap`, `mm/memfd.c` `check_write_seal`); the
  vDSO's data pages may only be read. -/
  maxProt : Prot
  /-- The page's VMA grows down on a fault below it (`VM_GROWSDOWN`, `growStack`): the initial stack's
  pages and those it grew to, also after a split of its VMA (`mm/vma.c` `__split_vma` copies the
  flags). No other mapping the model creates grows down. -/
  growsDown : Bool

/-- The contents behind a mapping. -/
inductive Backing
  /-- Memory private to the process: anonymous memory, or a private copy of a file page. -/
  | priv (f : Frame)
  /-- A page the kernel owns and writes at any time (the vDSO's data pages,
  `arch/x86/entry/vdso/vma.c`, `lib/vdso/datastore.c`), with its current contents, or `none`
  for a page whose source this system does not have (the time-namespace page outside a time
  namespace, a paravirtual-clock page without that clock): the mapping's fault handler then
  returns `VM_FAULT_SIGBUS`, so every access raises `SIGBUS`. Whether a page has a source does
  not change while the process runs. -/
  | kernel (f : Option Frame)
  /-- A private file mapping not yet written by the process: reads see the file page's
  current contents. -/
  | cow (fp : FilePage)
  /-- A shared file mapping (`MAP_SHARED`, including shared anonymous memory, which Linux
  backs by a `shmem` file): reads and writes go to the file page. -/
  | file (fp : FilePage)
  /-- Private anonymous memory freed lazily (`madvise(MADV_FREE)`, `mm/madvise.c`
  `madvise_free_pte_range`), with its contents `f`: reads see `f` until the kernel drops the page
  (`EnvEvent.reclaim`, at any time, when it needs memory), after which it is zeros; a store first
  keeps the page, with its old contents and the store (`writeByte`). The kernel may drop the page
  at any instant, on another CPU; here it drops it between two instructions (or iterations of a
  repeated string instruction), so an instruction that reads such a page and then writes it (an
  unlocked read-modify-write) sees the page either before or after the drop, where the kernel may
  let the read see the old bytes and the write land on the zeros. -/
  | freed (f : Frame)

/-- Where a byte is stored: a backing and the offset within its page. -/
structure ByteLoc where
  backing : Nat
  offset : BitVec 12
  deriving DecidableEq

/-- Files as seen through mappings. -/
structure Files where
  /-- Current contents of each file page. -/
  page : FilePage → Frame
  /-- Current size in bytes of each file. -/
  size : FileId → Nat
  /-- Files no other agent can write or truncate while the process runs: a running
  executable (`fs/exec.c` `exe_file_deny_write_access`; `ETXTBSY`). -/
  denyWrite : FileId → Bool
  /-- Regular files (`S_ISREG`: a file of a disk file system, a `tmpfs` or memfd file), as opposed to
  the other files with pages, block devices, whose pages run to the device's size (`size` here,
  `bdev_nr_bytes`) while `fstat` reports the size of the device file's own inode (0), and whose writes
  the kernel limits by the device's end rather than by `RLIMIT_FSIZE` (`block/fops.c`
  `blkdev_write_iter`). For a regular file `fstat`'s size
  is `size` (`generic_fillattr`, `i_size_read`) and `write` checks the file size limit
  (`generic_write_check_limits`). -/
  regular : FileId → Bool

/-- Whether page number `p` lies in one of the runs `rs` (first page number, number of pages). -/
def inRuns (rs : List (Nat × Nat)) (p : Nat) : Bool := rs.any fun (f, n) => decide (f ≤ p ∧ p < f + n)

/-- The address space. -/
structure Memory where
  map : PageNum → Option Mapping
  backings : Nat → Backing
  files : Files
  /-- The first page of the initial stack as `execve` mapped it (`MAP_GROWSDOWN` is not modelled):
  system calls that unmap or replace it are not modelled (`Memory.touchesFixed`). A growth of the
  stack maps pages below it and leaves it in the stack (`growStack`). -/
  growsDown : List PageNum
  /-- Where the backings and the areas (`Mapping.area`) of new mappings start: no mapping uses an
  index from here on (`execve` makes it so, and each change that takes new ones moves it past
  them). -/
  fresh : Nat
  /-- Runs of pages (first page number, number of pages) outside which no page is mapped (`covers`).
  For evaluation only: no definition of the model reads it, and it restricts nothing, since every page
  map has one (all `2 ^ 52` pages). The search for the next mapped page (`Memory.nextMapped`) is
  evaluated over it (`Spec/MemoryEval.lean`), instead of page by page across unmapped space. Each change
  of the layout states its cover: the old one, with the run of pages it maps added. -/
  cover : List (Nat × Nat)
  covers : ∀ p : PageNum, (map p).isSome = true → inRuns cover p.toNat = true

/-- The kind of a memory access. -/
inductive Access
  | read
  | write
  /-- An instruction fetch. -/
  | fetch
  deriving DecidableEq, Repr

/-- Why an access to a canonical address faults. -/
inductive AccessFault
  /-- No mapping, a file page wholly beyond the end of the file, or a kernel page without a
  source. -/
  | notPresent
  /-- The mapping's permissions forbid the access, and its protection key does not. -/
  | protection
  /-- The page's protection key forbids the access (`PKRU`), whether or not its permissions do: the
  page-fault error code's PK bit (SDM Vol. 3A, 5.7; an AMD Zen 4 sets it also when the permissions
  forbid the access). -/
  | pkey
  deriving DecidableEq, Repr

/-- Whether file page `fp` lies wholly beyond the end of its file. An access to such a page
raises `SIGBUS` (`mm/filemap.c` `filemap_fault`). Bytes of the last page past the end read as
the page holds them (Linux zero-fills them when it reads the page in). -/
def Files.beyondEof (fs : Files) (fp : FilePage) : Bool :=
  decide (fs.size fp.file ≤ 4096 * fp.index)

/-- The file page behind a backing, if any. -/
def Backing.filePage : Backing → Option FilePage
  | .cow fp | .file fp => some fp
  | .priv _ | .kernel _ | .freed _ => none

/-- Whether a backing is a kernel page without a source (`Backing.kernel none`). -/
def Backing.noSource : Backing → Bool
  | .kernel none => true
  | _ => false

/-- The current contents of a backing (zeros for a kernel page without a source, which cannot
be read). -/
def Backing.frame (fs : Files) : Backing → Frame
  | .priv f | .freed f => f
  | .kernel f => f.getD fun _ => 0
  | .cow fp | .file fp => fs.page fp

/-- Whether the hardware lets user mode perform access `acc` on a page of mapping `m`,
ignoring protection keys (SDM Vol. 3A, 5.6.1). On x86 every present user page is readable,
so write-only and execute-only mappings are readable (Linux can make execute-only mappings
unreadable only with a protection key, `arch/x86/mm/pkeys.c`). Without the execute-disable
bit every readable page is executable. -/
def Mapping.allows (feat : Features) (m : Mapping) : Access → Bool
  | .read => m.prot.read || m.prot.write || m.prot.exec
  | .write => m.prot.write
  | .fetch => m.prot.exec || (!feat.nx && (m.prot.read || m.prot.write))

/-- Whether `PKRU` forbids data access `acc` to pages with key `k` (SDM Vol. 3A, 5.6.2):
bit `2k` (AD) disables all data access, bit `2k+1` (WD) disables writes. Fetches are not
checked. -/
def pkeyDenies (pkru : BitVec 32) (k : BitVec 4) : Access → Bool
  | .read => pkru.getLsbD (2 * k.toNat)
  | .write => pkru.getLsbD (2 * k.toNat) || pkru.getLsbD (2 * k.toNat + 1)
  | .fetch => false

/-- Check access `acc` to the byte at canonical address `a`: whether its page is not present, else
whether the page's protection key forbids the access, else whether its permissions do. -/
def Memory.check (feat : Features) (pkru : BitVec 32) (mem : Memory) (acc : Access)
    (a : Addr) : Option AccessFault :=
  match mem.map (pageOf a) with
  | none => some .notPresent
  | some m =>
    match (mem.backings m.backing).filePage with
    | some fp => if mem.files.beyondEof fp then some .notPresent else rest m
    | none => if (mem.backings m.backing).noSource then some .notPresent else rest m
where
  rest (m : Mapping) : Option AccessFault :=
    if feat.pku && pkeyDenies pkru m.pkey acc then some .pkey
    else if !m.allows feat acc then some .protection
    else none

/-- The byte at address `a` of a mapped page (0 for an unmapped page; callers check first). -/
def Memory.readByte (mem : Memory) (a : Addr) : Byte :=
  match mem.map (pageOf a) with
  | none => 0
  | some m => (mem.backings m.backing).frame mem.files (pageOffset a)

/-- A frame of zeros. -/
def zeroFrame : Frame := fun _ => 0

/-- `f` with byte `o` replaced by `v`. -/
def Frame.set (f : Frame) (o : BitVec 12) (v : Byte) : Frame :=
  fun x => if x = o then v else f x

/-- `mem` with backing `i` replaced by `b`. -/
def Memory.setBacking (mem : Memory) (i : Nat) (b : Backing) : Memory :=
  { mem with backings := fun j => if j = i then b else mem.backings j }

/-- `fs` with the contents of file page `fp` replaced by `f`. -/
def Files.setPage (fs : Files) (fp : FilePage) (f : Frame) : Files :=
  { fs with page := fun p => if p = fp then f else fs.page p }

/-- `fs` with the size of file `file` set to `n`. -/
def Files.setSize (fs : Files) (file : FileId) (n : Nat) : Files :=
  { fs with size := fun i => if i = file then n else fs.size i }

/-- Store byte `v` at address `a` of a mapped page. A `cow` backing becomes a private copy
of its file page first, a `freed` one private memory again. A `file` backing writes the file page,
so every mapping of it sees the change. -/
def Memory.writeByte (mem : Memory) (a : Addr) (v : Byte) : Memory :=
  match mem.map (pageOf a) with
  | none => mem
  | some m =>
    let o := pageOffset a
    match mem.backings m.backing with
    | .priv f | .freed f => mem.setBacking m.backing (.priv (f.set o v))
    | .kernel f => mem.setBacking m.backing (.kernel (f.map (·.set o v)))
    | .cow fp => mem.setBacking m.backing (.priv ((mem.files.page fp).set o v))
    | .file fp => { mem with files := mem.files.setPage fp ((mem.files.page fp).set o v) }

/-! ## Changes of the layout

What the system calls of `Spec/Linux/Syscall/Mm.lean` do to the page map, over the `n` pages from
page number `first`. -/

/-- Whether page `p` is one of the `n` pages from page number `first`. -/
def inPages (first n : Nat) (p : PageNum) : Bool := decide (first ≤ p.toNat ∧ p.toNat < first + n)

/-- A page map that maps pages only where `mem`'s does is covered by `mem`'s cover. -/
theorem Memory.covers_sub (mem : Memory) {f : PageNum → Option Mapping}
    (h : ∀ p, (f p).isSome = true → (mem.map p).isSome = true) :
    ∀ p, (f p).isSome = true → inRuns mem.cover p.toNat = true :=
  fun p hp => mem.covers p (h p hp)

/-- A page map that maps pages only where `mem`'s does or among the `n` from `first` is covered by
`mem`'s cover with that run added. -/
theorem Memory.covers_add (mem : Memory) {f : PageNum → Option Mapping} {first n : Nat}
    (h : ∀ p, (f p).isSome = true → inPages first n p = true ∨ (mem.map p).isSome = true) :
    ∀ p, (f p).isSome = true → inRuns ((first, n) :: mem.cover) p.toNat = true := by
  intro p hp
  rcases h p hp with h | h
  · simp only [inRuns, List.any_cons, Bool.or_eq_true]; exact .inl h
  · simp only [inRuns, List.any_cons, Bool.or_eq_true]; exact .inr (mem.covers p h)

/-- The runs `rs` without the `n` pages from `first`: each run's parts below and above them. -/
def cutRuns (rs : List (Nat × Nat)) (first n : Nat) : List (Nat × Nat) :=
  rs.flatMap fun (f, k) =>
    (if f < first then [(f, min (f + k) first - f)] else []) ++
    (if first + n < f + k then [(max f (first + n), f + k - max f (first + n))] else [])

theorem inRuns_cutRuns {first n x : Nat} (hx : ¬ (first ≤ x ∧ x < first + n)) :
    ∀ rs : List (Nat × Nat), inRuns rs x = true → inRuns (cutRuns rs first n) x = true
  | [], h => h
  | (f, k) :: rs, h => by
    simp only [inRuns, List.any_cons, Bool.or_eq_true, decide_eq_true_eq] at h
    simp only [cutRuns, List.flatMap_cons, inRuns, List.any_append, Bool.or_eq_true] at ⊢
    rcases h with h | h
    · left
      by_cases h₁ : x < first
      · left; simp only [show f < first by omega, ↓reduceIte, List.any_cons, List.any_nil, Bool.or_false,
          decide_eq_true_eq]; omega
      · right; simp only [show first + n < f + k by omega, ↓reduceIte, List.any_cons, List.any_nil,
          Bool.or_false, decide_eq_true_eq]; omega
    · right; exact inRuns_cutRuns hx rs h

/-- `if inPages first n p then x else mem.map p` maps pages only among the `n` from `first` or where
`mem`'s map does. -/
theorem Memory.covers_ite (mem : Memory) {first n : Nat} (x : PageNum → Option Mapping) (p : PageNum)
    (h : (if inPages first n p then x p else mem.map p).isSome = true) :
    inPages first n p = true ∨ (mem.map p).isSome = true := by
  by_cases hp : inPages first n p = true
  · exact .inl hp
  · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h; exact .inr h

/-- The mapping of page number `p` (as a number; none beyond the 52-bit page numbers). -/
def Memory.mapAt (mem : Memory) (p : Nat) : Option Mapping :=
  if p < 2 ^ 52 then mem.map (BitVec.ofNat 52 p) else none

/-- Whether every one of the `n` pages from `first` is unmapped. -/
def Memory.free (mem : Memory) (first n : Nat) : Bool :=
  (List.range n).all fun k => (mem.mapAt (first + k)).isNone

/-- Whether some page of the `n` from `first` is mapped. -/
def Memory.anyMapped (mem : Memory) (first n : Nat) : Bool := !mem.free first n

/-- The first mapped page above page number `p`, among the `n` after it: its number and mapping
(`find_vma`: the first VMA that ends above an address). -/
def Memory.nextMapped (mem : Memory) (p : Nat) : Nat → Option (Nat × Mapping)
  | 0 => none
  | n + 1 =>
    match mem.mapAt (p + 1) with
    | some m => some (p + 1, m)
    | none => mem.nextMapped (p + 1) n

/-- The mapping of the last mapped page below page number `p`, among the `n` before it (`vma_prev`:
the VMA below). -/
def Memory.prevMapped (mem : Memory) : Nat → Nat → Option Mapping
  | 0, _ => none
  | _, 0 => none
  | p + 1, n + 1 =>
    match mem.mapAt p with
    | some m => some m
    | none => mem.prevMapped p n

/-- The number of pages from page number `p` up, among the `n` from it, that are mapped by mappings
with property `P`, up to the first that is not. -/
def Memory.pagesWhile (mem : Memory) (P : Mapping → Bool) (p : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    match mem.mapAt p with
    | some m => if P m then mem.pagesWhile P (p + 1) n + 1 else 0
    | none => 0

/-- Whether some page of the `n` from `first` belongs to a special mapping or is the initial
stack's first page as `execve` mapped it (`Memory.growsDown`): changes there are not modelled. -/
def Memory.touchesFixed (mem : Memory) (first n : Nat) : Bool :=
  (List.range n).any fun k =>
    (match mem.mapAt (first + k) with
     | some m => m.special
     | none => false) ||
    mem.growsDown.any fun g => g.toNat = first + k

/-- `mem` with the `n` pages from `first` unmapped (`munmap(2)`). Their contents stay in their
backings, which no page refers to any more unless another mapping shares them. -/
def Memory.unmap (mem : Memory) (first n : Nat) : Memory :=
  { mem with
    map := fun p => if inPages first n p then none else mem.map p
    cover := cutRuns mem.cover first n
    covers := fun p h => by
      by_cases hp : inPages first n p = true
      · simp [hp] at h
      · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
        exact inRuns_cutRuns (by simpa [inPages] using hp) _ (mem.covers p h) }

/-- `mem` with the `n` pages from `first` mapped to new private anonymous memory of zeros, with
protection `prot` and protection key 0, replacing what was mapped there: page `first + k` gets
the new backing `fresh + k`, all in the new area `fresh` (`mm/mmap.c` `mmap_region`; the kernel
fills anonymous pages with zeros when they are first touched, `do_anonymous_page`). -/
def Memory.mapAnon (mem : Memory) (first n : Nat) (prot : Prot) : Memory :=
  { mem with
    map := fun p => if inPages first n p then
        some ⟨prot, mem.fresh + (p.toNat - first), 0, false, none, mem.fresh, ⟨true, true, true⟩, false⟩
      else mem.map p
    backings := fun i => if mem.fresh ≤ i ∧ i < mem.fresh + n then .priv zeroFrame else mem.backings i
    fresh := mem.fresh + n
    cover := (first, n) :: mem.cover
    covers := mem.covers_add (mem.covers_ite _) }

/-- `mem` with the `n` pages from `first` mapped as pages of the mapping `m` grown down to them, a
stack's growth (`mm/vma.c` `expand_downwards`): new private anonymous memory of zeros (the kernel
fills a page with zeros when it is first touched, `do_anonymous_page`) with `m`'s protection, key,
area, maximum protection and `growsDown`; page `first + k` gets the new backing `fresh + k`. -/
def Memory.growDown (mem : Memory) (first n : Nat) (m : Mapping) : Memory :=
  { mem with
    map := fun p => if inPages first n p then
        some { m with backing := mem.fresh + (p.toNat - first), special := false, origin := none }
      else mem.map p
    backings := fun i => if mem.fresh ≤ i ∧ i < mem.fresh + n then .priv zeroFrame else mem.backings i
    fresh := mem.fresh + n
    cover := (first, n) :: mem.cover
    covers := mem.covers_add (mem.covers_ite _) }

/-- `mem` with the `n` pages from `first` mapped to the file pages from `fp` on (page `first + k`
to page `fp.index + k` of `fp.file`), privately (`Backing.cow`) or shared (`Backing.file`), with
protection `prot`, maximum protection `maxProt` and protection key 0, replacing what was mapped
there: page `first + k` gets the new backing `fresh + k`, all in the new area `fresh` (`mm/vma.c`
`__mmap_region`). -/
def Memory.mapFile (mem : Memory) (first n : Nat) (prot maxProt : Prot) (fp : FilePage) (shared : Bool) :
    Memory :=
  let pageAt (k : Nat) : FilePage := ⟨fp.file, fp.index + k⟩
  { mem with
    map := fun p => if inPages first n p then
        some ⟨prot, mem.fresh + (p.toNat - first), 0, false, some (pageAt (p.toNat - first)), mem.fresh, maxProt,
          false⟩
      else mem.map p
    backings := fun i => if mem.fresh ≤ i ∧ i < mem.fresh + n then
        (if shared then .file (pageAt (i - mem.fresh)) else .cow (pageAt (i - mem.fresh)))
      else mem.backings i
    fresh := mem.fresh + n
    cover := (first, n) :: mem.cover
    covers := mem.covers_add (mem.covers_ite _) }

/-- `mem` with the `n` pages from `first` mapped to a new shmem file, shared, with protection
`prot` (`MAP_SHARED | MAP_ANONYMOUS`; `mm/shmem.c` `shmem_zero_setup`): the file `shmem fresh`, of
`n` pages of zeros, maps them, every protection allowed. -/
def Memory.mapShmem (mem : Memory) (first n : Nat) (prot : Prot) : Memory :=
  let id := FileId.shmem mem.fresh
  let fs := mem.files
  ({ mem with files := { fs with page := fun fp => if fp.file = id then zeroFrame else fs.page fp,
                                 size := fun f => if f = id then 4096 * n else fs.size f } } : Memory).mapFile
    first n prot ⟨true, true, true⟩ ⟨id, 0⟩ true

/-- `fs` with the bytes `bs` written into file `file` from byte offset `pos` on, its size grown to
cover them (`write(2)` to a regular file, `mm/filemap.c` `generic_perform_write`). Bytes between
the old end and `pos` read as the pages hold them. -/
def Files.writeAt (fs : Files) (file : FileId) (pos : Nat) (bs : List Byte) : Files :=
  { fs with
    page := fun fp o =>
      let x := 4096 * fp.index + o.toNat
      if fp.file = file ∧ pos ≤ x ∧ x < pos + bs.length then bs.getD (x - pos) 0 else fs.page fp o
    size := fun f => if f = file then max (fs.size f) (pos + bs.length) else fs.size f }

/-- Byte `i` of file `file` as the kernel reads it (`kernel_read`, `read(2)`): the file page's byte
below the file's size, and 0 beyond it (reads stop at the end of the file; `execve`'s buffer for the
file header, `bprm->buf`, starts zeroed). -/
def Files.byte (fs : Files) (file : FileId) (i : Nat) : Byte :=
  if i < fs.size file then fs.page ⟨file, i / 4096⟩ (BitVec.ofNat 12 i) else 0

/-- The `k` bytes of file `file` from byte `pos` on. -/
def Files.bytes (fs : Files) (file : FileId) (pos k : Nat) : List Byte :=
  (List.range k).map fun i => fs.byte file (pos + i)

/-- Whether one of the `n` pages from `first` maps backing `i`. -/
def Memory.mappedFrom (mem : Memory) (first n i : Nat) : Bool :=
  (List.range n).any fun k => (mem.mapAt (first + k)).any (·.backing = i)

/-- `mem` with the file pages `fps` made zeros (a hole punched into their files,
`fallocate(FALLOC_FL_PUNCH_HOLE | FALLOC_FL_KEEP_SIZE)`); the sizes stay. -/
def Memory.punch (mem : Memory) (fps : List FilePage) : Memory :=
  { mem with files := { mem.files with page := fun fp => if fp ∈ fps then zeroFrame else mem.files.page fp } }

/-- `mem` with the private anonymous pages among the `n` from `first` freed lazily
(`madvise(MADV_FREE)`): each `priv` backing they map becomes `freed` with the same contents. -/
def Memory.freePages (mem : Memory) (first n : Nat) : Memory :=
  { mem with backings := fun i =>
      match mem.backings i with
      | .priv f => if mem.mappedFrom first n i then .freed f else .priv f
      | b => b }

/-- `mem` with the pages among the `n` from `first` faulted in for writing
(`madvise(MADV_POPULATE_WRITE)`, `mm/gup.c` with `FOLL_WRITE`): a private file page not yet copied
gets its copy and a lazily freed page is kept (`priv`), as at a store; nothing else changes. -/
def Memory.populate (mem : Memory) (first n : Nat) : Memory :=
  { mem with backings := fun i =>
      match mem.backings i with
      | .cow fp => if mem.mappedFrom first n i then .priv (mem.files.page fp) else .cow fp
      | .freed f => if mem.mappedFrom first n i then .priv f else .freed f
      | b => b }

/-- `mem` with the protection of the mapped pages among the `n` from `first` set to `prot`
(`mprotect(2)`); contents, backings and protection keys stay. -/
def Memory.protect (mem : Memory) (first n : Nat) (prot : Prot) : Memory :=
  { mem with
    map := fun p => if inPages first n p then (mem.map p).map ({ · with prot }) else mem.map p
    covers := mem.covers_sub fun p h => by
      by_cases hp : inPages first n p = true
      · simpa [hp] using h
      · simpa only [hp, Bool.false_eq_true, ↓reduceIte] using h }

/-- The offset, among the pages from `first`, of the first page of the run of mapped pages of one
area that page `first + i` is in (at most `i`). -/
def Memory.runStart (mem : Memory) (first : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 =>
    match mem.mapAt (first + i), mem.mapAt (first + i + 1) with
    | some a, some b => if a.area = b.area then mem.runStart first i else i + 1
    | _, _ => i + 1

/-- The runs of mapped pages of one area among the `n` from `first`, as offset and length: parts of
one VMA each. -/
def Memory.runs (mem : Memory) (first n : Nat) : List (Nat × Nat) :=
  ((List.range n).filter fun i => (mem.mapAt (first + i)).isSome && mem.runStart first i == i).map fun i =>
    (i, ((List.range (n - i)).takeWhile fun j =>
      (mem.mapAt (first + i + j)).isSome && mem.runStart first (i + j) == i).length)

/-- `mem` with new areas for the mapped pages among the `n` from `first`, after a change that may
split VMAs at the range's ends: the pages of each run of one area share a new one, `fresh` plus the
run's offset, so that pages that were one VMA still count as one and nothing else does; `fresh`
moves past them. -/
def Memory.renumber (mem : Memory) (first n : Nat) : Memory :=
  { mem with
    map := fun p => if inPages first n p then
        (mem.map p).map fun m => { m with area := mem.fresh + mem.runStart first (p.toNat - first) }
      else mem.map p
    fresh := mem.fresh + n
    covers := mem.covers_sub fun p h => by
      by_cases hp : inPages first n p = true
      · simpa [hp] using h
      · simpa only [hp, Bool.false_eq_true, ↓reduceIte] using h }

/-- Whether the `n` pages from `first` are mapped and of one area: one VMA. -/
def Memory.sameArea (mem : Memory) (first n : Nat) : Bool :=
  match mem.mapAt first with
  | none => false
  | some m₀ => (List.range n).all fun k => (mem.mapAt (first + k)).any (·.area == m₀.area)

/-- Whether the backing of mapping `m` is a shared file page (`MAP_SHARED`). -/
def Memory.sharedAt (mem : Memory) (m : Mapping) : Bool :=
  match mem.backings m.backing with
  | .file _ => true
  | _ => false

/-- Whether the `n` pages from `first` are all mapped and could belong to one VMA, the kernel's unit
of mapping (`struct vm_area_struct`): the same protection, maximum protection, key and kind, and either all anonymous
or mapping consecutive pages of one file, all privately or all shared. Pages that differ in one
of these are in different VMAs; adjacent VMAs that agree in all of them may have been merged
(`mm/vma.c` `vma_merge_existing_range`, `is_mergeable_vma`), and are surely one VMA only where the
pages are of one area (`Memory.sameArea`). -/
def Memory.oneArea (mem : Memory) (first n : Nat) : Bool :=
  match mem.mapAt first with
  | none => false
  | some m₀ => (List.range n).all fun k =>
    match mem.mapAt (first + k) with
    | none => false
    | some m => decide (m.prot = m₀.prot ∧ m.pkey = m₀.pkey ∧ m.special = m₀.special ∧
        m.maxProt = m₀.maxProt ∧ m.origin = m₀.origin.map (fun fp => ⟨fp.file, fp.index + k⟩)) &&
        mem.sharedAt m == mem.sharedAt m₀

/-- `mem` with the mapped pages among the `n` from `src` moved to the `n` pages from `dst`
(`mremap(2)`, which moves the page-table entries, `mm/mremap.c` `move_page_tables`): page `dst + k`
gets the mapping of page `src + k`, backing included, so that its contents (and, for a file page,
its file) go along, and page `src + k` is unmapped. A page of the destination whose source page is
unmapped keeps its mapping. The two ranges do not overlap (`sysMremap` checks it). -/
def Memory.move (mem : Memory) (src dst n : Nat) : Memory :=
  { mem with
    map := fun p =>
      let q := src + (p.toNat - dst)
      if inPages dst n p && (mem.mapAt q).isSome then mem.mapAt q
      else if inPages src n p then none else mem.map p
    cover := (dst, n) :: cutRuns mem.cover src n
    covers := fun p h => by
      simp only [inRuns, List.any_cons, Bool.or_eq_true]
      by_cases hd : (inPages dst n p && (mem.mapAt (src + (p.toNat - dst))).isSome) = true
      · simp only [Bool.and_eq_true] at hd; exact .inl hd.1
      · simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hs : inPages src n p = true
        · simp [hs] at h
        · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
          exact .inr (inRuns_cutRuns (by simpa [inPages] using hs) _ (mem.covers p h)) }

/-- The contents a page of mapping `m` shows when it has no contents of its own: for a shared
file mapping its file page (as always), for a private one its file page (`m.origin`), and for
anonymous memory zeros. -/
def Memory.pristine (mem : Memory) (m : Mapping) : Backing :=
  match mem.backings m.backing, m.origin with
  | .file fp, _ => .file fp
  | _, some fp => .cow fp
  | _, none => .priv zeroFrame

/-- `mem` with the `n` pages from `first` mapped like mapping `m`, `skip` pages on: with `m`'s
protection, maximum protection, key, area and growing down, and new backings from `fresh` on, which hold zeros if
`m` is anonymous, and otherwise map the file pages from `skip` pages after `m`'s on, privately or
shared as `m` does. -/
def Memory.mapAs (mem : Memory) (first n : Nat) (m : Mapping) (skip : Nat) : Memory :=
  let origin (k : Nat) : Option FilePage := m.origin.map fun fp => ⟨fp.file, fp.index + skip + k⟩
  { mem with
    map := fun p => if inPages first n p then
        some ⟨m.prot, mem.fresh + (p.toNat - first), m.pkey, false, origin (p.toNat - first), m.area,
          m.maxProt, m.growsDown⟩
      else mem.map p
    backings := fun i => if mem.fresh ≤ i ∧ i < mem.fresh + n then
        match origin (i - mem.fresh), mem.sharedAt m with
        | none, _ => .priv zeroFrame
        | some fp, true => .file fp
        | some fp, false => .cow fp
      else mem.backings i
    fresh := mem.fresh + n
    cover := (first, n) :: mem.cover
    covers := mem.covers_add (mem.covers_ite _) }

/-- `mem` with the `n` pages from `first` mapped as the pages that follow mapping `m` (the page
before them, when `mremap(2)` grows a mapping): `m`'s kind and area (the kernel grows that VMA), the
file pages after `m`'s. -/
def Memory.extend (mem : Memory) (first n : Nat) (m : Mapping) : Memory := mem.mapAs first n m 1

/-- `mem` with the `n` pages from `first` mapped as the pages from `src` were in `old`, where they
were mapped (the others as they are), but without contents of their own: page `first + k` gets `old`'s mapping of page
`src + k` with a new backing (from `fresh` on) showing what a page of that mapping shows when it has
none (`Memory.pristine`). This is what remains of a range whose page-table entries `mremap(2)` moved
away while the range stayed mapped (`MREMAP_DONTUNMAP`, or an unmap that failed; `src = first`), and
of a copy the kernel made of a mapping and failed to remove after a failed move. -/
def Memory.remapEmpty (mem : Memory) (first n : Nat) (old : Memory) (src : Nat) : Memory :=
  { mem with
    map := fun p => if inPages first n p then
        match old.mapAt (src + (p.toNat - first)) with
        | some m => some { m with backing := mem.fresh + (p.toNat - first) }
        | none => mem.map p
      else mem.map p
    backings := fun i => if mem.fresh ≤ i ∧ i < mem.fresh + n then
        match old.mapAt (src + (i - mem.fresh)) with
        | some m => old.pristine m
        | none => .priv zeroFrame
      else mem.backings i
    fresh := mem.fresh + n
    cover := (first, n) :: mem.cover
    covers := mem.covers_add (mem.covers_ite _) }

/-- `mem` with the private contents of the mapped pages among the `n` from `first` dropped
(`madvise(MADV_DONTNEED)`, `mm/madvise.c` `madvise_dontneed_single_vma`, which removes the
page-table entries): each such page shows afterwards what a page of its mapping shows when it has
no contents of its own (`Memory.pristine`): zeros for anonymous memory, its file page for a file
mapping. The page map stays. The backing is replaced in place: a page's private backing is its
own, because every mapping the kernel creates gets new ones (`Memory.fresh`) and a move takes a
page's backing along (`Memory.move`). -/
def Memory.discard (mem : Memory) (first n : Nat) : Memory :=
  { mem with backings := fun i =>
      match (List.range n).findSome? fun k => (mem.mapAt (first + k)).filter (·.backing = i) with
      | some m => mem.pristine m
      | none => mem.backings i }

/-- `mem` after another agent set the size of file `file` to `size` bytes (`truncate(2)`, an
appending `write(2)`): the kernel unmaps the pages of the file's mappings wholly beyond the new end,
the private copies of a private mapping included (`mm/truncate.c` `truncate_pagecache`, which calls
`unmap_mapping_range` with `even_cows`), so such a page of a private mapping shows its file page
again (`Memory.pristine`), and an access to it faults while the file stays that short. Each such page
gets a new backing, `fresh` plus its page number. Pages of shared mappings show the file page anyway;
the bytes of the last page past the new end keep their values here (the kernel zeroes them in the
file, which `EnvEvent.fileWrite` can do). -/
def Memory.truncate (mem : Memory) (file : FileId) (size : Nat) : Memory :=
  let dropped (m : Mapping) : Bool :=
    (m.origin.any fun fp => fp.file = file && size ≤ 4096 * fp.index) && !mem.sharedAt m
  { mem with
    map := fun p => (mem.map p).map fun m => if dropped m then { m with backing := mem.fresh + p.toNat } else m
    covers := mem.covers_sub fun p h => by simpa using h
    backings := fun i =>
      if mem.fresh ≤ i ∧ i < mem.fresh + 2 ^ 52 then
        match mem.map (BitVec.ofNat 52 (i - mem.fresh)) with
        | some m => if dropped m then mem.pristine m else mem.backings i
        | none => mem.backings i
      else mem.backings i
    files := mem.files.setSize file size
    fresh := mem.fresh + 2 ^ 52 }

end ZellicX86
