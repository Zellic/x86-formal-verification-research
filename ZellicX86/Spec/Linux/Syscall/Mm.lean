import ZellicX86.Spec.Linux.Syscall.Common
/-!
# Linux system calls: `brk`, `mmap`, `munmap`, `mprotect`, `mremap`, `madvise`

The calls that change the address space's layout or its pages' contents, as relations over the
kernel's choices. What the
kernel decides from the state and the arguments alone (alignment, lengths, the flags, what is
mapped where) is computed here; where it may choose, it is asked (`Spec/Request.lean`):

- where a mapping whose address the caller left to the kernel goes (`Request.place`): any free,
  page-aligned range of user space; an answer that is not one ends the call with `ENOMEM`, the
  kernel's error when it finds no room;
- whether the call fails for a reason the model does not track (`Request.memFail`): lack of
  memory, limits other processes may change, the security module, and for `mremap` a boundary
  between VMAs the model does not see. A failed `mprotect` may have changed a first part of its
  range, a failed `MAP_FIXED` may have unmapped one, and a failed `mremap` with `MREMAP_FIXED` may
  have unmapped or moved part of its ranges, as the kernel leaves them (`mm/mprotect.c`
  `do_mprotect_pkey`, `mm/vma.c` `vms_abort_munmap_vmas`, `mm/mremap.c` `remap_move`).

The model has no VMAs (the kernel's `struct vm_area_struct`), only pages: which adjacent pages of
the same kind the kernel merged into one VMA is not visible, and a call whose result depends on it
(an `mremap` of a range across such a boundary fails with `EFAULT`) has the kernel's outcomes as
`memFail` answers. Pages of different protection, key, file or offset are in different VMAs, and the
calls that need one VMA fail for them as the kernel does (`Memory.oneArea`).

So a theorem that holds for every answer holds for every kernel decision, and some answers are
not decisions any kernel makes (the kernel honours a free hint; it fails only when something runs
out): the relation is wider than the kernel, never narrower.

Not modelled: mappings of devices and special files (`FileMap.other`), `MAP_SYNC`, `MAP_HUGETLB`,
private `MAP_GROWSDOWN`, `MAP_DROPPABLE`, `MAP_LOCKED`, `PROT_GROWSDOWN`/`PROT_GROWSUP`, execute-only memory on a CPU with protection
keys (the kernel assigns it a key and changes `PKRU`), and changes over the vDSO's pages or the
first page of the initial stack. `mseal(2)`, `pkey_mprotect(2)` and `personality(2)` are not
modelled, so no page is sealed, except possibly the vDSO's (with `CONFIG_MSEAL_SYSTEM_MAPPINGS`;
changes to it are not modelled anyway), and `READ_IMPLIES_EXEC`, which `execve` of a 64-bit ELF clears
(`arch/x86/kernel/process_64.c` `set_personality_64bit`), stays clear.

Sources: Linux v6.18 `mm/mmap.c` (`brk`, `do_mmap`, `ksys_mmap_pgoff`, `__get_unmapped_area`),
`mm/vma.c` (`do_vmi_munmap`, `__mmap_region`), `mm/mprotect.c`, `arch/x86/kernel/sys_x86_64.c`,
`arch/x86/mm/pkeys.c`, `mm/mremap.c`, `mm/madvise.c`, `include/uapi/asm-generic/mman-common.h`,
`include/uapi/linux/mman.h`, `mmap(2)`, `brk(2)`, `mprotect(2)`, `mremap(2)`, `madvise(2)`.
-/
namespace ZellicX86

/-- `mmap` flags (`include/uapi/asm-generic/mman-common.h`, `include/uapi/linux/mman.h`): the
mapping type in the low four bits (`MAP_TYPE`), `MAP_SHARED` 1, `MAP_PRIVATE` 2, `MAP_DROPPABLE`
8; `MAP_FIXED`, `MAP_ANONYMOUS`, `MAP_GROWSDOWN`, `MAP_LOCKED`, `MAP_HUGETLB`, `MAP_FIXED_NOREPLACE`. -/
def MAP_TYPE : Nat := 0xf
/-- `mmap` type: a shared mapping. -/
def MAP_SHARED : Nat := 0x01
/-- `mmap` type: a private (copy-on-write) mapping. -/
def MAP_PRIVATE : Nat := 0x02
/-- `mmap` type: a private mapping whose pages the kernel may drop under memory pressure. -/
def MAP_DROPPABLE : Nat := 0x08
/-- `mmap` flag: map exactly at `addr`, replacing what is mapped there. -/
def MAP_FIXED : Nat := 0x10
/-- `mmap` flag: memory not backed by a file. -/
def MAP_ANONYMOUS : Nat := 0x20
/-- Linux x86-64 `MAP_32BIT` (`arch/x86/include/uapi/asm/mman.h`). -/
def MAP_32BIT : Nat := 0x40
/-- `mmap` flag: a mapping that grows down, as a stack does. -/
def MAP_GROWSDOWN : Nat := 0x100
/-- `mmap` flag: lock the mapping's pages in memory. -/
def MAP_LOCKED : Nat := 0x2000
/-- `mmap` flag: back the mapping with huge pages (hugetlbfs). -/
def MAP_HUGETLB : Nat := 0x40000
/-- `mmap` flag: map exactly at `addr`, failing with `EEXIST` where something is mapped there. -/
def MAP_FIXED_NOREPLACE : Nat := 0x100000

/-- `mprotect` flag: extend the change down to the start of a mapping that grows down
(`include/uapi/asm-generic/mman-common.h`). -/
def PROT_GROWSDOWN : Nat := 0x01000000
/-- `mprotect` flag: extend the change up to the end of a mapping that grows up. -/
def PROT_GROWSUP : Nat := 0x02000000

/-- Whether bit `i` of `v` is set. -/
def bitSet (v : Nat) (i : Nat) : Bool := v / 2 ^ i % 2 = 1

/-- Whether `v` has one of the bits of mask `m` set: their bitwise and is not 0. -/
def anyBits (v m : Nat) : Bool := v &&& m != 0

/-- The protection `PROT_READ` (bit 0), `PROT_WRITE` (bit 1), `PROT_EXEC` (bit 2) of `prot`; the
kernel ignores its other bits in `mmap` (`calc_vm_prot_bits`). -/
def protOf (prot : Nat) : Prot := ⟨bitSet prot 0, bitSet prot 1, bitSet prot 2⟩

/-- The number of pages from `first` on, among `n`, that are mapped before the first that is not. -/
def Memory.leadMapped (mem : Memory) (first n : Nat) : Nat :=
  ((List.range n).takeWhile fun k => (mem.mapAt (first + k)).isSome).length

/-- `s` with memory `mem` and program break `b`. -/
def State.withLayout (s : State) (mem : Memory) (b : Addr) : State :=
  { s with proc.mm := { s.proc.mm with mem, brk := b } }

/-- `brk(b)` (`mm/mmap.c` `brk`): moves the program break to `b` and returns it, or on failure
returns the break unchanged. It fails for a break below `brkMin`, and for a reason the model does
not track (`Request.memFail`: `RLIMIT_DATA`, accounting, `vm.mmap_min_addr`, and when moving up the
stack guard gap below a mapping that grows down, `vm_start_gap`). Within the break's last page only the
break moves. Moving it down unmaps the pages above the new break's page, whatever is mapped there,
and fails when none is mapped. Moving it up maps zero pages, read-write, from the old break's page
to the new one's; it fails unless those pages and the one after them are free and within user
space (`check_brk_limits`, the check of the next mapping in `brk`). -/
def sysBrk (feat : Features) (s : State) : Req StepResult := do
  let b := s.cpu.gpr.rdi
  let old := s.proc.mm.brk
  let keep : StepResult := sysReturn s old [] []
  if b.toNat < s.proc.mm.brkMin.toNat then Pure.pure keep else
  match ← Req.request (.memFail 0) with
  | some _ => Pure.pure keep
  | none =>
    let mem := s.proc.mm.mem
    let newP := pageUp b.toNat / 4096
    let oldP := pageUp old.toNat / 4096
    if newP = oldP then Pure.pure (sysReturn (s.withLayout mem b) b [] [])
    else if newP < oldP then
      if !mem.anyMapped newP (oldP - newP) then Pure.pure keep
      else if mem.touchesFixed newP (oldP - newP) then
        Pure.pure (.stopped (.notModelled (.feature "brk over the vDSO or the initial stack")))
      else Pure.pure (sysReturn (s.withLayout (mem.unmap newP (oldP - newP)) b) b [] [])
    else if 4096 * newP > taskSize feat || !mem.free oldP (newP - oldP + 1) then Pure.pure keep
    else Pure.pure (sysReturn (s.withLayout (mem.mapAnon oldP (newP - oldP) ⟨true, true, false⟩) b) b [] [])

/-- `mmap` type: a shared mapping that refuses flags the kernel does not know (`include/uapi/linux/mman.h`). -/
def MAP_SHARED_VALIDATE : Nat := 0x03
/-- `mmap` flag, with `MAP_SHARED_VALIDATE`: synchronous page faults for a DAX file
(`include/uapi/asm-generic/mman-common.h`). -/
def MAP_SYNC : Nat := 0x80000

/-- The flags a shared mapping of a file accepts (`LEGACY_MAP_MASK`, `include/linux/mman.h`):
`MAP_SHARED`, `MAP_PRIVATE`, `MAP_FIXED`, `MAP_ANONYMOUS`, `MAP_32BIT`, `MAP_ABOVE4G`,
`MAP_GROWSDOWN`, `MAP_DENYWRITE`, `MAP_EXECUTABLE`, `MAP_LOCKED`, `MAP_NORESERVE`, `MAP_POPULATE`,
`MAP_NONBLOCK`, `MAP_STACK`, `MAP_HUGETLB`, `MAP_UNINITIALIZED`, `MAP_HUGE_2MB`, `MAP_HUGE_1GB`. -/
def legacyMapMask : Nat := 0x7c07f9f3

/-- `MAX_LFS_FILESIZE` on 64-bit (`include/linux/fs.h`): the largest size of a regular file. -/
def maxLfsFilesize : Nat := 2 ^ 63 - 1

/-- `file_mmap_ok` (`mm/mmap.c`) for files of maximum size `max`: `len` bytes from page `pgoff` lie
within it. -/
def fileMmapOk (max len pgoff : Nat) : Bool := len ≤ max && pgoff ≤ (max - len) / 4096

/-- `mmap(addr, len, prot, flags, fd, off)` (`arch/x86/kernel/sys_x86_64.c` `mmap`,
`ksys_mmap_pgoff`, `vm_mmap_pgoff`, `do_mmap`), of anonymous memory, private or shared, and of the
pages of a file (`FileMap.pages`), privately or shared. In the kernel's order:
- `off` must be page-aligned (`EINVAL`); without `MAP_ANONYMOUS`, `fd` must be open, and not with
  `O_PATH` (`EBADF`; `fdget`, `FdTable.descNoPath`); a device or special file (`FileMap.other`) is not modelled, and `MAP_HUGETLB`
  is `EINVAL` with a file and not modelled without;
- `len` must not be 0 (`EINVAL`), and rounded up to pages neither wrap (`ENOMEM`) nor exceed user
  space (`ENOMEM`);
- the address: with `MAP_FIXED` or `MAP_FIXED_NOREPLACE` it is `addr`, which must leave room for
  the length below `TASK_SIZE` (`ENOMEM`) and be page-aligned (`EINVAL`); otherwise the kernel's
  choice (`Request.place`), which must be page-aligned, at or above the first page, and free up to
  the length within user space (else `ENOMEM`); with `MAP_32BIT`, the end is at most
  `0x80000000` and the start at least `0x40000000`, except that a nonzero page-rounded-down hint may be
  accepted below the search range, possibly raised to the page-rounded-up `mmap_min_addr`
  (`mm/mmap.c` `round_hint_to_min`; `arch/x86/kernel/sys_x86_64.c` `find_start_end`,
  `arch_get_unmapped_area`). Since the `vm.mmap_min_addr` setting can change at run time, the model
  does not check it here but leaves it to the kernel's choice of place (`Request.place`), so a low
  hint permits a start at or above its rounded-down page. Fixed mappings ignore `MAP_32BIT`;
- with `MAP_FIXED_NOREPLACE`, a page mapped in the range fails with `EEXIST`;
- `MAP_LOCKED` is not modelled: the mapping's pages are locked in memory (`VM_LOCKED`), which the
  model does not keep, and a locked mapping refuses `madvise`'s `MADV_DONTNEED`, `MADV_FREE`,
  `MADV_REMOVE`, `MADV_COLD` and `MADV_PAGEOUT` (`EINVAL`, `mm/madvise.c`);
- anonymous memory: the type must be `MAP_PRIVATE` or `MAP_SHARED` (`EINVAL`; `MAP_DROPPABLE` is
  not modelled); `MAP_GROWSDOWN` is `EINVAL` for a shared mapping and not modelled for a private
  one;
- a file: the length and offset must lie within the largest file (`file_mmap_ok`: `EOVERFLOW`; for a
  file without pages the bound depends on its type, so in between it is the kernel's choice,
  `Request.pick`); the type must be `MAP_SHARED`, `MAP_SHARED_VALIDATE` or `MAP_PRIVATE`
  (`EINVAL`); `MAP_SHARED_VALIDATE` refuses flags outside `legacyMapMask` (`EOPNOTSUPP`; `MAP_SYNC`,
  for DAX files, is not modelled); then what the file is now (`Request.fileAttrs`) decides, for a
  shared mapping: `PROT_WRITE` needs the descriptor open for writing (`EACCES`) and the file not a
  swap file (`ETXTBSY`), and an append-only file open for writing refuses it (`EACCES`); for every
  file mapping: the descriptor must be open for reading (`EACCES`), a `noexec` mount refuses
  `PROT_EXEC` (`EPERM`), a file without an `mmap` operation is `ENODEV`, `MAP_GROWSDOWN` `EINVAL`;
  a shared mapping of a write-sealed memfd open for writing refuses `PROT_WRITE` (`EPERM`);
- a failure the model does not track (`Request.memFail`), which with `MAP_FIXED` may leave a first
  part of the range unmapped;
- the range is mapped with protection `prot` (`protOf`), replacing what was mapped there, and `rax`
  is its address: private anonymous memory of zeros (`Memory.mapAnon`), a new shmem file for shared
  anonymous memory (`Memory.mapShmem`), or the file pages from `off` on (`Memory.mapFile`), whose
  maximum protection lacks `write` for a shared mapping of a descriptor not open for writing or of
  a write-sealed memfd and `exec` on a `noexec` mount.
The kernel ignores the other flags (`MAP_NORESERVE`, `MAP_POPULATE`, `MAP_STACK` change nothing the
model shows; `MAP_POPULATE` of a private file mapping makes the copies at once,
which `EnvEvent.cowBreak` covers) and the offset of an anonymous mapping. -/
def sysMmap (feat : Features) (s : State) : Req StepResult := do
  let addr := s.cpu.gpr.rdi.toNat
  let len := s.cpu.gpr.rsi.toNat
  let prot := s.cpu.gpr.rdx.toNat
  let flags := s.cpu.gpr.r10.toNat
  let fd := s.cpu.gpr.r8.toNat % 2 ^ 32
  let off := s.cpu.gpr.r9.toNat
  let fail (e : Nat) : Req StepResult := Pure.pure (sysReturn s (errRet e) [] [])
  let stop (what : String) : Req StepResult := Pure.pure (.stopped (.notModelled (.feature what)))
  let mem := s.proc.mm.mem
  let anon := bitSet flags 5
  let fo : Option OpenFile := if anon then none else s.proc.files.descNoPath fd
  let kind : Option FileMap := fo.map (·.map)
  if off % 4096 ≠ 0 then fail EINVAL
  else if !anon && fo.isNone then fail EBADF
  else if kind matches some .other then stop "mmap of a device or special file"
  else if anyBits flags MAP_HUGETLB then (if anon then stop "MAP_HUGETLB" else fail EINVAL)
  else if len = 0 then fail EINVAL
  else
  let L := pageUp len
  let fixed := anyBits flags (MAP_FIXED ||| MAP_FIXED_NOREPLACE)
  if L ≥ 2 ^ 64 then fail ENOMEM
  else if feat.pku && prot = 4 then stop "execute-only memory with protection keys"
  else if L > taskSize feat then fail ENOMEM
  else do
  let a ← if fixed then Pure.pure addr else do
    let a ← Req.request (.place L)
    Pure.pure a.toNat
  let n := L / 4096
  -- the end: the range mapped by `mapIt`, unless the kernel fails for a reason not tracked
  let finish (mapIt : Memory → Memory) : Req StepResult :=
    if mem.touchesFixed (a / 4096) n then stop "mmap over the vDSO or the initial stack" else do
    match ← Req.request (.memFail (if fixed then n else 0)) with
    | some (e, k) =>
      let mem' := if fixed then mem.unmap (a / 4096) k.val else mem
      Pure.pure (sysReturn (s.withMem mem') (errRet e.val) [] [])
    | none => Pure.pure (sysReturn (s.withMem (mapIt mem)) (BitVec.ofNat 64 a) [] [])
  let ty := flags % 16
  if fixed && addr > taskSize feat - L then fail ENOMEM
  else if fixed && addr % 4096 ≠ 0 then fail EINVAL
  else if !fixed && !(a % 4096 = 0 && 4096 ≤ a && a + L ≤ taskSize feat && mem.free (a / 4096) n) then
    fail ENOMEM
  else if !fixed && anyBits flags MAP_32BIT &&
      !(a + L ≤ 0x80000000 && (0x40000000 ≤ a || (addr / 4096 ≠ 0 && addr / 4096 * 4096 ≤ a))) then fail ENOMEM
  else if anyBits flags MAP_FIXED_NOREPLACE && mem.anyMapped (a / 4096) n then fail EEXIST
  else if anyBits flags MAP_LOCKED then stop "MAP_LOCKED"
  else match fo with
  | none =>
    if ty = MAP_DROPPABLE then stop "MAP_DROPPABLE"
    else if ty ≠ MAP_PRIVATE && ty ≠ MAP_SHARED then fail EINVAL
    else if anyBits flags MAP_GROWSDOWN then (if ty = MAP_SHARED then fail EINVAL else stop "MAP_GROWSDOWN")
    else if ty = MAP_SHARED then finish (·.mapShmem (a / 4096) n (protOf prot))
    else finish (·.mapAnon (a / 4096) n (protOf prot))
  | some f => do
    let pg := off / 4096
    let over ← match f.map with
      | .pages _ => Pure.pure !(fileMmapOk maxLfsFilesize L pg)
      | _ =>
        if fileMmapOk maxLfsFilesize L pg then Pure.pure false
        else if !fileMmapOk (2 ^ 64 - 1) L pg then Pure.pure true
        else do
          let c ← Req.request (.pick 1)
          Pure.pure (c.val = 1)
    let shared := ty = MAP_SHARED || ty = MAP_SHARED_VALIDATE
    let write := bitSet prot 1
    if over then fail EOVERFLOW
    else if !shared && ty ≠ MAP_PRIVATE then fail EINVAL
    else if ty = MAP_SHARED_VALIDATE && anyBits flags (2 ^ 64 - 1 - legacyMapMask - MAP_SYNC) then
      fail EOPNOTSUPP
    else if ty = MAP_SHARED_VALIDATE && anyBits flags MAP_SYNC then stop "MAP_SYNC"
    else do
    let attrs ← Req.request (.fileAttrs f.id)
    if shared && write && !f.writable then fail EACCES
    else if shared && write && attrs.swap then fail ETXTBSY
    else if shared && attrs.append && f.writable then fail EACCES
    else if !f.readable then fail EACCES
    else if attrs.noexec && bitSet prot 2 then fail EPERM
    else match f.map with
    | .pages id =>
      if anyBits flags MAP_GROWSDOWN then fail EINVAL
      else if shared && f.writable && attrs.writeSealed && write then fail EPERM
      else
        let maxProt : Prot := ⟨true, !shared || (f.writable && !attrs.writeSealed), !attrs.noexec⟩
        finish (·.mapFile (a / 4096) n (protOf prot) maxProt ⟨id, pg⟩ shared)
    | _ => fail ENODEV

/-- `munmap(addr, len)` (`mm/vma.c` `do_vmi_munmap`): `addr` must be page-aligned, `len` not 0,
and the range within user space (`EINVAL`); the pages of the range, rounded up to pages, are
unmapped. With nothing mapped there it returns 0 at once; otherwise it may fail for a reason the
model does not track (`Request.memFail`), changing nothing. -/
def sysMunmap (feat : Features) (s : State) : Req StepResult := do
  let addr := s.cpu.gpr.rdi.toNat
  let len := s.cpu.gpr.rsi.toNat
  let mem := s.proc.mm.mem
  if addr % 4096 ≠ 0 || addr > taskSize feat || len > taskSize feat - addr || len = 0 then
    Pure.pure (sysReturn s (errRet EINVAL) [] [])
  else
  let first := addr / 4096
  let n := pageUp len / 4096
  if !mem.anyMapped first n then Pure.pure (sysReturn s 0 [] [])
  else if mem.touchesFixed first n then
    Pure.pure (.stopped (.notModelled (.feature "munmap of the vDSO or the initial stack")))
  else
    match ← Req.request (.memFail 0) with
    | some (e, _) => Pure.pure (sysReturn s (errRet e.val) [] [])
    | none => Pure.pure (sysReturn (s.withMem (mem.unmap first n)) 0 [] [])

/-- `mprotect(addr, len, prot)` (`mm/mprotect.c` `do_mprotect_pkey`): `PROT_GROWSDOWN` and
`PROT_GROWSUP` together are `EINVAL`, either alone is not modelled; `addr` must be page-aligned
(`EINVAL`); a `len` of 0 returns 0; the range rounded up to pages must not wrap (`ENOMEM`); `prot`
may have no bits but `PROT_READ`, `PROT_WRITE`, `PROT_EXEC` and `PROT_SEM` (`EINVAL`). The pages
of the range get protection `prot`, from the first up to the first unmapped one, if any: then the
call returns `ENOMEM` (also when the first page is unmapped, changing nothing). It may fail for a
reason the model does not track after changing a first part of those pages (`Request.memFail`).
The changed pages get new areas, as the kernel splits their VMAs (`mprotect_fixup`; a VMA whose
protection does not change is not split, so this is wider than the kernel).
A page whose maximum protection (`Mapping.maxProt`) lacks a bit of `prot` fails the call with
`EACCES`, the pages before it changed: the kernel goes VMA by VMA, and pages of one VMA share their
maximum, so such a page is the first of its VMA in the range. -/
def sysMprotect (feat : Features) (s : State) : Req StepResult := do
  let addr := s.cpu.gpr.rdi.toNat
  let len := s.cpu.gpr.rsi.toNat
  let protG := s.cpu.gpr.rdx.toNat
  let fail (e : Nat) : Req StepResult := Pure.pure (sysReturn s (errRet e) [] [])
  let stop (what : String) : Req StepResult := Pure.pure (.stopped (.notModelled (.feature what)))
  let mem := s.proc.mm.mem
  let down := anyBits protG PROT_GROWSDOWN
  let up := anyBits protG PROT_GROWSUP
  let prot := protG % 2 ^ 24 + protG / 2 ^ 26 * 2 ^ 26
  if down && up then fail EINVAL
  else if addr % 4096 ≠ 0 then fail EINVAL
  else if len = 0 then Pure.pure (sysReturn s 0 [] [])
  else if addr + pageUp len ≥ 2 ^ 64 then fail ENOMEM
  else if prot ≥ 16 then fail EINVAL
  else if down || up then stop "mprotect with PROT_GROWSDOWN or PROT_GROWSUP"
  else
  let first := addr / 4096
  let n := pageUp len / 4096
  let k := mem.leadMapped first n
  if k = 0 then fail ENOMEM
  else if (List.range k).any fun i => (mem.mapAt (first + i)).any (·.special) then
    if first = vsyscallPage.toNat then fail ENOMEM else stop "mprotect of the vDSO"
  else if feat.pku && prot = 4 then stop "execute-only memory with protection keys"
  else
    -- the pages changed before one whose maximum protection refuses `prot`
    let c := ((List.range k).takeWhile fun i =>
      (mem.mapAt (first + i)).all fun m => (protOf prot).within m.maxProt).length
    match ← Req.request (.memFail n) with
    | some (e, j) =>
      let m' := (mem.protect first (min j.val c) (protOf prot)).renumber first (min j.val c)
      Pure.pure (sysReturn (s.withMem m') (errRet e.val) [] [])
    | none =>
      let ret := if c < k then errRet EACCES else if k = n then 0 else errRet ENOMEM
      Pure.pure (sysReturn (s.withMem ((mem.protect first c (protOf prot)).renumber first c)) ret [] [])

/-- `mremap` flag: the kernel may move the mapping (`include/uapi/linux/mman.h`). -/
def MREMAP_MAYMOVE : Nat := 1
/-- `mremap` flag: move the mapping to `new_addr`. -/
def MREMAP_FIXED : Nat := 2
/-- `mremap` flag: leave the old range mapped, without its contents. -/
def MREMAP_DONTUNMAP : Nat := 4

/-- Whether some page of the `n` from `first` is of a mapping that grows down (`Mapping.growsDown`):
the initial stack, or a part of it. -/
def Memory.touchesStack (mem : Memory) (first n : Nat) : Bool :=
  (List.range n).any fun k => (mem.mapAt (first + k)).any (·.growsDown)

/-- After a move of pages from `src`, for each run of them of one area (`runs` of `old`, the memory
before the move): whether the kernel failed to unmap it (`Request.pick 1`, answer 1; `mm/mremap.c`
`unmap_source_vma`, whose failure, of a split when memory is short, the call does not report). Such
a run stays mapped without contents of its own (`Memory.remapEmpty`). -/
def keepSources (old : Memory) (src : Nat) : List (Nat × Nat) → Memory → Req Memory
  | [], m => Pure.pure m
  | (o, l) :: rs, m => do
    let c ← Req.request (.pick 1)
    keepSources old src rs (if c.val = 1 then m.remapEmpty (src + o) l old (src + o) else m)

/-- `mremap(addr, old_len, new_len, flags, new_addr)` (`mm/mremap.c` `do_mremap`): moves, grows or
shrinks the mapping of the `old_len` bytes at `addr`; the lengths are rounded up to pages (modulo
2^64, as the kernel's `PAGE_ALIGN`). In the kernel's order:
- `flags` may have only `MREMAP_MAYMOVE`, `MREMAP_FIXED`, `MREMAP_DONTUNMAP`; `addr` must be
  page-aligned; the new length must not be 0 or exceed user space (each `EINVAL`);
- with `MREMAP_FIXED` or `MREMAP_DONTUNMAP`, `new_addr` must leave room for the new length below
  `TASK_SIZE` and be page-aligned, `MREMAP_MAYMOVE` must be given, `MREMAP_DONTUNMAP` must keep the
  length, and the old and new ranges must not overlap (each `EINVAL`);
- then the call may fail for a reason the model does not track (`Request.memFail`): lack of memory
  and its accounting, `vm.max_map_count`, limits (`RLIMIT_AS`, `RLIMIT_DATA`), the security module
  (`mmap_min_addr` for a new place), and a boundary between two VMAs the kernel did not merge, which
  the model allows (`EFAULT`) unless the pages the kernel checks are of one area
  (`Memory.sameArea`): then an `EFAULT` answer means no failure. What a failure leaves:
  - a failed `MREMAP_FIXED` move of an unchanged length may have moved a first part of the range
    (the kernel moves VMA by VMA) and unmapped the destination of part of the next (the count `k` in
    `Request.memFail`'s answer: the pages moved; then `Request.pick` for how many more destination
    pages whose source is mapped were unmapped);
  - a failed `MREMAP_FIXED` call that changes the length may have unmapped the destination (count 1
    or 2), and when shrinking also the tail of the old range (count 2);
  - any other failure changes nothing;
  - and a failed move may leave the copy the kernel made for it mapped, without contents, at
    `new_addr` or where the kernel placed it (`Request.pick`, then `Request.place`: the kernel
    failed to remove the copy, `move_vma`);
- `MREMAP_FIXED` with an unchanged length moves every mapped page of the old range to the same
  place relative to `new_addr`, replacing what is mapped there (`remap_move`, VMA by VMA); holes in
  the range are allowed, and the destination's pages across from them keep their mappings, but the
  first page must be mapped (`EFAULT`);
- otherwise the first page must be mapped (`EFAULT`). Without `MREMAP_FIXED` and
  `MREMAP_DONTUNMAP`, shrinking unmaps the old range beyond the new length, whatever is mapped
  there, and an unchanged length does nothing; both return `addr`. Every other call needs a
  non-zero old length or a shared mapping (`EINVAL`: the kernel refuses to duplicate a private
  mapping) and the old range, cut to the new length when shrinking, within one VMA
  (`Memory.oneArea`; `EFAULT`);
- an old length of 0 duplicates a shared mapping: the new length's pages, moved as below (never in
  place, so without `MREMAP_MAYMOVE` and `MREMAP_FIXED` it is `ENOMEM`), map the file pages of the
  mapping from `addr`'s on again (`Memory.mapAs`, a new area), and nothing is unmapped; a failed
  duplicate may leave the copy mapped likewise;
- growing in place: if the pages after the old range are free up to the new length within user
  space, they are mapped as the mapping's continuation (`Memory.extend`) and `addr` is returned;
  otherwise, without `MREMAP_MAYMOVE`, `ENOMEM`;
- moving: to `new_addr` with `MREMAP_FIXED` (after unmapping what is there and, when shrinking, the
  old range's tail), or to a place the kernel chooses (`Request.place`; checked as for `mmap`, else
  `ENOMEM`; `new_addr` without `MREMAP_FIXED` is a hint): the old range's pages move there
  (`Memory.move`), pages beyond the old length continue the mapping, and the new address is
  returned. The moved pages get new areas (the kernel copies the VMA), and pages beyond the old
  length continue the last one's. With `MREMAP_DONTUNMAP` the old range stays mapped, without
  contents of its own (`Memory.remapEmpty`); otherwise it is unmapped, unless the kernel failed to
  unmap part of it (`keepSources`), which may also happen to the pages a failed `MREMAP_FIXED`
  move moved.
Not modelled: an old range with a page on the vDSO or on a mapping that grows down (`Mapping.growsDown`:
the kernel would move that part of the stack with its `VM_GROWSDOWN`, making a mapping that grows down
whose first page the model does not record in `Memory.growsDown`), and an `MREMAP_FIXED` destination over
the vDSO or over the first page of a mapping that grows down. The pages a growth in place would add are
only checked to be free (`vma_expandable`), so what lies after the old range does not matter. -/
def sysMremap (feat : Features) (s : State) : Req StepResult := do
  let addr := s.cpu.gpr.rdi.toNat
  let oldL := pageUp s.cpu.gpr.rsi.toNat % 2 ^ 64
  let newL := pageUp s.cpu.gpr.rdx.toNat % 2 ^ 64
  let flags := s.cpu.gpr.r10.toNat
  let newAddr := s.cpu.gpr.r8.toNat
  let fail (e : Nat) : Req StepResult := Pure.pure (sysReturn s (errRet e) [] [])
  let stop (what : String) : Req StepResult := Pure.pure (.stopped (.notModelled (.feature what)))
  let done (mem : Memory) (ret : Nat) : Req StepResult :=
    Pure.pure (sysReturn (s.withMem mem) (BitVec.ofNat 64 ret) [] [])
  let mem := s.proc.mm.mem
  let maymove := bitSet flags 0
  let fixed := bitSet flags 1
  let dontunmap := bitSet flags 2
  let given := fixed || dontunmap
  let P := addr / 4096
  let oldn := oldL / 4096
  let newn := newL / 4096
  let D := newAddr / 4096
  if flags ≥ 8 || addr % 4096 ≠ 0 || newL = 0 || newL > taskSize feat then fail EINVAL
  else if given && (newAddr > taskSize feat - newL || newAddr % 4096 ≠ 0 || !maymove ||
      (dontunmap && oldL ≠ newL) || ((addr + oldL) % 2 ^ 64 > newAddr && newAddr + newL > addr)) then
    fail EINVAL
  else if mem.touchesFixed P (max oldn 1) || (fixed && mem.touchesFixed D newn) then
    if P = vsyscallPage.toNat then fail EFAULT else stop "mremap over the vDSO or the initial stack"
  else if mem.touchesStack P (max oldn 1) then stop "mremap of the initial stack"
  else
  let moveOnly := fixed && oldL = newL
  -- the pages whose VMA boundaries the kernel checks
  let chk := if moveOnly then oldn else if newL > oldL || given then min oldn newn else 1
  -- the `n` pages from `src` moved to `dst`, with new areas there, and what they leave behind
  let moved (m : Memory) (src dst n : Nat) : Req Memory :=
    let m₁ := (m.move src dst n).renumber dst n
    if dontunmap then Pure.pure (m₁.remapEmpty src n mem src) else keepSources mem src (mem.runs src n) m₁
  let f ← Req.request (.memFail (if moveOnly then oldn else if fixed then 2 else 0))
  let f := match f with
    | some (e, k) => if e.val = EFAULT && mem.sameArea P chk then none else some (e, k)
    | none => none
  -- the copy of `n` pages from `src` the kernel made at `dst` for a move that failed, which it then
  -- may fail to remove (`unmap_source_vma` of the copy): it stays, without contents, a new area
  let copyKept (m : Memory) (dst src n : Nat) : Memory := (m.remapEmpty dst n mem src).renumber dst n
  -- the duplicate of a shared mapping (an old length of 0) at `a` in `m`: the same file pages from
  -- `addr`'s on, a new area
  let dup (m : Memory) (a : Nat) : Memory := match mem.mapAt P with
    | some like => (m.mapAs (a / 4096) newn like 0).renumber (a / 4096) newn
    | none => m
  match f with
  | some (e, k) =>
    if moveOnly then do
      let j ← Req.request (.pick (oldn - k.val))
      let m₁ ← moved mem P D k.val
      let lost := (List.range j.val).filter fun i => (mem.mapAt (P + k.val + i)).isSome
      let m₂ := lost.foldl (fun m i => m.unmap (D + k.val + i) 1) m₁
      let c ← Req.request (.pick 1)
      let m₃ := if c.val = 1 then copyKept m₂ (D + k.val) (P + k.val) j.val else m₂
      Pure.pure (sysReturn (s.withMem m₃) (errRet e.val) [] [])
    else do
      let m₁ := if fixed && k.val ≥ 1 then mem.unmap D newn else mem
      let m₂ := if fixed && k.val = 2 && newL < oldL then m₁.unmap (P + newn) (oldn - newn) else m₁
      let n := min oldn newn
      let m₃ ← if !(given || (newL > oldL && maymove)) then Pure.pure m₂ else do
        let c ← Req.request (.pick 1)
        if c.val = 0 then Pure.pure m₂ else do
          let a ← if fixed then Pure.pure newAddr else do
            let a ← Req.request (.place newL)
            Pure.pure a.toNat
          if !fixed && !(a % 4096 = 0 && 4096 ≤ a && a + newL ≤ taskSize feat && m₂.free (a / 4096) newn) then
            Pure.pure m₂
          else
            let m₄ := copyKept m₂ (a / 4096) P n
            Pure.pure (if n = 0 then dup m₂ a else match m₄.mapAt (a / 4096 + n - 1) with
              | some like => m₄.extend (a / 4096 + n) (newn - n) like
              | none => m₄)
      Pure.pure (sysReturn (s.withMem m₃) (errRet e.val) [] [])
  | none =>
  if (mem.mapAt P).isNone then fail EFAULT
  else if moveOnly then do
    let m ← moved mem P D oldn
    done m newAddr
  else if !(newL > oldL || given) then
    if newL < oldL then done (mem.unmap (P + newn) (oldn - newn)) addr else done mem addr
  else if oldL = 0 then
    if !(mem.mapAt P).any mem.sharedAt then fail EINVAL
    else if !given && !maymove then fail ENOMEM
    else do
    let m₁ := if fixed then mem.unmap D newn else mem
    let a ← if fixed then Pure.pure newAddr else do
      let a ← Req.request (.place newL)
      Pure.pure a.toNat
    if !fixed && !(a % 4096 = 0 && 4096 ≤ a && a + newL ≤ taskSize feat && m₁.free (a / 4096) newn) then
      fail ENOMEM
    else done (dup m₁ a) a
  else if !mem.oneArea P (min oldn newn) then fail EFAULT
  else
  -- the old range's last page, which pages beyond the old length continue
  match mem.mapAt (P + min oldn newn - 1) with
  | none => fail EFAULT
  | some last =>
  if !given && newL > oldL && mem.free (P + oldn) (newn - oldn) && (P + newn) * 4096 ≤ taskSize feat then
    done (mem.extend (P + oldn) (newn - oldn) last) addr
  else if !given && !maymove then fail ENOMEM
  else do
  -- the move: the destination cleared first with `MREMAP_FIXED`, and the old range's tail when shrinking
  let m₁ := if fixed then mem.unmap D newn else mem
  let m₂ := if newL < oldL then m₁.unmap (P + newn) (oldn - newn) else m₁
  let n := min oldn newn
  let a ← if fixed then Pure.pure newAddr else do
    let a ← Req.request (.place newL)
    Pure.pure a.toNat
  if !fixed && !(a % 4096 = 0 && 4096 ≤ a && a + newL ≤ taskSize feat && m₂.free (a / 4096) newn) then
    fail ENOMEM
  else do
    let m₃ ← moved m₂ P (a / 4096) n
    done (m₃.extend (a / 4096 + n) (newn - n) ((m₃.mapAt (a / 4096 + n - 1)).getD last)) a

/-- `madvise` advice: no special treatment (`include/uapi/asm-generic/mman-common.h`). -/
def MADV_NORMAL : Int := 0
/-- `madvise` advice: expect page references in random order. -/
def MADV_RANDOM : Int := 1
/-- `madvise` advice: expect page references in sequential order. -/
def MADV_SEQUENTIAL : Int := 2
/-- `madvise` advice: the pages will be needed soon (read ahead). -/
def MADV_WILLNEED : Int := 3
/-- `madvise` advice: the pages are not needed: drop their private contents. -/
def MADV_DONTNEED : Int := 4
/-- `madvise` advice: the pages' contents may be freed lazily. -/
def MADV_FREE : Int := 8
/-- `madvise` advice: free the pages and the file's storage under them (punch a hole). -/
def MADV_REMOVE : Int := 9
/-- `madvise` advice: a child made by `fork` does not get the range. -/
def MADV_DONTFORK : Int := 10
/-- `madvise` advice: undo `MADV_DONTFORK`. -/
def MADV_DOFORK : Int := 11
/-- `madvise` advice: let KSM merge pages of identical contents. -/
def MADV_MERGEABLE : Int := 12
/-- `madvise` advice: undo `MADV_MERGEABLE`. -/
def MADV_UNMERGEABLE : Int := 13
/-- `madvise` advice: back the range with transparent huge pages. -/
def MADV_HUGEPAGE : Int := 14
/-- `madvise` advice: do not back the range with transparent huge pages. -/
def MADV_NOHUGEPAGE : Int := 15
/-- `madvise` advice: leave the range out of a core dump. -/
def MADV_DONTDUMP : Int := 16
/-- `madvise` advice: undo `MADV_DONTDUMP`. -/
def MADV_DODUMP : Int := 17
/-- `madvise` advice: a child made by `fork` sees the range zeroed. -/
def MADV_WIPEONFORK : Int := 18
/-- `madvise` advice: undo `MADV_WIPEONFORK`. -/
def MADV_KEEPONFORK : Int := 19
/-- `madvise` advice: deactivate the pages, so that they are reclaimed first. -/
def MADV_COLD : Int := 20
/-- `madvise` advice: reclaim the pages now. -/
def MADV_PAGEOUT : Int := 21
/-- `madvise` advice: fault the pages in for reading. -/
def MADV_POPULATE_READ : Int := 22
/-- `madvise` advice: fault the pages in for writing. -/
def MADV_POPULATE_WRITE : Int := 23
/-- `madvise` advice: as `MADV_DONTNEED`, also for locked pages. -/
def MADV_DONTNEED_LOCKED : Int := 24
/-- `madvise` advice: collapse the range into transparent huge pages now. -/
def MADV_COLLAPSE : Int := 25
/-- `madvise` advice: poison the pages, as after a memory failure (for testing). -/
def MADV_HWPOISON : Int := 100
/-- `madvise` advice: take the pages' memory offline softly (for testing). -/
def MADV_SOFT_OFFLINE : Int := 101
/-- `madvise` advice: install guard regions, which fault on any access. -/
def MADV_GUARD_INSTALL : Int := 102
/-- `madvise` advice: remove guard regions. -/
def MADV_GUARD_REMOVE : Int := 103

/-- `madvise(start, len, advice)` (`mm/madvise.c` `do_madvise`); `advice` is an `int`. In the
kernel's order:
- `advice` must be one the kernel knows (`madvise_behavior_valid`; `EINVAL`); those the kernel
  knows only with `CONFIG_KSM`, `CONFIG_TRANSPARENT_HUGEPAGE` or `CONFIG_MEMORY_FAILURE`
  (`MADV_MERGEABLE`, `MADV_UNMERGEABLE`, `MADV_HUGEPAGE`, `MADV_NOHUGEPAGE`, `MADV_COLLAPSE`,
  `MADV_HWPOISON`, `MADV_SOFT_OFFLINE`) are not modelled;
- `start` must be page-aligned, and `len`, rounded up to pages, must neither wrap to 0 nor make
  the range wrap (`EINVAL`); an empty range returns 0;
- the advice applies to the mapped pages of the range; if some page of it is unmapped, the call
  returns `ENOMEM` afterwards (`madvise_walk_vmas`).
`MADV_DONTNEED` and `MADV_DONTNEED_LOCKED` drop the pages' private contents (`Memory.discard`): a
page of anonymous memory reads zeros afterwards, a page of a private file mapping its file page
(`Mapping.origin`), a page of a shared one is unchanged. `MADV_NORMAL`, `MADV_RANDOM`,
`MADV_SEQUENTIAL`, `MADV_WILLNEED`, `MADV_DONTDUMP`, `MADV_DODUMP`, `MADV_COLD`, `MADV_PAGEOUT`,
`MADV_DONTFORK`, `MADV_DOFORK` and `MADV_KEEPONFORK` change nothing the model has but VMA boundaries
(read-ahead, the core dump, reclaim, what `fork` copies, which the model does not have): those that
change VMA flags (all but `MADV_WILLNEED`, `MADV_COLD`, `MADV_PAGEOUT`) give the range's pages new
areas, as the kernel may split VMAs at its ends (`madvise_update_vma`; also when the call then
fails). They may fail for a reason the model does not track (`Request.memFail`: the kernel's
`EAGAIN` when splitting a VMA finds no memory, `EBADF` for `MADV_WILLNEED` of anonymous memory
without swap). The advice that works on some kinds of VMA only goes VMA by VMA and stops at the
first that refuses it, with the pages before it done:
- `MADV_WIPEONFORK` (also a flag of `fork`'s): private anonymous memory only (`EINVAL`);
- `MADV_FREE`: private anonymous memory only (`EINVAL`): its pages are freed lazily
  (`Memory.freePages`, `Backing.freed`);
- `MADV_REMOVE`: shared mappings that may be written only (`EINVAL` for anonymous memory, `EACCES`
  for other file mappings): a hole is punched into the file under the pages (`Memory.punch`); the
  file system may refuse (`Request.memFail`, `EOPNOTSUPP`).
`MADV_POPULATE_READ` and `MADV_POPULATE_WRITE` fault the range's pages in, in order, as
`get_user_pages` without `FOLL_FORCE` (`mm/madvise.c` `madvise_populate`, `mm/gup.c`
`check_vma_flags`): a page that is unmapped is `ENOMEM`, one whose protection lacks `PROT_READ`
(respectively `PROT_WRITE`; by the protection asked for, not the hardware's rule) or whose key
`PKRU` denies is `EINVAL`, one beyond the end of its file `EFAULT`, the pages before it faulted in;
`MADV_POPULATE_WRITE` makes the copies of private file pages and keeps lazily freed pages
(`Memory.populate`); a failure the model does not track (lack of memory) stops after a first part.
Not modelled: `MADV_GUARD_INSTALL` and `MADV_GUARD_REMOVE`, and ranges over the vDSO. -/
def sysMadvise (feat : Features) (s : State) : Req StepResult := do
  let start := s.cpu.gpr.rdi.toNat
  let lenIn := s.cpu.gpr.rsi.toNat
  let advice := argInt s.cpu.gpr.rdx
  let fail (e : Nat) : Req StepResult := Pure.pure (sysReturn s (errRet e) [] [])
  let stop (what : String) : Req StepResult := Pure.pure (.stopped (.notModelled (.feature what)))
  let mem := s.proc.mm.mem
  let len := pageUp lenIn % 2 ^ 64
  let known := [MADV_NORMAL, MADV_RANDOM, MADV_SEQUENTIAL, MADV_WILLNEED, MADV_DONTNEED, MADV_FREE,
    MADV_REMOVE, MADV_DONTFORK, MADV_DOFORK, MADV_DONTDUMP, MADV_DODUMP, MADV_WIPEONFORK,
    MADV_KEEPONFORK, MADV_COLD, MADV_PAGEOUT, MADV_POPULATE_READ, MADV_POPULATE_WRITE,
    MADV_DONTNEED_LOCKED, MADV_GUARD_INSTALL, MADV_GUARD_REMOVE]
  let byConfig := [MADV_MERGEABLE, MADV_UNMERGEABLE, MADV_HUGEPAGE, MADV_NOHUGEPAGE, MADV_COLLAPSE,
    MADV_HWPOISON, MADV_SOFT_OFFLINE]
  let flagAdvice := [MADV_NORMAL, MADV_RANDOM, MADV_SEQUENTIAL, MADV_DONTDUMP, MADV_DODUMP, MADV_DOFORK,
    MADV_KEEPONFORK]
  let hints := [MADV_WILLNEED, MADV_COLD, MADV_PAGEOUT]
  if advice ∈ byConfig then stop "madvise advice that depends on the kernel's configuration"
  else if advice ∉ known then fail EINVAL
  else if start % 4096 ≠ 0 || (lenIn ≠ 0 && len = 0) || start + len ≥ 2 ^ 64 then fail EINVAL
  else if len = 0 then Pure.pure (sysReturn s 0 [] [])
  else
  let first := start / 4096
  let n := len / 4096
  let ret : BitVec 64 := if (List.range n).any fun k => (mem.mapAt (first + k)).isNone then errRet ENOMEM else 0
  if (List.range n).any fun k => (mem.mapAt (first + k)).any (·.special) then
    if first = vsyscallPage.toNat then fail ENOMEM else stop "madvise of the vDSO"
  else if advice = MADV_DONTNEED ∨ advice = MADV_DONTNEED_LOCKED then
    Pure.pure (sysReturn (s.withMem (mem.discard first n)) ret [] [])
  else if advice ∈ flagAdvice ∨ advice ∈ hints ∨ advice = MADV_DONTFORK then
    -- advice that changes VMA flags splits VMAs (`madvise_update_vma`), also before a failure
    let s' := if advice ∈ hints then s else s.withMem (mem.renumber first n)
    match ← Req.request (.memFail 0) with
    | some (e, _) => Pure.pure (sysReturn s' (errRet e.val) [] [])
    | none => Pure.pure (sysReturn s' ret [] [])
  else
  -- the number of pages before the first mapped one that fails `ok`: the VMAs before it are done
  let upTo (ok : Mapping → Bool) : Nat :=
    ((List.range n).takeWhile fun k => (mem.mapAt (first + k)).all ok).length
  let anonPriv (m : Mapping) : Bool := m.origin.isNone && !mem.sharedAt m
  if advice = MADV_WIPEONFORK then
    let c := upTo anonPriv
    let s' := s.withMem (mem.renumber first c)
    if c < n then Pure.pure (sysReturn s' (errRet EINVAL) [] []) else
    match ← Req.request (.memFail 0) with
    | some (e, _) => Pure.pure (sysReturn s' (errRet e.val) [] [])
    | none => Pure.pure (sysReturn s' ret [] [])
  else if advice = MADV_FREE then
    let c := upTo anonPriv
    Pure.pure (sysReturn (s.withMem (mem.freePages first c)) (if c < n then errRet EINVAL else ret) [] [])
  else if advice = MADV_REMOVE then
    let c := upTo fun m => mem.sharedAt m && m.maxProt.write
    let bad : BitVec 64 := match mem.mapAt (first + c) with
      | some m => if m.origin.isNone then errRet EINVAL else errRet EACCES
      | none => ret
    let punched (k : Nat) : State :=
      s.withMem (mem.punch ((List.range k).filterMap fun i => (mem.mapAt (first + i)).bind fun m =>
        (mem.backings m.backing).filePage))
    match ← Req.request (.memFail n) with
    | some (e, k) => Pure.pure (sysReturn (punched (min k.val c)) (errRet e.val) [] [])
    | none => Pure.pure (sysReturn (punched c) (if c < n then bad else ret) [] [])
  else if advice = MADV_POPULATE_READ ∨ advice = MADV_POPULATE_WRITE then
    let write := advice = MADV_POPULATE_WRITE
    let acc : Access := if write then .write else .read
    -- why the page `k` pages from `first` cannot be faulted in, if it cannot
    let refused (k : Nat) : Option Nat := match mem.mapAt (first + k) with
      | none => some ENOMEM
      | some m =>
        if !(if write then m.prot.write else m.prot.read) || (feat.pku && pkeyDenies s.cpu.pkru m.pkey acc) then
          some EINVAL
        else if (mem.backings m.backing).filePage.any mem.files.beyondEof then some EFAULT
        else none
    let c := ((List.range n).takeWhile fun k => (refused k).isNone).length
    let done (k : Nat) : State := if write then s.withMem (mem.populate first k) else s
    match ← Req.request (.memFail n) with
    | some (e, k) => Pure.pure (sysReturn (done (min k.val c)) (errRet e.val) [] [])
    | none => Pure.pure (sysReturn (done c) (match refused c with
        | some e => if c < n then errRet e else 0
        | none => 0) [] [])
  else stop "madvise advice MADV_GUARD_INSTALL or MADV_GUARD_REMOVE"

end ZellicX86
