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

Not modelled: mappings of devices and special files (`FileMap.other`), `MAP_SYNC`, shared `MAP_HUGETLB`, private `MAP_GROWSDOWN`, `MAP_DROPPABLE`, `MAP_LOCKED`, `PROT_GROWSDOWN`/`PROT_GROWSUP`, execute-only memory on a CPU with protection
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
/-- `mmap` flag: reserve no swap space (`VM_NORESERVE`); with `MAP_HUGETLB`, no huge pages either. -/
def MAP_NORESERVE : Nat := 0x4000
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

/-- `may_expand_vm` (`mm/mmap.c`) in `s` for `n` new pages, of a data mapping or not (`is_data_mapping`): `RLIMIT_AS`
against all pages (`Memory.totalVm`), `RLIMIT_DATA` against the data pages (`Memory.dataVm`; `mayExpand`). Where
`RLIMIT_DATA` alone refuses, the kernel lets the pages through if it ignores that limit (`Request.dataLimitIgnored`). -/
def mayExpandVm (s : State) (n : Nat) (data : Bool) : Req Bool := do
  let rl := s.proc.signal.rlimits
  let mem := s.proc.mm.mem
  if mayExpand (rl RLIMIT_AS) (rl RLIMIT_DATA) false mem.totalVm mem.dataVm n data then Pure.pure true
  else if mayExpand (rl RLIMIT_AS) (rl RLIMIT_DATA) true mem.totalVm mem.dataVm n data then
    Req.request .dataLimitIgnored
  else Pure.pure false

/-- The bytes `check_data_rlimit` (`include/linux/mm.h`) counts against `RLIMIT_DATA` for a break `b`: those from the
initial break to `b` and those of the data segment, summed in 64-bit unsigned arithmetic as the kernel's. -/
def Mm.dataUse (mm : Mm) (b : Addr) : Nat := ((b - mm.startBrk) + (mm.endData - mm.startData)).toNat

/-- `check_data_rlimit` (`include/linux/mm.h`) for a break `b` and the soft limit `lim` of `RLIMIT_DATA`: unless the
limit is `RLIM_INFINITY`, the bytes it counts (`Mm.dataUse`) are at most the limit. -/
def Mm.dataFits (mm : Mm) (lim : BitVec 64) (b : Addr) : Bool :=
  lim == RLIM_INFINITY || decide (mm.dataUse b ≤ lim.toNat)

/-- `brk(b)` (`mm/mmap.c` `brk`): moves the program break to `b` and returns it, or on failure
returns the break unchanged. It fails for a break below `brkMin`, and for one past `RLIMIT_DATA` (`Mm.dataFits`). Within
the break's last page only the break moves, with no other check. Otherwise it may fail for a reason the model does not
track (`Request.memFail`: accounting, `vm.mmap_min_addr`, and when moving up the stack guard
gap below a mapping that grows down, `vm_start_gap`). Moving it down unmaps the pages above the new break's page,
whatever is mapped there, and fails when none is mapped, or when the unmapping would cut a huge page of a mapping of huge
pages (`Memory.cutsHuge`; `do_vmi_align_munmap` fails, and `brk` restores the old break). Moving it up maps zero pages,
read-write, from the old break's page to the new one's; it fails unless those pages and the one after them are free and
within user space (`check_brk_limits`, the check of the next mapping in `brk`), and the limits allow them (`mayExpandVm`,
data pages). -/
def sysBrk (feat : Features) (s : State) : Req StepResult := do
  let b := s.cpu.gpr.rdi
  let old := s.proc.mm.brk
  let keep : StepResult := sysReturn s old [] []
  if b.toNat < s.proc.mm.brkMin.toNat then Pure.pure keep else
  if !s.proc.mm.dataFits (s.proc.signal.rlimits RLIMIT_DATA).cur b then Pure.pure keep else
  let mem := s.proc.mm.mem
  let newP := pageUp b.toNat / 4096
  let oldP := pageUp old.toNat / 4096
  if newP = oldP then Pure.pure (sysReturn (s.withLayout mem b) b [] []) else
  match ← Req.request (.memFail 0) with
  | some _ => Pure.pure keep
  | none =>
    if newP < oldP then
      if !mem.anyMapped newP (oldP - newP) then Pure.pure keep
      else if mem.touchesFixed newP (oldP - newP) then
        Pure.pure (.stopped (.notModelled (.feature "brk over the vDSO or the initial stack")))
      else if mem.cutsHuge newP (oldP - newP) then Pure.pure keep
      else Pure.pure (sysReturn (s.withLayout (mem.unmap newP (oldP - newP)) b) b [] [])
    else if 4096 * newP > taskSize feat || !mem.free oldP (newP - oldP + 1) then Pure.pure keep
    else
      match ← mayExpandVm s (newP - oldP) true with
      | false => Pure.pure keep
      | true => Pure.pure (sysReturn (s.withLayout (mem.mapAnon oldP (newP - oldP) ⟨true, true, false⟩) b) b [] [])

/-- The error of a change of the layout that would cut a huge page of a mapping of huge pages (`Memory.cutsHuge`):
`EINVAL` (`mm/vma.c` `__split_vma`, `mm/hugetlb.c` `hugetlb_vm_op_split`), unless a failure the kernel checks first and
the model does not track comes before it (`Request.memFail`; `vms_gather_munmap_vmas`' `max_map_count` check, `ENOMEM`),
changing nothing either way. -/
def cutError : Req Nat := do
  match ← Req.request (.memFail 0) with
  | some (e, _) => Pure.pure e.val
  | none => Pure.pure EINVAL

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

/-- `mmap(addr, len, prot, flags, -1, off)` with `MAP_ANONYMOUS` and `MAP_HUGETLB` (`sysMmap`, whose checks before
come first): huge pages of the size the flags' bits 26–31 name (`MAP_HUGE_SHIFT`; 0 the default), one of the kernel's
(`LinuxBoot.hugeSizes`; else `EINVAL`). The kernel makes the request a private mapping of a new hugetlbfs file
(`mm/mmap.c` `ksys_mmap_pgoff`, `hugetlb_file_setup`), which may fail first (`Request.memFail`), and goes on as for a
file (`do_mmap`), in its order:
- the length is rounded up to the huge page size (modulo `2 ^ 64`; 0 is `EINVAL`) and must not exceed user space
  (`ENOMEM`); execute-only memory with protection keys is not modelled;
- a `MAP_FIXED` or `MAP_FIXED_NOREPLACE` address must be aligned to the huge page size (`EINVAL`;
  `fs/hugetlbfs/inode.c` `hugetlb_get_unmapped_area`), then leave room below `TASK_SIZE` (`ENOMEM`); the kernel's
  place (`Request.place`) must be aligned to it, and is checked as for any mapping, `MAP_32BIT` too (else `ENOMEM`);
- `MAP_FIXED_NOREPLACE` over a mapped page is `EEXIST`; `MAP_LOCKED` is not modelled;
- the offset must lie within the largest file (`EOVERFLOW`, `file_mmap_ok`, before the type); the type must be
  `MAP_PRIVATE` (`MAP_SHARED` and `MAP_SHARED_VALIDATE` share the file: not modelled; others `EINVAL`);
  `MAP_GROWSDOWN` is `EINVAL`;
- a `MAP_FIXED` range that would split a mapping of huge pages inside a huge page is `EINVAL` (`cutError`);
- the limits (`mayExpandVm`; `mm/vma.c` `__mmap_prepare`): the pages added to those a `MAP_FIXED` range replaces, of
  data where writable (`ENOMEM`, the old mappings kept);
- an offset not aligned to the huge page size is `EINVAL` (`hugetlbfs_file_mmap`), after a `MAP_FIXED` range's old
  mappings were taken out: they are put back, or all gone (`Request.pick`; `mm/vma.c` `vms_abort_munmap_vmas`);
- the pages are reserved, which may fail (`Request.memFail`, as any failure the model does not track, with a
  `MAP_FIXED` range's first part unmapped); with `MAP_NORESERVE` none are (`do_mmap` sets `VM_NORESERVE` for a hugetlbfs
  file whatever the overcommit setting, and `hugetlb_reserve_pages` reserves nothing then), so only the other failures
  remain, which the same request covers; and the range is mapped as private memory whose huge pages the kernel
  allocates and clears at their first fault (`Memory.mapHuge`, `Backing.hugeEmpty`), which may still fail
  (`hugeFault`: the hugetlb controller charges at the fault), and `rax` is its address. -/
def sysMmapHuge (prof : Profile) (s : State) : Req StepResult := do
  let feat := prof.feat
  let addr := s.cpu.gpr.rdi.toNat
  let len := s.cpu.gpr.rsi.toNat
  let prot := s.cpu.gpr.rdx.toNat
  let flags := s.cpu.gpr.r10.toNat
  let off := s.cpu.gpr.r9.toNat
  let fail (e : Nat) : Req StepResult := Pure.pure (sysReturn s (errRet e) [] [])
  let stop (what : String) : Req StepResult := Pure.pure (.stopped (.notModelled (.feature what)))
  let mem := s.proc.mm.mem
  let code := flags / 2 ^ 26 % 64
  let hs : Option Nat := if code = 0 then prof.linux.hugeSizes.head? else
    if code ∈ prof.linux.hugeSizes then some code else none
  match hs with
  | none => fail EINVAL
  | some h => do
  match ← Req.request (.memFail 0) with
  | some (e, _) => fail e.val
  | none =>
  let sz := 2 ^ (h - 12) * 4096
  let L := (len + sz - 1) / sz * sz % 2 ^ 64
  let fixed := anyBits flags (MAP_FIXED ||| MAP_FIXED_NOREPLACE)
  if L = 0 then fail EINVAL
  else if feat.pku && prot = 4 then stop "execute-only memory with protection keys"
  else if L > taskSize feat then fail ENOMEM
  else do
  let a ← if fixed then Pure.pure addr else do
    let a ← Req.request (.place L)
    Pure.pure a.toNat
  let n := L / 4096
  let ty := flags % 16
  if fixed && addr % sz ≠ 0 then fail EINVAL
  else if fixed && addr > taskSize feat - L then fail ENOMEM
  else if !fixed && !(a % sz = 0 && 4096 ≤ a && a + L ≤ taskSize feat && mem.free (a / 4096) n) then
    fail ENOMEM
  else if !fixed && anyBits flags MAP_32BIT &&
      !(a + L ≤ 0x80000000 && (0x40000000 ≤ a || (addr / 4096 ≠ 0 && addr / 4096 * 4096 ≤ a))) then fail ENOMEM
  else if anyBits flags MAP_FIXED_NOREPLACE && mem.anyMapped (a / 4096) n then fail EEXIST
  else if anyBits flags MAP_LOCKED then stop "MAP_LOCKED"
  else if !fileMmapOk maxLfsFilesize L (off / 4096) then fail EOVERFLOW
  else if ty = MAP_SHARED || ty = MAP_SHARED_VALIDATE then stop "shared MAP_HUGETLB"
  else if ty ≠ MAP_PRIVATE then fail EINVAL
  else if anyBits flags MAP_GROWSDOWN then fail EINVAL
  else if mem.touchesFixed (a / 4096) n then stop "mmap over the vDSO or the initial stack"
  else if fixed && mem.cutsHuge (a / 4096) n then do fail (← cutError)
  else do
  -- the limits (`__mmap_prepare`'s `may_expand_vm`, before the file's `mmap`): the pages added to those replaced, data
  -- where writable (private)
  if !(← mayExpandVm s (n - mem.mappedIn (a / 4096) n) (protOf prot).write) then fail ENOMEM
  else if off % sz ≠ 0 then do
    let gap ← Req.request (.pick 1)
    let mem' := if fixed && gap.val = 1 then mem.unmap (a / 4096) n else mem
    Pure.pure (sysReturn (s.withMem mem') (errRet EINVAL) [] [])
  else
  match ← Req.request (.memFail (if fixed then n else 0)) with
  | some (e, k) =>
    let mem' := if fixed then mem.unmap (a / 4096) k.val else mem
    Pure.pure (sysReturn (s.withMem mem') (errRet e.val) [] [])
  | none =>
    Pure.pure (sysReturn (s.withMem (mem.mapHuge (a / 4096) n (protOf prot) h)) (BitVec.ofNat 64 a) [] [])

/-- `mmap(addr, len, prot, flags, fd, off)` (`arch/x86/kernel/sys_x86_64.c` `mmap`,
`ksys_mmap_pgoff`, `vm_mmap_pgoff`, `do_mmap`), of anonymous memory, private or shared, and of the
pages of a file (`FileMap.pages`), privately or shared. In the kernel's order:
- `off` must be page-aligned (`EINVAL`); without `MAP_ANONYMOUS`, `fd` must be open, and not with
  `O_PATH` (`EBADF`; `fdget`, `FdTable.descNoPath`); a device or special file (`FileMap.other`) is not modelled, and `MAP_HUGETLB`
  is `EINVAL` with a file;
- `MAP_HUGETLB` without a file maps huge pages (`sysMmapHuge`);
- `len` must not be 0 (`EINVAL`), and rounded up to pages neither wrap (`ENOMEM`) nor exceed user
  space (`ENOMEM`);
- the address: with `MAP_FIXED` or `MAP_FIXED_NOREPLACE` it is `addr`, which must leave room for
  the length below `TASK_SIZE` (`ENOMEM`) and be page-aligned (`EINVAL`); otherwise the kernel's
  choice (`Request.place`), which must be page-aligned, at or above the first page, free up to
  the length within user space, and end outside the guard gap below a stack (`Memory.inStackGap`, the profile's
  `stackGuardGap`) (else `ENOMEM`); with `MAP_32BIT`, the end is at most
  `0x80000000` and the start at least `0x40000000`, except that a nonzero page-rounded-down hint may be
  accepted below the search range, possibly raised to the page-rounded-up `mmap_min_addr`
  (`mm/mmap.c` `round_hint_to_min`; `arch/x86/kernel/sys_x86_64.c` `find_start_end`,
  `arch_get_unmapped_area`). Since the `vm.mmap_min_addr` setting can change at run time, the model
  does not check it here but leaves it to the kernel's choice of place (`Request.place`), so a low
  hint permits a start at or above its rounded-down page. Fixed mappings ignore `MAP_32BIT`;
- with `MAP_FIXED_NOREPLACE`, a page mapped in the range fails with `EEXIST`;
- with `MAP_FIXED`, a range that would split a mapping of huge pages inside a huge page fails with `EINVAL`
  (`Memory.cutsHuge`, `cutError`), changing nothing;
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
- the limits (`mayExpandVm`: the range's pages less those it replaces, data if private and writable): `ENOMEM`;
- a failure the model does not track (`Request.memFail`), which with `MAP_FIXED` may leave a first
  part of the range unmapped;
- the range is mapped with protection `prot` (`protOf`), replacing what was mapped there, and `rax`
  is its address: private anonymous memory of zeros (`Memory.mapAnon`), a new shmem file for shared
  anonymous memory (`Memory.mapShmem`), or the file pages from `off` on (`Memory.mapFile`), whose
  maximum protection lacks `write` for a shared mapping of a descriptor not open for writing or of
  a write-sealed memfd and `exec` on a `noexec` mount.
The kernel ignores the other flags (`MAP_NORESERVE` without `MAP_HUGETLB`, `MAP_POPULATE`, `MAP_STACK` change nothing the
model shows; `MAP_POPULATE` of a private file mapping makes the copies at once,
which `EnvEvent.cowBreak` covers) and the offset of an anonymous mapping without `MAP_HUGETLB`. -/
def sysMmap (prof : Profile) (s : State) : Req StepResult := do
  let feat := prof.feat
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
  else if anyBits flags MAP_HUGETLB then (if anon then sysMmapHuge prof s else fail EINVAL)
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
  -- the end: the range mapped by `mapIt` (a data mapping or not), unless the limits refuse the pages it adds to those
  -- it replaces, or the kernel fails for a reason not tracked
  let finish (data : Bool) (mapIt : Memory → Memory) : Req StepResult :=
    if mem.touchesFixed (a / 4096) n then stop "mmap over the vDSO or the initial stack"
    else if fixed && mem.cutsHuge (a / 4096) n then do fail (← cutError) else do
    if !(← mayExpandVm s (n - mem.mappedIn (a / 4096) n) data) then fail ENOMEM else
    match ← Req.request (.memFail (if fixed then n else 0)) with
    | some (e, k) =>
      let mem' := if fixed then mem.unmap (a / 4096) k.val else mem
      Pure.pure (sysReturn (s.withMem mem') (errRet e.val) [] [])
    | none => Pure.pure (sysReturn (s.withMem (mapIt mem)) (BitVec.ofNat 64 a) [] [])
  let ty := flags % 16
  if fixed && addr > taskSize feat - L then fail ENOMEM
  else if fixed && addr % 4096 ≠ 0 then fail EINVAL
  else if !fixed && !(a % 4096 = 0 && 4096 ≤ a && a + L ≤ taskSize feat && mem.free (a / 4096) n &&
      !mem.inStackGap (a / 4096 + n) prof.linux.stackGuardGap) then
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
    else if ty = MAP_SHARED then finish false (·.mapShmem (a / 4096) n (protOf prot))
    else finish (bitSet prot 1) (·.mapAnon (a / 4096) n (protOf prot))
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
        finish (!shared && write) (·.mapFile (a / 4096) n (protOf prot) maxProt ⟨id, pg⟩ shared)
    | _ => fail ENODEV

/-- `munmap(addr, len)` (`mm/vma.c` `do_vmi_munmap`): `addr` must be page-aligned, `len` not 0,
and the range within user space (`EINVAL`); the pages of the range, rounded up to pages, are
unmapped. With nothing mapped there it returns 0 at once; a range that would split a mapping of huge pages
inside a huge page fails with `EINVAL` (`Memory.cutsHuge`, `cutError`); otherwise it may fail for a reason the model does not track
(`Request.memFail`), changing nothing. -/
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
  else if mem.cutsHuge first n then do Pure.pure (sysReturn s (errRet (← cutError)) [] [])
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
maximum, so such a page is the first of its VMA in the range.
A range that starts inside a huge page of a mapping of huge pages (`Mapping.huge`) whose protection `prot` changes fails
with `EINVAL` before any change, unless its first page refuses `prot`; one that ends inside one fails so when the walk
reaches that mapping's VMA, the VMAs before it changed: the pages before some huge page boundary at or before the last
page's huge page (`Request.pick`; the model does not know where that VMA starts). Where the protection of that page is
already `prot`, the kernel does not split its VMA (`mprotect_fixup`: `newflags == oldflags` returns at once; the
protection key and `VM_ACCOUNT`, the other flags `mprotect` sets, do not change for such a mapping on x86), and nothing
is cut. -/
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
      -- (a VMA whose protection does not change is not split: `mprotect_fixup`'s `newflags == oldflags`)
      let changes (p : Nat) : Bool := (mem.mapAt p).any (·.prot != protOf prot)
      if 0 < c && mem.hugeCut first first && changes first then Pure.pure (sysReturn s (errRet EINVAL) [] [])
      else if c = n && mem.hugeCut (first + n - 1) (first + n) && changes (first + n - 1) then do
        let j ← Req.request (.pick (mem.hugeStart (first + n - 1) - first))
        Pure.pure (sysReturn (s.withMem ((mem.protect first j.val (protOf prot)).renumber first j.val))
          (errRet EINVAL) [] [])
      else
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

/-- Whether the kernel refuses to move the `l` pages from page `src` to page `dst`, one VMA's part of an `mremap` move
(of huge pages of `2 ^ s` bytes for `h = some s`), before changing anything for it, in memory `m` as the earlier parts
left it (`EINVAL`): huge pages need `src` and `dst` on their boundaries (`mm/mremap.c` `check_prep_vma`,
`align_hugetlb`); unmapping the destination (`mremap_to`'s `do_munmap`) must not end above `TASK_SIZE` (`mm/vma.c`
`do_vmi_munmap`) nor split a mapping of huge pages inside a huge page (`Memory.cutsHuge`). -/
def remapRefused (feat : Features) (m : Memory) (src dst l : Nat) (h : Option Nat) : Bool :=
  h.any (fun s => src % 2 ^ (s - 12) != 0 || dst % 2 ^ (s - 12) != 0) || (dst + l) * 4096 > taskSize feat ||
    m.cutsHuge dst l

/-- An `mremap` move with `MREMAP_FIXED` of an unchanged length (`mm/mremap.c` `remap_move`): the parts `ps` of the
range from page `P` (`Memory.moveParts`, offsets from `P`), in order, each moved to the same place relative to page `D`
by `move` (`move m src dst l`: the `l` pages from `src` to `dst` in `m`), in memory `m` as the earlier parts left it.
`old` is the memory before the call; `dontunmap` is `MREMAP_DONTUNMAP`, and `keeps m src l` whether the limits let the
`l` pages from `src` stay mapped as well (`may_expand_vm` in memory `m`). For each part:
- a part of huge pages extends to the end of its last huge page (`align_hugetlb`, `vma_kernel_pagesize`: only the
  range's last part can end inside one, and the kernel moves that huge page whole);
- with `fail = some (e, k)` (`Request.memFail`: a failure the model does not track, after the first `k` pages), only its
  pages before offset `k` move, down to a huge page's boundary, and never all pages of the last part (the kernel does
  not fail after it moved the last VMA, so a failure beyond falls in the last part);
- if those pages, or with none of them the part's first (huge) page, are refused (`remapRefused`: the kernel checks a
  VMA before anything can fail in moving it), or with `dontunmap` the part is of huge pages (`check_prep_vma`: a
  hugetlb VMA is `VM_DONTEXPAND`, `fs/hugetlbfs/inode.c`), the call ends with `EINVAL`, the earlier parts moved;
- with `dontunmap`, their destination is unmapped and the limits checked for them (`mremap_to`: `do_munmap`, then
  `may_expand_vm` with the part's own flags, in the memory the earlier parts left, where each moved part counts
  twice), for the pages that move together: a part may hold several VMAs (`Memory.moveParts`), which the kernel checks
  one by one, and its refusal at a later one, the earlier ones moved, is among a failure's outcomes (`Request.memFail`
  at that VMA); if they refuse, the call ends with `ENOMEM`, that destination unmapped and the earlier parts moved;
- else they move; if the failure falls in this part, the call ends with `e`, and of the part's next pages, `j`
  (`Request.pick`) may have had their destination unmapped (`mremap_to` unmaps it before `move_vma` fails; only `j`
  that the kernel would not refuse, whole huge pages, else none), and the copy the kernel made of them may be kept,
  without contents (`Request.pick 1`: `move_vma` failed to unmap it).
Returns the memory and the error: `none` when every part moved; with `fail`, its error when there is no part. -/
def remapParts (feat : Features) (old : Memory) (P D : Nat) (fail : Option (Nat × Nat)) (dontunmap : Bool)
    (keeps : Memory → Nat → Nat → Req Bool) (move : Memory → Nat → Nat → Nat → Req Memory) :
    List (Nat × Nat × Option Nat) → Memory → Req (Memory × Option Nat)
  | [], m => Pure.pure (m, fail.map (·.1))
  | (o, l, h) :: ps, m => do
    let hp := h.elim 1 fun s => 2 ^ (s - 12)
    let l := (l + hp - 1) / hp * hp
    let k := match fail with
      | some (_, k) => min (if ps.isEmpty then l - hp else l) ((k - o) / hp * hp)
      | none => l
    if remapRefused feat m (P + o) (D + o) (max k hp) h || (dontunmap && h.isSome) then Pure.pure (m, some EINVAL)
    else do
    let m := if dontunmap && 0 < k then m.unmap (D + o) k else m
    let ok ← if dontunmap && 0 < k then keeps m (P + o) k else Pure.pure true
    if !ok then Pure.pure (m, some ENOMEM) else do
    let m ← if 0 < k then move m (P + o) (D + o) k else Pure.pure m
    match fail with
    | some (e, _) =>
      if k < l then do
        let q := o + k
        let j ← Req.request (.pick (l - k))
        let j := if j.val % hp = 0 && !remapRefused feat m (P + q) (D + q) j.val h then j.val else 0
        let m₁ := m.unmap (D + q) j
        let c ← Req.request (.pick 1)
        Pure.pure (if c.val = 1 then (m₁.remapEmpty (D + q) j old (P + q)).renumber (D + q) j else m₁, some e)
      else remapParts feat old P D fail dontunmap keeps move ps m
    | none => remapParts feat old P D fail dontunmap keeps move ps m

/-- `mremap(addr, old_len, new_len, flags, new_addr)` (`mm/mremap.c` `do_mremap`): moves, grows or
shrinks the mapping of the `old_len` bytes at `addr`; the lengths are rounded up to pages (modulo
2^64, as the kernel's `PAGE_ALIGN`). In the kernel's order:
- `flags` may have only `MREMAP_MAYMOVE`, `MREMAP_FIXED`, `MREMAP_DONTUNMAP`; `addr` must be
  page-aligned; the new length must not be 0 or exceed user space (each `EINVAL`);
- with `MREMAP_FIXED` or `MREMAP_DONTUNMAP`, `new_addr` must leave room for the new length below
  `TASK_SIZE` and be page-aligned, `MREMAP_MAYMOVE` must be given, `MREMAP_DONTUNMAP` must keep the
  length, and the old and new ranges must not overlap (each `EINVAL`);
- a mapping of huge pages at `addr` (`Mapping.huge`; `mm/mremap.c` `align_hugetlb`, `check_prep_vma`): both lengths
  are rounded up to its huge pages, `addr` and `new_addr` (given or not) must be aligned to them, the mapping may not
  grow, `MREMAP_DONTUNMAP` and an old length of 0 are refused (each `EINVAL`); it then moves and shrinks as below,
  with the rounded lengths. A move (`MREMAP_FIXED` with an unchanged length, before this rounding: `vrm_move_only`)
  instead rounds only its last part, VMA by VMA (`remapParts`): its range ends at the end of its last page's huge page;
- the limits (`mayExpandVm`), unless an error the kernel finds first applies (`check_prep_vma`: no mapping at `addr`;
  for a call that maps new pages, an old length of 0 on a private mapping, or an old range beyond one VMA, below): a
  growth by its new pages, with the flags of `addr`'s mapping, and with `MREMAP_DONTUNMAP` the moved pages; else
  `ENOMEM`. With `MREMAP_DONTUNMAP` and `MREMAP_FIXED` the lengths are equal, so the call is a move (below): the kernel
  then unmaps each part's destination (`mremap_to`; that unmapping stays) and checks the limits part by part, each part
  with its own flags (`remapParts`);
- unless such an earlier error applies, an `MREMAP_FIXED` destination is `EINVAL` if unmapping it (`mremap_to`'s
  `do_munmap`, `mm/vma.c` `do_vmi_munmap`) would split a mapping of huge pages inside a huge page (`Memory.cutsHuge`)
  or, for a call that changes the length, end above `TASK_SIZE` (the rounding to huge pages can make it); for a move
  over several areas, part by part (`remapParts`);
- then the call may fail for a reason the model does not track (`Request.memFail`): lack of memory
  and its accounting, `vm.max_map_count`, the security module
  (`mmap_min_addr` for a new place), and a boundary between two VMAs the kernel did not merge, which
  the model allows (`EFAULT`) unless the pages the kernel checks are of one area
  (`Memory.sameArea`): then an `EFAULT` answer means no failure. What a failure leaves:
  - a failed `MREMAP_FIXED` move of an unchanged length may have moved a first part of the range
    (the kernel moves VMA by VMA) and unmapped the destination of part of the next (the count `k` in
    `Request.memFail`'s answer: the pages moved; `remapParts`);
  - a failed `MREMAP_FIXED` call that changes the length may have unmapped the destination (count 1
    or 2), and when shrinking also the tail of the old range (count 2);
  - any other failure changes nothing, as does every failure of a call with one of the errors `check_prep_vma` finds
    before the limits (above: the kernel ends the call there, so it fails before changing anything);
  - and a failed move may leave the copy the kernel made for it mapped, without contents, at
    `new_addr` or where the kernel placed it (`Request.pick`, then `Request.place`: the kernel
    failed to remove the copy, `move_vma`);
- `MREMAP_FIXED` with an unchanged length moves every mapped page of the old range to the same
  place relative to `new_addr`, replacing what is mapped there (`remap_move`, VMA by VMA: `remapParts` over
  `Memory.moveParts`); holes in the range are allowed, and the destination's pages across from them keep their
  mappings, but the first page must be mapped (`EFAULT`). A part the kernel refuses (`remapRefused`: huge pages whose
  source or destination is not on a huge page's boundary, a destination that would cut a huge page or end above
  `TASK_SIZE`) ends the call with `EINVAL`, the parts before it moved. With `MREMAP_DONTUNMAP` a later part of huge
  pages is refused likewise, and a part the limits refuse ends the call with `ENOMEM`, its destination unmapped and the
  parts before it moved, their old pages kept;
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
  old range's tail), or to a place the kernel chooses (`Request.place`; checked as for `mmap`, the end outside the
  guard gap of `gap` pages below a stack included, `Memory.inStackGap`, else `ENOMEM`; `new_addr` without
  `MREMAP_FIXED` is a hint): the old range's pages move there
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
def sysMremap (feat : Features) (gap : Nat) (s : State) : Req StepResult := do
  let addr := s.cpu.gpr.rdi.toNat
  let oldL₀ := pageUp s.cpu.gpr.rsi.toNat % 2 ^ 64
  let newL₀ := pageUp s.cpu.gpr.rdx.toNat % 2 ^ 64
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
  let D := newAddr / 4096
  -- a move: `MREMAP_FIXED` with an unchanged length (`vrm_move_only`, before any rounding to huge pages)
  let moveOnly := fixed && oldL₀ = newL₀
  -- a mapping of huge pages at `addr`: the lengths rounded up to its huge pages (`align_hugetlb`); a move's range to the
  -- end of its last page's huge page (`remap_move` rounds its last VMA's part)
  let hz := (mem.mapAt P).bind (·.huge)
  let sz := 2 ^ (hz.getD 12 - 12) * 4096
  let up (x : Nat) : Nat := match hz with
    | some _ => (x + sz - 1) / sz * sz % 2 ^ 64
    | none => x
  let lastEnd : Nat := ((mem.mapAt (P + oldL₀ / 4096 - 1)).bind (·.huge)).elim oldL₀ fun s =>
    (addr + oldL₀ + 2 ^ s - 1) / 2 ^ s * 2 ^ s - addr
  let oldL := if moveOnly then lastEnd else up oldL₀
  let newL := if moveOnly then lastEnd else up newL₀
  let oldn := oldL / 4096
  let newn := newL / 4096
  if flags ≥ 8 || addr % 4096 ≠ 0 || newL₀ = 0 || newL₀ > taskSize feat then fail EINVAL
  else if given && (newAddr > taskSize feat - newL₀ || newAddr % 4096 ≠ 0 || !maymove ||
      (dontunmap && oldL₀ ≠ newL₀) || ((addr + oldL₀) % 2 ^ 64 > newAddr && newAddr + newL₀ > addr)) then
    fail EINVAL
  else if hz.isSome && (addr % sz ≠ 0 || newAddr % sz ≠ 0 || newL > oldL || dontunmap || oldL = 0) then fail EINVAL
  else if mem.touchesFixed P (max oldn 1) || (fixed && mem.touchesFixed D newn) then
    if P = vsyscallPage.toNat then fail EFAULT else stop "mremap over the vDSO or the initial stack"
  else if mem.touchesStack P (max oldn 1) then stop "mremap of the initial stack"
  else
  -- the pages whose VMA boundaries the kernel checks
  let chk := if moveOnly then oldn else if newL > oldL || given then min oldn newn else 1
  -- the `n` pages from `src` moved to `dst`, with new areas there, and what they leave behind
  let moved (m : Memory) (src dst n : Nat) : Req Memory :=
    let m₁ := (m.move src dst n).renumber dst n
    if dontunmap then Pure.pure (m₁.remapEmpty src n mem src) else keepSources mem src (mem.runs src n) m₁
  -- the errors `check_prep_vma` returns before the limits: no mapping at `addr`; for a call that maps new pages, an old
  -- length of 0 on a private mapping, an old range (cut to the new length when shrinking) beyond one VMA
  let early := (mem.mapAt P).isNone || (!moveOnly && (newL > oldL || given) &&
    (if oldL = 0 then !(mem.mapAt P).any mem.sharedAt else !mem.oneArea P (min oldn newn)))
  -- the limits (`check_prep_vma`'s `may_expand_vm`, before any change): a growth by its new pages, with the flags of
  -- `addr`'s mapping; with `MREMAP_DONTUNMAP` and no `MREMAP_FIXED` (no destination to unmap: with both, the lengths are
  -- equal, so the call is a move), the moved pages; for a move, part by part in `remapParts`, after each part's
  -- destination is unmapped (`mremap_to`), each with its own flags
  let dataAt (m : Mapping) : Bool := m.prot.write && !m.growsDown && !(mem.backings m.backing).isFile
  let data := (mem.mapAt P).any dataAt
  let grows ← if !early && newn > oldn then mayExpandVm s (newn - oldn) data else Pure.pure true
  if !grows then fail ENOMEM else
  -- unmapping a fixed destination (`mremap_to`'s `do_munmap`); a move of several VMAs unmaps it part by part
  -- (`remapParts`), which also checks a move's end against `TASK_SIZE`
  if fixed && !early && (!moveOnly || mem.sameArea P oldn) &&
      (mem.cutsHuge D newn || (!moveOnly && (D + newn) * 4096 > taskSize feat)) then fail EINVAL else
  let keeps ← if !early && dontunmap && !moveOnly then mayExpandVm s oldn data else Pure.pure true
  if !keeps then Pure.pure (sysReturn s (errRet ENOMEM) [] []) else
  -- a move's part of `n` pages from `src` (of one VMA's kind, `Memory.moveParts`): the limits in `m`, its flags
  let partKeeps (m : Memory) (src n : Nat) : Req Bool := mayExpandVm (s.withMem m) n ((mem.mapAt src).any dataAt)
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
    -- (after an error `check_prep_vma` finds, a failure changes nothing)
    if early then fail e.val
    else if moveOnly then do
      let (m, err) ← remapParts feat mem P D (some (e.val, k.val)) dontunmap partKeeps moved (mem.moveParts P oldn) mem
      Pure.pure (sysReturn (s.withMem m) (errRet (err.getD e.val)) [] [])
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
          if !fixed && !(a % 4096 = 0 && 4096 ≤ a && a + newL ≤ taskSize feat && m₂.free (a / 4096) newn &&
              !m₂.inStackGap (a / 4096 + newn) gap) then
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
    let (m, err) ← remapParts feat mem P D none dontunmap partKeeps moved (mem.moveParts P oldn) mem
    match err with
    | some e => Pure.pure (sysReturn (s.withMem m) (errRet e) [] [])
    | none => done m newAddr
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
    if !fixed && !(a % 4096 = 0 && 4096 ≤ a && a + newL ≤ taskSize feat && m₁.free (a / 4096) newn &&
        !m₁.inStackGap (a / 4096 + newn) gap) then
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
  if !fixed && !(a % 4096 = 0 && 4096 ≤ a && a + newL ≤ taskSize feat && m₂.free (a / 4096) newn &&
              !m₂.inStackGap (a / 4096 + newn) gap) then
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
- `advice` must be one the kernel knows (`madvise_behavior_valid`; `EINVAL`): `MADV_HUGEPAGE`,
  `MADV_NOHUGEPAGE` and `MADV_COLLAPSE` only with `CONFIG_TRANSPARENT_HUGEPAGE` (`LinuxBoot.thp`); those
  the kernel knows only with `CONFIG_KSM` or `CONFIG_MEMORY_FAILURE` (`MADV_MERGEABLE`, `MADV_UNMERGEABLE`,
  `MADV_HWPOISON`, `MADV_SOFT_OFFLINE`), and `MADV_COLLAPSE`, are not modelled;
- `start` must be page-aligned, and `len`, rounded up to pages, must neither wrap to 0 nor make
  the range wrap (`EINVAL`); an empty range returns 0;
- the advice applies to the mapped pages of the range; if some page of it is unmapped, the call
  returns `ENOMEM` afterwards (`madvise_walk_vmas`).
`MADV_DONTNEED` and `MADV_DONTNEED_LOCKED` drop the pages' private contents (`Memory.discard`): a
page of anonymous memory reads zeros afterwards, a page of a private file mapping its file page
(`Mapping.origin`), a page of a shared one is unchanged. `MADV_NORMAL`, `MADV_RANDOM`,
`MADV_SEQUENTIAL`, `MADV_WILLNEED`, `MADV_DONTDUMP`, `MADV_DODUMP`, `MADV_COLD`, `MADV_PAGEOUT`,
`MADV_DONTFORK`, `MADV_DOFORK`, `MADV_KEEPONFORK`, `MADV_HUGEPAGE` and `MADV_NOHUGEPAGE` change nothing
the model has but VMA boundaries (read-ahead, the core dump, reclaim, what `fork` copies, whether the
kernel backs the pages with transparent huge pages, `mm/khugepaged.c` `hugepage_madvise`, which the model
does not have): those that change VMA flags (all but `MADV_WILLNEED`, `MADV_COLD`, `MADV_PAGEOUT`) give the range's pages new
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
(`Memory.populate`); either allocates the huge pages of a mapping of huge pages it faults in
(`Memory.populateHuge`); a failure the model does not track (lack of memory, a huge page the kernel
cannot allocate: `EFAULT`) stops after a first part.
A mapping of huge pages (`Mapping.huge`) is a private mapping of a hugetlbfs file to the kernel: `MADV_WIPEONFORK`
and `MADV_FREE` refuse it (`EINVAL`), `MADV_REMOVE` too (`EACCES`), `MADV_COLD` and `MADV_PAGEOUT` too (`EINVAL`,
`can_madv_lru_vma`); `MADV_DONTNEED` and `MADV_DONTNEED_LOCKED` need the range to start on a huge page boundary
there (`EINVAL`) and drop whole huge pages only (the end rounded down, `madvise_dontneed_free_valid_vma`); the advice
that changes VMA flags fails with `EINVAL` where it would split such a mapping inside a huge page (`Memory.hugeCut`):
at the range's start before any change, at its end after the VMAs before the last one's, whose pages, like the range's
others, get new areas (the model's areas allow more boundaries than the kernel made). The kernel splits a VMA only
where the advice changes its flags (`madvise_update_vma`: `new_flags == vma->vm_flags` returns at once); the model does
not track the flags this advice sets (`VM_RAND_READ`, `VM_DONTDUMP`, …), so at each such cut the environment says
whether they change (`Request.pick`: `EINVAL`, or nothing cut).
Not modelled: `MADV_GUARD_INSTALL` and `MADV_GUARD_REMOVE`, and ranges over the vDSO. -/
def sysMadvise (prof : Profile) (s : State) : Req StepResult := do
  let feat := prof.feat
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
    MADV_DONTNEED_LOCKED, MADV_GUARD_INSTALL, MADV_GUARD_REMOVE] ++
    if prof.linux.thp then [MADV_HUGEPAGE, MADV_NOHUGEPAGE] else []
  let byConfig := [MADV_MERGEABLE, MADV_UNMERGEABLE, MADV_HWPOISON, MADV_SOFT_OFFLINE]
  let flagAdvice := [MADV_NORMAL, MADV_RANDOM, MADV_SEQUENTIAL, MADV_DONTDUMP, MADV_DODUMP, MADV_DOFORK,
    MADV_KEEPONFORK, MADV_HUGEPAGE, MADV_NOHUGEPAGE]
  let hints := [MADV_WILLNEED, MADV_COLD, MADV_PAGEOUT]
  if advice ∈ byConfig then stop "madvise advice that depends on the kernel's configuration"
  else if prof.linux.thp ∧ advice = MADV_COLLAPSE then stop "madvise advice MADV_COLLAPSE"
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
    if mem.hugeCut first first then fail EINVAL
    else
    -- a mapping of huge pages at the end gives up whole huge pages only
    let n' := if mem.hugeCut (first + n - 1) (first + n) then mem.hugeStart (first + n - 1) - first else n
    Pure.pure (sysReturn (s.withMem (mem.discard first n')) ret [] [])
  else if advice = MADV_COLD ∨ advice = MADV_PAGEOUT then
    -- VMA by VMA, up to the first of huge pages
    if (List.range n).any fun k => ((mem.mapAt (first + k)).bind (·.huge)).isSome then fail EINVAL
    else match ← Req.request (.memFail 0) with
    | some (e, _) => fail e.val
    | none => Pure.pure (sysReturn s ret [] [])
  else if advice ∈ flagAdvice ∨ advice ∈ hints ∨ advice = MADV_DONTFORK then
    -- advice that changes VMA flags splits VMAs (`madvise_update_vma`), also before a failure
    let s' := if advice ∈ hints then s else s.withMem (mem.renumber first n)
    -- (a cut only where the VMA's flags change: `madvise_update_vma`; the model does not track them, so the
    -- environment says)
    let cutStart ← if advice ∉ hints && mem.hugeCut first first then
      Req.request (.pick 1) else Pure.pure (0 : Fin 2)
    let cutEnd ← if advice ∉ hints && cutStart.val = 0 && mem.hugeCut (first + n - 1) (first + n) then
      Req.request (.pick 1) else Pure.pure (0 : Fin 2)
    if cutStart.val = 1 then fail EINVAL
    else if cutEnd.val = 1 then Pure.pure (sysReturn s' (errRet EINVAL) [] [])
    else
    match ← Req.request (.memFail 0) with
    | some (e, _) => Pure.pure (sysReturn s' (errRet e.val) [] [])
    | none => Pure.pure (sysReturn s' ret [] [])
  else
  -- the number of pages before the first mapped one that fails `ok`: the VMAs before it are done
  let upTo (ok : Mapping → Bool) : Nat :=
    ((List.range n).takeWhile fun k => (mem.mapAt (first + k)).all ok).length
  let anonPriv (m : Mapping) : Bool := m.origin.isNone && !mem.sharedAt m && m.huge.isNone
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
      | some m => if m.origin.isNone && m.huge.isNone then errRet EINVAL else errRet EACCES
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
    -- (a huge page faulted in is allocated whole, for a read too)
    let mem₁ (k : Nat) : Memory := mem.populateHugeRange first k
    let done (k : Nat) : State := s.withMem (if write then (mem₁ k).populate first k else mem₁ k)
    match ← Req.request (.memFail n) with
    | some (e, k) => Pure.pure (sysReturn (done (min k.val c)) (errRet e.val) [] [])
    | none => Pure.pure (sysReturn (done c) (match refused c with
        | some e => if c < n then errRet e else 0
        | none => 0) [] [])
  else stop "madvise advice MADV_GUARD_INSTALL or MADV_GUARD_REMOVE"

end ZellicX86
