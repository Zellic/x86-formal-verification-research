import ZellicX86.Spec.Linux.Syscall.Mm
/-!
# Linux system calls: `prctl`

`prctl(option, arg2, arg3, arg4, arg5)` (`kernel/sys.c`) with the one option the model has, `PR_SET_VMA` with
`PR_SET_VMA_ANON_NAME`: naming the anonymous memory of a range. Every other option stops as not modelled.

Sources: Linux v6.18 `kernel/sys.c` (`prctl`, `prctl_set_vma`), `mm/madvise.c` (`set_anon_vma_name`,
`madvise_set_anon_name`, `madvise_walk_vmas`, `madvise_vma_behavior`, `madvise_update_vma`), `mm/util.c`
(`strndup_user`), `include/linux/mm.h`, `include/uapi/linux/prctl.h`, `security/commoncap.c` and
`security/yama/yama_lsm.c` (the security modules' `task_prctl`, which pass `PR_SET_VMA` on), `PR_SET_VMA(2const)`.
-/
namespace ZellicX86

/-- `prctl`'s option for a range of the address space (`include/uapi/linux/prctl.h`). -/
def PR_SET_VMA : Nat := 0x53564d41
/-- `PR_SET_VMA`'s sub-option that names the anonymous memory of a range (`include/uapi/linux/prctl.h`). -/
def PR_SET_VMA_ANON_NAME : Nat := 0
/-- The size of an anonymous VMA's name with its NUL (`mm/madvise.c` `ANON_VMA_NAME_MAX_LEN`). -/
def anonNameMax : Nat := 80

/-- A byte a VMA's name may hold (`mm/madvise.c` `is_valid_name_char`): printable ASCII, and none of ``\ ` $ [ ]``. -/
def anonNameChar (b : Byte) : Bool :=
  decide (0x20 ≤ b.toNat ∧ b.toNat < 0x7f) && !([0x5c, 0x60, 0x24, 0x5b, 0x5d] : List Nat).contains b.toNat

/-- `prctl` (`kernel/sys.c`): the option is an `int` (`rdi`), its arguments `rsi rdx r10 r8`.

`PR_SET_VMA` (`prctl_set_vma`): on a kernel without `CONFIG_ANON_VMA_NAME` (`LinuxBoot.anonVmaName`), or with a
sub-option other than `PR_SET_VMA_ANON_NAME`, `EINVAL`. Otherwise `set_anon_vma_name (start, len, name)`, in the
kernel's order:
- the name, unless its address is 0 (which unnames): at most 79 bytes and a NUL (`strndup_user`, `userStr`: else
  `EINVAL`; a byte the kernel cannot read before the NUL, `EFAULT`); its copies may find no memory (`Request.memFail`;
  `strndup_user` allocates first); every byte printable and none of ``\ ` $ [ ]`` (`EINVAL`);
- the range, as `madvise`'s: `start` page-aligned, the length rounded up to whole pages not overflowing (`EINVAL`); an
  empty range does nothing;
- the walk over the range's VMAs (`madvise_walk_vmas`): a VMA of a file that is not anonymous shared memory stops it
  with `EBADF` (`madvise_vma_behavior`: `vma->vm_file && !vma_is_anon_shmem`), the pages before it done. Shared
  anonymous memory (`FileId.shmem`, `shmem_zero_setup`) is anonymous shared memory, and so is a mapping of a shmem file
  without links when it was mapped (`mm/shmem.c` `shmem_mmap`: a memfd, `O_TMPFILE`, an unlinked tmpfs file), which the
  model does not record of a `FileId.inode` mapping: at the pages of such files the environment says where, if at all,
  the walk stops (`Request.pick`; the page it names may lie inside one of the kernel's VMAs, since the model's areas need
  not match them, so the answers are a superset of the kernel's stops, every one of which is among them); the others
  are named, which may split them at the
  range's ends (`madvise_update_vma`; their pages get new areas, `Memory.renumber`) and may fail for a reason the model
  does not track (`Request.memFail`: the kernel's `EAGAIN` when a split finds no memory or meets `vm.max_map_count`);
  unmapped pages in the range give `ENOMEM` at the end, after the rest is done. A range over the vsyscall page is
  `ENOMEM` (outside the VMA tree); one over the vDSO is not modelled (`special_mapping_split` refuses a split).
The name itself shows only in `/proc/PID/maps` and `smaps`, whose contents the model takes from the environment, and
in which VMAs the kernel merges, which areas leave open (`Mapping.area`): the model keeps no name. The event records
the name's bytes as taken from the process.

Not modelled: every other option. -/
def sysPrctl (prof : Profile) (s : State) : Req StepResult := do
  if arg32 s.cpu.gpr.rdi ≠ PR_SET_VMA then Pure.pure (.stopped (.notModelled (.feature "prctl option"))) else
  if !prof.linux.anonVmaName || s.cpu.gpr.rsi.toNat ≠ PR_SET_VMA_ANON_NAME then
    Pure.pure (sysReturn s (errRet EINVAL) [] []) else
  let start := s.cpu.gpr.rdx.toNat
  let lenIn := s.cpu.gpr.r10.toNat
  let unnames := s.cpu.gpr.r8 = 0
  let (s, name) ← if unnames then Pure.pure (s, Except.ok []) else userStr prof s s.cpu.gpr.r8 anonNameMax
  match name with
  | .error e => Pure.pure (sysReturn s (errRet e) [] [])
  | .ok bs =>
  let ret (s' : State) (r : BitVec 64) : Req StepResult := Pure.pure (sysReturn s' r bs [])
  -- the name's copy (`strndup_user` allocates before the characters are checked; `anon_vma_name_alloc` after)
  match ← (if unnames then Pure.pure none else Req.request (.memFail 0)) with
  | some (e, _) => ret s (errRet e.val)
  | none =>
  if !bs.all anonNameChar then ret s (errRet EINVAL) else
  let mem := s.proc.mm.mem
  let len := pageUp lenIn % 2 ^ 64
  if start % 4096 ≠ 0 || (lenIn ≠ 0 && len = 0) || start + len ≥ 2 ^ 64 then ret s (errRet EINVAL)
  else if len = 0 then ret s 0
  else
  let first := start / 4096
  let n := len / 4096
  let gap : BitVec 64 := if (List.range n).any fun k => (mem.mapAt (first + k)).isNone then errRet ENOMEM else 0
  if (List.range n).any fun k => (mem.mapAt (first + k)).any (·.special) then
    if first = vsyscallPage.toNat then ret s (errRet ENOMEM)
    else Pure.pure (.stopped (.notModelled (.feature "prctl(PR_SET_VMA) of the vDSO")))
  else
  -- the pages before the first of a VMA of a file that is not anonymous shared memory are named: anonymous memory and
  -- shared anonymous memory (`FileId.shmem`) are; a file of the file systems (`FileId.inode`) is when it is a shmem file
  -- without links at its mapping (a memfd, `O_TMPFILE`, an unlinked tmpfs file), which the model does not record: the
  -- environment says at which such page, if any, the walk stops
  let ofInode (k : Nat) : Bool := (mem.mapAt (first + k)).any fun m => m.origin.any fun fp =>
    match fp.file with
    | .inode _ => true
    | .shmem _ => false
  let c ← if (List.range n).any ofInode then do
      let j ← Req.request (.pick n)
      Pure.pure (if j.val < n && ofInode j.val then j.val else n)
    else Pure.pure n
  let s' := s.withMem (mem.renumber first c)
  match ← Req.request (.memFail 0) with
  | some (e, _) => ret s' (errRet e.val)
  | none => ret s' (if c < n then errRet EBADF else gap)

end ZellicX86
