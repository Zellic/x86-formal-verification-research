import ZellicX86.Spec.Statement.Memory
/-!
# Statement vocabulary: Linux

The part of the statement vocabulary that is about Linux (`Spec/Statement.lean` imports it, and its contracts and
runs name these): the thread's state in the kernel, the process's state outside memory, the rules of its memory layout,
what other agents and the system are assumed to do, the system calls' events, and output and input as byte streams.

- The thread: one that uses no single-stepping, alignment checking, shadow stack or `CPUID` faulting (`Plain`), a
  registered `rseq` area into which the kernel only writes the ids (`RseqQuiet`, `rseqArea`, `rseqIds`), and its
  settings, which a function keeps but those it changes (`Setting`, `KeepsSettingsBut`: the thread's own state, its
  settings but those named and its pending signals but those it may leave pending).
- The process outside memory: its descriptor table, open file descriptions, signal actions and limits, kept but the
  file positions a function moves (`KeepsProc`).
- The memory layout: one a process can have (`LayoutOk`), what every function keeps of the address space and the files
  (`KeepsFixed`), and what a function keeps of the layout: all of it (`KeepsEnv`), all outside the pages it owns, for one
  that may map memory (`KeepsEnvOut`, `PageIn`), and all outside them but the protection of named pages, for one that
  may also re-protect those (`KeepsEnvProt`).
- The environment of a run: what other agents are assumed not to do (`Undisturbed`, over `EnvEvent.ordinary`), what the
  system is assumed to do (`ReadsWhole`: no read of a file fails part way; `WritesProgress`: no `write` takes none of its
  bytes; `OpensAs`: the file a path opens; `ProcSelfExe`: `/proc/self/exe` is procfs's link).
- System calls: that one failed (`Event.Failed`: it returned `-e` for an error number `e`), that the process was killed in
  a `write` (`Outcome.KilledInWrite`), and what an event of a `write`, a `read`, an `openat`, an `mmap` or a `munmap` is
  (`Event.IsWrite`, `Event.IsWriteFault` from a buffer the kernel cannot read to its end, `Event.IsWritev`, `Event.IsRead`, `Event.IsOpen`,
  `Event.IsMmap`, `Event.IsMunmap`), of the memory family an allocator uses (`Event.IsMemCall`), and of any call by its
  number and arguments (`Event.IsCall`).
- Output and input as byte streams: everything a run wrote to a descriptor (`Output`, the bytes each `write` or `writev` took,
  `Event.wrote`) or read from one (`Input`, the bytes each `read` delivered, `Event.got`), however the program cut them
  into calls; a `write` to a descriptor whose file no memory of the process holds a page of (`WriteUnmapped`), what a
  contract of a function that writes assumes; a descriptor on an input file (`InputAt`) and one on none of its pages
  (`OutAt`).
- Files: a file kept (`FileKept`: its size and its pages' bytes), and every file kept but those named descriptors are
  open on (`KeepsFilesBut`), what every function keeps of the files.
-/
namespace ZellicX86

/-! ## The thread -/


/-- The thread in `s` uses none of the features that make a run depend on more than its code
and memory: single-stepping (`RFLAGS.TF`, not modelled), alignment checking (`RFLAGS.AC`, not
modelled), a user shadow stack (`ThreadK.shstk`), with which every `CALL` and `RET` also pushes
and checks it (not modelled), and `CPUID` faulting (`ThreadK.cpuidFaults`), with which `CPUID` raises
`#GP` (`arch_prctl(ARCH_SET_CPUID)`). A thread `execve` starts has none of them
(`arch_setup_new_exec` turns `CPUID` faulting off). A registered `rseq` area is allowed; what a
statement needs of it is `RseqQuiet`. -/
def Plain (s : State) : Prop :=
  s.cpu.rflags.tf = false ∧ s.cpu.rflags.ac = false ∧ s.thread.shstk = none ∧
    s.thread.cpuidFaults = false

/-- The thread's registered restartable-sequences area (`rseq(2)`), if any: the 32 bytes of the
original `struct rseq` (`ORIG_RSEQ_SIZE`, `kernel/rseq.c`; the layout in `include/uapi/linux/rseq.h`),
which hold every field the kernel reads or writes. -/
def rseqArea (s : State) : List Rgn :=
  match s.thread.rseq with
  | none => []
  | some r => [⟨r.area, 32⟩]

/-- The bytes of the thread's `rseq` area that the kernel writes at every return to user mode
(`kernelEntry`): `cpu_id_start` and `cpu_id` (offsets 0–7), `node_id` and `mm_cid` (offsets 20–27).
`rseq_cs` and `flags` (offsets 8–19) are the thread's, which the kernel only reads. -/
def rseqIds (s : State) : List Rgn :=
  match s.thread.rseq with
  | none => []
  | some r => [⟨r.area, 8⟩, ⟨r.area.add 20, 8⟩]

/-- The thread in `s` has no `rseq` area, or one into which the kernel only writes the ids
(`rseqIds`) whenever it returns to user mode, an ordinary event of every run (`kernelEntry`): the
area does not reach past `2 ^ 64`, is writable, lies in no page the kernel owns or may drop
(`NotKernel`) and in no shared mapping (so the kernel's stores change no other address), and no
critical section is active (`rseq_cs`, the word at offset 8, is 0; with one, the kernel may move
`rip` to the section's abort handler, which is not modelled). glibc 2.43 registers such an area for
the main thread before `main` (`__tls_init_tp`, `sysdeps/nptl/dl-tls_init_tp.c`) and for every thread
it starts (`nptl/pthread_create.c`), with `rseq_cs` 0 (`sysdeps/unix/sysv/linux/rseq-internal.h`),
and enters no critical section itself; a program may (`manual/threads.texi`, "Restartable
Sequences"). -/
def RseqQuiet (feat : Features) (s : State) : Prop :=
  match s.thread.rseq with
  | none => True
  | some r =>
    let a : Rgn := ⟨r.area, 32⟩
    a.Fits ∧ Accessible feat s .write a ∧ NotKernel s [a] ∧ NotShared s [a] ∧ Word s (r.area.add 8) 0

/-- A setting of the thread that a function may change, by its contract (`Contract.sets`): each piece of the
thread's own state, in the kernel or in its registers, that a system call or an instruction of the thread changes
for the thread alone and that no calling convention covers.
- `rseq`: its restartable-sequences registration (`ThreadK.rseq`; `rseq(2)`, `kernel/rseq.c`), which glibc
  makes for the main thread before `main` (`__tls_init_tp`, `sysdeps/nptl/dl-tls_init_tp.c`);
- `fsBase`, `gsBase`: the `FS` and `GS` bases (`Segs.fsBase`, `Segs.gsBase`; `arch_prctl(ARCH_SET_FS)` and
  `ARCH_SET_GS`, `do_arch_prctl_64` in `arch/x86/kernel/process_64.c`, and `WRFSBASE`/`WRGSBASE`, SDM Vol. 2D,
  which Linux lets user code run, `X86_CR4_FSGSBASE`); glibc sets the `FS` base, the thread pointer, before
  `main` (`__libc_setup_tls`, `csu/libc-tls.c`);
- `pkru`: its protection-key rights (`Cpu.pkru`; `WRPKRU`, SDM Vol. 2D; `pkey_set` in glibc);
- `sigmask`: its blocked signals (`ThreadK.sigmask`; `rt_sigprocmask(2)`, `sigprocmask` in `kernel/signal.c`);
- `altStack`: its alternate signal stack (`ThreadK.altStack`; `sigaltstack(2)`, `do_sigaltstack` in
  `kernel/signal.c`);
- `clearChildTid`, `robustList`: the addresses the kernel uses when the thread exits (`ThreadK.clearChildTid`,
  `ThreadK.robustList`; `set_tid_address(2)`, `kernel/fork.c`; `set_robust_list(2)`, `kernel/futex/syscalls.c`),
  which glibc sets before `main` (`__tls_init_tp`);
- `tscFaults`: whether `RDTSC` faults for the thread (`ThreadK.tscFaults`; `prctl(PR_SET_TSC)`, `set_tsc_mode`
  in `arch/x86/kernel/process.c`); whether `CPUID` faults is not a setting but part of `Plain`, which every
  function keeps;
- `uid`: its real user id (`ThreadK.uid`; `setuid(2)` and its relatives, `kernel/sys.c`, which change the
  credentials of the calling thread). -/
inductive Setting where
  | rseq
  | fsBase
  | gsBase
  | pkru
  | sigmask
  | altStack
  | clearChildTid
  | robustList
  | tscFaults
  | uid
  deriving DecidableEq

/-- From `s₀` to `s`, the thread's own state is as it was but for the settings among `ss` and the pending entries
of the signals among `ps`: each setting (`Setting`) unless `ss` names it, the entries of signals pending for the
thread but those of the signals `ps` (`SigPending.drop`: the same entries in the same order once those are left out),
and in any case the thread's id and a thread that is still `Plain` (no single-stepping, no alignment checking, no
shadow stack, no `CPUID` faulting). With `ss = []` and `ps = []`, for a thread that is `Plain` at `s₀` too, that is
every part of the thread's state in the kernel (`ThreadK`) and its `PKRU` and `FS` and `GS` bases; the shadow stack
and `CPUID` faulting are stated only through `Plain s`. A function's contract names the settings it may change
(`Contract.sets`), and the signals it may leave pending or take (`Contract.pends`); the new values are its
postcondition's business. Signals left pending are not a setting: a `write` to a broken pipe sends `SIGPIPE`, which
stays pending where the thread blocks it (`writeFile`), and `tgkill(2)` of a blocked signal to itself does the same.
That a signal the thread does not block is not pending where its code runs (the kernel takes it on every return to
user mode, `deliverSignals`) holds of the states a run from `execve` reaches but is not part of this frame: a
contract's entry state need not satisfy it. The registers are the calling convention's business (`Conv`).
The segment selectors are named by neither this frame nor `sysv`: the model changes them only at a signal's
delivery and at `rt_sigreturn` (`CS`, `SS`), and no modelled instruction writes one (`MOV Sreg`, `POP Sreg` are not
modelled). -/
structure KeepsSettingsBut (ss : List Setting) (ps : List Signal) (s₀ s : State) : Prop where
  /-- The thread's protection-key rights (`PKRU`), unless `ss` names it. -/
  pkru : Setting.pkru ∉ ss → s.cpu.pkru = s₀.cpu.pkru
  /-- The thread's `rseq` registration, unless `ss` names it. -/
  rseq : Setting.rseq ∉ ss → s.thread.rseq = s₀.thread.rseq
  /-- The `FS` base, unless `ss` names it. The psABI makes it callee-saved: its register usage table
  (figure "Register Usage", `fig-reg-usage`, `low-level-sys-info.tex`) lists `%fs` as "thread pointer",
  and its TLS model reads thread data at `%fs:` offsets (`object-files.tex`, "Thread-Local Storage"), which
  in 64-bit mode address from the base. The selector is not stated: user code does not load it, and
  Linux keeps it 0 next to a base set by `arch_prctl(ARCH_SET_FS)`. -/
  fsBase : Setting.fsBase ∉ ss → s.cpu.seg.fsBase = s₀.cpu.seg.fsBase
  /-- The `GS` base, unless `ss` names it (the selector, as for `FS`, not stated). -/
  gsBase : Setting.gsBase ∉ ss → s.cpu.seg.gsBase = s₀.cpu.seg.gsBase
  /-- The thread's blocked signals, unless `ss` names it. -/
  sigmask : Setting.sigmask ∉ ss → s.thread.sigmask = s₀.thread.sigmask
  /-- The thread's alternate signal stack, unless `ss` names it. -/
  altStack : Setting.altStack ∉ ss → s.thread.altStack = s₀.thread.altStack
  /-- The address the kernel clears when the thread exits (`set_tid_address`), unless `ss` names it. -/
  clearChildTid : Setting.clearChildTid ∉ ss → s.thread.clearChildTid = s₀.thread.clearChildTid
  /-- The thread's robust futex list (`set_robust_list`), unless `ss` names it. -/
  robustList : Setting.robustList ∉ ss → s.thread.robustList = s₀.thread.robustList
  /-- Whether `RDTSC` faults for the thread, unless `ss` names it. -/
  tscFaults : Setting.tscFaults ∉ ss → s.thread.tscFaults = s₀.thread.tscFaults
  /-- The thread's real user id, unless `ss` names it. -/
  uid : Setting.uid ∉ ss → s.thread.uid = s₀.thread.uid
  /-- The thread's id. -/
  tid : s.thread.tid = s₀.thread.tid
  /-- The signals pending for the thread but the entries of the signals `ps` (those pending for the process are
  `KeepsProc`'s). -/
  pending : s.thread.pending.drop ps = s₀.thread.pending.drop ps
  /-- The thread is still `Plain`. -/
  plain : Plain s

/-! ## The process outside memory -/

/-- From `s₀` to `s`, the process's state outside its memory is as it was, but for the positions of the
open file descriptions on the descriptors `moved` (which `read`, `write` and `lseek` on them move): the same
descriptor table, close-on-exec flags included (`Proc.files`, `struct files_struct`); the position
(`FilePos`, `f_pos` of `struct file`) of every other open file description, and every one's status flags
(`O_APPEND` and the others, `f_flags`, which `fcntl(F_SETFL)` changes); the same identity for the next description the process creates (`OpenTable.next`);
the same signal actions (`Proc.sighand`, `struct sighand_struct`); and the same signals pending for the
process and resource limits (`Proc.signal`, `struct signal_struct`). The descriptors are those of `s₀`'s
table, which is `s`'s. A function's contract names the descriptors it moves (`Contract.moves`); where it
leaves their positions is its postcondition's business. What it does to the memory layout and the program
break is its layout rule's (`KeepsLayout`).

Other agents may change some of this between two instructions: another process sharing an open file
description moves its position (`EnvEvent.filePos`), anybody may send the process a signal (`EnvEvent.signal`,
which may stay pending) or change its limits (`EnvEvent.rlimit`). A contract promises `KeepsProc` on the runs of
its environment (`Contract.env`), so it can be kept only by a contract whose environment excludes those events
(`Undisturbed`, the default, excludes all three); that is the environment's assumption, not the function's
doing. -/
structure KeepsProc (moved : List Nat) (s₀ s : State) : Prop where
  /-- The descriptor table. -/
  files : s.proc.files = s₀.proc.files
  /-- The position of every open file description on none of the descriptors `moved`. -/
  pos : ∀ f, (∀ d ∈ moved, s₀.proc.files.desc d ≠ some f) → s.proc.opens.pos f = s₀.proc.opens.pos f
  /-- Whether each open file description's writes append. -/
  append : ∀ f, (s.proc.opens.pos f).append = (s₀.proc.opens.pos f).append
  /-- Each open file description's other status flags (`FilePos.flags`, which `fcntl(F_SETFL)` changes). -/
  flags : ∀ f, (s.proc.opens.pos f).flags = (s₀.proc.opens.pos f).flags
  /-- The identity of the next open file description. -/
  next : s.proc.opens.next = s₀.proc.opens.next
  /-- The signal actions. -/
  sighand : s.proc.sighand = s₀.proc.sighand
  /-- The signals pending for the process, and the resource limits. -/
  signal : s.proc.signal = s₀.proc.signal

/-! ## The memory layout -/

/-- The layout of `s` is one a process on a processor with features `feat` can have, in six respects the model's types
do not enforce:
the initial stack's first page as `execve` mapped it (`Memory.growsDown`) is mapped, no page maps a backing
from `Memory.fresh` on, the lowest break `brk` accepts (`Mm.brkMin`) is above 0, the program break is at or
above it, every mapped page's maximum protection allows reading, and every mapped page lies below the end of the user
address space (`taskSize feat`), but the vsyscall page. Every state of a process has all six: `execve` maps the stack, starts `fresh` past every backing it
maps and sets the lowest break above 0 and at or below the break (`Linux/Exec.lean`, `brkMin`: `mm->start_brk`, or
the end of the data segment, which is at or below it; `fs/binfmt_elf.c` `load_elf_binary` sets
`mm->start_brk = mm->brk`), nothing else changes the lowest break, `brk` never moves the break below it (`sysBrk`;
`mm/mmap.c` `brk` refuses a request below `min_brk`), every change of the layout takes new backings from `fresh` and
moves it past them (a growth of the
stack too, which maps pages below that first page and leaves it mapped, `growStack`), and a system call
that would unmap or replace that first page ends the run as not modelled (`Memory.touchesFixed`; a change
of the stack's other pages leaves it mapped). A
function that maps memory at a place the kernel picks (`mmap` without `MAP_FIXED`) relies on the first
two: such a page is none of the free pages the kernel may pick (`sysMmap`), and the new mapping's backings are no page's; one that asks for the break with `brk(0)` on
the third: below the lowest break, `brk` returns the break and changes nothing (`sysBrk`); one that moves the break
by an amount (`sbrk`) on the fourth: the break it moves to is at or above the lowest, so `brk` does not refuse it.
The fourth holds because the model has no system call that sets the break's bounds directly: `prctl(PR_SET_MM)`
(`kernel/sys.c`, `prctl_set_mm`, `CAP_SYS_RESOURCE`), which checks `start_brk ≤ brk` but not the end of the data
segment against the break, so that under `CONFIG_COMPAT_BRK` with the break not randomized `PR_SET_MM_END_DATA` or
`PR_SET_MM_MAP` can put the lowest break above it, is not modelled.
The fifth: every mapped page's maximum protection (`Mapping.maxProt`, the kernel's `VM_MAY*` flags) allows reading.
`execve` maps every page so (its segments, the stack, the vDSO); Linux v6.18
`mm/mmap.c`, `do_mmap`, sets `VM_MAYREAD` unconditionally (the check for a file opened for reading refuses the
mapping, rather than setting the flag). `mprotect`, `mremap` and the stack's growth keep a page's maximum; a function
that makes pages read-only (`mprotect(…, PROT_READ)`, glibc's RELRO pages) relies on it: `mprotect` refuses a
protection beyond a page's maximum (`EACCES`). A device mapping whose driver clears `VM_MAYREAD` (xe, ocxl, hfi1) is
not modelled: `sysMmap` stops "not modelled" for a device or special file (`FileMap.other`).
The sixth: Linux maps no user page at or above `TASK_SIZE` (`taskSize`: `TASK_SIZE_MAX`, 2^47 − 4096, with 5-level
paging 2^56 − 4096). `execve` maps the stack below `STACK_TOP` and the vDSO below it, and kills a program whose
segment would end above `TASK_SIZE` (`segmentRegions`; `fs/binfmt_elf.c` `load_elf_binary`); `mmap` and `mremap` place
or accept a range only below it (`mm/mmap.c` `__get_unmapped_area`, `do_mmap`; `mm/mremap.c`), `brk` grows only below
it (`mm/mmap.c` `brk`, `check_brk_limits`), the stack's growth looks for the stack only below it (`find_vma`, `growStack`),
and `mprotect` and `munmap` map nothing new. The page of the legacy vsyscall area (`vsyscallPage`, `0xffffffffff600000`)
is above it: in `vsyscall=emulate` mode the model maps it, as a special mapping, and the kernel serves it from its
gate area (`arch/x86/entry/vsyscall/vsyscall_64.c`), not a VMA of the process. A function that maps memory relies on
it where a range's end must be within the user address space (a zero-length range at a mapping's end, `access_ok`). -/
def LayoutOk (feat : Features) (s : State) : Prop :=
  (∀ g ∈ s.proc.mm.mem.growsDown, s.proc.mm.mem.map g ≠ none) ∧
  (∀ p m, s.proc.mm.mem.map p = some m → m.backing < s.proc.mm.mem.fresh) ∧
  0 < s.proc.mm.brkMin.toNat ∧ s.proc.mm.brkMin.toNat ≤ s.proc.mm.brk.toNat ∧
  (∀ p m, s.proc.mm.mem.map p = some m → m.maxProt.read = true) ∧
  (∀ p m, s.proc.mm.mem.map p = some m →
    (p.toNat + 1) * 4096 ≤ taskSize feat ∨ (p = vsyscallPage ∧ m.special = true))

/-- From `s₀` to `s`, what of the address space and the files every function keeps, whether or not it
may change the memory layout (`KeepsEnv`, `KeepsEnvOut`), is as it was. -/
structure KeepsFixed (s₀ s : State) : Prop where
  /-- Every file that some backing of `s` holds a page of (a shared or a private file mapping not yet
  copied; whether a page still maps that backing or not) has the size it had: the function truncates or
  extends no such file. -/
  fileSizes : ∀ j fp, (s.proc.mm.mem.backings j).filePage = some fp →
    s.proc.mm.mem.files.size fp.file = s₀.proc.mm.mem.files.size fp.file
  /-- The same files are write-denied (mapped executables, `MAP_DENYWRITE`). -/
  denyWrite : s.proc.mm.mem.files.denyWrite = s₀.proc.mm.mem.files.denyWrite
  /-- The same mappings grow down (the initial stack, `Memory.growsDown`). -/
  growsDown : s.proc.mm.mem.growsDown = s₀.proc.mm.mem.growsDown
  /-- The lowest break `brk` accepts (`Mm.brkMin`). -/
  brkMin : s.proc.mm.brkMin = s₀.proc.mm.brkMin

/-- From `s₀` to `s`, the memory layout a caller relies on is as it was: the same page map, every
backing refined as by stores (`Backing.Refines`), the same place for the backings of new mappings
(`Memory.fresh`), the program break, and what every function keeps of the address space and the files
(`KeepsFixed`: the sizes of the files the backings hold pages of, the write-denied files, the mappings that
grow down, and the lowest break `brk` accepts). A function that maps or unmaps memory or moves the break
(also within its last page, which `brk` does without changing a mapping) does not keep it; one that
writes to a file it does not map may. -/
def KeepsEnv (s₀ s : State) : Prop :=
  s.proc.mm.mem.map = s₀.proc.mm.mem.map ∧
  (∀ j, (s.proc.mm.mem.backings j).Refines s₀.proc.mm.mem.files (s₀.proc.mm.mem.backings j)) ∧
  s.proc.mm.mem.fresh = s₀.proc.mm.mem.fresh ∧ s.proc.mm.brk = s₀.proc.mm.brk ∧ KeepsFixed s₀ s

/-- Every byte of the virtual page `p` lies in one of the regions `rs`. -/
def PageIn (rs : List Rgn) (p : PageNum) : Prop := ∀ a, pageOf a = p → Foot rs a

/-- From `s₀` to `s`, the memory layout changed only in the pages wholly in the regions `own` and in
pages no mapping held in `s₀`, and the rest of what `KeepsEnv` keeps is as it was: what a function
that may map, unmap or change memory it owns (an allocator's `brk`, `mmap`, `munmap`, `mprotect`)
keeps.
- Every page mapped in `s₀` with a byte outside `own` keeps its mapping, and its backing is refined
  as by stores (`Backing.Refines`).
- Every page that maps a backing it did not map in `s₀` (mapped since, or wholly in `own` and remapped)
  maps one that holds no file page and that no page with a byte outside `own` maps in `s₀`: new mappings
  are anonymous memory and alias none of the memory the function does not own. A page wholly in `own`
  that still maps the backing it mapped in `s₀` is not bound by this, whatever else of its mapping changed
  (its protection and key, `mprotect` and `pkey_mprotect`; its area, which they renumber; and as far as this
  clause goes its maximum protection, origin, `special` and `growsDown`): it may still map a private file page
  not yet copied (glibc's `mprotect` of its RELRO pages after relocation, the first of which no store has
  copied yet).
- Every backing that holds a file page (a shared or a private file mapping not yet copied) is as in
  `s₀`: the function maps no file.
- New backings start no lower (`Memory.fresh`), and the layout is one a process on a processor with features `feat` can have if it was
  (`LayoutOk`).
- What every function keeps of the address space and the files is as in `s₀` (`KeepsFixed`).
With `own = []` it still allows new mappings of pages unmapped in `s₀`; `KeepsEnv` allows none. The
program break may move (a contract says whether, `Layout.owns`). -/
def KeepsEnvOut (feat : Features) (own : List Rgn) (s₀ s : State) : Prop :=
  (∀ p m, s₀.proc.mm.mem.map p = some m → ¬ PageIn own p →
    s.proc.mm.mem.map p = some m ∧
    (s.proc.mm.mem.backings m.backing).Refines s₀.proc.mm.mem.files (s₀.proc.mm.mem.backings m.backing)) ∧
  (∀ p m, s.proc.mm.mem.map p = some m → (∀ m₀, s₀.proc.mm.mem.map p = some m₀ → m₀.backing ≠ m.backing) →
    (s.proc.mm.mem.backings m.backing).filePage = none ∧
    ∀ q n, s₀.proc.mm.mem.map q = some n → ¬ PageIn own q → n.backing ≠ m.backing) ∧
  (∀ j, (s.proc.mm.mem.backings j).filePage ≠ none → s.proc.mm.mem.backings j = s₀.proc.mm.mem.backings j) ∧
  s₀.proc.mm.mem.fresh ≤ s.proc.mm.mem.fresh ∧ (LayoutOk feat s₀ → LayoutOk feat s) ∧ KeepsFixed s₀ s

/-- From `s₀` to `s`, the memory layout changed only in the pages wholly in the regions `own`, in the protection of the
pages wholly in the regions `prot` and in pages no mapping held in `s₀`, and the rest of what `KeepsEnv` keeps is as it
was: what a function keeps that may change memory it owns, as `KeepsEnvOut own` allows, and besides re-protect memory
it does not own (a C library's startup, which may change the library's own memory as each of its later calls may, and
makes its RELRO segment read-only after relocating it: `mprotect` in `_dl_protect_relro`, glibc 2.43's
`elf/dl-reloc.c`, called from `elf/dl-support.c` in a static program).
- Every page mapped in `s₀` that is wholly in `prot` or has a byte outside `own` (a page wholly in `prot` is
  re-protected only, also where it lies in `own`) keeps its backing, refined as by stores (`Backing.Refines`), and its
  mapping: such a page wholly in `prot` may change its protection, its protection key and its area (which `mprotect`
  and `pkey_mprotect` renumber), nothing else; every other keeps its mapping as it was. (`mprotect` changes whole
  pages: glibc's covers its RELRO segment's from the page of its start to the page of its end, both rounded down, so
  `prot` names those pages, not the segment's bytes.)
- Every page that maps a backing it did not map in `s₀` (mapped since, or wholly in `own` and remapped) maps one that
  holds no file page and that no page kept as above maps in `s₀`: new mappings are anonymous memory and alias none of
  the memory the function does not own (as for `KeepsEnvOut`).
- Every backing that holds a file page is as in `s₀`: the function maps no file.
- New backings start no lower (`Memory.fresh`), and the layout is one a process on a processor with features `feat` can have if it was (`LayoutOk`).
- What every function keeps of the address space and the files is as in `s₀` (`KeepsFixed`).
With `prot = []` it is `KeepsEnvOut own`'s frame; with `own = []` it re-protects only. The program break may move (a
contract says whether, `Layout.protects`). -/
def KeepsEnvProt (feat : Features) (own prot : List Rgn) (s₀ s : State) : Prop :=
  (∀ p m, s₀.proc.mm.mem.map p = some m → (PageIn own p → PageIn prot p) → ∃ m', s.proc.mm.mem.map p = some m' ∧
    m' = { m with prot := m'.prot, pkey := m'.pkey, area := m'.area } ∧ (¬ PageIn prot p → m' = m) ∧
    (s.proc.mm.mem.backings m.backing).Refines s₀.proc.mm.mem.files (s₀.proc.mm.mem.backings m.backing)) ∧
  (∀ p m, s.proc.mm.mem.map p = some m → (∀ m₀, s₀.proc.mm.mem.map p = some m₀ → m₀.backing ≠ m.backing) →
    (s.proc.mm.mem.backings m.backing).filePage = none ∧
    ∀ q n, s₀.proc.mm.mem.map q = some n → (PageIn own q → PageIn prot q) → n.backing ≠ m.backing) ∧
  (∀ j, (s.proc.mm.mem.backings j).filePage ≠ none → s.proc.mm.mem.backings j = s₀.proc.mm.mem.backings j) ∧
  s₀.proc.mm.mem.fresh ≤ s.proc.mm.mem.fresh ∧ (LayoutOk feat s₀ → LayoutOk feat s) ∧ KeepsFixed s₀ s

/-! ## The environment of a run -/

/-- Whether an environment event is the kernel going about its own business: entering the
kernel and returning (interrupts, preemption, migration), updating a page it owns, or dropping a
lazily freed page. -/
def EnvEvent.ordinary : EnvEvent → Bool
  | .kernelEntry .. | .kernelData .. | .reclaim _ => true
  | .signal _ | .fileWrite .. | .fileSize .. | .filePos .. | .cowBreak _ | .remoteWrite .. | .remoteRead ..
  | .tracer _
  | .rlimit .. => false

/-- Between instructions only ordinary events happen: nobody sends the process a signal,
changes a file or its size, moves the position of an open file it shares, pins its pages for writing,
writes its memory or registers from outside, or changes its resource limits. The signals the kernel sends when the process's CPU time reaches its
limit (`SIGXCPU`, then `SIGKILL`; `RLIMIT_CPU`) are such signals, since the model has no time: a run
that is `Undisturbed` does not reach that limit. -/
def Undisturbed (o : Oracle) : Prop :=
  ∀ t cpus (e : EnvEvent), List.Mem e (o t (.between cpus)).val → e.ordinary = true

/-- No `read` of a file with pages fails (`Request.readFail`): none runs out of memory for the page
cache, meets an error of the storage, or is refused by the security module, so each delivers every
byte asked for up to the file's end. An assumption about the system, as `Undisturbed` is about other
agents: a statement makes it by running over `fun o => Undisturbed o ∧ ReadsWhole o`. -/
def ReadsWhole (o : Oracle) : Prop :=
  ∀ t file n, o t (.readFail file n) = none

/-- No `write` of at least one byte takes none without failing (`Request.write`, `Request.writeFault`: the answer
`WriteResult.wrote 0` only for no bytes). Linux's pipes wait for room and its terminals and regular files take a byte
or fail, but the model lets a file answer any count up to the bytes offered. Code that writes until all is taken
(glibc 2.43's `_IO_new_file_write`, `libio/fileops.c`, which `exit`'s flush of stdio's buffers runs) would loop forever
on such an answer; a statement that it ends makes this assumption, as `ReadsWhole`, by running over
`fun o => Undisturbed o ∧ WritesProgress o`. -/
def WritesProgress (o : Oracle) : Prop :=
  (∀ t file bs h, o t (.write file bs) = WriteResult.wrote 0 h → bs = []) ∧
    ∀ t file bs n h, o t (.writeFault file bs n) = WriteResult.wrote 0 h → n = 0

/-- Opening the path `p` (the bytes of its name, without the NUL) from the working directory, or from
anywhere if `p` is absolute (`Request.openAt none p flags`), opens the pages of file `file` whenever it
opens anything: the file system resolves `p` to `file` all through the run (nobody renames, replaces or
removes it), with any flags. The open may still fail (`OpenResult.error`: permissions, limits, lack of
memory, …). An assumption about the system, as `ReadsWhole` is: a statement about a program that opens
its input by name makes it by running over `fun o => Undisturbed o ∧ OpensAs o p file`, and names the
file's bytes by `FileBytes`. The model has no working directory: a relative `p` means `p` from wherever
the process runs. -/
def OpensAs (o : Oracle) (p : List Byte) (file : FileId) : Prop :=
  ∀ t flags m, o t (.openAt none p flags) = .opened m → m = .pages file

/-- The path `/proc/self/exe` is procfs's `exe` link of the process, or `readlink` of it fails: whatever the file
system answers to a `readlink` of it (`Request.readlink`, from any directory) is that link (`LinkResult.procExe`, whose
contents the kernel writes: the path of the process's executable, which starts with `/`, `ExePath.bytes`) or an error,
never another symbolic link. True where procfs is mounted at `/proc`, as Linux systems mount it (`proc(5)`), or nothing
is (`ENOENT`); a file system mounted there instead may hold any link at that path. An assumption about the system, as
`OpensAs` is: a statement about a program whose C library reads its executable's path there (glibc 2.43's static
startup, `_dl_get_origin` in `sysdeps/unix/sysv/linux/dl-origin.c`, which asserts that a non-empty answer starts with
`/` or `[`) assumes it (`fun o => Undisturbed o ∧ ProcSelfExe o`). -/
def ProcSelfExe (o : Oracle) : Prop :=
  ∀ t d bs, o t (.readlink d ("/proc/self/exe".toUTF8.toList.map UInt8.toBitVec)) ≠ .target bs

/-! ## System calls and their events -/

/-- The call `ev` failed: it returned an error, `-e` for an error number `e` from 1 to 4095. That is how
system calls report an error (`include/linux/err.h`: `MAX_ERRNO`, `IS_ERR_VALUE`), and what the C
library's wrappers test before they set `errno`. A call that succeeds mostly returns a count, a
descriptor, a file offset below `2 ^ 63` or a user address below `TASK_SIZE`, outside that range. Not
every call follows the convention, so a statement about one of these says what its result means
itself: `brk` reports a failure by returning the unchanged break (`sysBrk`), `rt_sigreturn` returns the
interrupted context's `rax`, whatever it is (`sysRtSigreturn`), and `getpid`/`gettid` return the thread
id, which the model does not bound (`sysGetpid`; Linux keeps ids below `PID_MAX_LIMIT`, `2 ^ 22`). -/
def Event.Failed (ev : Event) : Prop := ∃ e, 0 < e ∧ e < 4096 ∧ ev.ret = errRet e

/-- The process ended as the model describes it: it exited or was killed, not an end at which the model stops because
it does not model what the run met (`Outcome.notModelled`), where the real process goes on. -/
def Outcome.Modelled (out : Outcome) : Prop := ∀ w, out ≠ .notModelled w

/-- The process was killed, by the kernel, with the signal it sends in a `write` it does not complete
(`sysWrite`): `SIGPIPE`, to a pipe without readers, or `SIGXFSZ`, to a file at the file size limit
(`RLIMIT_FSIZE`). -/
def Outcome.KilledInWrite (out : Outcome) : Prop :=
  out = .killed Signal.SIGPIPE .kernel ∨ out = .killed Signal.SIGXFSZ .kernel

/-- `ev` is a `write(fd, buf, n)` system call (number 1, `sysWrite`) whose buffer the kernel can read
as the bytes `bs`, up to `n` of them: all `n` (`Event.IsWrite`), or, from a buffer with a byte the kernel
cannot read, the first bytes before it (fewer than `n`). The call number is `rax`'s low 32 bits and the
argument registers `rdi rsi rdx` held `fd` (in their low 32 bits, as the kernel reads the number and the
descriptor: `syscall`, `sysWrite`), `buf` and `n`, the kernel wrote nothing into the process's memory, and either the call returned a count
`k` of at most `n`, not an error, and took the first `k` bytes of `bs` (a file that does not read the
buffer, `/dev/null`, may return more than `bs.length`), or it failed (`Event.Failed`; `EFAULT` when nothing
was taken) and took none. -/
def Event.IsWriteFault (ev : Event) (fd : Nat) (buf : Addr) (n : Nat) (bs : List Byte) : Prop :=
  arg32 ev.nr = 1 ∧ (∃ d, ev.args.take 3 = [d, buf, BitVec.ofNat 64 n] ∧ arg32 d = fd) ∧
    ev.toProc = [] ∧
    ((¬ ev.Failed ∧ ev.ret.toNat ≤ n ∧ ev.fromProc = bs.take ev.ret.toNat) ∨
      (ev.Failed ∧ ev.fromProc = []))

/-- `ev` is a `write(fd, buf, bs.length)` system call (number 1, `sysWrite`) of the bytes `bs`
from `buf`: `Event.IsWriteFault` with all `bs.length` bytes readable. The argument registers `rdi rsi rdx`
held `fd` (in their low 32 bits, as for `Event.IsWriteFault`), `buf` and the length, the kernel wrote nothing into the process's memory, and either the call
returned a count `k` of at most `bs.length`, not an error, and took the first `k` bytes of `bs`, or it failed
(`Event.Failed`) and took none. -/
def Event.IsWrite (ev : Event) (fd : Nat) (buf : Addr) (bs : List Byte) : Prop :=
  ev.IsWriteFault fd buf bs.length bs

/-- `ev` is a `writev(fd, iov, count)` system call (number 20 in `rax`'s low 32 bits, `sysWritev`; Linux v6.18
`fs/read_write.c` `do_writev`) whose buffers hold `n` bytes in all, of which the kernel can read the first ones as `bs`:
the argument registers `rdi rsi rdx` held `fd`, `iov` and `count` (`fd` and `count` in their low 32 bits, as the kernel
reads them: `fdget_pos`, `import_iovec`), the kernel wrote nothing into the process's memory, and either the call
returned a count `k` of at most `n` and `maxRwCount`, not an error, and took the first `k` bytes of `bs` (a file that
does not read the buffers, `/dev/null`, may return more than `bs.length`), or it failed (`Event.Failed`) and took none.
The bytes taken (`ev.fromProc`) are the buffers' bytes, not the vector array's. That `iov` holds particular vectors and
that `bs` are the bytes at their addresses is not said here: a statement says it of the state. -/
def Event.IsWritev (ev : Event) (fd : Nat) (iov : Addr) (count n : Nat) (bs : List Byte) : Prop :=
  arg32 ev.nr = 20 ∧ (∃ d c, ev.args.take 3 = [d, iov, c] ∧ arg32 d = fd ∧ arg32 c = count) ∧
    ev.toProc = [] ∧ ((¬ ev.Failed ∧ ev.ret.toNat ≤ min n maxRwCount ∧ ev.fromProc = bs.take ev.ret.toNat) ∨
      (ev.Failed ∧ ev.fromProc = []))

/-- `ev` is a `read(fd, buf, n)` system call (number 0 in `rax`'s low 32 bits, `sysRead`): the argument
registers `rdi rsi rdx` held `fd` (in their low 32 bits, as the kernel reads it), `buf` and `n`, the kernel took nothing from the process's memory, and
either the call returned the number of bytes it delivered into the process (`ev.toProc`, at most
`n`; none at the end of the file), or it failed (`Event.Failed`) and delivered none. Where the bytes went is the state's business, not the event's: `sysRead` writes
them at `buf`. -/
def Event.IsRead (ev : Event) (fd : Nat) (buf : Addr) (n : Nat) : Prop :=
  arg32 ev.nr = 0 ∧ (∃ d, ev.args.take 3 = [d, buf, BitVec.ofNat 64 n] ∧ arg32 d = fd) ∧
    ev.fromProc = [] ∧
    ((ev.toProc.length ≤ n ∧ ev.ret = BitVec.ofNat 64 ev.toProc.length) ∨
      (ev.Failed ∧ ev.toProc = []))

/-- `ev` is an `openat(AT_FDCWD, p, flags)` system call (number 257 in `rax`'s low 32 bits, `sysOpenat`) of
the path `p` (its
bytes without the NUL): the argument registers `rdi rdx` held `AT_FDCWD` and `flags` as the kernel reads
them (their low 32 bits), the kernel took the path's bytes from the process's memory and delivered
nothing into it, and the call returned a descriptor (below `2 ^ 31`) or failed (`Event.Failed`). Which file the descriptor is open on is the state's business, not the event's. -/
def Event.IsOpen (ev : Event) (p : List Byte) (flags : Nat) : Prop :=
  arg32 ev.nr = 257 ∧ (∃ d a r, ev.args.take 3 = [d, a, r] ∧ argInt d = AT_FDCWD ∧ arg32 r = flags) ∧
    ev.fromProc = p ∧ ev.toProc = [] ∧
    (ev.ret.toNat < 2 ^ 31 ∨ ev.Failed)

/-- `ev` is an `mmap(addr, len, prot, flags, fd, off)` system call (number 9 in `rax`'s low 32 bits,
`sysMmap`): the argument registers `rdi rsi rdx r10 r8 r9` held the arguments, `fd` in the low 32 bits
of `r8` as the kernel reads it, and the kernel took nothing from the
process's memory and delivered nothing into it. Its result is not constrained: the address of the
new mapping, or an error (`Event.Failed`), as a statement says; what the call mapped is the state's
business, not the event's. -/
def Event.IsMmap (ev : Event) (addr len prot flags fd off : BitVec 64) : Prop :=
  arg32 ev.nr = 9 ∧ (∃ d, ev.args = [addr, len, prot, flags, d, off] ∧ arg32 d = arg32 fd) ∧
    ev.fromProc = [] ∧ ev.toProc = []

/-- `ev` is system call `nr` (`syscall` with `nr` in `rax`'s low 32 bits, as the kernel reads it) whose
first argument registers held `args`, in the order `rdi rsi rdx r10 r8 r9`. What the call took from the process's memory
(`ev.fromProc`), delivered into it (`ev.toProc`) and returned (`ev.ret`) is the statement's
business. -/
def Event.IsCall (ev : Event) (nr : Nat) (args : List (BitVec 64)) : Prop :=
  arg32 ev.nr = nr ∧ ev.args.take args.length = args

/-- `ev` is a `munmap(addr, len)` system call (number 11 in `rax`'s low 32 bits, `sysMunmap`): the argument registers
`rdi rsi` held `addr` and `len`, and the kernel took nothing from the process's memory and delivered
nothing into it. -/
def Event.IsMunmap (ev : Event) (addr len : BitVec 64) : Prop :=
  arg32 ev.nr = 11 ∧ ev.args.take 2 = [addr, len] ∧ ev.fromProc = [] ∧ ev.toProc = []

/-- `ev` is a system call of the memory family an allocator makes to get or give back memory:
`brk` (number 12, `sysBrk`), a private anonymous `mmap` (number 9, `sysMmap`, with `MAP_ANONYMOUS`
and the type `MAP_PRIVATE` in its flags, `r10`), `munmap` (11, `sysMunmap`) or `mprotect` (10,
`sysMprotect`), with any arguments (the number in `rax`'s low 32 bits, as the kernel reads it), and the kernel took nothing from the process's memory and
delivered nothing into it. What the call did to the layout is the state's business, not the
event's. -/
def Event.IsMemCall (ev : Event) : Prop :=
  ev.fromProc = [] ∧ ev.toProc = [] ∧
  (arg32 ev.nr = 12 ∨ arg32 ev.nr = 11 ∨ arg32 ev.nr = 10 ∨
    arg32 ev.nr = 9 ∧ ∃ addr len prot flags fd off, ev.args = [addr, len, prot, flags, fd, off] ∧
      flags.toNat / 32 % 2 = 1 ∧ flags.toNat % 16 = 2)

/-! ## Output and input as byte streams -/

/-- The bytes the event `ev` wrote to descriptor `fd`: the data bytes a `write` or `writev` to `fd` took from the process
(`ev.fromProc`, none when it failed), and none for any other event. The call and the descriptor are read
as the kernel reads them (`syscall`, `sysWrite`): the call number is the low 32 bits of `rax`, the
descriptor the low 32 bits of `rdi`. `write` and `writev` add to a stream (`fs/read_write.c`, `ksys_write`, `do_writev`): `pwrite64`
writes at an offset it is given and is not in the stream, by design; `sendfile` and the like are not modelled, so a run
that makes one ends as not modelled. -/
def Event.wrote (fd : Nat) (ev : Event) : List Byte :=
  if (arg32 ev.nr = 1 ∨ arg32 ev.nr = 20) ∧ ev.args.head?.map arg32 = some fd then ev.fromProc else []

/-- The bytes the event `ev` read from descriptor `fd`: the bytes a `read` of `fd` delivered into the
process (`ev.toProc`, none at the end of the file or when it failed), and none for any other event. The
call and the descriptor are read as the kernel reads them (`syscall`, `sysRead`), as for `Event.wrote`;
`pread64` (modelled, `sysPread64`) reads at an offset it is given and is not in the stream, by design; `readv` and the
like are not modelled. -/
def Event.got (fd : Nat) (ev : Event) : List Byte :=
  if arg32 ev.nr = 0 ∧ ev.args.head?.map arg32 = some fd then ev.toProc else []

/-- Everything the events `evs` wrote to descriptor number `fd`, in order: the bytes each `write` or `writev` to
`fd` took, one after the other, however the program cut them into calls. By number, as the program's
code names the descriptor: a statement for which `fd` must mean the file open there at the start (standard
output, say) also says that the program does not `close` or `dup2` it, which a statement that says which
calls the program makes says anyway. `write` and `writev` add bytes to the stream: the same file reached through
another number (an `openat` of `/dev/stdout`) or through a shared mapping of it is not in it. Since the
kernel reads the descriptor's low 32 bits, `Output fd evs` is `[]` for `fd ≥ 2 ^ 32`. -/
def Output (fd : Nat) (evs : List Event) : List Byte := evs.flatMap (Event.wrote fd)

/-- Everything the events `evs` read from descriptor number `fd`, in order: the bytes each `read` of `fd`
delivered, one after the other. By number, as `Output`. -/
def Input (fd : Nat) (evs : List Event) : List Byte := evs.flatMap (Event.got fd)

/-- A `write` or `writev` to descriptor `fd` in state `s` puts none of its bytes into memory the process maps: the open file
description on the descriptor (the kernel reads its low 32 bits, `sysWrite`/`sysWritev`), if it is on the pages of a file
(`FileMap.pages`, a regular file, say) whose writing is not denied (`Files.denyWrite`), is on a file no backing of
`s`'s memory holds a page of. A write puts its bytes into the pages of the file its descriptor is on, where every
mapping of the file sees them (`sysWrite`, `sysWritev`). Every backing counts, one a page maps now and one a page mapped before an
`munmap`, a `MAP_FIXED` replacement or an `mremap` (the memory keeps those backings, as `ChangesOnly` speaks of them
too): a file the process mapped and unmapped earlier (the dynamic loader's cache, say) does not meet this. A descriptor
that is closed, on a pipe, a terminal or `/dev/null`, or on a regular file the process never mapped, meets it. A
contract of a function that writes to `fd` assumes it, so that its frame (`ChangesOnly`) can hold. -/
def WriteUnmapped (s : State) (fd : Nat) : Prop :=
  ∀ f id, s.proc.files.desc (fd % 2 ^ 32) = some f → f.map = .pages id → s.proc.mm.mem.files.denyWrite id = false →
    ∀ j fp, (s.proc.mm.mem.backings j).filePage = some fp → fp.file ≠ id

/-- Descriptor `fd` of the descriptor table `fds` is open for reading on the pages of the file `f` (`FileMap.pages`: a
regular file, whose bytes `read` delivers from the description's position, `sysRead`): the description it refers to is
readable and on `f`. A statement over an input file read through `fd` (standard input redirected from a file) assumes
it. -/
def InputAt (fds : FdTable) (fd : Nat) (f : FileId) : Prop :=
  ∃ o, fds.desc fd = some o ∧ o.readable = true ∧ o.map = .pages f

/-- Descriptor `j` of the descriptor table `fds`, if open, is not on the pages of the file `f`: a `write` to `j` changes
none of `f`'s bytes (`sysWrite` writes into the pages of the file its description is on). A statement whose program
reads a file `f` and writes to `j` (standard output) assumes it, so that what it reads is the file's bytes at the start;
a closed descriptor, a pipe, a terminal or another file meets it. -/
def OutAt (fds : FdTable) (j : Nat) (f : FileId) : Prop :=
  ∀ o, fds.desc j = some o → o.map ≠ .pages f

/-! ## Files -/

/-- File `g` holds in `X` what it held in `s`: its size and every page's bytes as they were. -/
def FileKept (s X : State) (g : FileId) : Prop :=
  X.proc.mm.mem.files.size g = s.proc.mm.mem.files.size g ∧
    ∀ k, X.proc.mm.mem.files.page ⟨g, k⟩ = s.proc.mm.mem.files.page ⟨g, k⟩

/-- From `s₀` to `s`, every file is as it was (`FileKept`: its size and every page's bytes) but those the descriptors `ds`
of `s₀`'s table are open on: a file on whose pages one of them is (`FileMap.pages`; `OutAt` fails for it) may have
changed, whichever descriptor it was changed through. A descriptor of `ds` that is closed, or on a pipe, a terminal or
`/dev/null`, releases nothing. A function changes a file by `write` and `pwrite64` to a descriptor on it (`sysWrite`,
`sysPwrite64`) and by stores into a shared mapping of it; a contract names the descriptors it writes through
(`Contract.writesTo`), and its footprint excludes shared mappings from what it writes (`Footprint.Ok`). The files a
function reads (an input file) are those its callers know the bytes of after the call. The descriptors are those of
`s₀`: a function that opens a file and writes to it through the new descriptor may change a file no descriptor of `ds`
is open on (the file it opens may also be one a descriptor of `ds` is on), and has no contract under this form
(this form does not cover functions that open files by path). An environment that lets another agent write a file
or change its size (`EnvEvent.fileWrite`, `EnvEvent.fileSize`) breaks this for every file but those that deny writes
(`Files.denyWrite`: a running executable, which neither event changes); `Undisturbed` excludes both. -/
def KeepsFilesBut (ds : List Nat) (s₀ s : State) : Prop :=
  ∀ g, (∀ d ∈ ds, OutAt s₀.proc.files d g) → FileKept s₀ s g

end ZellicX86
