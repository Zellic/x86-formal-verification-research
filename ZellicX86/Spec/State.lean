import ZellicX86.Spec.Memory
import ZellicX86.Spec.Signal
import ZellicX86.Spec.Outcome
/-!
# Machine state

All state user code can observe, split by owner, as the kernel shares state between a process's threads:

- `Cpu` — one thread's processor state (registers of every kind, `rip`, `rflags`, `PKRU`);
- `ThreadK` — the kernel's per-thread state that user code can observe or that decides
  what the kernel does (signal mask, `rseq` registration, ...);
- `Proc` — state shared by all threads of the process, in the kernel's shared structures:
  the address space with the program break, the descriptor table, the open file descriptions,
  the signal actions, and the signal state with the resource limits.

A run of a single-threaded process is a `State`, one of each. The processor state includes
x87 and vector registers, even for programs that do not use them.

Sources: SDM Vol. 1, 3.4 "Basic Program Execution Registers", 8.1 "x87 FPU Execution
Environment", 10.2 and 15.1 (SSE/AVX registers), Vol. 3A 2.7 (`PKRU`); Linux v6.18
`include/linux/sched.h` (`struct task_struct`), `include/linux/sched/signal.h`,
`include/linux/mm_types.h`, `include/linux/fdtable.h`, `include/linux/fs.h`, `kernel/fork.c`.
-/
namespace ZellicX86

/-- The sixteen 64-bit general-purpose registers (SDM Vol. 1, 3.4.1.1). -/
structure Gprs where
  rax : BitVec 64
  rcx : BitVec 64
  rdx : BitVec 64
  rbx : BitVec 64
  rsp : BitVec 64
  rbp : BitVec 64
  rsi : BitVec 64
  rdi : BitVec 64
  r8 : BitVec 64
  r9 : BitVec 64
  r10 : BitVec 64
  r11 : BitVec 64
  r12 : BitVec 64
  r13 : BitVec 64
  r14 : BitVec 64
  r15 : BitVec 64

/-- A general-purpose register by its encoding number (`rax` = 0, ..., `r15` = 15; SDM
Vol. 2, 2.2.1.2, Table 2-4). -/
abbrev Reg := Fin 16

/-- Register `r`. -/
def Gprs.get (g : Gprs) (r : Reg) : BitVec 64 :=
  match r.val with
  | 0 => g.rax | 1 => g.rcx | 2 => g.rdx | 3 => g.rbx
  | 4 => g.rsp | 5 => g.rbp | 6 => g.rsi | 7 => g.rdi
  | 8 => g.r8 | 9 => g.r9 | 10 => g.r10 | 11 => g.r11
  | 12 => g.r12 | 13 => g.r13 | 14 => g.r14 | _ => g.r15   -- 15

/-- `g` with register `r` set to `v`. -/
def Gprs.set (g : Gprs) (r : Reg) (v : BitVec 64) : Gprs :=
  match r.val with
  | 0 => { g with rax := v } | 1 => { g with rcx := v }
  | 2 => { g with rdx := v } | 3 => { g with rbx := v }
  | 4 => { g with rsp := v } | 5 => { g with rbp := v }
  | 6 => { g with rsi := v } | 7 => { g with rdi := v }
  | 8 => { g with r8 := v } | 9 => { g with r9 := v }
  | 10 => { g with r10 := v } | 11 => { g with r11 := v }
  | 12 => { g with r12 := v } | 13 => { g with r13 := v }
  | 14 => { g with r14 := v } | _ => { g with r15 := v }   -- 15

/-- `RFLAGS` (SDM Vol. 1, 3.4.3, Figure 3-8). Bit 1 always reads 1; bits 3, 5, 15 and 22–63
are reserved and read 0, so they are not stored. -/
structure Rflags where
  /-- Carry, bit 0. -/
  cf : Bool
  /-- Parity, bit 2. -/
  pf : Bool
  /-- Auxiliary carry, bit 4. -/
  af : Bool
  /-- Zero, bit 6. -/
  zf : Bool
  /-- Sign, bit 7. -/
  sf : Bool
  /-- Trap (single-step), bit 8. -/
  tf : Bool
  /-- Interrupt enable, bit 9 (always set in user mode under Linux). -/
  if_ : Bool
  /-- Direction, bit 10. -/
  df : Bool
  /-- Overflow, bit 11. -/
  of : Bool
  /-- I/O privilege level, bits 12–13. -/
  iopl : BitVec 2
  /-- Nested task, bit 14. -/
  nt : Bool
  /-- Resume, bit 16. -/
  rf : Bool
  /-- Virtual-8086 mode, bit 17. -/
  vm : Bool
  /-- Alignment check, bit 18. -/
  ac : Bool
  /-- Virtual interrupt, bit 19. -/
  vif : Bool
  /-- Virtual interrupt pending, bit 20. -/
  vip : Bool
  /-- `CPUID` availability toggle, bit 21. -/
  id : Bool

/-- `RFLAGS` as a 64-bit value. -/
def Rflags.toBits (f : Rflags) : BitVec 64 :=
  let b (x : Bool) (i : Nat) : BitVec 64 := if x then 1 <<< i else 0
  b f.cf 0 ||| 2 ||| b f.pf 2 ||| b f.af 4 ||| b f.zf 6 ||| b f.sf 7 ||| b f.tf 8 |||
  b f.if_ 9 ||| b f.df 10 ||| b f.of 11 ||| (f.iopl.setWidth 64 <<< 12) ||| b f.nt 14 |||
  b f.rf 16 ||| b f.vm 17 ||| b f.ac 18 ||| b f.vif 19 ||| b f.vip 20 ||| b f.id 21

/-- Segment registers (SDM Vol. 1, 3.4.2). In 64-bit mode only the `FS` and `GS` bases
affect addresses (3.3.7.1); the selectors are still visible. -/
structure Segs where
  cs : BitVec 16
  ss : BitVec 16
  ds : BitVec 16
  es : BitVec 16
  fs : BitVec 16
  gs : BitVec 16
  fsBase : Addr
  gsBase : Addr

/-- x87 FPU state (SDM Vol. 1, 8.1; AMD APM Vol. 1, 6.2): the eight 80-bit data registers `R0`–`R7`
(physical order; `ST(i)` is `R((TOP + i) mod 8)`), the control and status words, which registers
are not empty, the last opcode, and the last instruction and data pointers. The MMX registers alias
the data registers.

`full` has bit `j` set when `Rj` is not empty: the abridged tag word `FXSAVE` and `XSAVE` store
(SDM Vol. 1, 13.5.1). Only empty or not is state: the full tag word's other three tags (valid,
zero, special) are computed from the register's contents when the tag word is stored
(`x87TagsFrom`), and a loaded tag word is used only to tell empty from not empty (SDM Vol. 1, 8.1.7;
Vol. 3A, 15.2.1; APM Vol. 1, 6.2.4). -/
structure X87 where
  st : Fin 8 → BitVec 80
  fcw : BitVec 16
  fsw : BitVec 16
  full : BitVec 8
  fop : BitVec 11
  fip : BitVec 64
  fdp : BitVec 64

/-- SSE/AVX/AVX-512 state (SDM Vol. 1, 10.2, 14.1, 15.1): `ZMM0`–`ZMM31` (`XMMi` and
`YMMi` are their low 128 and 256 bits), opmask registers `k0`–`k7`, and `MXCSR`. -/
structure VecRegs where
  zmm : Fin 32 → BitVec 512
  k : Fin 8 → BitVec 64
  mxcsr : BitVec 32

/-- `z` with register `ZMMn` replaced by `v`. -/
def withZmm (z : Fin 32 → BitVec 512) (n : Fin 32) (v : BitVec 512) : Fin 32 → BitVec 512 :=
  fun j => if j = n then v else z j

/-- `k` with opmask register `kn` replaced by `v`. -/
def withK (k : Fin 8 → BitVec 64) (n : Fin 8) (v : BitVec 64) : Fin 8 → BitVec 64 :=
  fun j => if j = n then v else k j

/-- One thread's processor state. -/
structure Cpu where
  gpr : Gprs
  rip : Addr
  rflags : Rflags
  seg : Segs
  x87 : X87
  vec : VecRegs
  /-- Protection-key rights register (SDM Vol. 3A, 2.7). Per thread. -/
  pkru : BitVec 32

/-- A register a statement can name: a general register, a vector register `ZMMn` (whose
low parts are `XMMn` and `YMMn`), or an opmask register `kn`. -/
inductive RegName
  | gpr (r : Reg)
  | zmm (n : Fin 32)
  | k (n : Fin 8)

/-- Register `r` has the same value in `c` and `c'`. -/
def Cpu.agreeOn (c c' : Cpu) : RegName → Prop
  | .gpr r => c.gpr.get r = c'.gpr.get r
  | .zmm n => c.vec.zmm n = c'.vec.zmm n
  | .k n => c.vec.k n = c'.vec.k n

/-- A thread's registered restartable-sequences area (`rseq(2)`, `kernel/rseq.c`). -/
structure RseqReg where
  area : Addr
  len : BitVec 32
  sig : BitVec 32

/-- A thread's alternate signal stack as the kernel keeps it (`sas_ss_sp`, `sas_ss_size`,
`sas_ss_flags` of `struct task_struct`; `sigaltstack(2)`): its lowest address and size, size 0 when
there is none, and the flags it was set up with (`SS_AUTODISARM`, and the mode `sigaltstack` was
given). -/
structure AltStack where
  sp : Addr
  size : BitVec 64
  flags : BitVec 32

/-- No alternate stack (`sas_ss_reset`, `include/linux/sched/signal.h`). -/
def AltStack.disabled : AltStack := ⟨0, 0, SS_DISABLE⟩

/-- A signal waiting to be delivered: the kernel's queue entry (`struct sigqueue`) with what it
records (`SigInfo`), and why it was sent, which the outcome reports if the signal ends the process
(`KillCause`; the kernel does not keep it). -/
structure Queued where
  info : SigInfo
  cause : KillCause

/-- Pending signals (`struct sigpending`, `include/linux/signal_types.h`), oldest first: a signal is
pending if an entry for it is. A signal 1–31 has at most one entry (`legacy_queue`,
`kernel/signal.c`); a real-time signal (32–64) one per time it was sent. -/
abbrev SigPending := List Queued

/-- The signals with an entry in `p`. -/
def SigPending.set (p : SigPending) : SigSet :=
  p.foldl (fun m q => m.insert q.info.signo) 0

/-- A thread's user shadow stack, when it has one (SDM Vol. 1, ch. 18; Linux enables it with
`arch_prctl(ARCH_SHSTK_ENABLE, ARCH_SHSTK_SHSTK)`, `arch/x86/kernel/shstk.c`). With it, a near
`CALL` also pushes the return address on the shadow stack and a near `RET` pops it from there and
raises `#CP` when the two differ. -/
structure ShadowStack where
  /-- The shadow-stack pointer `SSP` (CPU state, `IA32_PL3_SSP`; kept here with the rest of the
  shadow-stack state). -/
  ssp : Addr
  /-- The mapping the kernel allocated for it (`struct thread_shstk`, `arch/x86/include/asm/shstk.h`):
  its start and length. -/
  base : Addr
  size : BitVec 64
  /-- `WRSS` is enabled (`IA32_U_CET.WR_SHSTK_EN`, `arch_prctl(ARCH_SHSTK_ENABLE, ARCH_SHSTK_WRSS)`). -/
  wrss : Bool
  deriving DecidableEq

/-- The kernel's per-thread state. -/
structure ThreadK where
  /-- Thread id. -/
  tid : Nat
  /-- Blocked signals. -/
  sigmask : SigSet
  /-- Signals pending for this thread. -/
  pending : SigPending
  altStack : AltStack
  rseq : Option RseqReg
  /-- `set_tid_address(2)`: written with 0 when the thread exits while others share the
  address space. -/
  clearChildTid : Addr
  /-- `set_robust_list(2)`: head of the robust futex list, walked when the thread exits. -/
  robustList : Addr
  /-- `CPUID` faulting is on for the thread (`TIF_NOCPUID`, set by `arch_prctl(ARCH_SET_CPUID,
  0)`): `CPUID` raises `#GP(0)` (`arch/x86/kernel/process.c`). -/
  cpuidFaults : Bool
  /-- `RDTSC` faults for the thread (`TIF_NOTSC`, set by `prctl(PR_SET_TSC, PR_TSC_SIGSEGV)` and by
  `seccomp(SECCOMP_SET_MODE_STRICT)`, which make the kernel set `CR4.TSD` while the thread runs):
  `RDTSC` raises `#GP(0)` (`arch/x86/kernel/process.c` `disable_TSC`). Unlike `cpuidFaults` it
  survives `execve`. -/
  tscFaults : Bool
  /-- The thread's user shadow stack, if enabled (`ShadowStack`). `execve` starts every program
  without one (`reset_thread_features`, `arch/x86/kernel/shstk.c`). -/
  shstk : Option ShadowStack
  /-- The thread's real user id (`cred->uid`), which a signal it sends carries (`si_uid`). -/
  uid : Nat

/-- What `mmap(2)` of an open file maps (the file's `mmap` operation, `file->f_op->mmap`): fixed
for an open file description, since its file and the file's type are. -/
inductive FileMap
  /-- The pages of file `file` (`Files`): a regular file of a disk file system or tmpfs, a memfd, a
  block device. A mapping reads and writes the page cache, and `read(2)` and `write(2)` go through it
  at the open file's position (`OpenTable.pos`; `mm/filemap.c` `filemap_read`,
  `generic_perform_write`), and its open file descriptions have a position and take reads and writes
  at an offset (`FMODE_LSEEK`, `FMODE_PREAD`, `FMODE_PWRITE`, which `fs/open.c` `do_dentry_open` sets). A
  file whose reads bypass the page cache though it can be mapped (FUSE with `FOPEN_DIRECT_IO`, whose server
  answers each read), and one opened without a position (`stream_open`, `nonseekable_open`: FUSE with
  `FOPEN_STREAM` or `FOPEN_NONSEEKABLE`, `fs/fuse/file.c` `fuse_finish_open`), are not of this kind but
  `other`. -/
  | pages (file : FileId)
  /-- A file without an `mmap` operation (a pipe, socket, directory, most character devices):
  `ENODEV` (`mm/mmap.c` `do_mmap`, `can_mmap_file`). -/
  | none
  /-- A descriptor opened with `O_PATH`, which `mmap`, `read` and `write` refuse (`EBADF`; `fget`
  does not return it, `fs/file.c`). -/
  | path
  /-- A device or special file whose mapping the model does not know (`/dev/zero`, `/dev/mem`,
  graphics devices, hugetlbfs, DAX files): an `mmap` of it is not modelled. -/
  | other
  deriving DecidableEq

/-- Whether an open file is on the pages of a file (`FileMap.pages`). -/
def FileMap.isPages : FileMap → Bool
  | .pages _ => true
  | _ => false

/-- An open file description behind a file descriptor, as far as it stays the same while it is open.
Its identity is opaque; what changes, its position and status flags, the process keeps per description
(`OpenTable.pos`). What `read` and `write` on it return is the file's pages for a file with pages
(`FileMap.pages`) and otherwise the environment's answer (`Spec/Request.lean`). -/
structure OpenFile where
  id : Nat
  /-- Opened for reading (`O_RDONLY` or `O_RDWR`). -/
  readable : Bool
  /-- Opened for writing (`O_WRONLY` or `O_RDWR`). -/
  writable : Bool
  /-- What a mapping of it maps. -/
  map : FileMap
  deriving DecidableEq

/-- What of an open file description changes while it is open (`struct file`, `include/linux/fs.h`):
its position and its status flags that may change (`fcntl(F_SETFL)`). Every descriptor on the description sees the same
(`dup(2)`), in every process that has one (`fork(2)`, `SCM_RIGHTS`); a `read` or `write` of a regular
file holds the description's position lock while it runs (`fs/file.c` `fdget_pos`, `FMODE_ATOMIC_POS`),
so another process moves it between two calls of this one, not inside one (`EnvEvent.filePos`). -/
structure FilePos where
  /-- The position (`f_pos`), in bytes from the file's start, where the next `read` or `write` goes
  on (`fs/read_write.c` `ksys_read`, `ksys_write`). -/
  offset : Nat
  /-- Writes go to the file's end (`O_APPEND` in `f_flags`; `generic_write_checks_count`), which
  `fcntl(F_SETFL)` may change. -/
  append : Bool
  /-- Its other status flags (`f_flags`, which `fcntl(F_GETFL)` reports; the bit of `O_APPEND` here means
  nothing): the access mode, `O_NONBLOCK`, `O_DSYNC`, `FASYNC`, `O_DIRECT`, `O_LARGEFILE`, `O_DIRECTORY`,
  `O_NOFOLLOW`, `O_NOATIME`, `__O_SYNC`, `O_PATH`, as the description's creation set them (`fs/open.c`
  `build_open_flags`, `do_dentry_open`). `fcntl(F_SETFL)` changes those of `SETFL_MASK`
  (`O_NONBLOCK`, `O_DIRECT`, `O_NOATIME`; `fs/fcntl.c` `setfl`) and, through the file's `fasync` operation, `FASYNC`;
  the others stay. -/
  flags : Nat

/-- A resource limit (`struct rlimit`, `getrlimit(2)`): the soft limit the kernel enforces and the
hard limit up to which the soft one may be raised. `RLIM_INFINITY` is `2 ^ 64 - 1`. -/
structure Rlimit where
  cur : BitVec 64
  max : BitVec 64

/-- `RLIM_INFINITY` (`include/uapi/asm-generic/resource.h`): no limit. -/
def RLIM_INFINITY : BitVec 64 := -1

/-- The number of the file size limit, `RLIMIT_FSIZE` (`include/uapi/asm-generic/resource.h`). -/
def RLIMIT_FSIZE : Fin 16 := 1

/-- The number of the open descriptors' limit, `RLIMIT_NOFILE` (`include/uapi/asm-generic/resource.h`). -/
def RLIMIT_NOFILE : Fin 16 := 7

/-- The number of the data segment's limit, `RLIMIT_DATA` (`include/uapi/asm-generic/resource.h`): the bytes of the
private writable mappings and of the heap (`mm/mmap.c` `may_expand_vm`'s `data_vm`, `brk`'s `check_data_rlimit`). The
model's `brk` and `mmap` do not check it: a refusal for it is a `Request.memFail` answer. -/
def RLIMIT_DATA : Fin 16 := 2

/-- The number of the stack's resource limit, `RLIMIT_STACK` (`include/uapi/asm-generic/resource.h`). -/
def RLIMIT_STACK : Fin 16 := 3

/-- The number of the address space's limit, `RLIMIT_AS` (`include/uapi/asm-generic/resource.h`): the bytes of all
mappings (`may_expand_vm`'s `total_vm`). The model's `brk` and `mmap` do not check it: a refusal for it is a
`Request.memFail` answer. -/
def RLIMIT_AS : Fin 16 := 9

/-- The address space (`struct mm_struct`, `include/linux/mm_types.h`), which threads created with
`CLONE_VM` share and `fork` copies: the mappings and the memory behind them, and the program break,
which `brk(2)` moves together with the mapping of the heap. The files' pages and sizes in it
(`Memory.files`) are system-wide; the address space holds its view of them. -/
structure Mm where
  /-- The mappings and what backs them (`Memory`). -/
  mem : Memory
  /-- The lowest break `brk(2)` accepts (`min_brk` in `mm/mmap.c` `brk`: `mm->start_brk`, or
  `mm->end_data` with `CONFIG_COMPAT_BRK` when the break was not randomized). -/
  brkMin : Addr
  /-- Current program break (`mm->brk`). -/
  brk : Addr

/-- A descriptor's entry in the descriptor table: the open file description it refers to (`fdt->fd`)
and its close-on-exec flag (`FD_CLOEXEC`, the `fdt->close_on_exec` bit; `include/linux/fdtable.h`),
which `execve` closes the descriptor by (`do_close_on_exec`, `fs/file.c`). -/
structure FdEntry where
  file : OpenFile
  cloexec : Bool
  deriving DecidableEq

/-- The descriptor table (`struct files_struct`, `include/linux/fdtable.h`), which threads created with
`CLONE_FILES` share and `fork` copies: descriptor number to its entry, if open. -/
abbrev FdTable := Nat → Option FdEntry

/-- The open file description descriptor `n` of table `t` refers to, if `n` is open. -/
def FdTable.desc (t : FdTable) (n : Nat) : Option OpenFile := (t n).map FdEntry.file

/-- The open file description descriptor `n` of table `t` refers to, as the kernel's `fdget` gives it to
a call that does not take an `O_PATH` descriptor (`fs/file.c` `__fget_light` with `FMODE_PATH`): none if
`n` is not open or is open with `O_PATH` (`FileMap.path`), which the call fails with `EBADF`. Calls that
take one (`fdget_raw`: `close`, `fstat`, the directory of `openat`) use `desc`, and so do `read` and `write`
(`fdget_pos`), which check the access mode next: a descriptor opened with `O_PATH` is neither readable nor
writable (`sysOpenat`), so they fail with the same `EBADF`. -/
def FdTable.descNoPath (t : FdTable) (n : Nat) : Option OpenFile :=
  (t.desc n).filter fun f => f.map != .path

/-- The open file descriptions as far as they change while open (`struct file`, `include/linux/fs.h`).
They are not part of a descriptor table: descriptors of any table, in any process, may refer to one
(`dup(2)`, `fork(2)`, `SCM_RIGHTS`), and every one of them sees the same position. -/
structure OpenTable where
  /-- The position and the status flags that may change of each open file description, by description
  (the same identity, `OpenFile.id`). The position is used for files with pages (`FileMap.pages`); what
  another file does with a position is its own (a pipe has none, a terminal ignores it). -/
  pos : OpenFile → FilePos
  /-- The identity (`OpenFile.id`) the next open file description the process creates gets: the kernel
  allocates a new `struct file` for each (`fs/file_table.c` `alloc_empty_file`), so it is above every
  identity of a description the process holds (`ExecChoice.nextOpen`), and each creation moves it on. -/
  next : Nat

/-- The signal state the threads of a process share (`struct signal_struct`,
`include/linux/sched/signal.h`), which `CLONE_THREAD` shares and `fork` makes new. -/
structure ProcSignal where
  /-- Signals pending for the process as a whole (`shared_pending`). -/
  pending : SigPending
  /-- The resource limits (`rlim`), by number `RLIMIT_CPU` = 0 to `RLIMIT_RTTIME` = 15
  (`include/uapi/asm-generic/resource.h`). -/
  rlimits : Fin 16 → Rlimit
  /-- `SIGNAL_UNKILLABLE` (`flags`): the process is the init of a PID namespace, its child reaper
  (`kernel/fork.c` `copy_process`; the first process of a container started without an init of its
  own). Signals whose action is `SIG_DFL` are then ignored when sent, unless the sender forces
  `SIGKILL` or `SIGSTOP` (`sig_task_ignored`), and dropped when taken, but for `SIGKILL` and `SIGSTOP`
  (`get_signal`); `execve` keeps the flag, and the kernel clears it when it forces a signal whose action
  is then `SIG_DFL` (`force_sig_info_to_task`). The initial namespace's init (`is_global_init`), which
  never takes `SIGKILL` or `SIGSTOP` at all, is not in the model's scope. -/
  unkillable : Bool

/-- State shared by all threads of the process, grouped as the kernel shares it: each field but
`opens` is a structure, or part of one, that `clone(2)` shares or copies as a whole by one flag
(`kernel/fork.c` `copy_process`); the open file descriptions are shared whatever the flags. -/
structure Proc where
  /-- The address space (`CLONE_VM`). -/
  mm : Mm
  /-- The descriptor table (`CLONE_FILES`). -/
  files : FdTable
  /-- The open file descriptions the process refers to, shared whatever the flags. -/
  opens : OpenTable
  /-- The signal actions (`struct sighand_struct`; `CLONE_SIGHAND`). -/
  sighand : Signal → SigAction
  /-- Signals pending for the process, and its resource limits (`CLONE_THREAD`). -/
  signal : ProcSignal
  /-- The number of descriptors the table holds before it must grow (`fdt->max_fds`,
  `include/linux/fdtable.h`; with the table, `CLONE_FILES`): at least `NR_OPEN_DEFAULT`, 64, above every
  open descriptor, and it only grows (`fs/file.c` `expand_files`; a copy for `fork` or `execve`'s
  `unshare_files` sizes a new table to its open descriptors, `dup_fd`). -/
  fdMax : Nat

/-- The state of a single-threaded process. -/
structure State where
  proc : Proc
  cpu : Cpu
  thread : ThreadK

end ZellicX86
