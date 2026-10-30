import ZellicX86.Spec.Elf
import ZellicX86.Spec.Linux.Basic
import ZellicX86.Spec.Linux.Stack
import ZellicX86.Spec.Linux.Syscall.Common
import ZellicX86.Spec.Linux.Vsyscall
/-!
# Linux: `execve` of a static ELF executable

The state of a new process at its first instruction, as Linux v6.18 builds it for a static
x86-64 `ET_EXEC` file: the address space (one mapping per loadable segment, the initial stack,
the vDSO), the registers, and the kernel's per-process and per-thread state.

What `execve` depends on is explicit:
- the files (`Files`), the executable among them by its identity, read through its pages as
  any other file (`Spec/Memory.lean`): the segments are private mappings of its pages;
- what the caller passes and the process inherits (`ExecArgs`);
- how the kernel is built and booted (`Profile.linux`: the vDSO, `CONFIG_COMPAT_BRK`) and the
  settings an administrator may change as `execve` reads them (`KernelConfig`), fixed for a theorem;
- what the kernel chooses at random for each new process (`ExecChoice`), within the ranges
  `ExecChoice.Valid` states. `Valid` may admit more than the kernel does; it admits less only in
  the case `ExecChoice.VdsoPlace` names (a vDSO placed where the stack must then grow, a launch the
  kernel ends by killing the new program), which the theorems therefore do not cover;
- what the kernel computed from the processor at boot (`Profile.aux`).

Not modelled (`notModelled`): ELF interpreters (`PT_INTERP`, dynamically linked programs), `ET_DYN` executables
(static PIE), files the ELF loader rejects (other binary formats may accept them), the `MMAP_PAGE_ZERO`
personality, segments that overlap the initial stack, and a `vm.max_map_count` too low to be sure it is never
reached (`KernelConfig.maxMapCount`). Permission checks on the file (`EACCES`, `noexec` mounts) are the caller's
side and assumed to allow the call; the security module's decisions are an input (`ExecArgs.lsm`, `LsmVerdict`; a
credential transition by the security module that changes what the new program inherits is not modelled).
Failures that follow from the state are computed: the memory limits `RLIMIT_AS` and `RLIMIT_DATA` where the
kernel checks them (`may_expand_vm`), an inherited `PR_SET_MDWE` (`ExecArgs.mdwe`), the `RLIMIT_NPROC` recheck
(`ExecArgs.nprocOver`). Failures that do not, the kernel's own memory (allocations, overcommit) and a fatal
signal while it waits, are the kernel's choice (`ExecChoice.fail`). A failure in neither group ends "not
modelled", never in success (`RLIMIT_MEMLOCK` cannot fail it: no area of the new program is locked).

Sources: Linux v6.18 `fs/exec.c` (`do_execveat_common`, `bprm_stack_limits`, `copy_strings`,
`setup_arg_pages`, `begin_new_exec`), `fs/binfmt_elf.c` (`load_elf_binary`, `elf_load`,
`padzero`, `create_elf_tables`), `mm/util.c` (`randomize_stack_top`, `randomize_page`),
`arch/x86/kernel/process.c` (`arch_align_stack`, `arch_randomize_brk`),
`arch/x86/kernel/process_64.c` (`start_thread_common`), `arch/x86/entry/vdso/vma.c`
(`map_vdso`), `arch/x86/mm/mmap.c` (`arch_pick_mmap_layout`, `mmap_base`), `arch/x86/kernel/sys_x86_64.c`
(`arch_get_unmapped_area_topdown`, `arch_get_unmapped_area`), `mm/mmap.c` (`__get_unmapped_area`), `mm/vma.c`
(`unmapped_area_topdown`, `unmapped_area`), `mm/huge_memory.c` (`__thp_get_unmapped_area`), `arch/x86/include/asm/elf.h`, `kernel/signal.c` (`flush_signal_handlers`).
-/
namespace ZellicX86
open Signal

/-! ## Inputs -/

/-- What the security module (the LSMs the kernel runs: SELinux, AppArmor, Landlock, …) decides about an `execve`, by
its policy and the caller's credentials and labels, none of which the model records: the caller states it
(`ExecArgs.lsm`). Its hooks on the path, in order (Linux v6.18): opening the file for execution (`security_file_open`,
in `do_dentry_open`, `fs/open.c`, from `do_open_execat`), before the strings are copied; the exec itself
(`security_bprm_creds_for_exec` in `bprm_execve`, `security_bprm_check` in `search_binary_handler`, `fs/exec.c`), after
them, and `security_bprm_creds_from_file` in `begin_new_exec`, after the ELF loader's checks of the file and before the
point of no return (the model reports a refusal by any of these hooks before it reads the file; that the last hook
runs only for files the loader accepts makes no difference, since a rejected file is not modelled either way); its
credential transition (`bprm_committing_creds`, `bprm_committed_creds`), past the point of no return; the mappings of
the file's segments (`security_mmap_file` in `vm_mmap_pgoff`, `mm/util.c`, `security_mmap_addr` in
`__get_unmapped_area`, `mm/mmap.c`), past it too. -/
inductive LsmVerdict where
  /-- It allows the call, with no credential transition that changes what the new program inherits. -/
  | allow
  /-- It refuses to open the file for execution, with error `e`. -/
  | openFile (e : Nat)
  /-- It refuses the exec, with error `e`. -/
  | exec (e : Nat)
  /-- It refuses a segment's mapping: the new program is killed. -/
  | mapping
  /-- It allows the call with a credential transition that changes what the new program inherits (SELinux on a change
  of the security identifier: descriptors the new domain may not use closed, `flush_unauthorized_files`; soft limits
  reset without `rlimitinh`; pending signals, handlers and the blocked mask flushed without `siginh`;
  `security/selinux/hooks.c`, `selinux_bprm_committing_creds`, `selinux_bprm_committed_creds`; AppArmor on a profile
  change likewise, `security/apparmor/lsm.c`): not modelled. -/
  | transition
  deriving DecidableEq, Repr

/-- An error a refusal before the point of no return gives is an error number (below `MAX_ERRNO`, 4096). -/
def LsmVerdict.Valid : LsmVerdict → Prop
  | .openFile e | .exec e => 0 < e ∧ e < 4096
  | _ => True

instance (v : LsmVerdict) : Decidable v.Valid := by
  cases v <;> unfold LsmVerdict.Valid <;> infer_instance

/-- The verdict refuses the file's opening. -/
def LsmVerdict.refusesOpen : LsmVerdict → Bool
  | .openFile _ => true
  | _ => false

/-- The verdict refuses the exec. -/
def LsmVerdict.refusesExec : LsmVerdict → Bool
  | .exec _ => true
  | _ => false

/-- The error of a refusal before the point of no return. -/
def LsmVerdict.err : LsmVerdict → Nat
  | .openFile e | .exec e => e
  | _ => 0

/-- What the caller of `execve` passes and what the new program inherits from the process
that calls it: the process's shared structures (`Proc`) as `execve` reads them, and the calling
thread's state it keeps. -/
structure ExecArgs where
  /-- The path as passed to `execve` (`AT_EXECFN` points to a copy). -/
  filename : List Byte
  /-- The argument strings, without their terminating NUL. -/
  argv : List (List Byte)
  /-- The environment strings, without their terminating NUL. -/
  envp : List (List Byte)
  /-- The real user id after the call (`AT_UID`; set-user-id and set-group-id files have changed the
  ids already). -/
  uid : Nat
  /-- The effective user id after the call (`AT_EUID`). -/
  euid : Nat
  /-- The real group id after the call (`AT_GID`). -/
  gid : Nat
  /-- The effective group id after the call (`AT_EGID`). -/
  egid : Nat
  /-- `AT_SECURE` (`bprm->secureexec`): the call changed credentials (set-user-id, file
  capabilities) or a security module asked for secure mode. -/
  secure : Bool
  /-- The calling process's descriptor table, with the close-on-exec flags (`FD_CLOEXEC`). -/
  files : FdTable
  /-- The size of that table (`Proc.fdMax`) as `execve` keeps it: the calling process's, or, where it
  shared its table with another (`CLONE_FILES`), the size of the copy `unshare_files` made (`dup_fd`,
  sized to the open descriptors); closing the close-on-exec descriptors leaves it. -/
  fdMax : Nat
  /-- The positions and status flags of the open file descriptions (`OpenTable.pos`): they belong to
  the descriptions, which outlive `execve`. -/
  filePos : OpenFile → FilePos
  /-- The calling process's signal dispositions (`Proc.sighand`, of which `execve` keeps only which
  signals are ignored). -/
  sighand : Signal → Disposition
  /-- The calling process's signal state (`Proc.signal`), which `execve` keeps: the signals pending
  for the process, the resource limits (`signal->rlim`, which `fork` copies and `execve` keeps
  but for the stack's soft limit of a secure exec, `ExecArgs.stackRlimit`), and whether it is a PID
  namespace's init (`ProcSignal.unkillable`, `signal->flags`). -/
  signal : ProcSignal
  /-- The calling thread's signal mask, kept across `execve`. -/
  sigmask : SigSet
  /-- Signals pending for the calling thread, kept across `execve`. -/
  threadPending : SigPending
  /-- The thread id of the new program's only thread (the process id). -/
  tid : Nat
  /-- The personality flags (`personality(2)`), inherited. -/
  personality : BitVec 32
  /-- `RDTSC` faults for the calling thread (`ThreadK.tscFaults`), inherited: `execve` does not
  clear `TIF_NOTSC` (`arch_setup_new_exec`). -/
  tscFaults : Bool
  /-- The flags of the calling thread's alternate signal stack (`sas_ss_flags`), which `execve`
  keeps while it removes the stack (`begin_new_exec`, `fs/exec.c`). -/
  altStackFlags : BitVec 32
  /-- The calling thread's `brk_randomized` (`struct task_struct`, `include/linux/sched.h`): set by an
  `execve` that randomized the program break, with `CONFIG_COMPAT_BRK` (`load_elf_binary`), in this
  process or one it was forked from (`fork` copies the task, `dup_task_struct`), and never cleared. It
  decides the lowest break `brk` accepts (`brkMin`). -/
  brkRandomized : Bool
  /-- Memory-deny-write-execute is on for the new program (`MMF_HAS_MDWE`): the calling process has it
  (`prctl(PR_SET_MDWE)`, `kernel/sys.c`, or inherited) and not `PR_MDWE_NO_INHERIT`, which drops it in every new
  address space, a fork's and an `execve`'s alike (`mm_init` takes `mmf_init_legacy_flags` of the caller's flags,
  `kernel/fork.c`, `include/linux/mm_types.h`). Then a new mapping both writable and executable is refused
  (`map_deny_write_exec`, `include/linux/mman.h`). Not set by default. -/
  mdwe : Bool := false
  /-- A `set*uid` call of the calling thread found its new user over `RLIMIT_NPROC` (`PF_NPROC_EXCEEDED`), and
  the user's processes still exceed the caller's `RLIMIT_NPROC` when `execve` checks again (`do_execveat_common`,
  `fs/exec.c`): the count is the system's, not this process's, so the caller states it. Not set by default. -/
  nprocOver : Bool := false
  /-- What the security module decides about the call (`LsmVerdict`). Allows it by default. -/
  lsm : LsmVerdict := .allow

/-- The most process ids a 64-bit kernel hands out, `PID_MAX_LIMIT` (`include/linux/threads.h`: 4 Mi, or fewer with
`CONFIG_BASE_SMALL`): the `pid_max` setting cannot exceed it (`kernel/pid.c`, `pid_max_max`), and a thread id is
below `pid_max` in every PID namespace (`alloc_pid`: `idr_alloc_cyclic`'s end is exclusive). -/
def pidMaxLimit : Nat := 4 * 1024 * 1024

/-- The arguments are what a caller can pass: C strings, ids that fit their types, limits the kernel
keeps: no string contains a NUL byte (`execve` copies each string up to its NUL), the ids are below `2 ^ 32`, the
id of the new program's only thread (after `de_thread`), which is the process id (`ExecArgs.tid`), is one `alloc_pid`
hands out (from 1, below `pidMaxLimit`), no soft limit exceeds its hard limit (`kernel/sys.c` `do_prlimit` refuses
that), and the security module's errors are error numbers (`LsmVerdict.Valid`). -/
def ExecArgs.Ok (a : ExecArgs) : Prop :=
  (∀ s ∈ a.filename :: a.argv ++ a.envp, ∀ b ∈ s, b ≠ 0) ∧
  a.uid < 2 ^ 32 ∧ a.euid < 2 ^ 32 ∧ a.gid < 2 ^ 32 ∧ a.egid < 2 ^ 32 ∧
  (∀ r, (a.signal.rlimits r).cur.toNat ≤ (a.signal.rlimits r).max.toNat) ∧
  0 < a.tid ∧ a.tid < pidMaxLimit ∧ a.lsm.Valid

/-- The settings of the running kernel that `execve` reads and that an administrator can change while
processes run, as `execve` reads them: fixed for a theorem, not chosen per process. Later reads of
the same settings are the environment's: `Request.initPkru` for `init_pkru`, and the refusals
`Request.memFail` and `Request.growFail` include those `vm.mmap_min_addr` causes. The kernel's build and
boot settings are the profile's
(`Profile.linux`, `LinuxBoot`). -/
structure KernelConfig where
  /-- The lowest address a mapping may start at (the `vm.mmap_min_addr` setting and the
  security module's minimum, `security_mmap_addr`; a process with `CAP_SYS_RAWIO` is exempt from
  the first for the segments' mappings, but not for the stack, whose checks read the setting itself:
  `setup_arg_pages` and `expand_downwards`). The model applies it to both: with `CAP_SYS_RAWIO` it may kill
  a launch the kernel starts, never the reverse. A statement about such a caller sets it to the security module's
  minimum (the segments' bound), and the model then only admits more than the kernel: it does not refuse the stack
  below `vm.mmap_min_addr`. -/
  mmapMinAddr : Nat
  /-- The initial `PKRU` (`init_pkru=` on the command line or the `init_pkru` file in debugfs;
  default `0x55555554`, every key but 0 access-disabled, `arch/x86/mm/pkeys.c`). -/
  initPkru : BitVec 32
  /-- `ignore_rlimit_data` (`mm/mmap.c`, a boot option also writable at run time, `core_param`): `RLIMIT_DATA` only
  warns, it refuses no mapping (`may_expand_vm`). Off by default. -/
  ignoreRlimitData : Bool := false
  /-- `vm.max_map_count` (`mm/mmap.c`, default `DEFAULT_MAX_MAP_COUNT`, 65530): `do_mmap` and `vm_brk_flags` refuse a
  new area when the process has more areas than this, the splitting of an area when it has as many (a process may end
  with one or two more). -/
  maxMapCount : Nat := 65530

/-- A configuration the kernel runs programs under: `init_pkru` allows access to key 0. Writing the
`init_pkru` file refuses a value that does not (`init_pkru_write_file`, `arch/x86/mm/pkeys.c`); the
boot option does not check (`setup_init_pkru`), but with protection keys enabled (`OSPKE`) no program
starts under such a value: `execve` loads it before it writes the new stack (`flush_thread`,
`pkru_flush_thread`), whose pages have key 0, so `create_elf_tables` fails and the new program is
killed, the first one (`init`) too. Without `OSPKE` the kernel never loads the value
(`pkru_write_default` returns early, `arch/x86/include/asm/pkru.h`; nor saves `PKRU`, which it leaves
out of `XCR0`, `xsave_cpuid_features` in `arch/x86/kernel/fpu/xstate.c`), so kernels with any value
run programs there; the condition excludes those, and loses nothing by it: the processor applies no
protection keys without `CR4.PKE` (`RDPKRU` and `WRPKRU` raise `#UD`), and the model's access checks
read `PKRU` only with `Features.pku` (`Memory.check`). -/
def KernelConfig.Valid (k : KernelConfig) : Prop := k.initPkru &&& 3 = 0

/-- Whether `execve` fails for a reason that does not follow from the state: the kernel's own memory (an allocation,
including those for a shared descriptor or signal-handler table and the new credentials' counts; the overcommit
policy's accounting, `security_vm_enough_memory_mm`, which depends on the whole system's commitments), or a fatal
signal while it waits for a lock (`fs/exec.c`, `fs/binfmt_elf.c`). -/
inductive ExecFail where
  /-- None: the call goes as the model computes. -/
  | none
  /-- Before the point of no return: `execve` fails with error `e` and the caller goes on. -/
  | early (e : Nat)
  /-- Past the point of no return (`begin_new_exec`): the kernel kills the new program (`SIGSEGV`,
  `force_fatal_sig` in `bprm_execve`). -/
  | late
  deriving DecidableEq, Repr

/-- What the kernel chooses at random for a new process. -/
structure ExecChoice where
  /-- The end of the initial stack's mapping: `STACK_TOP` minus a random number of pages
  (`randomize_stack_top`), minus 0 or 1 more page from `arch_align_stack` in
  `setup_arg_pages`. -/
  stackTop : Nat
  /-- The random number of bytes `create_elf_tables` leaves below the strings
  (`arch_align_stack`, before rounding down to 16). -/
  stackAlign : Nat
  /-- The 16 bytes at `AT_RANDOM`, least significant first. -/
  random : BitVec 128
  /-- The address of the vDSO's first data page (`get_unmapped_area`). -/
  vdsoBase : Nat
  /-- The current contents of the vDSO's data pages that have a source; the kernel rewrites them
  at any time. -/
  vdsoData : Fin 6 → Frame
  /-- The initial program break (`mm->start_brk = mm->brk`). -/
  brk : Nat
  /-- Where the identities of the open file descriptions the new program creates start (`OpenTable.next`):
  above those of the descriptions it inherits (`ExecChoice.Valid`), since each new one is a new
  `struct file`. -/
  nextOpen : Nat
  /-- Whether the kernel fails the call for a reason the model does not track (`ExecFail`). -/
  fail : ExecFail := .none

/-- The address of the vDSO's code, `AT_SYSINFO_EHDR`. -/
def ExecChoice.vdsoText (c : ExecChoice) : Nat := c.vdsoBase + 6 * 4096

/-- The end of the vDSO with code `text`. -/
def ExecChoice.vdsoEnd (c : ExecChoice) (text : List Frame) : Nat :=
  c.vdsoText + 4096 * text.length

/-! ## Constants -/

/-- `E2BIG`, argument list too long (`include/uapi/asm-generic/errno-base.h`). -/
def E2BIG : Nat := 7


/-- `STACK_TOP` of a 64-bit process (`TASK_SIZE_LOW = DEFAULT_MAP_WINDOW`, `2 ^ 47 - 4096`, also
with 5-level paging). Despite its name this is not the kernel's `STACK_TOP_MAX` (`TASK_SIZE_MAX`,
`2 ^ 56 - 4096` with 5-level paging), where `execve` first builds the stack before `setup_arg_pages`
moves it. -/
def stackTopMax : Nat := 2 ^ 47 - 4096

/-- `MAX_ARG_STRLEN` (`include/uapi/linux/binfmts.h`): the longest argument or environment
string, with its NUL. -/
def maxArgStrlen : Nat := 32 * 4096

/-- `MAX_ARG_STRINGS` (`include/uapi/linux/binfmts.h`). -/
def maxArgStrings : Nat := 0x7FFFFFFF

/-- `MMAP_PAGE_ZERO` (`include/uapi/linux/personality.h`). -/
def MMAP_PAGE_ZERO : BitVec 32 := 0x0100000



/-! ## The stack limit -/

/-- `_STK_LIM`, 8 MiB (`include/uapi/linux/resource.h`). -/
def stkLim : Nat := 8 * 1024 * 1024

/-- The stack's soft limit in bytes as the caller has it, which limits the argument strings
(`bprm_stack_limits`). -/
def ExecArgs.stackLimit (a : ExecArgs) : Nat := (a.signal.rlimits RLIMIT_STACK).cur.toNat

/-- The stack's limit of the new program: the caller's, but a secure exec lowers a soft limit
above `_STK_LIM` to it, after the point of no return (`begin_new_exec`). The stack's mapping is set
up with it (`setup_arg_pages`). -/
def ExecArgs.stackRlimit (a : ExecArgs) : Rlimit :=
  let r := a.signal.rlimits RLIMIT_STACK
  if a.secure && decide (r.cur.toNat > stkLim) then { r with cur := BitVec.ofNat 64 stkLim } else r

/-! ## The argument strings -/

/-- `argv` as the kernel uses it: an empty list becomes `[""]` (`do_execveat_common`). -/
def ExecArgs.argv' (a : ExecArgs) : List (List Byte) := if a.argv = [] then [[]] else a.argv

/-- The strings `execve` copies to the top of the new stack, each with its NUL, from the lowest
address: `argv`, `envp`, the file name (`copy_strings` copies the last string first, below the
previous one). -/
def ExecArgs.strings (a : ExecArgs) : List Byte :=
  (a.argv' ++ a.envp ++ [a.filename]).flatMap fun s => s ++ [0]

/-- Whether `bprm_stack_limits` and `copy_strings` accept the strings: at most
`MAX_ARG_STRINGS` of each kind, each at most `MAX_ARG_STRLEN` bytes with its NUL, and all of
them together within a quarter of the stack limit (at most 6 MiB, at least 128 KiB) less the
space for their pointers. The stack the strings are copied to starts as one page and grows
down for them (`get_arg_page`), each time within `RLIMIT_STACK` (`acct_stack_growth`,
`mm/vma.c`), so their pages, with the 8 bytes above them, must fit the limit too. -/
def ExecArgs.withinLimits (a : ExecArgs) : Bool :=
  let limit := max (min (stkLim / 4 * 3) (a.stackLimit / 4)) maxArgStrlen
  let ptrs := 8 * (max a.argv.length 1 + a.envp.length)
  let pages := pageUp (8 + a.strings.length)
  a.argv.length ≤ maxArgStrings && a.envp.length ≤ maxArgStrings &&
  (a.argv' ++ a.envp).all (fun s => s.length + 1 ≤ maxArgStrlen) &&
  ptrs < limit && a.strings.length ≤ limit - ptrs && (pages ≤ 4096 || pages ≤ a.stackLimit)

/-! ## The initial stack -/

/-- The bytes of the 64-bit words `ws`, each little-endian. -/
def wordBytes (ws : List Nat) : List Byte :=
  ws.flatMap fun w => toBytesLE (BitVec.ofNat 64 w) 8

/-- The places on the initial stack (`fs/exec.c`, `create_elf_tables`), from the top down: 8
zero bytes; the strings (`ExecArgs.strings`) from `strings`; `stackAlign` bytes, rounded down
to 16, to `platform`; `"x86_64"` with its NUL just below `platform`; the 16 `AT_RANDOM` bytes
below that; then, from `sp` (16-aligned) up, the argument count, the `argv` pointers and 0, the
`envp` pointers and 0, and the auxiliary vector. -/
structure StackLayout where
  /-- The lowest byte of the strings. -/
  strings : Nat
  /-- The end of the platform string. -/
  platform : Nat
  /-- The initial `rsp`. -/
  sp : Nat
  /-- The lowest address of the stack's mapping as `setup_arg_pages` makes it: the pages of the
  strings and at least 128 KiB more, unless the stack's limit (`ExecArgs.stackRlimit`) is lower. -/
  reserved : Nat
  /-- The lowest address of the stack's mapping at the first instruction: `reserved`, or lower
  if the words from `sp` up do not fit above it (`create_elf_tables` grows the stack for them,
  `find_extend_vma_locked`). -/
  start : Nat

/-- The platform string, `ELF_PLATFORM` (`arch/x86/include/asm/elf.h`), with its NUL. -/
def platformString : List Byte := [0x78, 0x38, 0x36, 0x5f, 0x36, 0x34, 0]

/-- The number of auxiliary vector entries, with `AT_NULL`. -/
def auxCount (lb : LinuxBoot) : Nat := if lb.vdso then 23 else 22

/-- Where `execve` puts things on the stack. -/
def stackLayout (a : ExecArgs) (lb : LinuxBoot) (c : ExecChoice) : StackLayout :=
  let strings := c.stackTop - 8 - a.strings.length
  let platform := (strings - c.stackAlign) / 16 * 16
  let items := 1 + (a.argv'.length + 1) + (a.envp.length + 1)
  let sp := (platform - platformString.length - 16 - 16 * auxCount lb - 8 * items) / 16 * 16
  let size := c.stackTop - pageDown strings
  let reserved := c.stackTop - max size (min (a.stackRlimit.cur.toNat / 4096 * 4096) (size + 131072))
  { strings, platform, sp, reserved, start := min reserved (pageDown sp) }

/-- The auxiliary vector as `create_elf_tables` writes it, ending with `AT_NULL`. -/
def auxv (prof : Profile) (hdr : ElfHeader) (phdrAddr : Nat) (a : ExecArgs) (c : ExecChoice)
    (l : StackLayout) : List (Nat × Nat) :=
  let execfn := c.stackTop - 8 - (a.filename.length + 1)
  (if prof.linux.vdso then [(33, c.vdsoText)] else []) ++   -- AT_SYSINFO_EHDR
  [(51, prof.aux.minSigStkSz),            -- AT_MINSIGSTKSZ
   (16, prof.aux.hwcap.toNat),            -- AT_HWCAP
   (6, 4096),                             -- AT_PAGESZ
   (17, 100),                             -- AT_CLKTCK
   (3, phdrAddr),                         -- AT_PHDR
   (4, phdrSize),                         -- AT_PHENT
   (5, hdr.phnum),                        -- AT_PHNUM
   (7, 0),                                -- AT_BASE: no interpreter
   (8, 0),                                -- AT_FLAGS
   (9, hdr.entry),                        -- AT_ENTRY
   (11, a.uid), (12, a.euid), (13, a.gid), (14, a.egid),  -- AT_UID AT_EUID AT_GID AT_EGID
   (23, if a.secure then 1 else 0),       -- AT_SECURE
   (25, l.platform - platformString.length - 16),  -- AT_RANDOM
   (26, prof.aux.hwcap2.toNat),           -- AT_HWCAP2
   (31, execfn),                          -- AT_EXECFN
   (15, l.platform - platformString.length),       -- AT_PLATFORM
   (27, 28),                              -- AT_RSEQ_FEATURE_SIZE
   (28, 32),                              -- AT_RSEQ_ALIGN
   (0, 0)]                                -- AT_NULL

/-- The addresses of the strings `ss` laid out one after another from `x`, each with its NUL. -/
def stringAddrs : Nat → List (List Byte) → List Nat
  | _, [] => []
  | x, s :: ss => x :: stringAddrs (x + s.length + 1) ss

/-- The words from `rsp` up: the argument count, the `argv` pointers and 0, the `envp` pointers
and 0, the auxiliary vector. -/
def stackWords (aux : List (Nat × Nat)) (a : ExecArgs) (l : StackLayout) : List Nat :=
  let ptrs := stringAddrs l.strings (a.argv' ++ a.envp)
  [a.argv'.length] ++ ptrs.take a.argv'.length ++ [0] ++ ptrs.drop a.argv'.length ++ [0] ++
    aux.flatMap fun (t, v) => [t, v]

/-- The byte at address `x` in the runs `rs` (address, bytes), 0 outside them. -/
def runsByte (rs : List (Nat × Array Byte)) (x : Nat) : Byte :=
  match rs.find? fun (a, bs) => a ≤ x ∧ x < a + bs.size with
  | some (a, bs) => bs.getD (x - a) 0
  | none => 0

/-! ## The address space -/

/-- A run of pages that `execve` maps: `count` pages from page number `first`, with protection
`prot` and maximum protection `maxProt`; the `k`-th page has backing `backing k` and maps file page
`origin k` (`Mapping.origin`); `special` for the vDSO and legacy gate mappings (`Mapping.special`), `growsDown` for
the stack's (`Mapping.growsDown`). -/
structure Region where
  /-- The number of the first page. -/
  first : Nat
  /-- The number of pages. -/
  count : Nat
  /-- The pages' protection. -/
  prot : Prot
  /-- The backing of the `k`-th page. -/
  backing : Nat → Backing
  /-- A vDSO or vsyscall mapping (`Mapping.special`). -/
  special : Bool
  /-- The file page the `k`-th page maps, if any (`Mapping.origin`). -/
  origin : Nat → Option FilePage
  /-- The pages' maximum protection (`Mapping.maxProt`). -/
  maxProt : Prot
  /-- The stack's mapping, which grows down (`Mapping.growsDown`). -/
  growsDown : Bool

/-- The legacy vsyscall page in emulate mode: readable, not writable or executable, and special: outside
`TASK_SIZE_MAX`, kept by the kernel as a gate area outside the process's own mappings, so `mmap`,
`mprotect` and `munmap` cannot change it. The other modes map nothing there.
`arch/x86/entry/vsyscall/vsyscall_64.c` (`map_vsyscall`), `arch/x86/include/asm/pgtable_types.h`
(`PAGE_KERNEL_VVAR`); its bytes are `vsyscallFrame`'s. -/
def vsyscallRegions (v : Vsyscall) : List Region :=
  if v = .emulate then
    [⟨vsyscallPage.toNat, 1, ⟨true, false, false⟩, fun _ => .priv vsyscallFrame,
      true, fun _ => none, ⟨true, false, false⟩, false⟩]
  else []

/-- Whether page number `p` is in region `r`. -/
def Region.has (r : Region) (p : Nat) : Bool := r.first ≤ p && p < r.first + r.count

/-- The address space made of regions `rs`, a later region replacing an earlier one where they
overlap (later segments are mapped with `MAP_FIXED`). Each page has a backing of its own, whose
index is the page number, so new mappings start at `2 ^ 52`. Each page is an area of its own (its
page number): the model does not say which of them the kernel made one VMA. -/
def regionsMemory (rs : List Region) (files : Files) (growsDown : List PageNum) : Memory :=
  let at? (p : Nat) := rs.reverse.find? (·.has p)
  { map := fun p => (at? p.toNat).map fun r =>
      ⟨r.prot, p.toNat, 0, r.special, r.origin (p.toNat - r.first), p.toNat, r.maxProt, r.growsDown⟩
    backings := fun i => match at? i with
      | some r => r.backing (i - r.first)
      | none => .priv zeroFrame
    files, growsDown, fresh := 2 ^ 52
    cover := rs.map fun r => (r.first, r.count)
    covers := fun p h => by
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (Option.isSome_map ▸ h)
      have hh := List.find?_some hr
      simp only [Region.has, Bool.and_eq_true, decide_eq_true_eq] at hh
      simp only [inRuns, List.any_map, List.any_eq_true]
      exact ⟨r, List.mem_reverse.1 (List.mem_of_find?_eq_some hr), by simp [hh.1, hh.2]⟩ }

/-- The protection of a segment (`make_prot`; x86 does not adjust it). -/
def Phdr.prot (ph : Phdr) : Prot := ⟨ph.hasFlag 4, ph.hasFlag 2, ph.hasFlag 1⟩

/-- How mapping one segment ends. -/
inductive SegResult
  /-- The segment's regions. -/
  | ok (rs : List Region)
  /-- The kernel kills the new process (`SIGSEGV`; past the point of no return). -/
  | killed
  /-- A case not modelled, named by `what`. -/
  | notModelled (what : String)

/-- The regions of `PT_LOAD` segment `ph` of file `exe` (`elf_load`, `elf_map`, `padzero`, and
the checks after them in `load_elf_binary`), with the initial stack between `stackLo` and
`stackHi`:
- the file pages holding the segment, private mappings of the file's pages from
  `p_offset - (p_vaddr mod 4096)` (which must be a multiple of the page size), when
  `p_filesz > 0`;
- if `p_memsz > p_filesz`, the rest of the last file page zeroed (`padzero`, whose failure is
  ignored for a segment without write permission, so its page keeps the file's bytes), and
  anonymous zero pages up to `p_vaddr + p_memsz`, read-write, and executable if the segment
  is (`vm_brk_flags`).
Every mapping must start at `mmapMinAddr` or above and end within `TASK_SIZE`. A segment with bytes in the file that
is only executable (`PF_X` alone, mapped with `PROT_EXEC`) on a processor with protection keys is not modelled:
`do_mmap` (`mm/mmap.c`) gives such a mapping the execute-only key of `execute_only_pkey`
(`arch/x86/mm/pkeys.c`), which also denies the key's access in the thread's `PKRU`. -/
def segmentRegions (feat : Features) (files : Files) (exe : FileId) (k : KernelConfig)
    (stackLo stackHi : Nat) (ph : Phdr) : SegResult :=
  let pgoff := ph.vaddr % 4096
  let fileStart := pageDown ph.vaddr
  let fileEnd := if ph.filesz = 0 then fileStart else pageUp (ph.vaddr + ph.filesz)
  let zeroStart := if ph.filesz = 0 then fileStart else ph.vaddr + ph.filesz
  let anonStart := if ph.filesz = 0 then fileStart else fileEnd
  let anonEnd := if ph.memsz > ph.filesz then max anonStart (pageUp (ph.vaddr + ph.memsz))
    else anonStart
  let firstPage := (ph.offset - pgoff) / 4096
  let filePage (k : Nat) : FilePage := ⟨exe, firstPage + k⟩
  let lastFile := (zeroStart - fileStart) / 4096
  let padded := ph.filesz > 0 ∧ ph.memsz > ph.filesz ∧ zeroStart % 4096 ≠ 0
  let padFails := files.beyondEof (filePage lastFile)
  let backing (k : Nat) : Backing :=
    if padded ∧ ph.prot.write ∧ k = lastFile then
      .priv fun o => if o.toNat < zeroStart % 4096 then files.page (filePage k) o else 0
    else .cow (filePage k)
  let fileR : Region := ⟨fileStart / 4096, (fileEnd - fileStart) / 4096, ph.prot, backing, false,
    fun k => some (filePage k), ⟨true, true, true⟩, false⟩
  let anonR : Region := ⟨anonStart / 4096, (anonEnd - anonStart) / 4096,
    ⟨true, true, ph.hasFlag 1⟩, fun _ => .priv zeroFrame, false, fun _ => none, ⟨true, true, true⟩, false⟩
  let over (lo hi : Nat) := lo < hi ∧ lo < stackHi ∧ stackLo < hi
  if ph.filesz > 0 ∧ (ph.offset % 4096 ≠ pgoff ∨ fileStart < k.mmapMinAddr ∨
      fileEnd > taskSize feat ∨ ph.offset - pgoff + (fileEnd - fileStart) > 2 ^ 63 - 1) then
    .killed
  else if ph.filesz > 0 ∧ feat.pku ∧ ph.prot = ⟨false, false, true⟩ then
    .notModelled "execute-only ELF segment with protection keys"
  else if over fileStart fileEnd ∨ over anonStart anonEnd then
    .notModelled "ELF segment over the initial stack"
  else if padded ∧ ph.prot.write ∧ padFails then .killed
  else if anonEnd > anonStart ∧ (anonStart < k.mmapMinAddr ∨ anonEnd > taskSize feat) then
    .killed
  else if ph.vaddr ≥ taskSize feat ∨ ph.filesz > ph.memsz ∨ ph.memsz > taskSize feat ∨
      taskSize feat - ph.memsz < ph.vaddr then .killed
  else .ok ([fileR, anonR].filter (·.count > 0))

/-- The regions of all `PT_LOAD` segments, in the order of the program headers. -/
def loadRegions (feat : Features) (files : Files) (exe : FileId) (k : KernelConfig)
    (stackLo stackHi : Nat) : List Phdr → SegResult
  | [] => .ok []
  | ph :: phs =>
    if ph.type ≠ PT_LOAD then loadRegions feat files exe k stackLo stackHi phs
    else match segmentRegions feat files exe k stackLo stackHi ph with
      | .ok rs =>
        match loadRegions feat files exe k stackLo stackHi phs with
        | .ok rs' => .ok (rs ++ rs')
        | r => r
      | r => r

/-- The address of the program header table in memory (`AT_PHDR`): in the last `PT_LOAD`
segment whose file bytes contain `e_phoff`, 0 if there is none. -/
def phdrAddr (hdr : ElfHeader) (phs : List Phdr) : Nat :=
  phs.foldl (fun acc ph =>
    if ph.type = PT_LOAD ∧ ph.offset ≤ hdr.phoff ∧ hdr.phoff < ph.offset + ph.filesz
    then hdr.phoff - ph.offset + ph.vaddr else acc) 0

/-- `PT_GNU_STACK` with `PF_X` (the last such header counts): the stack is executable. -/
def execStack (phs : List Phdr) : Bool :=
  phs.foldl (fun acc ph => if ph.type = PT_GNU_STACK then ph.hasFlag 1 else acc) false

/-- The initial program break: the page after the end of the highest segment
(`load_elf_binary`, before randomization). -/
def brkBase (phs : List Phdr) : Nat :=
  pageUp (phs.foldl (fun acc ph => if ph.type = PT_LOAD then max acc (ph.vaddr + ph.memsz)
    else acc) 0)

/-- The end of the loadable segments' file bytes, `mm->end_data` (`load_elf_binary`). -/
def endData (phs : List Phdr) : Nat :=
  phs.foldl (fun acc ph => if ph.type = PT_LOAD then max acc (ph.vaddr + ph.filesz) else acc) 0

/-- The lowest break `brk` accepts (`mm/mmap.c` `brk`, `min_brk`): the initial break, or with
`CONFIG_COMPAT_BRK` and `brk_randomized` unset the end of the data segment. `execve` sets
`brk_randomized` when it randomizes the break (the break is then not `brkBase`, which a randomized one
never is, `ExecChoice.Valid`); the caller's may be set already (`ExecArgs.brkRandomized`). -/
def brkMin (lb : LinuxBoot) (phs : List Phdr) (a : ExecArgs) (c : ExecChoice) : Nat :=
  if lb.compatBrk ∧ c.brk = brkBase phs ∧ !a.brkRandomized then endData phs else c.brk

/-! ## Memory limits -/

/-- A resource limit's soft value in pages, as `may_expand_vm` compares with it (`rlimit(r) >> PAGE_SHIFT`). -/
def Rlimit.pages (r : Rlimit) : Nat := r.cur.toNat / 4096

/-- Whether `may_expand_vm` (`mm/mmap.c`) lets an area of `n` pages be added to `total` pages of mappings and, for a
private writable area (`data`, `is_data_mapping`: `VM_WRITE` without `VM_SHARED` or `VM_STACK`), to `dataVm` pages of
such areas, under the limits `as` (`RLIMIT_AS`) and `dat` (`RLIMIT_DATA`): the first not above `as`, the second
not above `dat` unless `dat` is 0 and the area fits the hard limit (a workaround the kernel keeps for Valgrind) or
the kernel ignores `RLIMIT_DATA` (`KernelConfig.ignoreRlimitData`). -/
def mayExpand (as dat : Rlimit) (ignoreData : Bool) (total dataVm n : Nat) (data : Bool) : Bool :=
  total + n ≤ as.pages &&
    (!data || dataVm + n ≤ dat.pages || (dat.cur = 0 && dataVm + n ≤ dat.max.toNat / 4096) || ignoreData)

/-- The pages of the half-open page range `[lo, hi)` within the disjoint ranges `iv` (each with whether it is data),
and those of them that are data. -/
def ivOverlap (iv : List (Nat × Nat × Bool)) (lo hi : Nat) : Nat × Nat :=
  iv.foldl (fun (t, d) (l, h, isData) =>
    let o := min h hi - max l lo
    (t + o, if isData then d + o else d)) (0, 0)

/-- The disjoint ranges `iv` without the pages of `[lo, hi)`. -/
def ivRemove (iv : List (Nat × Nat × Bool)) (lo hi : Nat) : List (Nat × Nat × Bool) :=
  iv.flatMap fun (l, h, isData) =>
    (if l < min h lo then [(l, min h lo, isData)] else []) ++ (if max l hi < h then [(max l hi, h, isData)] else [])

/-- The accounting of the segments' areas as `load_elf_binary` maps them, in order, after the stack's `stack` pages
(`total_vm` and `data_vm` as `vm_stat_account` keeps them, `mm/mmap.c`): whether every `may_expand_vm` passes, and
the pages in the end. A file area (`elf_map`: `do_mmap` with `MAP_FIXED`) is checked for its pages less those of
areas it replaces (`__mmap_prepare`, `mm/vma.c`), against the counts before they are removed; an anonymous one (the
segment's zero part, `vm_brk_flags`) after the range is unmapped (`do_vmi_munmap`, then `do_brk_flags`). An area is
data if it is writable (`Region.prot`): every zero part is (`VM_DATA_DEFAULT_FLAGS`), a file area if its segment is. -/
def segmentAccount (as dat : Rlimit) (ignoreData : Bool) (stack : Nat) (segs : List Region) : Bool × Nat × Nat :=
  let step (acc : Bool × List (Nat × Nat × Bool)) (r : Region) : Bool × List (Nat × Nat × Bool) :=
    let (ok, iv) := acc
    let lo := r.first
    let hi := r.first + r.count
    let total := stack + iv.foldl (fun n (l, h, _) => n + (h - l)) 0
    let dataVm := iv.foldl (fun n (l, h, d) => if d then n + (h - l) else n) 0
    let (oT, oD) := ivOverlap iv lo hi
    let fileArea := (r.origin 0).isSome
    let pass := if fileArea then mayExpand as dat ignoreData total dataVm (r.count - oT) r.prot.write
      else mayExpand as dat ignoreData (total - oT) (dataVm - oD) r.count r.prot.write
    (ok && pass, ivRemove iv lo hi ++ [(lo, hi, r.prot.write)])
  let (ok, iv) := segs.foldl step (true, [])
  (ok, stack + iv.foldl (fun n (l, h, _) => n + (h - l)) 0, iv.foldl (fun n (l, h, d) => if d then n + (h - l) else n) 0)

/-! ## `execve` -/

/-- How `execve` ends. -/
inductive ExecResult
  /-- The new program is ready to run its first instruction in state `s`. -/
  | ok (s : State)
  /-- `execve` fails with error `e`; the calling program continues. -/
  | error (e : Nat)
  /-- The calling program is gone and the new one ends before its first instruction (outcome
  `o`): killed by `SIGSEGV` when the kernel fails past the point of no return (`fs/exec.c`
  `bprm_execve`), or something not modelled. -/
  | stopped (o : Outcome)

/-- The new program's return to user mode handles the pending signals that are not blocked
(`get_signal`), all with their default action or ignored, since `execve` removed the handlers: an
ignored one, or one whose default action does nothing or continues, is discarded, as, in a PID
namespace's init (`ProcSignal.unkillable`), every one but `SIGKILL` and `SIGSTOP`; one whose default
action terminates ends the process; one whose default action stops it is not modelled.
`fuel` bounds the signals taken (each takes one pending entry). -/
def execSignals : Nat → State → ExecResult
  | 0, _ => .stopped (.notModelled (.feature "more signals than pending entries"))
  | fuel + 1, s =>
    match nextSignal s with
    | none => .ok s
    | some (q, s₁) =>
      let sig := q.info.signo
      match (s₁.proc.sighand sig).disp with
      | .default =>
        if s₁.proc.signal.unkillable && !kernelOnly sig then execSignals fuel s₁ else
        match defaultAction sig with
        | .term | .core => .stopped (.killed sig q.cause)
        | .stop => .stopped (.notModelled (.feature "a signal that stops the process"))
        | .ign | .cont => execSignals fuel s₁
      | _ => execSignals fuel s₁

/-- The ELF file header and program headers of file `exe` that Linux accepts, if it does
(`load_elf_binary`, `load_elf_phdrs`): the ELF magic number, `e_type` `ET_EXEC` or `ET_DYN`,
`e_machine` x86-64, `e_phentsize` 56, `e_phnum` between 1 and 1170 (the table at most 64 KiB),
and the whole table within the file. -/
def readElf (files : Files) (exe : FileId) : Option (ElfHeader × List Phdr) :=
  let rd := files.byte exe
  let hdr := ElfHeader.read rd
  if elfMagic rd ∧ (hdr.type = ET_EXEC ∨ hdr.type = ET_DYN) ∧ hdr.machine = EM_X86_64 ∧
      hdr.phentsize = phdrSize ∧ 0 < hdr.phnum ∧ phdrSize * hdr.phnum ≤ 65536 ∧
      hdr.phoff + phdrSize * hdr.phnum ≤ files.size exe
  then some (hdr, readPhdrs rd hdr.phoff hdr.phnum) else none

/-- The registers at the first instruction (`start_thread_common`, `ELF_PLAT_INIT`, the FPU
reset of `begin_new_exec`): every general register 0 but `rsp`; `rip` the entry point;
`RFLAGS` with only `IF` (`0x202`); `cs` and `ss` the user selectors, the others 0, the `FS` and
`GS` bases 0; the x87 and vector state at its initial values (`FCW` `0x37f`, `MXCSR` `0x1f80`,
every register empty or zero); `PKRU` the kernel's initial value. -/
def entryCpu (entry sp : Nat) (pkru : BitVec 32) : Cpu :=
  let z : BitVec 64 := 0
  { gpr := ⟨z, z, z, z, BitVec.ofNat 64 sp, z, z, z, z, z, z, z, z, z, z, z⟩
    rip := BitVec.ofNat 64 entry
    rflags := ⟨false, false, false, false, false, false, true, false, false, 0, false, false,
      false, false, false, false, false⟩
    seg := ⟨0x33, 0x2b, 0, 0, 0, 0, 0, 0⟩
    x87 := ⟨fun _ => 0, 0x37f, 0, 0, 0, 0, 0⟩
    vec := ⟨fun _ => 0, fun _ => 0, 0x1f80⟩
    pkru }

/-- `execve` of file `exe` with arguments `a` and kernel choices `c`, on processor `prof`:
- the kernel may fail for its own reasons (`ExecChoice.fail`, `ExecFail`; its first allocation, `getname`'s, comes
  before the next check);
- a caller still over `RLIMIT_NPROC` after a `set*uid` fails (`ExecArgs.nprocOver`, `EAGAIN`);
- the security module may refuse the file's opening (before the strings' checks) or the exec (after them), with its
  error, or a segment's mapping (killed), and a credential transition of its is not modelled (`ExecArgs.lsm`);
- the strings must fit the limits (`E2BIG`), the stack that holds them `RLIMIT_AS` too (it grows a page at a time
  while they are copied, `get_arg_page`; `E2BIG`);
- the file must be an x86-64 ELF executable the loader accepts; past this point (the point of
  no return) a failure kills the new process;
- the memory limits as `may_expand_vm` (`mm/mmap.c`) applies them to the areas mapped (`mayExpand`): the stack grown to
  its first size (`setup_arg_pages`, `RLIMIT_AS`), the segments' file and zero areas in order (`segmentAccount`:
  `RLIMIT_AS`, and `RLIMIT_DATA` for the writable ones), and the stack grown for the words below the strings
  (`create_elf_tables`: `RLIMIT_AS`, counting the vDSO's pages, whose own mapping was not checked against
  any limit);
- under memory-deny-write-execute (`ExecArgs.mdwe`), a segment with file bytes that is writable and executable is
  refused (`mmap_region`, `mm/vma.c`; its zero area, by `vm_brk_flags`, is not checked); with `vm.max_map_count`
  below `4 * n + 2` for `n` loadable segments (each mapping adds at most two areas, one by splitting) the model
  does not count the areas: not modelled;
- the initial stack (`stackLayout`) is set up first, then the segments are mapped
  (`loadRegions`), then the vDSO, and the stack's contents written; where the words below the
  strings do not fit the stack's first mapping (`StackLayout.reserved`), the stack grows down for
  them (`create_elf_tables`, `find_extend_vma_locked`, `expand_downwards`) within `RLIMIT_STACK`
  and not within the guard gap (`prof.linux.stackGuardGap` pages) above an accessible mapping that
  does not grow down, as a fault's growth (`growStack`);
- the executable is write-denied (`Files.denyWrite`) while it runs;
- handled signals revert to their default action, ignored ones stay ignored, both with no flags,
  mask or restorer; the signal mask and pending signals are kept, and the pending signals that are
  not blocked are handled on the way to the first instruction (`execSignals`); descriptors with
  close-on-exec are closed; the alternate signal stack (but its flags), `rseq` registration,
  `clear_child_tid` and the robust list are cleared, and `CPUID`
  faulting is turned off (`arch_setup_new_exec`, `arch/x86/kernel/process.c`); a user shadow
  stack is disabled and freed (`start_thread_common`, `arch/x86/kernel/process_64.c`); the resource
  limits are kept, the stack's as `ExecArgs.stackRlimit`. -/
def execve (prof : Profile) (files : Files) (exe : FileId) (a : ExecArgs) (k : KernelConfig)
    (c : ExecChoice) : ExecResult :=
  let feat := prof.feat
  let as := a.signal.rlimits RLIMIT_AS
  let dat := a.signal.rlimits RLIMIT_DATA
  match c.fail with
  | .early e => .error e
  | _ =>
  if a.nprocOver then .error EAGAIN else
  if a.lsm.refusesOpen then .error a.lsm.err else
  if !a.withinLimits then .error E2BIG else
  let strPages := pageUp (8 + a.strings.length) / 4096
  if 1 < strPages ∧ as.pages < strPages then .error E2BIG else
  if a.lsm.refusesExec then .error a.lsm.err else
  match readElf files exe with
  | none => .stopped (.notModelled (.feature "execve of a file the ELF loader rejects"))
  | some (hdr, phs) =>
    if hdr.type = ET_DYN then .stopped (.notModelled (.feature "ET_DYN executable")) else
    if phs.any (·.type = PT_INTERP) then
      .stopped (.notModelled (.feature "ELF interpreter (PT_INTERP)")) else
    if a.personality &&& MMAP_PAGE_ZERO ≠ 0 then
      .stopped (.notModelled (.feature "MMAP_PAGE_ZERO personality")) else
    if c.fail = .late then .stopped (.killed SIGSEGV .kernel) else
    if a.lsm = .transition then .stopped (.notModelled (.feature "a credential transition of the security module")) else
    let l := stackLayout a prof.linux c
    let stackPages := (c.stackTop - l.reserved) / 4096
    if c.stackTop < k.mmapMinAddr ∨ c.stackTop - pageDown l.strings ≥ c.stackTop - k.mmapMinAddr
    then .stopped (.killed SIGSEGV .kernel) else
    if strPages < stackPages ∧ (as.pages < stackPages ∨ l.reserved < k.mmapMinAddr) then
      .stopped (.killed SIGSEGV .kernel) else
    if l.start < l.reserved ∧ (c.stackTop - l.start > a.stackLimit ∨ l.start < k.mmapMinAddr) then
      .stopped (.killed SIGSEGV .kernel) else
    match loadRegions feat files exe k l.start c.stackTop phs with
    | .killed => .stopped (.killed SIGSEGV .kernel)
    | .notModelled w => .stopped (.notModelled (.feature w))
    | .ok segs =>
      if k.maxMapCount < 4 * (phs.filter (·.type = PT_LOAD)).length + 2 then
        .stopped (.notModelled (.feature "vm.max_map_count near the areas execve maps")) else
      let (segsOk, total, _) := segmentAccount as dat k.ignoreRlimitData stackPages segs
      if !segsOk ∨ (a.mdwe ∧ phs.any fun ph => ph.type = PT_LOAD ∧ ph.filesz > 0 ∧ ph.prot.write ∧ ph.prot.exec) ∨
        a.lsm = .mapping
      then .stopped (.killed SIGSEGV .kernel) else
      if hdr.entry ≥ taskSize feat then .stopped (.killed SIGSEGV .kernel) else
      let vdsoPages := if prof.linux.vdso then 6 + prof.linux.vdsoText.length else 0
      if l.start < l.reserved ∧ as.pages < total + vdsoPages + (l.reserved - l.start) / 4096 then
        .stopped (.killed SIGSEGV .kernel) else
      let aux := auxv prof hdr (phdrAddr hdr phs) a c l
      let random := l.platform - platformString.length - 16
      let runs := [(l.sp, (wordBytes (stackWords aux a l)).toArray),
        (random, (toBytesLE c.random 16 ++ platformString).toArray), (l.strings, a.strings.toArray)]
      let stack : Region := ⟨l.start / 4096, (c.stackTop - l.start) / 4096,
        ⟨true, true, execStack phs⟩,
        fun k => .priv fun o => runsByte runs (l.start + 4096 * k + o.toNat), false, fun _ => none,
        ⟨true, true, true⟩, true⟩
      let data (i : Nat) : Backing :=
        let j := Fin.ofNat 6 i
        .kernel (if prof.linux.vdsoData j then some (c.vdsoData j) else none)
      let vdso : List Region := if prof.linux.vdso then
          [⟨c.vdsoBase / 4096, 6, ⟨true, false, false⟩, data, true, fun _ => none, ⟨true, false, false⟩, false⟩,
           ⟨c.vdsoText / 4096, prof.linux.vdsoText.length, ⟨true, false, true⟩,
            fun i => .priv (prof.linux.vdsoText.getD i zeroFrame), true, fun _ => none, ⟨true, true, true⟩, false⟩]
        else []
      let files' := { files with denyWrite := fun f => decide (f = exe) || files.denyWrite f }
      let mem := regionsMemory (vsyscallRegions prof.linux.vsyscall ++ (stack :: segs ++ vdso)) files' [BitVec.ofNat 52 (l.start / 4096)]
      if l.start < l.reserved ∧ (mem.prevMapped (l.start / 4096) prof.linux.stackGuardGap).any
          (fun mp => !mp.growsDown && mp.accessible) then .stopped (.killed SIGSEGV .kernel) else
      let s : State :=
        { proc := { mm := { mem
                            brkMin := BitVec.ofNat 64 (brkMin prof.linux phs a c)
                            brk := BitVec.ofNat 64 c.brk }
                    files := fun n => match a.files n with
                      | some ⟨f, false⟩ => some ⟨f, false⟩
                      | _ => none
                    fdMax := a.fdMax
                    opens := { pos := a.filePos, next := c.nextOpen }
                    sighand := fun sig => match a.sighand sig with
                      | .ignore => { SigAction.dfl with disp := .ignore }
                      | _ => SigAction.dfl
                    signal := { pending := a.signal.pending
                                rlimits := fun r => if r = RLIMIT_STACK then a.stackRlimit else a.signal.rlimits r
                                unkillable := a.signal.unkillable } }
          cpu := entryCpu hdr.entry l.sp k.initPkru
          thread := { tid := a.tid, sigmask := a.sigmask, pending := a.threadPending,
                      altStack := ⟨0, 0, a.altStackFlags⟩, rseq := none, clearChildTid := 0,
                      robustList := 0, cpuidFaults := false, tscFaults := a.tscFaults, shstk := none,
                      uid := a.uid } }
      execSignals (a.signal.pending.length + a.threadPending.length + 1) s

/-! ## The kernel's choices -/

/-- The lowest `mmap_base` of a 64-bit process (`arch/x86/mm/mmap.c` `mmap_base`, `arch_pick_mmap_layout`): the top of
the area that top-down `mmap` placement searches (`arch_get_unmapped_area_topdown`) is
`PAGE_ALIGN(task_size - gap - rnd)`, with `task_size` `DEFAULT_MAP_WINDOW` (`stackTopMax`, also with 5-level paging:
`task_size_64bit(0)`), `gap` the stack's limit plus its randomization and guard gap clamped to at most
`task_size / 6 * 5`, and `rnd` fewer than `2 ^ mmap_rnd_bits` random pages (`arch_rnd`), `vm.mmap_rnd_bits` at most
`CONFIG_ARCH_MMAP_RND_BITS_MAX`, 32 for a 64-bit kernel (`arch/x86/Kconfig`, a value no configuration option
changes; `mm/mmap.c` `mmap_rnd_bits_max`). About 5.3 TiB. The legacy layout's base, `TASK_UNMAPPED_BASE` plus `rnd`
(`mmap_legacy_base`; `task_size / 3` rounded up to a page, `arch/x86/include/asm/processor.h`), is higher. -/
def mmapBaseMin : Nat := stackTopMax - stackTopMax / 6 * 5 - (2 ^ 32 - 1) * 4096

/-- How low the vDSO of a process started with arguments `a`, at the choices `c`, may lie unless it lies below a
loadable segment (`ExecChoice.VdsoPlace.floor`): its length and 2 MiB below the lower of `mmapBaseMin` and the start
of the stack's guard gap (`vm_start_gap`: `prof.linux.stackGuardGap` pages below the stack's mapping as
`setup_arg_pages` made it, `StackLayout.reserved`; 0 if the gap would reach below address 0). The 2 MiB: where the
vDSO's length is a multiple of 2 MiB, `__get_unmapped_area` searches for that length and 2 MiB more and places the
vDSO within the range found (`thp_get_unmapped_area_vmflags`, `mm/huge_memory.c` `__thp_get_unmapped_area`). -/
def ExecChoice.vdsoFloor (lb : LinuxBoot) (a : ExecArgs) (c : ExecChoice) : Nat :=
  min mmapBaseMin ((stackLayout a lb c).reserved - 4096 * lb.stackGuardGap) - (c.vdsoEnd lb.vdsoText - c.vdsoBase) -
    2 ^ 21

/-- Where the kernel can map the vDSO (`arch/x86/entry/vdso/vma.c` `map_vdso`: `get_unmapped_area` without a hint, for
its six data pages and its image, after the stack and the segments are mapped and before the break is set,
`fs/binfmt_elf.c` `load_elf_binary`; `mm/mmap.c` `__get_unmapped_area`, `arch/x86/kernel/sys_x86_64.c`, `mm/vma.c`
`unmapped_area_topdown`, `unmapped_area`; where the length is a multiple of 2 MiB, `mm/huge_memory.c`
`__thp_get_unmapped_area`: the same search for 2 MiB more, the vDSO within the range found). In the default top-down layout (`MMF_TOPDOWN`) the kernel takes the highest
free range below `mmap_base` and below the stack's guard gap (`vm_start_gap`), above `mmap_min_addr`; if there is none,
or in the legacy layout (the personality's `ADDR_COMPAT_LAYOUT` or `vm.legacy_va_layout`, `mmap_is_legacy`), the
lowest free range at or above the legacy base (`mmap_legacy_base`, at least `task_size / 3`), below
`DEFAULT_MAP_WINDOW`, skipping the stack where the range would reach into its guard gap. So the vDSO:
- `aligned`, `low`, `high`: is page-aligned, at or above `mmap_min_addr`, and ends at or below `DEFAULT_MAP_WINDOW`;
- `stack`: lies below the initial stack, or above it (where the bottom-up search skipped it: only when loadable
  segments fill what lies between the legacy base and the stack, or the stack's guard gap reaches below that base);
- `segs`: lies apart from every loadable segment;
- `floor`: lies at or above `ExecChoice.vdsoFloor` (within its length and 2 MiB of the top of its range in the top-down
  search, or anywhere in the bottom-up one, above the legacy base), or below a loadable segment (where a segment took the top of that range), so
  a program whose segments end far enough below `mmapBaseMin` and whose stack's guard gap does too has its vDSO far
  above its break's range.

Below the stack, it lies below the stack as `create_elf_tables` grew it for its words (`StackLayout.start`): `mmap_base`
leaves room for the stack to grow to `RLIMIT_STACK` and a guard gap of at least a page, and growing further kills the
process (`execve`). Not admitted: with `stack_guard_gap=0` on the
command line, or with segments filling the space below the stack, a vDSO in the pages the stack is then grown into,
where the kernel kills the new process. -/
structure ExecChoice.VdsoPlace (lb : LinuxBoot) (phs : List Phdr) (a : ExecArgs) (k : KernelConfig)
    (c : ExecChoice) : Prop where
  aligned : c.vdsoBase % 4096 = 0
  low : k.mmapMinAddr ≤ c.vdsoBase
  high : c.vdsoEnd lb.vdsoText ≤ stackTopMax
  stack : c.vdsoEnd lb.vdsoText ≤ (stackLayout a lb c).start ∨ c.stackTop ≤ c.vdsoBase
  segs : ∀ ph ∈ phs, ph.type = PT_LOAD →
    c.vdsoEnd lb.vdsoText ≤ pageDown ph.vaddr ∨ pageUp (ph.vaddr + ph.memsz) ≤ c.vdsoBase
  floor : c.vdsoFloor lb a ≤ c.vdsoBase ∨
    ∃ ph ∈ phs, ph.type = PT_LOAD ∧ c.vdsoEnd lb.vdsoText ≤ pageDown ph.vaddr

/-- The choices the kernel can make for a new process of the static ELF with program headers
`phs` and arguments `a`, for every setting of `randomize_va_space` and the personality's
`ADDR_NO_RANDOMIZE`:
- the stack's end is `STACK_TOP` minus fewer than `2 ^ 22` random pages and 0 or 1 more page
  (`randomize_stack_top`, `arch_align_stack` in `setup_arg_pages`);
- fewer than 8192 bytes are left below the strings (`arch_align_stack` in `create_elf_tables`);
- the program break is the page after the highest segment, or with randomization one page more
  plus fewer than `2 ^ 30` bytes in whole pages (`arch_randomize_brk`, `randomize_page`);
- the vDSO, if mapped, where `get_unmapped_area` can put it (`ExecChoice.VdsoPlace`);
- the identities of the descriptions the program creates start above those of every description it is
  passed (each is a new `struct file`);
- an error the kernel may return for its own reasons is an error number (`ExecFail.early`: `ENOMEM`, `EINTR`,
  ..., all below 4096, `MAX_ERRNO`). -/
structure ExecChoice.Valid (lb : LinuxBoot) (phs : List Phdr) (a : ExecArgs) (k : KernelConfig)
    (c : ExecChoice) : Prop where
  stackTop : c.stackTop % 4096 = 0 ∧ stackTopMax - 2 ^ 22 * 4096 ≤ c.stackTop ∧
    c.stackTop ≤ stackTopMax
  stackAlign : c.stackAlign < 8192
  brk : c.brk % 4096 = 0 ∧ brkBase phs ≤ c.brk ∧ c.brk < brkBase phs + 4096 + 2 ^ 30
  vdso : lb.vdso = true → c.VdsoPlace lb phs a k
  nextOpen : ∀ n e, a.files n = some e → e.file.id < c.nextOpen
  fail : ∀ e, c.fail = .early e → 0 < e ∧ e < 4096

end ZellicX86
