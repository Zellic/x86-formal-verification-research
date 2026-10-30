import ZellicX86.Spec.State
/-!
# Choices as requests

Everything the architecture and Linux leave open is a **request** the semantics issues and
someone else answers: values the manuals call undefined, what happens between two
instructions (the kernel running, other processes), and the results of system calls within
what the kernel may return. The semantics is a program over requests (`Req`); who answers is
a separate choice:

- `Req.runStream`: an arbitrary stream of answers, indexed by a counter. Theorems that hold
  for all streams hold for every behaviour of the machine and its environment (every
  history-dependent chooser produces some stream).
- Any other interpretation, e.g. answers sampled from a distribution or given by an
  adversary strategy, runs the same program in another monad (`Req.interp`).
-/
namespace ZellicX86

/-- A tracer (`ptrace(2)`) writes a register of the stopped thread (`PTRACE_POKEUSER`,
`PTRACE_SETREGS`, `PTRACE_SETFPREGS`, `PTRACE_SETREGSET`; `arch/x86/kernel/ptrace.c`
`putreg`). A request that writes several registers is several events: the kernel writes them
one at a time and stops at the first it rejects. A write of `orig_rax` between instructions
has no effect and is no event. -/
inductive TracerWrite
  /-- General register `r` gets `v`. -/
  | gpr (r : Reg) (v : BitVec 64)
  /-- `rip` gets `v`. -/
  | rip (v : Addr)
  /-- `RFLAGS` gets the bits CF, PF, AF, ZF, SF, TF, DF, OF, NT, RF and AC of `v`; the others
  keep their values (`set_flags`, `FLAG_MASK`). -/
  | rflags (v : BitVec 64)
  /-- The `GS` base (`gs = true`) or the `FS` base gets `v`; rejected, with no effect, unless
  `v` is below `TASK_SIZE_MAX`. -/
  | segBase (gs : Bool) (v : Addr)
  /-- A segment selector (`set_segment_reg`). -/
  | selector
  /-- A debug register (`ptrace_set_debugreg`). -/
  | debug
  /-- The x87, SSE, AVX or `PKRU` state (`fpregs_set`, `xstateregs_set`). -/
  | fpu

/-- Something that may happen between two instructions of the process. -/
inductive EnvEvent
  /-- The kernel ran (interrupt, preemption, migration) and returned to user mode on CPU
  `cpu`, NUMA node `node`, with memory-map concurrency id `mmCid`. With an `rseq` area
  registered, the kernel writes these ids into it (`kernel/rseq.c`
  `__rseq_handle_notify_resume`). The CPU and the concurrency id are the machine's
  (`EnvEvent.OnCpus`). -/
  | kernelEntry (cpu node mmCid : BitVec 32)
  /-- Another process, or the kernel on its behalf, sends signal `sig` to the process. -/
  | signal (sig : Signal)
  /-- The kernel rewrites a backing it owns (a vDSO data page); affects only `kernel`
  backings that have a source. -/
  | kernelData (backing : Nat) (f : Frame)
  /-- Another agent changes the contents of a file page (`write(2)` by another process, a
  shared mapping elsewhere). No effect on a file whose writing is denied
  (`Files.denyWrite`). -/
  | fileWrite (fp : FilePage) (f : Frame)
  /-- Another agent changes a file's size (`truncate(2)`, appending writes); the process's private
  copies of the file's pages beyond the new end are dropped (`Memory.truncate`). -/
  | fileSize (file : FileId) (size : Nat)
  /-- Another process sharing the open file description `f` (inherited across `fork(2)`, passed by
  `SCM_RIGHTS`) moves its position or changes its status flags (`O_APPEND`, `FilePos.flags`), to `p`: by
  `read(2)`, `write(2)` or `lseek(2)` through its own descriptor, or `fcntl(F_SETFL)`. -/
  | filePos (f : OpenFile) (p : FilePos)
  /-- The kernel makes the private copy of a private file mapping's page before the process
  writes it: a page pinned for writing gets its copy then (`mm/gup.c` `faultin_page` with
  `FOLL_WRITE`), as for `ptrace(2)` and `/proc/PID/mem` writes and `process_vm_writev(2)` by
  another process, or `mlock(2)` and `MAP_POPULATE` (`populate_vma_page_range`). Affects only
  `cow` backings. -/
  | cowBreak (backing : Nat)
  /-- Another process writes `bytes` at `addr` into the process's memory through the kernel,
  which it may with ptrace access to the process: `process_vm_writev(2)` (`force = false`),
  `ptrace(2)` `PTRACE_POKEDATA` or a write to `/proc/PID/mem` (`force = true`: `FOLL_FORCE`,
  for `/proc/PID/mem` as the kernel's `proc_mem.force_override` allows). A write that fails
  part way has written a prefix of `bytes`: the event for that prefix. -/
  | remoteWrite (addr : Addr) (bytes : List Byte) (force : Bool)
  /-- A tracer reads `len` bytes at `addr` of the process's memory through the kernel (`ptrace(2)`
  `PTRACE_PEEKDATA`, a read of `/proc/PID/mem`). The process sees nothing of it, but the kernel may
  grow a stack for it (`__access_remote_vm`). (`process_vm_readv(2)` grows nothing and changes
  nothing: no event.) -/
  | remoteRead (addr : Addr) (len : Nat)
  /-- A tracer writes a register of the thread. -/
  | tracer (w : TracerWrite)
  /-- Another process sets resource limit `res` of the process to `lim` (`prlimit(2)`, with the
  permission `check_prlimit_permission` asks for). No effect if the soft limit exceeds the hard
  one, which the kernel refuses (`kernel/sys.c` `do_prlimit`). -/
  | rlimit (res : Fin 16) (lim : Rlimit)
  /-- The kernel drops a lazily freed page (`Backing.freed`, after `madvise(MADV_FREE)`) to reclaim
  memory (`mm/vmscan.c` `shrink_folio_list`, also at `madvise(MADV_PAGEOUT)`): it reads zeros
  afterwards. Affects only `freed` backings. -/
  | reclaim (backing : Nat)

/-- Whether event `e` can happen on a machine with `cpus` CPUs (`Profile.cpus`, one if 0): a kernel entry's
CPU is one of the machine's (`raw_smp_processor_id`, below `nr_cpu_ids`), and its concurrency id one of
those below the CPUs the process may run on (`mm_cid_get`, `__mm_cid_try_get`,
`kernel/sched/sched.h`). -/
def EnvEvent.OnCpus (cpus : Nat) : EnvEvent → Prop
  | .kernelEntry cpu _ mmCid => cpu.toNat < max cpus 1 ∧ mmCid.toNat < max cpus 1
  | _ => True

/-- A Linux error number, 1 to 4095 (`include/linux/err.h`, `MAX_ERRNO`). -/
abbrev Errno := { e : Nat // 0 < e ∧ e < 4096 }

/-- What `read` of up to `n` bytes returns: some bytes (at most `n`; none means end of
file), or an error. -/
inductive ReadResult (n : Nat)
  | data (bs : List Byte) (h : bs.length ≤ n)
  | error (e : Errno)

/-- What `write` of `n` bytes returns: the number of bytes written (at most `n`), an error,
a broken pipe (`EPIPE`, with `SIGPIPE` sent to the process, `fs/pipe.c` `pipe_write`), or a
file whose write position is at or beyond a size limit (`EFBIG`): the process's file size limit, with
`SIGXFSZ` sent to the process when it is not infinite (`fs/read_write.c` `generic_write_check_limits`),
or the file system's, without a signal; for a regular file with pages the model checks the process's
limit itself (`fsizeLimit`), and the answer is the file system's. -/
inductive WriteResult (n : Nat)
  | wrote (k : Nat) (h : k ≤ n)
  | error (e : Errno)
  | brokenPipe
  | fileTooBig

/-- The path of a process's executable file, the file `execve` opened (`mm->exe_file`), as the kernel names it now
(`d_path`, `fs/d_path.c`): the names of the directories down to the file and the file's own name (`names`, none for a
lone `/`), normally from the process's root directory, but any `/`-path the kernel's walk gives (`__prepend_path` climbs
past a `chroot`'s root to the namespace's, and gives a lone `/` for a path that escaped it), and whether the file has
been unlinked (`deleted`, `d_unlinked`). `names` admits more than the kernel writes (empty names, names with `/` or
NUL): more answers than Linux gives, never fewer.
A file of a file system that names its files itself (`d_dname`) has one name: a memfd's is `memfd:NAME`, unlinked
(`simple_dname`, `fs/d_path.c`; every other `d_dname` of Linux v6.18 belongs to a file system whose files `execve`
refuses: sockets, pipes, namespaces, anonymous inodes, `pidfs`). The model has no file system, so the names are the
environment's; they may change between two calls (a rename). -/
structure ExePath where
  names : List (List Byte)
  deleted : Bool

/-- What the file system answers to `readlink` of a path: the link's contents (`target`), procfs's `exe` link of a
process (`procExe`), or an error (no such file, not a link, permission denied, ...). The `exe` link's contents are
not the file system's but the kernel's: the path of that process's executable (`proc_exe_link`, `proc_pid_readlink`,
`fs/proc/base.c`), which the model writes itself (`ExePath.bytes`, `sysReadlinkat`). Which path names such a link
(where procfs is mounted, which process `self` names) is the file system's, as every lookup. -/
inductive LinkResult
  | target (bs : List Byte)
  | procExe (p : ExePath)
  | error (e : Errno)

/-- A file's status (`struct stat`, `arch/x86/include/uapi/asm/stat.h`; `stat(2)`). -/
structure Stat where
  dev : BitVec 64
  ino : BitVec 64
  nlink : BitVec 64
  /-- The file type and permission bits (`S_IFMT`, `S_IFREG`, `S_IFCHR`, `S_IFIFO`, ...). -/
  mode : BitVec 32
  uid : BitVec 32
  gid : BitVec 32
  /-- The device a device file stands for. -/
  rdev : BitVec 64
  size : BitVec 64
  /-- The preferred block size for I/O. -/
  blksize : BitVec 64
  /-- The number of 512-byte blocks allocated. -/
  blocks : BitVec 64
  atime : BitVec 64
  atimeNsec : BitVec 64
  mtime : BitVec 64
  mtimeNsec : BitVec 64
  ctime : BitVec 64
  ctimeNsec : BitVec 64

/-- What `fstat` of an open file finds: its status, or an error (`EIO`, the security module). -/
inductive StatResult
  | ok (st : Stat)
  | error (e : Errno)

/-- What a device or file system answers to an `ioctl` that delivers `n` bytes: the bytes, or an
error (`ENOTTY`: the file does not understand the command). -/
inductive IoctlResult (n : Nat)
  | ok (bs : List Byte) (h : bs.length = n)
  | error (e : Errno)

/-- What `mmap` of a file finds about it that may change while the process runs (by a remount, a
change of the inode's attributes, `swapon(2)`, `fcntl(F_ADD_SEALS)`): `mm/mmap.c` `do_mmap`. -/
structure FileAttrs where
  /-- The file's mount is `noexec` (`path_noexec`): `PROT_EXEC` is refused, and the mapping may
  not become executable. -/
  noexec : Bool
  /-- The inode is append-only (`IS_APPEND`, `chattr +a`): a shared mapping through a descriptor
  open for writing is refused. -/
  append : Bool
  /-- The file is an active swap file (`IS_SWAPFILE`): a shared writable mapping is refused. -/
  swap : Bool
  /-- The file is a memfd with a write seal (`F_SEAL_WRITE` or `F_SEAL_FUTURE_WRITE`,
  `mm/memfd.c` `check_write_seal`): a shared writable mapping is refused, a shared read-only one may
  not become writable. -/
  writeSealed : Bool

/-- What the file system answers to opening a path (`fs/namei.c` `do_filp_open`): a new open file
description, given by what a mapping of it maps (`FileMap`: the pages of a file for a regular file, say;
its identity is the process's next, `OpenTable.next`), or an error (no such file `ENOENT`, a
permission `EACCES`, a component not a directory `ENOTDIR`, a directory opened for writing `EISDIR`,
the system's or the descriptor limits `ENFILE`, `EMFILE`, lack of memory `ENOMEM`, the security
module, …). -/
inductive OpenResult
  | opened (map : FileMap)
  | error (e : Errno)

/-- A time as a clock gives it (`struct timespec64`, `include/linux/time64.h`): seconds, signed,
and nanoseconds below a second. -/
structure Timespec where
  sec : BitVec 64
  nsec : Fin 1000000000

/-- A request. -/
inductive Request
  /-- A `w`-bit value the processor manuals leave undefined. -/
  | undefined (w : Nat)
  /-- One of `n + 1` alternatives the processor or the kernel may take (e.g. which of two faulting
  pages of an access the processor reports, how many bytes a faulting copy to user memory wrote). -/
  | pick (n : Nat)
  /-- What happens before the next instruction, on a machine with `cpus` CPUs: a list of environment
  events, in order, each one that can happen there (`EnvEvent.OnCpus`). -/
  | between (cpus : Nat)
  /-- The result of `read` of up to `n` bytes from the open file with identity `file`, which is not a
  file with pages (`FileMap.pages`). -/
  | read (file : Nat) (n : Nat)
  /-- Whether a `read` of the next `n` bytes of the file with pages (`FileMap.pages`) that the open
  file with identity `file` is on fails, and how: `none`, it delivers all `n`; `some (e, k)`, it fails
  with error `e` after the first `k` (`mm/filemap.c` `filemap_read`: the page cache cannot be allocated,
  `ENOMEM`; a page cannot be read from the storage, `EIO`; a fatal signal, `EINTR`), or before any byte
  (`fs/read_write.c` `rw_verify_area`: the security module's `security_file_permission`, a fanotify
  permission listener). -/
  | readFail (file : Nat) (n : Nat)
  /-- The result of `write` of `bytes` to the open file with identity `file`. -/
  | write (file : Nat) (bytes : List Byte)
  /-- Whether a `write` to the open file with identity `file`, a regular file with pages, fails before the
  kernel checks the file size limit, and with which error: the security module and a fanotify permission
  listener (`fs/read_write.c` `rw_verify_area`), and the file system's own checks before it
  (`ext4_file_write_iter` on a file system that was shut down, `EIO`). Asked where the write position is
  at or past the limit (`fsizeLimit`). -/
  | writeRefused (file : Nat)
  /-- The result of a `write` of `n` bytes to the open file with identity `file`, which is not a file
  with pages (`FileMap.pages`), from a buffer of which the kernel can read only the first bytes,
  `bytes`, fewer than `n`: what such a file does with them is its own (a pipe takes whole pages of
  the buffer and fails with `EFAULT` when it took none, `fs/pipe.c` `anon_pipe_write`; `/dev/null`
  reads nothing and returns `n`, `drivers/char/mem.c` `write_null`), so the answer is any count up
  to `n`, of which the first `bytes` are the bytes taken, or an error. -/
  | writeFault (file : Nat) (bytes : List Byte) (n : Nat)
  /-- What `mmap` finds about the open file with identity `file` (`FileAttrs`). -/
  | fileAttrs (file : Nat)
  /-- Where the kernel places a new mapping of `len` bytes whose address the caller left to it
  (`get_unmapped_area`): an address. Which free range it picks depends on randomization, the
  hint, the mapping's alignment and the layout (`arch/x86/kernel/sys_x86_64.c`); the system call
  checks that the answer is a range the kernel may pick (`sysMmap`). -/
  | place (len : Nat)
  /-- Whether a system call that changes the layout over `pages` pages fails for a reason the
  model does not track, and how: `none`, it goes on; `some (e, k)`, it fails with error `e` after
  its change was made to the first `k` pages. Such failures are always possible: lack of memory
  and its accounting (`ENOMEM`), `vm.max_map_count`, limits another process may lower at any time
  (`RLIMIT_AS`, `RLIMIT_DATA`, `RLIMIT_MEMLOCK` by `prlimit(2)`), `vm.mmap_min_addr` (`EPERM`),
  and the security module's policy (`EACCES`, `EPERM`). -/
  | memFail (pages : Nat)
  /-- Whether the kernel refuses to grow a stack for a reason the model does not track
  (`mm/vma.c` `acct_stack_growth`, `expand_downwards`; `true` to refuse): the address space limit
  (`RLIMIT_AS` against the pages of every VMA), the locked-memory limit of a stack that is locked
  (`RLIMIT_MEMLOCK`), the overcommit policy (`security_vm_enough_memory_mm`), `vm.mmap_min_addr`,
  which another agent may change at any time, and memory for the kernel's own structures. -/
  | growFail
  /-- The time-stamp counter as `RDTSC` reads it (SDM Vol. 3B, 20.17 "Time-Stamp Counter"): a
  value of the CPU the thread runs on, which software with privilege (the kernel, a hypervisor)
  may write and which need not agree between CPUs, so nothing about it is built in: monotonicity
  holds only on some machines (an invariant TSC, never written), and is for a statement to
  assume. -/
  | tsc
  /-- The in-use bitmap that `XGETBV` with `ECX = 1` reads, or that a Linux signal frame saves, with every bit of
  `required` set. The caller computes `required` from the state (`Cpu.xInuseRequired`): the bits of the components
  `Cpu.xInit` does not find in their initial configuration, and SSE's where `MXCSR` is not its initial value; a
  component in its initial configuration may read either way (SDM Vol. 1, 13.6; APM Vol. 3, `XGETBV` and `XSAVEC`).
  The caller masks the answer to the components it reads or saves. -/
  | xinuse (required : BitVec 64)
  /-- How `getrandom` for a buffer of `n` bytes goes: the number of bytes it returns, at most `n`
  (fewer when a signal is pending while it fills a large buffer), or its error (`EAGAIN` before the
  kernel's generator is initialized under `GRND_NONBLOCK`, `EINTR` while waiting for it;
  `drivers/char/random.c` `getrandom`). Separate from the bytes (`randomBytes`), so that an
  interpretation can choose the bytes uniformly whoever chooses this. -/
  | randomCount (n : Nat)
  /-- The `k` random bytes `getrandom` returns. -/
  | randomBytes (k : Nat)
  /-- The contents of the symbolic link at `path` (without its NUL), looked up from the working
  directory (`dir = none`; also for an absolute path) or from the directory open as the file with
  identity `dir`: `readlink(2)`. -/
  | readlink (dir : Option Nat) (path : List Byte)
  /-- The status of the open file with identity `file`: `fstat(2)`. For a regular file with pages the
  model replaces its size and type by the file's (`statOf`). -/
  | stat (file : Nat)
  /-- What opening `path` with the flags `flags` (`open(2)`) gives, looked up from the working
  directory (`dir = none`; also for an absolute path) or from the directory open as the file with
  identity `dir`: how the path resolves is the file system's, which the model does not have. -/
  | openAt (dir : Option Nat) (path : List Byte) (flags : Nat)
  /-- Whether `lseek` may put the position of the open file with identity `file`, which is on the pages
  of a file (`FileMap.pages`), at `pos`, past the file's end: up to the largest file of its file system,
  for a regular file far past its size (`fs/read_write.c` `vfs_setpos` against `s_maxbytes`;
  `ext4_llseek`, `shmem_file_llseek`), for a block device not past its size (`block/fops.c`
  `blkdev_llseek`, `fixed_size_llseek`). -/
  | seekPast (file : Nat) (pos : Nat)
  /-- The new position `lseek(fd, offset, whence)` gives the open file with identity `file`, which is not
  on the pages of a file, or its error: such a file's own (`file->f_op->llseek`; a pipe or socket has
  no position, `ESPIPE`). -/
  | seek (file : Nat) (offset : Int) (whence : Nat)
  /-- The `n` bytes the open file with identity `file` delivers for `ioctl` command `cmd`, or its
  error. -/
  | ioctlGet (file : Nat) (cmd : Nat) (n : Nat)
  /-- What the file's `flush` operation returns when `close(2)` drops a descriptor on the open file with
  identity `file` (`fs/open.c` `filp_flush`): `none` for success, or its error. Network and FUSE file
  systems write back and report a failure there (`nfs_file_flush`, `fuse_flush`); most files have no
  `flush` and always succeed, but which file system a file is on is not modelled. -/
  | close (file : Nat)
  /-- How the descriptor table grows to hold descriptor `fd`, at or above its size (`Proc.fdMax`;
  `fs/file.c` `expand_files`, `expand_fdtable`, `alloc_fdtable`): to a new size above `fd`, which is
  `fd + 1` rounded up to a power of two unless the `fs.nr_open` setting is lower (then that setting rounded
  down to a multiple of 64); or not, with `EMFILE` when the setting is at or below `fd`, or `ENOMEM` when
  memory for the larger table cannot be allocated. The setting, which an administrator may change at any
  time, is not modelled. -/
  | fdGrow (fd : Nat)
  /-- Whether the kernel refuses `fcntl(2)` command `cmd` with argument `arg` on the open file with
  identity `file` for a reason the model does not track, and with which error: the security module
  (`security_file_fcntl`, for every command); for `F_SETFL` (`fs/fcntl.c` `setfl`), clearing `O_APPEND`
  of an append-only file (`EPERM`), setting `O_NOATIME` without owning the file (`EPERM`), `O_DIRECT` on a
  file that does not support it (`EINVAL`), and the file's own check (`check_flags`). -/
  | fcntl (file : Nat) (cmd : Nat) (arg : Nat)
  /-- Whether the open file with identity `file`, which is not on the pages of a file, takes reads
  (`write = false`) or writes (`write = true`) at an offset (`FMODE_PREAD`, `FMODE_PWRITE`, which
  `fs/open.c` `do_dentry_open` sets and `nonseekable_open` and `stream_open` clear: pipes and sockets do
  not, `ESPIPE`; `fs/seq_file.c` `seq_open` clears `FMODE_PWRITE` alone). -/
  | positional (file : Nat) (write : Bool)
  /-- The CPU, NUMA node and memory-map concurrency id (`mm_cid`) the thread returns to user mode
  with, when the kernel must write them into its `rseq` area at once (`rseq_set_notify_resume`), on a
  machine with `cpus` CPUs: ids a kernel entry there can have (`EnvEvent.OnCpus`). -/
  | resumeIds (cpus : Nat)
  /-- Whether the kernel refuses to set the process's resource limit `res` to `lim`, and with which
  error (`kernel/sys.c` `do_prlimit`): raising the hard limit needs `CAP_SYS_RESOURCE` (`EPERM`),
  the descriptor limit's hard limit may not exceed the `fs.nr_open` setting (`EPERM`), and the
  security module may refuse any change. The process's credentials and the settings are not
  modelled, so every change may be refused. -/
  | setRlimit (res : Fin 16) (lim : Rlimit)
  /-- Whether the kernel could allocate the queue entry for a signal `sig` it sends
  (`sigqueue_alloc`, `kernel/signal.c`): it may not for want of memory, and a signal a process sends
  counts against `RLIMIT_SIGPENDING` of its user, over all the user's processes, which the model
  does not see. Without an entry the signal is still pending, with the information of
  `SigInfo.lost` (`collect_signal`). -/
  | queued (sig : Signal)
  /-- The `PKRU` value the kernel gives a thread entering a signal handler (`init_pkru_value`,
  `arch/x86/mm/pkeys.c`): the `init_pkru=` boot option, which an administrator may change at any
  time through debugfs. It allows access to key 0: the debugfs file refuses a value that does not
  (`init_pkru_write_file`), and with protection keys enabled no program starts under such a boot value
  (`KernelConfig.Valid`). -/
  | initPkru
  /-- What the clock with id `id` reads (`kernel/time/posix-timers.c` `clock_gettime`, `posix_clocks`):
  the wall clock (`CLOCK_REALTIME`, 0), which an administrator or `adjtimex` may set or slew at any
  time, the monotonic and boot clocks, the process's and the thread's CPU time, and their coarse and raw
  variants. Nothing relates two readings, even of one clock: an assumption about them (a monotonic
  clock does not go back) is for a statement to make. -/
  | clock (id : Nat)
  /-- Whether the machine has a real-time clock with alarms, which the alarm clocks need
  (`CLOCK_REALTIME_ALARM`, `CLOCK_BOOTTIME_ALARM`; `kernel/time/alarmtimer.c`
  `alarm_clock_get_timespec`, `alarmtimer_get_rtcdev`). -/
  | rtcAlarm
  /-- The kernel's time zone (`sys_tz`, `kernel/time/time.c`: `tz_minuteswest` and `tz_dsttime`, two
  32-bit integers), which `settimeofday` may change at any time. -/
  | timezone
  /-- The CPU the thread runs on in the kernel, one of the machine's `cpus` (`Profile.cpus`, one if 0), and its
  NUMA node (`getcpu(2)`: `raw_smp_processor_id`, below `nr_cpu_ids`, and `cpu_to_node`). -/
  | cpuNode (cpus : Nat)

/-- The type of answers to a request. -/
def Request.Answer : Request → Type
  | .undefined w => BitVec w
  | .pick n => Fin (n + 1)
  | .between cpus => { evs : List EnvEvent // ∀ e ∈ evs, e.OnCpus cpus }
  | .read _ n => ReadResult n
  | .readFail _ n => Option (Errno × Fin (n + 1))
  | .write _ bytes => WriteResult bytes.length
  | .writeRefused _ => Option Errno
  | .writeFault _ _ n => WriteResult n
  | .fileAttrs _ => FileAttrs
  | .place _ => BitVec 64
  | .memFail pages => Option (Errno × Fin (pages + 1))
  | .growFail => Bool
  | .tsc => BitVec 64
  | .xinuse required => { v : BitVec 64 // required &&& v = required }
  | .randomCount n => Except Errno (Fin (n + 1))
  | .randomBytes k => { bs : List Byte // bs.length = k }
  | .readlink .. => LinkResult
  | .stat _ => StatResult
  | .openAt .. => OpenResult
  | .seekPast .. => Bool
  | .seek .. => Except Errno (Fin (2 ^ 63))
  | .ioctlGet _ _ n => IoctlResult n
  | .close _ => Option Errno
  | .fdGrow fd => Except Errno { n : Nat // fd < n ∧ n ≤ (fd + 1).nextPowerOfTwo }
  | .fcntl .. => Option Errno
  | .positional .. => Bool
  | .resumeIds cpus => { ids : BitVec 32 × BitVec 32 × BitVec 32 // (EnvEvent.kernelEntry ids.1 ids.2.1 ids.2.2).OnCpus cpus }
  | .setRlimit .. => Option Errno
  | .queued _ => Bool
  | .initPkru => { v : BitVec 32 // v &&& 3 = 0 }
  | .clock _ => Timespec
  | .rtcAlarm => Bool
  | .timezone => BitVec 64
  | .cpuNode cpus => { p : BitVec 32 × BitVec 32 // p.1.toNat < max cpus 1 }

/-- A program that issues requests and ends with a value. -/
inductive Req (α : Type) where
  | pure (a : α)
  | ask (r : Request) (k : r.Answer → Req α)

/-- Sequencing. -/
def Req.bind {α β : Type} : Req α → (α → Req β) → Req β
  | .pure a, f => f a
  | .ask r k, f => .ask r fun x => (k x).bind f

/-- Request programs form a monad. -/
instance : Monad Req where
  pure := .pure
  bind := Req.bind

/-- Ask request `r`. -/
def Req.request (r : Request) : Req r.Answer := .ask r .pure

/-- A stream of answers: the answer to any request at position `t`. -/
def Oracle := Nat → (r : Request) → r.Answer

/-- Run with answers from stream `o`, starting at position `t`; returns the result and the
next position. -/
def Req.runStream {α : Type} (o : Oracle) : Req α → Nat → α × Nat
  | .pure a, t => (a, t)
  | .ask r k, t => (k (o t r)).runStream o (t + 1)

/-- Run in any monad, answering requests with `h`. -/
def Req.interp {α : Type} {m : Type → Type} [Monad m] (h : (r : Request) → m r.Answer) :
    Req α → m α
  | .pure a => Pure.pure a
  | .ask r k => do let x ← h r; (k x).interp h

end ZellicX86
