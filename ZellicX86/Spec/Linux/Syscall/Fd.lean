import ZellicX86.Spec.Linux.Syscall.Files
/-!
# Linux system calls: the descriptor table

`close`, `dup`, `dup2`, `dup3` and `fcntl` (`F_DUPFD`, `F_DUPFD_CLOEXEC`, `F_DUPFD_QUERY`, `F_GETFD`,
`F_SETFD`, `F_GETFL`, `F_SETFL`). They change the process's descriptor table (`Proc.files`): which
descriptors are open, on which open file description, with which close-on-exec flag; and the status
flags of a description (`FilePos`). A description itself is never copied: every descriptor `dup` makes
refers to the same one, so it shares its position and status flags (`OpenTable.pos`, by description).

What the model does not track is the environment's: a file's `flush` at `close` (`Request.close`), the
table growing past its size (`Proc.fdMax`, `Request.fdGrow`), and the security module's and the file's
refusals of `fcntl` (`Request.fcntl`).

A description no descriptor refers to any more stays in `OpenTable.pos`, where nothing reads it: the
kernel frees it when its last reference goes (`fput`), and its identity is never given to another
(`OpenTable.next`). Its release does nothing the process sees in the model: what it does to others (a
pipe's reader seeing the end, a socket shut down, a lock released) is theirs, and reaches the process,
if at all, through the environment's answers. Not modelled: the other `fcntl` commands (record locks,
owners and signals, leases, notifications, pipe sizes, seals); `F_SETFL` changing `FASYNC` of a file without
pages (pipes, sockets and terminals have a `fasync` operation, and the signal it enables is not modelled);
`close_range`.

Sources: Linux v6.18 `fs/file.c` (`alloc_fd`, `expand_files`, `close_fd`, `do_dup2`, `ksys_dup3`, `dup2`,
`dup`, `f_dupfd`, `set_close_on_exec`, `get_close_on_exec`), `fs/open.c` (`close`, `filp_flush`),
`fs/fcntl.c` (`fcntl`, `check_fcntl_cmd`, `do_fcntl`, `setfl`, `f_dupfd_query`),
`include/uapi/asm-generic/fcntl.h`, `include/uapi/linux/fcntl.h`, `include/linux/errno.h`, `close(2)`,
`dup(2)`, `fcntl(2)`.
-/
namespace ZellicX86

/-- Interrupted system call (`include/uapi/asm-generic/errno-base.h`). -/
def EINTR : Nat := 4

/-- `fcntl`: duplicate the descriptor onto the lowest free one at or above the argument. -/
def F_DUPFD : Nat := 0
/-- `fcntl`: the descriptor's flags (`FD_CLOEXEC`). -/
def F_GETFD : Nat := 1
/-- `fcntl`: set the descriptor's flags. -/
def F_SETFD : Nat := 2
/-- `fcntl`: the description's status flags (`f_flags`). -/
def F_GETFL : Nat := 3
/-- `fcntl`: set the description's status flags that may be set (`setflMask`). -/
def F_SETFL : Nat := 4
/-- `fcntl`: whether the argument is a descriptor on the same open file description
(`F_LINUX_SPECIFIC_BASE + 3`, `include/uapi/linux/fcntl.h`). -/
def F_DUPFD_QUERY : Nat := 1027
/-- `fcntl`: whether the description's open created its file (`F_LINUX_SPECIFIC_BASE + 4`). -/
def F_CREATED_QUERY : Nat := 1028
/-- `fcntl`: as `F_DUPFD`, the new descriptor close-on-exec (`F_LINUX_SPECIFIC_BASE + 6`). -/
def F_DUPFD_CLOEXEC : Nat := 1030
/-- The descriptor flag close-on-exec (`include/uapi/asm-generic/fcntl.h`); `F_SETFD` reads the low
bit of its argument. -/
def FD_CLOEXEC : Nat := 1

/-- `s` with descriptor `fd`'s entry set to `e` (`none`: closed). -/
def State.setFd (s : State) (fd : Nat) (e : Option FdEntry) : State :=
  { s with proc.files := fun n => if n = fd then e else s.proc.files n }

/-- What `close` returns for the error `e` of a file's `flush`: a request to restart the call
(`ERESTARTSYS`, `ERESTARTNOINTR`, `ERESTARTNOHAND`, `ERESTART_RESTARTBLOCK`, `include/linux/errno.h`)
becomes `EINTR`, since the descriptor is already gone (`fs/open.c` `close`). -/
def closeErr (e : Nat) : Nat :=
  if e = 512 ∨ e = 513 ∨ e = 514 ∨ e = 516 then EINTR else e

/-- `close(fd)` (`fs/open.c` `close`, `fs/file.c` `file_close_fd`); `fd` is 32-bit. The descriptor must be
open, `O_PATH` or not (`EBADF`). It is closed whatever comes next. The file's `flush` operation then runs
and its error is the result (`Request.close`; `closeErr`); a descriptor opened with `O_PATH` has no file
operations, so its result is 0 (`filp_flush`, `empty_fops`). -/
def sysClose (s : State) : Req StepResult := do
  let fd := arg32 s.cpu.gpr.rdi
  match s.proc.files.desc fd with
  | none => Pure.pure (sysReturn s (errRet EBADF) [] [])
  | some f =>
    let s' := s.setFd fd none
    if f.map = .path then Pure.pure (sysReturn s' 0 [] []) else
    match ← Req.request (.close f.id) with
    | none => Pure.pure (sysReturn s' 0 [] [])
    | some e => Pure.pure (sysReturn s' (errRet (closeErr e.val)) [] [])

/-- `dup(fd)` (`fs/file.c` `dup`); `fd` is 32-bit. The descriptor must be open, `O_PATH` or not
(`EBADF`; `fget_raw`); the new descriptor is the lowest free one (`allocFd`), on the same open file
description, not close-on-exec, and it is the result. -/
def sysDup (s : State) : Req StepResult := do
  match s.proc.files.desc (arg32 s.cpu.gpr.rdi) with
  | none => Pure.pure (sysReturn s (errRet EBADF) [] [])
  | some f =>
    match ← allocFd s 0 with
    | .error e => Pure.pure (sysReturn s (errRet e) [] [])
    | .ok (fd, s) => Pure.pure (sysReturn (s.setFd fd (some ⟨f, false⟩)) (BitVec.ofNat 64 fd) [] [])

/-- Descriptor `old` duplicated onto `new`, a different one, close-on-exec as `cloexec` says (`fs/file.c`
`ksys_dup3`, `do_dup2`): `new` must be below the soft limit `RLIMIT_NOFILE` (`EBADF`); the table is
grown to hold `new` first (`expandFiles`: past `nrOpenMax`, or the environment's refusal of
`Request.fdGrow`), and a grown table stays grown whatever follows; then `old` must be open, `O_PATH` or not
(`EBADF`), and the table's growth must have succeeded (its error, `EMFILE` becoming `EBADF`). Then `new` refers to `old`'s
open file description, and `new` is the result. A description `new` referred to before loses that
reference, and its `flush` error is dropped (`do_dup2` calls `filp_close` and ignores its result). -/
def dupTo (s : State) (old new : Nat) (cloexec : Bool) : Req StepResult := do
  let fail (e : Nat) : Req StepResult := Pure.pure (sysReturn s (errRet e) [] [])
  if (s.proc.signal.rlimits RLIMIT_NOFILE).cur.toNat ≤ new then fail EBADF else
  if nrOpenMax ≤ new then fail EBADF else
  match ← expandFiles s new with
  | .error e =>
    match s.proc.files.desc old with
    | none => fail EBADF
    | some _ => fail (if e = EMFILE then EBADF else e)
  | .ok s =>
    match s.proc.files.desc old with
    | none => Pure.pure (sysReturn s (errRet EBADF) [] [])
    | some f => Pure.pure (sysReturn (s.setFd new (some ⟨f, cloexec⟩)) (BitVec.ofNat 64 new) [] [])

/-- `dup2(old, new)` (`fs/file.c` `dup2`); both are 32-bit. The same descriptor twice: `old` if it is open,
`O_PATH` or not, else `EBADF`, and nothing changes. Otherwise `dupTo`, not close-on-exec. -/
def sysDup2 (s : State) : Req StepResult :=
  let old := arg32 s.cpu.gpr.rdi
  let new := arg32 s.cpu.gpr.rsi
  if old = new then
    match s.proc.files.desc old with
    | none => Pure.pure (sysReturn s (errRet EBADF) [] [])
    | some _ => Pure.pure (sysReturn s (BitVec.ofNat 64 old) [] [])
  else dupTo s old new false

/-- `dup3(old, new, flags)` (`fs/file.c` `ksys_dup3`); all three are 32-bit. Flags other than
`O_CLOEXEC`, or the same descriptor twice, are `EINVAL`; otherwise `dupTo`, close-on-exec with
`O_CLOEXEC`. -/
def sysDup3 (s : State) : Req StepResult :=
  let old := arg32 s.cpu.gpr.rdi
  let new := arg32 s.cpu.gpr.rsi
  let flags := arg32 s.cpu.gpr.rdx
  if clearFlags flags O_CLOEXEC ≠ 0 ∨ old = new then Pure.pure (sysReturn s (errRet EINVAL) [] [])
  else dupTo s old new (hasFlag flags O_CLOEXEC)

/-- The `fcntl` commands a descriptor opened with `O_PATH` takes (`fs/fcntl.c` `check_fcntl_cmd`); the
others are `EBADF` on it. -/
def pathFcntlCmds : List Nat :=
  [F_CREATED_QUERY, F_DUPFD, F_DUPFD_CLOEXEC, F_DUPFD_QUERY, F_GETFD, F_SETFD, F_GETFL]

/-- The `fcntl` commands the model has. -/
def modelledFcntlCmds : List Nat :=
  [F_DUPFD, F_DUPFD_CLOEXEC, F_DUPFD_QUERY, F_GETFD, F_SETFD, F_GETFL, F_SETFL]

/-- `fcntl(fd, cmd, arg)` (`fs/fcntl.c` `fcntl`, `do_fcntl`); `fd` and `cmd` are 32-bit, the commands
below read `arg` as an `int` (its low 32 bits). The descriptor must be open (`EBADF`; `fdget_raw`), and
one opened with `O_PATH` takes only `pathFcntlCmds` (`EBADF`). Commands other than `modelledFcntlCmds`
are not modelled. The security module may refuse any command, and the file `F_SETFL` (`Request.fcntl`,
before the command runs). Then:
- `F_DUPFD` and `F_DUPFD_CLOEXEC` (`f_dupfd`): the argument as an unsigned number must be below the soft
  limit `RLIMIT_NOFILE` (`EINVAL`); the lowest free descriptor at or above it (`allocFd`) refers to the
  same open file description, close-on-exec for `F_DUPFD_CLOEXEC`, and is the result;
- `F_DUPFD_QUERY` (`f_dupfd_query`): the argument must be an open descriptor (`EBADF`); 1 if it is on the
  same description, else 0;
- `F_GETFD`: `FD_CLOEXEC` if the descriptor is close-on-exec, else 0; `F_SETFD`: the descriptor becomes
  close-on-exec as the argument's low bit says (`set_close_on_exec`), and the result is 0;
- `F_GETFL`: the description's status flags (`statusFlags`);
- `F_SETFL` (`setfl`): the flags of `setflMask` become the argument's, for every descriptor on the
  description; the result is 0. `FASYNC` changes only through the file's `fasync` operation, which sets
  it (`fasync_helper`): files with pages have none (regular files of tmpfs, memfds, block devices and the
  disk file systems: `mm/shmem.c`, `block/fops.c`), or pass it to the regular file below, which has none
  (ecryptfs, `fs/ecryptfs/file.c` `ecryptfs_fasync`), so it stays; for other files a change of it is not
  modelled. -/
def sysFcntl (s : State) : Req StepResult := do
  let fd := arg32 s.cpu.gpr.rdi
  let cmd := arg32 s.cpu.gpr.rsi
  let argi := arg32 s.cpu.gpr.rdx
  let fail (e : Nat) : Req StepResult := Pure.pure (sysReturn s (errRet e) [] [])
  match s.proc.files fd with
  | none => fail EBADF
  | some ent =>
    let f := ent.file
    if f.map = .path ∧ cmd ∉ pathFcntlCmds then fail EBADF else
    if cmd ∉ modelledFcntlCmds then Pure.pure (.stopped (.notModelled (.feature "fcntl command"))) else
    match ← Req.request (.fcntl f.id cmd s.cpu.gpr.rdx.toNat) with
    | some e => fail e.val
    | none =>
      if cmd = F_DUPFD ∨ cmd = F_DUPFD_CLOEXEC then
        if (s.proc.signal.rlimits RLIMIT_NOFILE).cur.toNat ≤ argi then fail EINVAL else
        match ← allocFd s argi with
        | .error e => fail e
        | .ok (n, s) => Pure.pure (sysReturn (s.setFd n (some ⟨f, cmd = F_DUPFD_CLOEXEC⟩)) (BitVec.ofNat 64 n) [] [])
      else if cmd = F_DUPFD_QUERY then
        match s.proc.files.desc argi with
        | none => fail EBADF
        | some g => Pure.pure (sysReturn s (if g = f then 1 else 0) [] [])
      else if cmd = F_GETFD then Pure.pure (sysReturn s (if ent.cloexec then BitVec.ofNat 64 FD_CLOEXEC else 0) [] [])
      else if cmd = F_SETFD then
        Pure.pure (sysReturn (s.setFd fd (some ⟨f, hasFlag argi FD_CLOEXEC⟩)) 0 [] [])
      else
        let p := s.proc.opens.pos f
        let cur := statusFlags p
        if cmd = F_GETFL then Pure.pure (sysReturn s (BitVec.ofNat 64 cur) [] []) else
        if hasFlag (argi ^^^ cur) FASYNC ∧ !f.map.isPages then
          Pure.pure (.stopped (.notModelled (.feature "fcntl F_SETFL changing FASYNC")))
        else
          let nf := (argi &&& setflMask) ||| clearFlags cur setflMask
          Pure.pure (sysReturn (s.setFilePos f ⟨p.offset, hasFlag nf O_APPEND, clearFlags nf O_APPEND⟩) 0 [] [])

end ZellicX86
