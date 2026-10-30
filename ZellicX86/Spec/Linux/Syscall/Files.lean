import ZellicX86.Spec.Linux.Syscall.Common
/-!
# Linux system calls: opening and asking about files

`openat`, `readlinkat`, `fstat` and `ioctl(TCGETS2)`. The model has no file system: what a path
resolves to, a file's status and a terminal's settings are the environment's answers
(`Request.openAt`, `Request.readlink`, `Request.stat`, `Request.ioctlGet`), which may also be any error.
What the kernel computes itself is modelled: the flags' checks, the descriptor lookup and allocation,
reading the path name, the size limits, and copying the answer to the process's memory.

Not modelled: `ioctl` commands other than `TCGETS2`; `openat` that may create or truncate a file
(`O_CREAT`, `O_TRUNC`, `O_TMPFILE`). The close-on-exec flag a descriptor gets (`O_CLOEXEC`) is kept in
its entry (`FdEntry.cloexec`), which `execve` and `fcntl(F_GETFD)` read (`Spec/Linux/Syscall/Fd.lean`).

Sources: Linux v6.18 `fs/open.c` (`do_sys_openat2`, `build_open_how`, `build_open_flags`), `fs/file.c`
(`alloc_fd`), `fs/stat.c` (`do_readlinkat`, `vfs_readlink`, `newfstat`, `cp_new_stat`),
`fs/namei.c` (`getname_flags`, `path_init`), `fs/ioctl.c` (`ioctl`, `do_vfs_ioctl`),
`drivers/tty/tty_ioctl.c` (`tty_mode_ioctl`), `arch/x86/include/uapi/asm/stat.h`,
`include/uapi/asm-generic/ioctls.h`, `include/uapi/asm-generic/termbits.h`, `include/uapi/linux/fcntl.h`,
`include/uapi/asm-generic/fcntl.h`, `include/linux/fcntl.h`, `open(2)`, `readlink(2)`, `fstat(2)`,
`ioctl_tty(2)`.
-/
namespace ZellicX86

/-- `AT_FDCWD`: the working directory as the directory argument (`include/uapi/linux/fcntl.h`). -/
def AT_FDCWD : Int := -100

/-- No such file or directory (`include/uapi/asm-generic/errno-base.h`). -/
def ENOENT : Nat := 2
/-- Too many open files (`include/uapi/asm-generic/errno-base.h`). -/
def EMFILE : Nat := 24

/-- `open`'s access mode, its flags' low two bits (`include/uapi/asm-generic/fcntl.h`): `O_RDONLY` 0,
`O_WRONLY` 1, `O_RDWR` 2. -/
def O_ACCMODE : Nat := 0o3
/-- `open`: create the file if it does not exist. -/
def O_CREAT : Nat := 0o100
/-- `open`: with `O_CREAT`, fail if the file exists. -/
def O_EXCL : Nat := 0o200
/-- `open`: a terminal opened does not become the controlling terminal. -/
def O_NOCTTY : Nat := 0o400
/-- `open`: truncate the file to size 0. -/
def O_TRUNC : Nat := 0o1000
/-- `open`: every write goes to the file's end. -/
def O_APPEND : Nat := 0o2000
/-- `open`: reads and writes that would wait fail with `EAGAIN` instead (`O_NDELAY` is the same bit). -/
def O_NONBLOCK : Nat := 0o4000
/-- `open`: writes wait for the data to reach the storage. -/
def O_DSYNC : Nat := 0o10000
/-- `FASYNC` (`O_ASYNC`): the file signals the process when input or output becomes possible. -/
def FASYNC : Nat := 0o20000
/-- `open`: reads and writes bypass the page cache where the file system can. -/
def O_DIRECT : Nat := 0o40000
/-- `open`: the file may be larger than `2 ^ 31` bytes; `openat` sets it on x86-64 (`force_o_largefile`). -/
def O_LARGEFILE : Nat := 0o100000
/-- `open`: the path must name a directory. -/
def O_DIRECTORY : Nat := 0o200000
/-- `open`: do not follow a symbolic link in the last component. -/
def O_NOFOLLOW : Nat := 0o400000
/-- `open`: reads do not update the file's access time. -/
def O_NOATIME : Nat := 0o1000000
/-- `open`: the descriptor is closed by `execve`. -/
def O_CLOEXEC : Nat := 0o2000000
/-- `__O_SYNC`, the bit `O_SYNC` adds to `O_DSYNC`: writes wait for the data and the metadata. -/
def O_SYNC_BIT : Nat := 0o4000000
/-- `open`: a descriptor that only names the file, for path operations. -/
def O_PATH : Nat := 0o10000000
/-- `__O_TMPFILE`, the bit `O_TMPFILE` adds to `O_DIRECTORY`. -/
def O_TMPFILE_BIT : Nat := 0o20000000

/-- The flags `open` and `openat` take (`include/linux/fcntl.h` `VALID_OPEN_FLAGS`): the others are
dropped (`build_open_how`), as are all but `O_PATH_FLAGS` with `O_PATH`. -/
def VALID_OPEN_FLAGS : Nat := 0o37777703
/-- The flags `O_PATH` keeps (`include/linux/fcntl.h`). -/
def O_PATH_FLAGS : Nat := O_DIRECTORY ||| O_NOFOLLOW ||| O_PATH ||| O_CLOEXEC

/-- Whether flag bit(s) `b` are set in `flags`. -/
def hasFlag (flags b : Nat) : Bool := flags &&& b != 0

/-- `flags` without the bits `b` (`flags & ~b`). -/
def clearFlags (flags b : Nat) : Nat := flags ^^^ (flags &&& b)

/-- The status flags `fcntl(F_SETFL)` sets (`fs/fcntl.c` `SETFL_MASK`; `O_NDELAY` is `O_NONBLOCK` on
x86-64). -/
def setflMask : Nat := O_APPEND ||| O_NONBLOCK ||| O_DIRECT ||| O_NOATIME

/-- The status flags (`f_flags`) of the open file description `openat` creates with the flags `flags`
(after `VALID_OPEN_FLAGS`, and `O_PATH_FLAGS` with `O_PATH`): `O_LARGEFILE` added unless with `O_PATH`
(`openat` adds it before `build_open_how` drops it with `O_PATH`), `O_CLOEXEC` dropped (`build_open_flags`
strips it), `O_DSYNC` added with `__O_SYNC` (`build_open_flags`), and `O_CREAT`, `O_EXCL`, `O_NOCTTY`,
`O_TRUNC` dropped (`fs/open.c` `do_dentry_open`). -/
def openStatus (flags : Nat) : Nat :=
  if hasFlag flags O_PATH then clearFlags flags O_CLOEXEC
  else clearFlags (flags ||| O_LARGEFILE ||| (if hasFlag flags O_SYNC_BIT then O_DSYNC else 0))
    (O_CLOEXEC ||| O_CREAT ||| O_EXCL ||| O_NOCTTY ||| O_TRUNC)

/-- The status flags of an open file description with changing state `p` as `fcntl(F_GETFL)` reports
them (`f_flags`): `p.flags`, with `O_APPEND` as `p.append` says. -/
def statusFlags (p : FilePos) : Nat :=
  clearFlags p.flags O_APPEND ||| (if p.append then O_APPEND else 0)

/-- The lowest descriptor from `k` on, below `k + n`, that is not open (`fs/file.c` `alloc_fd`). -/
def firstFreeFd (fds : Nat → Option OpenFile) : Nat → Nat → Option Nat
  | 0, _ => none
  | n + 1, k => if fds k = none then some k else firstFreeFd fds n (k + 1)

/-- The entries of a descriptor table that start it (`NR_OPEN_DEFAULT`, `BITS_PER_LONG`,
`include/linux/fdtable.h`): no table holds fewer, so a descriptor below it never needs the table to grow. -/
def nrOpenDefault : Nat := 64

/-- `s` with its descriptor table able to hold descriptor `fd` (`fs/file.c` `expand_files`): as it is if
`fd` is below `nrOpenDefault` or below the table's size (`Proc.fdMax`); otherwise the table grows to the size
the environment gives (`Request.fdGrow`: `alloc_fdtable`), or fails with its error. -/
def expandFiles (s : State) (fd : Nat) : Req (Except Nat State) := do
  if fd < nrOpenDefault ∨ fd < s.proc.fdMax then Pure.pure (.ok s) else
  match ← Req.request (.fdGrow fd) with
  | .ok n => Pure.pure (.ok { s with proc.fdMax := n.val })
  | .error e => Pure.pure (.error e.val)

/-- A new descriptor at or above `start` (`fs/file.c` `alloc_fd`): the lowest not open, below the soft
limit `RLIMIT_NOFILE` and below `nrOpenMax`, past which no table grows (`EMFILE`), with the table made to
hold it (`expandFiles`, which may fail). The descriptor and the state with the table as it then is, or the
error. -/
def allocFd (s : State) (start : Nat) : Req (Except Nat (Nat × State)) := do
  let lim := min (s.proc.signal.rlimits RLIMIT_NOFILE).cur.toNat nrOpenMax
  match firstFreeFd s.proc.files.desc (lim - start) start with
  | none => Pure.pure (.error EMFILE)
  | some fd =>
    match ← expandFiles s fd with
    | .ok s' => Pure.pure (.ok (fd, s'))
    | .error e => Pure.pure (.error e)

/-- `openat(dirfd, path, flags, mode)` (`fs/open.c` `do_sys_openat2`); `dirfd` and `flags` are 32-bit.
The flags not in `VALID_OPEN_FLAGS` are dropped, and with `O_PATH` all but `O_PATH_FLAGS`
(`build_open_how`); `O_DIRECTORY` with `O_CREAT`, and `O_TMPFILE` without `O_DIRECTORY` or without
write access, are `EINVAL` (`build_open_flags`). The path is read from the process's memory
(`userPath`: `EFAULT`, `ENAMETOOLONG`; an empty one is `ENOENT`, `getname`). The new descriptor is
allocated next, before the path is looked up (`get_unused_fd_flags` before `do_filp_open`): the lowest
not open, below the soft limit `RLIMIT_NOFILE` and below `nrOpenMax` (`allocFd`: `EMFILE`; growing the
table may fail, `ENOMEM`, or meet a lower `fs.nr_open` setting, `EMFILE`); a table grown for it stays
grown when the call fails later (`put_unused_fd` frees the descriptor, not the table's room). A relative path is
looked up from `dirfd`, an open descriptor (`EBADF`) or the working directory (`AT_FDCWD`); what it
resolves to is the file system's (`Request.openAt`): a new open file description, with the process's
next identity (`OpenTable.next`, which moves on), readable for the
access modes `O_RDONLY` and `O_RDWR`, writable for `O_WRONLY` and `O_RDWR` (`OPEN_FMODE`), neither with
`O_PATH`, which also maps nothing a `mmap`, `read` or `write` takes (`FileMap.path`); its status flags are
`openStatus` of the flags (`O_APPEND` in `FilePos.append`), and its position is 0. The descriptor is the result, close-on-exec with `O_CLOEXEC` (`fs/file.c` `alloc_fd`
sets the bit from the flags), which `O_PATH` keeps: `O_PATH` drops every flag but `O_PATH_FLAGS`, of which
`O_CLOEXEC` is one (`fs/open.c` `build_open_how`). A file the call may create or truncate is not
modelled. -/
def sysOpenat (prof : Profile) (s : State) : Req StepResult := do
  let dfd := argInt s.cpu.gpr.rdi
  let fl₀ := arg32 s.cpu.gpr.rdx &&& VALID_OPEN_FLAGS
  let path? := hasFlag fl₀ O_PATH
  let flags := if path? then fl₀ &&& O_PATH_FLAGS else fl₀
  let acc := flags &&& O_ACCMODE
  if hasFlag flags O_DIRECTORY && hasFlag flags O_CREAT then Pure.pure (sysReturn s (errRet EINVAL) [] []) else
  if hasFlag flags O_TMPFILE_BIT && (!hasFlag flags O_DIRECTORY || acc == 0) then
    Pure.pure (sysReturn s (errRet EINVAL) [] []) else
  let (s, path) ← userPath prof s s.cpu.gpr.rsi
  let fail (e : Nat) (path : List Byte) : Req StepResult := Pure.pure (sysReturn s (errRet e) path [])
  match path with
  | .error e => fail e []
  | .ok [] => fail ENOENT []
  | .ok p =>
    match ← allocFd s 0 with
    | .error e => fail e p
    | .ok (fd, s) =>
      let fail (e : Nat) (path : List Byte) : Req StepResult := Pure.pure (sysReturn s (errRet e) path [])
      let dir : Except Nat (Option Nat) :=
        if p.head? = some 0x2f ∨ dfd = AT_FDCWD then .ok none
        else match (if dfd < 0 then none else s.proc.files.desc dfd.toNat) with
          | some f => .ok (some f.id)
          | none => .error EBADF
      match dir with
      | .error e => fail e p
      | .ok d =>
        if hasFlag flags (O_CREAT ||| O_TRUNC ||| O_TMPFILE_BIT) then
          Pure.pure (.stopped (.notModelled (.feature "openat that may create or truncate a file")))
        else
        match ← Req.request (.openAt d p flags) with
        | .error e => fail e.val p
        | .opened map =>
          let f : OpenFile :=
            { id := s.proc.opens.next, readable := !path? && (acc == 0 || acc == 2), writable := !path? && (acc == 1 || acc == 2),
              map := if path? then .path else map }
          let s' := { s with proc.files := fun n => if n = fd then some ⟨f, hasFlag flags O_CLOEXEC⟩ else s.proc.files n,
                             proc.opens.next := s.proc.opens.next + 1 }
          Pure.pure (sysReturn (s'.setFilePos f ⟨0, hasFlag flags O_APPEND, clearFlags (openStatus flags) O_APPEND⟩)
            (BitVec.ofNat 64 fd) p [])

/-- The bytes of the executable's path `p` as `d_path` writes them (`fs/d_path.c`): each name after a `/`
(`prepend_name`), a lone `/` for no names (`prepend_path`), then ` (deleted)` for an unlinked file; a memfd's
`/memfd:NAME (deleted)` (`simple_dname`) has the same form. Every such path starts with `/`. -/
def ExePath.bytes (p : ExePath) : List Byte :=
  (if p.names = [] then [0x2f] else p.names.flatMap (0x2f :: ·)) ++
    (if p.deleted then " (deleted)".toUTF8.toList.map UInt8.toBitVec else [])

/-- `readlinkat(dirfd, path, buf, bufsiz)` (`fs/stat.c` `do_readlinkat`); `dirfd` and `bufsiz` are
`int`s. A `bufsiz` of 0 or less is `EINVAL`. The path is read from the process's memory
(`userPath`: `EFAULT`, `ENAMETOOLONG`); unless it is absolute, it is looked up from `dirfd`, the
working directory for `AT_FDCWD` and otherwise an open descriptor (`EBADF`). The file system answers
with the link's contents, procfs's `exe` link of a process, or an error (`Request.readlink`). The
contents of an `exe` link are the executable's path (`ExePath.bytes`), which `d_path` writes into a
buffer of `PATH_MAX` bytes with its NUL: a longer path is `ENAMETOOLONG` (`do_proc_readlink`,
`fs/proc/base.c`). The first `bufsiz` bytes of the contents, without a NUL, are copied to `buf`
(`EFAULT`), and their number is the result. -/
def sysReadlinkat (prof : Profile) (s : State) : Req StepResult := do
  let dfd := argInt s.cpu.gpr.rdi
  let buf := s.cpu.gpr.rdx
  let bufsiz := argInt s.cpu.gpr.r10
  if bufsiz ≤ 0 then Pure.pure (sysReturn s (errRet EINVAL) [] []) else
  let (s, path) ← userPath prof s s.cpu.gpr.rsi
  let fail (e : Nat) (path : List Byte) : Req StepResult := Pure.pure (sysReturn s (errRet e) path [])
  match path with
  | .error e => fail e []
  | .ok p =>
    let dir : Except Nat (Option Nat) :=
      if p.head? = some 0x2f ∨ dfd = AT_FDCWD then .ok none
      else match (if dfd < 0 then none else s.proc.files.desc dfd.toNat) with
        | some f => .ok (some f.id)
        | none => .error EBADF
    match dir with
    | .error e => fail e p
    | .ok d =>
      let copy (t : List Byte) : Req StepResult := do
        let bs := t.take bufsiz.toNat
        let (s', k, all) ← copyOut prof s buf bs
        Pure.pure (sysReturn s' (if all then BitVec.ofNat 64 k else errRet EFAULT) p (bs.take k))
      match ← Req.request (.readlink d p) with
      | .error e => fail e.val p
      | .target t => copy t
      | .procExe x => if x.bytes.length < pathMax then copy x.bytes else fail ENAMETOOLONG p

/-- `struct stat` as the kernel writes it (`cp_new_stat`, `arch/x86/include/uapi/asm/stat.h`):
144 bytes, the fields little-endian at offsets 0 (`st_dev`), 8 (`st_ino`), 16 (`st_nlink`), 24
(`st_mode`), 28 (`st_uid`), 32 (`st_gid`), 40 (`st_rdev`), 48 (`st_size`), 56 (`st_blksize`), 64
(`st_blocks`), 72 to 112 (the three times, seconds then nanoseconds); the padding at 36 and from
120 on is zero (`INIT_STRUCT_STAT_PADDING`). -/
def Stat.bytes (st : Stat) : List Byte :=
  toBytesLE st.dev 8 ++ toBytesLE st.ino 8 ++ toBytesLE st.nlink 8 ++ toBytesLE st.mode 4 ++
  toBytesLE st.uid 4 ++ toBytesLE st.gid 4 ++ toBytesLE (0 : BitVec 32) 4 ++ toBytesLE st.rdev 8 ++
  toBytesLE st.size 8 ++ toBytesLE st.blksize 8 ++ toBytesLE st.blocks 8 ++
  toBytesLE st.atime 8 ++ toBytesLE st.atimeNsec 8 ++ toBytesLE st.mtime 8 ++
  toBytesLE st.mtimeNsec 8 ++ toBytesLE st.ctime 8 ++ toBytesLE st.ctimeNsec 8 ++
  toBytesLE (0 : BitVec 192) 24

/-- The mask of a file's type in `st_mode` (`S_IFMT`, `include/uapi/linux/stat.h`). -/
def S_IFMT : BitVec 32 := 0o170000

/-- The type of a regular file in `st_mode` (`S_IFREG`). -/
def S_IFREG : BitVec 32 := 0o100000

/-- The status `fstat` reports for the open file `f`, of the status `st` the file system gives
(`Request.stat`) and the files `fs`: for a regular file with pages (`FileMap.pages`, `Files.regular`),
its size is the file's (`st_size`, `i_size_read` in `generic_fillattr`) and its type `S_IFREG`; the rest
is the file system's (the device and inode numbers, links, owner, permissions, block counts, times),
as is all of another file's status. -/
def statOf (fs : Files) (f : OpenFile) (st : Stat) : Stat :=
  match f.map with
  | .pages id =>
    if fs.regular id then
      { st with size := BitVec.ofNat 64 (fs.size id), mode := (st.mode &&& ~~~S_IFMT) ||| S_IFREG }
    else st
  | _ => st

/-- `fstat(fd, buf)` (`fs/stat.c` `newfstat`); `fd` is 32-bit. The descriptor must be open
(`EBADF`); the file's status or an error is the environment's (`Request.stat`), except for the size
and type of a regular file with pages, which the model holds (`statOf`); the status is copied to `buf`
as `struct stat` (`Stat.bytes`; `EFAULT`). -/
def sysFstat (prof : Profile) (s : State) : Req StepResult := do
  let buf := s.cpu.gpr.rsi
  match s.proc.files.desc (arg32 s.cpu.gpr.rdi) with
  | none => Pure.pure (sysReturn s (errRet EBADF) [] [])
  | some f =>
    match ← Req.request (.stat f.id) with
    | .error e => Pure.pure (sysReturn s (errRet e.val) [] [])
    | .ok st =>
      let bs := (statOf s.proc.mm.mem.files f st).bytes
      let (s', k, all) ← copyOut prof s buf bs
      Pure.pure (sysReturn s' (if all then 0 else errRet EFAULT) [] (bs.take k))

/-- `TCGETS2`, `_IOR('T', 0x2A, struct termios2)`: a terminal's settings, 44 bytes
(`include/uapi/asm-generic/ioctls.h`, `termbits.h`). -/
def TCGETS2 : Nat := 0x802C542A

/-- `ioctl(fd, cmd, arg)` (`fs/ioctl.c`); `fd` and `cmd` are 32-bit. The descriptor must be open and
not `O_PATH` (`EBADF`, whatever the command; `CLASS(fd)`, `fdget`: `FdTable.descNoPath`). For `TCGETS2` the file answers with a `struct termios2` or an error (`ENOTTY` for a file
that is not a terminal; `Request.ioctlGet`), which is copied to `arg` (`EFAULT`). Other commands are
not modelled. -/
def sysIoctl (prof : Profile) (s : State) : Req StepResult := do
  let cmd := arg32 s.cpu.gpr.rsi
  match s.proc.files.descNoPath (arg32 s.cpu.gpr.rdi) with
  | none => Pure.pure (sysReturn s (errRet EBADF) [] [])
  | some f =>
    if cmd ≠ TCGETS2 then Pure.pure (.stopped (.notModelled (.feature "ioctl command"))) else
    match ← Req.request (.ioctlGet f.id cmd 44) with
    | .error e => Pure.pure (sysReturn s (errRet e.val) [] [])
    | .ok bs _ =>
      let (s', k, all) ← copyOut prof s s.cpu.gpr.rdx bs
      Pure.pure (sysReturn s' (if all then 0 else errRet EFAULT) [] (bs.take k))

end ZellicX86
