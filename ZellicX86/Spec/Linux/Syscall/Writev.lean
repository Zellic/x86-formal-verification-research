import ZellicX86.Spec.Linux.Syscall.ReadWrite
/-!
# Linux system calls: `writev`

Sources: Linux v6.18 `fs/read_write.c` (`do_writev`, `vfs_writev`), `lib/iov_iter.c`
(`copy_iovec_from_user`, `iovec_from_user`, `__import_iovec`, `import_ubuf`, `copy_from_user_iter`),
`include/linux/uio.h` (`iov_iter_truncate`), `include/linux/iov_iter.h` (`iterate_iovec`),
`include/uapi/linux/uio.h`.
-/
namespace ZellicX86

/-- A native x86-64 `struct iovec` (`include/uapi/linux/uio.h`): a user pointer and an unsigned 64-bit
length. -/
structure Iovec where
  /-- `iov_base`: where the entry's bytes start. -/
  base : Addr
  /-- `iov_len`: how many bytes the entry has. -/
  len : Nat
  deriving Repr

/-- The `n` entries of a native `iovec` array at `a`, read as `copy_iovec_from_user` reads them: each
entry's length before its base. A length that is negative as a signed 64-bit number is `EINVAL`, a word
the kernel cannot read `EFAULT`. The reads grow a stack where they must (`growFor`); the result comes
with the state after the growths. -/
def copyIovecs (prof : Profile) : Nat → State → Addr → Req (State × Except Nat (List Iovec))
  | 0, s, _ => Pure.pure (s, .ok [])
  | n + 1, s, a => do
    let s ← growFor prof s .read (a.add 8) 8
    match kernelRead prof.feat s (a.add 8) 8 with
    | none => Pure.pure (s, .error EFAULT)
    | some bs =>
      let len := ofBytesLE 64 bs
      let s ← growFor prof s .read a 8
      match kernelRead prof.feat s a 8 with
      | none => Pure.pure (s, .error EFAULT)
      | some bs =>
        if len.toInt < 0 then Pure.pure (s, .error EINVAL) else
        let (s, rest) ← copyIovecs prof n s (a.add 16)
        Pure.pure (s, rest.map (⟨ofBytesLE 64 bs, len.toNat⟩ :: ·))

/-- The entries `vs` cut to `room` bytes in all, without reading user memory again (`iov_iter_truncate`;
the file size limit cuts a write this way). -/
def takeIovecs : List Iovec → Nat → List Iovec
  | [], _ => []
  | v :: vs, room => ⟨v.base, min v.len room⟩ :: takeIovecs vs (room - min v.len room)

/-- The import of several entries (`__import_iovec`): every entry's whole range must pass `access_ok`
(`EFAULT`), also the part beyond the cap; then the entries are cut to `room` bytes in all. -/
def limitIovecsMany (feat : Features) : List Iovec → Nat → Except Nat (List Iovec)
  | [], _ => .ok []
  | v :: vs, room =>
    if !accessOk feat v.base v.len then .error EFAULT else
    let n := min v.len room
    (limitIovecsMany feat vs (room - n)).map (⟨v.base, n⟩ :: ·)

/-- The entries `vs` checked and cut to `room` bytes in all: a single entry is cut first and then
checked (`__import_iovec_ubuf`, `import_ubuf`); several are checked whole first (`limitIovecsMany`). -/
def limitIovecs (feat : Features) (vs : List Iovec) (room : Nat) : Except Nat (List Iovec) :=
  match vs with
  | [v] =>
    let n := min v.len room
    if !accessOk feat v.base n then .error EFAULT else .ok [⟨v.base, n⟩]
  | _ => limitIovecsMany feat vs room

/-- The import of a native `iovec` array of `count` entries at `a` (`iovec_from_user`, `__import_iovec`).
No entries need no pointer and give none. More than `UIO_MAXIOV` (1024) is `EINVAL`; more than
`UIO_FASTIOV` (8) needs a kernel allocation, whose failure is a choice (`Request.pick`, answer 1:
`ENOMEM`). `count` is an unsigned 32-bit number (`import_iovec`'s parameter), also for the native
`writev`. The whole array must pass `access_ok` (`EFAULT`) before its words are read (`copyIovecs`);
the entries are then cut to `MAX_RW_COUNT` bytes in all (`limitIovecs`). -/
def importIovecs (prof : Profile) (s : State) (a : Addr) (count : Nat) :
    Req (State × Except Nat (List Iovec)) := do
  if count = 0 then Pure.pure (s, .ok []) else
  if count > 1024 then Pure.pure (s, .error EINVAL) else
  if count > 8 then
    let fail ← Req.request (.pick 1)
    if fail.val = 1 then return (s, .error ENOMEM)
  if !accessOk prof.feat a (16 * count) then Pure.pure (s, .error EFAULT) else
  let (s, r) ← copyIovecs prof count s a
  Pure.pure (s, r.bind (fun vs => limitIovecs prof.feat vs maxRwCount))

/-- The bytes the kernel reads from the entries, in order, up to the first byte it cannot read
(`iterate_iovec`, `copy_from_user_iter`); `chunks` holds the parts read so far, the last first. Only
the entries' bytes are read, not the `iovec` array. The reads grow a stack where they must
(`growFor`). Whether a buffer lies on the output file's pages is checked by `writevFile` before this
runs. -/
def readIovecs (prof : Profile) : List Iovec → State → List (List Byte) → Req (State × List Byte)
  | [], s, chunks => Pure.pure (s, chunks.reverse.flatten)
  | v :: vs, s, chunks => do
    let s ← growFor prof s .read v.base v.len
    let k := readableLead prof.feat s v.base v.len
    let chunks := readBytes s.proc.mm.mem v.base k :: chunks
    if k < v.len then Pure.pure (s, chunks.reverse.flatten)
    else readIovecs prof vs s chunks

/-- `writev` to the open file `f`, which can be written (`vfs_writev`, after its `FMODE_CAN_WRITE`
check): the entries are imported (`importIovecs`), an empty total returns 0, and their bytes are
written as one write, as `writeFile` writes them for `write`. -/
def writevFile (prof : Profile) (s : State) (f : OpenFile) : Req StepResult := do
  let (s, imported) ← importIovecs prof s s.cpu.gpr.rsi (arg32 s.cpu.gpr.rdx)
  match imported with
  | .error e => Pure.pure (sysReturn s (errRet e) [] [])
  | .ok vs =>
    let count := (vs.map (·.len)).sum
    if count = 0 then Pure.pure (sysReturn s 0 [] []) else
    if f.map.isPages ∧ 2 ^ 63 ≤ (s.proc.opens.pos f).offset + count then
      Pure.pure (sysReturn s (errRet EINVAL) [] []) else
    match ← fsizeLimit s f count none with
    | .error r => Pure.pure r
    | .ok n =>
      let vs := takeIovecs vs n
      let target := f.writeTarget s.proc.mm.mem.files
      if target.any (fun id => vs.any (fun v => s.proc.mm.mem.readsFile v.base v.len id)) then
        Pure.pure (.stopped (.notModelled (.feature "writev from a mapping of the file written")))
      else
        let fresh := s.proc.mm.mem.fresh
        let (s, bs) ← readIovecs prof vs s []
        let grows := fresh != s.proc.mm.mem.fresh
        if bs.length = n then
          let r ← Req.request (.write f.id bs)
          writeFile.answer s f target bs none false grows r
        else match f.map with
        | .pages _ =>
          let r ← Req.request (.write f.id bs)
          writeFile.answer s f target bs none true grows r
        | _ =>
          let r ← Req.request (.writeFault f.id bs n)
          writeFile.answer s f target bs none false grows r


/-- `writev(fd, iov, iovcnt)` (`fs/read_write.c` `do_writev`, `vfs_writev`); `fd` and `iovcnt` are
32-bit. The descriptor must be open for writing (`EBADF`). A file without pages may lack a write
operation (`FMODE_CAN_WRITE`): then `EINVAL`, before the import, which the model leaves to a choice
(`Request.pick`, answer 1) made afresh on every call. The entries are imported (`importIovecs`) and
their concatenation is written as one operation (`writevFile`); an empty total returns 0 without
asking the file. The file's position, the limits, the signals, the page cache and partial writes are
as for `write` (`writeFile.answer`; `generic_perform_write`, `fs/pipe.c` `anon_pipe_write`): a buffer
the kernel cannot read ends the data early, which may give a short count, and a file without pages
answers through `Request.writeFault`. Not modelled, as for `write`: buffers on the output file's pages
(the kernel may read bytes it already wrote), and a partial write or an error after the reads grew a
stack. -/
def sysWritev (prof : Profile) (s : State) : Req StepResult := do
  match s.proc.files.desc (arg32 s.cpu.gpr.rdi) with
  | none => Pure.pure (sysReturn s (errRet EBADF) [] [])
  | some f =>
    if !f.writable then Pure.pure (sysReturn s (errRet EBADF) [] []) else
    if !f.map.isPages then
      -- The model does not identify every device's file operations. Even an O_RDWR timerfd
      -- has no write operation (`fs/open.c` `do_dentry_open`, `fs/timerfd.c` `timerfd_fops`).
      let unavailable ← Req.request (.pick 1)
      if unavailable.val = 1 then return sysReturn s (errRet EINVAL) [] []
    writevFile prof s f

end ZellicX86
