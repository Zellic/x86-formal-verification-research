import ZellicX86.Spec.Linux.Syscall.Common
/-!
# Linux system calls: `read`, `write`, `lseek`, `pread64` and `pwrite64`

Sources: `fs/read_write.c`, `fs/pipe.c`, `mm/filemap.c`, `lib/iov_iter.c`, `drivers/char/mem.c`,
`include/uapi/linux/fs.h`, `lseek(2)`.
-/
namespace ZellicX86
open Signal

/-- The end of a `read` that delivers the bytes `bs` from a file into `buf`, the state after it
changed by `done` (the file's position): the kernel copies them to the process's memory, which grows a
stack where it must (`growFor`), and the call returns their number. Delivering data into bytes the
process cannot write is not modelled (the kernel's result then depends on the file type). -/
def deliverRead (prof : Profile) (s : State) (buf : Addr) (bs : List Byte) (done : State → State) :
    Req StepResult := do
  let s ← growFor prof s .write buf bs.length
  match kernelWrite prof.feat s buf bs with
  | some s' => Pure.pure (sysReturn (done s') (BitVec.ofNat 64 bs.length) [] bs)
  | none => Pure.pure (.stopped (.notModelled (.feature "read into unwritable memory")))

/-- A read of up to `count` bytes into `buf` from the open file `f`, which is on the pages of file `id`
(`FileMap.pages`), at offset `off` (`fs/read_write.c` `vfs_read`, `rw_verify_area`, `mm/filemap.c`
`filemap_read`): `EINVAL` if the offset and the count reach `2 ^ 63` (a `loff_t`); otherwise the file's
bytes from the offset (`Files.bytes`, the page cache's), as many as asked for up to the file's end (none
at or past it), unless the read fails part way (`Request.readFail`): then the bytes before the failure,
or the error if there are none. The state after delivering `k` bytes is changed by `done k`. -/
def readPagesAt (prof : Profile) (s : State) (f : OpenFile) (id : FileId) (buf : Addr) (count off : Nat)
    (done : Nat → State → State) : Req StepResult := do
  if 2 ^ 63 ≤ off + count then Pure.pure (sysReturn s (errRet EINVAL) [] []) else
  let fs := s.proc.mm.mem.files
  let want := min (min count maxRwCount) (fs.size id - off)
  let deliver (k : Nat) : Req StepResult := deliverRead prof s buf (fs.bytes id off k) (done k)
  match ← Req.request (.readFail f.id want) with
  | none => deliver want
  | some (e, k) => if k.val = 0 then Pure.pure (sysReturn s (errRet e.val) [] []) else deliver k.val

/-- `read` of up to `count` bytes into `buf` from the open file `f`, which is on the pages of file `id`:
`readPagesAt` the open file's position, which advances by the bytes delivered. -/
def readPages (prof : Profile) (s : State) (f : OpenFile) (id : FileId) (buf : Addr) (count : Nat) :
    Req StepResult :=
  let p := s.proc.opens.pos f
  readPagesAt prof s f id buf count p.offset fun k s' => s'.setFilePos f { p with offset := p.offset + k }

/-- `read(fd, buf, count)` (`fs/read_write.c` `ksys_read`, `vfs_read`). The descriptor must
be open for reading (`EBADF`), `buf` and `count` must pass `access_ok` (`EFAULT`); `count` is
limited to `MAX_RW_COUNT`. A file with pages delivers its bytes from the open file's position
(`readPages`); for every other file the data or error comes from the environment. The bytes are
delivered as `deliverRead` says. -/
def sysRead (prof : Profile) (s : State) : Req StepResult := do
  let fd := s.cpu.gpr.rdi.toNat % 2 ^ 32
  let buf := s.cpu.gpr.rsi
  let count := s.cpu.gpr.rdx.toNat
  match s.proc.files.desc fd with
  | none => Pure.pure (sysReturn s (errRet EBADF) [] [])
  | some f =>
    if !f.readable then Pure.pure (sysReturn s (errRet EBADF) [] [])
    else if !accessOk prof.feat buf count then Pure.pure (sysReturn s (errRet EFAULT) [] [])
    else match f.map with
    | .pages id => readPages prof s f id buf count
    | _ => do
      let r ← Req.request (.read f.id (min count maxRwCount))
      match r with
      | .error e => Pure.pure (sysReturn s (errRet e.val) [] [])
      | .data bs _ => deliverRead prof s buf bs fun t => t

/-- Whether one of the `n` bytes from `a` is stored in a page that maps a page of file `file`
(a shared mapping of it, or a private one not yet copied). -/
def Memory.readsFile (mem : Memory) (a : Addr) (n : Nat) (file : FileId) : Bool :=
  (List.range n).any fun i =>
    match mem.map (pageOf (a.add i)) with
    | some m => ((mem.backings m.backing).filePage.map (·.file)) == some file
    | none => false

/-- The file whose pages a `write` to the open file `f` changes (`Files`): its pages' file
(`FileMap.pages`), unless its writing is denied. -/
def OpenFile.writeTarget (f : OpenFile) (fs : Files) : Option FileId :=
  match f.map with
  | .pages id => if fs.denyWrite id then none else some id
  | _ => none

/-- A signal the kernel sends the thread in a `write` (`SIGPIPE`, `SIGXFSZ`: `send_sig` with
`SEND_SIG_NOINFO`, the thread's own process and user id as the sender's; not forced,
`send_signal_locked`, so a PID namespace's init ignores it, `sigTaskIgnored`). -/
def writeSignal (s : State) (sig : Signal) : StepResult :=
  sendNoHandler s ⟨SigInfo.ofSender sig SI_USER s.thread.tid s.thread.uid, .kernel⟩ true false

/-- Whether the kernel checks the file size limit itself on a write to the open file `f` that the model
follows: `f` is on the pages of a regular file (`Files.regular`), whose file system checks it before it
copies (`generic_write_checks`, `generic_write_check_limits`). -/
def OpenFile.limitChecked (f : OpenFile) (fs : Files) : Bool :=
  match f.map with
  | .pages id => fs.regular id
  | _ => false

/-- The file size limit (`RLIMIT_FSIZE`) on a write of `n` bytes (`n` at most `MAX_RW_COUNT`) to the open
file `f` at offset `off?` (else its position), before the kernel reads the buffer (`fs/read_write.c`
`generic_write_checks_count`, `generic_write_check_limits`): for a regular file with pages
(`OpenFile.limitChecked`), `n` not 0 and a limit (not `RLIM_INFINITY`), the write position (the file's end
with `O_APPEND`) at or beyond the limit fails the call, with `SIGXFSZ` sent (`EFBIG` if the signal does not
end the process), unless the call fails earlier (`Request.writeRefused`); below it the write is cut to end
at the limit. `.ok` with the number of bytes the write goes on with, or `.error` with the call's end. -/
def fsizeLimit (s : State) (f : OpenFile) (n : Nat) (off? : Option Nat) : Req (Except StepResult Nat) := do
  let lim := (s.proc.signal.rlimits RLIMIT_FSIZE).cur
  let fs := s.proc.mm.mem.files
  match f.map with
  | .pages id =>
    if !fs.regular id || n = 0 || lim = RLIM_INFINITY then Pure.pure (.ok n) else
    let p := s.proc.opens.pos f
    let pos := if p.append then fs.size id else off?.getD p.offset
    if pos < lim.toNat then Pure.pure (.ok (min n (lim.toNat - pos))) else
    match ← Req.request (.writeRefused f.id) with
    | some e => Pure.pure (.error (sysReturn s (errRet e.val) [] []))
    | none =>
      match writeSignal s SIGXFSZ with
      | .running s' _ => Pure.pure (.error (sysReturn s' (errRet EFBIG) [] []))
      | r => Pure.pure (.error r)
  | _ => Pure.pure (.ok n)

/-- A write of `count` bytes from `buf` to the open file `f` (`fs/read_write.c` `vfs_write`), at the
open file's position (`off? = none`, `write`) or at offset `off?` (`pwrite64`). The open file must be
writable (`EBADF`), and `buf` and `count` must pass `access_ok` (`EFAULT`); for a file with pages, the offset (the
position for `write`, even with `O_APPEND`) and the count must stay below `2 ^ 63` (`rw_verify_area`,
`EINVAL`). The count is limited to `MAX_RW_COUNT`; the environment decides how many bytes the file
takes. A broken pipe sends `SIGPIPE` and returns `EPIPE` if the signal does not end the process (`fs/pipe.c` `pipe_write`). A regular file
with pages has the file size limit (`RLIMIT_FSIZE`) checked by the model before the buffer is read
(`fsizeLimit`); the environment's `fileTooBig` is then the file system's own size limit (`s_maxbytes`),
`EFBIG` without a signal. For another file whose write position is at or beyond the limit (a regular file
the model knows no pages of, `FileMap.other`), the environment's `fileTooBig` sends `SIGXFSZ` and returns
`EFBIG` if the signal does not end the process (`fs/read_write.c` `generic_write_check_limits`); with no
limit (`RLIM_INFINITY`) there is no signal, and `EFBIG` is the file system's own size limit.
The bytes written to a file with pages (`FileMap.pages`) go into its page cache at once
(`mm/filemap.c` `generic_perform_write`), where every mapping of the file sees them: they are
written into `Files` at the offset, or at the file's end with `O_APPEND`
(`generic_write_checks_count`, also for `pwrite64`), the file grows to cover them, and for `write` the
position ends after them (`written`); `pwrite64` leaves it. A file whose writing is denied
(`Files.denyWrite`) has no descriptor open for writing (`ETXTBSY` at `open`) and is not changed.
A buffer with a byte the kernel cannot read (for example on a page wholly beyond the end of a mapped file):
the kernel copies from it up to that byte at most (`copy_from_user` stops at the fault,
`lib/iov_iter.c`), the readable bytes before it (`readableLead`, which is all `n` when the kernel can read
them all). A file with pages takes a first
part of them, and none is `EFAULT` (`generic_perform_write`, which retries a short copy until it
fails without progress); what another file does is its own (`Request.writeFault`).
The kernel's reads of the buffer grow a stack where they must (`growFor`), but only for the bytes it
reads, which a file that takes part of them, or fails, leaves open (a pipe copies as much as it has
room for, a file system a part at a time): where the reads grew a stack (the state after them took
new backings, `Memory.fresh`), such an answer is not modelled.
Not modelled: taking data from a mapping of the file being written, not write-denied (the kernel
copies a page at a time and may read bytes it already wrote). -/
def writeFile (prof : Profile) (s : State) (f : OpenFile) (buf : Addr) (count : Nat) (off? : Option Nat) :
    Req StepResult := do
    if !f.writable then Pure.pure (sysReturn s (errRet EBADF) [] [])
    else if !accessOk prof.feat buf count then Pure.pure (sysReturn s (errRet EFAULT) [] [])
    else if f.map.isPages ∧ 2 ^ 63 ≤ off?.getD (s.proc.opens.pos f).offset + count then
      Pure.pure (sysReturn s (errRet EINVAL) [] [])
    else do
      match ← fsizeLimit s f (min count maxRwCount) off? with
      | .error r => Pure.pure r
      | .ok n =>
      let target := f.writeTarget s.proc.mm.mem.files
      let fresh₀ := s.proc.mm.mem.fresh
      let s ← growFor prof s .read buf n
      let grows := fresh₀ != s.proc.mm.mem.fresh
      let lead := readableLead prof.feat s buf n
      let bs := readBytes s.proc.mm.mem buf lead
      if target.any (s.proc.mm.mem.readsFile buf lead) then
        Pure.pure (.stopped (.notModelled (.feature "write from a mapping of the file written")))
      else if lead = n then do
        let r ← Req.request (.write f.id bs)
        answer s f target bs off? false grows r
      else
        match f.map with
        | .pages _ => do
          let r ← Req.request (.write f.id bs)
          answer s f target bs off? true grows r
        | _ => do
          let r ← Req.request (.writeFault f.id bs n)
          answer s f target bs off? false grows r
where
  /-- The state after the open file `f` took the bytes `bs`, none or more: for a file with pages, they
  are written at the offset (`off?`, else the position), or at the file's end with `O_APPEND`, into the
  file `target` unless its writing is denied, and for `off? = none` the position ends after them; other
  files keep what they take. -/
  written (s : State) (f : OpenFile) (target : Option FileId) (bs : List Byte) (off? : Option Nat) : State :=
    match f.map with
    | .pages id =>
      if bs = [] then s else
      let p := s.proc.opens.pos f
      let pos := if p.append then s.proc.mm.mem.files.size id else off?.getD p.offset
      let mem := s.proc.mm.mem
      let s' := match target with
        | some t => s.withMem { mem with files := mem.files.writeAt t pos bs }
        | none => s
      match off? with
      | none => s'.setFilePos f { p with offset := pos + bs.length }
      | some _ => s'
    | _ => s
  /-- The call's end for the answer `r` of the open file `f` (changing the file `target`) about the
  bytes `bs` the kernel read from the buffer, at `off?` as for `written`: it took the first `k` of them,
  or fails. `efault`: the copy stopped at a byte it cannot read, so a count of 0 is `EFAULT`. `grows`: the kernel's reads
  grew a stack, so an answer other than taking all of `bs` is not modelled. -/
  answer (s : State) (f : OpenFile) (target : Option FileId) (bs : List Byte) (off? : Option Nat) (efault grows : Bool)
      {n : Nat} :
      WriteResult n → Req StepResult
    | .wrote k _ =>
      if grows && k != bs.length then partGrown else
      if efault && k == 0 then Pure.pure (sysReturn s (errRet EFAULT) [] []) else
      Pure.pure (sysReturn (written s f target (bs.take k) off?) (BitVec.ofNat 64 k) (bs.take k) [])
    | .error e => if grows then partGrown else Pure.pure (sysReturn s (errRet e.val) [] [])
    | .brokenPipe =>
      if grows then partGrown else
      match writeSignal s SIGPIPE with
      | .running s' _ => Pure.pure (sysReturn s' (errRet EPIPE) [] [])
      | r => Pure.pure r
    | .fileTooBig =>
      if grows then partGrown else
      if (s.proc.signal.rlimits RLIMIT_FSIZE).cur = RLIM_INFINITY ∨ f.limitChecked s.proc.mm.mem.files then
        Pure.pure (sysReturn s (errRet EFBIG) [] [])
      else
        match writeSignal s SIGXFSZ with
        | .running s' _ => Pure.pure (sysReturn s' (errRet EFBIG) [] [])
        | r => Pure.pure r
  /-- A `write` that took part of a buffer for which the kernel may have grown a stack. -/
  partGrown : Req StepResult :=
    Pure.pure (.stopped (.notModelled (.feature "a write taking part of a buffer the kernel grew a stack for")))

/-- `write(fd, buf, count)` (`fs/read_write.c` `ksys_write`); `fd` is 32-bit. The descriptor must be
open (`EBADF`; one opened with `O_PATH` is not writable); the write is `writeFile` at the open file's
position. -/
def sysWrite (prof : Profile) (s : State) : Req StepResult := do
  match s.proc.files.desc (s.cpu.gpr.rdi.toNat % 2 ^ 32) with
  | none => Pure.pure (sysReturn s (errRet EBADF) [] [])
  | some f => writeFile prof s f s.cpu.gpr.rsi s.cpu.gpr.rdx.toNat none

/-- `lseek`'s `whence` (`include/uapi/linux/fs.h`): the new position counts from the file's start. -/
def SEEK_SET : Nat := 0
/-- `lseek`'s `whence`: the new position counts from the current one. -/
def SEEK_CUR : Nat := 1
/-- `lseek`'s `whence`: the new position counts from the file's end. -/
def SEEK_END : Nat := 2
/-- The largest `whence`, `SEEK_HOLE`; `SEEK_DATA` (3) and `SEEK_HOLE` (4) look for the next data or
hole. -/
def SEEK_MAX : Nat := 4

/-- `lseek(fd, offset, whence)` (`fs/read_write.c` `ksys_lseek`, `vfs_llseek`); `fd` and `whence` are
32-bit, `offset` a signed 64-bit `off_t`. The descriptor must be open and not `O_PATH` (`EBADF`;
`fdget_pos`, `FdTable.descNoPath`), and `whence` at most `SEEK_MAX` (`EINVAL`). For a file with pages
(`generic_file_llseek_size`): `SEEK_CUR` with offset 0 returns the position and leaves it; otherwise
the new position is the offset from the start, the position or the file's size, which must not be
negative (`EINVAL`; a sum at or past `2 ^ 63` wraps around to a negative `loff_t`), and past the file's
end must be one the file system accepts (`Request.seekPast`, else `EINVAL`); the position becomes it,
and it is the result. `SEEK_DATA` and `SEEK_HOLE` depend on the file system's holes: not modelled.
Every other file answers for itself (`Request.seek`), and its position is its own. -/
def sysLseek (s : State) : Req StepResult := do
  let off := s.cpu.gpr.rsi.toInt
  let whence := arg32 s.cpu.gpr.rdx
  let fail (e : Nat) : Req StepResult := Pure.pure (sysReturn s (errRet e) [] [])
  match s.proc.files.descNoPath (arg32 s.cpu.gpr.rdi) with
  | none => fail EBADF
  | some f =>
    if whence > SEEK_MAX then fail EINVAL
    else match f.map with
    | .pages id =>
      let p := s.proc.opens.pos f
      if whence = SEEK_CUR ∧ off = 0 then Pure.pure (sysReturn s (BitVec.ofNat 64 p.offset) [] [])
      else if whence > SEEK_END then Pure.pure (.stopped (.notModelled (.feature "lseek SEEK_DATA or SEEK_HOLE")))
      else
        let size := s.proc.mm.mem.files.size id
        let pos : Int := (if whence = SEEK_SET then 0 else if whence = SEEK_CUR then (p.offset : Int) else size) + off
        if pos < 0 ∨ 2 ^ 63 ≤ pos then fail EINVAL
        else do
          let ok ← if pos.toNat ≤ size then Pure.pure true else Req.request (.seekPast f.id pos.toNat)
          if ok then
            Pure.pure (sysReturn (s.setFilePos f { p with offset := pos.toNat }) (BitVec.ofNat 64 pos.toNat) [] [])
          else fail EINVAL
    | _ => do
      match ← Req.request (.seek f.id off whence) with
      | .error e => fail e.val
      | .ok pos => Pure.pure (sysReturn s (BitVec.ofNat 64 pos.val) [] [])

/-- Illegal seek: the file has no position (`include/uapi/asm-generic/errno-base.h`). -/
def ESPIPE : Nat := 29

/-- `pread64(fd, buf, count, pos)` (`fs/read_write.c` `ksys_pread64`, `vfs_read`); `fd` is 32-bit, `pos` a
signed 64-bit `loff_t`. A negative offset is `EINVAL`; the descriptor must be open and not `O_PATH`
(`EBADF`; `fdget`). A file with pages takes reads at an offset: it must be open for reading (`EBADF`),
`buf` and `count` must pass `access_ok` (`EFAULT`), and the read is `readPagesAt` the offset, with the
same failures as `read`'s; the position does not move. Another file may not take them (`ESPIPE`:
`Request.positional`); one that does is not modelled. -/
def sysPread64 (prof : Profile) (s : State) : Req StepResult := do
  let buf := s.cpu.gpr.rsi
  let count := s.cpu.gpr.rdx.toNat
  let pos := s.cpu.gpr.r10.toInt
  let fail (e : Nat) : Req StepResult := Pure.pure (sysReturn s (errRet e) [] [])
  if pos < 0 then fail EINVAL else
  match s.proc.files.descNoPath (arg32 s.cpu.gpr.rdi) with
  | none => fail EBADF
  | some f =>
    match f.map with
    | .pages id =>
      if !f.readable then fail EBADF
      else if !accessOk prof.feat buf count then fail EFAULT
      else readPagesAt prof s f id buf count pos.toNat fun _ s' => s'
    | _ =>
      let positional : Bool ← Req.request (.positional f.id false)
      if positional then
        Pure.pure (.stopped (.notModelled (.feature "pread64 of a file without pages")))
      else fail ESPIPE

/-- `pwrite64(fd, buf, count, pos)` (`fs/read_write.c` `ksys_pwrite64`); `fd` is 32-bit, `pos` a signed
64-bit `loff_t`. A negative offset is `EINVAL`; the descriptor must be open and not `O_PATH` (`EBADF`;
`fdget`). A file with pages takes writes at an offset: the write is `writeFile` at the offset (with
`O_APPEND` at the file's end), and the position does not move. Another file may not take them
(`ESPIPE`: `Request.positional`); one that does is not modelled. -/
def sysPwrite64 (prof : Profile) (s : State) : Req StepResult := do
  let pos := s.cpu.gpr.r10.toInt
  let fail (e : Nat) : Req StepResult := Pure.pure (sysReturn s (errRet e) [] [])
  if pos < 0 then fail EINVAL else
  match s.proc.files.descNoPath (arg32 s.cpu.gpr.rdi) with
  | none => fail EBADF
  | some f =>
    match f.map with
    | .pages _ => writeFile prof s f s.cpu.gpr.rsi s.cpu.gpr.rdx.toNat (some pos.toNat)
    | _ =>
      let positional : Bool ← Req.request (.positional f.id true)
      if positional then
        Pure.pure (.stopped (.notModelled (.feature "pwrite64 of a file without pages")))
      else fail ESPIPE

end ZellicX86
