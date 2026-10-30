import ZellicX86.Spec.Lib.C.Runtime
/-!
# Statement vocabulary: the C library's `read`, `write` and `_exit`

A library layer over the statement vocabulary (`Spec/Statement.lean`): what a C library's `read(fd, buf, n)` and
`write(fd, buf, n)` do, as contracts over the library's runtime (`Runtime`, `Spec/Lib/C/Runtime.lean`), for any
library that keeps them. POSIX.1-2024 (`read`, `write`) describes them as the system calls of the same names: the C
function passes its arguments to the kernel and returns what the kernel returned, or `-1` with the error in `errno`.
That is what glibc 2.43 does (`io/read.c`, `io/write.c`, through `SYSCALL_CANCEL` and `__syscall_cancel`,
`nptl/cancellation.c`) and musl 1.2.5 (`src/unistd/read.c`, `write.c`, `syscall_cp` and `__syscall_ret`), each in one
system call. So each contract says:

- the call makes exactly one system call, the `read` or `write` of the arguments (`Event.IsRead`,
  `Event.IsWriteFault`): `fd` as the kernel reads the C `int` (the low 32 bits of `rdi`), `buf` (`rsi`) and `n`
  (`rdx`, a `size_t`);
- it returns the call's result where the call succeeded, and `-1` with the call's error number in `errno` where it
  failed (`SysResult`): `-1` or a count of at most `n`; `errno` is otherwise unspecified (C17 7.5 lets a library
  function set it on success too);
- `read`: the bytes it delivered are at `buf` at the return; for a descriptor open for reading on the pages of a file
  (a regular file), they are the file's bytes from the description's position, as many as the count it returned, at
  most as many as there are from it, none only at the file's end (or for `n = 0`) or where the call failed, and the
  position moved past them (`ReadFile`, over the returned count, `retCount`); it writes to no file, so its frame keeps
  every file (`KeepsFilesBut`);
- `write`: it took the first bytes of `buf` that the call reports (`Event.IsWriteFault`: those the buffer held at the
  call); it writes to the file `fd` is on and no other (`Contract.writesTo`), so its frame keeps every other file; it
  may end the process the way the kernel's `write` does (`SIGPIPE`, `SIGXFSZ`), or, where the thread blocks the
  signal, leave it pending and return the error (`EPIPE`, `EFBIG`; `Contract.pends`);
- each is a function over the library's runtime (`Runtime.call`, `Spec/Lib/C/Runtime.lean`), for every ghost `g` at the
  call: the library's invariant at the call and again at the return (its memory possibly other, `Heap.Next`), the stack
  below the call's `rsp` the function uses (`Runtime.readStack`, `writeStack`), `errno` and, for `read`, the buffer it
  fills are all it writes besides the library's own memory; the program's blocks outside that buffer and their pages
  are kept (`KeepsLive`); the position of `fd`'s open file description is all it moves of the process's state. A
  library may change its own state in them (as one that switches a thread's cancellation state around the system
  call does).

`_exit(status)` (`C._exit`; POSIX.1-2024 `_exit`, C17 7.22.4.5 `_Exit`) ends the process at once with the status's low
byte: by `exit_group`, so every thread ends (Linux's `exit` system call would end only the calling thread), without
flushing streams or running `atexit` handlers (that is `exit`'s, `Spec/Lib/C/Start.lean`'s `CStart.exit`). glibc 2.43
(`sysdeps/unix/sysv/linux/_exit.c`) and musl 1.2.5 (`src/exit/_Exit.c`) make `exit_group` first.

Not promised: that a `read` delivers all that was asked for up to the file's end (the kernel may deliver less where
reading the file's pages fails). A variant of `read` could promise it, `count = min n (size - pos)`, under an
environment that assumes no read of the file's pages fails (`Contract.env := fun _ o => Undisturbed o ∧ ReadsWhole o`);
`read` does not, so a client that relies on one full read of a small file cannot get it from `read`. Nor promised:
anything about the position of a descriptor on a pipe or a terminal; that `errno` is kept on success (glibc keeps
it; a C library need not); the bytes of the buffer past the count it returned, or of the whole buffer where it failed
(it may write all `n`: Linux leaves them as they were, a library need not).

-/
namespace ZellicX86.C

/-- `X` is the return of a function of the library `L` that made the system call `ev` and returns the call's result as
POSIX's `read` and `write` do: the call's result where it succeeded, and `-1` where it failed (`Event.Failed`), with
the error number it returned (`errRet e`, `-e`) in `errno` (`Runtime.errno`). -/
def SysResult (L : Runtime) (ev : Event) (X : State) : Prop :=
  (¬ ev.Failed ∧ X.cpu.gpr.rax = ev.ret) ∨ (ev.Failed ∧ X.cpu.gpr.rax = -1 ∧ ev.ret = errRet (L.errno X))

/-- The count a C function returning `ssize_t` (`read`, `write`) returns in `r`: `r` as a count, and 0 where `r` read as a
signed 64-bit integer is negative (`-1`, an error). -/
def retCount (r : BitVec 64) : Nat := if r.toInt < 0 then 0 else r.toNat

/-- What `read(fd, buf, n)`, called in `s` and returning at `X`, did to the file it read, if `fd` was open for reading
on the pages of a file (`FileMap.pages`: a regular file) in `s`: the bytes whose count it returned (`retCount`) are at
`buf` in `X`, and they are the file's from the open file description's position on (`Files.bytes`), at most as many
as there are from there; the position in `X` lies past them; and it returned 0 only where it failed (`-1`), was asked
for no bytes, or the position was at the file's end (`sysRead`'s `readPages`, `mm/filemap.c`'s `filemap_read`). -/
def ReadFile (s X : State) (fd : Nat) (buf : Addr) (n : Nat) : Prop :=
  ∀ d f, s.proc.files.desc fd = some d → d.readable = true → d.map = .pages f →
    (X.proc.opens.pos d).offset = (s.proc.opens.pos d).offset + retCount X.cpu.gpr.rax ∧
    readBytes X.proc.mm.mem buf (retCount X.cpu.gpr.rax) =
      s.proc.mm.mem.files.bytes f (s.proc.opens.pos d).offset (retCount X.cpu.gpr.rax) ∧
    retCount X.cpu.gpr.rax ≤ s.proc.mm.mem.files.size f - (s.proc.opens.pos d).offset ∧
    (retCount X.cpu.gpr.rax = 0 →
      X.cpu.gpr.rax = -1 ∨ n = 0 ∨ s.proc.mm.mem.files.size f ≤ (s.proc.opens.pos d).offset)

/-- The buffer of a call `read(fd, buf, n)` or `write(fd, buf, n)` from `s`: `n` bytes (`rdx`) at `buf` (`rsi`). -/
def ioBuf (s : State) : Rgn := ⟨s.cpu.gpr.rsi, s.cpu.gpr.rdx.toNat⟩

/-- The C library `L`'s `read(fd, buf, n)` (`fd` in `edi`, `buf` in `rsi`, `n` in `rdx`; POSIX.1-2024 `read`) at the
ghost `g`, on a processor with features `feat`, as a contract over the runtime (`Runtime.call`): with its stack
(`Runtime.readStack` bytes below `rsp`) apart from the buffer, the buffer apart from `errno` and from what the library
reads without owning it, and holding none of the library's own data outside the program's blocks (`InLive`), it writes at most its stack, `errno` and the buffer (and the
library's memory), moves at most the position on `fd` (the descriptor as the kernel reads it, `arg32`), writes to no
file, and returns with the library's invariant, the program's blocks outside the buffer and their pages kept
(`KeepsLive`), `-1` or a count of at most `n` returned and, for a file it read, what `ReadFile` says; having made
exactly one system call `ev`, a `read` of `n` bytes from `fd` into `buf` (`Event.IsRead`), whose result it returns
(`SysResult`) and whose bytes are at `buf` at the return. -/
def read (L : Runtime) (feat : Features) (g : Ghost) : Contract :=
  L.call feat g
    { stack := L.readStack
      writes := fun s => [ioBuf s]
      pre := fun s => Apart [frame s L.readStack] [ioBuf s] ∧ Apart [ioBuf s] [L.errnoLoc s] ∧ InLive g (ioBuf s) ∧
        Apart [ioBuf s] (L.reads s.cpu.seg.fsBase)
      post := fun s X => KeepsLive g.live [ioBuf s] s X ∧
        (X.cpu.gpr.rax = -1 ∨ X.cpu.gpr.rax.toNat ≤ s.cpu.gpr.rdx.toNat) ∧
        ReadFile s X (arg32 s.cpu.gpr.rdi) s.cpu.gpr.rsi s.cpu.gpr.rdx.toNat
      events := fun s X evs => ∃ ev, evs = [ev] ∧ ev.IsRead (arg32 s.cpu.gpr.rdi) s.cpu.gpr.rsi s.cpu.gpr.rdx.toNat ∧
        SysResult L ev X ∧ readBytes X.proc.mm.mem s.cpu.gpr.rsi ev.toProc.length = ev.toProc
      moves := fun s => [arg32 s.cpu.gpr.rdi] }

/-- The C library `L`'s `write(fd, buf, n)` (`fd` in `edi`, `buf` in `rsi`, `n` in `rdx`; POSIX.1-2024 `write`) at the
ghost `g`, on a processor with features `feat`, as a contract over the runtime (`Runtime.call`): with its stack
(`Runtime.writeStack`) apart from the buffer, the buffer apart from `errno` (which the call writes; the buffer may lie
over what the library reads, as two things read), a descriptor whose `write` puts its bytes
into no memory the process maps (`WriteUnmapped`), and the signals the kernel sends in a `write` it does not complete
(`SIGPIPE`, `SIGXFSZ`) not handled (ignored or by default; blocked or not), it reads the buffer, writes at most its stack
and `errno` (and the library's memory), moves at most the position on `fd`, writes to no file but the one `fd` is on
(`writesTo`), may leave those two signals pending (`pends`: the kernel queues a blocked one, `kernel/signal.c`'s
`sig_ignored`, and the `write` returns `EPIPE` or `EFBIG`), and either returns with the library's invariant, the program's blocks and their pages kept (`KeepsLive`), and `-1` or a
count of at most `n` returned, having made exactly one system call `ev`, a `write` to `fd` of the first bytes of the `n`
the buffer holds at the call (`Event.IsWriteFault`), whose result it returns (`SysResult`); or the process is killed in
that `write` (`Outcome.KilledInWrite`), with no event. -/
def write (L : Runtime) (feat : Features) (g : Ghost) : Contract :=
  L.call feat g
    { stack := L.writeStack
      reads := fun s => [ioBuf s]
      pre := fun s => Apart [frame s L.writeStack] [ioBuf s] ∧ Apart [ioBuf s] [L.errnoLoc s] ∧
        WriteUnmapped s (arg32 s.cpu.gpr.rdi) ∧
        ((s.proc.sighand Signal.SIGPIPE).disp = .ignore ∨ (s.proc.sighand Signal.SIGPIPE).disp = .default) ∧
        ((s.proc.sighand Signal.SIGXFSZ).disp = .ignore ∨ (s.proc.sighand Signal.SIGXFSZ).disp = .default)
      post := fun s X => KeepsLive g.live [] s X ∧ (X.cpu.gpr.rax = -1 ∨ X.cpu.gpr.rax.toNat ≤ s.cpu.gpr.rdx.toNat)
      events := fun s X evs => ∃ ev, evs = [ev] ∧
        ev.IsWriteFault (arg32 s.cpu.gpr.rdi) s.cpu.gpr.rsi s.cpu.gpr.rdx.toNat
          (readBytes s.proc.mm.mem s.cpu.gpr.rsi s.cpu.gpr.rdx.toNat) ∧ SysResult L ev X
      ends := fun _ out evs => out.KilledInWrite ∧ evs = []
      pends := fun _ => [Signal.SIGPIPE, Signal.SIGXFSZ]
      moves := fun s => [arg32 s.cpu.gpr.rdi]
      writesTo := fun s => [arg32 s.cpu.gpr.rdi] }

/-- The C library's `_exit(status)` (`status` in `edi`; POSIX.1-2024 `_exit`, C17 7.22.4.5 `_Exit`), as a contract:
called under `sysv`, it never returns, writes nothing but its return address's slot, and ends the process by
`exit_group` with the low byte of `status` (the kernel keeps `status & 0xff`, `kernel/exit.c`'s `do_group_exit`),
making no system call before. -/
def _exit : Contract where
  conv := sysv
  reads _ := []
  writes s := [frame s 0]
  pre _ := True
  post _ _ := False
  events _ _ evs := evs = []
  ends s out evs := out = .exited .exitGroup (s.cpu.gpr.rdi.setWidth 8) ∧ evs = []

/-- The code segments `code` implement, at `entry` on processor `prof`, the C library `L`'s `read` (`read`) at every
ghost. -/
def ReadAt (L : Runtime) (prof : Profile) (entry : Addr) (code : List (Addr × List Byte)) : Prop :=
  ∀ g, ImplementsCall prof entry code (read L prof.feat g)

/-- The code segments `code` implement, at `entry` on processor `prof`, the C library `L`'s `write` (`write`) at every
ghost. -/
def WriteAt (L : Runtime) (prof : Profile) (entry : Addr) (code : List (Addr × List Byte)) : Prop :=
  ∀ g, ImplementsCall prof entry code (write L prof.feat g)

end ZellicX86.C
