import ZellicX86.Spec.Statement
/-!
# Statement vocabulary: the C library's streams (stdio)

A library layer over the statement vocabulary (`Spec/Statement.lean`): the C library's streams (C17 7.21, `FILE *`)
as contracts see them, without the library's representation of them. A C program writes to a stream (`printf`, `puts`,
`fwrite`) and the library hands the bytes to the stream's descriptor later, in one or more `write`s: when its buffer
is full, at a newline for a line-buffered stream, at `fflush`, or when the program ends by `exit` (C17 7.21.3p3, which
leaves the buffer's size and when "as a block" happens to the implementation; 7.22.4.4: `exit` flushes every open
stream with unwritten buffered data and closes them all). Reading, it may read more of the descriptor than the program
has taken from the stream yet (read-ahead), which `exit` gives back where the file can seek (POSIX.1-2024, `exit` and
`fclose`: the descriptor's offset set to the stream's position).

So a stream is abstractly (`Stream`): the descriptor it is on, the bytes written to it that the library has not yet
written to the descriptor (`out`), the bytes the library has read from the descriptor that the program has not yet
taken (`ahead`), and its error and end-of-file indicators. Its buffering mode and buffer size are not part of it: a
contract lets the library write pending bytes at any time, in order, so what a program wrote is exact at `fflush` and
at `exit` and, before, the bytes written so far followed by the pending ones (`Output fd evs ++ out`).

The library's representation of its streams (their `FILE`s, the list of them, their buffers, blocks of its own
`malloc`) is the library's state, in the memory its runtime owns (`Spec/Lib/C/Runtime.lean`'s `Ghost.own`); the open
streams as this model has them are a part of the runtime's ghost (`Ghost.streams`), which its invariant relates to that
state. A statement that quantifies over the library holds for every library keeping its contracts, whatever it keeps
there.

What `exit` does with them (`Streams.Closes`, used by `Spec/Lib/C/Start.lean`'s exit contract): each stream's pending
bytes written to its descriptor, all of them unless one of the `write`s failed, and its read-ahead, where it has some,
given back by `lseek(fd, -n, SEEK_CUR)`; the streams' events in any order and interleaved (glibc 2.43 flushes the streams one after
the other in `_IO_flush_all` and gives back read-ahead in the same loop and again in `_IO_unbuffer_all`, both in
`libio/genops.c`).

Not covered: the functions on streams (`fopen`, `fputs`, `printf`, …); streams not on a descriptor (`fmemopen`,
`open_memstream`, `fopencookie`); wide-oriented streams; a stream not opened write-only that was written to after the
library had read ahead on its descriptor, by the program's reads or by a positioning call (glibc 2.43's
`_IO_new_file_seekoff` reads the block around a target outside its buffer): the library's position on the descriptor is
then past the place of its pending output, and glibc's flush `lseek`s back to that place before the `write`
(`libio/fileops.c`, `new_do_write`) and on the `lseek`'s failure writes nothing, neither of which `Stream.Closes`
allows (defined C with a positioning call between a read and the write, C17 7.21.5.3p7; undefined without one). Not
covered either: other threads (every stream is used by one thread). A library
counts bytes pushed back with `ungetc` in `ahead` (glibc's `_IO_new_file_sync` seeks back over its backup area too).
-/
namespace ZellicX86.C

/-- A C stream (C17 7.21.3) as contracts see it, without the library's representation of it:
- `fd`: the descriptor it is on (`fileno`);
- `out`: the bytes written to the stream that the library has not yet written to `fd` (its pending output);
- `ahead`: the bytes the library has read from `fd` that the program has not yet read from the stream (its read-ahead);
- `err`, `eof`: its error and end-of-file indicators (`ferror`, `feof`; C17 7.21.10). -/
structure Stream where
  fd : Nat
  out : List Byte := []
  ahead : List Byte := []
  err : Bool := false
  eof : Bool := false

/-- A library's open streams, each by its `FILE *`. -/
abbrev Streams := List (Addr × Stream)

/-- No stream of `σ` has pending output or read-ahead: closing them writes nothing and moves no descriptor. -/
def Streams.Quiet (σ : Streams) : Prop := ∀ p ∈ σ, p.2.out = [] ∧ p.2.ahead = []

/-- `ev` is a `write` to descriptor `fd` (number 1 in `rax`'s low 32 bits; `rdi`'s low 32 bits `fd`, as the kernel reads
them), of any buffer and length: the bytes it took are `Event.wrote fd ev`. -/
def Event.IsWriteTo (ev : Event) (fd : Nat) : Prop :=
  arg32 ev.nr = 1 ∧ ev.args.head?.map arg32 = some fd ∧ ev.toProc = []

/-- `ev` is `lseek(fd, -n, SEEK_CUR)` (number 8, `sysLseek`; `rdi`'s and `rdx`'s low 32 bits `fd` and `SEEK_CUR`, as
the kernel reads them, `rsi` the offset `-n`): the descriptor's position moved back by `n` bytes, where it can seek. -/
def Event.IsSeekBack (ev : Event) (fd n : Nat) : Prop :=
  arg32 ev.nr = 8 ∧ (∃ d w, ev.args.take 3 = [d, BitVec.ofInt 64 (-(n : Int)), w] ∧ arg32 d = fd ∧ arg32 w = SEEK_CUR) ∧
    ev.fromProc = [] ∧ ev.toProc = []

/-- The events `es` are a start of closing the stream `st`: each a `write` to its descriptor, where it has pending
output, or the return of its read-ahead (`lseek(fd, -n, SEEK_CUR)`, `n` the read-ahead's length), where it has some; and
the bytes the `write`s took, in order, a first part of its pending output. A stream with nothing pending and nothing
read ahead is closed without a system call. -/
def Stream.Flushing (st : Stream) (es : List Event) : Prop :=
  (∀ ev ∈ es, (Event.IsWriteTo ev st.fd ∧ st.out ≠ []) ∨ (Event.IsSeekBack ev st.fd st.ahead.length ∧ st.ahead ≠ [])) ∧
    Output st.fd es <+: st.out

/-- The events `es` close the stream `st` as `exit` does (C17 7.22.4.4; POSIX.1-2024 `exit`, whose closing of the
streams sets the descriptor's offset to the stream's position where the file can seek; `fclose`, C17 7.21.5.1, would
also close the descriptor, which `exit` leaves to the process's end): a start of closing it (`Stream.Flushing`) that
wrote all its pending output, or one of whose `write`s failed (`Event.Failed`; the library gives up on the rest, as
glibc 2.43's `_IO_new_file_write` does), and that gave back its read-ahead where it has some (an `lseek`, which may
fail where the file cannot seek). -/
def Stream.Closes (st : Stream) (es : List Event) : Prop :=
  st.Flushing es ∧ (Output st.fd es = st.out ∨ ∃ ev ∈ es, Event.IsWriteTo ev st.fd ∧ ev.Failed) ∧
    (st.ahead ≠ [] → ∃ ev ∈ es, Event.IsSeekBack ev st.fd st.ahead.length)

/-- The events `evs` are those of the streams of `σ`, each as `F` says of it, in any order and interleaved: each event
belongs to one stream (`owner`, its index in `σ`), and the events of each stream, in their order, satisfy `F`. -/
def Streams.Each (F : Stream → List Event → Prop) (σ : Streams) (evs : List Event) : Prop :=
  ∃ owner : List Nat, owner.length = evs.length ∧ (∀ i ∈ owner, i < σ.length) ∧
    ∀ i (h : i < σ.length), F σ[i].2 ((evs.zip owner).filterMap fun p => if p.2 = i then some p.1 else none)

/-- The events `evs` close the streams `σ` (`Stream.Closes`, each stream's events in any order and interleaved):
what `exit` does with them. -/
def Streams.Closes (σ : Streams) (evs : List Event) : Prop := Streams.Each Stream.Closes σ evs

/-- The events `evs` are a start of closing the streams `σ` (`Stream.Flushing`, interleaved): where the process ends
in one of the `write`s. -/
def Streams.Flushing (σ : Streams) (evs : List Event) : Prop := Streams.Each Stream.Flushing σ evs

end ZellicX86.C
