import ZellicX86.Spec.Lib.C.Errno
import ZellicX86.Spec.Lib.C.Stdio
/-!
# Statement vocabulary: a C library's runtime

A library layer over the statement vocabulary (`Spec/Statement.lean`): a C library as its functions' contracts see it,
without its code. A program's statement about its calls of library functions (`Spec/Lib/C/Unistd.lean`'s `read` and
`write`, `Spec/Lib/C/Malloc.lean`'s `malloc` and `free`) holds for every library that keeps those contracts; which
library a binary contains is settled by proving that its code keeps them (for a static binary, from the library's
objects), not by the statement.

What a library keeps between its functions' calls is its business: its global data (glibc's
`__libc_single_threaded`, its `atexit` list), the calling thread's control block (glibc's `struct pthread` at the thread
pointer), its allocator's heap and the program break it keeps track of (glibc's `__curbrk`), its streams' `FILE`s and
their buffers. Much of it lies where the run puts it: the heap grows where the kernel maps memory, the streams' buffers
and the blocks the library's startup and exit allocate are blocks of its own `malloc`. So a statement does not name
those regions; it carries them as a ghost (`Ghost`), from call to call, as an allocator's callers carry what it owns
(`Heap`, `Heap.Next`):

- `own`: the memory the library owns, wherever the run put it; it may include memory the library made read-only (the
  data its startup relocated and then protected), and memory it may change the layout of (map, unmap, re-protect) in
  its calls;
- `live`: the blocks of its `malloc` the program holds, inside `own`;
- `libLive`: the blocks of its `malloc` its own side holds (its startup and exit objects, the toolchain's included: its
  streams' buffers, what its startup allocates), which its allocator counts in use as it counts the program's; where
  they lie (inside `own`, apart from the program's blocks) is its invariant's to say;
- `streams`: its open streams, as the program sees them (`Spec/Lib/C/Stdio.lean`).

A library instance (`Runtime`) has an abstract invariant over the ghost and what the library sees of the process
(`Heap.View`: the bytes it owns outside the program's blocks, the accesses there, the program break, the `FS` base, the
bytes it reads without owning them). A statement that quantifies over the library holds for every library keeping its
contracts, whatever it keeps and whatever its invariant says. Every function over the runtime (`Runtime.call`: the
library's functions, and the program's functions that call them) assumes the invariant at the call and promises it at
the return for the ghost at the return, which may own other memory (`Heap.Next`: what it owned, or memory mapped
since); a program's code keeps it by not storing into what the library owns outside the program's blocks. The
library's startup gives the first ghost and its exit takes the last (`Spec/Lib/C/Start.lean`).

The allocator is a part of the runtime: `Runtime.heap L g` is the allocator (`Heap`) the library is at the ghost `g`,
whose invariant is the runtime's, so that `malloc` and `free` are the core allocator contracts over it
(`Spec/Lib/C/Malloc.lean`) and keep the whole library's invariant.

The instance also fixes where `errno` lies (`errnoOff`, `Spec/Lib/C/Errno.lean`), how much stack each of its functions
uses below the stack pointer at a call (`readStack`, `writeStack`, `heapStack`: a constant per function, not
a bound that depends on the call), its blocks' alignment and its standard streams. A
function's stack is assumed mapped at the call (the contracts' footprint): a call that would grow the main thread's
stack is not covered.

Not covered: other threads (every function here is called from the only thread); a signal handler that calls the
library while the interrupted code is inside it.
-/
namespace ZellicX86.C

/-- What a statement tracks of a C library between its calls, besides the machine state: what the run has placed.
- `own`: the memory the library owns (its data, its threads' control blocks, its heap with the blocks it holds itself,
  its streams' state), wherever the run put it;
- `live`: the blocks of its `malloc` the program holds (each inside `own`); none unless given;
- `libLive`: the blocks of its `malloc` the library's side holds (its startup and exit objects, the toolchain's
  included), wherever the run put them; none unless given. A static glibc 2.43 program's: its streams' buffers
  (`libio/filedoalloc.c`), what its startup allocates (`_dl_get_origin`, `sysdeps/unix/sysv/linux/dl-origin.c`;
  `_dl_init_paths`, `elf/dl-load.c`; `_dl_find_object_init`, `elf/dl-find_object.c`) and libgcc's frame registry's
  b-tree nodes (`btree_allocate_node`, from crtbeginT.o's `frame_dummy`). Like `live`, its allocator counts them in use; unlike
  `live`, they are the library's data, which its invariant sees (`Runtime.Holds`) and the program does not write. A
  program's `malloc` and `free` keep them (`Runtime.heap`); the functions that allocate or free them (the stream
  functions, the startup, the exit's handlers) must say so in their contracts. That they lie inside `own` and apart
  from `live` is the library's invariant's to say;
- `streams`: its open streams, by `FILE *` (`Streams`); none unless given. -/
structure Ghost where
  own : List Rgn
  live : List Rgn := []
  libLive : List Rgn := []
  streams : Streams := []

/-- A C library as its functions' contracts see it, without its code:
- `errnoOff`: the offset of its `errno` from the `FS` base (`Spec/Lib/C/Errno.lean`);
- `readStack`, `writeStack`, `heapStack`: the bytes of stack below the stack pointer at a call that its `read`, its
  `write`, and its `malloc` and `free` use at most (their frames and those of the functions they call: glibc 2.43's
  `read` and `write` use 56 each, the frames of `__libc_read` and `__syscall_cancel` with the return address and the
  call's number between them);
- `align`: the alignment of the blocks its `malloc` returns (16 for glibc's on x86-64, `MALLOC_ALIGNMENT` in
  `sysdeps/generic/malloc-alignment.h`);
- `stdin`, `stdout`, `stderr`: the streams a program starts with (C17 7.21.3p7), by their `FILE *` (glibc 2.43's
  `_IO_2_1_stdin_`, `_IO_2_1_stdout_`, `_IO_2_1_stderr_` in a static program, `libio/stdfiles.c`); 0 unless given;
- `reads fs`: the regions it reads without owning them, for the thread whose `FS` base is `fs` (data of others it
  depends on, which others may change between its calls); none unless given;
- `inv g v`: its invariant over the ghost `g` and what it sees of the process (`v`). Abstract: a statement that
  quantifies over the library holds for every library keeping its contracts, whatever it keeps. Unless given: no stream
  ever holds anything (`Streams.Quiet`), a library without buffered streams, whose exit writes nothing. -/
structure Runtime where
  errnoOff : Nat
  readStack : Nat := 0
  writeStack : Nat := 0
  heapStack : Nat := 0
  align : Nat := 1
  stdin : Addr := 0
  stdout : Addr := 0
  stderr : Addr := 0
  reads : Addr → List Rgn := fun _ => []
  inv : Ghost → Heap.View → Prop := fun g _ => g.streams.Quiet

/-- The streams a program starts with (C17 7.21.3p7, POSIX.1-2024 `stdin`): standard input, output and error of the
library `L` on descriptors 0, 1 and 2, with nothing pending or read ahead and both indicators clear. -/
def Runtime.initial (L : Runtime) : Streams :=
  [(L.stdin, { fd := 0 }), (L.stdout, { fd := 1 }), (L.stderr, { fd := 2 })]

/-- `errno` of the library `L` in the thread of `s` (`errnoLoc` at `L.errnoOff`). -/
abbrev Runtime.errnoLoc (L : Runtime) (s : State) : Rgn := C.errnoLoc L.errnoOff s

/-- The value of `errno` of the library `L` in `s` (`C.errno` at `L.errnoOff`). -/
abbrev Runtime.errno (L : Runtime) (s : State) : Nat := C.errno L.errnoOff s

/-- The library `L` at the ghost `g` as an allocator (`Heap`): its `malloc`'s and `free`'s stack and alignment, what it
reads without owning it, `errno` as the only bytes it changes without owning them, and its
invariant for what it owns and the live blocks: `L.inv` of `g` with those (its other parts, the blocks the library
holds itself and the streams, as in `g`). Its live blocks are the program's: a program's `malloc` adds its block to
them and keeps the library's own blocks (`g.libLive`), a program's `free` removes one of the program's. -/
def Runtime.heap (L : Runtime) (g : Ghost) : Heap where
  stack := L.heapStack
  align := L.align
  reads := L.reads
  writes fs := [errnoAt L.errnoOff fs]
  inv own v live := L.inv { g with own, live } v

/-- The invariant of the library `L` holds in `s` for the ghost `g`, on a processor with features `feat`: `L.inv` of
`g` and what the library sees of `s` (`Heap.view`: the bytes of `g.own` outside the program's blocks `g.live`, those of
the blocks the library holds itself among them, the accesses there, the break, the `FS` base, the bytes of
`L.reads`). -/
def Runtime.Holds (L : Runtime) (feat : Features) (g : Ghost) (s : State) : Prop :=
  (L.heap g).inv g.own ((L.heap g).view feat g.own s g.live) g.live

/-- What a call into the library `L` at the ghost `g` needs of its caller in `s`, on a processor with features `feat`,
for a call that uses `k` bytes of stack below `rsp`: the library's invariant (`Runtime.Holds`), that stack apart from
what the library owns, the program's blocks inside what it owns, `PKRU` allowing access with key 0 (the library may map
memory, which gets key 0), what the library reads without owning it and `errno` apart from that stack and from what it
owns (so stores there keep what it reads, and its own stores leave what it reads alone), and what it reads apart from
`errno`. -/
def Runtime.Ready (L : Runtime) (feat : Features) (g : Ghost) (k : Nat) (s : State) : Prop :=
  L.Holds feat g s ∧ Apart [frame s k] g.own ∧ (∀ a, Foot g.live a → Foot g.own a) ∧ s.cpu.pkru &&& 3 = 0 ∧
    Apart (L.reads s.cpu.seg.fsBase ++ [L.errnoLoc s]) (frame s k :: g.own) ∧
    Apart (L.reads s.cpu.seg.fsBase) [L.errnoLoc s]

/-- Every byte of the region `r` that the library owns (in `g.own`) lies in a block the program holds (`g.live`): `r`
holds none of the library's own data, so a function may write it and keep the library's invariant. -/
def InLive (g : Ghost) (r : Rgn) : Prop := ∀ a, r.Mem a → Foot g.own a → Foot g.live a

/-- From `s` to `X`, the bytes of the blocks `live` outside the regions `ws` are as they were, and every page holding a
byte of the blocks keeps its mapping (`KeepsPages`): what a function that writes `ws` promises of the program's blocks
(a function over the runtime may change the layout of what the library owns, in which they lie). -/
def KeepsLive (live ws : List Rgn) (s X : State) : Prop :=
  (∀ a, Foot live a → ¬ Foot ws a → X.proc.mm.mem.readByte a = s.proc.mm.mem.readByte a) ∧ KeepsPages live s X

/-- What a function over a C library's runtime says of itself besides the runtime (`Runtime.call`), as `Heap.Use` for an
allocator's client: the bytes of stack it uses below its entry `rsp` with those of the library's functions it calls
(`stack`), the regions it reads and writes besides its stack and `errno` (`reads`, `writes`, functions of the entry
state; none unless given), its precondition `pre` (`True` unless given), its postcondition `post` about the entry and
the return state, and, as in a `Contract` (whose fields of the same names they become):
- `live`: the program's blocks at the return, from those at the call and the entry and return states; the same as at the
  call unless given;
- `events`: what its system calls are, about the entry and the return state; only an allocator's memory calls
  (`Event.IsMemCall`) unless given;
- `ends`: how it may end the process (`Contract.ends`); never unless given;
- `sets`, `pends`, `moves`, `writesTo`: the thread's settings it may change, the signals it may leave pending (a
  `write`'s `SIGPIPE` and `SIGXFSZ`, where the thread blocks them), the descriptors whose positions it may move and
  those whose files it may change; none unless given;
- `env`: what it assumes of the environment while it runs (`Contract.env`); `Undisturbed` unless given. -/
structure Fn where
  stack : Nat
  reads : State → List Rgn := fun _ => []
  writes : State → List Rgn := fun _ => []
  pre : State → Prop := fun _ => True
  post : State → State → Prop
  live : List Rgn → State → State → List Rgn := fun live _ _ => live
  events : State → State → List Event → Prop := fun _ _ evs => ∀ ev ∈ evs, Event.IsMemCall ev
  ends : State → Outcome → List Event → Prop := fun _ _ _ => False
  sets : State → List Setting := fun _ => []
  pends : State → List Signal := fun _ => []
  moves : State → List Nat := fun _ => []
  writesTo : State → List Nat := fun _ => []
  env : State → Oracle → Prop := fun _ => Undisturbed

/-- The contract of a function `u` over the C library `L` at the ghost `g` (a function of the library's, or of the
program's that calls them), on a processor with features `feat`: called under `sysv` ready to call into the library
with its stack of `u.stack` bytes below `rsp` (`Runtime.Ready`: the library's invariant, the stack apart from what the
library owns, `PKRU`, …) and with `u.pre`, it reads
`L.reads` and `u.reads`, writes at most its stack, `errno` and `u.writes`, may change the bytes and the layout of what
the library owns, map new memory in pages unmapped at the call, and move the program break (`Layout.owns`, `KeepsEnvOut`:
every other mapping stays as it was; the library's memory is the library's business), and
returns with the invariant holding again for the program's blocks `u.live` gives, the library owning memory that arose
from what it owned as `Heap.Next` allows (`Heap.Intact`; the blocks it holds itself and its streams as at the call),
and `u.post`; its events, ends,
settings, pending signals, positions, files and environment are `u`'s. What it promises about the program's blocks (their bytes, their
pages: `KeepsLive`) and how its own regions lie relative to the library's memory (`InLive`) are in `u.pre` and
`u.post`. -/
def Runtime.call (L : Runtime) (feat : Features) (g : Ghost) (u : Fn) : Contract where
  conv := sysv
  reads s := (L.heap g).reads s.cpu.seg.fsBase ++ u.reads s
  writes s := frame s u.stack :: ((L.heap g).writes s.cpu.seg.fsBase ++ u.writes s)
  pre s := L.Ready feat g u.stack s ∧ u.pre s
  post s X := (L.heap g).Intact feat s X g.own (u.live g.live s X) ∧ u.post s X
  events := u.events
  ends := u.ends
  layout _ := .owns g.own (movesBrk := true)
  sets := u.sets
  pends := u.pends
  moves := u.moves
  writesTo := u.writesTo
  env := u.env

end ZellicX86.C
