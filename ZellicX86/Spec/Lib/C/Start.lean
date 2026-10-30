import ZellicX86.Spec.Process
import ZellicX86.Spec.Lib.C.Runtime
/-!
# Statement vocabulary: the C library's start and exit around `main`

A library layer over the statement vocabulary (`Spec/Statement.lean`): what a C library does before and after a
program's `main`, as the program's statement sees it, without the library's code.

How a C program runs on Linux (psABI section 3.4.1; glibc 2.43's `sysdeps/x86_64/start.S`, `csu/libc-start.c`,
`sysdeps/nptl/libc_start_call_main.h`, `stdlib/exit.c`): the program's entry point `_start` calls the library's
`__libc_start_main(main, argc, argv, init, fini, rtld_fini, stack_end)`, which sets up the library (thread-local
storage and the thread pointer, the thread's `rseq` area and robust list, the stack's protection, the
initialisers) and calls `main(argc, argv, envp)` with `envp` the environment after `argv`'s null pointer
(C17 5.1.2.2.1). When `main` returns into the library, the library calls `exit` with `main`'s result
(C17 5.1.2.2.3), which runs the handlers registered with `atexit`, flushes and closes the streams and ends the
process with `exit_group` of the status's low byte (C17 7.22.4.4; POSIX `_Exit`).

A process statement over such a program takes the library's two parts as contracts and `main` by its own:

- the *startup* (`CStart.startup`, a contract for `ImplementsCallUpto` at `__libc_start_main`): from the library's entry
  the run reaches `main`'s entry as a call that returns into the library (`CStart.back`), with `main`'s arguments, a
  thread ready to call it, room on the stack and the library's runtime ready to be called (`CallOf` of `CStart.room`),
  having made only the system calls of a C library's startup (`Event.IsStartup`), or ends the process as the library
  says (`CStart.startEnds`); or, for a startup that need not get to `main` (`ImplementsCallUptoIf`: one that may loop
  for ever before it gets there), at every point it has reached that call, or has made only a startup's system calls
  so far, or has ended the process as the library says;
- the *exit* (`CStart.exit`, a contract for `ImplementsAtUpto` at `CStart.back`): from `main`'s return into the
  library, with the library's runtime as `main` left it (its streams among it, `Spec/Lib/C/Stdio.lean`), the run closes
  the streams (their pending output written, their read-ahead given back where they have some) and ends the process by
  `exit_group` with the low byte of `main`'s result, making besides only the system calls the library says its exit
  makes (`CStart.exitCalls`: glibc's allocator's memory calls, its exit's handlers `free` blocks).

What the library keeps between the two is its runtime's state (`CStart.rt`, a `Runtime`, `Spec/Lib/C/Runtime.lean`): the
memory it owns wherever the run put it, the program's blocks of its `malloc`, its streams, as the runtime's ghost
(`Ghost`). The startup gives the first ghost: the library's memory, which lies in its static data in the executable
(`CStart.statics`) or in memory mapped since `execve` (so apart from the program's own data), no blocks of the program's
(the blocks its startup and the toolchain's startup objects allocated among its own, `Ghost.libLive`), and the streams a program starts with (`Runtime.initial`: nothing pending). `main` hands the ghost from call to call as
the runtime's contracts say (`Runtime.call`); the exit takes it as `main` leaves it (`CStart.exit L feat g`, for every
ghost `g`), so its events say what the program's buffered output became. Besides, the startup's own stack frame above
`main`'s return address is the library's (`CStart.own` by the stack pointer at `main`'s return, with an invariant over
its bytes, `CStart.inv`): a `main` whose footprint lies apart from it keeps it.

Not covered: program code that runs inside the exit. Handlers `main` registers with `atexit` or `__cxa_atexit`
(this vocabulary has no contract for those functions, so a `main` proved by its contract registers none); and
handlers that run without `main` registering them: the entries of `.fini_array`, which glibc's exit calls through
`call_fini` and which hold the program's destructors (`__attribute__((destructor))`) beside the toolchain's
(`__do_global_dtors_aux`), and C++'s static destructors, registered with `__cxa_atexit` by constructors during the
startup. For a program with such code the exit contract is not the library's alone: its proof covers the binary's
handlers (they are the exit's code), so it is per binary, and a handler that writes or makes system calls is outside
the contract's events. Nor covered: C++'s `thread_local` destructors, a `main` that calls `exit` itself (its contract
is the exit's with a call's entry), other threads at `main`'s return. Nor a program with thread-local data of its own
(`__thread`, Rust's `thread_local!`, in the TLS block next to the library's): the startup's call of `main` does not put
it apart from what the library owns (`g.own`), so `main` cannot be proved to keep the runtime while writing it.
-/
namespace ZellicX86.C

/-- `ev` is a system call that a C library's startup makes before `main`, by its number (`rax`'s low 32 bits, as the
kernel reads it), with any arguments: `brk` (12) and `mmap` (9) for the thread-local storage, `mprotect` (10) for the
read-only data after relocation, `arch_prctl` (158) for the thread pointer, `set_tid_address` (218),
`set_robust_list` (273) and `rseq` (334) for the main thread, `prlimit64` (302) for the stack's limit, `getrandom`
(318) for the heap's and the stack protector's randomness, `clock_gettime` (228) for the heap's randomness where
`getrandom`'s is short or weak (glibc 2.43's `tcache_key_initialize`, `malloc/malloc.c`, by `random_bits`, before the
vDSO is set up) and `readlinkat` (267) for the executable's path: what glibc 2.43's static startup makes
(`csu/libc-tls.c`, `sysdeps/nptl/dl-tls_init_tp.c`, `elf/dl-support.c`, `csu/libc-start.c`, `malloc/arena.c`; traced
with `strace` on a static program, the clock read from the code); and `writev` (20) or `write` (1) to descriptor 2
(the descriptor's low 32 bits, as the kernel reads it), a diagnostic on standard error: glibc warns so of an invalid
setting in `GLIBC_TUNABLES` and goes on (`parse_tunable_print_error`, `elf/dl-tunables.c`, by `_dl_error_printf`).
None writes to another descriptor (`Output fd` of such events is empty for every `fd` but 2).

The class also admits `munmap` (11), which glibc 2.43's startup does not make: the startup calls `malloc` (from
`call_init`), whose contract allows every memory call of an allocator (`Event.IsMemCall`, `munmap` among them). No event
of the class reads a descriptor, and none writes to a descriptor other than 2. -/
def Event.IsStartup (ev : Event) : Prop :=
  arg32 ev.nr = 12 ∨ arg32 ev.nr = 9 ∨ arg32 ev.nr = 10 ∨ arg32 ev.nr = 11 ∨ arg32 ev.nr = 158 ∨ arg32 ev.nr = 218 ∨
    arg32 ev.nr = 273 ∨ arg32 ev.nr = 334 ∨ arg32 ev.nr = 302 ∨ arg32 ev.nr = 318 ∨ arg32 ev.nr = 228 ∨
    arg32 ev.nr = 267 ∨
    ((arg32 ev.nr = 20 ∨ arg32 ev.nr = 1) ∧ (ev.args.headD 0).setWidth 32 = 2)

/-- The values of the environment strings of the arguments `a` named `name`, in their order: `v` for each string `name=v`
(`name`'s UTF-8 bytes, then `=`). The first is the one a C library's `getenv` returns (POSIX `getenv`; glibc 2.43's
`stdlib/getenv.c` scans `__environ` from its start). -/
def _root_.ZellicX86.ExecArgs.envVals (a : ExecArgs) (name : String) : List (List Byte) :=
  let key := name.toUTF8.toList.map UInt8.toBitVec ++ [0x3d]
  a.envp.filterMap fun e => if key.isPrefixOf e then some (e.drop key.length) else none

/-- A C library's start and exit around `main`, as a program's statement sees them, without their code:
- `back`: where `main` returns to, the address after the library's call of `main`, where its exit starts (glibc
  2.43's `__libc_start_call_main` calls `main` through its stack frame and then `exit`);
- `rt`: its runtime (`Runtime`): what its functions' contracts see of it, which its startup sets up and its exit takes;
- `statics`: the regions of its data in the executable as `execve` loads it (link values), where its startup may keep
  state (glibc's `.data`, `.bss` and RELRO in a static program); none unless given (a library the dynamic linker maps
  after `execve` has none);
- `own p`: the regions of its startup's stack frame it keeps until its exit, by the stack pointer `p` at `main`'s return
  (above which that frame lies); none unless given;
- `inv b p`: its invariant over the bytes `b` of those regions (`0` at every other address) and `p`. `True` unless
  given;
- `pre`: what its startup assumes of the state at its entry besides what every process start gives (`CStart.startup`:
  `main`'s address, `argc`, the initial stack, the loaded segments, the thread, the break): the library's own assumptions
  (`True` unless given), which a statement about the whole program discharges at `_start`'s call of the startup.
  glibc 2.43's `__libc_start_main(main, argc, argv, init, fini, rtld_fini, stack_end)` (`csu/libc-start.c`, called by
  `sysdeps/x86_64/start.S`) needs here: `init` (`rcx`) and `rtld_fini` (`r9`) zero (a non-null `init` is called, a
  non-null `rtld_fini` registered with `__cxa_atexit`; a static `_start` passes zero and the kernel's `rdx`, zero at the
  first instruction), and, for the diagnostic its failure path writes to standard error, descriptor 2's `write`s
  putting nothing into mapped memory and `SIGPIPE` and `SIGXFSZ` not handled (the failure path exits after the
  `write`, so either may be left pending where the thread blocks it);
- `reads`: what its startup reads that it does not write, of the state at its entry (none unless given): the initial
  stack's vectors, the library's data as the executable file loads it (its relocations, `.rela.iplt`, the program
  headers at `AT_PHDR`, the TLS image);
- `writes`: what its startup may write, of the state at its entry (its stack frame, its data);
- `stack`: the bytes of stack its startup uses below its entry `rsp`, at most (`CStart.stackRgn`), which a process
  statement gives room for (`StackRoom`);
- `protects`: the regions whose pages its startup may re-protect, of the state at its entry (none unless given):
  glibc makes its RELRO segment's whole pages read-only after relocating it, from the page of its start up to the page
  of its end, both rounded down (`_dl_protect_relro` in `elf/dl-reloc.c`, called from `elf/dl-support.c`; for example,
  `PT_GNU_RELRO` `[0x4ac108, 0x4b0000)` gives `mprotect(0x4ac000, 16384)`), so the region to name is
  `[ALIGN_DOWN(p_vaddr), ALIGN_DOWN(p_vaddr + p_memsz))`; it may write them as well, but neither unmaps nor remaps
  them (`Layout.protects`, which re-protects only pages wholly in the regions);
- `exitStack`: the bytes of stack its exit uses below `p` (none unless given);
- `exitCalls`: the system calls its exit may make besides closing the streams (none unless given). glibc 2.43's, with
  the tunables its allocator's contracts admit (not `glibc.malloc.hugetlb`, under which a `free` may also `madvise` and
  read `/sys`): the allocator's memory calls (`Event.IsMemCall`), since its exit's handlers `free` blocks its startup allocated (libgcc's
  `release_registered_frames`, `unwind-dw2-fde.c`), and a `free` may grow the heap (a thread's first `free` sets up its
  cache, `tcache_init`, by a `malloc` that `brk` serves where the top chunk has no room) or give memory back (`systrim`;
  `malloc/malloc.c`);
- `startEnds`: how its startup may end the process instead of reaching `main` (never, unless given). For a startup
  stated by `ImplementsCallUptoIf` (one that need not get to `main`), any end of the process (`Outcome.Modelled`: not
  one where the model stops, after which the real process goes on) with only a startup's system calls
  (`fun out evs => out.Modelled ∧ ∀ ev ∈ evs, Event.IsStartup ev`): glibc's ends the process after a refused memory
  request (`exit_group(127)` after a diagnostic, `_startup_fatal`);
- `args`: what its startup assumes of the arguments, environment and credentials `execve` started the process with (any,
  unless given), which a statement about the whole program discharges from the launch: for a library whose startup is
  proved only for some launches (glibc's without set-user-ID launches or some settings of its tunables), those;
- `env`: what its startup assumes of the environment while it runs, about its entry state (`Contract.env`; `Undisturbed`
  unless given): for a library whose startup is proved only where the kernel grants it memory, that. It is a predicate
  over the whole stream of answers (`Oracle`), not over the startup's part of it, so a statement composed from the
  startup's contract runs over it for the whole run: what it excludes, it excludes for `main` and the exit too. -/
structure CStart where
  back : Addr
  rt : Runtime
  statics : List Rgn := []
  own : Addr → List Rgn := fun _ => []
  inv : (Addr → Byte) → Addr → Prop := fun _ _ => True
  pre : State → Prop := fun _ => True
  reads : State → List Rgn := fun _ => []
  writes : State → List Rgn
  stack : Nat
  protects : State → List Rgn := fun _ => []
  exitStack : Nat := 0
  exitCalls : Event → Prop := fun _ => False
  startEnds : Outcome → List Event → Prop := fun _ _ => False
  args : ExecArgs → Prop := fun _ => True
  env : State → Oracle → Prop := fun _ => Undisturbed

/-- The stack the startup of the library `L` uses, at its entry `s`: from `L.stack` bytes below `rsp` up to the initial
stack's words (`argv`, in `rdx`: the return address and what the program's entry point left between). -/
def CStart.stackRgn (L : CStart) (s : State) : Rgn :=
  ⟨s.cpu.gpr.rsp - BitVec.ofNat 64 L.stack, L.stack + (s.cpu.gpr.rdx.toNat - s.cpu.gpr.rsp.toNat)⟩

/-- The invariant of the startup's frame of the library `L` holds in `s` at the stack pointer `p` at `main`'s return:
`L.inv` of the bytes of the regions it keeps there (`Heap.readBytes`: theirs, `0` elsewhere) and `p`. -/
def CStart.Holds (L : CStart) (p : Addr) (s : State) : Prop :=
  L.inv (Heap.readBytes (L.own p) s) p

/-- What `main` is called with at the end of the startup of the library `L` from the state `s` at the library's entry
(`main` in `rdi`, `argc` in `esi`, `argv` in `rdx`), on a processor with features `feat`, for a `main` that uses `k`
bytes of stack below its entry `rsp`, in a program whose read-only data is `ro` (`roSegments`), the library's runtime at
the ghost `g`, as the contract whose call that is (`CStart.startup`, `CallOf`): under `sysv`, what the library reads
without owning it (`Runtime.reads`) and `ro` as memory it may read, the stack below the return address for `main` and
then the library's exit (`frame X (k + L.exitStack)`), `errno` (which `main`, calling the library, and the exit may set)
and the regions of the startup's frame the library keeps (`CStart.own` at `X`'s `rsp + 8`, where `main` returns, among
them the word there) as memory it may write, the library's memory as memory it owns (`Layout.owns g.own`), `argc` in
`edi`, `argv` in `rsi`, the environment after `argv`'s null pointer in `rdx` (`argv + 8 (argc + 1)`, `argc` an `int`;
C17 5.1.2.2.1, glibc's `csu/libc-start.c`), the stack apart from the startup's frame, that frame apart from the
library's memory, what it reads and `errno`, `ro` apart from all `main` and the library may write (not from what the
library reads: read-only data may be read by both), the frame's invariant (`CStart.Holds`), the runtime ready to be
called from that stack (`Runtime.Ready`), and the stack below the return address and the word above it short of the top
of the address space (so the exit's stack below where `main` returns does not wrap around). Only what a call's state is
counts (`CallOf`: the convention, the regions, the precondition); it promises nothing (`post` `True`): what `main` does
is its own contract's. -/
def CStart.room (L : CStart) (feat : Features) (k : Nat) (ro : List Rgn) (g : Ghost) (s : State) : Contract where
  conv := sysv
  reads X := L.rt.reads X.cpu.seg.fsBase ++ ro
  writes X := frame X (k + L.exitStack) :: L.rt.errnoLoc X :: L.own (X.cpu.gpr.rsp + 8)
  pre X :=
    X.cpu.gpr.rdi.setWidth 32 = s.cpu.gpr.rsi.setWidth 32 ∧ X.cpu.gpr.rsi = s.cpu.gpr.rdx ∧
    X.cpu.gpr.rdx = s.cpu.gpr.rdx + 8 * ((s.cpu.gpr.rsi.setWidth 32).signExtend 64 + 1) ∧
    Apart [frame X (k + L.exitStack)] (L.own (X.cpu.gpr.rsp + 8)) ∧
    (∀ a, (⟨X.cpu.gpr.rsp + 8, 8⟩ : Rgn).Mem a → Foot (L.own (X.cpu.gpr.rsp + 8)) a) ∧
    Apart (L.own (X.cpu.gpr.rsp + 8)) (g.own ++ L.rt.reads X.cpu.seg.fsBase ++ [L.rt.errnoLoc X]) ∧
    Apart ro (frame X (k + L.exitStack) :: L.rt.errnoLoc X :: (L.own (X.cpu.gpr.rsp + 8) ++ g.own)) ∧
    L.Holds (X.cpu.gpr.rsp + 8) X ∧ L.rt.Ready feat g (k + L.exitStack) X ∧
    (⟨X.cpu.gpr.rsp - BitVec.ofNat 64 (k + L.exitStack), k + L.exitStack + 16⟩ : Rgn).Fits
  post _ _ := True
  events _ _ _ := True
  layout _ := .owns g.own (movesBrk := true)

/-- The startup of the library `L` as a contract for `ImplementsCallUpto` (or `ImplementsCallUptoIf`) at
`__libc_start_main(main, argc, argv, …)` (`main` in `rdi`, `argc` in `rsi`, `argv` in `rdx`), on processor `prof`, in a
process `execve` started from an executable whose bytes are `img`, whose ELF header is `hdr` and whose program headers
are `phs`, for a `main` that uses `k` bytes of stack below its entry `rsp`. `room` is the code `main`'s call may run
(`main`'s and its callees': at link time the loaded executable segment, of which `main`'s code is a part), still loaded
at the call and not aliased by the room's data (`CallOf`). The code the startup itself runs is the code list of its
`ImplementsCallUpto`, which may be another: one without `main`'s bytes (at link time the loaded executable segment
without them) says that the startup executes no byte of `main` before it calls it (`InCode`), so that a run at `main`'s
entry has got to that call.

Precondition, under `sysv`:
- `main`'s address is canonical (a call through a pointer to a non-canonical address raises `#GP`: SDM Vol. 2A, CALL);
- for some arguments `a` a caller can pass (`ExecArgs.Ok`: C strings, the thread id a process id, …), `execve` accepts
  (`ExecArgs.withinLimits`: at most `MAX_ARG_STRINGS` of them, their bytes within the stack's limit) and the library
  takes (`L.args`): `argc` is their count (`ExecArgs.argv'`), and the initial stack from `argv` on is as `execve` wrote
  it (`InitialStackIn`: the vectors, the auxiliary vector and what it points to, the strings, the vDSO's image), in
  regions `IS` that fit, lie in no page the kernel owns (`NotKernel`) and lie apart from what the startup writes and
  re-protects and from the loadable segments' pages (`segmentPages`);
- the return address lies below `argv` (`rsp + 8 ≤ argv`, so the startup's stack frame lies below the initial stack),
  and the stack the startup uses (`CStart.stackRgn`: `L.stack` bytes below `rsp` up to `argv`) lies apart from the
  loadable segments' pages (`execve` maps them apart: `load_elf_binary` in `fs/binfmt_elf.c`, `MAP_FIXED_NOREPLACE`);
- the loadable segments hold the file's bytes (`SegmentsLoaded`: the library's data, relocations, program headers and
  TLS image among them), and the executable's read-only data (`roSegments phs`) lies apart from what the startup may
  write, change and re-protect (`L.writes`, `L.statics`, `L.protects`), so that its bytes stay as `execve` loaded them;
- no page aliases another (`NoAliasOver` of every list of regions: `execve` maps every page privately and the entry
  point maps none);
- `PKRU` allows access with key 0 (as `execve` leaves it, `KernelConfig`'s `init_pkru`; the library maps memory, which
  gets key 0), no `rseq` area is registered (`execve` leaves none: `rseq_execve`), the program break is page-aligned,
  above 0 and below `2 ^ 47` (`execve` puts it within 1 GiB above the executable's data, `ExecChoice.Valid`: below
  `2 ^ 47` for an executable loaded below `2 ^ 46`), and the thread's id is in `(0, 2 ^ 32)` (a process id,
  `ExecArgs.Ok`);
- `L.pre`;
- the loadable segments' pages lie in no page of the vDSO and no first page of the stack (`NotFixed`: `execve` maps the
  segments as ordinary private mappings, apart from both; so the runtime may own its static data there);
- the footprint of `L.writes` written, `L.statics` and `L.protects` owned, `L.reads` and the read-only data read, and
  `room` as code is ordinary memory (`Footprint.Ok`): the code `main`'s call runs is there and can be fetched at the
  startup's entry, apart from what the startup writes and re-protects, as its own code is by its call (`CallOf`).

Then the startup reads at most `L.reads` and the read-only data and writes at most `L.writes`. It may write and
re-protect the pages of `L.protects`, change the layout of the pages wholly in its static data `L.statics` otherwise (as
each later call into the library may change what it owns, `Runtime.call`), map memory and move the program break. It
may change the thread's `FS` base, `rseq` registration, `clear_child_tid` address and robust list, and of the files only
the one standard error is on (descriptor 2, where a startup's diagnostic goes, `Event.IsStartup`). It reaches a call of
`main` (`CallOf` of `CStart.room` at `main`'s address with the code `room`, returning to `L.back`: `main`'s entry with
its arguments, a thread that may start it, its stack, the startup's frame, the read-only data and the code segments
`room` ordinary memory, the library's runtime ready to be called), for the ghost of a runtime that owns memory only in
its static data (`L.statics`) and in pages not mapped at the startup's entry (so apart from the program's data), holds
no blocks of the program's (some of its own, which its startup and the toolchain's startup objects allocated:
`Ghost.libLive`) and has the streams a program starts with (`Runtime.initial`), having made only a startup's system
calls (`Event.IsStartup`). Or it ends the process as `L.startEnds` says. All this on the runs in the environment
`L.env` admits. With `ImplementsCallUptoIf`, the startup need not get to that call: at every point it has reached it,
has made only a startup's system calls so far, or has ended the process as `L.startEnds` says. -/
def CStart.startup (L : CStart) (prof : Profile) (img : Nat → Byte) (hdr : ElfHeader) (phs : List Phdr) (k : Nat)
    (room : List (Addr × List Byte)) : Contract where
  conv := sysv
  reads s := L.reads s ++ roSegments phs
  writes := L.writes
  pre s := Addr.canonical prof.feat.la57 s.cpu.gpr.rdi = true ∧
    (∃ (a : ExecArgs) (IS : List Rgn), s.cpu.gpr.rsi = BitVec.ofNat 64 a.argv'.length ∧
      InitialStackIn prof s a hdr phs s.cpu.gpr.rdx IS ∧ a.Ok ∧ a.withinLimits = true ∧ L.args a ∧ (∀ r ∈ IS, r.Fits) ∧ NotKernel s IS ∧
      Apart IS (L.writes s ++ L.protects s ++ segmentPages phs)) ∧
    s.cpu.gpr.rsp.toNat + 8 ≤ s.cpu.gpr.rdx.toNat ∧ SegmentsLoaded prof.feat s img phs ∧
    Apart (roSegments phs) (L.writes s ++ L.statics ++ L.protects s) ∧ Apart [L.stackRgn s] (segmentPages phs) ∧
    (∀ rs, NoAliasOver s rs) ∧ s.cpu.pkru &&& 3 = 0 ∧ s.thread.rseq = none ∧
    s.proc.mm.brk.toNat % 4096 = 0 ∧ 0 < s.proc.mm.brk.toNat ∧ s.proc.mm.brk.toNat < 2 ^ 47 ∧
    0 < s.thread.tid ∧ s.thread.tid < 2 ^ 32 ∧ L.pre s ∧ NotFixed s (segmentPages phs) ∧
    (⟨L.writes s, L.statics ++ L.protects s, L.reads s ++ roSegments phs, room⟩ : Footprint).Ok prof.feat s
  post s X := ∃ own libLive : List Rgn,
    (∀ a, Foot own a → Foot L.statics a ∨ s.proc.mm.mem.map (pageOf a) = none) ∧
    CallOf prof s.cpu.gpr.rdi room (L.room prof.feat k (roSegments phs) { own, libLive, streams := L.rt.initial } s) X
      L.back
  events _ _ evs := ∀ ev ∈ evs, Event.IsStartup ev
  ends _ := L.startEnds
  layout s := .protects L.statics (L.protects s) true
  sets _ := [.fsBase, .rseq, .clearChildTid, .robustList]
  writesTo _ := [2]
  env := L.env

/-- The events `evs` are those of `es` and those of `os`, interleaved, each list in its order: `mask` says of each event of
`evs` which list it is from (`true`: `es`). -/
def Event.Interleaves (evs es os : List Event) : Prop :=
  ∃ mask : List Bool, mask.length = evs.length ∧ es = ((evs.zip mask).filter (·.2)).map (·.1) ∧
    os = ((evs.zip mask).filter (!·.2)).map (·.1)

/-- The exit of the library `L` after `main` returned into it, with its runtime at the ghost `g` (the streams
`g.streams` open), on a processor with features `feat`, as a contract for `ImplementsAtUpto` at `L.back` (C17
5.1.2.2.3 and 7.22.4.4: `exit` with `main`'s result): from a state at `main`'s return (`rsp` 16-aligned, `DF` clear, the
x87 stack empty, as `sysv`'s exit leaves them after a call from an aligned stack) with the startup's frame's invariant
(`CStart.Holds` at `rsp`), the word at `rsp` among that frame's regions (it lies above `main`'s return address, in the
startup's frame: glibc's `__libc_start_call_main`'s), that frame apart from the library's memory, what it reads and
`errno`, the runtime ready to be called from the stack the exit uses (`Runtime.Ready` with `L.exitStack`), and, if a
stream has pending output, a `write` to its descriptor putting no bytes into memory the process maps (`WriteUnmapped`)
and the signals the kernel sends in a `write` it does not complete (`SIGPIPE`, `SIGXFSZ`) not handled (ignored or by
default), reading what the library reads without owning it, writing at most the `L.exitStack` bytes below `rsp`,
`errno`, the word at it and the startup's frame (and the library's memory, `Layout.owns`), it closes the streams
(`Streams.Closes`: each one's pending output written to its descriptor, all of it unless a `write` failed, and its
read-ahead, where it has some, given back) and ends the process by `exit_group` with the low byte of `main`'s result
(`eax`), making no other system call but those `L.exitCalls` admits, interleaved with the closing ones
(`Event.Interleaves`); or, where a stream has pending output, the process is killed in one of those `write`s
(`Outcome.KilledInWrite`), after a start of closing them (`Streams.Flushing`), amid such calls. Where a stream has pending output,
the runs are those in which no `write` of at least one byte takes none (`WritesProgress`): the library writes until all
is taken. -/
def CStart.exit (L : CStart) (feat : Features) (g : Ghost) : Contract where
  conv := sysv
  reads s := L.rt.reads s.cpu.seg.fsBase
  writes s := frame s L.exitStack :: L.rt.errnoLoc s :: L.own s.cpu.gpr.rsp
  pre s := s.cpu.gpr.rsp.toNat % 16 = 0 ∧ s.cpu.rflags.df = false ∧ s.cpu.x87.full = 0 ∧
    L.Holds s.cpu.gpr.rsp s ∧ (∀ a, (⟨s.cpu.gpr.rsp, 8⟩ : Rgn).Mem a → Foot (L.own s.cpu.gpr.rsp) a) ∧
    Apart (L.own s.cpu.gpr.rsp) (g.own ++ L.rt.reads s.cpu.seg.fsBase ++ [L.rt.errnoLoc s]) ∧
    L.rt.Ready feat g L.exitStack s ∧
    ∀ p ∈ g.streams, p.2.out ≠ [] → WriteUnmapped s p.2.fd ∧
      ((s.proc.sighand Signal.SIGPIPE).disp = .ignore ∨ (s.proc.sighand Signal.SIGPIPE).disp = .default) ∧
      ((s.proc.sighand Signal.SIGXFSZ).disp = .ignore ∨ (s.proc.sighand Signal.SIGXFSZ).disp = .default)
  post _ _ := False
  events _ _ evs := evs = []
  ends s out evs := ∃ es os, Event.Interleaves evs es os ∧ (∀ ev ∈ os, L.exitCalls ev) ∧
    ((out = .exited .exitGroup (s.cpu.gpr.rax.setWidth 8) ∧ g.streams.Closes es) ∨
      (out.KilledInWrite ∧ g.streams.Flushing es ∧ ∃ p ∈ g.streams, p.2.out ≠ []))
  layout _ := .owns g.own (movesBrk := true)
  env _ o := Undisturbed o ∧ ((∀ p ∈ g.streams, p.2.out = []) ∨ WritesProgress o)

end ZellicX86.C
