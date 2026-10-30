import ZellicX86.Spec.Statement.Linux
/-!
# Statement vocabulary

The named predicates theorem statements are written in. A statement file uses these and
the definitions of `Spec`; an auditor who has read this file, the two modules of `Spec/Statement/` and what
they mention knows what a theorem says.

The vocabulary is in three modules, read in this order:
- `Spec/Statement/Memory.lean`: regions of virtual addresses (`Rgn`, `Foot`, `Apart`) and facts about the memory
  behind them (accessible, contents, no aliasing, not owned by the kernel, not shared), and what a call may change of
  it (`ChangesOnly`);
- `Spec/Statement/Linux.lean`: what is about Linux: the thread (`Plain`, `RseqQuiet`, its settings and
  `KeepsSettingsBut`), the process outside memory (`KeepsProc`), the rules of the memory layout (`LayoutOk`, `KeepsEnv`,
  `KeepsEnvOut`, `KeepsEnvProt`), the environment of a run (`Undisturbed`, `ReadsWhole`, `WritesProgress`, `OpensAs`),
  the system calls' events (`Event.IsWrite`, `Event.IsRead`, …), output and input as byte streams (`Output`, `Input`),
  descriptors on files (`WriteUnmapped`, `InputAt`, `OutAt`) and the files a function keeps (`FileKept`,
  `KeepsFilesBut`);
- this file: calling conventions, runs, contracts and allocators, which name the Linux module's pieces where a
  function's frame or environment is Linux's.

This file:
- Calling conventions (`Conv`, with the psABI's `sysv`), the state at a function's entry
  (`CallShape`) and at its return (`Returns`).
- Runs: reaching a state or an outcome on every run, with the system-call events on the way and what holds of every
  state before (`ReachOrEndsIn`; `ReachOrEnds` with nothing said of those states, and its two special cases `Reach`
  and `Ends`), what holds at every point of a run (`Always`), a safety property with an optional reach (`ReachIf`),
  ending on every run that gets to a given state (`EndsIf`), and the events of a loop as rounds (`RoundsThen`).
- Contracts: what a function promises independently of its code, including how it may end the
  process instead of returning and what it does to the memory layout (`Contract`, `Layout`), and that
  given code (its own and its callees') keeps that promise, executing only that code until it returns or ends
  (`ImplementsCall`, `InCode`): every call of it
  (`CallOf`: its shape `CallShape`, a thread `Ready` to start it, its `Footprint` ordinary memory,
  `Footprint.Ok`, and the precondition) returns as the contract says (`Returned`, with `Contract.Frame`: the memory
  layout as the contract's rule allows, the thread's settings, the process outside memory, the files but those it writes
  to, the memory but what it writes, what it owns and the ids the kernel writes into the `rseq` area) or
  ends the process as it allows, the code a list of segments with the function's own bytes a slice of one of them
  (`CodeIn`); code whose part a statement speaks of ends at a state its contract describes
  rather than at a return (`ImplementsCallUpto`, `Contract.Reached`: a C library's startup up to its call of `main`;
  `ImplementsCallUptoIf` for code that need not get there), and code entered other than by a call (`ResumeOf`,
  `ImplementsAtUpto`: a C library's exit after `main` returned).
- Allocators: what `malloc` and `free` promise their callers whatever the allocator is (`Heap`,
  `Heap.malloc`, `Heap.free`), over the regions the allocator owns, which each call takes and returns
  (`Heap.Next`) and whose layout it may change but for the live blocks' pages (`KeepsPages`), the regions it
  reads and changes without owning them, apart from those (`Heap.Outside`), and an invariant the callers do
  not know, over what it sees of the process (`Heap.View`, `Heap.view`): the bytes and the accesses the
  allocator owns, the program break, the `FS` base and the bytes it reads; code that keeps these contracts
  (`Heap.ImplementedBy`), and the contract of a function that uses an allocator (`Heap.client`, `Heap.Use`).

The library layer `Spec/Lib/` builds on this file with vocabulary for particular kinds of data: linked
structures in memory (`Spec/Lib/Linked.lean`), text a program writes (`Spec/Lib/Text.lean`), and the C library
(`Spec/Lib/C/`: `errno`, `malloc` and `free`, `read` and `write`, its streams, its start and exit around `main`).
-/
namespace ZellicX86

/-! ## Calling conventions -/

/-- A calling convention: what a function may assume at entry and must guarantee at its
return, apart from `rip` (a contract names its argument and result locations itself).
`preserved` are the registers the callee leaves as it found them. -/
structure Conv where
  preserved : List RegName
  entry : State → Prop
  exit : State → State → Prop

/-- The System V x86-64 psABI convention for global functions (psABI 3.2.1, 3.2.2, 3.2.3;
`low-level-sys-info.tex`):
- entry: `rsp + 8` is a multiple of 16 (the end of the argument area is 16-byte aligned
  and the return address has been pushed), `DF = 0`, the x87 stack is empty (every x87 register
  empty: `X87.full = 0`, the "x87 mode" the psABI requires);
- exit: `rsp` is the entry `rsp + 8` (the return address popped), `rbx rbp r12–r15` are
  preserved, `DF = 0`, the x87 stack is empty, `MXCSR` from bit 6 up (the control bits 6–15,
  "callee-saved" in psABI 3.2.1, and the bits above, reserved but for AMD's misaligned SSE mode, bit
  17, a control bit too) and the x87 control word are as at entry. No vector register is preserved.

The `FS` base, which the psABI also makes callee-saved (the thread pointer), is a setting of the thread
that a contract keeps unless it says it changes it (`KeepsSettingsBut`, `Contract.sets`): glibc's startup
sets it.

The empty x87 stack at entry and at exit is the rule of the System V Intel386 ABI (4th edition,
1997, "Function Calling Sequence", p. 3-12: `%st(0)`–`%st(7)` "must be empty before entry and upon
exit from a function", `%st(0)` except for a floating-point return value). The x86-64 psABI does not
restate it; it requires "x87 mode upon entry" (no `MMX` state). A function returning a value on the
x87 stack (`long double`, in `st0`) needs its own convention. -/
def sysv : Conv where
  preserved := [.gpr 3, .gpr 5, .gpr 12, .gpr 13, .gpr 14, .gpr 15]
  entry s :=
    (s.cpu.gpr.rsp + 8).toNat % 16 = 0 ∧ s.cpu.rflags.df = false ∧ s.cpu.x87.full = 0
  exit s₀ s :=
    s.cpu.gpr.rsp = s₀.cpu.gpr.rsp + 8 ∧ s.cpu.rflags.df = false ∧ s.cpu.x87.full = 0 ∧
    s.cpu.vec.mxcsr >>> 6 = s₀.cpu.vec.mxcsr >>> 6 ∧ s.cpu.x87.fcw = s₀.cpu.x87.fcw

/-- `c` with the extra registers `rs` preserved (a callee whose callers rely on more than
the convention, e.g. under GCC's interprocedural register allocation). -/
def Conv.preserving (c : Conv) (rs : List RegName) : Conv :=
  { c with preserved := c.preserved ++ rs }

/-- `s` is at the entry `entry` of a function called under convention `c` that returns to
`ra`, on a processor with features `feat`: `rip` is the entry, the return address is on top of
the stack and canonical, and `c`'s entry conditions hold. A `ret` to a non-canonical address
raises `#GP(0)` (SDM Vol. 2B, RET); a `call` pushes the address after itself, which Linux keeps
canonical by leaving the last page below the canonical boundary unmapped
(`DEFAULT_MAP_WINDOW`, `arch/x86/include/asm/page_64_types.h`). -/
def CallShape (feat : Features) (c : Conv) (s : State) (entry ra : Addr) : Prop :=
  s.cpu.rip = entry ∧ Word s s.cpu.gpr.rsp ra ∧ ra.canonical feat.la57 = true ∧ c.entry s

/-- `s` is a return, under convention `c`, from the call whose entry state was `s₀` to `ra`:
`rip` is `ra`, the preserved registers are as at entry, and `c`'s exit conditions hold. -/
def Returns (c : Conv) (s₀ : State) (ra : Addr) (s : State) : Prop :=
  s.cpu.rip = ra ∧
  (∀ r ∈ c.preserved, s.cpu.agreeOn s₀.cpu r) ∧
  c.exit s₀ s

/-! ## Runs -/

/-- On processor `prof`, for every stream of answers satisfying `env`, the run from `s₀` either reaches a state `s`
without ending first, having produced the system-call events `evs` on the way, with `P s evs`, or ends with an outcome
`out`, having produced the events `evs`, with `E out evs`; and every state the run is in before it gets there (after
fewer steps: `s₀` and every state after it up to the one before `s`, or before the step that ends the run) satisfies
`I`. The statement of a function that may end the process instead of returning (a call of `abort` or
`__stack_chk_fail` on a failed check): `P` says what a return gives, `E` how the process may end, `I` where the run
stays until then (`ImplementsCall`: its `rip` in the function's code, `InCode`). The state is one the run passes
through after some number of steps, not necessarily the first with `P`. For a function's return (`ImplementsCall`) it
is a state at the return address with the contract's facts, from which a caller's statement continues; where the
return address lies outside the code segments the statement names, it is the first return, since every earlier state
has its `rip` in those segments (`InCode`). -/
def ReachOrEndsIn (prof : Profile) (env : Oracle → Prop) (s₀ : State) (I : State → Prop)
    (P : State → List Event → Prop) (E : Outcome → List Event → Prop) : Prop :=
  ∀ o, env o → ∀ t, ∃ n st evs t', run prof o n s₀ t = (st, evs, t') ∧
    (∀ m < n, ∀ s evs' t'', run prof o m s₀ t = (.running s, evs', t'') → I s) ∧
    match st with
    | .running s => P s evs
    | .done out => E out evs

/-- On processor `prof`, for every stream of answers satisfying `env`, the run from `s₀` either reaches a state `s`
without ending first, having produced the system-call events `evs` on the way, with `P s evs`, or ends with an outcome
`out`, having produced the events `evs`, with `E out evs`: `ReachOrEndsIn` with nothing said of the states on the
way. -/
abbrev ReachOrEnds (prof : Profile) (env : Oracle → Prop) (s₀ : State) (P : State → List Event → Prop)
    (E : Outcome → List Event → Prop) : Prop :=
  ReachOrEndsIn prof env s₀ (fun _ => True) P E

/-- On processor `prof`, for every stream of answers satisfying `env`, the run from `s₀`
reaches a state `s` without ending first, having produced the system-call events `evs` on the way,
with `P s evs`: `ReachOrEnds` with no way to end. -/
abbrev Reach (prof : Profile) (env : Oracle → Prop) (s₀ : State) (P : State → List Event → Prop) :
    Prop :=
  ReachOrEnds prof env s₀ P fun _ _ => False

/-- On processor `prof`, for every stream of answers satisfying `env`, the run from `s₀`
ends with an outcome `out`, having produced the system-call events `evs` on the way, with
`P out evs`: `ReachOrEnds` with no state to reach. The outcome and the events are stated together
because the outcome may depend on the events: a `write` to a broken pipe ends the process by
`SIGPIPE` instead of returning (`sysWrite`). -/
abbrev Ends (prof : Profile) (env : Oracle → Prop) (s₀ : State) (P : Outcome → List Event → Prop) :
    Prop :=
  ReachOrEnds prof env s₀ (fun _ _ => False) P

/-- On processor `prof`, for every stream of answers satisfying `env`, at every point of the run
from `s₀` (after any number of steps `n`): either the process is still running, in a state `s`, and `I`
holds of `s` and the system-call events so far, or it has ended with an outcome `out` and events `evs`
with `P out evs`.
Nothing is said about the run ending: a process that copies its input until the end of the input
runs forever on an input that never ends (a pipe whose writer keeps writing), and the statement
still covers every finite part of that run. -/
def Always (prof : Profile) (env : Oracle → Prop) (s₀ : State) (I : State → List Event → Prop)
    (P : Outcome → List Event → Prop) : Prop :=
  ∀ o, env o → ∀ t n, match run prof o n s₀ t with
    | (.running s, evs, _) => I s evs
    | (.done out, evs, _) => P out evs

/-- On processor `prof`, for every stream of answers satisfying `env`, at every point of the run from `s₀` (after any
number of steps `n`): either the run has passed by then (after at most `n` steps) through a state `s`, with the
system-call events `evs` up to there, with `P s evs`; or it is still running, in a state `s` with `I s evs`, or it has
ended with an outcome `out` and events `evs` with `E out evs`. A safety property with an optional reach: nothing says
that the run gets to a state with `P`, nor that it ends; `I` and `E` say what holds until it gets there. The statement
of code that need not get to the point its contract speaks of: a C library's startup, which may loop for ever or end the
process before it calls `main` (`ImplementsCallUptoIf`, `Spec/Lib/C/Start.lean`). -/
def ReachIf (prof : Profile) (env : Oracle → Prop) (s₀ : State) (P I : State → List Event → Prop)
    (E : Outcome → List Event → Prop) : Prop :=
  ∀ o, env o → ∀ t n, (∃ m ≤ n, ∃ s evs t', run prof o m s₀ t = (.running s, evs, t') ∧ P s evs) ∨
    match run prof o n s₀ t with
    | (.running s, evs, _) => I s evs
    | (.done out, evs, _) => E out evs

/-- On processor `prof`, for every stream of answers satisfying `env` on which the run from `s₀` passes through a state
`s` with `R s evs` (`evs` the system-call events up to there), the run ends, with an outcome `out` and the events `evs`
with `P out evs`. A liveness property on the runs that get somewhere: a run that never passes through such a state need
not end. -/
def EndsIf (prof : Profile) (env : Oracle → Prop) (s₀ : State) (R : State → List Event → Prop)
    (P : Outcome → List Event → Prop) : Prop :=
  ∀ o, env o → ∀ t, (∃ n s evs t', run prof o n s₀ t = (.running s, evs, t') ∧ R s evs) →
    ∃ n out evs t', run prof o n s₀ t = (.done out, evs, t') ∧ P out evs

/-- The events `evs` are rounds, each satisfying `R`, one after the other, then the events `last`: the
events of a loop whose iterations make system calls, each iteration's as `R` says, followed by what
came after the last full iteration. -/
def RoundsThen (R : List Event → Prop) (evs last : List Event) : Prop :=
  ∃ rs : List (List Event), (∀ r ∈ rs, R r) ∧ evs = rs.flatten ++ last

/-! ## Contracts -/

/-- The `k` bytes of stack below `rsp` in `s` and the 8 bytes at `rsp` (at a function's entry,
the return address): the region a function with a frame of at most `k` bytes uses. -/
def frame (s : State) (k : Nat) : Rgn := ⟨s.cpu.gpr.rsp - BitVec.ofNat 64 k, k + 8⟩

/-- The regions a call uses, by what it does with them: the data it `writes`, the memory it `own`s
(an allocator's, whose layout it may change: `Layout.owns`), the data it `reads`, and the `code`
segments (pairs of an address and the bytes there): its own code and its callees'. -/
structure Footprint where
  writes : List Rgn
  own : List Rgn
  reads : List Rgn
  code : List (Addr × List Byte)

/-- The code segments of `fp` as regions. -/
def Footprint.codeRgns (fp : Footprint) : List Rgn := fp.code.map fun c => ⟨c.1, c.2.length⟩

/-- The data regions of `fp`: written, owned, read. -/
def Footprint.data (fp : Footprint) : List Rgn := fp.writes ++ fp.own ++ fp.reads

/-- In `s`, on a processor with features `feat`, the footprint `fp` is ordinary memory a function can
use. `own` is held to everything `writes` is except accessibility, and must also be memory the function
may unmap (`NotFixed`): a function may have made what it owns inaccessible itself (a guard page, pages
it unmapped), and what it may do there is its contract's business (an allocator's invariant over the
accesses it may make, `Heap.access`). How the data regions lie relative to each other (a stack frame
apart from the buffers, an output apart from an input) is not said here: it is part of a contract's
precondition. -/
structure Footprint.Ok (feat : Features) (s : State) (fp : Footprint) : Prop where
  /-- No region and no segment reaches past `2 ^ 64`. -/
  fits : ∀ r ∈ fp.data ++ fp.codeRgns, r.Fits
  /-- The regions written are accessible for writing. -/
  writable : ∀ r ∈ fp.writes, Accessible feat s .write r
  /-- The regions read are accessible for reading. -/
  readable : ∀ r ∈ fp.reads, Accessible feat s .read r
  /-- Every segment's bytes are at its address, and can be fetched. -/
  code : ∀ c ∈ fp.code, CodeBytes feat s c.1 c.2
  /-- No region and no segment is stored in a page the kernel owns or may drop (`NotKernel`). -/
  notKernel : NotKernel s (fp.data ++ fp.codeRgns)
  /-- No two of the regions, the segments and the thread's `rseq` area alias (`NoAliasOver`). -/
  noAlias : NoAliasOver s (fp.data ++ fp.codeRgns ++ rseqArea s)
  /-- The regions written and owned are in no shared mapping. -/
  notShared : NotShared s (fp.writes ++ fp.own)
  /-- The regions owned lie in no page of the vDSO and no first page of the stack (`NotFixed`). -/
  notFixed : NotFixed s fp.own
  /-- The code lies apart from the data. -/
  codeApart : Apart fp.data fp.codeRgns
  /-- The thread's `rseq` area lies apart from the data and the code. -/
  rseqApart : Apart (rseqArea s) (fp.data ++ fp.codeRgns)

/-- The thread in `s`, on a processor with features `feat`, may start a call: it is `Plain`, its
`rseq` area, if it has one, is quiet (`RseqQuiet`), and the layout is one a process can have
(`LayoutOk`). -/
structure Ready (feat : Features) (s : State) : Prop where
  plain : Plain s
  rseq : RseqQuiet feat s
  layout : LayoutOk feat s

/-- What a function does to the memory layout, by its contract (`Contract.layout`).
- `keeps`: it keeps the layout and the program break (`KeepsEnv`).
- `owns own movesBrk`: it may map pages no mapping held at the call and map, unmap or change the
  pages wholly in the regions `own`, whose bytes it may also change; the rest of the layout it keeps
  (`KeepsEnvOut`). `own` is what the function owns at the call (an allocator's memory, `Heap`). With
  `movesBrk` false it returns with the program break as at the call; an allocator that grows by `brk`,
  and a function that calls one, may move it.
- `protects own prot movesBrk`: it may do what `owns own movesBrk` allows, except that of a page wholly in the regions
  `prot` (also one in `own`) it may change only the protection, protection key and area (`Mapping.area`), and its
  bytes; the rest of the layout it keeps (`KeepsEnvProt`): a C library's startup, which may change the library's own
  memory (`CStart.statics`) as each of its later calls may, and re-protects its RELRO segment (`CStart.protects`). It
  neither unmaps nor remaps the pages of `prot`, so its callers keep knowing where they are. The program break as for
  `owns`. -/
inductive Layout where
  | keeps
  | owns (own : List Rgn) (movesBrk : Bool)
  | protects (own prot : List Rgn) (movesBrk : Bool)

/-- The regions a function with the layout rule `l` owns, whose bytes it may change besides those it writes: `own` for
`owns own _`, `own` and `prot` for `protects own prot _`, none for `keeps`. -/
def Layout.owned : Layout → List Rgn
  | .keeps => []
  | .owns own _ => own
  | .protects own prot _ => own ++ prot

/-- From the call `s₀` to `X`, on a processor with features `feat`, the layout changed only as the rule `l` allows:
`KeepsEnv` for `keeps`; `KeepsEnvOut feat own` for `owns own movesBrk` and `KeepsEnvProt feat own prot` for
`protects own prot movesBrk` (a layout such a processor's process can have stays one, `LayoutOk feat`), and the program
break as at the call unless `movesBrk`. -/
def KeepsLayout (feat : Features) : Layout → State → State → Prop
  | .keeps, s₀, X => KeepsEnv s₀ X
  | .owns own movesBrk, s₀, X => KeepsEnvOut feat own s₀ X ∧ (movesBrk = false → X.proc.mm.brk = s₀.proc.mm.brk)
  | .protects own prot movesBrk, s₀, X =>
    KeepsEnvProt feat own prot s₀ X ∧ (movesBrk = false → X.proc.mm.brk = s₀.proc.mm.brk)

/-- What a function promises its callers, independently of its code. Called under convention `conv` from a state
satisfying `pre`, in which the regions `reads` are readable and `writes` writable, it either returns or ends the
process. If it returns, it has changed only `writes`, what it owns by its layout rule (`layout`) and the ids the kernel
writes into the `rseq` area (`rseqIds`); `post` holds of the entry state and the return state; and its system-call
events satisfy `events` (for a function without system calls, `fun _ _ evs => evs = []`). `post` and `events` are about
the state after the piece of code the contract is about: a function's return (`ImplementsCall`) or, for code whose part
ends elsewhere (`ImplementsCallUpto`, `ImplementsAtUpto`), the state that part reaches. If it ends the process, the
outcome and the events satisfy `ends` of the entry state. The regions are functions of the entry state (they depend on
arguments); `writes` includes the function's stack frame (`frame`). `reads` is what the function needs
readable; nothing bounds which bytes the code reads (a vector load may read past an object on the
object's pages, which cannot fault where the object's bytes do not).

`ends` is `False` unless given: such a function never ends the process. A function with run-time
checks that end the process when they fail (`assert`, a Rust panic under `panic = abort`,
`__stack_chk_fail` after a stack smash, musl's `a_crash`) says in `ends` how and when it may end;
a function that never returns (`abort`, `__stack_chk_fail` itself) has `post` `False`.

`layout` is `Layout.keeps` unless given: such a function keeps the memory layout and the program
break.

`sets` are the settings of the thread the function may change (`Setting`: its `rseq` registration, the
`FS` and `GS` bases, `PKRU`, its blocked signals, …), none unless given: it keeps the others and the rest of
the thread's state (`KeepsSettingsBut`). `pends` are the signals whose entries in the thread's pending set it may add
or remove, none unless given: a function that `write`s names `SIGPIPE` and `SIGXFSZ`, which stay pending where the
thread blocks them. `moves` are the
descriptors whose open file descriptions' positions it may move, none unless given: it keeps the rest of
the process's state outside memory (`KeepsProc`). `writesTo` are the descriptors whose files it may change (by
`write` or `pwrite64` through them), none unless given: it keeps every other file, its size and its pages' bytes
(`KeepsFilesBut`), so that a caller that knows a file's bytes (an input it reads) knows them after the call. `moves`
does not say this: `pwrite64` changes a file without moving the position. All four are about the entry state.

`env` is what the function assumes of the environment while it runs, about the entry state: the runs
`ImplementsCall` speaks of are those whose answers satisfy `env s₀` (`ReachOrEnds`). It is `Undisturbed`
unless given; a function that reads a file assumes what a program's statement does (`fun _ o =>
Undisturbed o ∧ ReadsWhole o`, `OpensAs`). The frame (`Contract.Frame`) is promised on those runs, so an
environment that lets other agents move the positions, signal the process or change its limits leaves a
`KeepsProc` no code can keep, and one that lets a tracer write the thread's registers (`EnvEvent.tracer`: the
`FS` and `GS` bases, `PKRU` among them) leaves a `KeepsSettingsBut` no code can keep, and one that lets another agent
write a file or change its size (`EnvEvent.fileWrite`, `EnvEvent.fileSize`) leaves a `KeepsFilesBut` no code can keep
(for any file, however few the contract's runs touch): no code that returns can keep such a contract (one whose runs
never return, or whose precondition is false, never needs its frame). `Undisturbed` excludes all of these. -/
structure Contract where
  conv : Conv
  reads : State → List Rgn
  writes : State → List Rgn
  pre : State → Prop
  post : State → State → Prop
  events : State → State → List Event → Prop
  ends : State → Outcome → List Event → Prop := fun _ _ _ => False
  layout : State → Layout := fun _ => .keeps
  sets : State → List Setting := fun _ => []
  pends : State → List Signal := fun _ => []
  moves : State → List Nat := fun _ => []
  writesTo : State → List Nat := fun _ => []
  env : State → Oracle → Prop := fun _ => Undisturbed

/-- The footprint of a call of a function with contract `C` and code segments `code` from `s`: the
contract's regions at `s` and what the function owns there by its layout rule. -/
def Contract.footprint (C : Contract) (code : List (Addr × List Byte)) (s : State) : Footprint where
  writes := C.writes s
  own := (C.layout s).owned
  reads := C.reads s
  code := code

/-- `s₀` is a call, on processor `prof`, of the function at `entry` with code segments `code` and
contract `C`, returning to `ra`: the state is at `entry` (`CallShape`, under `C.conv`), the thread may
start a call (`Ready`), the call's footprint is ordinary memory it can use (`Footprint.Ok`), and the
contract's precondition holds. -/
structure CallOf (prof : Profile) (entry : Addr) (code : List (Addr × List Byte)) (C : Contract)
    (s₀ : State) (ra : Addr) : Prop where
  shape : CallShape prof.feat C.conv s₀ entry ra
  ready : Ready prof.feat s₀
  foot : (C.footprint code s₀).Ok prof.feat s₀
  pre : C.pre s₀

/-- The frame condition of contract `C`: what a call of the function from `s₀` left alone at `X`: the
layout as its layout rule allows (`KeepsLayout`), the thread's settings but those it sets and its pending signals but
those it may leave pending (`KeepsSettingsBut`), the process's state outside memory but the positions it moves (`KeepsProc`),
every file but those of the descriptors it writes to (`KeepsFilesBut`), and
every byte but those of the regions it writes, of what it owns, and of the ids the kernel writes into the
`rseq` area (`rseqIds`). On a processor with features `feat`: the layout kept is one such a processor's process can
have (`LayoutOk feat`). (Not to be confused with a page's bytes, `Frame`, or a function's stack frame, `frame`.) -/
def Contract.Frame (C : Contract) (feat : Features) (s₀ X : State) : Prop :=
  KeepsLayout feat (C.layout s₀) s₀ X ∧ KeepsSettingsBut (C.sets s₀) (C.pends s₀) s₀ X ∧ KeepsProc (C.moves s₀) s₀ X ∧
    KeepsFilesBut (C.writesTo s₀) s₀ X ∧ ChangesOnly s₀ X (C.writes s₀ ++ (C.layout s₀).owned ++ rseqIds s₀)

/-- `X` is a state reached, with the system-call events `evs` on the way, by a run of code with contract `C` that
started in `s₀`, as `C` says of such a state: the frame of `C` kept up to there (`Contract.Frame`), `C.post s₀ X`
and events satisfying `C.events`, on a processor with features `feat` (the layout kept one such a processor's process can
have, `LayoutOk feat`). `Returned` is this with the return (`Returns`); this alone is what `ImplementsCallUpto`
and `ImplementsAtUpto` conclude,
for code that does not return to a caller but goes on into code its statement names otherwise. -/
abbrev Contract.Reached (C : Contract) (feat : Features) (s₀ X : State) (evs : List Event) : Prop :=
  C.Frame feat s₀ X ∧ C.post s₀ X ∧ C.events s₀ X evs

/-- `X` is a return, with the system-call events `evs` on the way, of the call of a function with
contract `C` from `s₀` to `ra`: a return under `C.conv` (`Returns`), with the frame of `C` kept
(`Contract.Frame`), `C.post` holding, and events satisfying `C.events`, on a processor with features `feat` (the layout
kept one such a processor's process can have, `LayoutOk feat`). -/
def Returned (feat : Features) (C : Contract) (s₀ : State) (ra : Addr) (X : State) (evs : List Event) : Prop :=
  Returns C.conv s₀ ra X ∧ C.Reached feat s₀ X evs

/-- The bytes `bs` lie at the address `a` inside one of the code segments `L` (pairs of an address and the bytes
there): some segment of `L` holds them `k` bytes after its start (`bs` is a prefix of its bytes from the `k`-th on).
How a function's statement places its own code among the code its calls may run (`ImplementsCall`). Meant for
non-empty `bs` (a function's code): for `bs = []` and a non-empty `L` it holds of every address, since `k` is not
bounded. -/
def CodeIn (L : List (Addr × List Byte)) (a : Addr) (bs : List Byte) : Prop :=
  ∃ c ∈ L, ∃ k, a = c.1.add k ∧ bs <+: c.2.drop k

/-- The thread of `s` executes code of the segments `L` (pairs of an address and the bytes there) next: its `rip` is
the address of one of the bytes of a segment of `L`, `k` bytes after the segment's start. Where code whose statement
names `L` keeps its control flow (`ImplementsCall`): it executes no byte outside `L`'s segments, so none of the data
regions of a contract over `L` (which `CallOf` keeps apart from `L`), and, where `L` holds only the function's and its
callees' bytes, none of its caller's code before it returns; a list that holds the whole executable segment says
less. -/
def InCode (L : List (Addr × List Byte)) (s : State) : Prop :=
  ∃ c ∈ L, ∃ k, k < c.2.length ∧ s.cpu.rip = c.1.add k

/-- The code segments `code` (pairs of an address and the bytes there) implement contract `C` at
`entry` on processor `prof`: every call of it (`CallOf`: at `entry`, from a thread that may start one,
with an ordinary footprint and `C.pre`), on every run in the environment `C` assumes (`Contract.env`:
`Undisturbed` unless given), either returns as `C` says (`Returned`) or ends the process with an
outcome and events satisfying `C.ends s₀` (never, for a contract without `ends`), and until then executes only the
code `code`: at every state before the return or the end, `rip` lies in one of its segments (`InCode`,
`ReachOrEndsIn`). So the call's control flow stays in the code the statement names: it executes no byte outside
`code`'s segments, so none of the contract's data regions, and, where `code` holds only the function's and its callees'
bytes, none of its caller's code before it returns.

The segments are the code the calls may run: the function's own and that of the functions it calls. A function's
statement does not fix them: it is over every list `L` that holds the function's bytes as a slice of one of its
segments (`∀ L, CodeIn L entry bytes → …`), and each function it calls is a hypothesis over the same `L`
(`ImplementsCall prof g L Cg`, by the callee's contract `Cg`), so that the statement names its own code and its
callees' contracts and nothing of their code. A program's statement fixes `L` once, at link time: the byte ranges of
the functions its run may reach, each a slice of a segment the program's objects are loaded from, and nothing else.
`L` must not hold bytes a contract reads, writes or owns: `Footprint.Ok` keeps a call's data apart from every segment of
`L`, so with such bytes in `L` (read-only data or the ELF headers in a code segment linked without `-z
separate-code`, a table in hand-written assembly) no call meets `CallOf` and the statement holds vacuously. A
statement over a list with more segments, or longer ones, says no more: it follows from the one over the smaller list
(the larger list's `CallOf` gives the smaller's), and covers only calls whose data also lies apart from the extra
bytes, which must also be present, fetchable and unaliased (and it confines the control flow less). -/
def ImplementsCall (prof : Profile) (entry : Addr) (code : List (Addr × List Byte)) (C : Contract) :
    Prop :=
  ∀ s₀ ra, CallOf prof entry code C s₀ ra →
    ReachOrEndsIn prof (C.env s₀) s₀ (InCode code) (Returned prof.feat C s₀ ra) (C.ends s₀)

/-- The code segments `code` implement contract `C` at `entry` on processor `prof` up to the state `C.post`
describes: every call of it (`CallOf`), on every run in the environment `C` assumes, reaches a state `X` with the frame
kept up to there, `C.post s₀ X` and the events so far satisfying `C.events` (`Contract.Reached`), or ends the process
as `C.ends` allows, with `rip` in `code` at every state before (`InCode`, as for `ImplementsCall`). `ImplementsCall`
without the return (`Returns`): for code that is entered by a call but whose part a
statement speaks of ends at another point, where the run goes on into code the statement names otherwise. A C
library's startup is such code: called by the program's entry point, it calls the program's `main`, and its
contract's `post` says that `X` is at that call (`CallShape`; `Spec/Lib/C/Start.lean`). The state is one the run
passes through, not necessarily the first with `C.post` (as for `ImplementsCall`, `ReachOrEnds`). The convention's exit
conditions (`Conv.exit`) are not used. -/
def ImplementsCallUpto (prof : Profile) (entry : Addr) (code : List (Addr × List Byte)) (C : Contract) : Prop :=
  ∀ s₀ ra, CallOf prof entry code C s₀ ra →
    ReachOrEndsIn prof (C.env s₀) s₀ (InCode code) (C.Reached prof.feat s₀) (C.ends s₀)

/-- The code segments `code` implement contract `C` at `entry` on processor `prof` up to the state `C.post` describes,
if the run gets there: every call of it (`CallOf`), on every run in the environment `C` assumes, at every point has
passed through a state `X` with the frame kept up to there, `C.post s₀ X` and the events so far satisfying `C.events`
(`Contract.Reached`), or is still running, in a state whose `rip` lies in `code` (`InCode`), with the events so far
satisfying `C.events` (at the state it is in), or has ended the process as `C.ends` allows (`ReachIf`). So before it
gets there the run executes only `code`: a state whose `rip` lies outside it (the program's `main`, apart from a C
library's startup code) is one the run reaches only after it got there. `ImplementsCallUpto` without the promise to
get there: for code that may run for ever before the point its contract speaks of, and that until then keeps to its
events and ends the process only as `C.ends` allows. A C library's startup is such code: it may loop for ever on the
clock's readings for the heap's key, or end the process after a refused memory request, before it calls `main`
(`Spec/Lib/C/Start.lean`). -/
def ImplementsCallUptoIf (prof : Profile) (entry : Addr) (code : List (Addr × List Byte)) (C : Contract) : Prop :=
  ∀ s₀ ra, CallOf prof entry code C s₀ ra →
    ReachIf prof (C.env s₀) s₀ (C.Reached prof.feat s₀) (fun s evs => InCode code s ∧ C.events s₀ s evs) (C.ends s₀)

/-- `s₀` is a resumption, on processor `prof`, of the code at `entry` with code segments `code` and contract `C`:
`rip` is `entry`, the thread may run (`Ready`), the footprint is ordinary memory it can use (`Footprint.Ok`), and the
contract's precondition holds. `CallOf` without the call: the code is entered other than by a call, where a call it
made returns (a C library's exit, entered where the program's `main` returns into the library), so there is no
return address on the stack, and what holds of `rsp` and the flags (a return's `Conv.exit`) is the precondition's
business. -/
structure ResumeOf (prof : Profile) (entry : Addr) (code : List (Addr × List Byte)) (C : Contract) (s₀ : State) :
    Prop where
  rip : s₀.cpu.rip = entry
  ready : Ready prof.feat s₀
  foot : (C.footprint code s₀).Ok prof.feat s₀
  pre : C.pre s₀

/-- The code segments `code` implement contract `C` from `entry` on processor `prof`: every resumption of it there
(`ResumeOf`: not a call), on every run in the environment `C` assumes, reaches a state `X` as `C` says of it
(`Contract.Reached`), or ends the process as `C.ends` allows, with `rip` in `code` at every state before (`InCode`, as
for `ImplementsCall`). With `post` `False`, the run ends the process: a C
library's exit after the program's `main` returned into it (`Spec/Lib/C/Start.lean`). -/
def ImplementsAtUpto (prof : Profile) (entry : Addr) (code : List (Addr × List Byte)) (C : Contract) : Prop :=
  ∀ s₀, ResumeOf prof entry code C s₀ →
    ReachOrEndsIn prof (C.env s₀) s₀ (InCode code) (C.Reached prof.feat s₀) (C.ends s₀)

/-! ## Allocators -/

/-- What an allocator's invariant sees of the process (`Heap.inv`, `Heap.view`): all its invariant may
depend on, so that what a caller does outside it keeps the invariant.
- `bytes`: the bytes the allocator owns outside the live blocks, and `0` at every other address
  (`Heap.bytes`), so stores into live blocks and anywhere outside what it owns keep the invariant;
- `access`: the accesses the thread may make at the bytes the allocator owns, and none at any other
  address (`Heap.access`): which of its pages it may read and write, without the mappings' other
  details;
- `brk`: the program break (`Mm.brk`): an allocator that grows by `brk` keeps where it thinks the break
  is (musl's `ctx.brk`), and is right only while nobody else moves it;
- `fs`: the thread's `FS` base (`Segs.fsBase`), at which its thread-local storage lies (glibc's `tcache`
  and `thread_arena`, `malloc/malloc.c`);
- `reads`: the bytes of the regions the allocator reads without owning them (`Heap.reads` at `fs`), and
  `0` at every other address (`Heap.readBytes`): data of others it depends on, such as glibc's
  `__libc_single_threaded` and `_dl_pagesize`. -/
structure Heap.View where
  bytes : Addr → Byte
  access : Addr → Access → Prop
  brk : Addr
  fs : Addr
  reads : Addr → Byte

/-- An allocator (`malloc` and `free`) as its callers see it, without its code: the bytes of stack
its functions use below their entry `rsp` (`stack`), the alignment of its blocks (`align`; 16 for
glibc's `malloc` on x86-64, `MALLOC_ALIGNMENT` in `sysdeps/generic/malloc-alignment.h`), the regions it
reads without owning them (`reads`) and those it may change without owning them (`writes`), and its
invariant `inv own v live` over the regions `own` it owns, what it sees of the process (`v`, a
`Heap.View`, read from a state by `Heap.view`) and the live blocks `live`. The invariant is abstract: a
statement that quantifies over `H` holds for every allocator that keeps the contracts `H.malloc` and
`H.free`, whatever its invariant is.

`reads` and `writes` are functions of the thread's `FS` base (they may lie in its thread-local storage),
none unless given. What an allocator reads without owning it is data others may change between its calls
(glibc's `__libc_single_threaded`, which creating a thread clears), so its invariant sees those bytes
(`Heap.View.reads`). What it changes without owning it is data others change too, whose value at a return
its contracts do not fix: a C library's `errno` (`Spec/Lib/C/Malloc.lean`), which glibc's `malloc` sets even
when it succeeds.

What the allocator owns is not part of `H`: each call takes the regions it owns at the call (`own`,
its static data, the memory it has mapped) and returns the regions it owns at the return (`∃ own'`,
`Heap.Next`), and a caller hands those to the next call. Inside a call the allocator may map new
memory and map, unmap or change the pages wholly in what it owns (`brk`, `mmap`, `munmap`,
`mprotect`) and move the program break (`Contract.layout`, `Layout.owns`). -/
structure Heap where
  stack : Nat
  align : Nat
  reads : Addr → List Rgn := fun _ => []
  writes : Addr → List Rgn := fun _ => []
  inv : List Rgn → Heap.View → List Rgn → Prop

/-- The bytes of `s` that an allocator owning the regions `own` owns outside the blocks `live`, and
`0` at every other address (`Heap.View.bytes`). -/
def Heap.bytes (own : List Rgn) (s : State) (live : List Rgn) (a : Addr) : Byte :=
  if Foot own a ∧ ¬ Foot live a then s.proc.mm.mem.readByte a else 0

/-- The accesses the thread of `s` may make at the bytes of the regions `own`, on a processor with
features `feat` (`Heap.View.access`): `acc` at `a` when `a` lies in `own`, is canonical and passes
`Memory.check` with the thread's `PKRU`; none at any other address. A caller that keeps the layout of
what the allocator owns and `PKRU` keeps it. -/
def Heap.access (feat : Features) (own : List Rgn) (s : State) (a : Addr) (acc : Access) : Prop :=
  Foot own a ∧ a.canonical feat.la57 = true ∧ s.proc.mm.mem.check feat s.cpu.pkru acc a = none

/-- The bytes of `s` in the regions `rs`, and `0` at every other address (`Heap.View.reads`). -/
def Heap.readBytes (rs : List Rgn) (s : State) (a : Addr) : Byte :=
  if Foot rs a then s.proc.mm.mem.readByte a else 0

/-- What the invariant of the allocator `H` owning the regions `own`, with the blocks `live` live, sees of
the state `s` on a processor with features `feat`: the bytes it owns outside the live blocks, the
accesses the thread may make at what it owns, the program break, the thread's `FS` base, and the bytes it
reads without owning them there. -/
def Heap.view (H : Heap) (feat : Features) (own : List Rgn) (s : State) (live : List Rgn) : Heap.View where
  bytes := Heap.bytes own s live
  access := Heap.access feat own s
  brk := s.proc.mm.brk
  fs := s.cpu.seg.fsBase
  reads := Heap.readBytes (H.reads s.cpu.seg.fsBase) s

/-- In `s`, the regions the allocator `H` reads and those it changes without owning them (at the thread's
`FS` base) lie apart from its stack frame of `k` bytes (`frame`) and from the regions `own` it owns, and
those it reads apart from those it changes: a store into its frame or what it owns, or into what it may
change, leaves what it reads as it was, and a caller's stores into its live blocks (in `own`) leave
both. -/
def Heap.Outside (H : Heap) (s : State) (k : Nat) (own : List Rgn) : Prop :=
  Apart (H.reads s.cpu.seg.fsBase ++ H.writes s.cpu.seg.fsBase) (frame s k :: own) ∧
    Apart (H.reads s.cpu.seg.fsBase) (H.writes s.cpu.seg.fsBase)

/-- From `s` to `X`, every page holding a byte of the regions `rs` keeps its mapping, and its backing
is refined as by stores (`Backing.Refines`): what a caller needs to go on using the live blocks of
an allocator that may change the layout of the rest of what it owns. -/
def KeepsPages (rs : List Rgn) (s X : State) : Prop :=
  ∀ a, Foot rs a → ∀ m, s.proc.mm.mem.map (pageOf a) = some m →
    X.proc.mm.mem.map (pageOf a) = some m ∧
    (X.proc.mm.mem.backings m.backing).Refines s.proc.mm.mem.files (s.proc.mm.mem.backings m.backing)

/-- From the call `s` to the return `X` of one of its functions, an allocator went from owning the
regions `own` to owning `own'`, with the blocks `live` live at the return: each byte it owns at the
return it owned at the call or lies in memory it mapped since, the live blocks are its, and what it owns
at the return is memory the next call can own (`Footprint.Ok`'s facts about owned regions, and the
thread's `rseq` area apart). So a caller's data, which are mapped and apart from `own`, stay apart from
`own'`, and the next call's hypotheses about `own'` alone hold. The `rseq` area's part follows from the
others at every return `ImplementsCall` speaks of (the area was mapped and apart from `own` at the call, and
its registration is kept), so it adds nothing to a contract; it is stated for the caller. (The name: what
the allocator owns next; it may grow or shrink.) -/
structure Heap.Next (s X : State) (live own own' : List Rgn) : Prop where
  /-- Every region of `own'` fits. -/
  fits : ∀ r ∈ own', r.Fits
  /-- Each byte of `own'` lies in `own`, or in a page that was not mapped at the call (memory the
  allocator mapped since). -/
  grown : ∀ a, Foot own' a → Foot own a ∨ s.proc.mm.mem.map (pageOf a) = none
  /-- The live blocks lie in `own'`. -/
  live : ∀ a, Foot live a → Foot own' a
  /-- No byte of `own'` is in a page the kernel owns or may drop (`NotKernel`). -/
  notKernel : NotKernel X own'
  /-- No byte of `own'` is in a shared mapping (`NotShared`). -/
  notShared : NotShared X own'
  /-- No two pages of `own'` alias (`NoAliasOver`). -/
  noAlias : NoAliasOver X own'
  /-- No byte of `own'` is in a page of the vDSO or a first page of the stack (`NotFixed`). -/
  notFixed : NotFixed X own'
  /-- The thread's `rseq` area lies apart from `own'`. -/
  rseqApart : Apart (rseqArea X) own'

/-- At the state `X`, reached from `s` where it owned the regions `own`, the allocator `H` is intact
with the blocks `live` live, on a processor with features `feat`: it owns regions `own'` that arose
from `own` as `Heap.Next` allows, and its invariant holds for them and the live blocks. What `free`
promises, and a caller of the allocator at its return. -/
def Heap.Intact (H : Heap) (feat : Features) (s X : State) (own live : List Rgn) : Prop :=
  ∃ own', Heap.Next s X live own own' ∧ H.inv own' (H.view feat own' X live) live

/-- `malloc(n)` of the allocator `H` owning the regions `own` while the blocks `live` are live, on a
processor with features `feat` (C17 7.22.3.4; `n` in `rdi`, the result in `rax`), as a contract:
called with its invariant holding, its stack frame apart from what it owns, the live blocks in what it
owns, `PKRU` allowing access with key 0 (the key of every new mapping), and what it reads and changes
without owning it apart from its frame and what it owns (`Heap.Outside`), it reads `H.reads`, writes at
most its frame, `H.writes` and `own`, may map new memory, change the layout of the pages wholly in `own`
and move the program break (`layout`), and makes only the memory calls of an allocator
(`Event.IsMemCall`); it leaves the bytes of the live blocks and the mappings of their pages as they are, and returns owning some regions `own'` (`Heap.Next`) and
either a null pointer, its invariant holding for the same live blocks, or the address `p` of a new
block `⟨p, n⟩` of `n` bytes that fits, is aligned to `H.align`, lies in `own'` (so it aliases no other
memory it owns, and none of its caller's) and apart from the live blocks, and can be written, its
invariant holding with that block live too. (Without the live blocks in `own`, so apart from the
frame, no code could keep this contract for every `live`: its own stack writes would change the bytes
of a block in its frame.) -/
def Heap.malloc (H : Heap) (feat : Features) (own live : List Rgn) : Contract where
  conv := sysv
  reads s := H.reads s.cpu.seg.fsBase
  writes s := frame s H.stack :: H.writes s.cpu.seg.fsBase
  pre s := H.inv own (H.view feat own s live) live ∧ Apart [frame s H.stack] own ∧
    (∀ a, Foot live a → Foot own a) ∧ s.cpu.pkru &&& 3 = 0 ∧ H.Outside s H.stack own
  post s X := SameBytes s X live ∧ KeepsPages live s X ∧ ∃ own', Heap.Next s X live own own' ∧
    (X.cpu.gpr.rax = 0 ∧ H.inv own' (H.view feat own' X live) live ∨
     let b : Rgn := ⟨X.cpu.gpr.rax, s.cpu.gpr.rdi.toNat⟩
     X.cpu.gpr.rax ≠ 0 ∧ b.Fits ∧ X.cpu.gpr.rax.toNat % H.align = 0 ∧
       (∀ a, b.Mem a → Foot own' a) ∧ Apart [b] live ∧ Accessible feat X .write b ∧
       H.inv own' (H.view feat own' X (b :: live)) (b :: live))
  events _ _ evs := ∀ ev ∈ evs, Event.IsMemCall ev
  layout _ := .owns own (movesBrk := true)

/-- `free(p)` of the allocator `H` owning the regions `own` (C17 7.22.3.3) for the live block
`some b`, while the blocks `front ++ b :: back` are live (`p = b.base` in `rdi`), or of a null
pointer, `b = none` (`p = 0`, the live blocks `front ++ back`, nothing freed), on a processor with
features `feat`, as a contract: called with its invariant holding, its stack frame apart from what it
owns, the live blocks in what it owns, `PKRU` allowing access with key 0 (the key of every new mapping: a
`free` may map memory, glibc's where it sets up a thread's cache), and what it reads and changes without
owning it apart from its frame and what it owns (`Heap.Outside`), it reads `H.reads`, writes at most its
frame, `H.writes` and `own`, may change the layout
and move the break as `malloc` may, makes only the memory calls of an allocator, leaves the bytes of the other live
blocks and the mappings of their pages as they are, and returns with the allocator intact for them
(`Heap.Intact`). -/
def Heap.free (H : Heap) (feat : Features) (own front : List Rgn) (b : Option Rgn) (back : List Rgn) :
    Contract where
  conv := sysv
  reads s := H.reads s.cpu.seg.fsBase
  writes s := frame s H.stack :: H.writes s.cpu.seg.fsBase
  pre s := H.inv own (H.view feat own s (front ++ (b.toList ++ back))) (front ++ (b.toList ++ back)) ∧
    s.cpu.gpr.rdi = (b.map (·.base)).getD 0 ∧ Apart [frame s H.stack] own ∧
    (∀ a, Foot (front ++ (b.toList ++ back)) a → Foot own a) ∧ s.cpu.pkru &&& 3 = 0 ∧ H.Outside s H.stack own
  post s X := SameBytes s X (front ++ back) ∧ KeepsPages (front ++ back) s X ∧
    H.Intact feat s X own (front ++ back)
  events _ _ evs := ∀ ev ∈ evs, Event.IsMemCall ev
  layout _ := .owns own (movesBrk := true)

/-- The code segments `code` implement, at `entry` on processor `prof`, the `malloc` of the allocator
`H`: its contract `H.malloc` for whatever the allocator owns at the call and every set of live blocks. -/
def Heap.MallocAt (H : Heap) (prof : Profile) (entry : Addr) (code : List (Addr × List Byte)) : Prop :=
  ∀ own live, ImplementsCall prof entry code (H.malloc prof.feat own live)

/-- The code segments `code` implement, at `entry` on processor `prof`, the `free` of the allocator `H`:
its contract `H.free` for whatever the allocator owns at the call, every live block and a null pointer,
and every set of other live blocks. -/
def Heap.FreeAt (H : Heap) (prof : Profile) (entry : Addr) (code : List (Addr × List Byte)) : Prop :=
  ∀ own front b back, ImplementsCall prof entry code (H.free prof.feat own front b back)

/-- The code segments `code` implement the allocator `H` on processor `prof`, its `malloc` at `mallocE`
(`Heap.MallocAt`) and its `free` at `freeE` (`Heap.FreeAt`): what a client's statement assumes of its code list
(`ImplementsCall`). An allocator's own statement proves each half for every list that holds that function's bytes
(`CodeIn`); together they give this for every list that holds both functions' bytes. -/
def Heap.ImplementedBy (H : Heap) (prof : Profile) (code : List (Addr × List Byte)) (mallocE freeE : Addr) : Prop :=
  H.MallocAt prof mallocE code ∧ H.FreeAt prof freeE code

/-- What a function that uses an allocator says of itself besides the allocator (`Heap.client`): the
bytes of stack its own code uses below its entry `rsp`, the return addresses its own `call`s push included
(`stack`; the allocator's `H.stack` come below them), the
regions it reads and writes besides its stack (`reads`, `writes`, functions of the entry state; none
unless given), its precondition `pre` (`True` unless given), its postcondition `post` about the
entry and the return state, and, as in a `Contract` (whose fields of the same names they become):
- `live`: the live blocks at the return, from those at the call and the entry and return states; the
  same as at the call unless given. A function that allocates a block and keeps it live (a stream's
  buffer) adds it, one that frees a block of its caller's drops it;
- `events`: what its system calls are, about the entry and the return state; only the allocator's
  memory calls (`Event.IsMemCall`) unless given;
- `ends`: how it may end the process (`Contract.ends`); never unless given;
- `sets`, `moves`, `writesTo`: the thread's settings it may change, the descriptors whose positions it may move and
  those whose files it may change (`Contract.sets`, `Contract.moves`, `Contract.writesTo`); none unless given;
- `env`: what it assumes of the environment while it runs (`Contract.env`); `Undisturbed` unless
  given. -/
structure Heap.Use where
  stack : Nat
  reads : State → List Rgn := fun _ => []
  writes : State → List Rgn := fun _ => []
  pre : State → Prop := fun _ => True
  post : State → State → Prop
  live : List Rgn → State → State → List Rgn := fun live _ _ => live
  events : State → State → List Event → Prop := fun _ _ evs => ∀ ev ∈ evs, Event.IsMemCall ev
  ends : State → Outcome → List Event → Prop := fun _ _ _ => False
  sets : State → List Setting := fun _ => []
  moves : State → List Nat := fun _ => []
  writesTo : State → List Nat := fun _ => []
  env : State → Oracle → Prop := fun _ => Undisturbed

/-- The contract of a function `u` that uses the allocator `H` (calls its `malloc` and `free`), owning the
regions `own` at the call, while its caller's blocks `live` are live, on a processor with features
`feat`: called with the allocator's invariant holding, its stack (its own `u.stack` bytes, the return
address and the allocator's `H.stack`) apart from what the allocator owns, the live blocks in what it
owns, `PKRU` allowing access with key 0 (the allocator may map memory), `u.pre`, and what the allocator
reads and changes without owning it apart from that stack and what it owns (`Heap.Outside`), it returns
with the allocator intact for the live blocks `u.live` gives (`Heap.Intact`; those at the call unless
given) and `u.post`; it reads `H.reads` and `u.reads`, writes at most its stack, `H.writes`, `u.writes`
and what the allocator owns, may map new memory, change the layout of what the allocator owns and move the
program break as the allocator may, and makes the system calls `u.events` allows (only the allocator's
memory calls, `Event.IsMemCall`, unless given). Whatever it promises about its caller's blocks (their
bytes, their pages) and about how its own regions lie relative to what the allocator owns is in `u.pre`
and `u.post`. -/
def Heap.client (H : Heap) (feat : Features) (own live : List Rgn) (u : Heap.Use) : Contract where
  conv := sysv
  reads s := H.reads s.cpu.seg.fsBase ++ u.reads s
  writes s := frame s (H.stack + u.stack) :: (H.writes s.cpu.seg.fsBase ++ u.writes s)
  pre s := H.inv own (H.view feat own s live) live ∧ Apart [frame s (H.stack + u.stack)] own ∧
    (∀ a, Foot live a → Foot own a) ∧ s.cpu.pkru &&& 3 = 0 ∧ u.pre s ∧ H.Outside s (H.stack + u.stack) own
  post s X := H.Intact feat s X own (u.live live s X) ∧ u.post s X
  events := u.events
  ends := u.ends
  layout _ := .owns own (movesBrk := true)
  sets := u.sets
  moves := u.moves
  writesTo := u.writesTo
  env := u.env

end ZellicX86
