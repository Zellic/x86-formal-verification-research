import ZellicX86.Spec.Linux
import ZellicX86.Spec.Linux.Vsyscall
/-!
# Steps and runs

One step of the process: first whatever the environment does before the next instruction
(`Request.between`), then fetch, decode and execute the instruction at `rip`, with the
kernel's handling of an exception or a `syscall`. A run is a sequence of steps.
-/
namespace ZellicX86

/-- The byte at offset `i` from `rip` as instruction fetch sees it: `none` if it cannot be
fetched (non-canonical, or `fetch` access faults). -/
def fetchByte (feat : Features) (s : State) (i : Nat) : Option Byte :=
  let a := s.cpu.rip.add i
  if a.canonical feat.la57 && (s.proc.mm.mem.check feat s.cpu.pkru .fetch a).isNone
  then some (s.proc.mm.mem.readByte a)
  else none

/-- What a failed fetch of the byte at `a` raises: `#GP(0)` for a non-canonical address, else `#PF` with the
instruction-fetch bit (SDM Vol. 3A, 7.15; 5.7). With `vsyscall=xonly` or `emulate`, a fault at `rip` itself on the
`vsyscall` page is the kernel's to emulate (`emulate_vsyscall`, `arch/x86/entry/vsyscall/vsyscall_64.c`, which
handles only a fetch at `rip`), by `emulateVsyscall`; with `vsyscall=none`, and for an instruction that only reaches
into the page, it is an ordinary `#PF` (`emulate_vsyscall` returns `false`). -/
def fetchFault (prof : Profile) (s : State) (a : Addr) : Req StepResult :=
  if !a.canonical prof.feat.la57 then raiseException prof s (.gp 0)
  else if pageOf a = vsyscallPage ∧ a = s.cpu.rip ∧ prof.linux.vsyscall ≠ .none then
    emulateVsyscall prof s
  else raiseException prof s (.pf a .fetch false)

/-- The state an exception `e` raised by an instruction leaves for the kernel, of the state `s` before
the instruction and `s₁` after its fetch: `#BP` is a trap, after the instruction (the signal frame
records the next `rip`, SDM Vol. 3A, 7.5); `#XM` leaves the flags it set in `MXCSR`
(`Exception.xm`); every other exception is a fault, before the instruction. -/
def exceptionState (s s₁ : State) : Exception → State
  | .bp => s₁
  | .xm m => s.modCpu fun c => { c with vec := { c.vec with mxcsr := m } }
  | _ => s

/-- Execute the instruction at `rip`. Single-stepping (`RFLAGS.TF = 1`, which raises `#DB`
after the instruction) is not modelled. -/
def instruction (prof : Profile) (s : State) : Req StepResult :=
  let feat := prof.feat
  if s.cpu.rflags.tf then Pure.pure (.stopped (.notModelled (.feature "single-step (RFLAGS.TF)")))
  else
  match Decode.decode feat (fetchByte feat s) with
  | .pf off => fetchFault prof s (s.cpu.rip.add off)
  | .gp => raiseException prof s (.gp 0)
  | .ud => raiseException prof s .ud
  | .nm map op => Pure.pure (.stopped (.notModelled (.encoding map op)))
  | .ok i => do
    -- `RF` is cleared at the start of every instruction (SDM Vol. 3B, 20.3.1.1)
    let s₁ := s.modCpu fun c => { c with rip := c.rip.add i.len, rflags := { c.rflags with rf := false } }
    match ← (exec prof i).run feat prof.linux.splitLock s₁ with
    | .ok .next s₂ => Pure.pure (.running s₂ none)
    | .ok .syscall s₂ => syscall prof s₂
    | .ok .again s₂ =>
      -- An iteration of a repeated string instruction that stored into the instruction's own
      -- bytes: whether the processor goes on with the instruction it has or fetches the new
      -- bytes is not specified (SDM Vol. 3A, 14.6 "Self-Modifying Code" covers prefetched
      -- instructions, not the one executing), so not modelled.
      if readBytes s₂.proc.mm.mem s.cpu.rip i.len = readBytes s.proc.mm.mem s.cpu.rip i.len then
        Pure.pure (.running (s₂.modCpu fun c => { c with rip := s.cpu.rip }) none)
      else Pure.pure (.stopped (.notModelled (.feature "string instruction storing into its own bytes")))
    | .exception e => raiseException prof (exceptionState s s₁ e) e
    | .notModelled w => Pure.pure (.stopped (.notModelled w))

/-- One step of the process on processor `prof`. -/
def step (prof : Profile) (s : State) : Req StepResult := do
  let evs ← Req.request (.between prof.cpus)
  match envEvents prof.feat s evs.val with
  | .running s' _ => instruction prof s'
  | r => Pure.pure r

/-- Where a run stands after some steps. -/
inductive Status
  | running (s : State)
  | done (o : Outcome)

/-- `n` steps from `s` with answers from stream `o` starting at position `t`: the status
reached, the system-call events in order, and the next stream position. -/
def run (prof : Profile) (o : Oracle) : Nat → State → Nat → Status × List Event × Nat
  | 0, s, t => (.running s, [], t)
  | n + 1, s, t =>
    match (step prof s).runStream o t with
    | (.running s' ev, t') =>
      match run prof o n s' t' with
      | (st, evs, t'') => (st, ev.toList ++ evs, t'')
    | (.stopped out, t') => (.done out, [], t')

end ZellicX86
