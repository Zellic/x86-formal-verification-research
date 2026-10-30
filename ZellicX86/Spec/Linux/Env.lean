import ZellicX86.Spec.Linux.Stack
/-!
# Linux: environment events

What each event between two instructions (`EnvEvent`, `Spec/Request.lean`) does to the
process: the kernel's return to user mode (with the `rseq` update), signals from outside,
changes to kernel pages and files, early copy-on-write, writes by other processes and by a
tracer, a tracer's reads (which only a stack's growth would show), resource limits set by another process, and the reclaim of lazily freed pages.

Sources: `kernel/rseq.c`, `kernel/signal.c`, `mm/gup.c`, `arch/x86/kernel/ptrace.c`,
`kernel/sys.c`, `mm/vmscan.c`.
-/
namespace ZellicX86
open Signal

/-- The kernel's update of the thread's `rseq` area at a return to user mode (`kernel/rseq.c`
`__rseq_handle_notify_resume`), with the thread on CPU `cpu`, node `node`, concurrency id `mmCid`:
with an area registered it stores `cpu_id_start`, `cpu_id`, `node_id` and `mm_cid` (offsets 0, 4,
20, 24 of `struct rseq`, `include/uapi/linux/rseq.h`); if the area's `rseq_cs` field (offset 8) is
set, the kernel first checks whether `rip` is inside that critical section and may move it to the
abort handler, which is not modelled (`.error`). `.ok none`: a read or a write failed, and the kernel
forces `SIGSEGV` (`force_sigsegv`), which its caller does. Its accesses fault into the page-fault
handler, which may grow a stack for them (`growFor`); where it may (`mayGrowFor`: an area on a page of
a stack that was unmapped), a failed update is not modelled (the update is computed without asking the
environment, so the model cannot follow a stack growth there). On a return from an interrupt or
exception the kernel also stores 0 into
`rseq_cs` when it is already 0 (`rseq_ip_fixup`, `clear_rseq_cs`); that store changes no byte and, on
the same page as the ids (`rseq` registers only areas aligned to 32 bytes), faults exactly when
theirs do, so it is left out. -/
def rseqUpdate (feat : Features) (s : State) (cpu node mmCid : BitVec 32) : Except Outcome (Option State) :=
  match s.thread.rseq with
  | none => .ok (some s)
  | some r =>
    let failed : Except Outcome (Option State) :=
      if mayGrowFor feat s .write r.area 28 then
        .error (.notModelled (.feature "an rseq update for which the kernel may grow a stack"))
      else .ok none
    match kernelRead feat s (r.area.add 8) 8 with
    | none => failed
    | some cs =>
      if ofBytesLE 64 cs ≠ 0 then .error (.notModelled (.feature "rseq critical section"))
      else
        let ids := [(0, cpu), (4, cpu), (20, node), (24, mmCid)]
        match ids.foldl (fun acc (o, v) => acc.bind fun t =>
          kernelWrite feat t (r.area.add o) (toBytesLE v 4)) (some s) with
        | some t => .ok (some t)
        | none => failed

/-- The kernel ran and returns to user mode: it updates the `rseq` area (`rseqUpdate`); a failed
update sends `SIGSEGV` (`force_sigsegv(0)`, which is `force_sig`: `forceSignal`). -/
def kernelEntry (feat : Features) (s : State) (cpu node mmCid : BitVec 32) : StepResult :=
  match rseqUpdate feat s cpu node mmCid with
  | .ok (some t) => .running t none
  | .ok none => forceSignal s SIGSEGV .kernel
  | .error o => .stopped o

/-- Whether another process may write the byte at `a` through the kernel (`mm/gup.c`
`check_vma_flags` with `FOLL_REMOTE | FOLL_WRITE`): a user address, mapped, not a page the
kernel owns (`VM_IO | VM_PFNMAP`), not a file page wholly beyond the end of its file, and
either the mapping is writable or, with `force` (`FOLL_FORCE`), private (a copy-on-write
mapping), whatever its protection; the write then goes to the process's private copy.
Protection keys do not restrict another process (`arch_vma_access_permitted` with
`foreign`). -/
def remoteWritable (feat : Features) (mem : Memory) (force : Bool) (a : Addr) : Bool :=
  decide (a.toNat < userPtrMax feat) &&
  match mem.map (pageOf a) with
  | none => false
  | some m =>
    match mem.backings m.backing with
    | .kernel _ => false
    | .file fp => !mem.files.beyondEof fp && m.prot.write
    | .cow fp => !mem.files.beyondEof fp && (m.prot.write || force)
    | .priv _ | .freed _ => m.prot.write || force

/-- Whether a tracer may read the byte at `a` through the kernel with `FOLL_FORCE` (`ptrace(2)`,
`/proc/PID/mem`; `mm/gup.c` `check_vma_flags`): a user address, mapped, not a page the kernel owns
(`VM_IO | VM_PFNMAP`), not a file page wholly beyond the end of its file, whatever its protection. -/
def remoteReadable (feat : Features) (mem : Memory) (a : Addr) : Bool :=
  decide (a.toNat < userPtrMax feat) &&
  match mem.map (pageOf a) with
  | none => false
  | some m =>
    match mem.backings m.backing with
    | .kernel _ => false
    | .file fp | .cow fp => !mem.files.beyondEof fp
    | .priv _ | .freed _ => true

/-- Whether a tracer's access of the `n` bytes from `a` (`ptrace(2)`, `/proc/PID/mem`:
`__access_remote_vm`, `mm/memory.c`) may grow a stack in memory `mem`: the first byte it cannot access
(`ok`: `remoteWritable` with `FOLL_FORCE` for a write, `remoteReadable` for a read) lies below
`TASK_SIZE` on a page no mapping covers (`growthFault`), and the first mapped page above it belongs to a
mapping that grows down (`Memory.stackAbove` with no limit short of `TASK_SIZE`). The kernel then grows
the stack as for a fault (`expand_stack`), with the limits of the tracer, which the model does not have.
(`process_vm_writev` and `process_vm_readv` grow nothing: `get_user_pages` never does, `mm/gup.c`
`gup_vma_lookup`.) -/
def remoteMayGrow (feat : Features) (mem : Memory) (ok : Addr → Bool) (a : Addr) (n : Nat) : Bool :=
  (growthFault feat mem ok a n).any fun x => (mem.stackAbove feat (taskSize feat / 4096) x).isSome

/-- `f` with the bits a tracer may set taken from `v` (`arch/x86/kernel/ptrace.c`
`FLAG_MASK`). -/
def Rflags.setTraced (f : Rflags) (v : BitVec 64) : Rflags :=
  { f with cf := v.getLsbD 0, pf := v.getLsbD 2, af := v.getLsbD 4, zf := v.getLsbD 6,
           sf := v.getLsbD 7, tf := v.getLsbD 8, df := v.getLsbD 10, of := v.getLsbD 11,
           nt := v.getLsbD 14, rf := v.getLsbD 16, ac := v.getLsbD 18 }

/-- Apply a tracer's register write. -/
def tracerWrite (feat : Features) (s : State) : TracerWrite → StepResult
  | .gpr r v => .running (s.modCpu fun c => { c with gpr := c.gpr.set r v }) none
  | .rip v => .running (s.modCpu fun c => { c with rip := v }) none
  | .rflags v => .running (s.modCpu fun c => { c with rflags := c.rflags.setTraced v }) none
  | .segBase gs v =>
    if v.toNat < userPtrMax feat then
      .running (s.modCpu fun c =>
        { c with seg := if gs then { c.seg with gsBase := v } else { c.seg with fsBase := v } })
        none
    else .running s none
  | .selector => .stopped (.notModelled (.feature "tracer write of a segment selector"))
  | .debug => .stopped (.notModelled (.feature "tracer write of a debug register"))
  | .fpu => .stopped (.notModelled (.feature "tracer write of the x87, SSE, AVX or PKRU state"))

/-- Apply environment event `e`. -/
def envEvent (feat : Features) (s : State) : EnvEvent → StepResult
  | .kernelEntry cpu node mmCid => kernelEntry feat s cpu node mmCid
  | .signal sig => externalSignal s sig
  | .kernelData b f =>
    match s.proc.mm.mem.backings b with
    | .kernel (some _) => .running (s.withMem (s.proc.mm.mem.setBacking b (.kernel (some f)))) none
    | _ => .running s none
  | .fileWrite fp f =>
    if s.proc.mm.mem.files.denyWrite fp.file then .running s none
    else .running (s.withMem { s.proc.mm.mem with files := s.proc.mm.mem.files.setPage fp f }) none
  | .fileSize file size =>
    if s.proc.mm.mem.files.denyWrite file then .running s none
    else .running (s.withMem (s.proc.mm.mem.truncate file size)) none
  | .filePos f p => .running (s.setFilePos f p) none
  | .cowBreak b =>
    match s.proc.mm.mem.backings b with
    | .cow fp => .running (s.withMem (s.proc.mm.mem.setBacking b (.priv (s.proc.mm.mem.files.page fp)))) none
    | _ => .running s none
  | .remoteWrite a bs force =>
    if (byteAddrs a bs.length).all (remoteWritable feat s.proc.mm.mem force) then
      .running (s.withMem (writeBytes s.proc.mm.mem a bs)) none
    else if force && remoteMayGrow feat s.proc.mm.mem (remoteWritable feat s.proc.mm.mem true) a bs.length then
      .stopped (.notModelled (.feature "a tracer's write for which the kernel may grow a stack"))
    else .running s none
  | .remoteRead a n =>
    if remoteMayGrow feat s.proc.mm.mem (remoteReadable feat s.proc.mm.mem) a n then
      .stopped (.notModelled (.feature "a tracer's read for which the kernel may grow a stack"))
    else .running s none
  | .tracer w => tracerWrite feat s w
  | .reclaim b =>
    match s.proc.mm.mem.backings b with
    | .freed _ => .running (s.withMem (s.proc.mm.mem.setBacking b (.priv zeroFrame))) none
    | _ => .running s none
  | .rlimit res lim =>
    if lim.cur.toNat ≤ lim.max.toNat then
      .running { s with proc.signal.rlimits := fun r => if r = res then lim else s.proc.signal.rlimits r }
        none
    else .running s none

/-- Apply environment events in order, stopping at the first that ends the run. -/
def envEvents (feat : Features) (s : State) : List EnvEvent → StepResult
  | [] => .running s none
  | e :: es =>
    match envEvent feat s e with
    | .running s' _ => envEvents feat s' es
    | r => r

end ZellicX86
