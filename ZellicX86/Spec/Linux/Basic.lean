import ZellicX86.Spec.Semantics
/-!
# Linux: signals for exceptions, and the kernel's access to user memory

How a step of the process ends (`StepResult`); the signal Linux sends for an exception raised
in user mode and what a forced or external signal does; the kernel reading and writing the
process's memory with user access rights; the user address bound.

Sources: `arch/x86/kernel/traps.c`, `arch/x86/mm/fault.c`, `kernel/signal.c`,
`arch/x86/include/asm/page_64.h`.
-/
namespace ZellicX86
open Signal

/-- The page number of the legacy vsyscall page at `0xffffffffff600000` (`VSYSCALL_ADDR`, Linux v6.18
`arch/x86/include/uapi/asm/vsyscall.h`). -/
def vsyscallPage : PageNum := pageOf 0xffffffffff600000


/-- How one step of the process ends. -/
inductive StepResult
  /-- The process continues in state `s`; `ev` is the system call it made, if any. -/
  | running (s : State) (ev : Option Event)
  /-- The run ends. -/
  | stopped (o : Outcome)

/-- Whether the kernel refuses access `acc` to a page of mapping `m` by the mapping's rights when the
access faults, before it tries to resolve the fault (`arch/x86/mm/fault.c` `access_error`, which
`do_user_addr_fault` calls first): the page's protection key forbids a data access
(`arch_vma_access_permitted`), a write meets a mapping without write permission, any other access a
mapping without any permission (`vma_is_accessible`). An instruction fetch counts as a read here: the
kernel brings in a page that is not present for it, and only a fetch from the present page then faults
for the execute-disable bit. -/
def accessError (feat : Features) (pkru : BitVec 32) (m : Mapping) (acc : Access) : Bool :=
  (feat.pku && pkeyDenies pkru m.pkey acc) || !m.allows feat (if acc = .write then .write else .read)

/-- Whether access `acc` at address `a`, made with `PKRU` value `pkru`, ends in `SIGBUS`: the page is
a file page wholly beyond the end of its file, or a kernel page without a source (pages whose fault
handler returns `VM_FAULT_SIGBUS`), and the kernel's check of the access against the mapping's rights,
which comes first, passes (`accessError`; otherwise `SIGSEGV`). -/
def sigbusAt (feat : Features) (pkru : BitVec 32) (mem : Memory) (acc : Access) (a : Addr) : Bool :=
  match mem.map (pageOf a) with
  | none => false
  | some m =>
    !accessError feat pkru m acc &&
      match (mem.backings m.backing).filePage with
      | some fp => mem.files.beyondEof fp
      | none => (mem.backings m.backing).noSource

/-- The signal Linux sends for exception `e` raised in user mode with `PKRU` value `pkru`
(`arch/x86/kernel/traps.c`; for `#PF`, `arch/x86/mm/fault.c`: `SIGBUS` where `sigbusAt` says so, else
`SIGSEGV`; for `#CP`, `arch/x86/kernel/cet.c`). `#NM` in user mode is not modelled. -/
def exceptionSignal (feat : Features) (pkru : BitVec 32) (mem : Memory) : Exception → Option Signal
  | .de => some SIGFPE
  | .db => some SIGTRAP
  | .bp => some SIGTRAP
  | .ud => some SIGILL
  | .nm => none
  | .ss _ => some SIGBUS
  | .gp _ => some SIGSEGV
  | .pf a acc _ => some (if sigbusAt feat pkru mem acc a then SIGBUS else SIGSEGV)
  | .mf => some SIGFPE
  | .ac => some SIGBUS
  | .xm _ => some SIGFPE
  | .cp _ => some SIGSEGV

/-! ## Sending and taking pending signals -/

/-- Whether the signal `sig` with action `a` is ignored (`sig_handler_ignored`, `kernel/signal.c`):
`SIG_IGN`, or `SIG_DFL` for a signal whose default action is to do nothing (`SIGCHLD`, `SIGURG`,
`SIGWINCH`, and `SIGCONT`, which only continues a stopped process). -/
def SigAction.ignores (a : SigAction) (sig : Signal) : Bool :=
  match a.disp with
  | .ignore => true
  | .default => defaultAction sig == .ign || defaultAction sig == .cont
  | .handler _ => false

/-- The signals only the kernel handles, whose action cannot change (`sig_kernel_only`): `SIGKILL`,
`SIGSTOP`. -/
def kernelOnly (sig : Signal) : Bool := sig == SIGKILL || sig == SIGSTOP

/-- Whether the kernel discards signal `sig` sent to the process in state `s` when it is not blocked
(`sig_task_ignored`, `kernel/signal.c`): its action ignores it (`SigAction.ignores`), or the process is
a PID namespace's init (`ProcSignal.unkillable`) and the action is `SIG_DFL`, unless the sender forces
(`force`: from an ancestor namespace, or the kernel's own) a signal only the kernel handles
(`kernelOnly`). -/
def sigTaskIgnored (s : State) (sig : Signal) (force : Bool) : Bool :=
  let a := s.proc.sighand sig
  (s.proc.signal.unkillable && a.disp matches .default && !(force && kernelOnly sig)) || a.ignores sig

/-- `p` without the entries of the signals `sigs` (`flush_sigqueue_mask`). -/
def SigPending.drop (p : SigPending) (sigs : List Signal) : SigPending :=
  p.filter fun q => !sigs.contains q.info.signo

/-- The stop signals, whose default action stops the process (`SIG_KERNEL_STOP_MASK`). -/
def stopSignals : List Signal := [SIGSTOP, SIGTSTP, SIGTTIN, SIGTTOU]

/-- `s` with signal pending `q` sent to the thread (`toThread`) or to the process
(`__send_signal_locked`, `prepare_signal`, `kernel/signal.c`): a stop signal discards a pending
`SIGCONT` and `SIGCONT` the pending stop signals; a signal that is ignored (`sigTaskIgnored`, the
sender forcing it or not, `force`) and not blocked is discarded; a signal 1–31 already pending in the
same set is not queued again (`legacy_queue`); otherwise its entry is queued last. `SIGKILL` does not
come here: it ends the process at once. -/
def sendSignal (s : State) (q : Queued) (toThread force : Bool) : State :=
  let sig := q.info.signo
  let flush : List Signal :=
    if stopSignals.contains sig then [SIGCONT] else if sig = SIGCONT then stopSignals else []
  let s₁ : State := if flush = [] then s else
    { s with proc.signal.pending := s.proc.signal.pending.drop flush,
             thread := { s.thread with pending := s.thread.pending.drop flush } }
  if !s₁.thread.sigmask.mem sig && sigTaskIgnored s₁ sig force then s₁
  else
    let pend := if toThread then s₁.thread.pending else s₁.proc.signal.pending
    if sig < 32 && pend.set.mem sig then s₁
    else if toThread then { s₁ with thread := { s₁.thread with pending := pend ++ [q] } }
    else { s₁ with proc.signal.pending := pend ++ [q] }

/-- The signals that cause an exception (`SYNCHRONOUS_MASK`, `kernel/signal.c`): `SIGSEGV`,
`SIGBUS`, `SIGILL`, `SIGTRAP`, `SIGFPE`, `SIGSYS`, taken before other pending signals. -/
def syncSignals : List Signal := [SIGSEGV, SIGBUS, SIGILL, SIGTRAP, SIGFPE, SIGSYS]

/-- The pending signal set `p` offers next with the signals in `mask` blocked (`next_signal`): the
lowest unblocked synchronous one if there is one, otherwise the lowest unblocked one. -/
def nextIn (p : SigPending) (mask : SigSet) : Option Signal :=
  let x := p.set &&& ~~~mask
  let sigs := (List.range 64).map (· + 1) |>.filter x.mem
  match sigs.find? syncSignals.contains with
  | some sig => some sig
  | none => sigs.head?

/-- `p`'s first entry for signal `sig`, and `p` without it (`collect_signal`). -/
def SigPending.take (p : SigPending) (sig : Signal) : Option (Queued × SigPending) :=
  match p.findIdx? (·.info.signo = sig) with
  | some i => p[i]?.map fun q => (q, p.eraseIdx i)
  | none => none

/-- The pending signal the kernel takes next for the thread, and the state without it
(`get_signal`: `dequeue_synchronous_signal`, then `dequeue_signal`): first the oldest entry of the
thread's set whose code says the kernel sent it for an exception (`si_code > 0`) of a synchronous
signal, provided some synchronous signal pending for the thread is unblocked (the kernel does not
check that the entry's own signal is); then the signal `nextIn` offers of the thread's set, then of
the process's. -/
def nextSignal (s : State) : Option (Queued × State) :=
  let tp := s.thread.pending
  let mask := s.thread.sigmask
  let syncUnblocked := syncSignals.any fun sig => tp.set.mem sig && !mask.mem sig
  let syncEntry := if syncUnblocked then
      tp.findIdx? fun q => q.info.code.toInt > 0 && syncSignals.contains q.info.signo
    else none
  match syncEntry with
  | some i => tp[i]?.map fun q => (q, { s with thread := { s.thread with pending := tp.eraseIdx i } })
  | none =>
    match nextIn tp mask with
    | some sig => (tp.take sig).map fun (q, tp') => (q, { s with thread := { s.thread with pending := tp' } })
    | none =>
      match nextIn s.proc.signal.pending mask with
      | some sig => (s.proc.signal.pending.take sig).map fun (q, pp) =>
          (q, { s with proc.signal.pending := pp })
      | none => none

/-- `s` with the action of signal `sig` set to `a`. -/
def State.setAction (s : State) (sig : Signal) (a : SigAction) : State :=
  { s with proc.sighand := fun x => if x = sig then a else s.proc.sighand x }

/-- The kernel forces signal `q` on the thread (`force_sig_info_to_task`, `kernel/signal.c`): if the
signal is blocked or ignored, its action is reset to `SIG_DFL` and it is unblocked; if its action is
then `SIG_DFL`, the process stops being unkillable (`ProcSignal.unkillable`); then it is sent to the
thread (as the kernel's own: a forced signal is never discarded, `sigTaskIgnored`). -/
def State.force (s : State) (q : Queued) : State :=
  let sig := q.info.signo
  let a := s.proc.sighand sig
  let s₁ := if s.thread.sigmask.mem sig || a.disp matches .ignore then
      { (s.setAction sig { a with disp := .default }) with
        thread := { s.thread with sigmask := s.thread.sigmask &&& ~~~((1 : SigSet) <<< (sig - 1)) } }
    else s
  let s₂ := if (s₁.proc.sighand sig).disp matches .default then
      { s₁ with proc.signal.unkillable := false } else s₁
  sendSignal s₂ q true true

/-- The kernel forces `SIGSEGV` on the thread because handling signal `sig` went wrong: its `rseq`
area could not be updated at the delivery, or its frame could not be written (`force_sigsegv`,
`kernel/signal.c`). When `sig` is `SIGSEGV` itself, `SIGSEGV`'s action is reset to `SIG_DFL` whatever
it was, and it is unblocked if blocked (`force_fatal_sig`, `HANDLER_SIG_DFL`), so it ends the process
when taken; otherwise it is forced as any signal (`State.force`), keeping a handler it has unless it
is blocked. -/
def State.forceSigsegv (s : State) (sig : Signal) : State :=
  let s₁ := if sig = SIGSEGV then s.setAction SIGSEGV { s.proc.sighand SIGSEGV with disp := .default }
    else s
  s₁.force ⟨SigInfo.kernel SIGSEGV, .kernel⟩

/-- A signal the kernel forces on the process at a point where the model does not deliver to handlers
(a failed `rseq` update at a return to user mode, `kernelEntry`). The only signal forced here,
`SIGSEGV`, terminates by default, so the process ends, unless a handler is installed and the signal is
unblocked; that delivery is not modelled. -/
def forceSignal (s : State) (sig : Signal) (cause : KillCause) : StepResult :=
  match (s.proc.sighand sig).disp with
  | .handler _ =>
    if s.thread.sigmask.mem sig then .stopped (.killed sig cause)
    else .stopped (.notModelled (.signalHandler sig))
  | _ => .stopped (.killed sig cause)

/-- Signal `q` sent to the process (`toThread = false`) or to the thread at a point where the model
does not deliver to handlers (between instructions, from outside; by the kernel at the end of `write`),
by a sender that forces it or not (`force`, `sigTaskIgnored`). A blocked signal is left pending
(`sendSignal`). An unblocked one is handled at once, as the kernel does on its way back to user mode
(every other pending signal being blocked): it is discarded if ignored (`sigTaskIgnored`, which
includes a `SIG_DFL` signal to a PID namespace's init; by `sendSignal`); it ends the process if its
default action terminates; a default action that stops the process is not modelled (a stopped process
waits, possibly forever, which a run cannot express); delivery to a handler is not modelled here. A
stop signal discards a pending `SIGCONT`, and `SIGCONT` the pending stop signals, whatever then becomes
of the signal (`prepare_signal`). `SIGKILL` is not sent here. -/
def sendNoHandler (s : State) (q : Queued) (toThread force : Bool) : StepResult :=
  let sig := q.info.signo
  if s.thread.sigmask.mem sig || sigTaskIgnored s sig force then .running (sendSignal s q toThread force) none
  else
    match (s.proc.sighand sig).disp with
    | .ignore => .running (sendSignal s q toThread force) none
    | .handler _ => .stopped (.notModelled (.signalHandler sig))
    | .default =>
      match defaultAction sig with
      | .term | .core => .stopped (.killed sig q.cause)
      | .stop => .stopped (.notModelled (.feature "a signal that stops the process"))
      | .ign | .cont => .running (sendSignal s q toThread force) none

/-- Signal `sig` sent to the process from outside (`kernel/signal.c` `send_signal_locked`,
`get_signal`), arriving between two instructions. Numbers outside 1–64 are not signals and have no
effect. `SIGKILL` cannot be caught, blocked or ignored; `SIGSTOP` stops the process until someone
continues it, which is not modelled, as other stops (`sendNoHandler`). Otherwise as `sendNoHandler`, with
what the sender recorded unknown (the entry's `siginfo` is not used: delivering it to a handler is
not modelled). A real-time signal that is blocked is not modelled: whether the kernel queues
another entry for it depends on its memory (`sigqueue_alloc`). For a PID namespace's init
(`ProcSignal.unkillable`) the sender decides: `SIGKILL` and `SIGSTOP` from an ancestor namespace are
forced, from inside the namespace ignored (`send_signal_locked`). The model does not know which kind of
sender it is, so `SIGKILL` to such a process is not modelled; other signals with the action `SIG_DFL`
are ignored either way (`sigTaskIgnored`). -/
def externalSignal (s : State) (sig : Signal) : StepResult :=
  if sig = 0 ∨ 64 < sig then .running s none
  else if sig = SIGKILL then
    if s.proc.signal.unkillable then
      .stopped (.notModelled (.feature "SIGKILL from outside to a PID namespace's init"))
    else .stopped (.killed sig .external)
  else if sig = SIGSTOP then .stopped (.notModelled (.feature "a signal that stops the process"))
  else if 32 ≤ sig && s.thread.sigmask.mem sig then
    .stopped (.notModelled (.feature "blocked real-time signal from outside"))
  else sendNoHandler s ⟨SigInfo.lost sig, .external⟩ false false

/-- The kernel writes `bs` at `a` in the process's memory with user access rights
(`put_user`, `copy_to_user`); `none` if some byte is not writable. -/
def kernelWrite (feat : Features) (s : State) (a : Addr) (bs : List Byte) : Option State :=
  let addrs := byteAddrs a bs.length
  if addrs.all fun x => x.canonical feat.la57 && (s.proc.mm.mem.check feat s.cpu.pkru .write x).isNone
  then some (s.withMem (writeBytes s.proc.mm.mem a bs))
  else none

/-- Whether the kernel can read the `n` bytes at `a` with user access rights: each is readable. -/
def kernelReadable (feat : Features) (s : State) (a : Addr) (n : Nat) : Bool :=
  (byteAddrs a n).all fun x => x.canonical feat.la57 && (s.proc.mm.mem.check feat s.cpu.pkru .read x).isNone

/-- The kernel reads `n` bytes at `a` with user access rights (`copy_from_user`); `none` if
some byte is not readable. -/
def kernelRead (feat : Features) (s : State) (a : Addr) (n : Nat) : Option (List Byte) :=
  if kernelReadable feat s a n then some (readBytes s.proc.mm.mem a n) else none

/-- `USER_PTR_MAX` (= `TASK_SIZE_MAX`: `2^47 - 4096`, with 5-level paging `2^56 - 4096`;
`arch/x86/include/asm/page_64.h`, `arch/x86/kernel/cpu/common.c`): the end of the user address space,
the first byte past its last ordinary user page. The emulate-mode vsyscall gate is mapped above
this limit but remains inaccessible to kernel uaccess. The kernel's check of a user pointer
accepts addresses up to it (`valid_user_address`: `x <= USER_PTR_MAX`,
`arch/x86/include/asm/uaccess_64.h`). -/
def userPtrMax (feat : Features) : Nat :=
  if feat.la57 then 2 ^ 56 - 4096 else 2 ^ 47 - 4096

/-- `TASK_SIZE` of a 64-bit process: the end of the user address space (`TASK_SIZE_MAX`). -/
def taskSize (feat : Features) : Nat := userPtrMax feat

/-- The start of the page containing `a`. -/
def pageDown (a : Nat) : Nat := a / 4096 * 4096

/-- `a` rounded up to a page boundary. -/
def pageUp (a : Nat) : Nat := (a + 4095) / 4096 * 4096

end ZellicX86
