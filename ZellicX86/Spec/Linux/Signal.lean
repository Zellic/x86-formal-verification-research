import ZellicX86.Spec.Linux.Env
import ZellicX86.Spec.Linux.Stack
import ZellicX86.Spec.Linux.Syscall.Common
import ZellicX86.Spec.Xsave
/-!
# Linux: delivering signals to handlers

What the kernel does with pending signals on its way back to user mode (`get_signal`,
`handle_signal`): it takes them one at a time in its order (`nextSignal`) and discards each one
that is ignored, ends the process for one whose default action terminates, and for one with a
handler writes a signal frame on the stack and starts the handler (`setupFrame`). It goes on until
no unblocked signal is pending, so several handlers may be entered at once, the last one running
first.

The kernel does this at every return to user mode. Every signal pending at an instruction boundary
is blocked: the kernel handled every unblocked one at the last return, and a signal becomes
deliverable only inside the kernel, when it is sent or unblocked (and the model's `execve` handles
the pending signals the new program inherits). So the model handles signals where that happens:
after the system calls that send the process a signal or unblock one (`Syscall/Signal.lean`), and
after an exception (`raiseException`). Where the model does not deliver to handlers (a signal from
outside, `externalSignal`; the signals `write` sends, `sysWrite`; a failed `rseq` update at a return
to user mode, `kernelEntry`), reaching one is not modelled.

The frame is the 64-bit `struct rt_sigframe` (`arch/x86/include/asm/sigframe.h`): the return address
`sa_restorer`, a `ucontext` (flags, the alternate stack, the registers as `struct sigcontext`
(`arch/x86/include/uapi/asm/sigcontext.h`), the signal mask), the `siginfo` for an `SA_SIGINFO`
handler, and above them, 64-byte aligned, the `XSAVE` area (`Spec/Xsave.lean`) with the kernel's
software bytes (`struct _fpx_sw_bytes`) and a trailing magic number.

Not modelled: frames for 32-bit or x32 handlers (`SA_IA32_ABI`, `SA_X32_ABI`; this process's system
calls are 64-bit), a thread with a shadow stack (the kernel pushes a token, `setup_signal_shadow_stack`),
a processor without `XSAVE` (the kernel then writes an `FXSAVE` image), anything but the process's end
after the kernel failed to write part of a frame (the memory holds part of the frame), the `siginfo` of
a signal from outside, the signals of `#DB`, `#MF` and `#CP` reaching a handler (`exceptionInfo`;
`#XM`'s is delivered), an `rseq` critical section at a delivery (`rseqUpdate`), and a default action
that stops the process (it waits for someone to continue it). System calls interrupted by a signal (`-ERESTARTSYS`, `SA_RESTART`) do not arise: the
model's system calls complete, and signals from outside arrive between instructions.

Sources: Linux v6.18 `kernel/signal.c` (`get_signal`, `signal_delivered`, `force_sigsegv`),
`arch/x86/kernel/signal.c` (`get_sigframe`, `handle_signal`), `arch/x86/kernel/signal_64.c`
(`x64_setup_rt_frame`), `arch/x86/kernel/fpu/signal.c` (`copy_fpstate_to_sigframe`),
`arch/x86/kernel/fpu/xstate.h` (`xsave_to_user_sigframe`, `update_pkru_in_sigframe`),
`arch/x86/kernel/fpu/core.c` (`fpu__clear_user_states`), `arch/x86/kernel/traps.c`,
`arch/x86/mm/fault.c`, `include/linux/rseq.h` (`rseq_signal_deliver`).
-/
namespace ZellicX86
open Signal

/-- The first word of the kernel's software bytes in the `XSAVE` area, `FP_XSTATE_MAGIC1`
(`arch/x86/include/uapi/asm/sigcontext.h`). -/
def FP_XSTATE_MAGIC1 : BitVec 32 := 0x46505853

/-- The word after the `XSAVE` area, `FP_XSTATE_MAGIC2`. -/
def FP_XSTATE_MAGIC2 : BitVec 32 := 0x46505845

/-- The size of `struct rt_sigframe` for a 64-bit handler: the return address (8), the
`ucontext` (304), the `siginfo` (128). -/
def rtSigframeSize : Nat := 440

/-- `uc_flags` of a 64-bit frame on a processor with `XSAVE` (`frame_uc_flags`):
`UC_FP_XSTATE | UC_SIGCONTEXT_SS | UC_STRICT_RESTORE_SS`. -/
def frameUcFlags : BitVec 64 := 7

/-- `UC_STRICT_RESTORE_SS` (`arch/x86/include/uapi/asm/ucontext.h`). -/
def UC_STRICT_RESTORE_SS : BitVec 64 := 4

/-- Whether `sp` lies on the alternate stack `a`: above its lowest address and at most its size
above it (`__on_sig_stack`, `include/linux/sched/signal.h`). -/
def AltStack.onRaw (a : AltStack) (sp : Addr) : Bool :=
  decide (a.sp < sp) && decide ((sp - a.sp).toNat ≤ a.size.toNat)

/-- Whether `sp` is on the alternate stack `a` (`on_sig_stack`): never with `SS_AUTODISARM`. -/
def AltStack.on (a : AltStack) (sp : Addr) : Bool :=
  a.flags &&& SS_AUTODISARM == 0 && a.onRaw sp

/-- The `ss_flags` mode of `a` at stack pointer `sp` (`sas_ss_flags`): `SS_DISABLE` without an
alternate stack, `SS_ONSTACK` while `sp` is on it, otherwise 0. -/
def AltStack.mode (a : AltStack) (sp : Addr) : BitVec 32 :=
  if a.size = 0 then SS_DISABLE else if a.on sp then SS_ONSTACK else 0

/-- What the thread's kernel state records about the exception that sent a signal
(`trap_nr`, `error_code`, `cr2` of `struct thread_struct`), which the frame reports in `trapno`,
`err` and `cr2`. `cr2` is the address of the last page fault the kernel reported (`none`: not one
of this exception). -/
structure TrapRec where
  /-- The exception's vector (`trap_nr`). -/
  trapno : BitVec 64
  /-- The exception's error code (`error_code`). -/
  err : BitVec 64
  /-- The address of a page fault (`cr2`); `none`: not one of this exception. -/
  cr2 : Option Addr

/-- The kernel stores runs of bytes at offsets from `base` with user access rights, as
`kernelWrite` does; `none` if some byte cannot be written. -/
def kernelWrites (feat : Features) (s : State) (base : Addr) (ws : List (Nat × List Byte)) :
    Option State :=
  ws.foldl (fun acc (o, bs) => acc.bind fun t => kernelWrite feat t (base.add o) bs) (some s)

/-- The kernel updates the `rseq` area at a delivery as at a return to user mode
(`rseq_signal_deliver`, `rseqUpdate`), with where the thread runs as `Request.resumeIds`. -/
def rseqAtDelivery (prof : Profile) (s : State) : Req (Except Outcome (Option State)) :=
  match s.thread.rseq with
  | none => Pure.pure (.ok (some s))
  | some _ => do
    let ⟨(cpu, node, mmCid), _⟩ ← Req.request (.resumeIds prof.cpus)
    Pure.pure (rseqUpdate prof.feat s cpu node mmCid)

/-- What setting up a signal frame gives: the state at the handler's first instruction; a failure,
with the state before the frame and whether the kernel had begun to write it (`wrote`: the memory then
holds part of a frame, which the model does not track); or a case not modelled. -/
inductive FrameResult
  /-- The frame is written; `s` is the state at the handler's first instruction. -/
  | ok (s : State)
  /-- The frame could not be set up; `s` is the state before it, `wrote` whether part of it was written. -/
  | failed (s : State) (wrote : Bool)
  /-- The run ends with outcome `o`: a case not modelled. -/
  | stop (o : Outcome)

/-- The kernel's 48 software bytes at offset 464 of the frame's `XSAVE` area (`save_sw_bytes`):
`FP_XSTATE_MAGIC1`, the size with the trailing magic number, the components saved, the area's
size, and 28 bytes of zeros. -/
def swBytes (prof : Profile) : List Byte :=
  toBytesLE FP_XSTATE_MAGIC1 4 ++ toBytesLE (BitVec.ofNat 32 (prof.xUserSize + 4)) 4 ++
  toBytesLE prof.userXfeatures 8 ++ toBytesLE (BitVec.ofNat 32 prof.xUserSize) 4 ++
  List.replicate 28 0

/-- The kernel delivers pending signal `q` to the handler at `handler` of action `act`, from state
`s` (`handle_signal`, `setup_rt_frame`, `x64_setup_rt_frame`):
- the `rseq` area is updated (`rseqAtDelivery`). A failed update forces `SIGSEGV` (`force_sigsegv` of
  the signal delivered, `State.forceSigsegv`) and the kernel goes on with the frame from there: the
  frame saves the mask as the force left it, and the forced `SIGSEGV` stays pending, to be taken after
  this delivery unless the delivery's mask blocks it (`rseq_signal_deliver`, `setup_rt_frame`);
- the frame goes below the red zone (128 bytes below `rsp`), or, for an `SA_ONSTACK` handler, at the
  top of the alternate stack if there is one and the thread is not on it; the `XSAVE` area is
  64-byte aligned below it, the frame below that so that `rsp + 8` is 16-byte aligned at the
  handler, as at a function's entry. An action without `SA_RESTORER`, a frame that would leave the
  alternate stack it is on, or an `XSAVE` area that fails `access_ok` fails before anything is written;
- the kernel writes the `XSAVE` area with every key's access allowed (`sig_prepare_pkru`): the header
  cleared, then `XSAVE` of the components the kernel saves (with `XINUSE` as
  `Request.xinuse`, bounded by the saved state's initial configuration, the bytes the manuals
  leave unspecified as `Request.undefined`), possibly
  after clearing the whole area because a first `XSAVE` faulted on a page not yet present
  (`Request.pick`), the software bytes, the trailing magic number, `XSTATE_BV` with x87 and SSE set,
  and the thread's `PKRU` with its bit (`update_pkru_in_sigframe`);
- then the `ucontext`: `uc_flags`, `uc_link` 0, the alternate stack as set, the registers, `cs` and
  `ss`, `gs` and `fs` 0, `err`, `trapno` and `cr2` from `trap` (for a signal not sent for an
  exception in this entry to the kernel, unspecified values: what the thread's last exception left),
  the mask, the area's address, the mask again (`uc_sigmask`); the return address; and for an
  `SA_SIGINFO` handler the `siginfo`, which is `SigInfo.lost`'s if the kernel could not allocate the
  signal's queue entry (`Request.queued`, for a signal 1–31; a real-time signal's entry was allocated
  when it was sent). Bytes it does not write keep their values. Every write must succeed, and the
  frame pass `access_ok` of its constant size (`user_access_begin`, `accessOkFixed`), checked after
  the `XSAVE` area is written; otherwise it fails after writing. The writes grow a stack where they must
  (`growFor`, from the frame's first byte to the area's end: the kernel writes the area first, then the
  frame below it, but a growth for a lower byte maps every page above it up to the stack, and one that
  fits the limit and the guard gap at a lower page does at a higher one, so the frame can be written
  after the same growths, and a failed frame ends the same way);
- the handler starts with `rdi` the signal, `rsi` the `siginfo`, `rdx` the `ucontext`, `rax` 0,
  `rsp` the frame, `rip` the handler, `cs` the 64-bit user code segment, `DF`, `RF` and `TF` clear,
  the x87 and vector state initial (`MXCSR` `1F80H`) and `PKRU` the kernel's default
  (`Request.initPkru`);
- the mask gains the action's mask and, without `SA_NODEFER`, the signal (`signal_delivered`), never
  `SIGKILL` or `SIGSTOP`, and an alternate stack set up with `SS_AUTODISARM` is disabled. -/
def setupFrame (prof : Profile) (s : State) (q : Queued) (act : SigAction) (handler : Addr)
    (trap : Option TrapRec) : Req FrameResult := do
  let feat := prof.feat
  let sig := q.info.signo
  let stop (what : String) : Req FrameResult := Pure.pure (.stop (.notModelled (.feature what)))
  let siginfo := act.flags &&& SA_SIGINFO ≠ 0
  if prof.xcr0.isNone then stop "signal frame without XSAVE" else
  if prof.userXfeatures &&& ~~~xHeld ≠ 0 then
    stop "signal frame with an XSAVE component the model does not hold" else
  if s.thread.shstk.isSome then stop "signal frame with a shadow stack" else
  if s.cpu.seg.ss ≠ 0x2b then stop "signal delivery with a stack segment other than the user one" else
  if siginfo && q.cause matches .external then stop "siginfo of a signal from outside" else
  match ← rseqAtDelivery prof s with
  | .error o => Pure.pure (.stop o)
  | .ok t =>
  let s := match t with
    | some t => t
    | none => s.forceSigsegv sig
  if act.flags &&& SA_RESTORER = 0 then Pure.pure (.failed s false) else
  let ss := s.thread.altStack
  let sp := s.cpu.gpr.rsp
  let sp₁ := sp - 128
  let entering := act.flags &&& SA_ONSTACK ≠ 0 && ss.mode sp₁ == 0
  let top := if entering then ss.sp + ss.size else sp₁
  let size := prof.xUserSize
  let fp := (top - BitVec.ofNat 64 (size + 4)) &&& ~~~63
  let frame := ((fp - BitVec.ofNat 64 rtSigframeSize) &&& ~~~15) - 8
  if (ss.on sp || entering) && !ss.onRaw frame then Pure.pure (.failed s false) else
  if !accessOk feat fp (size + 4) then Pure.pure (.failed s false) else
  if !accessOkFixed feat frame rtSigframeSize then Pure.pure (.failed s true) else
  let cleared : Fin 2 ← Req.request (.pick 1)
  let inuse ← Req.request (.xinuse (xsaveBv s.cpu 0 prof.userXfeatures 0))
  let rsv : BitVec (8 * size) ← Req.request (.undefined (8 * size))
  let tr : BitVec 192 ← Req.request (.undefined 192)
  let info ← if siginfo && sig < 32 then do
      let kept : Bool ← Req.request (.queued sig)
      Pure.pure (if kept then q.info else SigInfo.lost sig)
    else Pure.pure q.info
  let rfbm := prof.userXfeatures
  let bv := xsaveBv s.cpu 0 rfbm inuse.val ||| 3 ||| (if feat.pku then 0x200 else 0)
  let area : List (Nat × List Byte) :=
    [(512, List.replicate 64 0)] ++ (if cleared.val = 1 then [(0, List.replicate size 0)] else []) ++
    xsaveRuns prof s.cpu.x87 s.cpu.vec 0 rfbm rsv true ++
    [(464, swBytes prof), (size, toBytesLE FP_XSTATE_MAGIC2 4), (512, toBytesLE bv 8)] ++
    (if feat.pku then [(prof.xOffset 9, toBytesLE s.cpu.pkru 4)] else [])
  let g := s.cpu.gpr
  let w8 (v : BitVec 64) : List Byte := toBytesLE v 8
  let trapno := match trap with | some t => t.trapno | none => tr.setWidth 64
  let err := match trap with | some t => t.err | none => (tr >>> 64).setWidth 64
  let cr2 := match trap.bind (·.cr2) with | some a => a | none => (tr >>> 128).setWidth 64
  let mask := s.thread.sigmask
  let uc : List (Nat × List Byte) :=
    [(8, w8 frameUcFlags), (16, w8 0), (24, w8 ss.sp), (32, toBytesLE ss.flags 4), (40, w8 ss.size),
     (0, w8 act.restorer),
     (48, w8 g.r8), (56, w8 g.r9), (64, w8 g.r10), (72, w8 g.r11), (80, w8 g.r12), (88, w8 g.r13),
     (96, w8 g.r14), (104, w8 g.r15), (112, w8 g.rdi), (120, w8 g.rsi), (128, w8 g.rbp),
     (136, w8 g.rbx), (144, w8 g.rdx), (152, w8 g.rax), (160, w8 g.rcx), (168, w8 g.rsp),
     (176, w8 s.cpu.rip), (184, w8 s.cpu.rflags.toBits), (192, toBytesLE s.cpu.seg.cs 2),
     (194, [0, 0]), (196, [0, 0]), (198, toBytesLE s.cpu.seg.ss 2), (200, w8 err), (208, w8 trapno),
     (216, w8 mask), (224, w8 cr2), (232, w8 fp), (304, w8 mask)] ++
    (if siginfo then [(312, info.bytes)] else [])
  let s₀ ← growFor prof (s.modCpu fun c => { c with pkru := 0 }) .write frame (fp.toNat + size + 4 - frame.toNat)
  match (kernelWrites feat s₀ fp area).bind fun t => kernelWrites feat t frame uc with
  | none => Pure.pure (.failed s true)
  | some s₁ => do
    let pk : { v : BitVec 32 // v &&& 3 = 0 } ← Req.request .initPkru
    let c := s₁.cpu
    let mask' := (mask ||| act.mask ||| (if act.flags &&& SA_NODEFER ≠ 0 then 0 else (0 : SigSet).insert sig)).unblockable
    Pure.pure (.ok { s₁ with
      cpu := { c with
        gpr := { c.gpr with rdi := BitVec.ofNat 64 sig, rsi := frame.add 312, rdx := frame.add 8,
                            rax := 0, rsp := frame }
        rip := handler
        rflags := { c.rflags with df := false, rf := false, tf := false }
        seg := { c.seg with cs := 0x33 }
        x87 := X87.init
        vec := ⟨fun _ => 0, fun _ => 0, 0x1F80⟩
        pkru := pk.val }
      thread := { s₁.thread with
        sigmask := mask'
        altStack := if ss.flags &&& SS_AUTODISARM ≠ 0 then AltStack.disabled else ss } })

/-- The kernel handles the pending signals on its way back to user mode, from state `s`, after a
system call whose event is `ev` (`none` after an exception), with `trap` recorded for an exception
in this entry to the kernel (`get_signal`, `handle_signal`; `arch_do_signal_or_restart` once per
signal until none is deliverable): it takes the next one (`nextSignal`); an ignored one is
discarded, as one whose default action does nothing or continues, and, in a PID namespace's init
(`ProcSignal.unkillable`), one with the default action but `SIGKILL` and `SIGSTOP`; one whose default
action terminates ends the process (with a core dump for some, `DefaultAction.core`, which the process
does not see); one with a handler is delivered (`setupFrame`), and an `SA_RESETHAND` action reverts
to `SIG_DFL` as it is taken. A frame that fails forces `SIGSEGV` (`signal_setup_done`,
`State.forceSigsegv`), which is then taken as any pending signal. Once the kernel has written part of
a frame (`wrote`), the model goes on only to the process's end: a later delivery to a handler, or a
return with the partial frame in memory, is not modelled. `fuel` bounds the signals taken: the
pending entries, and the `SIGSEGV` entries forced on the way, at most one for each other delivery and
one more (a forced `SIGSEGV` is never queued twice, and once forced for a `SIGSEGV` delivery its
action stays `SIG_DFL`). -/
def handleSignals (prof : Profile) (trap : Option TrapRec) (ev : Option Event) :
    Nat → Bool → State → Req StepResult
  | 0, _, _ => Pure.pure (.stopped (.notModelled (.feature "more signals than pending entries")))
  | fuel + 1, wrote, s =>
    let partialFrame : Req StepResult :=
      Pure.pure (.stopped (.notModelled (.feature "a signal frame the kernel could not write")))
    match nextSignal s with
    -- `wrote` here cannot happen: the failed frame forced a `SIGSEGV`, which stays pending, unblocked,
    -- until taken (`State.forceSigsegv`). Kept so that no path returns with a partial frame.
    | none => if wrote then partialFrame else Pure.pure (.running s ev)
    | some (q, s₁) =>
      let sig := q.info.signo
      let act := s₁.proc.sighand sig
      match act.disp with
      | .ignore => handleSignals prof trap ev fuel wrote s₁
      | .default =>
        if s₁.proc.signal.unkillable && !kernelOnly sig then handleSignals prof trap ev fuel wrote s₁ else
        match defaultAction sig with
        | .term | .core => Pure.pure (.stopped (.killed sig q.cause))
        | .stop => Pure.pure (.stopped (.notModelled (.feature "a signal that stops the process")))
        | .ign | .cont => handleSignals prof trap ev fuel wrote s₁
      | .handler h =>
        if wrote then partialFrame else do
        let s₂ := if act.flags &&& SA_RESETHAND ≠ 0 then s₁.setAction sig { act with disp := .default }
          else s₁
        match ← setupFrame prof s₂ q act h trap with
        | .ok s₃ => handleSignals prof trap ev fuel false s₃
        | .stop o => Pure.pure (.stopped o)
        | .failed s₃ w => handleSignals prof trap ev fuel w (s₃.forceSigsegv sig)

/-- `handleSignals` with enough fuel: twice the pending entries and two more. -/
def deliverSignals (prof : Profile) (trap : Option TrapRec) (ev : Option Event) (s : State) :
    Req StepResult :=
  handleSignals prof trap ev (2 * (s.thread.pending.length + s.proc.signal.pending.length) + 2) false s

/-- The `si_code` of the `SIGFPE` for a `#XM` that leaves `MXCSR` as `m` (`fpu__exception_code`,
`arch/x86/kernel/fpu/core.c`): of the flags whose exceptions are unmasked (`~(m >> 7) & m`), invalid
operation gives `FPE_FLTINV`, else divide by zero `FPE_FLTDIV`, else overflow `FPE_FLTOVF`, else
underflow or denormal operand `FPE_FLTUND`, else precision `FPE_FLTRES`. A `#XM` always leaves such a
flag set (`simdDone`); with none the kernel would return to the instruction without a signal. -/
def xmCode (m : BitVec 32) : BitVec 32 :=
  let err := m.toNat % 64 &&& (63 - m.toNat / 2 ^ 7 % 64)
  if err &&& 1 ≠ 0 then FPE_FLTINV else if err &&& 4 ≠ 0 then FPE_FLTDIV
  else if err &&& 8 ≠ 0 then FPE_FLTOVF else if err &&& 18 ≠ 0 then FPE_FLTUND
  else if err &&& 32 ≠ 0 then FPE_FLTRES else 0

/-- The `siginfo` and the frame's trap record of the signal for exception `e` raised by the
instruction at `rip` in state `s` (`arch/x86/kernel/traps.c`, `arch/x86/mm/fault.c`), for the
exceptions whose signal the model delivers to a handler; `pf` gives the page-fault error code's
`P` bit (bit 0) and, without the execute-disable bit in use, its `I/D` bit (bit 1), which depend on
the kernel's page tables and `CR4.SMEP`:
- `#DE`: `FPE_INTDIV` at the instruction; `#UD`: `ILL_ILLOPN` at the instruction;
- `#BP`, `#SS`, `#GP`: `SI_KERNEL`, with the error code;
- `#PF`: on the vsyscall page `SEGV_MAPERR`, even in emulate mode where the page is mapped, because
  the kernel's lookup of the process's mappings does not find it (`arch/x86/entry/vsyscall/vsyscall_64.c`,
  `arch/x86/mm/fault.c` `do_user_addr_fault`).
  Else `SIGBUS` `BUS_ADRERR` where `sigbusAt` says so (a page beyond the end of its file whose
  mapping allows the access), else `SIGSEGV`: `SEGV_MAPERR` for an address without a mapping,
  `SEGV_PKUERR` with the page's key when protection keys forbid the access, `SEGV_ACCERR` otherwise
  (`bad_area_access_error`); the address in `si_addr` and `cr2`, the error code with the
  user bit, the write bit for a write, the instruction-fetch bit, the `P` bit, which the kernel
  sets for an address beyond the user range (`sanitize_error_code`), and the protection-key bit with
  it (`AccessFault.pkey`): a page not yet present faults as not present first, and the kernel then
  finds the key's violation from the mapping (`bad_area_access_from_pkeys`);
- `#AC`: `BUS_ADRALN`;
- `#XM`: trap 19, `SIGFPE` at the instruction with the code `xmCode` of the `MXCSR` it leaves
  (`exc_simd_coprocessor_error`, `math_error`). -/
def exceptionInfo (feat : Features) (s : State) (pf : BitVec 2) : Exception → Option (SigInfo × TrapRec)
  | .de => some (SigInfo.fault SIGFPE FPE_INTDIV s.cpu.rip, ⟨0, 0, none⟩)
  | .bp => some (SigInfo.kernel SIGTRAP, ⟨3, 0, none⟩)
  | .ud => some (SigInfo.fault SIGILL ILL_ILLOPN s.cpu.rip, ⟨6, 0, none⟩)
  | .ss err => some (SigInfo.kernel SIGBUS, ⟨12, err.setWidth 64, none⟩)
  | .gp err => some (SigInfo.kernel SIGSEGV, ⟨13, err.setWidth 64, none⟩)
  | .pf a acc pkey =>
    let mem := s.proc.mm.mem
    let p := decide (a.toNat ≥ userPtrMax feat) || pf.getLsbD 0
    let i := acc = .fetch && (feat.nx || pf.getLsbD 1)
    let err : BitVec 64 := (if p then 1 else 0) ||| (if acc = .write then 2 else 0) ||| 4 |||
      (if i then 16 else 0) ||| (if pkey && p then 32 else 0)
    let info := if pageOf a = vsyscallPage then SigInfo.fault SIGSEGV SEGV_MAPERR a else
      if sigbusAt feat s.cpu.pkru mem acc a then SigInfo.fault SIGBUS BUS_ADRERR a else
      match mem.map (pageOf a) with
      | none => SigInfo.fault SIGSEGV SEGV_MAPERR a
      | some m =>
        if feat.pku && (pkey || pkeyDenies s.cpu.pkru m.pkey acc) then
          ⟨SIGSEGV, 0, SEGV_PKUERR, a.setWidth 256 ||| (m.pkey.setWidth 256 <<< 128)⟩
        else SigInfo.fault SIGSEGV SEGV_ACCERR a
    some (info, ⟨14, err, some a⟩)
  | .ac => some (SigInfo.fault SIGBUS BUS_ADRALN 0, ⟨17, 0, none⟩)
  | .xm m => some (SigInfo.fault SIGFPE (xmCode m) s.cpu.rip, ⟨19, 0, none⟩)
  | .db | .nm | .mf | .cp _ => none

/-- The signal of exception `e`, raised by the current instruction (the state `s` is the one the
exception leaves: before the instruction for a fault, after it for `#BP`, a trap): the kernel forces
the exception's signal (`exceptionSignal`) on the thread (`State.force`); without a handler, or with
the signal blocked or ignored, it ends the process, and otherwise the kernel delivers it, first of
the pending signals (`deliverSignals`). `#NM` in user mode is not modelled. -/
def signalException (prof : Profile) (s : State) (e : Exception) : Req StepResult :=
  match exceptionSignal prof.feat s.cpu.pkru s.proc.mm.mem e with
  | none => Pure.pure (.stopped (.notModelled (.feature "#NM in user mode")))
  | some sig =>
    let a := s.proc.sighand sig
    match a.disp with
    | .handler _ =>
      if s.thread.sigmask.mem sig then Pure.pure (.stopped (.killed sig (.exception e))) else do
      let pf : BitVec 2 ← Req.request (.undefined 2)
      match exceptionInfo prof.feat s pf e with
      | none => Pure.pure (.stopped (.notModelled (.signalHandler sig)))
      | some (info, trap) =>
        -- the processor saves `RF` set for a fault (SDM Vol. 3B, 20.3.1.1)
        let sF := if e = .bp then s else s.modCpu fun c => { c with rflags := { c.rflags with rf := true } }
        deliverSignals prof (some trap) none (sF.force ⟨info, .exception e⟩)
    | _ => Pure.pure (.stopped (.killed sig (.exception e)))

/-- What exception `e`, raised by the current instruction, does to the process (the state `s` is the
one the exception leaves: before the instruction for a fault, after it for `#BP`, a trap). For `#PF` at
an address below `TASK_SIZE` whose page no mapping covers, the kernel's fault handler first tries to
grow a stack down to it (`growStack`; `arch/x86/mm/fault.c` `do_user_addr_fault`). If it does, it
checks the access again on the grown mapping (`access_error`): allowed, it returns to the
instruction, which runs again at the next step (with `RF` set, as the processor saved it for the
fault, SDM Vol. 3B, 20.3.1.1); not allowed (a fetch from a stack without `PROT_EXEC`, a write to one
made read-only, a protection key), it signals the fault on the grown state, which the growth stays
in. Otherwise, and for every other exception, its signal (`signalException`). -/
def raiseException (prof : Profile) (s : State) (e : Exception) : Req StepResult :=
  match e with
  | .pf a acc _ =>
    if (s.proc.mm.mem.map (pageOf a)).isNone && decide (a.toNat < taskSize prof.feat) then do
      match ← growStack prof s a with
      | some s' =>
        if (s'.proc.mm.mem.check prof.feat s'.cpu.pkru acc a).isNone then
          Pure.pure (.running (s'.modCpu fun c => { c with rflags := { c.rflags with rf := true } }) none)
        else signalException prof s' e
      | none => signalException prof s e
    else signalException prof s e
  | _ => signalException prof s e

end ZellicX86
