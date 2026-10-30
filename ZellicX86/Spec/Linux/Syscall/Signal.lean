import ZellicX86.Spec.Linux.Signal
import ZellicX86.Spec.Linux.Syscall.Task
/-!
# Linux system calls: signals

The calls that set the thread's and the process's signal state, send the process a signal, and
return from a handler: `rt_sigaction`, `rt_sigprocmask`, `rt_sigpending`, `sigaltstack`, `kill`,
`tkill` and `tgkill` to the process itself, `getpid` and `gettid`, and `rt_sigreturn`. A call that
sends a signal or unblocks one handles the pending signals before it returns (`deliverSignals`).

Not modelled: a signal to another process or to a process group, `rt_sigqueueinfo`,
`rt_tgsigqueueinfo`, `rt_sigsuspend`, `rt_sigtimedwait`, `signalfd`; a real-time signal sent with
`kill` whose queue entry the kernel cannot allocate (the kernel then keeps the signal without its
information, and later sends merge with it).

Sources: Linux v6.18 `kernel/signal.c` (`rt_sigaction`, `do_sigaction`, `rt_sigprocmask`,
`sigprocmask`, `rt_sigpending`, `sigaltstack`, `do_sigaltstack`, `restore_altstack`, `kill`,
`kill_something_info`, `tkill`, `tgkill`, `do_send_specific`, `prepare_kill_siginfo`),
`kernel/sys.c` (`getpid`, `gettid`), `arch/x86/kernel/signal_64.c` (`rt_sigreturn`,
`restore_sigcontext`), `arch/x86/kernel/signal.c` (`sigaltstack_size_valid`),
`arch/x86/kernel/fpu/signal.c` (`fpu__restore_sig`, `__fpu_restore_sig`,
`check_xstate_in_sigframe`, `restore_fpregs_from_user`), `sigaction(2)`, `sigprocmask(2)`,
`sigaltstack(2)`, `kill(2)`, `tgkill(2)`, `sigreturn(2)`.
-/
namespace ZellicX86
open Signal

/-- Finish a system call that may have made a signal deliverable: its result `ret` in `rax` of the
state `s` after it, its event (with the arguments of `s₀`, the state at the call, and the bytes
`toProc` the kernel wrote), then the pending signals (`deliverSignals`). -/
def sysReturnSignals (prof : Profile) (s₀ s : State) (ret : BitVec 64) (toProc : List Byte) :
    Req StepResult :=
  deliverSignals prof none (some ⟨s₀.cpu.gpr.rax, syscallArgs s₀, ret, [], toProc⟩) (s.setRax ret)

/-- `sa_handler` as a word: `SIG_DFL` 0, `SIG_IGN` 1, or the handler's address. -/
def SigAction.handlerWord (a : SigAction) : Addr :=
  match a.disp with
  | .default => 0
  | .ignore => 1
  | .handler h => h

/-- The 32 bytes of the kernel's `struct sigaction` (`arch/x86/include/uapi/asm/signal.h`):
`sa_handler`, `sa_flags`, `sa_restorer`, `sa_mask`, 8 bytes each. -/
def SigAction.bytes (a : SigAction) : List Byte :=
  toBytesLE a.handlerWord 8 ++ toBytesLE a.flags 8 ++ toBytesLE a.restorer 8 ++ toBytesLE a.mask 8

/-- The action in the 32 bytes `bs` of a `struct sigaction`. -/
def SigAction.ofBytes (bs : List Byte) : SigAction :=
  let w (i : Nat) : BitVec 64 := ofBytesLE 64 ((bs.drop (8 * i)).take 8)
  ⟨if w 0 = 0 then .default else if w 0 = 1 then .ignore else .handler (w 0), w 1, w 3, w 2⟩

/-- `rt_sigaction(sig, act, oact, sigsetsize)` (`kernel/signal.c`); `sig` is an `int`. `sigsetsize`
must be 8 (`EINVAL`); a new action is read first (32 bytes, `EFAULT`). A `sig` outside 1–64, or a new
action for `SIGKILL` or `SIGSTOP`, is `EINVAL`. The new action is stored with the flags the kernel
knows (`uapiSaFlags`) and its mask without `SIGKILL` and `SIGSTOP`; an action that ignores the signal
discards its pending entries, the thread's and the process's (`do_sigaction`). Then the old action,
with the flags the kernel knows, is copied to `oact` unless it is 0 (`EFAULT`, with the new action
set). -/
def sysRtSigaction (prof : Profile) (s : State) : Req StepResult := do
  let sig := argInt s.cpu.gpr.rdi
  let act := s.cpu.gpr.rsi
  let oact := s.cpu.gpr.rdx
  if s.cpu.gpr.r10.toNat ≠ 8 then Pure.pure (sysReturn s (errRet EINVAL) [] []) else
  let (s, new?) ← if act = 0 then Pure.pure (s, some none) else do
    let (s, bs?) ← copyIn prof s act 32
    Pure.pure (s, bs?.map fun bs => some (SigAction.ofBytes bs))
  let fail (e : Nat) : Req StepResult := Pure.pure (sysReturn s (errRet e) [] [])
  match new? with
  | none => fail EFAULT
  | some new =>
  if sig < 1 ∨ 64 < sig ∨ (new.isSome ∧ (sig = SIGKILL ∨ sig = SIGSTOP)) then fail EINVAL else
  let n := sig.toNat
  let old := s.proc.sighand n
  let s₁ : State := match new with
    | none => s
    | some a =>
      let a' := { a with flags := a.flags &&& uapiSaFlags, mask := a.mask.unblockable }
      let t := s.setAction n a'
      if a'.ignores n then
        { t with proc.signal.pending := t.proc.signal.pending.drop [n],
                 thread := { t.thread with pending := t.thread.pending.drop [n] } }
      else t
  let ob := { old with flags := old.flags &&& uapiSaFlags }.bytes
  if oact = 0 then Pure.pure (sysReturn s₁ 0 [] []) else do
  let (s₂, k, all) ← copyOut prof s₁ oact ob
  Pure.pure (sysReturn s₂ (if all then 0 else errRet EFAULT) [] (ob.take k))

/-- `rt_sigprocmask`'s `how`: add the set to the mask (`include/uapi/asm-generic/signal-defs.h`). -/
def SIG_BLOCK : Int := 0
/-- `rt_sigprocmask`'s `how`: remove the set from the mask. -/
def SIG_UNBLOCK : Int := 1
/-- `rt_sigprocmask`'s `how`: make the set the mask. -/
def SIG_SETMASK : Int := 2

/-- `rt_sigprocmask(how, nset, oset, sigsetsize)` (`kernel/signal.c`); `how` is an `int`.
`sigsetsize` must be 8 (`EINVAL`). A new set is read (8 bytes, `EFAULT`), without `SIGKILL` and
`SIGSTOP`, and added to the mask (`SIG_BLOCK`), removed from it (`SIG_UNBLOCK`) or made the mask
(`SIG_SETMASK`); any other `how` is `EINVAL`. Then the old mask is copied to `oset` unless it is 0
(`EFAULT`, with the new mask set), and the signals the call unblocked are handled. -/
def sysRtSigprocmask (prof : Profile) (s : State) : Req StepResult := do
  let how := argInt s.cpu.gpr.rdi
  let nset := s.cpu.gpr.rsi
  let oset := s.cpu.gpr.rdx
  if s.cpu.gpr.r10.toNat ≠ 8 then Pure.pure (sysReturn s (errRet EINVAL) [] []) else
  let old := s.thread.sigmask
  let (s, bs?) ← if nset = 0 then Pure.pure (s, none) else copyIn prof s nset 8
  let fail (e : Nat) : Req StepResult := Pure.pure (sysReturn s (errRet e) [] [])
  let s₁ : Except Nat State := if nset = 0 then .ok s else
    match bs? with
    | none => .error EFAULT
    | some bs =>
      let m := SigSet.unblockable (ofBytesLE 64 bs)
      let set (v : SigSet) : Except Nat State := .ok (s.modThread fun t => { t with sigmask := v.unblockable })
      if how = SIG_BLOCK then set (old ||| m)
      else if how = SIG_UNBLOCK then set (old &&& ~~~m)
      else if how = SIG_SETMASK then set m
      else .error EINVAL
  match s₁ with
  | .error e => fail e
  | .ok s₁ =>
    if oset = 0 then sysReturnSignals prof s s₁ 0 [] else do
    let (s₂, k, all) ← copyOut prof s₁ oset (toBytesLE old 8)
    sysReturnSignals prof s s₂ (if all then 0 else errRet EFAULT) ((toBytesLE old 8).take k)

/-- `rt_sigpending(uset, sigsetsize)` (`kernel/signal.c`): `sigsetsize` above 8 is `EINVAL`; the
signals pending for the thread or the process that are blocked, the first `sigsetsize` bytes of the
set, are copied to `uset` (`EFAULT`). -/
def sysRtSigpending (prof : Profile) (s : State) : Req StepResult := do
  let n := s.cpu.gpr.rsi.toNat
  if 8 < n then Pure.pure (sysReturn s (errRet EINVAL) [] []) else do
  let set := (s.thread.pending.set ||| s.proc.signal.pending.set) &&& s.thread.sigmask
  let bs := toBytesLE set n
  let (s', k, all) ← copyOut prof s s.cpu.gpr.rdi bs
  Pure.pure (sysReturn s' (if all then 0 else errRet EFAULT) [] (bs.take k))

/-- The 24 bytes of a `stack_t` (`include/uapi/asm-generic/signal.h`): `ss_sp`, `ss_flags` (an
`int`, then 4 bytes of padding), `ss_size`. -/
def AltStack.bytes (sp : Addr) (flags : BitVec 32) (size : BitVec 64) : List Byte :=
  toBytesLE sp 8 ++ toBytesLE flags 4 ++ [0, 0, 0, 0] ++ toBytesLE size 8

/-- The largest alternate signal stack a kernel that checks sizes strictly refuses for a process without
permission for AMX state (`sigaltstack_size_valid`): the largest signal frame, `AT_MINSIGSTKSZ`
(`max_frame_size`, `get_sigframe_size`), with the process's extended state (`xUserSize`,
`perm.__user_state_size`) in place of the largest one the kernel allows (`fpu__get_fpstate_size`: every
user component's, `xMaxSize`, the 4 bytes of `FP_XSTATE_MAGIC2` with `XSAVE`, and room for a 32-bit
process's x87 state, 112 bytes, with `CONFIG_IA32_EMULATION`). -/
def Profile.sasStrictMin (prof : Profile) : Nat :=
  prof.aux.minSigStkSz + prof.xUserSize -
    (prof.xMaxSize + (if prof.xcr0.isSome then 4 else 0) + (if prof.linux.ia32Emulation then 112 else 0))

/-- Set the thread's alternate stack to the one in the 24 bytes `bs` of a `stack_t`, at stack
pointer `sp` (`do_sigaltstack`): refused while `sp` is on the alternate stack (`EPERM`), with a mode
(`ss_flags` without `SS_AUTODISARM`) other than `SS_DISABLE`, `SS_ONSTACK` or 0 (`EINVAL`), and with a
size below `MINSIGSTKSZ` (`ENOMEM`). A kernel that checks sizes strictly (`LinuxBoot.strictSasSize`,
`sigaltstack_size_valid`) also refuses (`ENOMEM`) a size up to what a frame needs (`sasStrictMin`); one that
does not checks no more for a process without permission for AMX state (`arch_prctl(ARCH_REQ_XCOMP_PERM)`,
not modelled). `SS_DISABLE` stores no stack, with the flags given; the same stack as set changes nothing. -/
def setAltStack (prof : Profile) (s : State) (sp : Addr) (bs : List Byte) : Req (Except Nat State) :=
  let ss := s.thread.altStack
  let nsp : Addr := ofBytesLE 64 (bs.take 8)
  let nflags : BitVec 32 := ofBytesLE 32 ((bs.drop 8).take 4)
  let nsize : BitVec 64 := ofBytesLE 64 ((bs.drop 16).take 8)
  let mode := nflags &&& ~~~SS_AUTODISARM
  let store (a : AltStack) : Except Nat State := .ok (s.modThread fun t => { t with altStack := a })
  if ss.on sp then Pure.pure (.error EPERM)
  else if mode ≠ SS_DISABLE ∧ mode ≠ SS_ONSTACK ∧ mode ≠ 0 then Pure.pure (.error EINVAL)
  else if nsp = ss.sp ∧ nsize = ss.size ∧ nflags = ss.flags then Pure.pure (.ok s)
  else if mode = SS_DISABLE then Pure.pure (store ⟨0, 0, nflags⟩)
  else if nsize.toNat < MINSIGSTKSZ then Pure.pure (.error ENOMEM)
  else if prof.linux.strictSasSize ∧ nsize.toNat ≤ prof.sasStrictMin then Pure.pure (.error ENOMEM)
  else Pure.pure (store ⟨nsp, nsize, nflags⟩)

/-- `sigaltstack(uss, uoss)` (`kernel/signal.c`): a new stack is read (24 bytes, `EFAULT`) and set
(`setAltStack`, at the thread's `rsp`); if that succeeded, the old one is copied to `uoss` unless it
is 0 (`EFAULT`): its address and size, and `ss_flags` its mode at `rsp` (`AltStack.mode`) with
`SS_AUTODISARM` if it was set up with it. -/
def sysSigaltstack (prof : Profile) (s : State) : Req StepResult := do
  let uss := s.cpu.gpr.rdi
  let uoss := s.cpu.gpr.rsi
  let sp := s.cpu.gpr.rsp
  let ss := s.thread.altStack
  let ob := AltStack.bytes ss.sp (ss.mode sp ||| (ss.flags &&& SS_AUTODISARM)) ss.size
  let (s, bs?) ← if uss = 0 then Pure.pure (s, none) else copyIn prof s uss 24
  let fail (e : Nat) : Req StepResult := Pure.pure (sysReturn s (errRet e) [] [])
  let r ← if uss = 0 then Pure.pure (.ok s) else
    match bs? with
    | none => Pure.pure (.error EFAULT)
    | some bs => setAltStack prof s sp bs
  match r with
  | .error e => fail e
  | .ok s₁ =>
    if uoss = 0 then Pure.pure (sysReturn s₁ 0 [] []) else do
    let (s₂, k, all) ← copyOut prof s₁ uoss ob
    Pure.pure (sysReturn s₂ (if all then 0 else errRet EFAULT) [] (ob.take k))

/-- The process sends itself signal `sig` (1–64), to the thread (`toThread`) or to the process, with
code `code` and itself as the sender (`prepare_kill_siginfo`), which does not force it (`send_signal_locked`):
`SIGKILL` ends the process, except in a PID namespace's init, which ignores it (`sigTaskIgnored`), and the
call returns 0; otherwise the signal is sent (`sendSignal`) and the call returns 0 with the signal
handled. A real-time signal that is queued needs a queue entry (`Request.queued`); without one, a
`tkill`/`tgkill` (code `SI_TKILL`) fails with `EAGAIN`, and a `kill` (code `SI_USER`) is not
modelled. -/
def sendSelf (prof : Profile) (s : State) (sig : Signal) (code : BitVec 32) (toThread : Bool) :
    Req StepResult := do
  if sig = SIGKILL then
    if s.proc.signal.unkillable then sysReturnSignals prof s s 0 [] else Pure.pure (.stopped (.killed sig .self))
  else
  let q : Queued := ⟨SigInfo.ofSender sig code s.thread.tid s.thread.uid, .self⟩
  let queued := s.thread.sigmask.mem sig || !sigTaskIgnored s sig false
  let kept : Bool ← if 32 ≤ sig ∧ queued then Req.request (.queued sig) else Pure.pure true
  if kept then sysReturnSignals prof s (sendSignal s q toThread false) 0 []
  else if code = SI_USER then
    Pure.pure (.stopped (.notModelled (.feature "a real-time signal without a queue entry")))
  else Pure.pure (sysReturn s (errRet EAGAIN) [] [])

/-- `kill(pid, sig)` (`kernel/signal.c`); `pid` and `sig` are `int`s. To the process itself (`pid`
its id): a `sig` outside 0–64 is `EINVAL`, 0 only checks (0), any other is sent to the process
(`sendSelf`, `SI_USER`). `pid` `INT_MIN` is `ESRCH`; another process, the process group (0, or
`-pgid`) and every process (-1) are not modelled. -/
def sysKill (prof : Profile) (s : State) : Req StepResult :=
  let pid := argInt s.cpu.gpr.rdi
  let sig := argInt s.cpu.gpr.rsi
  if pid = s.thread.tid then
    if sig < 0 ∨ 64 < sig then Pure.pure (sysReturn s (errRet EINVAL) [] [])
    else if sig = 0 then Pure.pure (sysReturn s 0 [] [])
    else sendSelf prof s sig.toNat SI_USER false
  else if pid = -2147483648 then Pure.pure (sysReturn s (errRet ESRCH) [] [])
  else Pure.pure (.stopped (.notModelled (.feature "kill of another process or a process group")))

/-- `tgkill(tgid, tid, sig)` (`kernel/signal.c`; `tkill(tid, sig)` is `tgid` 0 without the check);
all `int`s: a `tid` (or a `tgid` given) not positive is `EINVAL`. For the thread itself, a `tgid`
that is not its process's is `ESRCH`; then a `sig` outside 0–64 is `EINVAL`, 0 only checks, and any
other is sent to the thread (`sendSelf`, `SI_TKILL`). Another thread is not modelled. -/
def sysTgkill (prof : Profile) (s : State) (tgid : Option Int) (tid sig : Int) : Req StepResult :=
  if tid ≤ 0 ∨ tgid.any (· ≤ 0) then Pure.pure (sysReturn s (errRet EINVAL) [] [])
  else if tid = s.thread.tid then
    if tgid.any (· ≠ (s.thread.tid : Int)) then Pure.pure (sysReturn s (errRet ESRCH) [] [])
    else if sig < 0 ∨ 64 < sig then Pure.pure (sysReturn s (errRet EINVAL) [] [])
    else if sig = 0 then Pure.pure (sysReturn s 0 [] [])
    else sendSelf prof s sig.toNat SI_TKILL true
  else Pure.pure (.stopped (.notModelled (.feature "tgkill of another thread")))

/-- `getpid()` and `gettid()` (`kernel/sys.c`): the process's only thread's id, which is the
process id. -/
def sysGetpid (s : State) : Req StepResult :=
  Pure.pure (sysReturn s (BitVec.ofNat 64 s.thread.tid) [] [])

/-! ## `rt_sigreturn` -/

/-- The `RFLAGS` bits `rt_sigreturn` takes from the frame (`FIX_EFLAGS`,
`arch/x86/include/asm/sighandling.h`): `AC`, `OF`, `DF`, `TF`, `SF`, `ZF`, `AF`, `PF`, `CF`, `RF`. -/
def Rflags.setFix (f : Rflags) (v : BitVec 64) : Rflags :=
  { f with cf := v.getLsbD 0, pf := v.getLsbD 2, af := v.getLsbD 4, zf := v.getLsbD 6,
           sf := v.getLsbD 7, tf := v.getLsbD 8, df := v.getLsbD 10, of := v.getLsbD 11,
           rf := v.getLsbD 16, ac := v.getLsbD 18 }

/-- The processor state components the kernel puts in their initial configuration, and the `PKRU`
it gives, when it resets the thread's user state (`fpu__clear_user_states`): x87, SSE, AVX and
AVX-512 state, `MXCSR` `1F80H`, `PKRU` the kernel's default. -/
def Cpu.fpuClear (c : Cpu) (pkru : BitVec 32) : Cpu :=
  { c with x87 := X87.init, vec := ⟨fun _ => 0, fun _ => 0, 0x1F80⟩, pkru }

/-- `rt_sigreturn`'s restore of the processor state from the `XSAVE` area at `buf` (`fpu__restore_sig`,
`__fpu_restore_sig`, `restore_fpregs_from_user`), in state `s`:
- `buf` 0 resets the state (`Cpu.fpuClear`);
- the area (with the trailing magic number) must pass `access_ok`; its software bytes are read
  (offset 464) and, if they start with `FP_XSTATE_MAGIC1`, the magic number after the area; if either
  is missing the area is taken as an `FXSAVE` image (x87 and SSE only, `FXRSTOR`), else `XRSTOR` loads
  the components the software bytes name of those the kernel saves. The bytes the instruction
  loads must be readable. The kernel runs it with page faults disabled, so it also faults on a page
  that is readable but not present (the model does not track which are), and then retries only if
  every byte of the area (`user_size` bytes) can be faulted in (`fault_in_readable`): with a byte of the
  area that cannot be read, the restore may fail (`Request.pick`). An instruction that faults
  otherwise fails. An area where the kernel's reads may grow a stack (`mayGrowFor`) is not modelled;
- every component the kernel saves that was not loaded is put in its initial configuration, from
  the kernel's initial area: `MXCSR` becomes `1F80H` with SSE among them, and may with AVX (a
  standard-form `XRSTOR` loads it, a compacted one, `XRSTORS`, does not; which the kernel uses is fixed at
  boot, `LinuxBoot.xsaves`).
`XLoad.gp` stands for every failure, after which the kernel resets the state and treats the frame as
bad. -/
def fpuRestore (prof : Profile) (s : State) (buf : Addr) : Req (XLoad Cpu) := do
  let feat := prof.feat
  let size := prof.xUserSize
  let rd (o n : Nat) : Option (List Byte) := kernelRead feat s (buf.add o) n
  let byte (o : Nat) : Byte := s.proc.mm.mem.readByte (buf.add o)
  let user := prof.userXfeatures
  if buf = 0 then do
    let pk : { v : BitVec 32 // v &&& 3 = 0 } ← Req.request .initPkru
    Pure.pure (.ok (s.cpu.fpuClear pk.val))
  else if !accessOk feat buf (size + 4) then Pure.pure .gp else
  if mayGrowFor feat s .read buf (size + 4) then
    Pure.pure (.notModelled "a signal frame's XSAVE area for which the kernel may grow a stack") else
  match rd 464 48 with
  | none => Pure.pure .gp
  | some sw =>
  let magic2 : Option (Option (List Byte)) :=
    if ofBytesLE 32 (sw.take 4) = FP_XSTATE_MAGIC1 then some (rd size 4) else none
  match magic2 with
  | some none => Pure.pure .gp
  | _ =>
  let fxOnly := match magic2 with
    | some (some m) => ofBytesLE 32 m != FP_XSTATE_MAGIC2
    | _ => true
  let xrestore : BitVec 64 := (if fxOnly then 3 else ofBytesLE 64 ((sw.drop 8).take 8)) &&& user
  let ok (o n : Nat) : Bool := kernelReadable feat s (buf.add o) n
  let comp (i : Nat) : Nat × Nat :=
    if i = 0 then (0, 160) else if i = 1 then (160, 256) else (prof.xOffset i, prof.xSize i)
  -- the restore, which fails when it faults and the area is not wholly readable
  let retried (r : XLoad Cpu) : Req (XLoad Cpu) :=
    if kernelReadable feat s buf size then Pure.pure r else do
      let faults : Fin 2 ← Req.request (.pick 1)
      Pure.pure (if faults.val = 1 then XLoad.gp else r)
  let loaded ← if fxOnly then
      if buf.toNat % 16 ≠ 0 || !ok 0 512 then Pure.pure XLoad.gp
      else retried ((fxrstor prof s.cpu.x87 s.cpu.vec byte true).map fun (x, v) =>
        { s.cpu with x87 := x, vec := v })
    else
      if buf.toNat % 64 ≠ 0 || !ok 512 64 then Pure.pure XLoad.gp else
      let bv : BitVec 64 := ofBytesLE 64 ((List.range 8).map fun k => byte (512 + k))
      let operated := (List.range 10).filter xrestore.getLsbD
      let needs := (if xrestore.getLsbD 1 || xrestore.getLsbD 2 then ok 24 8 else true) &&
        operated.all fun i => !bv.getLsbD i || ok (comp i).1 (comp i).2
      if !needs then Pure.pure XLoad.gp
      else retried (xrstor prof s.cpu byte xrestore)
  match loaded with
  | .ok c =>
    let initBv := user &&& ~~~xrestore
    let c₁ := (List.range 10).foldl (fun c i => if initBv.getLsbD i then c.xSetInit i else c) c
    if initBv.getLsbD 1 then Pure.pure (.ok { c₁ with vec := { c₁.vec with mxcsr := 0x1F80 } })
    else if initBv.getLsbD 2 ∧ !prof.linux.xsaves then
      Pure.pure (.ok { c₁ with vec := { c₁.vec with mxcsr := 0x1F80 } })
    else Pure.pure (.ok c₁)
  | r => Pure.pure r

/-- `rt_sigreturn()` (`arch/x86/kernel/signal_64.c`): return from a handler through the frame the
kernel wrote, at `rsp - 8` (the handler's `ret` popped the return address), as the process may have
changed it:
- the frame must pass `access_ok` of its size, a constant below a page (`accessOkFixed`: only its
  address is checked, and the bytes read after it decide the rest); the mask
  (`uc_sigmask`) and `uc_flags` are read and the mask set, without `SIGKILL` and `SIGSTOP`;
- the alternate stack is read and set as `sigaltstack` would at the current `rsp`, its errors
  ignored (`restore_altstack`);
- the registers are read (`struct sigcontext`, up to `reserved1`): the general registers, `rsp`,
  `rip`, the `RFLAGS` bits of `Rflags.setFix`, and `cs` and `ss` with privilege level 3. A `cs` other
  than the 64-bit user code segment is not modelled (the process would run 32-bit code); with
  `UC_STRICT_RESTORE_SS` in `uc_flags` an `ss` other than the user data segment is not modelled
  (returning to user mode faults), without it such an `ss` becomes the user data segment
  (`force_valid_ss`: the model has no other valid data segment). `RF` set suppresses an instruction
  breakpoint on the next instruction, which then clears it;
- the processor state is restored from the area the registers point to (`fpuRestore`);
- the call returns the restored `rax`, with the unblocked signals handled.
The kernel's reads of the frame grow a stack where they must (`growFor`), in its order: the mask
(offset 304) first, then `uc_flags` (offset 8), the lowest byte read, and the rest above it. A byte that cannot be read, or a failed restore of the processor state
(after which it is reset, `Cpu.fpuClear`), makes the frame bad: the kernel sends `SIGSEGV` (`signal_fault`, `force_sig`) and
returns 0 in `rax`, with what was restored so far. A thread with a shadow stack is not modelled
(the kernel checks the token, `restore_signal_shadow_stack`). -/
def sysRtSigreturn (prof : Profile) (s : State) : Req StepResult := do
  let feat := prof.feat
  let frame := s.cpu.gpr.rsp - 8
  let rd (t : State) (o n : Nat) : Option (List Byte) := kernelRead feat t (frame.add o) n
  let ev (ret : BitVec 64) : Event := ⟨s.cpu.gpr.rax, syscallArgs s, ret, [], []⟩
  let bad (t : State) : Req StepResult :=
    deliverSignals prof none (some (ev 0)) ((t.force ⟨SigInfo.kernel SIGSEGV, .kernel⟩).setRax 0)
  let stop (what : String) : Req StepResult := Pure.pure (.stopped (.notModelled (.feature what)))
  if s.thread.shstk.isSome then stop "rt_sigreturn with a shadow stack" else
  if !accessOkFixed feat frame rtSigframeSize then bad s else do
  let s ← growFor prof s .read (frame.add 304) 8
  match rd s 304 8 with
  | none => bad s
  | some mb => do
  let s ← growFor prof s .read (frame.add 8) 296
  match rd s 8 8 with
  | some fb =>
    let ucFlags : BitVec 64 := ofBytesLE 64 fb
    let s₁ := s.modThread fun t => { t with sigmask := SigSet.unblockable (ofBytesLE 64 mb) }
    match rd s₁ 24 24 with
    | none => bad s₁
    | some ab => do
      let s₂ ← match ← setAltStack prof s₁ s.cpu.gpr.rsp ab with
        | .ok t => Pure.pure t
        | .error _ => Pure.pure s₁
      match rd s₂ 48 192 with
      | none => bad s₂
      | some sc =>
        let w (o : Nat) : BitVec 64 := ofBytesLE 64 ((sc.drop o).take 8)
        let h (o : Nat) : BitVec 16 := ofBytesLE 16 ((sc.drop o).take 2)
        let cs := h 144 ||| 3
        let ss₀ := h 150 ||| 3
        let ss : BitVec 16 := if ucFlags &&& UC_STRICT_RESTORE_SS = 0 then 0x2b else ss₀
        let flags := s₂.cpu.rflags.setFix (w 136)
        if cs ≠ 0x33 then stop "rt_sigreturn to a code segment other than the 64-bit user one" else
        if ss ≠ 0x2b then stop "rt_sigreturn to a stack segment other than the user one" else
        let s₃ := s₂.modCpu fun c => { c with
          gpr := ⟨w 104, w 112, w 96, w 88, w 120, w 80, w 72, w 64, w 0, w 8, w 16, w 24, w 32, w 40,
                  w 48, w 56⟩
          rip := w 128
          rflags := flags
          seg := { c.seg with cs, ss } }
        match ← fpuRestore prof s₃ (w 184) with
        | .ok c => sysReturnSignals prof s (s₃.modCpu fun _ => c) (w 104) []
        | .notModelled what => stop what
        | .gp => do
          let pk : { v : BitVec 32 // v &&& 3 = 0 } ← Req.request .initPkru
          bad (s₃.modCpu fun c => c.fpuClear pk.val)
  | none => bad s

end ZellicX86
