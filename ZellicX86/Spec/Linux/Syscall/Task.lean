import ZellicX86.Spec.Linux.Env
import ZellicX86.Spec.Linux.Syscall.Common
/-!
# Linux system calls: the thread's and the process's own settings

`arch_prctl` (the `FS` and `GS` bases, `CPUID` faulting), `set_tid_address`, `set_robust_list` and
`rseq`, which a C library calls for its first thread before `main`; and the resource limits
(`prlimit64`, `setrlimit`, `getrlimit`). The kernel computes all of them from the
state and the arguments; the choices are where the thread runs when `rseq` registers an area
(`Request.resumeIds`), whether the kernel lets the process set a resource limit
(`Request.setRlimit`), and how much of a faulting copy to user memory was written (`copyOut`).

Not modelled: the extended-state permissions (`ARCH_REQ_XCOMP_PERM` and its kin, for AMX), mapping a vDSO
(`ARCH_MAP_VDSO_*`), linear address masking (`ARCH_ENABLE_TAGGED_ADDR` and its kin), shadow stacks
(`ARCH_SHSTK_*`); the limits of another process.

What the thread state set here does later: `clear_child_tid` and the robust list matter when the
thread exits while another thread or process shares the memory (`kernel/fork.c` `mm_release`,
`kernel/futex/core.c` `exit_robust_list`); with one thread, the process's exit ends its memory, so
no run here observes them. The `rseq` area is written at every return to user mode (`kernelEntry`).

Sources: Linux v6.18 `arch/x86/kernel/process.c` (`arch_prctl`), `arch/x86/kernel/process_64.c`
(`do_arch_prctl_64`), `arch/x86/include/uapi/asm/prctl.h`, `kernel/fork.c` (`set_tid_address`),
`kernel/futex/syscalls.c` (`set_robust_list`), `kernel/rseq.c` (`rseq`), `include/uapi/linux/rseq.h`,
`kernel/sys.c` (`prlimit64`, `do_prlimit`), `arch_prctl(2)`, `set_tid_address(2)`,
`set_robust_list(2)`, `rseq(2)`, `getrlimit(2)`.
-/
namespace ZellicX86

/-- `arch_prctl` option: set the `GS` base (`arch/x86/include/uapi/asm/prctl.h`). -/
def ARCH_SET_GS : Nat := 0x1001
/-- `arch_prctl` option: set the `FS` base. -/
def ARCH_SET_FS : Nat := 0x1002
/-- `arch_prctl` option: store the `FS` base at the argument. -/
def ARCH_GET_FS : Nat := 0x1003
/-- `arch_prctl` option: store the `GS` base at the argument. -/
def ARCH_GET_GS : Nat := 0x1004
/-- `arch_prctl` option: whether `CPUID` is enabled for the thread. -/
def ARCH_GET_CPUID : Nat := 0x1011
/-- `arch_prctl` option: enable or disable `CPUID` for the thread. -/
def ARCH_SET_CPUID : Nat := 0x1012

/-- `s` with its thread's kernel state changed by `f`. -/
def State.modThread (s : State) (f : ThreadK → ThreadK) : State := { s with thread := f s.thread }

/-- `arch_prctl(option, arg)` (`arch/x86/kernel/process.c` `arch_prctl`, `process_64.c`
`do_arch_prctl_64`); `option` is an `int`:
- `ARCH_GET_CPUID` returns 1, or 0 while `CPUID` faults for the thread;
- `ARCH_SET_CPUID` fails with `ENODEV` unless the kernel's boot CPU has
  `X86_FEATURE_CPUID_FAULT` (`Profile.linux.cpuidFault`); otherwise 0 disables `CPUID` for the
  thread and any nonzero 64-bit argument enables it (`set_cpuid_mode`);
- `ARCH_SET_FS` and `ARCH_SET_GS` set the base to `arg`, and the selector to 0, unless `arg` is at
  or above `TASK_SIZE_MAX` (`EPERM`);
- `ARCH_GET_FS` and `ARCH_GET_GS` store the base, 8 bytes, at `arg` (`put_user`: one store, which
  writes all or nothing; `EFAULT`);
- the options listed in the module's header are not modelled; every other one is `EINVAL`. -/
def sysArchPrctl (prof : Profile) (s : State) : Req StepResult :=
  let feat := prof.feat
  let opt := arg32 s.cpu.gpr.rdi
  let arg := s.cpu.gpr.rsi
  let ret (s' : State) (v : BitVec 64) (toProc : List Byte) : Req StepResult :=
    Pure.pure (sysReturn s' v [] toProc)
  let fail (e : Nat) : Req StepResult := ret s (errRet e) []
  let stop (what : String) : Req StepResult := Pure.pure (.stopped (.notModelled (.feature what)))
  if opt = ARCH_GET_CPUID then ret s (if s.thread.cpuidFaults then 0 else 1) []
  else if opt = ARCH_SET_CPUID then
    if !prof.linux.cpuidFault then fail ENODEV
    else ret (s.modThread fun t => { t with cpuidFaults := arg = 0 }) 0 []
  else if opt = ARCH_SET_FS ∨ opt = ARCH_SET_GS then
    if arg.toNat ≥ userPtrMax feat then fail EPERM
    else ret (s.modCpu fun c => { c with seg := if opt = ARCH_SET_FS
      then { c.seg with fs := 0, fsBase := arg } else { c.seg with gs := 0, gsBase := arg } }) 0 []
  else if opt = ARCH_GET_FS ∨ opt = ARCH_GET_GS then
    let bs := toBytesLE (if opt = ARCH_GET_FS then s.cpu.seg.fsBase else s.cpu.seg.gsBase) 8
    if !accessOk feat arg 8 then fail EFAULT else do
    let s ← growFor prof s .write arg 8
    match kernelWrite feat s arg bs with
    | some s' => ret s' 0 bs
    | none => ret s (errRet EFAULT) []
  else if (0x1021 ≤ opt ∧ opt ≤ 0x1025) ∨ (0x2001 ≤ opt ∧ opt ≤ 0x2003) ∨
      (0x4001 ≤ opt ∧ opt ≤ 0x4004) ∨ (0x5001 ≤ opt ∧ opt ≤ 0x5005) then
    stop "arch_prctl of extended-state permissions, the vDSO, tagged addresses or shadow stacks"
  else fail EINVAL

/-- `set_tid_address(tidptr)` (`kernel/fork.c`): records `tidptr` as the thread's
`clear_child_tid` and returns the thread id. -/
def sysSetTidAddress (s : State) : Req StepResult :=
  Pure.pure (sysReturn (s.modThread fun t => { t with clearChildTid := s.cpu.gpr.rdi })
    (BitVec.ofNat 64 s.thread.tid) [] [])

/-- `set_robust_list(head, len)` (`kernel/futex/syscalls.c`): `len` must be the size of `struct
robust_list_head`, 24 (`EINVAL`); records `head`, unchecked. -/
def sysSetRobustList (s : State) : Req StepResult :=
  if s.cpu.gpr.rsi.toNat ≠ 24 then Pure.pure (sysReturn s (errRet EINVAL) [] [])
  else Pure.pure (sysReturn (s.modThread fun t => { t with robustList := s.cpu.gpr.rdi }) 0 [] [])

/-- `RSEQ_FLAG_UNREGISTER` (`include/uapi/linux/rseq.h`). -/
def RSEQ_FLAG_UNREGISTER : Nat := 1

/-- `rseq(area, len, flags, sig)` (`kernel/rseq.c`); `len`, `flags` and `sig` are 32-bit.
- Unregistering (`flags` has `RSEQ_FLAG_UNREGISTER`): no other flag (`EINVAL`); the thread's area
  must be `area` with length `len` (`EINVAL`) and signature `sig` (`EPERM`); the kernel resets the
  ids in the area (`cpu_id_start`, `node_id`, `mm_cid` to 0, `cpu_id` to `RSEQ_CPU_ID_UNINITIALIZED`,
  -1; all four fields lie in one 32-byte block, so the stores fault all or none: `EFAULT`) and the
  thread has no area.
- Registering (`flags` 0, else `EINVAL`): with an area registered, the same area and length but
  another signature is `EPERM`, the same signature `EBUSY`, and anything else `EINVAL`. Otherwise
  `len` must be at least `ORIG_RSEQ_SIZE`, 32, and `area` aligned to 32 (`AT_RSEQ_ALIGN`;
  `EINVAL`), and pass `access_ok` (`EFAULT`); the kernel reads the area's `rseq_cs` (offset 8, 8
  bytes; `EFAULT`) and clears it if it is not 0 (`EFAULT`). Then the area is registered, and before
  the thread returns to user mode the kernel writes its ids into it as at every return
  (`kernelEntry`, with where the thread runs as `Request.resumeIds`), which ends the process by
  `SIGSEGV` if it cannot. -/
def sysRseq (prof : Profile) (s : State) : Req StepResult := do
  let feat := prof.feat
  let area := s.cpu.gpr.rdi
  let len := arg32 s.cpu.gpr.rsi
  let flags := arg32 s.cpu.gpr.rdx
  let sig := s.cpu.gpr.r10.setWidth 32
  let fail (e : Nat) : Req StepResult := Pure.pure (sysReturn s (errRet e) [] [])
  if flags % 2 = 1 then
    if flags ≠ RSEQ_FLAG_UNREGISTER then fail EINVAL else
    match s.thread.rseq with
    | none => fail EINVAL
    | some r =>
      if r.area ≠ area ∨ r.len.toNat ≠ len then fail EINVAL
      else if r.sig ≠ sig then fail EPERM
      else if !accessOk feat area len then fail EFAULT
      else do
        let s ← growFor prof s .write area 28
        let reset := [(0, 0), (4, 0xffffffff), (20, 0), (24, 0)]
        let s' := reset.foldl (fun acc (o, v) => acc.bind fun t =>
          kernelWrite feat t (area.add o) (toBytesLE (BitVec.ofNat 32 v) 4)) (some s)
        match s' with
        | none => Pure.pure (sysReturn s (errRet EFAULT) [] [])
        | some t => Pure.pure (sysReturn (t.modThread fun th => { th with rseq := none }) 0 [] [])
  else if flags ≠ 0 then fail EINVAL
  else
    match s.thread.rseq with
    | some r =>
      if r.area ≠ area ∨ r.len.toNat ≠ len then fail EINVAL
      else if r.sig ≠ sig then fail EPERM
      else fail EBUSY
    | none =>
      if len < 32 ∨ area.toNat % 32 ≠ 0 then fail EINVAL
      else if !accessOk feat area len then fail EFAULT
      else do
        let s ← growFor prof s .read (area.add 8) 8
        match kernelRead feat s (area.add 8) 8 with
        | none => Pure.pure (sysReturn s (errRet EFAULT) [] [])
        | some cs =>
          let s₁ := if ofBytesLE 64 cs = 0 then some s
            else kernelWrite feat s (area.add 8) (toBytesLE (0 : BitVec 64) 8)
          match s₁ with
          | none => Pure.pure (sysReturn s (errRet EFAULT) [] [])
          | some s₁ => do
            let s₂ := s₁.modThread fun th => { th with rseq := some ⟨area, BitVec.ofNat 32 len, sig⟩ }
            let ⟨(cpu, node, mmCid), _⟩ ← Req.request (.resumeIds prof.cpus)
            match kernelEntry feat s₂ cpu node mmCid with
            | .running s₃ _ => Pure.pure (sysReturn s₃ 0 [] [])
            | r => Pure.pure r

/-- Set resource limit `res` of the process to `lim`, or not (`kernel/sys.c` `do_prlimit`): a soft
limit above the hard one is `EINVAL`, a descriptor limit whose hard limit exceeds the largest
`fs.nr_open` the kernel allows (`sysctl_nr_open_max`) is `EPERM`; otherwise the kernel may refuse
(`Request.setRlimit`; a hard descriptor limit above the current, lower `fs.nr_open` setting, or a raised
hard limit without `CAP_SYS_RESOURCE`, is among its refusals). On success the limit is set. The model
reads the limits where the kernel does: `RLIMIT_STACK` at every stack growth (`stackLimitPages`),
`RLIMIT_NOFILE` whenever a descriptor is allocated (`allocFd`, `dupTo`, `fcntl(F_DUPFD)`), `RLIMIT_FSIZE`
in `write` and `writev`; the memory limits only through the refusals `Request.memFail` stands for. The
CPU time limit's `SIGXCPU` and `SIGKILL` (`RLIMIT_CPU`; `kernel/time/posix-cpu-timers.c`) depend on time,
which the model does not have: they are external signals (`EnvEvent.signal`). -/
def setRlimit (s : State) (res : Fin 16) (lim : Rlimit) : Req (Except Nat State) := do
  if lim.cur.toNat > lim.max.toNat then Pure.pure (.error EINVAL)
  else if res = RLIMIT_NOFILE ∧ lim.max.toNat > nrOpenMax then Pure.pure (.error EPERM)
  else
    match ← Req.request (.setRlimit res lim) with
    | some e => Pure.pure (.error e.val)
    | none => Pure.pure (.ok { s with
        proc.signal.rlimits := fun r => if r = res then lim else s.proc.signal.rlimits r })

/-- The 16 bytes of a `struct rlimit`/`struct rlimit64`: the soft limit, then the hard one. -/
def Rlimit.bytes (r : Rlimit) : List Byte := toBytesLE r.cur 8 ++ toBytesLE r.max 8

/-- The limit in the 16 bytes `bs` (`Rlimit.bytes`). -/
def Rlimit.ofBytes (bs : List Byte) : Rlimit := ⟨ofBytesLE 64 (bs.take 8), ofBytesLE 64 (bs.drop 8)⟩

/-- `prlimit64(pid, resource, new, old)` (`kernel/sys.c`); `pid` is a `pid_t`, `resource` 32-bit.
A `new` limit is read first (16 bytes, `EFAULT`). A negative `pid` names no process (`ESRCH`); 0 or
the thread's id is the process itself, any other the limits of another process, not modelled. A
`resource` beyond `RLIMIT_RTTIME` is `EINVAL`. The limit is set as `setRlimit` says (an error
changes nothing); then the limit before the call, soft then hard, 8 bytes each, is copied to `old`
unless it is 0 (`EFAULT`, with the new limit set). -/
def sysPrlimit (prof : Profile) (s : State) : Req StepResult := do
  let pid := argInt s.cpu.gpr.rdi
  let res := arg32 s.cpu.gpr.rsi
  let new := s.cpu.gpr.rdx
  let old := s.cpu.gpr.r10
  let (s, newLim) ← if new = 0 then Pure.pure (s, some none) else do
    let (s, bs?) ← copyIn prof s new 16
    Pure.pure (s, bs?.map fun bs => some (Rlimit.ofBytes bs))
  let fail (e : Nat) : Req StepResult := Pure.pure (sysReturn s (errRet e) [] [])
  let stop (what : String) : Req StepResult := Pure.pure (.stopped (.notModelled (.feature what)))
  match newLim with
  | none => fail EFAULT
  | some newLim =>
  if pid < 0 then fail ESRCH
  else if pid ≠ 0 ∧ pid ≠ s.thread.tid then stop "prlimit64 of another process"
  else if h : res < 16 then do
    let r := s.proc.signal.rlimits ⟨res, h⟩
    let set ← match newLim with
      | none => Pure.pure (.ok s)
      | some lim => setRlimit s ⟨res, h⟩ lim
    match set with
    | .error e => fail e
    | .ok s₁ =>
      if old = 0 then Pure.pure (sysReturn s₁ 0 [] [])
      else
        let (s₂, k, all) ← copyOut prof s₁ old r.bytes
        Pure.pure (sysReturn s₂ (if all then 0 else errRet EFAULT) [] (r.bytes.take k))
  else fail EINVAL

/-- `setrlimit(resource, rlim)` (`kernel/sys.c`); `resource` is 32-bit: the 16 bytes at `rlim` are
read (`copy_from_user`, all or nothing: `EFAULT`), a `resource` beyond `RLIMIT_RTTIME` is `EINVAL`,
and the limit is set as `setRlimit` says. -/
def sysSetrlimit (prof : Profile) (s : State) : Req StepResult := do
  let res := arg32 s.cpu.gpr.rdi
  let (s, bs?) ← copyIn prof s s.cpu.gpr.rsi 16
  let fail (e : Nat) : Req StepResult := Pure.pure (sysReturn s (errRet e) [] [])
  match bs? with
  | none => fail EFAULT
  | some bs =>
    if h : res < 16 then do
      match ← setRlimit s ⟨res, h⟩ (Rlimit.ofBytes bs) with
      | .error e => fail e
      | .ok s' => Pure.pure (sysReturn s' 0 [] [])
    else fail EINVAL

/-- `getrlimit(resource, rlim)` (`kernel/sys.c`); `resource` is 32-bit: a `resource` beyond
`RLIMIT_RTTIME` is `EINVAL`; the limit, soft then hard, is copied to `rlim` (`EFAULT`). -/
def sysGetrlimit (prof : Profile) (s : State) : Req StepResult := do
  let res := arg32 s.cpu.gpr.rdi
  if h : res < 16 then do
    let bs := (s.proc.signal.rlimits ⟨res, h⟩).bytes
    let (s', k, all) ← copyOut prof s s.cpu.gpr.rsi bs
    Pure.pure (sysReturn s' (if all then 0 else errRet EFAULT) [] (bs.take k))
  else Pure.pure (sysReturn s (errRet EINVAL) [] [])

end ZellicX86
