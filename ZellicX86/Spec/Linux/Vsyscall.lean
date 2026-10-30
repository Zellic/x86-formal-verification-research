import ZellicX86.Spec.Linux.Syscall.Time
import ZellicX86.Spec.Linux.Signal
/-!
# Linux's legacy vsyscall emulation

Linux v6.18 `arch/x86/entry/vsyscall/vsyscall_64.c` (`emulate_vsyscall`,
`addr_to_vsyscall_nr`, `write_ok_or_segv`). The fault handler invokes this only for a fetch
at RIP on the legacy page in xonly or emulate mode. It does not execute the page's bytes.
-/
namespace ZellicX86
open Signal

/-- The bytes visible in `vsyscall=emulate` (`arch/x86/entry/vsyscall/vsyscall_emu_64.S`):
`mov imm32, %rax`, `syscall`, `ret` at offsets 0, 1024 and 2048; `int3` padding fills the rest of the page.
The system call numbers are 96, 201 and 309 (`arch/x86/entry/syscalls/syscall_64.tbl`). -/
def vsyscallFrame : Frame := fun o =>
  let i := o.toNat
  let nr := if i / 1024 = 0 then 96 else if i / 1024 = 1 then 201 else 309
  if i ≥ 3072 then 0xcc else
  match i % 1024 with
  | 0 => 0x48 | 1 => 0xc7 | 2 => 0xc0
  | 3 => BitVec.ofNat 8 nr | 4 => BitVec.ofNat 8 (nr / 256)
  | 5 | 6 => 0 | 7 => 0x0f | 8 => 0x05 | 9 => 0xc3
  | _ => 0xcc

/-- Force `SIGSEGV` for a rejected vsyscall (`emulate_vsyscall`, `force_sig` in `kernel/signal.c`).
When an output pointer fails `access_ok` (`write_ok_or_segv`), the signal has `SEGV_MAPERR` with that
address, and the frame's `trapno`, `err` and `cr2` are those of a user write page fault (14, 6, the
address). Otherwise the signal has `SI_KERNEL`, and `trapno`, `err` and `cr2` are unspecified (as in
`setupFrame` without a `TrapRec`). A blocked or ignored `SIGSEGV` is reset to the default action first,
so then, as without a handler, the process ends. -/
def vsyscallSegv (prof : Profile) (s : State) (bad : Option Addr := none) (ev : Option Event := none) : Req StepResult :=
  match bad with
  | some a => deliverSignals prof (some ⟨14, 6, some a⟩) ev
      (s.force ⟨SigInfo.fault SIGSEGV SEGV_MAPERR a, .kernel⟩)
  | none => deliverSignals prof none ev (s.force ⟨SigInfo.kernel SIGSEGV, .kernel⟩)

/-- Emulate an instruction fetch from the vsyscall page (`emulate_vsyscall`). Only offsets 0, 0x400 and
0x800 are entry points; any other offset forces `SIGSEGV`. The kernel first reads the 8-byte return
address at `rsp` (`get_user`; a failure forces `SIGSEGV`), then checks each output pointer with
`access_ok` of its fixed size (a failure: `vsyscallSegv` with that pointer), then calls `gettimeofday`,
`time` or `getcpu`. A call that returns `EFAULT` forces `SIGSEGV`, keeping what it wrote, with `rax`
`-ENOSYS`. A successful call puts its result in `rax`, pops the return address into `rip` and adds 8 to
`rsp`. Other registers and flags are kept, except that `RF` is set, as the processor saved it for the
fetch's page fault and the kernel's return restores it (SDM Vol. 3B, 20.3.1.1). For `getcpu` the kernel
passes 0 as the unused third argument and restores `rdx` afterwards. The event records the system call
made, with its own number, not the caller's `rax`. A non-canonical return address makes the kernel's
return to user mode (`IRETQ`) fault, and the process gets `SIGSEGV` as for a `#GP(0)`
(`arch/x86/entry/entry_64.S`, `fixup_bad_iret` in `arch/x86/kernel/traps.c`; SDM Vol. 2A,
IRET/IRETD/IRETQ). `NT` needs no handling: exception entry clears it (SDM Vol. 3A, 7.12.1.3), and
`IRETQ` restores the saved value. seccomp filters and tracers are assumed absent. -/
def emulateVsyscall (prof : Profile) (s : State) : Req StepResult := do
  let s := s.modCpu fun c => { c with rflags := { c.rflags with rf := true } }
  let off := s.cpu.rip.toNat - 0xffffffffff600000
  if ![0, 0x400, 0x800].contains off then vsyscallSegv prof s else
  let (s, caller) ← copyIn prof s s.cpu.gpr.rsp 8
  match caller with
  | none => vsyscallSegv prof s
  | some bs =>
    let sizes := if off = 0 then [(s.cpu.gpr.rdi, 16), (s.cpu.gpr.rsi, 8)]
      else if off = 0x400 then [(s.cpu.gpr.rdi, 8)]
      else [(s.cpu.gpr.rdi, 4), (s.cpu.gpr.rsi, 4)]
    match sizes.find? (fun (a, n) => !accessOkFixed prof.feat a n) with
    | some (a, _) => vsyscallSegv prof s (some a)
    | none =>
      let nr := if off = 0 then 96 else if off = 0x400 then 201 else 309
      let input := (s.setRax (BitVec.ofNat 64 nr)).modCpu fun c =>
        if off = 0x800 then { c with gpr := { c.gpr with rdx := 0 } } else c
      let r ← if off = 0 then sysGettimeofday prof input
        else if off = 0x400 then sysTime prof input else sysGetcpu prof input
      match r with
      | .stopped o => Pure.pure (.stopped o)
      | .running t ev =>
        let t := t.modCpu fun c => { c with gpr := { c.gpr with rdx := s.cpu.gpr.rdx } }
        if t.cpu.gpr.rax = errRet EFAULT then
          vsyscallSegv prof (t.setRax (errRet ENOSYS)) none ev
        else
          let t := t.modCpu fun c =>
            { c with rip := ofBytesLE 64 bs, gpr := { c.gpr with rsp := c.gpr.rsp.add 8 } }
          if !t.cpu.rip.canonical prof.feat.la57 then
            deliverSignals prof (some ⟨13, 0, none⟩) ev
              (t.force ⟨SigInfo.kernel SIGSEGV, .exception (.gp 0)⟩)
          else Pure.pure (.running t ev)

end ZellicX86
