import ZellicX86.Spec.Semantics.Basic
/-!
# Instruction semantics: control transfer and system instructions

Each definition follows the "Operation" and "Flags Affected" sections of the instruction's page in
Intel SDM Vol. 2 (rev. 092); where AMD APM Vol. 3 (rev. 4.10) differs, the case says so. Forms not
implemented stop with `notModelled`.
-/
namespace ZellicX86
open Decode Prog

/-- A `CALL` to a non-canonical target, on a processor of vendor `v`, whose return address would be
`next`: `#GP(0)`, with nothing pushed. When the push would fault as well, which exception comes first
depends on the vendor. AMD's operation pushes first and checks the target after (APM Vol. 3, "CALL
(Near)": `PUSH.v next_RIP`, then `EXCEPTION[#GP(0)]` for a non-canonical target), so the push's fault
(`#SS(0)` or `#PF`, including a protection-key `#PF`) comes first; an AMD Zen 4 does so. Intel's lists the
`#GP(0)` (SDM Vol. 2, "CALL", 64-Bit Mode Exceptions) but does not place it in the operation, so
the order is a `pick`. The push followed by `#GP(0)` discards the push when it does not fault. -/
def callNonCanonical (v : Vendor) (next : Addr) : Prog Ctl := do
  let pushFirst ← if v = .amd then Pure.pure true else do
    let i ← choice 1
    Pure.pure (i.val = 1)
  if pushFirst then push64 next
  throw (.gp 0)

/-- `CALL` (near) to a relative target or through a register or memory operand: a memory target is
read before the return address is pushed (program order, as AMD's operation has it, APM Vol. 3, "CALL
(Near)"), so when both would fault, the read's fault is reported (an AMD Zen 4 does so, and Intel's
manual does not order them), and a non-canonical target raises `#GP(0)` (`callNonCanonical`). A thread with
a user shadow stack (`ThreadK.shstk`) also pushes the return address there (SDM Vol. 1, 18.2):
not modelled. -/
def Sem.call (prof : Profile) (i : Inst) : Prog Ctl := do
  let feat := prof.feat
  let t ← readThread
  if t.shstk = none then
    match i.ops with
    | [.rel off] => do
      let next ← readRip
      if !Addr.canonical feat.la57 (next + BitVec.ofNat 64 off) then callNonCanonical prof.vendor next else
      push64 next
      writeRip (next + BitVec.ofNat 64 off)
      done
    | [t] => do
      let target ← readOp 64 t
      let next ← readRip
      if !Addr.canonical feat.la57 target then callNonCanonical prof.vendor next else
      push64 next
      writeRip target
      done
    | _ => formNotModelled i
  else unmodelled (.feature "CALL with a user shadow stack")

/-- `JMP` (near) to a relative target or through a register or memory operand (SDM Vol. 2,
"JMP"). -/
def Sem.jmp (feat : Features) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [.rel off] => do
    let next ← readRip
    jumpTo feat (next + BitVec.ofNat 64 off)
    done
  | [t] => do
    let target ← readOp 64 t
    jumpTo feat target
    done
  | _ => formNotModelled i

/-- `Jcc`: to the relative target if condition `c` holds (SDM Vol. 2, "Jcc"). -/
def Sem.jcc (feat : Features) (c : Cond) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [.rel off] => do
    let f ← readFlags
    let next ← readRip
    if f.cond c then jumpTo feat (next + BitVec.ofNat 64 off)
    done
  | _ => formNotModelled i

/-- `JRCXZ`, `JECXZ`: to the relative target if the count register is 0, `RCX`, or `ECX` with a `67`
prefix (the decoder's operand, `OS.rCX`); no flags are read or changed. The operand size is 64, so
the target is not truncated (SDM Vol. 2A, "Jcc": "In 64-bit mode, operand size is fixed at 64 bits";
AMD APM Vol. 3, "JCXZ, JECXZ, JRCXZ", p. 207: it "defaults to 64 bits", and a `66` prefix without `REX.W`, which AMD
honours, is not modelled, `finishForm`). -/
def Sem.jrcxz (feat : Features) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [.rel off, c] => do
    let n ← readOp c.width c
    let next ← readRip
    if n = 0 then jumpTo feat (next + BitVec.ofNat 64 off)
    done
  | _ => formNotModelled i

/-- `LOOP`, `LOOPE`, `LOOPNE`: decrement the count register of the address size (`rcx`, or `ecx` with `67`;
an `ecx` write clears bits 63–32 of `rcx`), then branch if it is nonzero and, for `LOOPE`/`LOOPNE`, `ZF` is 1/0
(`zf = none`: no condition). No flags change. A non-canonical target raises `#GP(0)` (`jumpTo`). The
`66`-prefixed form without `REX.W` is not modelled (the decoder). SDM Vol. 2A, "LOOP/LOOPcc"; AMD APM Vol. 3,
"LOOP, LOOPE, LOOPNE, LOOPNZ, LOOPZ". -/
def Sem.loop (feat : Features) (zf : Option Bool) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [.rel off, c] => do
    let n ← readOp c.width c
    let n := n - 1
    writeOp c n
    let cond ← match zf with
      | none => Prog.pure true
      | some b => do let f ← readFlags; Prog.pure (f.zf == b)
    let next ← readRip
    if n != 0 && cond then jumpTo feat (next + BitVec.ofNat 64 off)
    done
  | _ => formNotModelled i

/-- `RET` (near), and `RET imm16`, which releases `imm16` more bytes of stack: the return address
is checked for canonical form before `rsp` changes (SDM Vol. 2, "RET"). A thread with a user shadow
stack (`ThreadK.shstk`) also pops the return address from there and raises `#CP` when the two
differ (SDM Vol. 1, 18.2): not modelled. -/
def Sem.ret (feat : Features) (i : Inst) : Prog Ctl := do
  let t ← readThread
  if t.shstk = none then
    match i.ops with
    | [] => do
      let sp ← readReg 4
      let target ← read ⟨sp, true⟩ 64
      if !Addr.canonical feat.la57 target then throw (.gp 0) else
      writeReg 4 (sp + 8)
      writeRip target
      done
    | [.imm _ n] => do
      let sp ← readReg 4
      let target ← read ⟨sp, true⟩ 64
      if !Addr.canonical feat.la57 target then throw (.gp 0) else
      writeReg 4 (sp + 8 + BitVec.ofNat 64 n)
      writeRip target
      done
    | _ => formNotModelled i
  else unmodelled (.feature "RET with a user shadow stack")

/-- `NOP`, including the multi-byte forms `0F 1F /0`, which access no memory (SDM Vol. 2,
"NOP"). -/
def Sem.nop (_ : Inst) : Prog Ctl := done

/-- `PREFETCHNTA`, `PREFETCHT0`, `PREFETCHT1`, `PREFETCHT2`: a hint to move the line at the memory
operand closer to the processor, with no architectural effect: it neither faults nor accesses
memory as a load does (SDM Vol. 2, "PREFETCHh": "does not affect program behavior", "does not
cause an exception"). -/
def Sem.prefetch (_ : Inst) : Prog Ctl := done

/-- `LFENCE`, `SFENCE`, `MFENCE`: order the loads, the stores, or all memory accesses before
it against those after it (SDM Vol. 2, "LFENCE", "SFENCE", "MFENCE"; Vol. 3A, 11.2.5). -/
def Sem.lfence (_ : Inst) : Prog Ctl := do fenceOp .load; done
/-- See `Sem.lfence`. -/
def Sem.sfence (_ : Inst) : Prog Ctl := do fenceOp .store; done
/-- See `Sem.lfence`. -/
def Sem.mfence (_ : Inst) : Prog Ctl := do fenceOp .full; done

/-- `ENDBR64` executes as a `NOP`: Linux v6.18 does not enable indirect-branch tracking for user
mode. -/
def Sem.endbr64 (_ : Inst) : Prog Ctl := done

/-- `RDSSPD`/`RDSSPQ`: a `NOP` for a thread without a user shadow stack, on every processor (with
`CR4.CET` or `IA32_U_CET.SH_STK_EN` clear, and on one without CET, where `F3 0F 1E` is a hint
`NOP`); with one it reads `SSP` (SDM Vol. 2, "RDSSPD/RDSSPQ"): not modelled. -/
def Sem.rdssp (_ : Inst) : Prog Ctl := do
  let t ← readThread
  if t.shstk = none then done else unmodelled (.feature "RDSSP with a user shadow stack")

/-- `INCSSPD`/`INCSSPQ`, on a processor with CET shadow stacks (`Features.cetSs`; without them the
decoder makes the encoding not modelled, since no manual specifies it there): `#UD` for a thread without
a user shadow stack (`CR4.CET` or `IA32_U_CET.SH_STK_EN` clear); with one it pops entries off the shadow
stack (SDM Vol. 2, "INCSSPD/INCSSPQ"): not modelled. -/
def Sem.incssp (_ : Inst) : Prog Ctl := do
  let t ← readThread
  if t.shstk = none then throw .ud else unmodelled (.feature "INCSSP with a user shadow stack")

/-- `XTEST`: `ZF` cleared inside a transaction (an RTM region begun by `XBEGIN`, or an HLE region begun
by an `XACQUIRE` hint), set outside one; `CF`, `OF`, `SF`, `PF` and `AF` cleared (SDM Vol. 2, "XTEST";
Vol. 1, 17.3.2). No transaction is ever open in the model: `XBEGIN` is not modelled, and on a processor
with HLE neither are the hints (the decoder, `finishForm`), so `ZF` is set. The decoder admits `XTEST`
only on a processor with RTM or HLE (`Features.rtm`, `Features.hle`); on one with neither it is `#UD`. -/
def Sem.xtest (_ : Inst) : Prog Ctl := do
  let f ← readFlags
  writeFlags { f with zf := true, cf := false, of := false, sf := false, pf := false, af := false }
  done

/-- `SYSCALL`: `rcx` receives the address of the next instruction and `r11` `RFLAGS` (SDM Vol. 2,
"SYSCALL"); the kernel does the rest (`Spec/Linux/Syscall.lean`). -/
def Sem.syscall (_ : Inst) : Prog Ctl := do
  let next ← readRip
  let f ← readFlags
  writeReg 1 next
  writeReg 11 f.toBits
  Pure.pure .syscall

/-- `HLT` at privilege level 3 raises `#GP(0)` (SDM Vol. 2, "HLT"). -/
def Sem.hlt (_ : Inst) : Prog Ctl := throw (.gp 0)

/-- `INT3` raises `#BP` (SDM Vol. 2, "INT n/INTO/INT3/INT1"). -/
def Sem.int3 (_ : Inst) : Prog Ctl := throw .bp

/-- `UD2` raises `#UD` (SDM Vol. 2, "UD"). -/
def Sem.ud2 (_ : Inst) : Prog Ctl := throw .ud

/-- `CPUID`: `#GP(0)` with CPUID faulting on (`ThreadK.cpuidFaults`); otherwise a serializing
instruction (SDM Vol. 3A, 11.3) that writes the result of leaf `EAX`, subleaf `ECX` on the CPU
the instruction executes on into `EAX`, `EBX`, `ECX`, `EDX`, clearing bits 63–32 of `RAX`, `RBX`,
`RCX`, `RDX` (SDM Vol. 2, "CPUID"). Which of the profile's CPUs that is, is a choice: the thread
may run on any of them, and moves between them when the kernel runs, which it may between any
two instructions. -/
def Sem.cpuid (prof : Profile) (_ : Inst) : Prog Ctl := do
  let t ← readThread
  if t.cpuidFaults then throw (.gp 0) else do
  fenceOp .serializing
  let leaf ← readReg 0
  let sub ← readReg 1
  let cpu ← choice (prof.cpus - 1)
  let r := prof.cpuid cpu.val (leaf.setWidth 32) (sub.setWidth 32)
  writeReg 0 (r.eax.setWidth 64)
  writeReg 3 (r.ebx.setWidth 64)
  writeReg 1 (r.ecx.setWidth 64)
  writeReg 2 (r.edx.setWidth 64)
  done

/-- `RDTSC`: `#GP(0)` when the thread's `RDTSC` faults (`ThreadK.tscFaults`: Linux sets
`CR4.TSD`); otherwise the time-stamp counter (`Request.tsc`) into `EDX:EAX`, clearing bits 63–32
of `RAX` and `RDX` (SDM Vol. 2, "RDTSC"). Not serializing, so it needs no fence. -/
def Sem.rdtsc (_ : Inst) : Prog Ctl := do
  let t ← readThread
  if t.tscFaults then throw (.gp 0) else do
  let v ← readTsc
  writeReg 0 ((v.setWidth 32).setWidth 64)
  writeReg 2 ((v.extractLsb' 32 32).setWidth 64)
  done

/-- `RDTSCP`: `#GP(0)` when the thread's `RDTSC` faults (`ThreadK.tscFaults`: `CR4.TSD` governs
both); otherwise, after all earlier instructions have executed and their loads are globally
visible (a load fence), the time-stamp counter (`Request.tsc`) into `EDX:EAX` and `TSC_AUX` into
`ECX`, clearing bits 63–32 of `RAX`, `RDX`, `RCX` (SDM Vol. 2, "RDTSCP"). `TSC_AUX` is the value
Linux wrote on the CPU the instruction executes on (`Profile.tscAux`); which of the profile's CPUs
that is, is a choice, as for `CPUID`. The counter and `TSC_AUX` are read together on that CPU. -/
def Sem.rdtscp (prof : Profile) (_ : Inst) : Prog Ctl := do
  let t ← readThread
  if t.tscFaults then throw (.gp 0) else do
  fenceOp .load
  let cpu ← choice (prof.cpus - 1)
  let v ← readTsc
  writeReg 0 ((v.setWidth 32).setWidth 64)
  writeReg 2 ((v.extractLsb' 32 32).setWidth 64)
  writeReg 1 ((prof.tscAux cpu.val).setWidth 64)
  done

/-- `XGETBV`: `#UD` unless the OS enabled `XSAVE` (`CR4.OSXSAVE`); `ECX = 0` reads `XCR0` into
`EDX:EAX` (bits 63–32 of `RAX` and `RDX` cleared); `ECX = 1` reads `XCR0 AND XINUSE`: which
components are in use is left open within the manuals' bounds (a component not in its initial state is in use,
and SSE is whenever `MXCSR` is not `1F80H`; `Cpu.xInuseRequired`, `Request.xinuse`). It raises `#GP(0)`
without CPUID.(EAX=0DH,ECX=1):EAX[2], on the CPU the instruction executes on. If an enabled component is
one whose state the model does not represent (`xHeld`), the run ends as not modelled; any other `ECX` raises `#GP(0)`
(SDM Vol. 1, 13.6; Vol. 2, "XGETBV"; APM Vol. 3, "XGETBV"). -/
def Sem.xgetbv (prof : Profile) (_ : Inst) : Prog Ctl :=
  if prof.xcr0.isNone then throw .ud else do
  let x := prof.xcr0.getD 0
  let c ← readReg 1
  if c.setWidth 32 = 0 then do
    writeReg 0 ((x.setWidth 32).setWidth 64)
    writeReg 2 ((x.extractLsb' 32 32).setWidth 64)
    done
  else if c.setWidth 32 = 1 then do
    let cpu ← choice (prof.cpus - 1)
    if !(prof.cpuid cpu.val 0xD 1).eax.getLsbD 2 then throw (.gp 0)
    else if x &&& ~~~xHeld ≠ 0 then unmodelled (.form "xgetbv XINUSE of an unheld state component")
    else do
      let v ← Prog.op (.xinuse x) .pure
      writeReg 0 ((v.setWidth 32).setWidth 64)
      writeReg 2 ((v.extractLsb' 32 32).setWidth 64)
      done
  else throw (.gp 0)

end ZellicX86
