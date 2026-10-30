import ZellicX86.Spec.Semantics.Basic
/-!
# Instruction semantics: string instructions

`MOVS`, `STOS`, `LODS`, `CMPS`, `SCAS` with and without a repeat prefix, and `CLD`/`STD`, which
set the direction they walk in. Each case follows the "Operation" and "Flags Affected" sections
of the instruction's page in Intel SDM Vol. 2 (rev. 092), and SDM Vol. 1, 7.3.9 "String
Operations"; where AMD APM Vol. 3 (rev. 4.10) differs or says more, the case says so.

A repeated string instruction takes one step per iteration. An iteration that does not end the
repetition ends with `Ctl.again`: the next step starts at the same instruction, with `rcx`, `rsi`
and `rdi` as the iteration left them. So everything that can happen between instructions
(signals, other processes' writes, a tracer) can happen between iterations, as the manuals allow
("Service pending interrupts", SDM Vol. 2, "REP"); an exception in an iteration leaves the state
after the iterations before it, with `rip` at the instruction (SDM Vol. 2, "REP": "the source and
destination registers point to the next string elements ..., the EIP register points to the
string instruction, and the ECX register has the value it held following the last successful
iteration"). The stores of a fast-string operation may become visible to other agents out of
order or repeated (SDM Vol. 1, 7.3.9.3; Vol. 3A, 11.2.4); for one thread they are the stores of
the iterations in order.
-/
namespace ZellicX86
open Decode Prog

/-- Whether the string instruction `i` has a 32-bit address size (a `67` prefix): its pointer
and count registers are then `esi`, `edi`, `ecx` (SDM Vol. 1, 7.3.9.4). The decoder records the
prefix in the memory operands. -/
def Decode.Inst.addr32 (i : Inst) : Bool :=
  i.ops.any fun | .mem x => x.addr32 | _ => false

/-- Register `r` as a pointer or count register of the address size: its low 32 bits with a
32-bit address size. -/
def readAddrReg (a32 : Bool) (r : Reg) : Prog (BitVec 64) :=
  if a32 then do
    let v ← readReg r
    Pure.pure ((v.setWidth 32).setWidth 64)
  else readReg r

/-- Write `v` to the pointer or count register `r`. With a 32-bit address size the result is
zero-extended to 64 bits (AMD APM Vol. 3, Table B-1, footnote 5: "For 32-bit address size, any
pointer and count registers are zero-extended to 64 bits"; the SDM's operation writes `ESI`,
`EDI`, `ECX`, which zero-extends as every 32-bit result does, Vol. 1, 3.4.1.1). -/
def writeAddrReg (a32 : Bool) (r : Reg) (v : BitVec 64) : Prog Unit :=
  if a32 then writeReg r ((v.setWidth 32).setWidth 64) else writeReg r v

/-- Move the pointer register `r` to the next element of `b` bytes: up if `DF = 0`, down if
`DF = 1`. -/
def advance (a32 df : Bool) (b : Nat) (r : Reg) : Prog Unit := do
  let v ← readAddrReg a32 r
  if df then writeAddrReg a32 r (v - BitVec.ofNat 64 b) else writeAddrReg a32 r (v + BitVec.ofNat 64 b)

/-- The access of string operand `o` (a memory operand) of `w` bits. -/
def strAccess (w : Nat) (acc : Access) : Opd → Prog (MemRef × Access × Nat)
  | .mem x => do
    let r ← memRef x
    Pure.pure (r, acc, w / 8)
  | _ => unmodelled (.form "string operand")

/-- One iteration of string instruction `i` of mnemonic `m` (one element of `i.opsz` bits) in direction `df`
(`RFLAGS.DF`), with the pointer registers moved past the element. The two memory operands of
`MOVS` and `CMPS` are checked before either is accessed (`Prog.checkAll`). -/
def stringOp (m : StrMn) (i : Inst) (df : Bool) : Prog Unit := do
  let w := i.opsz
  let b := w / 8
  let a32 := i.addr32
  match m, i.ops with
  -- MOVS: the element at `[rsi]` to `[rdi]`
  | .movs, [d, s] => do
    let as ← strAccess w .read s
    let ad ← strAccess w .write d
    checkAccesses [as, ad]
    let v ← readOp w s
    writeOp d v
    advance a32 df b 6
    advance a32 df b 7
  -- STOS: `AL`/`AX`/`EAX`/`RAX` to `[rdi]`
  | .stos, [d, s] => do
    let v ← readOp w s
    writeOp d v
    advance a32 df b 7
  -- LODS: `[rsi]` to `AL`/`AX`/`EAX`/`RAX` (an 8- or 16-bit load keeps the register's other
  -- bits, a 32-bit one zero-extends, as `writeOp` does)
  | .lods, [d, s] => do
    let v ← readOp w s
    writeOp d v
    advance a32 df b 6
  -- CMPS: the flags of `[rsi] - [rdi]` (SDM: "temp := SRC1 - SRC2"), as `CMP`
  | .cmps, [s1, s2] => do
    let a1 ← strAccess w .read s1
    let a2 ← strAccess w .read s2
    checkAccesses [a1, a2]
    let x ← readOp w s1
    let y ← readOp w s2
    let f ← readFlags
    let (_, f') ← subOp false x y f
    writeFlags f'
    advance a32 df b 6
    advance a32 df b 7
  -- SCAS: the flags of `AL/AX/EAX/RAX - [rdi]`, as `CMP`
  | .scas, [a, s2] => do
    let x ← readOp w a
    let y ← readOp w s2
    let f ← readFlags
    let (_, f') ← subOp false x y f
    writeFlags f'
    advance a32 df b 7
  | mn, _ => unmodelled (.form (reprStr mn))

/-- Execute string instruction `i` of mnemonic `m`, or `CLD`/`STD`, with `rip` already advanced past it.

With a repeat prefix, a count register (`rcx`, or `ecx` with a 32-bit address size) of 0 does
nothing: no element and no register is written (SDM Vol. 2, "REP": `WHILE CountReg ≠ 0`; on an
AMD Zen 4, `67 F3 A4` with `ecx = 0` leaves bits 63–32 of `rcx`, `rsi` and `rdi` as they were).
Otherwise one iteration runs and the count is decremented; the repetition ends when the count
reaches 0 or, for `CMPS` and `SCAS`, when `ZF` is 0 after an iteration with `REPE` or 1 with
`REPNE` (SDM Vol. 2, "REPE/REPZ", "REPNE/REPNZ"). The flags after a faulting iteration of `REPE
CMPS` are those of the iterations before it: the SDM says that "the EFLAGS value is restored to
the state prior to the execution of the instruction"; the model reads "the instruction" as the
faulting iteration, as an AMD Zen 4 behaves. -/
def execString (m : StrMn) (i : Inst) : Prog Ctl :=
  match m with
  -- CLD, STD: the direction flag (SDM Vol. 2, "CLD", "STD"); no other flag changes
  | .cld => do
    let f ← readFlags
    writeFlags { f with df := false }
    done
  | .std => do
    let f ← readFlags
    writeFlags { f with df := true }
    done
  | _ =>
  -- one iteration, in the direction `DF` gives
  let iter : Prog Unit := do
    let f ← readFlags
    if f.df then stringOp m i true else stringOp m i false
  match i.rep with
  | none => do
    iter
    done
  | some r => do
    let a32 := i.addr32
    let c ← readAddrReg a32 1
    if c = 0 then done else do
    iter
    let c' := c - 1
    writeAddrReg a32 1 c'
    if c' = 0 then done else do
    match m, r with
    | .cmps, .rep | .scas, .rep => do
      let f ← readFlags
      if f.zf then Pure.pure .again else done
    | .cmps, .repne | .scas, .repne => do
      let f ← readFlags
      if f.zf then done else Pure.pure .again
    | _, _ => Pure.pure .again

end ZellicX86
