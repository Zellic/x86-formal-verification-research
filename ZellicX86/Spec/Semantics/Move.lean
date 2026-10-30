import ZellicX86.Spec.Semantics.Basic
/-!
# Instruction semantics: moves

Each definition follows the "Operation" and "Flags Affected" sections of the instruction's page in
Intel SDM Vol. 2 (rev. 092); where AMD APM Vol. 3 (rev. 4.10) differs, the case says so. Forms not
implemented stop with `notModelled`.
-/
namespace ZellicX86
open Decode Prog

/-- `MOV d, s`, also the `movabs` form `B8+r io` (SDM Vol. 2, "MOV"). -/
def Sem.mov (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do
    let v ← readOp i.opsz s
    writeOp d v
    done
  | _ => formNotModelled i

/-- `MOVZX d, s`: the source zero-extended to the operand size (SDM Vol. 2, "MOVZX"). -/
def Sem.movzx (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do
    let v ← readOp s.width s
    writeOp d (v.setWidth i.opsz)
    done
  | _ => formNotModelled i

/-- `MOVSX`, `MOVSXD d, s`: the source sign-extended to the operand size (SDM Vol. 2,
"MOVSX/MOVSXD"). -/
def movSigned (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do
    let v ← readOp s.width s
    writeOp d (v.signExtend i.opsz)
    done
  | _ => formNotModelled i

/-- `MOVSX` (`movSigned`). -/
def Sem.movsx (i : Inst) : Prog Ctl := movSigned i
/-- `MOVSXD` (`movSigned`). -/
def Sem.movsxd (i : Inst) : Prog Ctl := movSigned i

/-- `LEA d, m`: the effective address (no segment base), truncated to the operand size (SDM
Vol. 2, "LEA"). -/
def Sem.lea (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, .mem x] => do
    let a ← effOffset x
    writeOp d (a.setWidth i.opsz)
    done
  | _ => formNotModelled i

/-- `BSWAP d`, 32 and 64 bits. With a 16-bit register "the result is undefined" (SDM Vol. 2, "BSWAP";
APM Vol. 3, "BSWAP": "the result of applying the BSWAP instruction to a 16-bit register is undefined"):
an undefined value, and since neither manual says that bits 63–16 are kept, of the whole register (an
AMD Zen 4 zeroes bits 15–0 and keeps the rest). -/
def Sem.bswap (i : Inst) : Prog Ctl :=
  let w := i.opsz
  match i.ops with
  | [d] =>
    if w = 16 then do
      let v ← undefined 64
      writeOp d v
      done
    else do
      let x ← readOp w d
      writeOp d (ZellicX86.bswap x)
      done
  | _ => formNotModelled i

/-- `MOVBE d, s`: `s` with its bytes reversed, from memory to a register or from a register to
memory, 16, 32 or 64 bits (SDM Vol. 2, "MOVBE": a 16-bit register destination keeps bits 63–16).
-/
def Sem.movbe (i : Inst) : Prog Ctl :=
  let w := i.opsz
  match i.ops with
  | [d, s] => do
    let x ← readOp w s
    writeOp d (ZellicX86.bswap x)
    done
  | _ => formNotModelled i

/-- `XCHG a, b`; with a memory operand it is locked (SDM Vol. 2, "XCHG"). -/
def Sem.xchg (i : Inst) : Prog Ctl :=
  let w := i.opsz
  match i.ops with
  | [.mem x, s] | [s, .mem x] => do
    let v ← readOp w s
    let m ← memRef x
    let old ← Prog.lockedRmw m w (fun _ => v)
    writeOp s old
    done
  | [a, b] => do
    let x ← readOp w a
    let y ← readOp w b
    writeOp a y
    writeOp b x
    done
  | _ => formNotModelled i

/-- `CMPXCHG d, s`: compare the accumulator `a` (`AL`, `AX`, `EAX` or `RAX`) with `d`; if
equal, `d := s`, else `a := d`; the flags are those of `CMP a, d`. The destination is written
either way, with its own value if they differ (SDM Vol. 2, "CMPXCHG", Operation: `DEST ← TEMP`),
so a memory destination needs write access; the accumulator is written only if they differ. A
32-bit register destination that differs is zero-extended by that write per the SDM, but an AMD
Zen 4 leaves the register unchanged in hardware measurements: which of the two
happens is a `pick` (alternative 0: unchanged). With `LOCK` the memory operand is
replaced atomically (a locked read-modify-write, SDM Vol. 3A, 11.1.2). -/
def Sem.cmpxchg (i : Inst) : Prog Ctl :=
  let w := i.opsz
  match i.ops with
  | [d, s] => do
    let acc := accOf w 0
    let a ← readOp w acc
    let v ← readOp w s
    let old ← match d, i.lock with
      | .mem x, true => do
        let m ← memRef x
        Prog.lockedRmw m w fun old => if old = a then v else old
      | .reg _, _ => do
        let old ← readOp w d
        if old = a then writeOp d v
        else if w = 32 then do
          -- alternative 1: written (zero-extended); 0: unchanged
          let keep ← choice 1
          if keep.val = 1 then writeOp d old
        else writeOp d old
        Pure.pure old
      | _, _ => do
        let old ← readOp w d .write
        writeOp d (if old = a then v else old)
        Pure.pure old
    let f ← readFlags
    let (_, f') ← subOp false a old f
    writeFlags f'
    if old = a then done else do
      writeOp acc old
      done
  | _ => formNotModelled i

/-- `CMOVcc d, s`: the source is read whatever the condition; a 32-bit destination is written
(zero-extended) even when the condition is false (SDM Vol. 2, "CMOVcc"). -/
def Sem.cmovcc (c : Cond) (i : Inst) : Prog Ctl :=
  let w := i.opsz
  match i.ops with
  | [d, s] => do
    let v ← readOp w s
    let f ← readFlags
    if f.cond c then writeOp d v
    else if w = 32 then do let old ← readOp 32 d; writeOp d old
    done
  | _ => formNotModelled i

/-- `SETcc d`: the byte destination becomes 1 or 0 (SDM Vol. 2, "SETcc"). -/
def Sem.setcc (c : Cond) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d] => do
    let f ← readFlags
    writeOp d ((BitVec.ofBool (f.cond c)).setWidth 8)
    done
  | _ => formNotModelled i

/-- `PUSH s`, 64-bit only (a `66` prefix selects 16 bits, not modelled; SDM Vol. 2, "PUSH"). A memory
source is read before the push, so when both would fault the read's fault comes first: observed on an
AMD Zen 4 only; neither manual orders them. -/
def Sem.push (i : Inst) : Prog Ctl :=
  match i.ops with
  | [s] =>
    if i.opsz ≠ 64 then unmodelled (.form "push16") else do
    let v ← readOp 64 s
    push64 v
    done
  | _ => formNotModelled i

/-- `POP d`, 64-bit only (a `66` prefix selects 16 bits, not modelled; SDM Vol. 2, "POP"). The stack
is read before a memory destination is written, so when both would fault the read's fault comes
first: observed on an AMD Zen 4 only; neither manual orders them. -/
def Sem.pop (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d] =>
    if i.opsz ≠ 64 then unmodelled (.form "pop16") else do
    let v ← pop64
    writeOp d v
    done
  | _ => formNotModelled i

/-- `LEAVE`: `rsp := rbp`, then pop `rbp` (SDM Vol. 2, "LEAVE"); 64-bit only (a `66` prefix
selects 16 bits, not modelled). -/
def Sem.leave (i : Inst) : Prog Ctl :=
  if i.opsz ≠ 64 then unmodelled (.form "leave16") else do
  let bp ← readReg 5
  writeReg 4 bp
  let v ← pop64
  writeReg 5 v
  done

end ZellicX86
