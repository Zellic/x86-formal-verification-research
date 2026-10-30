import ZellicX86.Spec.Semantics.Basic
import ZellicX86.Spec.Float
import ZellicX86.Spec.Xsave
/-!
# Instruction semantics: the x87 unit

The x87 instructions (`Mn.x87`) on the x87 state (`X87`, SDM Vol. 1, chapter 8; AMD APM Vol. 1,
chapter 6), each following the "Operation" section of its page in SDM Vol. 2 and the APM's in Vol. 5;
where the two manuals differ, the case says so.

What is common to the family:

- **The register stack**: `ST(i)` is the physical register `R((TOP + i) mod 8)` (`X87.stIdx`); a
  push decrements `TOP` and fills the new `ST(0)`, a pop marks `ST(0)` empty and increments `TOP`. An
  empty register keeps its contents (`X87.full` says which are empty).
- **Waiting and non-waiting instructions** (SDM Vol. 1, 8.6 and 8.7.1; APM Vol. 1, 6.8.6): before it
  executes, every x87 instruction but `FNINIT`, `FNCLEX`, `FNSTSW`, `FNSTCW`, `FNSTENV`, `FNSAVE`,
  `FXSAVE` and `FXRSTOR` raises `#MF` if an unmasked exception is pending (`FSW.ES`, which the model
  keeps equal to "an exception flag is set whose mask bit is clear", `x87Summary`); `FWAIT` does
  nothing else (`x87Wait`).
- **Exceptions** (SDM Vol. 1, 8.5; APM Vol. 1, 6.8): an instruction's conditions set their flags in
  `FSW` (sticky). A stack fault (`#IS`: a push onto a register that is not empty, or a read of an empty
  one) sets `IE` and `SF`, and `C1` to 1 for an overflow, 0 for an underflow. If a condition is masked
  the instruction completes with the masked response (the QNaN indefinite for a stack fault or an
  invalid operand); if one of the invalid-operation, denormal-operand and divide-by-zero conditions is
  unmasked, the flags, `ES` and `B` are set and nothing else changes: "the top-of-stack pointer (TOP)
  and source operands remain unchanged" (SDM 8.5.1.1, 8.5.1.2, 8.5.2, 8.5.3; `x87Done`); the `#MF`
  comes at the next waiting instruction.
- **Condition codes** `C0`–`C3`: as each instruction's page says; where either manual leaves one
  undefined, the model leaves it undefined.
- **The last-instruction state** (`x87Last`): every non-control instruction records its address in
  `FIP` and, on AMD, its opcode in `FOP` (on Intel only with an unmasked exception), and its memory
  operand's offset in `FDP`. The control instructions (`FNINIT`, `FNCLEX`, `FLDCW`, `FNSTCW`,
  `FNSTSW`, `FNSTENV`, `FLDENV`, `FNSAVE`, `FRSTOR`, `FWAIT`, `FXSAVE`, `FXRSTOR`) do not record
  themselves there: `FNINIT` and `FNSAVE` clear these fields, `FLDENV`, `FRSTOR` and `FXRSTOR` load
  them, and the others leave them as `x87SeenPtrs` describes (SDM Vol. 1, 8.1.8; APM Vol. 1, 6.4.9).
- **Operands**: as in the SDM's "Instruction" column (`Mb n` a memory operand of `n` bytes).
-/
namespace ZellicX86
open Decode Prog

/-! ## The register stack and the status word -/

/-- `TOP`, bits 13–11 of the status word: the physical register that is `ST(0)` (SDM Vol. 1, 8.1.2,
8.1.3; APM Vol. 1, 6.2.1, 6.2.2). -/
def X87.top (x : X87) : Nat := (x.fsw >>> 11).toNat % 8

/-- The contents of `ST(i)`. -/
def X87.get (x : X87) (i : Nat) : BitVec 80 := x.st (X87.stIdx x.fsw i)

/-- Whether `ST(i)` is empty (SDM Vol. 1, 8.1.7; APM Vol. 1, 6.2.4). -/
def X87.isEmpty (x : X87) (i : Nat) : Bool := !x.full.getLsbD (X87.stIdx x.fsw i).val

/-- `x` with `ST(i)` holding `v`, not empty. -/
def X87.put (x : X87) (i : Nat) (v : BitVec 80) : X87 :=
  let j := X87.stIdx x.fsw i
  { x with st := fun k => if k = j then v else x.st k, full := x.full ||| ((1 : BitVec 8) <<< j.val) }

/-- `x` with `ST(i)` empty; its contents stay. -/
def X87.free (x : X87) (i : Nat) : X87 :=
  { x with full := x.full &&& ~~~((1 : BitVec 8) <<< (X87.stIdx x.fsw i).val) }

/-- `x` with `TOP` set to `t` modulo 8. -/
def X87.withTop (x : X87) (t : Nat) : X87 :=
  { x with fsw := (x.fsw &&& ~~~0x3800) ||| BitVec.ofNat 16 (t % 8 * 2048) }

/-- Push `v`: `TOP` decremented, then `ST(0)` holding `v` (SDM Vol. 1, 8.1.2). -/
def X87.push (x : X87) (v : BitVec 80) : X87 := (x.withTop (x.top + 7)).put 0 v

/-- Pop: `ST(0)` marked empty, then `TOP` incremented ("the processor marks the ST(0) register as
empty and increments the stack pointer (TOP) by 1", SDM Vol. 2, "FSTP"). -/
def X87.pop (x : X87) : X87 := (x.free 0).withTop (x.top + 1)

/-- What an instruction does to one of the condition codes `C0`–`C3`: keeps it, sets it to `b`, or
leaves it undefined. -/
inductive CCode
  | keep
  | set (b : Bool)
  | undef

/-- `x` with the condition codes `C0`, `C1`, `C2`, `C3` (status word bits 8, 9, 10, 14; SDM Vol. 1,
8.1.3.2; APM Vol. 1, 6.2.2) as `c0`, `c1`, `c2`, `c3` say. -/
def X87.codes (x : X87) (c0 c1 c2 c3 : CCode) : Prog X87 := do
  let bit (c : CCode) (n : Nat) : Prog (BitVec 16) := match c with
    | .keep => Pure.pure (x.fsw &&& (1 <<< n))
    | .set b => Pure.pure (if b then 1 <<< n else 0)
    | .undef => do let b ← undefinedBit; Pure.pure (if b then 1 <<< n else 0)
  let b0 ← bit c0 8
  let b1 ← bit c1 9
  let b2 ← bit c2 10
  let b3 ← bit c3 14
  Pure.pure { x with fsw := (x.fsw &&& ~~~0x4700) ||| b0 ||| b1 ||| b2 ||| b3 }

/-- `x` with `C0`–`C3` undefined: the instructions whose pages say so for all four (`FLDCW`, `FNSTCW`,
`FNSTSW`, `FNSTENV`, `FNCLEX`, `FWAIT`, `FFREE`, `FNOP`: SDM Vol. 2 and APM Vol. 5, "x87 Condition
Code"). -/
def X87.codesUndef (x : X87) : Prog X87 := x.codes .undef .undef .undef .undef

/-- `x` with the exception conditions `fl` and, with `sf`, a stack fault recorded in the status word:
their flags set (bits 5–0; `SF`, bit 6), and `ES` and `B` from the flags and the masks
(`x87Summary`; SDM Vol. 1, 8.1.3.3–8.1.3.4; APM Vol. 1, 6.2.2). -/
def X87.report (x : X87) (fl : FFlags) (sf : Bool) : X87 :=
  { x with fsw := x87Summary x.fcw (x.fsw ||| BitVec.ofNat 16 (fl.bits + if sf then 64 else 0)) }

/-- Whether one of the conditions `fl` is unmasked: its mask bit in `FCW` (bits 5–0) is clear. -/
def X87.unmasked (x : X87) (fl : FFlags) : Bool := fl.bits &&& (63 - x.fcw.toNat % 64) != 0

/-! ## Waiting, operands, the last-instruction state -/

/-- Check the endpoints of an x87 environment/state image of `size` bytes (`FNSTENV`, `FLDENV`,
`FNSAVE`, `FRSTOR`, `FXSAVE`, `FXRSTOR`) before any data access. These images span at most two pages:
a fault on the first page reports the first byte, and a fault only on the second reports the last.
SDM Vol. 3A, 7.15, Event 14 and APM Vol. 2, 8.2.15 specify CR2 as the faulting linear address but
leave the byte of a multi-byte access unspecified. This endpoint rule is measured on AMD Zen 4, including
images beginning on an inaccessible page; it is not
measured on Intel. The caller still reads/writes the image after this check. -/
def x87Area (m : MemRef) (acc : Access) (size : Nat) : Prog Unit := do
  checkAccesses [(m, acc, 1)]
  checkAccesses [(⟨m.addr + BitVec.ofNat 64 (size - 1), m.stack⟩, acc, 1)]

/-- The check a waiting x87 instruction makes before it executes: `#MF` if an unmasked exception is
pending (`FSW.ES`; SDM Vol. 1, 8.6, 8.7.1; APM Vol. 1, 6.8.6.2; Vol. 2, 8.2.16), else the x87 state.
With a memory operand whose access `a` would fault, which of the two the processor reports is not
specified (SDM Vol. 3A, 7.9, Table 7-2: both are "faults on executing an instruction", class 10;
APM Vol. 2, 8.5, Table 8-9: both priority 7): a `pick`. `image` selects the endpoint
check (`x87Area`) for an environment/state image, including this competing fault. -/
def x87Wait (a : Option (MemRef × Access × Nat)) (image : Bool := false) : Prog X87 := do
  let x ← readX87
  if x.fsw.getLsbD 7 then
    match a with
    | none => throw .mf
    | some acc => do
      let i ← choice 1
      if i.val = 1 then
        if image then x87Area acc.1 acc.2.1 acc.2.2 else checkAccesses [acc]
      throw .mf
  else Pure.pure x

/-- The memory reference and the offset (the effective address, `effOffset`) of operand `o`, if it is
a memory operand. -/
def x87Mem (o : Opd) : Prog (Option (MemRef × Addr)) :=
  match o with
  | .mem m => do
    let r ← memRef m
    let off ← effOffset m
    Pure.pure (some (r, off))
  | _ => Pure.pure none

/-- The first memory operand of `i`, if any. -/
def x87MemOpd (i : Inst) : Option Opd := i.ops.find? fun o => o matches .mem _

/-- The start of a waiting x87 instruction `i` whose memory operand, if any, is accessed as `acc`:
`x87Wait`, and the instruction's address (`rip` is already past it) and its memory operand's
reference and offset. `image` selects `x87Area` for a competing memory fault. -/
def x87Begin (i : Inst) (acc : Access) (image : Bool := false) :
    Prog (X87 × Addr × Option (MemRef × Addr)) := do
  let next ← readRip
  let mem ← match x87MemOpd i with
    | some o => x87Mem o
    | none => Pure.pure none
  let a := match mem, x87MemOpd i with
    | some (r, _), some o => some (r, acc, o.width / 8)
    | _, _ => none
  let x ← x87Wait a image
  Pure.pure (x, next - BitVec.ofNat 64 i.len, mem)

/-- The last-instruction state after the non-control instruction `i` at address `ip`, whose memory
operand, if any, has offset `dp`, and which incurred an unmasked exception if `unm`:
- `FIP` is `ip` (the instruction's first prefix; SDM Vol. 1, 8.1.8; APM Vol. 1, 6.2.5.1);
- `FOP` is the instruction's opcode (`Inst.fop`): on an AMD processor always (APM Vol. 1, 6.2.5.2),
  on an Intel processor only with an unmasked exception (SDM Vol. 1, 8.1.9);
- `FDP` is `dp`, the operand's offset ("the 64-bit offset of the last memory operand", APM Vol. 1,
  6.2.5.3); without a memory operand it is undefined ("undefined (reserved)", SDM 8.1.8; "implementation
  dependent", APM Vol. 2, 11.4.4); on an Intel processor with `Profile.fdpExcptnOnly` it is unchanged
  unless the exception is unmasked. -/
def x87Last (prof : Profile) (i : Inst) (ip : Addr) (dp : Option Addr) (unm : Bool) (x : X87) :
    Prog X87 := do
  let fop := if prof.vendor = .amd || unm then BitVec.ofNat 11 i.fop else x.fop
  let fdp ← if prof.vendor = .intel && prof.fdpExcptnOnly && !unm then Pure.pure x.fdp else
    match dp with
    | some a => Pure.pure a
    | none => undefined 64
  Pure.pure { x with fip := ip, fop := fop, fdp := fdp }

/-- The end of a non-control x87 instruction `i` (at `ip`, memory operand offset `dp`) on state `x`
that detected the conditions `fl` and, if `sf = some c1`, a stack fault with `C1 = c1`. If one of the
conditions `stops` (by default all of `fl`) is unmasked, the flags of the pre-computation conditions
(invalid operation, denormal operand, divide by zero) and of those of `stops` that come after them
(an overflow or underflow of a store to memory), `ES` and `B` and the stack fault's `C1` are set,
`held` sets the other condition codes, and nothing else changes: "the destination and the TOP are not
changed" (SDM Vol. 1, 8.5.1–8.5.5; APM Vol. 1, 6.8.6.2, Table 6-22); the result's other conditions
are not reported, there being none (as for SSE, SDM Vol. 1, 11.5.3; an AMD Zen 4 agrees). Otherwise `act`
gives the result (its stores and the new state, condition codes included), and the flags (with `ES`
and `B` if one is unmasked) are set on it. -/
def x87Done (prof : Profile) (i : Inst) (ip : Addr) (dp : Option Addr) (x : X87) (fl : FFlags)
    (sf : Option Bool) (held : X87 → Prog X87) (act : X87 → Prog X87) (stops : FFlags := fl) :
    Prog Ctl := do
  let x' ← if x.unmasked stops then do
      let x' ← held (x.report (fl.pre.or stops.post) sf.isSome)
      match sf with
      | some c => x'.codes .keep (.set c) .keep .keep
      | none => Pure.pure x'
    else do
      let x' ← act x
      Pure.pure (x'.report fl sf.isSome)
  writeX87 (← x87Last prof i ip dp (x.unmasked fl) x')
  done

/-- What an instruction whose `C0`, `C2`, `C3` are undefined leaves in them when an unmasked exception
stops it (`x87Done`). -/
def X87.heldUndef (x : X87) : Prog X87 := x.codes .undef .keep .undef .undef

/-- A stack overflow: pushing onto `x` would overwrite a register that is not empty (`ST(7)`; SDM
Vol. 1, 8.5.1.1). -/
def X87.overflows (x : X87) : Bool := !x.isEmpty 7

/-- The last-instruction state (`FOP`, `FIP`, `FDP`) of `x` as seen by an instruction that stores it
(`FNSTENV`, `FNSAVE`) or makes an exception pending (`FLDCW`); the state keeps what it sees from then on.
On an AMD processor with no exception pending (`FSW.ES` clear), the kernel may have saved and restored
the x87 state since the last non-control instruction (at any context switch), and such a save does not
keep these fields. With `Profile.amdErrPtrs` it stores them as 0, which the restore loads (APM Vol. 2,
11.5.10). Without it, the kernel overwrites them with an `FILD` of its own
(`restore_fpregs_from_fpstate`, `arch/x86/kernel/fpu/core.c`: "AMD K7/K8 and later CPUs up to Zen
don't save/restore FDP/FIP/FOP unless an exception is pending"), so they are undefined to the process.
Whether the process sees the recorded values or the replaced ones is a `pick`. An Intel processor's
`XSAVE` keeps them. -/
def x87SeenPtrs (prof : Profile) (x : X87) : Prog X87 := do
  if prof.vendor = .amd && !x.fsw.getLsbD 7 then
    let i ← choice 1
    if i.val = 0 then Pure.pure x
    else if prof.amdErrPtrs then Pure.pure { x with fop := 0, fip := 0, fdp := 0 }
    else do
      let fop ← undefined 11
      let fip ← undefined 64
      let fdp ← undefined 64
      Pure.pure { x with fop := fop, fip := fip, fdp := fdp }
  else Pure.pure x

/-! ## Values -/

/-- The datum an 80-bit register value encodes (`extDecode`; `none`: an unsupported encoding). -/
def extNum (v : BitVec 80) : Option FNum := extDecode v.toNat

/-- The 80-bit register value of a datum the double extended format represents (`extEncode`). -/
def extBits (x : FNum) : BitVec 80 := BitVec.ofNat 80 (extEncode x)

/-- The datum `a` of a single or double precision operand (format `f`) as a datum of the double extended
format: the same value, every value of these formats being one of the double extended format; a NaN keeps its
sign and quiet bit, and its fraction goes to the high bits of the wider fraction, which `extStore` truncates
back. The manuals do not say where the narrower fraction goes; an AMD Zen 4 puts it there in hardware
measurements with NaN payloads loaded by `FLD` and used by the arithmetic. -/
def FFormat.widen (f : FFormat) (a : FNum) : FNum :=
  match a with
  | .nan neg q p => .nan neg q (mulPow2 p (62 - (f.fbits - 1 : Nat)))
  | a => a

/-- The value `v` (`m` bits) of a single or double precision memory operand (format `f`) as an 80-bit
register value (`FFormat.widen`): exact (SDM Vol. 2, "FLD": "converts it to the double extended-precision
floating-point format"; APM Vol. 5, "FLD"); a denormal is normalized (SDM Vol. 1, 8.5.2), a signaling NaN
made quiet, with the invalid-operation condition (SDM Vol. 1, Table 8-10: "Any arithmetic operation on a
SNaN"; APM Vol. 5, "FLD": "A source operand was an SNaN value"). The second component: the conditions
(invalid operation for a signaling NaN, denormal operand for a denormal). -/
def extOfFormat (f : FFormat) (v : Nat) : BitVec 80 × FFlags :=
  match f.widen (f.decode v) with
  | .nan neg q p => (extBits (.nan neg true p), { ie := !q })
  | a => (extBits a, { de := f.isDenormal v })

/-- The integer `n` as a datum, exactly; `+0` for 0 (SDM Vol. 2, "FILD"; APM Vol. 5, "FILD"). -/
def FNum.ofInt (n : Int) : FNum := if n = 0 then .zero false else .finite (n < 0) n.natAbs 0

/-- The 80-bit register value of the integer `n` (`FNum.ofInt`). -/
def extOfInt (n : Int) : BitVec 80 := extBits (FNum.ofInt n)

/-- `+1.0` in double extended precision. -/
def extOne : BitVec 80 := 0x3FFF8000000000000000

/-! ## Comparisons and classification -/

/-- The comparison of `a` with `b` (each `none` when empty) by an x87 compare instruction, `unord` for
the unordered forms (`FUCOM`, `FUCOMI`): the relation, the stack fault (an empty operand: underflow,
`C1 = 0`) and the conditions. An empty operand compares as the indefinite would; an unsupported
encoding or a signaling NaN is an invalid operand, and so is a quiet NaN for the ordered forms; either
compares unordered (SDM Vol. 2, "FCOM/FCOMP/FCOMPP", "FUCOM/FUCOMP/FUCOMPP", "FCOMI/FCOMIP/FUCOMI/
FUCOMIP"; Vol. 1, Table 8-10; APM Vol. 5, "FCOM", "FUCOM", "FCOMI", "FUCOMI"). A denormal or
pseudo-denormal operand (`aden`, `bden`) adds the denormal-operand condition unless a NaN or an invalid
operand does (`FFlags.withDenormal`). -/
def x87Compare (unord : Bool) (a b : Option (Option FNum)) (aden bden : Bool) :
    FOrder × Option Bool × FFlags :=
  match a, b with
  | some (some a), some (some b) =>
    let nan := a.isNaN || b.isNaN
    let ie := a.isSNaN || b.isSNaN || (nan && !unord)
    (fcompare a b, none, ({ ie } : FFlags).withDenormal nan (aden || bden))
  | some none, some _ | some _, some none => (.unordered, none, { ie := true })
  | _, _ => (.unordered, some false, { ie := true })

/-- The condition codes `C3 C2 C0` of a comparison's relation (SDM Vol. 2, "FCOM/FCOMP/FCOMPP", Table 3-23:
greater 000, less 001, equal 100, unordered 111); the same bits are `ZF PF CF` for `FCOMI`. -/
def FOrder.codes : FOrder → Bool × Bool × Bool
  | .gt => (false, false, false)
  | .lt => (false, false, true)
  | .eq => (true, false, false)
  | .unordered => (true, true, true)

/-- `FXAM`'s class of `ST(0)` as `C3 C2 C0` (SDM Vol. 2, "FXAM", Table 3-44; APM Vol. 5, "FXAM"):
unsupported 000, NaN 001, normal 010, infinity 011, zero 100, empty 101, denormal (also a
pseudo-denormal) 110. -/
def fxamClass (empty : Bool) (v : BitVec 80) : Bool × Bool × Bool :=
  if empty then (true, false, true)
  else match extNum v with
    | none => (false, false, false)
    | some (.nan ..) => (false, false, true)
    | some (.inf _) => (false, true, true)
    | some (.zero _) => (true, false, false)
    | some (.finite ..) => if extIsDenormal v.toNat then (true, true, false) else (false, true, false)

/-! ## Control instructions -/

/-- `FNSTCW m16`: store `FCW`; `C0`–`C3` undefined (SDM Vol. 2, "FSTCW/FNSTCW"; APM Vol. 5,
"FSTCW/FNSTCW"). Non-waiting. -/
def Sem.fnstcw (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d] => do
    let x ← readX87
    writeOp d x.fcw
    writeX87 (← x.codesUndef)
    done
  | _ => formNotModelled i

/-- `FNSTSW m16` and `FNSTSW AX`: store `FSW`; `C0`–`C3` undefined afterwards (SDM Vol. 2,
"FSTSW/FNSTSW"; APM Vol. 5, "FSTSW/FNSTSW"). Non-waiting. -/
def Sem.fnstsw (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d] => do
    let x ← readX87
    writeOp d x.fsw
    writeX87 (← x.codesUndef)
    done
  | _ => formNotModelled i

/-- `FLDCW m16`: load `FCW`, its reserved bits as `x87Fcw` gives them (not modelled on Intel where
that is not known, `x87FcwKnown`); `ES` and `B` follow the new masks (an exception the new word
unmasks is pending, "generated upon execution of the next floating-point instruction", SDM Vol. 2,
"FLDCW"; APM Vol. 5, "FLDCW"), with the pointers as `x87SeenPtrs` finds them when one becomes
pending; `C0`–`C3` undefined. Waiting. -/
def Sem.fldcw (prof : Profile) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [s] => do
    let (x, _, _) ← x87Begin i .read
    let v ← readOp 16 s
    if !x87FcwKnown prof v then unmodelled (.feature "FLDCW: reserved FCW bits on Intel") else do
    let fcw := x87Fcw v
    let fsw := x87Summary fcw x.fsw
    -- an exception the new masks make pending keeps the pointers the instruction finds
    let x ← if fsw.getLsbD 7 then x87SeenPtrs prof x else Pure.pure x
    writeX87 (← ({ x with fcw := fcw, fsw := fsw } : X87).codesUndef)
    done
  | _ => formNotModelled i

/-- `FNCLEX`: clear the exception flags, `SF`, `ES` and `B`; `C0`–`C3` undefined (SDM Vol. 2,
"FCLEX/FNCLEX"; APM Vol. 5, "FCLEX/FNCLEX"). Non-waiting. -/
def Sem.fnclex (_ : Inst) : Prog Ctl := do
  let x ← readX87
  writeX87 (← ({ x with fsw := x.fsw &&& 0x7F00 } : X87).codesUndef)
  done

/-- `FNINIT`: `FCW` `037FH`, `FSW` 0 (so `TOP` and `C0`–`C3` 0), every register empty with its
contents unchanged, `FOP`, `FIP`, `FDP` 0 (SDM Vol. 2, "FINIT/FNINIT"; APM Vol. 1, 6.4.9). Non-waiting. -/
def Sem.fninit (_ : Inst) : Prog Ctl := do
  let x ← readX87
  writeX87 { x with fcw := 0x37F, fsw := 0, full := 0, fop := 0, fip := 0, fdp := 0 }
  done

/-- `WAIT`/`FWAIT`: `#MF` if an exception is pending (`x87Wait`); `C0`–`C3` undefined (SDM Vol. 2,
"WAIT/FWAIT"; APM Vol. 5, "FWAIT"). -/
def Sem.fwait (_ : Inst) : Prog Ctl := do
  let x ← x87Wait none
  writeX87 (← x.codesUndef)
  done

/-- The 28-byte environment image `FNSTENV` stores in 64-bit mode with a 32- or 64-bit operand size
(the 32-bit protected-mode format, SDM Vol. 1, 8.1.10, Figure 8-9; APM Vol. 2, 11.4.4): `FCW` at 0,
`FSW` at 4, the full tag word at 8 (`x87TagsFrom`), `FIP` bits 31–0 at 12, the code selector `FCS`
at 16, `FOP` in bits 26–16 of the doubleword at 16 (bits 31–27 zero), `FDP` bits 31–0 at 20, the data
selector `FDS` at 24. The upper halves of the doublewords at 0, 4, 8 and 24 are reserved: their values
come from `rsv`. So do `FCS` and `FDS`: the selectors of the last instruction and operand, which the
model does not hold. On an Intel processor that deprecates them (`Profile.zeroesSelectors`) they are
stored as 0 (SDM 8.1.8); otherwise they are whatever the processor last recorded, and every `XRSTOR` with
`REX.W`, which the kernel executes at each context switch and signal return, clears them (SDM 8.1.8),
so the process cannot know them. -/
def x87EnvImage (prof : Profile) (x : X87) (rsv : BitVec 96) : List Byte :=
  let sel : BitVec 32 := if prof.zeroesSelectors then 0 else rsv.extractLsb' 64 32
  let half (k : Nat) : List Byte := toBytesLE (rsv.extractLsb' (16 * k) 16) 2
  toBytesLE x.fcw 2 ++ half 0 ++ toBytesLE x.fsw 2 ++ half 1 ++ toBytesLE (x87TagsFrom x.full x.st) 2 ++
    half 2 ++ toBytesLE x.fip 4 ++ toBytesLE sel 2 ++ toBytesLE x.fop 2 ++ toBytesLE x.fdp 4 ++
    toBytesLE (sel >>> 16) 2 ++ half 3

/-- `FNSTENV m28`: store the environment (`x87EnvImage`) with the pointers as `x87SeenPtrs` finds them,
which the state keeps from then on, so a later store cannot see again pointers the kernel has cleared.
Then mask every exception: `FCW` bits 5–0 set, so nothing is pending (SDM Vol. 2, "FSTENV/FNSTENV":
"Then mask all floating-point exceptions"; APM Vol. 5, "FSTENV/FNSTENV"). `C0`–`C3` undefined.
Non-waiting. The 16-bit operand size (the 14-byte format) is not modelled. The access is checked by
`x87Area`. -/
def Sem.fnstenv (prof : Profile) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [.mem mo] => do
    let m ← memRef mo
    x87Area m .write 28
    let x ← readX87
    let seen ← x87SeenPtrs prof x
    let rsv ← undefined 96
    write m 224 (ofBytesLE 224 (x87EnvImage prof seen rsv))
    let fcw := x.fcw ||| 0x3F
    writeX87 (← ({ seen with fcw := fcw, fsw := x87Summary fcw x.fsw } : X87).codesUndef)
    done
  | _ => formNotModelled i

/-- The x87 state `x` with the environment loaded from the 28-byte image `img` that `FNSTENV` stores
(`x87EnvImage`), by the instruction `what` (`FLDENV`, `FRSTOR`): `FCW` (`x87Fcw`, and not modelled on
Intel where its reserved bits are not known, `x87FcwKnown`), `FSW` (`C0`–`C3` included), which
registers are empty (tag 3 in the tag word, the other tags are not used), `FIP` and `FDP` from their
low 32 bits with the upper 32 bits cleared, `FOP`; the selectors are not used (SDM Vol. 1, 8.1.8; Vol.
2, "FLDENV", "FRSTOR"; APM Vol. 5, "FLDENV", "FRSTOR"). `ES` and `B` as for `XRSTOR`: computed on AMD,
and a loaded `FSW` whose `ES`/`B` disagree with its flags not modelled on Intel (`x87SummaryKnown`). -/
def x87LoadEnv (prof : Profile) (what : String) (x : X87) (img : BitVec 224) : Prog X87 :=
  let rd (o : Nat) : Byte := img.extractLsb' (8 * o) 8
  let fcw := x87Fcw (img.extractLsb' 0 16)
  let fsw : BitVec 16 := img.extractLsb' 32 16
  let tags : BitVec 16 := img.extractLsb' 64 16
  if !x87SummaryKnown prof fun o => rd (if o < 2 then o else o + 2) then
    unmodelled (.feature s!"{what}: FSW.ES/B on Intel")
  else if !x87FcwKnown prof (img.extractLsb' 0 16) then
    unmodelled (.feature s!"{what}: reserved FCW bits on Intel")
  else
    Pure.pure
      { x with
        fcw := fcw
        fsw := x87Summary fcw fsw
        full := ofBits 8 (fun j => (tags >>> (2 * j)).setWidth 2 != 3)
        fip := (img.extractLsb' 96 32).setWidth 64
        fop := img.extractLsb' 144 11
        fdp := (img.extractLsb' 160 32).setWidth 64 }

/-- `FLDENV m28`: load the environment from the 28-byte image `FNSTENV` stores (`x87LoadEnv`). An
exception the loaded words leave pending is raised at the next waiting instruction. Waiting. The
access is checked by `x87Area`; the 16-bit operand size (14-byte format) is not modelled. -/
def Sem.fldenv (prof : Profile) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [.mem mo] => do
    let (x, _, _) ← x87Begin i .read true
    let m ← memRef mo
    x87Area m .read 28
    let img : BitVec 224 ← read m 224
    writeX87 (← x87LoadEnv prof "FLDENV" x img)
    done
  | _ => formNotModelled i

/-- `FXSAVE m512` (`REX.W`: `FXSAVE64`): store the x87 and SSE state in the 512-byte area's legacy
layout (`xsaveRuns` for the x87 and SSE components; SDM Vol. 2, "FXSAVE", Tables 3-48 and 3-49; APM
Vol. 5, "FXSAVE"): `#GP(0)` unless the area is 16-byte aligned (`#GP` and a fault of the access are not
ordered, `Op.checkAligned`), then the area's access (`x87Area`). Without `REX.W` the pointers are stored
as their low 32 bits with the selectors `FCS` and `FDS` beside them (`x87EnvImage` says why those are
undefined). The reserved bytes the layout leaves in the x87 part are undefined (an AMD Zen 4 writes
zeros); bytes 416–511 are not written (SDM Vol. 2, "FXSAVE": "Bytes 464:511 are available to software
use. The processor does not write to bytes 464:511"; bytes 416–463 are reserved, Tables 3-48 and 3-49,
and an AMD Zen 4 leaves them unwritten too). Non-waiting. -/
def Sem.fxsave (prof : Profile) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [.mem mo] => do
    let m ← memRef mo
    alignedTo m 16 .write 512 false
    x87Area m .write 512
    let x ← readX87
    let mx ← readMxcsr
    let xmm ← (List.range 16).mapM fun j => readZmm (xmmOf j)
    let rsv : BitVec 3328 ← undefined 3328
    let runs := xsaveRuns prof x ⟨fun j => xmm.getD j.val 0, fun _ => 0, mx⟩ 0 3 rsv (i.opsz = 64)
    let byteAt (o : Nat) : Byte :=
      (runs.findSome? fun (p, bs) => if p ≤ o then bs[o - p]? else none).getD (byteOf rsv o)
    write m 3328 (ofBytesLE 3328 ((List.range 416).map byteAt))
    done
  | _ => formNotModelled i

/-- `FXRSTOR m512` (`REX.W`: `FXRSTOR64`): `#GP(0)` unless the area is 16-byte aligned, the area's
access as `x87Area` says, then load the x87 and SSE state from it as `fxrstor` says (SDM Vol. 2,
"FXRSTOR"; APM Vol. 5, "FXRSTOR"). Bytes 0–415 are used. Non-waiting. -/
def Sem.fxrstor (prof : Profile) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [.mem mo] => do
    let m ← memRef mo
    alignedTo m 16 .read 512 false
    x87Area m .read 512
    let img : BitVec 3328 ← read m 3328
    let x ← readX87
    let mx ← readMxcsr
    let xmm ← (List.range 16).mapM fun j => readZmm (xmmOf j)
    match ZellicX86.fxrstor prof x ⟨fun j => xmm.getD j.val 0, fun _ => 0, mx⟩ (fun o => img.extractLsb' (8 * o) 8)
        (i.opsz = 64) with
    | .gp => throw (.gp 0)
    | .notModelled w => unmodelled (.feature w)
    | .ok (x', v') => do
      writeX87 x'
      writeMxcsr v'.mxcsr
      for j in List.range 16 do
        writeZmm (xmmOf j) (v'.zmm (xmmOf j))
      done
  | _ => formNotModelled i

/-! ## Loads, stores and moves between registers -/

/-- Push `v` with the stack-overflow check (`FLD`, `FILD`, the constants): if `ST(7)` is not empty,
a stack overflow (`C1 = 1`), whose masked response pushes the QNaN indefinite instead (SDM Vol. 1,
8.5.1.1); otherwise `C1 = 0`. The conditions `fl` (of reading the operand) come with it; an unmasked
denormal-operand condition stops the load on an Intel processor (SDM Vol. 1, 8.5.2: "The top-of-stack
pointer (TOP) and source operands remain unchanged"), but not on an AMD processor, which loads the
normalized value (measured on an AMD Zen 4; the APM's Table 6-22 says the TOP is not changed).
`C0`, `C2`, `C3` undefined (SDM Vol. 2, "FLD", "FILD", "FLD1/.../FLDZ": "C1 Set to 1 if stack overflow
occurred; otherwise, set to 0"; APM Vol. 5, "FLD"). -/
def x87Push (prof : Profile) (i : Inst) (ip : Addr) (dp : Option Addr) (x : X87) (v : BitVec 80)
    (fl : FFlags) : Prog Ctl :=
  if x.overflows then
    x87Done prof i ip dp x { fl with ie := true } (some true) X87.heldUndef fun x =>
      (x.push extIndefinite).codes .undef (.set true) .undef .undef
  else
    x87Done prof i ip dp x fl none X87.heldUndef
      (fun x => (x.push v).codes .undef (.set false) .undef .undef)
      (if prof.vendor = .amd then { fl with de := false } else fl)

/-- `FLD`: push a value (SDM Vol. 2, "FLD"; APM Vol. 5, "FLD"). From `ST(i)` (read before the push; an
empty one is a stack underflow whose masked response pushes the QNaN indefinite) and from an 80-bit
memory operand the bits are pushed as they are (non-arithmetic, SDM Vol. 1, Table 8-9); a single or
double precision operand is converted exactly (`extOfFormat`: a signaling NaN is an invalid operand,
a denormal a denormal operand). -/
def Sem.fld (prof : Profile) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [.st k] => do
    let (x, ip, _) ← x87Begin i .read
    if x.isEmpty k then
      if x.overflows then
        x87Done prof i ip none x { ie := true } (some true) X87.heldUndef fun x =>
          (x.push extIndefinite).codes .undef (.set true) .undef .undef
      else
        x87Done prof i ip none x { ie := true } (some false) X87.heldUndef fun x =>
          (x.push extIndefinite).codes .undef (.set false) .undef .undef
    else x87Push prof i ip none x (x.get k) {}
  | [s] => do
    let (x, ip, mem) ← x87Begin i .read
    let dp := mem.map (·.2)
    match s.width with
    | 80 => do let v ← readOp 80 s; x87Push prof i ip dp x v {}
    | 32 => do
      let v ← readOp 32 s
      let (r, fl) := extOfFormat binary32 v.toNat
      x87Push prof i ip dp x r fl
    | 64 => do
      let v ← readOp 64 s
      let (r, fl) := extOfFormat binary64 v.toNat
      x87Push prof i ip dp x r fl
    | _ => formNotModelled i
  | _ => formNotModelled i

/-- `FILD`: push a 16-, 32- or 64-bit signed integer, converted exactly (`extOfInt`; SDM Vol. 2, "FILD";
APM Vol. 5, "FILD"). -/
def Sem.fild (prof : Profile) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [s] => do
    let (x, ip, mem) ← x87Begin i .read
    let w := s.width
    let v ← readOp w s
    x87Push prof i ip (mem.map (·.2)) x (extOfInt v.toInt) {}
  | _ => formNotModelled i

/-- `FLDZ` and `FLD1`: push `+0.0` or `+1.0` (SDM Vol. 2, "FLD1/FLDL2T/FLDL2E/FLDPI/FLDLG2/FLDLN2/FLDZ";
APM Vol. 5, "FLD1", "FLDZ"); exact, so `FCW.RC` does not matter. -/
def Sem.fldConst (prof : Profile) (v : BitVec 80) (i : Inst) : Prog Ctl := do
  let (x, ip, _) ← x87Begin i .read
  x87Push prof i ip none x v {}

/-- `FST ST(i)`, `FSTP ST(i)` and `FSTP m80`: copy `ST(0)`'s bits, then pop for `FSTP` (non-arithmetic:
no exception for a NaN; SDM Vol. 2, "FST/FSTP"; Vol. 1, Table 8-9; APM Vol. 5, "FST", "FSTP"). An empty
`ST(0)` is a stack underflow whose masked response stores the QNaN indefinite. `C1 = 0`; `C0`, `C2`,
`C3` undefined. Stores to a single or double precision memory operand round; they are `Sem.fstm`. -/
def Sem.fst (prof : Profile) (pop : Bool) (i : Inst) : Prog Ctl :=
  let fin (x : X87) : Prog X87 := (if pop then x.pop else x).codes .undef (.set false) .undef .undef
  match i.ops with
  | [.st k] => do
    let (x, ip, _) ← x87Begin i .read
    if x.isEmpty 0 then
      x87Done prof i ip none x { ie := true } (some false) X87.heldUndef fun x => fin (x.put k extIndefinite)
    else x87Done prof i ip none x {} none X87.heldUndef fun x => fin (x.put k (x.get 0))
  | [d] =>
    if d.width = 80 then do
      let (x, ip, mem) ← x87Begin i .write
      let dp := mem.map (·.2)
      if x.isEmpty 0 then
        x87Done prof i ip dp x { ie := true } (some false) X87.heldUndef fun x => do
          writeOp d extIndefinite
          fin x
      else
        x87Done prof i ip dp x {} none X87.heldUndef fun x => do
          writeOp d (x.get 0)
          fin x
    else formNotModelled i
  | _ => formNotModelled i

/-- `FXCH ST(i)`: exchange `ST(0)` and `ST(i)`. An empty one is a stack underflow, whose masked
response loads the empty ones with the QNaN indefinite before the exchange (SDM Vol. 1, Table 8-10;
Vol. 2, "FXCH"; APM Vol. 5, "FXCH"). `C1 = 0`; `C0`, `C2`, `C3` undefined. -/
def Sem.fxch (prof : Profile) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [.st k] => do
    let (x, ip, _) ← x87Begin i .read
    let swap (x : X87) : Prog X87 := do
      let a := x.get 0
      let b := x.get k
      ((x.put 0 b).put k a).codes .undef (.set false) .undef .undef
    if x.isEmpty 0 || x.isEmpty k then
      x87Done prof i ip none x { ie := true } (some false) X87.heldUndef fun x =>
        let x := if x.isEmpty 0 then x.put 0 extIndefinite else x
        swap (if x.isEmpty k then x.put k extIndefinite else x)
    else x87Done prof i ip none x {} none X87.heldUndef swap
  | _ => formNotModelled i

/-- `FCMOVcc ST(0), ST(i)`: copy `ST(i)` to `ST(0)` if the `RFLAGS` condition `c` holds (the
condition codes of `Jcc`: `B`, `E`, `BE`, `P` (`FCMOVU`) and their negations; SDM Vol. 2, "FCMOVcc"; APM Vol. 5,
"FCMOVcc"). An empty `ST(0)` or `ST(i)` is a stack underflow (`C1 = 0`), whose masked response puts
the QNaN indefinite in `ST(0)`; without one, `C1` is undefined, as are `C0`, `C2`, `C3`. -/
def Sem.fcmov (prof : Profile) (c : Cond) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [_, .st k] => do
    let (x, ip, _) ← x87Begin i .read
    let f ← readFlags
    if x.isEmpty 0 || x.isEmpty k then
      x87Done prof i ip none x { ie := true } (some false) X87.heldUndef fun x =>
        (x.put 0 extIndefinite).codes .undef (.set false) .undef .undef
    else
      x87Done prof i ip none x {} none X87.heldUndef fun x =>
        (if f.cond c then x.put 0 (x.get k) else x).codesUndef
  | _ => formNotModelled i

/-- `FFREE ST(i)`: mark `ST(i)` empty; `C0`–`C3` undefined (SDM Vol. 2, "FFREE"; APM Vol. 5, "FFREE"). -/
def Sem.ffree (prof : Profile) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [.st k] => do
    let (x, ip, _) ← x87Begin i .read
    x87Done prof i ip none x {} none X87.heldUndef fun x => (x.free k).codesUndef
  | _ => formNotModelled i

/-- `FINCSTP` (`d = 1`) and `FDECSTP` (`d = 7`): add `d` to `TOP` modulo 8, the tags unchanged; `C1 = 0`,
`C0`, `C2`, `C3` undefined (SDM Vol. 2, "FINCSTP", "FDECSTP"; APM Vol. 5, "FINCSTP", "FDECSTP"). -/
def Sem.ftop (prof : Profile) (d : Nat) (i : Inst) : Prog Ctl := do
  let (x, ip, _) ← x87Begin i .read
  x87Done prof i ip none x {} none X87.heldUndef fun x =>
    (x.withTop (x.top + d)).codes .undef (.set false) .undef .undef

/-- `FNOP`: nothing; `C0`–`C3` undefined (SDM Vol. 2, "FNOP"; APM Vol. 5, "FNOP"). -/
def Sem.fnop (prof : Profile) (i : Inst) : Prog Ctl := do
  let (x, ip, _) ← x87Begin i .read
  x87Done prof i ip none x {} none X87.heldUndef fun x => x.codesUndef

/-- `FABS` (`neg = false`: clear the sign bit) and `FCHS` (`neg = true`: complement it) of `ST(0)`, on
any datum, NaNs included (non-arithmetic, SDM Vol. 1, Table 8-9; Vol. 2, "FABS", "FCHS"; APM Vol. 5,
"FABS", "FCHS"). An empty `ST(0)` is a stack underflow whose masked response is the QNaN indefinite.
`C1 = 0`; `C0`, `C2`, `C3` undefined. -/
def Sem.fsign (prof : Profile) (neg : Bool) (i : Inst) : Prog Ctl := do
  let (x, ip, _) ← x87Begin i .read
  let s : BitVec 80 := 1 <<< 79
  let v := x.get 0
  let r := if neg then v ^^^ s else v &&& ~~~s
  let codes (x : X87) : Prog X87 := x.codes .undef (.set false) .undef .undef
  if x.isEmpty 0 then
    x87Done prof i ip none x { ie := true } (some false) X87.heldUndef fun x => codes (x.put 0 extIndefinite)
  else x87Done prof i ip none x {} none X87.heldUndef fun x => codes (x.put 0 r)

/-- `FXAM`: classify `ST(0)` into `C3 C2 C0` (`fxamClass`), `C1` its sign bit, also when it is empty;
no exception (SDM Vol. 2, "FXAM"; APM Vol. 5, "FXAM"). -/
def Sem.fxam (prof : Profile) (i : Inst) : Prog Ctl := do
  let (x, ip, _) ← x87Begin i .read
  let (c3, c2, c0) := fxamClass (x.isEmpty 0) (x.get 0)
  x87Done prof i ip none x {} none X87.heldUndef fun x =>
    x.codes (.set c0) (.set (x.get 0).msb) (.set c2) (.set c3)

/-- The operand `ST(k)` of a comparison: `none` when empty, else its datum and whether it is a
denormal. -/
def X87.operand (x : X87) (k : Nat) : Option (Option FNum) × Bool :=
  if x.isEmpty k then (none, false) else (some (extNum (x.get k)), extIsDenormal (x.get k).toNat)

/-- A memory operand of the arithmetic and the comparisons, as `X87.operand` gives a register: the
datum and whether it is a denormal. A single or double precision operand (`w` bits, value `v`) is
decoded and widened (`FFormat.widen`), an integer one converted exactly (`FNum.ofInt`). -/
def x87MemOperand (int : Bool) (w : Nat) (v : Nat) : Option (Option FNum) × Bool :=
  if int then (some (some (FNum.ofInt (BitVec.ofNat w v).toInt)), false)
  else
    let f := if w = 32 then binary32 else binary64
    (some (some (f.widen (f.decode v))), f.isDenormal v)

/-- The comparisons that set `C3 C2 C0`: `FCOM`, `FCOMP`, `FCOMPP` (`unord = false`), `FUCOM`, `FUCOMP`,
`FUCOMPP` (`unord = true`), popping `pops` times, of `ST(0)` with `ST(i)` (`ST(1)` without operand) or a
single or double precision memory operand, `FICOM`/`FICOMP` with an integer one (`int`), and `FTST`
with `+0.0` (`x87Compare`; SDM Vol. 2, "FCOM/FCOMP/FCOMPP", "FUCOM/FUCOMP/FUCOMPP", "FICOM/FICOMP",
"FTST"; APM Vol. 5, "FCOM", "FUCOM", "FICOM", "FTST"). `C1 = 0` (SDM: "Set to 0"; for `FUCOM`, "Set to
0 if stack underflow occurred", the only case it names). With an unmasked invalid-operation or
denormal-operand exception nothing is popped, and the condition codes are set as for a masked one on
an AMD processor (APM Vol. 5, "FCOM": with a NaN or an unsupported operand it "sets the IE bit ... and
sets the condition flags to 'unordered'", whatever the mask; an AMD Zen 4 does so in hardware measurements).
On an Intel processor an unmasked invalid operation leaves them for `FCOM` and `FUCOM` ("If the
invalid-arithmetic-operand exception is unmasked, the condition code flags are not set", SDM, "FCOM";
"Flags not set if unmasked invalid-arithmetic-operand (#IA) exception is generated", "FUCOM"), and leaves
`C0`, `C2`, `C3` undefined for `FTST` and `FICOM`, whose pages say only that the flags are set to
"unordered", as for an unmasked denormal operand, of which the SDM says nothing. -/
def Sem.fcom (prof : Profile) (unord : Bool) (pops : Nat) (int tst : Bool) (i : Inst) : Prog Ctl := do
  let (x, ip, mem) ← x87Begin i .read
  let (a, aden) := x.operand 0
  let (b, bden) ← if tst then Pure.pure (some (some (FNum.zero false)), false) else
    match i.ops with
    | [] => Pure.pure (x.operand 1)
    | [.st k] => Pure.pure (x.operand k)
    | [s] => do
      let v ← readOp s.width s
      Pure.pure (x87MemOperand int s.width v.toNat)
    | _ => unmodelled (.form (reprStr i.mn))
  let (o, sf, fl) := x87Compare unord a b aden bden
  let (c3, c2, c0) := o.codes
  let held (x : X87) : Prog X87 :=
    if prof.vendor = .amd then x.codes (.set c0) .keep (.set c2) (.set c3)
    else if fl.ie && !int && !tst then Pure.pure x
    else x.codes .undef .keep .undef .undef
  x87Done prof i ip (mem.map (·.2)) x fl sf held fun x => do
    let x ← x.codes (.set c0) (.set false) (.set c2) (.set c3)
    Pure.pure (if pops = 0 then x else if pops = 1 then x.pop else x.pop.pop)

/-- `FCOMI`, `FCOMIP` (`unord = false`), `FUCOMI`, `FUCOMIP` (`unord = true`): compare `ST(0)` with
`ST(i)` into `ZF PF CF` (as `C3 C2 C0` would be, `FOrder.codes`), clear `OF`, `SF`, `AF`, and pop for
the `P` forms (SDM Vol. 2, "FCOMI/FCOMIP/FUCOMI/FUCOMIP", Table 3-24; APM Vol. 5, "FCOMI", "FUCOMI").
With an unmasked invalid-operation or denormal-operand exception nothing is popped, `OF`, `SF`, `AF` are
cleared "regardless of whether an invalid-operation exception is detected" (SDM), and `ZF`, `PF`, `CF`
are set as for a masked one on an AMD processor (APM Vol. 5, "FCOMI": "sets the flags to
'unordered'"; an AMD Zen 4 does so in hardware measurements). On an Intel processor an unmasked invalid
operation leaves them ("the status flags in the EFLAGS register are set only if the exception is
masked", SDM), and an unmasked denormal operand, of which the SDM says nothing, leaves them undefined. `C1 =
0`; `C0`, `C2`, `C3` unchanged. -/
def Sem.fcomi (prof : Profile) (unord pop : Bool) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [_, .st k] => do
    let (x, ip, _) ← x87Begin i .read
    let (a, aden) := x.operand 0
    let (b, bden) := x.operand k
    let (o, sf, fl) := x87Compare unord a b aden bden
    let (zf, pf, cf) := o.codes
    let f ← readFlags
    if x.unmasked fl && prof.vendor = .intel then
      if fl.ie then writeFlags { f with of := false, sf := false, af := false }
      else do
        let zf ← undefinedBit
        let pf ← undefinedBit
        let cf ← undefinedBit
        writeFlags { f with zf := zf, pf := pf, cf := cf, of := false, sf := false, af := false }
    else writeFlags { f with zf := zf, pf := pf, cf := cf, of := false, sf := false, af := false }
    x87Done prof i ip none x fl sf Pure.pure fun x => do
      let x ← x.codes .keep (.set false) .keep .keep
      Pure.pure (if pop then x.pop else x)
  | _ => formNotModelled i

/-! ## What rounds -/

/-- The significand precision the precision-control field `FCW.PC` (bits 9–8) selects for `FADD`,
`FSUB`, `FSUBR`, `FMUL`, `FDIV`, `FDIVR` and `FSQRT` (SDM Vol. 1, 8.1.5.2, Table 8-2; APM Vol. 1, 6.3.5,
Table 6-11):
24 bits for 00B, 53 for 10B, 64 for 11B; 01B is reserved: not modelled. The other instructions round
to 64 bits. An instruction asks for it only for a result it rounds (`x87ResultPc`), after `x87Begin`, so that
a pending `#MF`, a stack fault, an invalid operand, an unmasked denormal operand and a result that needs no
rounding come first whatever `PC` holds. -/
def x87Prec (fcw : BitVec 16) : Prog Nat :=
  match fcw.toNat / 256 % 4 with
  | 0 => Pure.pure 24
  | 2 => Pure.pure 53
  | 3 => Pure.pure 64
  | _ => unmodelled (.feature "x87 precision control 01B (reserved)")

/-- The rounding mode in `FCW.RC`, bits 11–10 (SDM Vol. 1, 8.1.5.3; APM Vol. 1, 6.2.3). -/
def x87Rc (fcw : BitVec 16) : Round := Round.ofBits (fcw.toNat / 1024)

/-- The nonzero finite result `(−1)^neg · v` of an instruction that writes a register, rounded under
the control word `fcw` to a significand of `p` bits (`x87Prec`, or 64) with the double extended
exponent range (reduced precision "keeps the exponent in double-extended range", APM Vol. 1, 6.3.5): the
value, its conditions, and whether it was rounded up in magnitude (`C1`, "the round-up bit"; SDM Vol.
1, 8.5.4–8.5.6; APM Vol. 1, Table 6-22). After overflow with `OM` set, and after underflow with `UM`
set (the result denormalized, underflow reported if it is inexact), the masked responses
(`roundExact`). With `OM` clear an overflowing result is rounded with its value divided by `2^24576`
(its exponent decreased by 24576), with `UM` clear a tiny one with its value multiplied by `2^24576`,
and stored so: the overflow or underflow and, if the rounding was inexact, the precision condition
(SDM 8.5.4, 8.5.5, 8.5.6; APM Table 6-22). -/
def extRound (p : Nat) (fcw : BitVec 16) (neg : Bool) (v : Exact) : BitVec 80 × FFlags × Bool :=
  let f : FFormat := ⟨15, p⟩
  let rc := x87Rc fcw
  let r := roundExact f rc neg v
  if r.overflow && !fcw.getLsbD 3 then
    let b := roundExact f rc neg (v.scale (-24576))
    (extBits b.val, { oe := true, pe := b.inexact }, b.up)
  else if r.tiny && !fcw.getLsbD 4 then
    let b := roundExact f rc neg (v.scale 24576)
    (extBits b.val, { ue := true, pe := b.inexact }, b.up)
  else (extBits r.val, { oe := r.overflow, ue := r.tiny && r.inexact, pe := r.inexact }, r.up)

/-- The result of an x87 operation with a NaN operand `a` or `b` (SDM Vol. 1, 4.8.3.5, Table 4-8, the x87
column; APM Vol. 1, Table 6-7): a quiet NaN beside a signaling one or a number; of two NaNs of the same
kind, the one with the larger significand, made quiet; the invalid-operation condition if either is
signaling. When the two significands are equal and the signs differ, the APM leaves the result
undefined and the SDM does not say: the result is that NaN with an undefined sign. -/
def extNan (a b : FNum) : Prog (FNum × FFlags) := do
  let fl : FFlags := { ie := a.isSNaN || b.isSNaN }
  match a, b with
  | .nan na qa pa, .nan nb qb pb =>
    if qa != qb then Pure.pure (if qa then a else b, fl)
    else if pa > pb then Pure.pure (a.quiet, fl)
    else if pb > pa then Pure.pure (b.quiet, fl)
    else if na = nb then Pure.pure (a.quiet, fl)
    else do
      let s ← undefinedBit
      Pure.pure (.nan s true pa, fl)
  | .nan .., _ => Pure.pure (a.quiet, fl)
  | _, _ => Pure.pure (b.quiet, fl)

/-- The register result of an operation `out` on operands of which one is a denormal if `den`, rounded
to `p` bits (`extRound`): the value, the conditions (the denormal operand's as `FFlags.withDenormal`
orders it), `C1`. -/
def x87Result (p : Nat) (fcw : BitVec 16) (out : FOut) (den : Bool) : Prog (BitVec 80 × FFlags × Bool) := do
  match out with
  | .exact x fl => Pure.pure (extBits x, fl.withDenormal false den, false)
  | .round neg v =>
    let (r, fl, up) := extRound p fcw neg v
    Pure.pure (r, fl.withDenormal false den, up)
  | .nan a b => do
    let (x, fl) ← extNan a b
    Pure.pure (extBits x, fl.withDenormal true den, false)

/-- `x87Result` for an instruction that rounds to `FCW.PC`'s precision: the precision is asked for
(`x87Prec`) only if `out` is a result to round and no unmasked denormal operand (`den` with `FCW.DM`,
bit 1, clear) stops the instruction before it rounds (`x87Done`). -/
def x87ResultPc (fcw : BitVec 16) (out : FOut) (den : Bool) : Prog (BitVec 80 × FFlags × Bool) := do
  let p ← match out with
    | .round .. => if den && !fcw.getLsbD 1 then Pure.pure 64 else x87Prec fcw
    | _ => Pure.pure 64
  x87Result p fcw out den

/-- The operation of the arithmetic `o` on the destination's value `a` and the source's `b` under
rounding mode `rc` (SDM Vol. 2, "FADD", "FSUB", "FSUBR", "FMUL", "FDIV", "FDIVR": the `R` forms
compute `b − a` and `b / a`). -/
def Decode.FArith.out (o : FArith) (rc : Round) (a b : FNum) : FOut :=
  match o with
  | .add => addOut rc a b
  | .sub => subOut rc a b
  | .subr => subOut rc b a
  | .mul => mulOut a b
  | .div => divOut a b
  | .divr => divOut b a

/-- The arithmetic `FADD`, `FSUB`, `FSUBR`, `FMUL`, `FDIV`, `FDIVR` (`o`), their popping forms (`pop`)
and the integer forms `FIADD` ... (`int`): `ST(0) := ST(0) o m` for a memory operand, `ST(0) := ST(0) o
ST(i)`, `ST(i) := ST(i) o ST(0)`, popping after the store for the `P` forms (SDM Vol. 2, "FADD/FADDP/
FIADD", ..., Tables 3-20, 3-26, 3-27, 3-31, 3-40, 3-41; APM Vol. 5). The result rounded to `FCW.PC`'s
precision (`x87ResultPc`; with the reserved 01B not modelled), `C1` the round-up bit, `C0`, `C2`, `C3`
undefined. An empty operand register is a stack underflow, whose masked response stores the QNaN
indefinite. An unmasked invalid-operation, denormal-operand or divide-by-zero condition stops the
instruction; an unmasked overflow, underflow or precision condition does not (`extRound`). -/
def Sem.farith (prof : Profile) (o : FArith) (pop int : Bool) (i : Inst) : Prog Ctl := do
  let (x, ip, mem) ← x87Begin i .read
  let dp := mem.map (·.2)
  let (d, a, b) ← match i.ops with
    | [.st 0, .st k] => Pure.pure (0, x.operand 0, x.operand k)
    | [.st k, .st 0] => Pure.pure (k, x.operand k, x.operand 0)
    | [s] => do
      let v ← readOp s.width s
      Pure.pure (0, x.operand 0, x87MemOperand int s.width v.toNat)
    | _ => unmodelled (.form (reprStr i.mn))
  let fin (up : Bool) (r : BitVec 80) (x : X87) : Prog X87 :=
    (if pop then (x.put d r).pop else x.put d r).codes .undef (.set up) .undef .undef
  match a, b with
  | (some (some av), ad), (some (some bv), bd) => do
    let (r, fl, up) ← x87ResultPc x.fcw (o.out (x87Rc x.fcw) av bv) (ad || bd)
    x87Done prof i ip dp x fl none X87.heldUndef (fin up r) fl.pre
  | (some _, _), (some _, _) =>
    x87Done prof i ip dp x { ie := true } none X87.heldUndef (fin false extIndefinite)
  | _, _ => x87Done prof i ip dp x { ie := true } (some false) X87.heldUndef (fin false extIndefinite)

/-- An instruction that replaces `ST(0)` by `g` of it (`FSQRT`, `FRNDINT`): an empty `ST(0)` is a stack
underflow, an unsupported encoding an invalid operand, both with the QNaN indefinite as masked
response; `g` gives the result, its conditions and `C1`, from the control word after the wait
(`x87Begin`), the datum and whether it is a denormal. -/
def x87Unary (prof : Profile) (i : Inst)
    (g : BitVec 16 → FNum → Bool → Prog (BitVec 80 × FFlags × Bool)) : Prog Ctl := do
  let (x, ip, _) ← x87Begin i .read
  let fin (up : Bool) (r : BitVec 80) (x : X87) : Prog X87 :=
    (x.put 0 r).codes .undef (.set up) .undef .undef
  match x.operand 0 with
  | (some (some a), den) => do
    let (r, fl, up) ← g x.fcw a den
    x87Done prof i ip none x fl none X87.heldUndef (fin up r) fl.pre
  | (some none, _) => x87Done prof i ip none x { ie := true } none X87.heldUndef (fin false extIndefinite)
  | (none, _) => x87Done prof i ip none x { ie := true } (some false) X87.heldUndef (fin false extIndefinite)

/-- `FSQRT`: the square root of `ST(0)` (`sqrtOut`), rounded to `FCW.PC`'s precision (`x87ResultPc`; SDM
Vol. 2, "FSQRT", Table 3-39; APM Vol. 5, "FSQRT"). -/
def Sem.fsqrt (prof : Profile) (i : Inst) : Prog Ctl :=
  x87Unary prof i fun fcw a den => x87ResultPc fcw (sqrtOut a) den

/-- `FRNDINT`: round `ST(0)` to an integer by `FCW.RC` (SDM Vol. 2, "FRNDINT"; APM Vol. 5, "FRNDINT"): a
zero or an infinity is kept, a NaN by `extNan`, a finite value rounded (a zero of its sign if it
rounds to 0), precision if it changed, `C1` if it was rounded up in magnitude. -/
def Sem.frndint (prof : Profile) (i : Inst) : Prog Ctl :=
  x87Unary prof i fun fcw a den => do
    match a with
    | .finite neg m e =>
      let (k, inexact, up) := roundAt (x87Rc fcw) neg (.ratio m 1 e) 0
      Pure.pure (extBits (if k = 0 then .zero neg else .finite neg k 0), ({ pe := inexact } : FFlags).withDenormal false den, up)
    | .nan .. => x87Result 64 fcw (.nan a a) den
    | _ => x87Result 64 fcw (.exact a {}) den

/-- `FSCALE`: `ST(0) · 2 ^ n` with `n` the integer part of `ST(1)` (truncated), rounded to 64 bits
(SDM Vol. 2, "FSCALE", Table 3-36; APM Vol. 5, "FSCALE"): a NaN operand by `extNan`; `ST(1)` infinite: a
finite `ST(0)` becomes an infinity (`+∞`) or a zero (`−∞`) of its sign, a zero times `+∞` and an
infinity times `−∞` are invalid operations; a zero or an infinity is kept. A result that overflows or
underflows even with the exponent bias of the unmasked response is an infinity or a zero of its sign
(SDM Vol. 1, 8.5.4, 8.5.5: "massive overflow"); `n` beyond `±2^16` gives that in every case and is
bounded so. Both operands empty-checked; `C1` the round-up bit. -/
def Sem.fscale (prof : Profile) (i : Inst) : Prog Ctl := do
  let (x, ip, _) ← x87Begin i .read
  let fin (up : Bool) (r : BitVec 80) (x : X87) : Prog X87 :=
    (x.put 0 r).codes .undef (.set up) .undef .undef
  match x.operand 0, x.operand 1 with
  | (some (some a), ad), (some (some b), bd) => do
    let den := ad || bd
    let (r, fl, up) ← match a, b with
      | .nan .., _ | _, .nan .. => x87Result 64 x.fcw (.nan a b) den
      | .zero _, .inf false | .inf _, .inf true => x87Result 64 x.fcw (.exact .indefinite { ie := true }) den
      | .finite n _ _, .inf false => x87Result 64 x.fcw (.exact (.inf n) {}) den
      | .finite n _ _, .inf true => x87Result 64 x.fcw (.exact (.zero n) {}) den
      | .finite n m e, _ =>
        let k : Int := match b with
          | .finite nb mb eb =>
            let t : Int := (mulPow2 mb eb : Nat)
            max (-65536) (min 65536 (if nb then -t else t))
          | _ => 0
        let (r, fl, up) := extRound 64 x.fcw n (.ratio m 1 (e + k))
        -- massive overflow or underflow: out of range even with the unmasked response's bias
        let E := (Exact.ratio m 1 (e + k)).log2
        let (r, up) :=
          if fl.oe && !x.fcw.getLsbD 3 && E - 24576 > 16383 then (extBits (.inf n), true)
          else if fl.ue && !x.fcw.getLsbD 4 && E + 24576 < -16382 then (extBits (.zero n), false)
          else (r, up)
        Pure.pure (r, fl.withDenormal false den, up)
      | _, _ => x87Result 64 x.fcw (.exact a {}) den
    x87Done prof i ip none x fl none X87.heldUndef (fin up r) fl.pre
  | (some _, _), (some _, _) => x87Done prof i ip none x { ie := true } none X87.heldUndef (fin false extIndefinite)
  | _, _ => x87Done prof i ip none x { ie := true } (some false) X87.heldUndef (fin false extIndefinite)

/-- `FXTRACT`: replace `ST(0)` by its exponent and push its significand (SDM Vol. 2, "FXTRACT"; APM Vol. 5,
"FXTRACT"): a finite value `m · 2^e` (a denormal normalized) becomes the unbiased exponent `E` (as a
value) in `ST(1)` and `m · 2^(e − E)`, in `[1, 2)`, with the sign, in `ST(0)`; a zero is the divide-by-zero
condition, `−∞` and the zero; an infinity gives `+∞` and itself; a NaN itself (made quiet) in both. A
stack overflow (`ST(7)` not empty) is checked as for a push. `C1 = 0` (overflow: 1); exact. -/
def Sem.fxtract (prof : Profile) (i : Inst) : Prog Ctl := do
  let (x, ip, _) ← x87Begin i .read
  let push2 (e s : BitVec 80) (x : X87) : Prog X87 :=
    ((x.put 0 e).push s).codes .undef (.set false) .undef .undef
  match x.operand 0 with
  | (none, _) => x87Done prof i ip none x { ie := true } (some false) X87.heldUndef (push2 extIndefinite extIndefinite)
  | _ =>
  if x.overflows then
    x87Done prof i ip none x { ie := true } (some true) X87.heldUndef fun x =>
      ((x.put 0 extIndefinite).push extIndefinite).codes .undef (.set true) .undef .undef
  else
  match x.operand 0 with
  | (some (some a), den) => do
    let (e, s, fl) ← match a with
      | .finite n m e =>
        let E := (Exact.ratio m 1 e).log2
        Pure.pure (extBits (if E = 0 then .zero false else .finite (E < 0) E.natAbs 0),
          extBits (.finite n m (e - E)), ({} : FFlags).withDenormal false den)
      | .zero n => Pure.pure (extBits (.inf true), extBits (.zero n), ({ ze := true } : FFlags))
      | .inf n => Pure.pure (extBits (.inf false), extBits (.inf n), ({} : FFlags))
      | .nan .. => do
        let (q, fl) ← extNan a a
        Pure.pure (extBits q, extBits q, fl)
    x87Done prof i ip none x fl none X87.heldUndef (push2 e s) fl.pre
  | _ => x87Done prof i ip none x { ie := true } none X87.heldUndef (push2 extIndefinite extIndefinite)

/-- `FPREM`'s and `FPREM1`'s result for the operands `a` (`ST(0)`) and `b` (`ST(1)`), one a denormal if
`den` (`Sem.fprem`). -/
def x87Rem (prof : Profile) (near : Bool) (i : Inst) (ip : Addr) (x : X87) (a b : FNum) (den : Bool) :
    Prog Ctl :=
  let set (r : BitVec 80) (c0 c1 c2 c3 : CCode) (x : X87) : Prog X87 := (x.put 0 r).codes c0 c1 c2 c3
  match a, b with
  | .nan .., _ | _, .nan .. => do
    let (r, fl, _) ← x87Result 64 x.fcw (.nan a b) den
    x87Done prof i ip none x fl none X87.heldUndef (set r .undef (.set false) (.set false) .undef) fl.pre
  | .inf _, _ | _, .zero _ =>
    x87Done prof i ip none x { ie := true } none X87.heldUndef
      (set extIndefinite .undef (.set false) (.set false) .undef)
  | _, .inf _ | .zero _, _ => do
    let fl := ({} : FFlags).withDenormal false den
    x87Done prof i ip none x fl none X87.heldUndef (set (x.get 0) (.set false) (.set false) (.set false) (.set false)) fl.pre
  | .finite na ma ea, .finite _ mb eb => do
    let Ea := (Exact.ratio ma 1 ea).log2
    let Eb := (Exact.ratio mb 1 eb).log2
    let D := Ea - Eb
    -- a and b over the common exponent `ec`
    let ec := min ea eb
    let ia := ma * 2 ^ (ea - ec).toNat
    let ib := mb * 2 ^ (eb - ec).toNat
    let (rem, q, part) ← if D < 64 then
        let qt := ia / ib
        let rt := ia % ib
        -- to nearest: the quotient rounded half to even
        let up := near && (2 * rt > ib || (2 * rt = ib && qt % 2 = 1))
        Pure.pure (if up then ((rt : Int) - ib, qt + 1, false) else ((rt : Int), qt, false))
      else do
        -- the partial quotient's bit count `N`: the APM's rule on AMD, any of 32–63 on Intel
        let n ← choice 31
        let N := if prof.vendor = .amd then 32 + (D % 32).toNat else 32 + n.val
        let sh := (D - N).toNat
        let qq := ia / (ib * 2 ^ sh)
        Pure.pure ((ia : Int) - qq * ib * 2 ^ sh, qq, true)
    -- the remainder has the dividend's sign, negated where the quotient was rounded up
    let neg := if rem < 0 then !na else na
    let out : FOut := if rem = 0 then .exact (.zero na) {} else .round neg (.ratio rem.natAbs 1 ec)
    let (r, fl, _) ← x87Result 64 x.fcw out den
    let bit (k : Nat) : CCode := .set (!part && q / 2 ^ k % 2 = 1)
    x87Done prof i ip none x fl none X87.heldUndef (set r (bit 2) (bit 0) (.set part) (bit 1)) fl.pre

/-- `FPREM` (`near = false`) and `FPREM1` (`near = true`): the partial remainder of `ST(0)` by `ST(1)`
(SDM Vol. 2, "FPREM", "FPREM1", Tables 3-33 and 3-34; APM Vol. 5). With `D` the difference of the
operands' exponents below 64, the quotient `Q` truncated (`FPREM`) or rounded to nearest-even (`FPREM1`), `ST(0)
− Q · ST(1)` exactly (zero with the dividend's sign), `C2 = 0` and the quotient's low bits in `C0`
(bit 2), `C3` (bit 1), `C1` (bit 0); else a partial reduction by a quotient scaled by `2^(D − N)`, `C2 =
1`, `C0`, `C1`, `C3` cleared (APM Action; SDM Vol. 3B, 25.18.2.1: "After an incomplete FPREM/FPREM1
instruction, the C0, C1, and C3 flags are set to 0 on the 32-bit x87 FPUs"). `N` is `32 + (D mod 32)` on
AMD (APM Action) and "an implementation-dependent number between 32 and 63" on Intel (SDM): a `pick`,
made on both vendors and ignored on AMD. A zero divisor or an infinite dividend is invalid (the indefinite,
`C2 = 0`); an infinite divisor or a zero dividend leaves `ST(0)`. A tiny remainder is exact: with `UM`
clear the underflow response's biased value (`extRound`). -/
def Sem.fprem (prof : Profile) (near : Bool) (i : Inst) : Prog Ctl := do
  let (x, ip, _) ← x87Begin i .read
  let set (r : BitVec 80) (c0 c1 c2 c3 : CCode) (x : X87) : Prog X87 := (x.put 0 r).codes c0 c1 c2 c3
  match x.operand 0, x.operand 1 with
  | (some (some a), ad), (some (some b), bd) => x87Rem prof near i ip x a b (ad || bd)
  | (some _, _), (some _, _) =>
    x87Done prof i ip none x { ie := true } none X87.heldUndef (set extIndefinite .undef (.set false) (.set false) .undef)
  | _, _ =>
    x87Done prof i ip none x { ie := true } (some false) X87.heldUndef
      (set extIndefinite .undef (.set false) .undef .undef)

/-- The internal values of the constants `FLDPI`, `FLDL2T`, `FLDL2E`, `FLDLG2`, `FLDLN2` loads, as
significand and exponent: `π`, `log₂ 10`, `log₂ e`, `log₁₀ 2`, `ln 2`, each truncated to 80 significant
bits. The manuals say that "an internal 66-bit constant is rounded (as specified by the RC field)" and
give `π`'s (SDM Vol. 1, 8.3.4, 8.3.8; Vol. 2, "FLD1/.../FLDZ"; APM Vol. 5); an AMD Zen 4 delivers in each
of the four rounding modes the constant rounded as these values are in hardware measurements, which for
`log₁₀ 2` a 66-bit value would not give (its 66-bit truncation is half-way between two 64-bit values). -/
def x87Const : X87Mn → Nat × Int
  | .fldpi => (0xc90fdaa22168c234c4c6, -78)
  | .fldl2t => (0xd49a784bcd1b8afe492b, -78)
  | .fldl2e => (0xb8aa3b295c17f0bbbe87, -79)
  | .fldlg2 => (0x9a209a84fbcff7988f89, -81)
  | _ => (0xb17217f7d1cf79abc9e3, -80)

/-- `FLDPI`, `FLDL2T`, `FLDL2E`, `FLDLG2`, `FLDLN2`: push the constant (`x87Const`) rounded to 64 bits by
`FCW.RC`, without the precision condition and with `C1` not the round-up bit (SDM Vol. 1, 8.3.4: "The
inexact-result exception (#P) is not generated as a result of this rounding, nor is the C1 flag set"). -/
def Sem.fldConstRounded (prof : Profile) (m : X87Mn) (i : Inst) : Prog Ctl := do
  let (x, ip, _) ← x87Begin i .read
  let (s, e) := x87Const m
  x87Push prof i ip none x (extBits (roundExact ⟨15, 64⟩ (x87Rc x.fcw) false (.ratio s 1 e)).val) {}

/-- `ST(0)`'s datum `a` stored to a single or double precision memory operand (format `f`, `FST`/`FSTP`;
SDM Vol. 2, "FST/FSTP"; APM Vol. 5, "FST"): a NaN keeps its sign and the high bits of its fraction,
made quiet (invalid if signaling); an unsupported encoding is invalid, the indefinite; a zero or an
infinity is kept; a finite value is rounded to `f` by `FCW.RC` (not `PC`), with `f`'s exponent range.
An overflow or underflow whose exception is unmasked stores nothing and reports no precision condition
(SDM Vol. 1, 8.5.4–8.5.6: "the inexact-result condition is not reported"; APM Vol. 1, Table 6-22); the
masked responses as `roundExact`. The value, the conditions, the round-up bit. -/
def extStore (f : FFormat) (fcw : BitVec 16) (a : Option FNum) : Nat × FFlags × Bool :=
  match a with
  | none => (f.encode .indefinite, { ie := true }, false)
  | some (.nan n q p) =>
    (f.encode (.nan n true (p / 2 ^ (62 - (f.fbits - 1)))), { ie := !q }, false)
  | some (.finite n m e) =>
    let r := roundExact f (x87Rc fcw) n (.ratio m 1 e)
    let trapped := (r.overflow && !fcw.getLsbD 3) || (r.tiny && !fcw.getLsbD 4)
    let ue := r.tiny && (!fcw.getLsbD 4 || r.inexact)
    let fl : FFlags := { oe := r.overflow, ue := ue, pe := r.inexact && !trapped }
    (f.encode r.val, fl, r.up)
  | some x => (f.encode x, {}, false)

/-- `FST`, `FSTP` (`pop`) to a single or double precision memory operand (`extStore`): an empty `ST(0)` is
a stack underflow whose masked response stores the format's QNaN indefinite; an unmasked invalid
operation, overflow or underflow stores nothing and does not pop. `C1` the round-up bit, `C0`, `C2`,
`C3` undefined. -/
def Sem.fstm (prof : Profile) (pop : Bool) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d] => do
    let (x, ip, mem) ← x87Begin i .write
    let dp := mem.map (·.2)
    let f := if d.width = 32 then binary32 else binary64
    let fin (up : Bool) (v : Nat) (x : X87) : Prog X87 := do
      writeOp d (BitVec.ofNat d.width v)
      (if pop then x.pop else x).codes .undef (.set up) .undef .undef
    match x.operand 0 with
    | (none, _) => x87Done prof i ip dp x { ie := true } (some false) X87.heldUndef (fin false (f.encode .indefinite))
    | (some a, _) =>
      let (v, fl, up) := extStore f x.fcw a
      let stops : FFlags := { fl.pre with oe := fl.oe && !x.fcw.getLsbD 3, ue := fl.ue && !x.fcw.getLsbD 4 }
      x87Done prof i ip dp x fl none X87.heldUndef (fin up v) stops
  | _ => formNotModelled i

/-- `FIST`, `FISTP` (`rc` = `FCW.RC`) and `FISTTP` (`rc` = toward zero): `ST(0)` rounded to a signed
integer of `w` bits (SDM Vol. 2, "FIST/FISTP", "FISTTP"; APM Vol. 5): a NaN, an infinity, an
unsupported encoding or a value whose rounded result is out of range is invalid, with the integer
indefinite (`2^(w − 1)`) as masked response; otherwise the integer, with precision and the round-up bit
if it differs from the value. -/
def extToInt (a : Option FNum) (w : Nat) (rc : Round) : Nat × FFlags × Bool :=
  let indefinite := (2 ^ (w - 1), ({ ie := true } : FFlags), false)
  match a with
  | some (.zero _) => (0, {}, false)
  | some (.finite n m e) =>
    let (k, inexact, up) := roundAt rc n (.ratio m 1 e) 0
    let i : Int := if n then -(k : Int) else k
    if -(2 ^ (w - 1) : Int) ≤ i ∧ i < 2 ^ (w - 1) then ((i % 2 ^ w).toNat, { pe := inexact }, up)
    else indefinite
  | _ => indefinite

/-- `FIST`, `FISTP`, `FISTTP` (`trunc`) of `ST(0)` to the memory operand (`extToInt`); an empty `ST(0)` is a
stack underflow whose masked response stores the integer indefinite; an unmasked invalid operation
stores nothing and does not pop. `C1` the round-up bit, `C0`, `C2`, `C3` undefined. -/
def Sem.fist (prof : Profile) (pop trunc : Bool) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d] => do
    let (x, ip, mem) ← x87Begin i .write
    let dp := mem.map (·.2)
    let w := d.width
    let fin (up : Bool) (v : Nat) (x : X87) : Prog X87 := do
      writeOp d (BitVec.ofNat w v)
      (if pop then x.pop else x).codes .undef (.set up) .undef .undef
    match x.operand 0 with
    | (none, _) => x87Done prof i ip dp x { ie := true } (some false) X87.heldUndef (fin false (2 ^ (w - 1)))
    | (some a, _) =>
      let (v, fl, up) := extToInt a w (if trunc then .zero else x87Rc x.fcw)
      x87Done prof i ip dp x fl none X87.heldUndef (fin up v) fl.pre
  | _ => formNotModelled i

/-- The integer an 18-digit packed BCD value `v` holds (SDM Vol. 1, 4.7, Table 4-5; APM Vol. 1, 6.3.2):
the digits in bytes 0–8, two per byte with the less significant in the low four bits, the sign in bit
79, bits 78–72 not used; `none` if a digit is above 9. -/
def bcdValue (v : BitVec 80) : Option Int :=
  let digits := (List.range 18).map fun k => (v.toNat / 16 ^ k) % 16
  if digits.any (· > 9) then none
  else
    let n : Nat := digits.foldr (fun d acc => d + 10 * acc) 0
    some (if v.getLsbD 79 then -(n : Int) else n)

/-- The 18-digit packed BCD encoding of `n` (`|n| < 10^18`) with sign bit `neg` (bits 78–72 zero). -/
def bcdEncode (neg : Bool) (n : Nat) : BitVec 80 :=
  let digits := (List.range 18).foldl (fun acc k => acc + (n / 10 ^ k % 10) * 16 ^ k) 0
  BitVec.ofNat 80 (digits + if neg then 2 ^ 79 else 0)

/-- `FBLD m80`: push the packed BCD integer, converted exactly, a zero keeping its sign (SDM Vol. 2,
"FBLD": "loaded without rounding errors. The sign of the source operand is preserved, including that of
−0"; APM Vol. 5, "FBLD"); a digit above 9 gives an undefined result ("Attempting to load an invalid
encoding produces an undefined result", SDM). A push as `FLD`'s (`x87Push`). -/
def Sem.fbld (prof : Profile) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [s] => do
    let (x, ip, mem) ← x87Begin i .read
    let v ← readOp 80 s
    let r ← match bcdValue v with
      | some n => Pure.pure (extBits (if n = 0 then .zero (v.getLsbD 79) else FNum.ofInt n))
      | none => undefined 80
    x87Push prof i ip (mem.map (·.2)) x r {}
  | _ => formNotModelled i

/-- `FBSTP m80`: `ST(0)` rounded to an integer by `FCW.RC` and stored as an 18-digit packed BCD integer,
then popped (SDM Vol. 2, "FBSTP", Table 3-21; APM Vol. 5, "FBSTP"): a zero, or a value rounding to 0,
keeps its sign; precision and the round-up bit if the value changed. A NaN, an infinity, an unsupported
encoding or a rounded value of more than 18 digits is invalid, with the packed BCD indefinite
(`FFFFC000000000000000H`, SDM Vol. 1, Table 4-5; APM Vol. 1, Table 6-10) as masked response; an unmasked one stores nothing and
does not pop; an empty `ST(0)` is a stack underflow. -/
def Sem.fbstp (prof : Profile) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d] => do
    let (x, ip, mem) ← x87Begin i .write
    let dp := mem.map (·.2)
    let indefinite : BitVec 80 := 0xFFFFC000000000000000
    let fin (up : Bool) (v : BitVec 80) (x : X87) : Prog X87 := do
      writeOp d v
      x.pop.codes .undef (.set up) .undef .undef
    match x.operand 0 with
    | (none, _) => x87Done prof i ip dp x { ie := true } (some false) X87.heldUndef (fin false indefinite)
    | (some a, _) =>
      let (v, fl, up) : BitVec 80 × FFlags × Bool := match a with
        | some (.zero n) => (bcdEncode n 0, {}, false)
        | some (.finite n m e) =>
          let (k, inexact, up) := roundAt (x87Rc x.fcw) n (.ratio m 1 e) 0
          if k < 10 ^ 18 then (bcdEncode n k, { pe := inexact }, up) else (indefinite, { ie := true }, false)
        | _ => (indefinite, { ie := true }, false)
      x87Done prof i ip dp x fl none X87.heldUndef (fin up v) fl.pre
  | _ => formNotModelled i

/-- `FNSAVE m108`: store the environment (`x87EnvImage`) and the registers `ST(0)`–`ST(7)` in stack order,
10 bytes each, then initialize the x87 unit as `FNINIT` does (SDM Vol. 2, "FSAVE/FNSAVE"; Vol. 1, 8.1.10,
Figure 8-9; APM Vol. 5, "FSAVE"). `C0`–`C3` saved, then cleared. Non-waiting. The access is checked
by `x87Area`; the 16-bit operand size (94-byte format) is not modelled. -/
def Sem.fnsave (prof : Profile) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [.mem mo] => do
    let m ← memRef mo
    x87Area m .write 108
    let x ← readX87
    let seen ← x87SeenPtrs prof x
    let rsv ← undefined 96
    let regs := (List.range 8).flatMap fun k => toBytesLE (x.get k) 10
    write m 864 (ofBytesLE 864 (x87EnvImage prof seen rsv ++ regs))
    writeX87 { x with fcw := 0x37F, fsw := 0, full := 0, fop := 0, fip := 0, fdp := 0 }
    done
  | _ => formNotModelled i

/-- `FRSTOR m108`: load the environment (`x87LoadEnv`, as `FLDENV`) and the registers `ST(0)`–`ST(7)`
from the image `FNSAVE` stores (SDM Vol. 2, "FRSTOR"; APM Vol. 5, "FRSTOR"). Waiting. The access is
checked by `x87Area`; the 16-bit operand size (94-byte format) is not modelled. -/
def Sem.frstor (prof : Profile) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [.mem mo] => do
    let (x, _, _) ← x87Begin i .read true
    let m ← memRef mo
    x87Area m .read 108
    let img : BitVec 864 ← read m 864
    let x ← x87LoadEnv prof "FRSTOR" x (img.setWidth 224)
    -- ST(k) is physical register (TOP + k) mod 8 of the loaded TOP
    writeX87 { x with st := fun j => img.extractLsb' (224 + 80 * ((j.val + 8 - x.top) % 8)) 80 }
    done
  | _ => formNotModelled i

/-! ## Dispatch -/

/-- Execute x87 instruction `i` with mnemonic `m` (`Mn.x87`). -/
def execX87 (prof : Profile) (m : X87Mn) (i : Inst) : Prog Ctl :=
  match m with
  | .fnstcw => Sem.fnstcw i
  | .fnstsw => Sem.fnstsw i
  | .fldcw => Sem.fldcw prof i
  | .fnclex => Sem.fnclex i
  | .fninit => Sem.fninit i
  | .fwait => Sem.fwait i
  | .fnstenv => if i.opsz = 16 then formNotModelled i else Sem.fnstenv prof i
  | .fldenv => if i.opsz = 16 then formNotModelled i else Sem.fldenv prof i
  | .fxsave => Sem.fxsave prof i
  | .fxrstor => Sem.fxrstor prof i
  | .fld => Sem.fld prof i
  | .fild => Sem.fild prof i
  | .fldz => Sem.fldConst prof 0 i
  | .fld1 => Sem.fldConst prof extOne i
  | .fst => if (i.ops.head?.map (·.width)).getD 80 < 80 then Sem.fstm prof false i else Sem.fst prof false i
  | .fstp => if (i.ops.head?.map (·.width)).getD 80 < 80 then Sem.fstm prof true i else Sem.fst prof true i
  | .fxch => Sem.fxch prof i
  | .fcmov c => Sem.fcmov prof c i
  | .ffree => Sem.ffree prof i
  | .fincstp => Sem.ftop prof 1 i
  | .fdecstp => Sem.ftop prof 7 i
  | .fnop => Sem.fnop prof i
  | .fabs => Sem.fsign prof false i
  | .fchs => Sem.fsign prof true i
  | .fxam => Sem.fxam prof i
  | .ftst => Sem.fcom prof false 0 false true i
  | .com u n => Sem.fcom prof u n false false i
  | .icom p => Sem.fcom prof false (if p then 1 else 0) true false i
  | .comi u p => Sem.fcomi prof u p i
  | .arith o p => Sem.farith prof o p false i
  | .iarith o => Sem.farith prof o false true i
  | .fsqrt => Sem.fsqrt prof i
  | .frndint => Sem.frndint prof i
  | .fscale => Sem.fscale prof i
  | .fxtract => Sem.fxtract prof i
  | .fprem => Sem.fprem prof false i
  | .fprem1 => Sem.fprem prof true i
  | .fldpi | .fldl2t | .fldl2e | .fldlg2 | .fldln2 => Sem.fldConstRounded prof m i
  | .fist => Sem.fist prof false false i
  | .fistp => Sem.fist prof true false i
  | .fisttp => Sem.fist prof true true i
  | .fnsave => if i.opsz = 16 then formNotModelled i else Sem.fnsave prof i
  | .fbld => Sem.fbld prof i
  | .fbstp => Sem.fbstp prof i
  | .frstor => if i.opsz = 16 then formNotModelled i else Sem.frstor prof i
  | _ => formNotModelled i

end ZellicX86
