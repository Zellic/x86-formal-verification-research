import ZellicX86.Spec.Semantics.Basic
import ZellicX86.Spec.Float
import ZellicX86.Spec.Xsave
/-!
# Instruction semantics: SSE and AVX floating point

The instructions that compute with single- and double-precision values (`Mn.fp`): each element of
a result is an operation of `Spec/Float.lean` on the sources' elements, under the controls of
`MXCSR` (rounding, `DAZ`, `FTZ`, the exception masks; SDM Vol. 1, 10.2.3; AMD APM Vol. 1, 4.2.2).
Each case follows the "Operation" section of the instruction's page in SDM Vol. 2; where AMD APM
Vol. 4 differs, the case says so.

What is common to the family:

- **Exceptions** (SDM Vol. 1, 11.5.3 "Generating SIMD Floating-Point Exceptions"; APM Vol. 1,
  4.10.3, Figure 4-52): the elements' conditions are combined (`FFlags.or`); if one of the
  pre-computation conditions (invalid operation, denormal operand, divide by zero) is unmasked,
  only those flags are set in `MXCSR` and `#XM` is raised; else if one of the post-computation
  conditions is unmasked, all the flags are set and `#XM` is raised; else the flags are set and the
  results written (`simdDone`). An instruction that raises `#XM` writes no result. Linux sets
  `CR4.OSXMMEXCPT` (`arch/x86/kernel/fpu/init.c`, `fpu__init_cpu_generic`), so the exception is
  `#XM`, never `#UD`. The flags are sticky: an instruction only sets them.
- **Operands**: a legacy SSE form has two operands, the destination being the first source, and
  keeps the destination's bits 511–128 (`writeOp` of `Opd.xmm`); a VEX form has a separate first
  source and clears the bits above its vector length (`Opd.vreg`). A scalar form computes element 0;
  the destination's other bits up to 127 come from the first source.
- **Alignment**: legacy packed forms of exception type 2 need a 16-byte aligned memory operand
  (SDM Vol. 2, 2.5.2, Table 2-19), except with AMD's misaligned SSE mode (`MXCSR.MM`); scalar forms
  (type 3), the forms of type 5 and all VEX forms take any address.
- `DAZ` reads denormal source elements as zeros (`FFormat.operand`), also for the conversions to
  integers; the denormal-operand condition is never reported by those conversions (SDM Vol. 1,
  11.5.2.2).
-/
namespace ZellicX86
open Decode Prog

/-- The format of element type `t`. -/
def Decode.FpTy.fmt : FpTy → FFormat
  | .ps | .ss => binary32
  | .pd | .sd => binary64

/-- The element size of element type `t` in bits. -/
def Decode.FpTy.esz : FpTy → Nat
  | .ps | .ss => 32
  | .pd | .sd => 64

/-- Whether element type `t` is scalar (`SS`, `SD`). -/
def Decode.FpTy.scalar : FpTy → Bool
  | .ss | .sd => true
  | .ps | .pd => false

/-- The controls in `MXCSR` value `m` (SDM Vol. 1, 10.2.3, Figure 10-3): the rounding control in
bits 14–13, `DAZ` bit 6, `FTZ` bit 15, the overflow and underflow masks bits 10 and 11. -/
def mxcsrCtl (m : BitVec 32) : FCtl :=
  ⟨Round.ofBits (m.toNat / 2 ^ 13), m.getLsbD 6, m.getLsbD 15, m.getLsbD 10, m.getLsbD 11⟩

/-- The end of a floating-point instruction whose elements detected the conditions `fl`, with
`write` writing its results (SDM Vol. 1, 11.5.3.1–11.5.3.3; APM Vol. 1, 4.10.3–4.10.4): a
condition is unmasked when its mask bit (`MXCSR` bits 7–12) is clear. On an Intel processor a
`#XM` for an unmasked overflow or underflow is not modelled: which flags it sets has not been checked
against Intel hardware. The SDM (Vol. 1, 4.9.1.6) sets the precision flag with it when the result is
inexact, as `FFormat.result` does following an AMD Zen 4 (`inexactWide`). -/
def simdDone (prof : Profile) (fl : FFlags) (write : Prog Unit) : Prog Ctl := do
  let m ← readMxcsr
  let unmasked (a : FFlags) : Bool := a.bits &&& (63 - m.toNat / 2 ^ 7 % 64) != 0
  if unmasked fl.pre then throw (.xm (m ||| BitVec.ofNat 32 fl.pre.bits))
  else if unmasked fl.post then
    if prof.vendor = .intel && unmasked { oe := fl.oe, ue := fl.ue } then
      unmodelled (.feature "#XM for an unmasked overflow or underflow on Intel")
    else throw (.xm (m ||| BitVec.ofNat 32 fl.bits))
  else do
    writeMxcsr (m ||| BitVec.ofNat 32 fl.bits)
    write
    done

/-- The `w`-bit vector of `esz`-bit elements `g j` for `j < w / esz`, with the conditions of all of
them: the packed forms compute each element on its own and combine the conditions (SDM Vol. 1,
11.5.3.1, Figure 11-9). -/
def fpLanes (w esz : Nat) (g : Nat → Nat × FFlags) : BitVec w × FFlags :=
  let rs := (List.range (w / esz)).map g
  (ofElems w esz fun j => BitVec.ofNat esz (rs.getD j (0, {})).1,
   rs.foldl (fun acc r => acc.or r.2) {})

/-- `#GP(0)` for a misaligned memory operand `s` of a legacy packed form (exception type 2:
`d` is a legacy `XMM` register), unless `MXCSR.MM` allows it (`aligned16`). -/
def legacyAligned (prof : Profile) (d s : Opd) : Prog Unit :=
  match d with
  | .xmm _ => aligned16 s .read prof.misalignSse
  | _ => Pure.pure ()

/-- The destination and the two sources of a floating-point instruction: a legacy form `[d, s]`
computes from `d` and `s` into `d`, a VEX form `[d, s₁, s₂]` from `s₁` and `s₂` into `d`. -/
def fpOperands (i : Inst) : Option (Opd × Opd × Opd) :=
  match i.ops with
  | [d, s] => some (d, d, s)
  | [d, s₁, s₂] => some (d, s₁, s₂)
  | _ => none

/-! ## Arithmetic -/

/-- One element of a binary operation `op` of format `f` on the bit patterns `x` and `y`: the
operands as the controls read them (`FFormat.operand`), the operation, and the denormal-operand
condition (`FFlags.withDenormal`). -/
def fpBinElem (f : FFormat) (c : FCtl) (op : FFormat → FCtl → FNum → FNum → Nat × FFlags)
    (x y : Nat) : Nat × FFlags :=
  let (a, da) := f.operand c x
  let (b, db) := f.operand c y
  let (r, fl) := op f c a b
  (r, fl.withDenormal (a.isNaN || b.isNaN) (da || db))

/-- A binary floating-point instruction of element type `t` whose element operation on the bit
patterns of format `t.fmt` is `g` (`fpOperands`; the common rules of this module). -/
def fpBinary (prof : Profile) (t : FpTy) (g : FFormat → FCtl → Nat → Nat → Nat × FFlags)
    (i : Inst) : Prog Ctl :=
  match fpOperands i with
  | none => formNotModelled i
  | some (d, s₁, s₂) => do
    if t.scalar then do
      let a ← readOp 128 s₁
      let b ← readOp t.esz s₂
      let c := mxcsrCtl (← readMxcsr)
      let (r, fl) := g t.fmt c (elem t.esz a 0).toNat b.toNat
      simdDone prof fl (writeOp d ((a >>> t.esz <<< t.esz) ||| BitVec.ofNat 128 r))
    else do
      legacyAligned prof d s₂
      let w := d.width
      let a ← readOp w s₁
      let b ← readOp w s₂
      let c := mxcsrCtl (← readMxcsr)
      let (r, fl) := fpLanes w t.esz fun j => g t.fmt c (elem t.esz a j).toNat (elem t.esz b j).toNat
      simdDone prof fl (writeOp d r)

/-- `ADDPS`, `ADDPD`, `ADDSS`, `ADDSD` and their VEX forms (`FFormat.add`; SDM Vol. 2, "ADDPS", ...). -/
def Sem.fpAdd (prof : Profile) (t : FpTy) (i : Inst) : Prog Ctl :=
  fpBinary prof t (fun f c => fpBinElem f c FFormat.add) i
/-- `SUBPS` ... (`FFormat.sub`; SDM Vol. 2, "SUBPS", ...). -/
def Sem.fpSub (prof : Profile) (t : FpTy) (i : Inst) : Prog Ctl :=
  fpBinary prof t (fun f c => fpBinElem f c FFormat.sub) i
/-- `MULPS` ... (`FFormat.mul`; SDM Vol. 2, "MULPS", ...). -/
def Sem.fpMul (prof : Profile) (t : FpTy) (i : Inst) : Prog Ctl :=
  fpBinary prof t (fun f c => fpBinElem f c FFormat.mul) i
/-- `DIVPS` ... (`FFormat.div`; SDM Vol. 2, "DIVPS", ...). -/
def Sem.fpDiv (prof : Profile) (t : FpTy) (i : Inst) : Prog Ctl :=
  fpBinary prof t (fun f c => fpBinElem f c FFormat.div) i

/-- One element of `MINPS` ... (`isMax` false) or `MAXPS` ... (SDM Vol. 2, "MINPS", "MAXPS", ...,
Operation: `MIN(SRC1, SRC2)`): the second source if either source is a NaN, with the invalid-operation
condition for a quiet NaN too, and its bits unchanged even if signaling (SDM Vol. 1, Table 11-1:
"Return the source 2 operand value"; APM Vol. 1, Table 4-15); the second source if both are zeros
(of either sign) or if the first is not less (`MIN`) or not greater (`MAX`); else the first. The
operands are the ones the controls give (`DAZ`: a denormal source is read, and returned, as a zero). -/
def FFormat.minMax (f : FFormat) (c : FCtl) (isMax : Bool) (x y : Nat) : Nat × FFlags :=
  let (a, da) := f.operand c x
  let (b, db) := f.operand c y
  if a.isNaN || b.isNaN then (f.encode b, { ie := true })
  else
    let first := if isMax then fcompare a b = .gt else fcompare a b = .lt
    (f.encode (if first then a else b), FFlags.withDenormal {} false (da || db))

/-- `MINPS`, `MINPD`, `MINSS`, `MINSD` and their VEX forms (`FFormat.minMax`). -/
def Sem.fpMin (prof : Profile) (t : FpTy) (i : Inst) : Prog Ctl :=
  fpBinary prof t (fun f c => f.minMax c false) i
/-- `MAXPS`, `MAXPD`, `MAXSS`, `MAXSD` and their VEX forms (`FFormat.minMax`). -/
def Sem.fpMax (prof : Profile) (t : FpTy) (i : Inst) : Prog Ctl :=
  fpBinary prof t (fun f c => f.minMax c true) i

/-- A packed instruction of element type `t` with one source (`[d, s]`, legacy and VEX) whose element
operation on the bit patterns of format `t.fmt` is `g`: the destination is written, not read (the common
rules of this module). -/
def fpUnaryPacked (prof : Profile) (t : FpTy) (g : FFormat → FCtl → Nat → Nat × FFlags) (d s : Opd) :
    Prog Ctl := do
  legacyAligned prof d s
  let w := d.width
  let b ← readOp w s
  let c := mxcsrCtl (← readMxcsr)
  let (r, fl) := fpLanes w t.esz fun j => g t.fmt c (elem t.esz b j).toNat
  simdDone prof fl (writeOp d r)

/-- One element of `SQRTPS` ...: the square root of the bit pattern `y` (`FFormat.sqrt`), with the
denormal-operand condition. -/
def FFormat.sqrtElem (f : FFormat) (c : FCtl) (y : Nat) : Nat × FFlags :=
  let (a, da) := f.operand c y
  let (r, fl) := f.sqrt c a
  (r, fl.withDenormal a.isNaN da)

/-- `SQRTPS`, `SQRTPD`, `SQRTSS`, `SQRTSD` and their VEX forms (`FFormat.sqrtElem`; SDM Vol. 2,
"SQRTPS", ...): the packed forms take one source (`[d, s]`, legacy and VEX; `fpUnaryPacked`), the scalar
ones as the other binary forms (`fpOperands`), the square root of the second source's element 0. -/
def Sem.fpSqrt (prof : Profile) (t : FpTy) (i : Inst) : Prog Ctl :=
  if t.scalar then fpBinary prof t (fun f c _ y => f.sqrtElem c y) i
  else match i.ops with
    | [d, s] => fpUnaryPacked prof t FFormat.sqrtElem d s
    | _ => formNotModelled i

/-! ## Integral rounding, fused arithmetic and SSE3 -/

/-- Check a `ROUND` immediate's reserved bits 7–4 (SDM Vol. 2, Figure 4-24; APM Vol. 4, "ROUNDPS"):
neither manual says what a nonzero value does. An AMD Zen 4 ignores them, so on AMD they are ignored;
on Intel an immediate that sets one is not modelled. -/
def Sem.fpRoundCheck (prof : Profile) (k : Nat) : Prog Unit := do
  if k >= 16 then
    if prof.vendor = .intel then
      unmodelled (.feature "ROUND: reserved immediate bits on Intel")

/-- `ROUNDPS`, `ROUNDPD`, `ROUNDSS`, `ROUNDSD` and their VEX forms (SDM Vol. 2, "ROUNDPS", ...; APM Vol. 4,
the same pages): each element rounded to an integral value (`roundIntOut`). Immediate bit 2 selects
`MXCSR.RC` instead of bits 1–0; bit 3 suppresses the precision condition. Bits 7–4 are checked by
`Sem.fpRoundCheck`. `DAZ` applies, and the denormal-operand condition is never reported. A NaN is made
quiet, with the invalid-operation condition for a signaling one. Legacy packed forms are of exception
type 2 (aligned memory operand), scalar forms of type 3. -/
def Sem.fpRound (prof : Profile) (t : FpTy) (i : Inst) : Prog Ctl :=
  let apply (k : Nat) (f : FFormat) (c : FCtl) (_ y : Nat) :=
    let (a, _) := f.operand c y
    let rc := if k / 4 % 2 = 1 then c.rc else Round.ofBits k
    let (r, fl) := f.finish c (roundIntOut rc a)
    (r, { fl with pe := fl.pe && k / 8 % 2 = 0 })
  match i.ops with
  | [d, s, .imm _ k] => do
    Sem.fpRoundCheck prof k
    if t.scalar then fpBinary prof t (apply k) { i with ops := [d, s] }
    else fpUnaryPacked prof t (fun f c y => apply k f c 0 y) d s
  | [d, a, b, .imm _ k] => do
    Sem.fpRoundCheck prof k
    fpBinary prof t (apply k) { i with ops := [d, a, b] }
  | _ => formNotModelled i

/-- One element of an FMA instruction: the sources reordered into the equation's order (multiplicand,
multiplier, addend; SDM Vol. 1, 14.5.1, Table 14-17; APM Vol. 1, 4.7.5.1, Figure 4-49), then `fmaOut`
with a single rounding. A NaN is chosen in that order, and the sign changes never alter a NaN's sign.
The denormal-operand condition is that of any source, unless a NaN or an invalid operation takes
precedence (`FFlags.withDenormal`). -/
def fpFmaElem (f : FFormat) (c : FCtl) (order : FmaOrder) (np sa : Bool)
    (x y z : Nat) : Nat × FFlags :=
  let (a, da) := f.operand c x
  let (b, db) := f.operand c y
  let (d, dd) := f.operand c z
  let (u, v, w) := match order with
    | .o132 => (a, d, b)
    | .o213 => (b, a, d)
    | .o231 => (b, d, a)
  let (r, fl) := f.finish c (fmaOut c.rc np sa u v w)
  (r, fl.withDenormal (a.isNaN || b.isNaN || d.isNaN) (da || db || dd))

/-- VEX FMA3 `VFMADD`, `VFMSUB`, `VFNMADD`, `VFNMSUB`, in orders 132/213/231,
scalar and packed (SDM Vol. 2, "VFMADD132PD/VFMADD213PD/VFMADD231PD", ...; APM Vol. 4, the same
pages).
All three sources are read before writing the destination. Scalar upper bits 127:esz
come from the old destination, not the VEX.vvvv operand; bits above 127 are cleared.
Packed memory sources take any alignment (Type 2 VEX). -/
def Sem.fpFma (prof : Profile) (t : FpTy) (order : FmaOrder) (np sa : Bool) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s₂, s₃] => do
    let w := if t.scalar then 128 else d.width
    let a ← readOp w d
    let b ← readOp w s₂
    let v ← readOp (if t.scalar then t.esz else w) s₃
    let c := mxcsrCtl (← readMxcsr)
    if t.scalar then
      let (r, fl) := fpFmaElem t.fmt c order np sa (elem t.esz a 0).toNat
        (elem t.esz b 0).toNat v.toNat
      simdDone prof fl (writeOp d ((a.setWidth 128 >>> t.esz <<< t.esz) ||| BitVec.ofNat 128 r))
    else
      let (r, fl) := fpLanes w t.esz fun j => fpFmaElem t.fmt c order np sa
        (elem t.esz a j).toNat (elem t.esz b j).toNat (elem t.esz v j).toNat
      simdDone prof fl (writeOp d r)
  | _ => formNotModelled i

/-- `ADDSUBPS`, `ADDSUBPD`, `HADDPS`, `HADDPD`, `HSUBPS`, `HSUBPD` and their VEX forms (SDM Vol. 2 and
APM Vol. 4, the instructions' pages). `ADDSUB` subtracts in the even elements and adds in the odd ones.
The horizontal forms combine adjacent pairs of the first source, then of the second, in each 128-bit
lane. Each element is `addOut` or `subOut`, whose first operand's NaN is the result when both are NaNs
(`FFormat.nanResult`). `HSUB` computes low − high. For `HADD` the manuals do not settle which element is
the first operand: the SDM's pseudocode puts the high one first (`SRC1[63:32] + SRC1[31:0]`) and its
description and figure the low one (`X0+X1`); the APM's description puts the high one first; an AMD
Zen 4 returns the low one's NaN, also beside a signaling high one. So for a pair of NaNs whose result
depends on the order, which element comes first is a `pick` (alternative 0: the low one), one per pair,
on both vendors. Legacy packed forms need an aligned memory operand (exception type 2). -/
def Sem.fpSse3 (prof : Profile) (t : FpTy) (horizontal subtract : Bool) (i : Inst) : Prog Ctl :=
  match fpOperands i with
  | some (d, s₁, s₂) => do
    legacyAligned prof d s₂
    let w := d.width
    let a ← readOp w s₁
    let b ← readOp w s₂
    let c := mxcsrCtl (← readMxcsr)
    let n := 128 / t.esz
    -- the operands of element `j`, in arithmetic order
    let opds (j : Nat) : Nat × Nat :=
      let h := j / n * n
      let k := j % n
      let v := if k < n / 2 then a else b
      if horizontal then
        ((elem t.esz v (h + (k % (n / 2)) * 2)).toNat, (elem t.esz v (h + (k % (n / 2)) * 2 + 1)).toNat)
      else ((elem t.esz a j).toNat, (elem t.esz b j).toNat)
    -- whether element `j` is a `HADD` pair of two NaNs whose result depends on their order
    let ordered (j : Nat) : Bool :=
      let a := t.fmt.decode (opds j).1
      let b := t.fmt.decode (opds j).2
      a.isNaN && b.isNaN && (t.fmt.nanResult a b).1 != (t.fmt.nanResult b a).1
    let swaps ← (List.range (w / t.esz)).mapM fun j =>
      if horizontal && !subtract && ordered j then do
        let k ← choice 1
        Pure.pure (k.val == 1)
      else Pure.pure false
    let (r, fl) := fpLanes w t.esz fun j =>
      let (x, y) := if swaps.getD j false then ((opds j).2, (opds j).1) else opds j
      fpBinElem t.fmt c (if (if horizontal then subtract else j % 2 = 0)
        then FFormat.sub else FFormat.add) x y
    simdDone prof fl (writeOp d r)
  | _ => formNotModelled i

/-! ## Comparisons -/

/-- Whether compare predicate `p` (the immediate's bits 3–0; SDM Vol. 2, "CMPPD", Table 3-8) holds
for outcome `o`. Each of the sixteen predicates is a set of outcomes, here a mask of bits for
less (1), equal (2), greater (4) and unordered (8): `EQ`, `LT`, `LE`, `UNORD`, `NEQ`, `NLT`, `NLE`,
`ORD`, `EQ_U`, `NGE`, `NGT`, `FALSE`, `NEQ_O`, `GE`, `GT`, `TRUE`. -/
def cmpHolds (p : Nat) (o : FOrder) : Bool :=
  let mask := [2, 1, 3, 8, 13, 14, 12, 7, 10, 9, 11, 0, 5, 6, 4, 15].getD (p % 16) 0
  let bit := match o with | .lt => 1 | .eq => 2 | .gt => 4 | .unordered => 8
  mask &&& bit != 0

/-- Whether compare predicate `p` (0–31) signals: raises the invalid-operation condition for a quiet
NaN operand too (SDM Vol. 2, "CMPPD", Table 3-8, the "Signals #IA on QNaN" column): `LT`, `LE`, `NLT`,
`NLE`, `NGE`, `NGT`, `GE`, `GT` (predicates 1, 2, 5, 6, 9, 10, 13, 14) do, the others not; predicates
16–31 are 0–15 with this reversed. A signaling NaN raises it for every predicate. -/
def cmpSignals (p : Nat) : Bool := (p % 4 = 1 || p % 4 = 2) != (p / 16 % 2 = 1)

/-- One element of `CMPPS` ... with predicate `p`: all ones if the predicate holds for the operands,
else 0 (SDM Vol. 2, "CMPPS", Operation). -/
def FFormat.cmpElem (f : FFormat) (c : FCtl) (p : Nat) (x y : Nat) : Nat × FFlags :=
  let (a, da) := f.operand c x
  let (b, db) := f.operand c y
  let o := fcompare a b
  let ie := a.isSNaN || b.isSNaN || (cmpSignals p && o = .unordered)
  (if cmpHolds p o then 2 ^ f.width - 1 else 0, FFlags.withDenormal { ie } (a.isNaN || b.isNaN) (da || db))

/-- `CMPPS`, `CMPPD`, `CMPSS`, `CMPSD` with predicate `imm8` (`FFormat.cmpElem`): a legacy form takes
predicates 0–7 (bits 2–0), a VEX form predicates 0–31 (bits 4–0). The manuals differ on the immediate's other
bits: the APM's legacy form "uses only bits [2:0] of the 8-bit immediate operand and functions as if imm[4:3]
are 00b", its VEX form "uses bits [4:0]" (APM Vol. 4, "CMPPS", "CMPPD", "Immediate Operand Encoding"; "CMPSS",
"CMPSD": the comparison type "is specified by bits [2:0]", for the VEX forms "bits [4:0]"; an AMD Zen 4 does
so in hardware measurements), while the SDM calls bits 7–3 of a legacy form's immediate
and bits 7–5 of a VEX form's reserved (SDM Vol. 2, "CMPPS": "Bits 3 through 7 of the immediate are reserved",
"Bits 5 through 7 of the immediate are reserved"). So on an AMD processor those bits are ignored, and on an
Intel processor an immediate that sets one is not modelled. -/
def Sem.fpCmp (prof : Profile) (t : FpTy) (i : Inst) : Prog Ctl :=
  let reserved : Prog Ctl := unmodelled (.feature "CMPPS/CMPPD/CMPSS/CMPSD: reserved immediate bits on Intel")
  match i.ops with
  | [d, s, .imm _ k] =>
    if k < 8 || prof.vendor = .amd then fpBinary prof t (fun f c => f.cmpElem c (k % 8)) { i with ops := [d, s] }
    else reserved
  | [d, s₁, s₂, .imm _ k] =>
    if k < 32 || prof.vendor = .amd then
      fpBinary prof t (fun f c => f.cmpElem c (k % 32)) { i with ops := [d, s₁, s₂] }
    else reserved
  | _ => formNotModelled i

/-- `COMISS`, `COMISD` (`signal`) and `UCOMISS`, `UCOMISD`, legacy and VEX: compare element 0 of the
two operands and set `ZF`, `PF`, `CF` to 111 for unordered, 000 for greater, 001 for less, 100 for
equal, and clear `OF`, `SF`, `AF` (SDM Vol. 2, "COMISD", "UCOMISD", Operation). The invalid-operation
condition comes with any NaN operand for `COMIS*`, with a signaling one only for `UCOMIS*` (SDM
Vol. 1, 11.5.2.1). With an unmasked exception `RFLAGS` is not changed. -/
def Sem.fpComi (prof : Profile) (t : FpTy) (signal : Bool) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [s₁, s₂] => do
    let x ← readOp t.esz s₁
    let y ← readOp t.esz s₂
    let c := mxcsrCtl (← readMxcsr)
    let (a, da) := t.fmt.operand c x.toNat
    let (b, db) := t.fmt.operand c y.toNat
    let o := fcompare a b
    let ie := a.isSNaN || b.isSNaN || (signal && o = .unordered)
    let fl := FFlags.withDenormal { ie } (a.isNaN || b.isNaN) (da || db)
    let (zf, pf, cf) := match o with
      | .unordered => (true, true, true)
      | .gt => (false, false, false)
      | .lt => (false, false, true)
      | .eq => (true, false, false)
    let f ← readFlags
    simdDone prof fl (writeFlags { f with zf, pf, cf, of := false, sf := false, af := false })
  | _ => formNotModelled i

/-! ## Conversions -/

/-- The integer a `w`-bit two's complement value encodes. -/
def signedOf {w : Nat} (v : BitVec w) : Int := v.toInt

/-- `CVTSI2SS`, `CVTSI2SD` and their VEX forms: the signed 32- or 64-bit integer source (by
`REX.W`/`VEX.W`) converted to element 0 (`FFormat.ofInt`, rounded by `MXCSR.RC`); the other bits as
for the scalar arithmetic forms (SDM Vol. 2, "CVTSI2SD", "CVTSI2SS"). -/
def Sem.fpCvtsi2 (prof : Profile) (t : FpTy) (i : Inst) : Prog Ctl :=
  match fpOperands i with
  | none => formNotModelled i
  | some (d, s₁, s₂) => do
    let a ← readOp 128 s₁
    let v ← readOp s₂.width s₂
    let c := mxcsrCtl (← readMxcsr)
    let (r, fl) := t.fmt.ofInt c.rc (signedOf v)
    simdDone prof fl (writeOp d ((a >>> t.esz <<< t.esz) ||| BitVec.ofNat 128 r))

/-- `CVTSS2SI`, `CVTSD2SI` (rounded by `MXCSR.RC`) and `CVTTSS2SI`, `CVTTSD2SI` (`trunc`: toward
zero), legacy and VEX: element 0 of the source converted to a signed integer of the destination's
size (`FNum.toInt`; SDM Vol. 2, "CVTSD2SI", "CVTTSD2SI", ...). -/
def cvtToInt (prof : Profile) (t : FpTy) (trunc : Bool) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do
    let x ← readOp t.esz s
    let c := mxcsrCtl (← readMxcsr)
    let (a, _) := t.fmt.operand c x.toNat
    let (r, fl) := a.toInt d.width (if trunc then .zero else c.rc)
    simdDone prof fl (writeOp d (BitVec.ofNat 64 r))
  | _ => formNotModelled i

/-- `CVTSS2SI`, `CVTSD2SI` (`cvtToInt`). -/
def Sem.fpCvt2si (prof : Profile) (t : FpTy) (i : Inst) : Prog Ctl := cvtToInt prof t false i
/-- `CVTTSS2SI`, `CVTTSD2SI` (`cvtToInt`). -/
def Sem.fpCvtt2si (prof : Profile) (t : FpTy) (i : Inst) : Prog Ctl := cvtToInt prof t true i

/-- One element converted from format `g` to format `f` (`FFormat.convert`), with the
denormal-operand condition. -/
def FFormat.convElem (f g : FFormat) (c : FCtl) (x : Nat) : Nat × FFlags :=
  let (a, da) := g.operand c x
  let (r, fl) := f.convert g c a
  (r, fl.withDenormal a.isNaN da)

/-- A scalar conversion of element 0 of the second source, of format `g`, to element 0 of the
destination, of format `f`; the destination's other bits up to 127 as for the scalar arithmetic
forms. -/
def fpConvScalar (prof : Profile) (f g : FFormat) (i : Inst) : Prog Ctl :=
  match fpOperands i with
  | none => formNotModelled i
  | some (d, s₁, s₂) => do
    let a ← readOp 128 s₁
    let b ← readOp g.width s₂
    let c := mxcsrCtl (← readMxcsr)
    let (r, fl) := f.convElem g c b.toNat
    simdDone prof fl (writeOp d ((a >>> f.width <<< f.width) ||| BitVec.ofNat 128 r))

/-- `CVTSS2SD`: element 0 of the source widened from single to double (`fpConvScalar`; SDM Vol. 2,
"CVTSS2SD"). -/
def Sem.cvtss2sd (prof : Profile) (i : Inst) : Prog Ctl := fpConvScalar prof binary64 binary32 i
/-- `CVTSD2SS`: element 0 of the source rounded from double to single (`fpConvScalar`; SDM Vol. 2,
"CVTSD2SS"). -/
def Sem.cvtsd2ss (prof : Profile) (i : Inst) : Prog Ctl := fpConvScalar prof binary32 binary64 i

/-- A packed conversion of `n` elements of `ein` bits (the source's low `n · ein` bits) to `n`
elements of `eout` bits, each `g` of its source element; the destination's bits above them are
cleared (legacy forms keep bits 511–128). A widening conversion fills the destination (`n` from its
width), a narrowing one reads the whole source (`n` from its width). `aligned`: a legacy form of
exception type 2. -/
def fpConvPacked (prof : Profile) (aligned : Bool) (ein eout : Nat) (g : FCtl → Nat → Nat × FFlags)
    (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do
    if aligned then legacyAligned prof d s
    let n := if ein ≤ eout then d.width / eout else s.width / ein
    let b ← readOp (n * ein) s
    let c := mxcsrCtl (← readMxcsr)
    let (r, fl) := fpLanes (n * eout) eout fun j => g c (elem ein b j).toNat
    simdDone prof fl (writeOp d (r.setWidth (max 128 (n * eout))))
  | _ => formNotModelled i

/-- `CVTPS2PD` (SDM Vol. 2, "CVTPS2PD"): two (VEX.256: four) singles from the low half of the source
widened to doubles; exception type 3. -/
def Sem.cvtps2pd (prof : Profile) (i : Inst) : Prog Ctl :=
  fpConvPacked prof false 32 64 (binary64.convElem binary32) i
/-- `CVTPD2PS` (SDM Vol. 2, "CVTPD2PS"): the source's doubles rounded to singles in the destination's
low half, its other bits cleared; exception type 2. -/
def Sem.cvtpd2ps (prof : Profile) (i : Inst) : Prog Ctl :=
  fpConvPacked prof true 64 32 (binary32.convElem binary64) i
/-- `CVTDQ2PS` (SDM Vol. 2, "CVTDQ2PS"): signed doublewords converted to singles, rounded by
`MXCSR.RC`; exception type 2. -/
def Sem.cvtdq2ps (prof : Profile) (i : Inst) : Prog Ctl :=
  fpConvPacked prof true 32 32 (fun c x => binary32.ofInt c.rc (signedOf (BitVec.ofNat 32 x))) i
/-- `CVTDQ2PD` (SDM Vol. 2, "CVTDQ2PD"): two (VEX.256: four) signed doublewords from the low half
converted to doubles, exactly; exception type 5. -/
def Sem.cvtdq2pd (prof : Profile) (i : Inst) : Prog Ctl :=
  fpConvPacked prof false 32 64 (fun c x => binary64.ofInt c.rc (signedOf (BitVec.ofNat 32 x))) i
/-- `CVTPS2DQ` (rounded by `MXCSR.RC`) and `CVTTPS2DQ` (`trunc`) (SDM Vol. 2, "CVTPS2DQ",
"CVTTPS2DQ"): singles converted to signed doublewords (`FNum.toInt`); exception type 2. -/
def fpCvtps2dq (prof : Profile) (trunc : Bool) (i : Inst) : Prog Ctl :=
  fpConvPacked prof true 32 32 (fun c x => (binary32.operand c x).1.toInt 32 (if trunc then .zero else c.rc)) i
/-- `CVTPS2DQ` (`fpCvtps2dq`). -/
def Sem.cvtps2dq (prof : Profile) (i : Inst) : Prog Ctl := fpCvtps2dq prof false i
/-- `CVTTPS2DQ` (`fpCvtps2dq`). -/
def Sem.cvttps2dq (prof : Profile) (i : Inst) : Prog Ctl := fpCvtps2dq prof true i
/-- `CVTPD2DQ` (rounded by `MXCSR.RC`) and `CVTTPD2DQ` (`trunc`) (SDM Vol. 2, "CVTPD2DQ",
"CVTTPD2DQ"): doubles converted to signed doublewords in the destination's low half, its other bits
cleared; exception type 2. -/
def fpCvtpd2dq (prof : Profile) (trunc : Bool) (i : Inst) : Prog Ctl :=
  fpConvPacked prof true 64 32 (fun c x => (binary64.operand c x).1.toInt 32 (if trunc then .zero else c.rc)) i
/-- `CVTPD2DQ` (`fpCvtpd2dq`). -/
def Sem.cvtpd2dq (prof : Profile) (i : Inst) : Prog Ctl := fpCvtpd2dq prof false i
/-- `CVTTPD2DQ` (`fpCvtpd2dq`). -/
def Sem.cvttpd2dq (prof : Profile) (i : Inst) : Prog Ctl := fpCvtpd2dq prof true i

/-! ## `MXCSR` -/

/-- `LDMXCSR m32` and `VLDMXCSR`: load `MXCSR`; `#GP(0)` if the value sets a bit the processor does
not support (`Profile.mxcsrOk`; SDM Vol. 2, "LDMXCSR"). Setting a flag whose exception is unmasked
raises nothing (SDM Vol. 1, 10.2.3.1). -/
def Sem.ldmxcsr (prof : Profile) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [s] => do
    let v ← readOp 32 s
    if prof.mxcsrOk v then do writeMxcsr v; done else throw (.gp 0)
  | _ => formNotModelled i

/-- `STMXCSR m32` and `VSTMXCSR`: store `MXCSR` (SDM Vol. 2, "STMXCSR"). -/
def Sem.stmxcsr (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d] => do
    let v ← readMxcsr
    writeOp d v
    done
  | _ => formNotModelled i

/-- Execute floating-point instruction `i` of mnemonic `m` on processor `prof`, with `rip` already
advanced past it. -/
def execFp (prof : Profile) (m : FpMn) (i : Inst) : Prog Ctl :=
  match m with
  | .round t => Sem.fpRound prof t i
  | .fma t order np sa => Sem.fpFma prof t order np sa i
  | .addsub t => Sem.fpSse3 prof t false false i
  | .hadd t => Sem.fpSse3 prof t true false i
  | .hsub t => Sem.fpSse3 prof t true true i
  | .add t => Sem.fpAdd prof t i | .sub t => Sem.fpSub prof t i | .mul t => Sem.fpMul prof t i
  | .div t => Sem.fpDiv prof t i | .min t => Sem.fpMin prof t i | .max t => Sem.fpMax prof t i
  | .sqrt t => Sem.fpSqrt prof t i | .cmp t => Sem.fpCmp prof t i
  | .comi t => Sem.fpComi prof t true i | .ucomi t => Sem.fpComi prof t false i
  | .cvtsi2 t => Sem.fpCvtsi2 prof t i | .cvt2si t => Sem.fpCvt2si prof t i
  | .cvtt2si t => Sem.fpCvtt2si prof t i
  | .cvtss2sd => Sem.cvtss2sd prof i | .cvtsd2ss => Sem.cvtsd2ss prof i
  | .cvtps2pd => Sem.cvtps2pd prof i | .cvtpd2ps => Sem.cvtpd2ps prof i
  | .cvtdq2ps => Sem.cvtdq2ps prof i | .cvtps2dq => Sem.cvtps2dq prof i
  | .cvttps2dq => Sem.cvttps2dq prof i | .cvtdq2pd => Sem.cvtdq2pd prof i
  | .cvtpd2dq => Sem.cvtpd2dq prof i | .cvttpd2dq => Sem.cvttpd2dq prof i
  | .ldmxcsr => Sem.ldmxcsr prof i | .stmxcsr => Sem.stmxcsr i

end ZellicX86
