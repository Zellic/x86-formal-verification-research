import ZellicX86.Spec.Semantics.Basic
/-!
# Instruction semantics: arithmetic and logic

Each case follows the "Operation" and "Flags Affected" sections of the instruction's page in
Intel SDM Vol. 2 (rev. 092); where AMD APM Vol. 3 (rev. 4.10) differs, the case says so. Flags the
manuals call undefined are left open: each is a value the environment chooses (`Prog.undefinedBit`), and a
theorem holds for every choice. Forms not implemented stop with `notModelled`.
-/
namespace ZellicX86
open Decode Prog

/-- `IMUL d, a, b` with two or three operands: `d := a * b` truncated to `w` bits, `CF` and `OF`
set iff the signed product does not fit, `SF`, `ZF`, `AF`, `PF` undefined (SDM, APM "IMUL"). -/
def imulTrunc (w : Nat) (d a b : Opd) : Prog Unit := do
  let x ← readOp w a
  let y ← readOp w b
  let f ← readFlags
  let p := x.signExtend (2 * w) * y.signExtend (2 * w)
  let r := p.setWidth w
  let wide := p != r.signExtend (2 * w)
  let sf ← undefinedBit
  let zf ← undefinedBit
  let af ← undefinedBit
  let pf ← undefinedBit
  writeOp d r
  writeFlags { f with cf := wide, of := wide, sf := sf, zf := zf, af := af, pf := pf }

/-- The dividend of a `w`-bit `DIV` or `IDIV`: `AX` for bytes, else `rDX:rAX`. -/
def dividend (w : Nat) : Prog (BitVec (2 * w)) :=
  if w = 8 then do
    let ax ← readOp 16 (accOf 16 0)
    Pure.pure (ax.setWidth (2 * w))
  else do
    let lo ← readOp w (accOf w 0)
    let hi ← readOp w (accOf w 2)
    Pure.pure ((hi ++ lo).setWidth (2 * w))

/-- Store the quotient `q` and remainder `r` of a `w`-bit `DIV` or `IDIV` (`AL` and `AH` for
bytes, else `rAX` and `rDX`). All six status flags are undefined (SDM, APM "DIV", "IDIV"). -/
def divResult (w : Nat) (q r : BitVec w) : Prog Unit := do
  let f ← readFlags
  let cf ← undefinedBit
  let of ← undefinedBit
  let sf ← undefinedBit
  let zf ← undefinedBit
  let af ← undefinedBit
  let pf ← undefinedBit
  if w = 8 then do
    writeOp (accOf 8 0) q
    writeOp (.reg ⟨8, 0, true⟩) r
  else do
    writeOp (accOf w 0) q
    writeOp (accOf w 2) r
  writeFlags { f with cf := cf, of := of, sf := sf, zf := zf, af := af, pf := pf }

/-! ## The instructions

One definition per instruction, `Sem.<mnemonic>`, from the operands `i.ops` the decoder gives
and the operand size `i.opsz`; `exec` (`Spec/Semantics.lean`) chooses it by mnemonic. -/

/-- `ADD d, s`: `d := d + s` with its flags (SDM Vol. 2, "ADD"). -/
def Sem.add (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do alu i.opsz d s true (addOp false); done
  | _ => formNotModelled i

/-- `ADC d, s`: `d := d + s + CF` with its flags (SDM Vol. 2, "ADC"). -/
def Sem.adc (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do alu i.opsz d s true fun x y f => addOp f.cf x y f; done
  | _ => formNotModelled i

/-- `SUB d, s`: `d := d - s` with its flags (SDM Vol. 2, "SUB"). -/
def Sem.sub (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do alu i.opsz d s true (subOp false); done
  | _ => formNotModelled i

/-- `SBB d, s`: `d := d - (s + CF)` with its flags (SDM Vol. 2, "SBB"). -/
def Sem.sbb (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do alu i.opsz d s true fun x y f => subOp f.cf x y f; done
  | _ => formNotModelled i

/-- `CMP a, b`: the flags of `a - b` (SDM Vol. 2, "CMP"). -/
def Sem.cmp (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do alu i.opsz d s false (subOp false); done
  | _ => formNotModelled i

/-- `AND d, s` (SDM Vol. 2, "AND"). -/
def Sem.and (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do alu i.opsz d s true (logicOp (· &&& ·)); done
  | _ => formNotModelled i

/-- `OR d, s` (SDM Vol. 2, "OR"). -/
def Sem.or (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do alu i.opsz d s true (logicOp (· ||| ·)); done
  | _ => formNotModelled i

/-- `XOR d, s` (SDM Vol. 2, "XOR"). -/
def Sem.xor (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do alu i.opsz d s true (logicOp (· ^^^ ·)); done
  | _ => formNotModelled i

/-- `TEST a, b`: the flags of `a AND b` (SDM Vol. 2, "TEST"). -/
def Sem.test (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do alu i.opsz d s false (logicOp (· &&& ·)); done
  | _ => formNotModelled i

/-- `NOT d`: no flags change (SDM Vol. 2, "NOT"). -/
def Sem.not (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d] => do
    let x ← readOp i.opsz d .write
    writeOp d (~~~x)
    done
  | _ => formNotModelled i

/-- `NEG d`: `0 - d`, with the flags of that subtraction, so `CF = 1` unless `d = 0` (SDM Vol. 2,
"NEG"). -/
def Sem.neg (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d] => do
    let x ← readOp i.opsz d .write
    let f ← readFlags
    let (r, f') ← subOp false 0 x f
    writeOp d r
    writeFlags f'
    done
  | _ => formNotModelled i

/-- `INC d`: as `ADD d, 1`, but `CF` is not affected (SDM Vol. 2, "INC"). -/
def Sem.inc (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d] => do
    let x ← readOp i.opsz d .write
    let f ← readFlags
    let (r, f') ← addOp false x 1 f
    writeOp d r
    writeFlags { f' with cf := f.cf }
    done
  | _ => formNotModelled i

/-- `DEC d`: as `SUB d, 1`, but `CF` is not affected (SDM Vol. 2, "DEC"). -/
def Sem.dec (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d] => do
    let x ← readOp i.opsz d .write
    let f ← readFlags
    let (r, f') ← subOp false x 1 f
    writeOp d r
    writeFlags { f' with cf := f.cf }
    done
  | _ => formNotModelled i

/-- `XADD d, s`: `d := d + s` and `s :=` the old `d`, with the flags of the addition (SDM Vol. 2,
"XADD": `TEMP := SRC + DEST; SRC := DEST; DEST := TEMP`, so with the same register as both
operands it receives the sum). A memory destination's address is resolved before the source
register changes, including when that register is its base or index. With `LOCK` it is replaced atomically
(`Sem.lockXadd`). -/
def Sem.xadd (i : Inst) : Prog Ctl :=
  match i.ops with
  | [.mem dest, s] => do
    let m ← memRef dest
    let x ← read m i.opsz .write
    let y ← readOp i.opsz s
    let f ← readFlags
    let (r, f') ← addOp false x y f
    writeOp s x
    write m i.opsz r
    writeFlags f'
    done
  | [d, s] => do
    let x ← readOp i.opsz d .write
    let y ← readOp i.opsz s
    let f ← readFlags
    let (r, f') ← addOp false x y f
    writeOp s x
    writeOp d r
    writeFlags f'
    done
  | _ => formNotModelled i

/-- A shift or rotate `op d, count` (`shiftRot`). -/
def shiftInst (prof : Profile) (op : ShiftOp) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, c] => do shiftRot prof i.opsz op d c; done
  | _ => formNotModelled i

/-- `SHL`/`SAL` (SDM Vol. 2, "SAL/SAR/SHL/SHR"). -/
def Sem.shl (prof : Profile) (i : Inst) : Prog Ctl := shiftInst prof .shl i
/-- `SHR` (SDM Vol. 2, "SAL/SAR/SHL/SHR"). -/
def Sem.shr (prof : Profile) (i : Inst) : Prog Ctl := shiftInst prof .shr i
/-- `SAR` (SDM Vol. 2, "SAL/SAR/SHL/SHR"). -/
def Sem.sar (prof : Profile) (i : Inst) : Prog Ctl := shiftInst prof .sar i
/-- `ROL` (SDM Vol. 2, "RCL/RCR/ROL/ROR"). -/
def Sem.rol (prof : Profile) (i : Inst) : Prog Ctl := shiftInst prof .rol i
/-- `ROR` (SDM Vol. 2, "RCL/RCR/ROL/ROR"). -/
def Sem.ror (prof : Profile) (i : Inst) : Prog Ctl := shiftInst prof .ror i

/-- `MUL s`, or `IMUL s` (`signed`) with one operand: the product of `rAX` (`AL`) and the source,
twice the operand size wide, in `rDX:rAX` (`AX` for bytes). `CF` and `OF` are set iff the upper
half is needed: nonzero for `MUL`, not the sign extension of the lower half for `IMUL`. `SF`,
`ZF`, `AF`, `PF` are undefined (SDM, APM "MUL", "IMUL"). -/
def mulWide (signed : Bool) (w : Nat) (s : Opd) : Prog Ctl := do
  let y ← readOp w s
  let x ← readOp w (accOf w 0)
  let f ← readFlags
  let p : BitVec (2 * w) := if signed then x.signExtend (2 * w) * y.signExtend (2 * w)
    else x.setWidth (2 * w) * y.setWidth (2 * w)
  let lo := p.setWidth w
  let wide := if signed then p != lo.signExtend (2 * w) else p.extractLsb' w w != 0
  let sf ← undefinedBit
  let zf ← undefinedBit
  let af ← undefinedBit
  let pf ← undefinedBit
  if w = 8 then writeOp (accOf 16 0) p
  else do
    writeOp (accOf w 0) lo
    writeOp (accOf w 2) (p.extractLsb' w w)
  writeFlags { f with cf := wide, of := wide, sf := sf, zf := zf, af := af, pf := pf }
  done

/-- `MUL s` (`mulWide`). -/
def Sem.mul (i : Inst) : Prog Ctl :=
  match i.ops with
  | [s] => mulWide false i.opsz s
  | _ => formNotModelled i

/-- `IMUL` with one operand (`mulWide`), and with two and three operands: the product of the two
sources (the immediate already sign-extended by the decoder) truncated to the operand size
(`imulTrunc`). -/
def Sem.imul (i : Inst) : Prog Ctl :=
  match i.ops with
  | [s] => mulWide true i.opsz s
  | [d, s] => do imulTrunc i.opsz d d s; done
  | [d, s, imm] => do imulTrunc i.opsz d s imm; done
  | _ => formNotModelled i

/-- `DIV s`: divide `rDX:rAX` (`AX` for bytes) by the source; the quotient goes to `rAX` (`AL`),
the remainder to `rDX` (`AH`). A zero divisor or a quotient that does not fit the operand size
raises `#DE` (SDM, APM "DIV"). -/
def Sem.div (i : Inst) : Prog Ctl :=
  let w := i.opsz
  match i.ops with
  | [s] => do
    let y ← readOp w s
    let n ← dividend w
    if y = 0 then throw .de else
    let q := n.toNat / y.toNat
    if 2 ^ w ≤ q then throw .de else
    divResult w (BitVec.ofNat w q) (BitVec.ofNat w (n.toNat % y.toNat))
    done
  | _ => formNotModelled i

/-- `IDIV s`: as `DIV`, signed: the quotient is truncated towards zero, and the remainder has the
sign of the dividend (SDM, APM "IDIV"). -/
def Sem.idiv (i : Inst) : Prog Ctl :=
  let w := i.opsz
  match i.ops with
  | [s] => do
    let y ← readOp w s
    let n ← dividend w
    if y = 0 then throw .de else
    let q := n.toInt.tdiv y.toInt
    if q < -2 ^ (w - 1) ∨ 2 ^ (w - 1) ≤ q then throw .de else
    divResult w (BitVec.ofInt w q) (BitVec.ofInt w (n.toInt.tmod y.toInt))
    done
  | _ => formNotModelled i

/-- `CBW`, `CWDE`, `CDQE` by operand size: sign-extend the lower half of `rAX` (`AL`, `AX`,
`EAX`) into `AX`, `EAX` or `RAX`; no flags change (SDM Vol. 2, "CBW/CWDE/CDQE"). -/
def Sem.cbw (i : Inst) : Prog Ctl := do
  let w := i.opsz
  let x ← readOp (w / 2) (accOf (w / 2) 0)
  writeOp (accOf w 0) (x.signExtend w)
  done

/-- `CWD`, `CDQ`, `CQO` by operand size: fill `DX`, `EDX` or `RDX` with the sign bit of `AX`,
`EAX` or `RAX`; no flags change (SDM Vol. 2, "CWD/CDQ/CQO"). -/
def Sem.cwd (i : Inst) : Prog Ctl := do
  let w := i.opsz
  let x ← readOp w (accOf w 0)
  writeOp (accOf w 2) (if x.msb then BitVec.allOnes w else 0)
  done

/-- The remainder of the polynomial `a` divided by the polynomial `p` of degree `d`, over the field
of two elements (bit `i` of a number the coefficient of `Xⁱ`; the SDM's `MOD2`, "Remainder from
Polynomial division modulus 2"): the terms of degree `d + k − 1` down to `d` are cancelled in turn,
each by `p` multiplied by the power of `X` that brings its leading term there, so `a` must have
degree below `d + k`. -/
def polyMod2 (p d : Nat) : (k : Nat) → (a : Nat) → Nat
  | 0, a => a
  | k + 1, a => polyMod2 p d k (if a.testBit (d + k) then a ^^^ (p <<< k) else a)

/-- One step of `CRC32` on an `n`-bit source `src` with the accumulated value `crc` (SDM Vol. 2A,
"CRC32", Operation, for each source width): the source and the value bit-reflected (`BIT_REFLECT`,
`BitVec.reverse`), the source's times `X³²` added to the value's times `Xⁿ`, the remainder modulo
the CRC-32C polynomial `11EDC6F41H`, reflected back. -/
def crc32Step {n : Nat} (crc : BitVec 32) (src : BitVec n) : BitVec 32 :=
  let temp5 := (src.reverse.toNat <<< 32) ^^^ (crc.reverse.toNat <<< n)
  (BitVec.ofNat 32 (polyMod2 0x11EDC6F41 32 n temp5)).reverse

/-- `CRC32 r32/r64, r/m8/16/32/64`: the destination's low 32 bits accumulated over the source
(`crc32Step`), written zero-extended to the destination's width; no flags change (SDM Vol. 2A,
"CRC32", 3-205 to 3-207; AMD APM Vol. 3, "CRC32", pp. 173–175). The decoder checks SSE4.2 and
rejects `LOCK` (`#UD` in both manuals). The APM's description says "bit-wise inverted" where the
SDM's operation reflects the bits (`BIT_REFLECT`); an AMD Zen 4 reflects in hardware measurements. -/
def Sem.crc32 (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do
    let crc ← readOp 32 d
    let v ← readOp s.width s
    writeOp d ((crc32Step crc v).setWidth d.width)
    done
  | _ => formNotModelled i

end ZellicX86
