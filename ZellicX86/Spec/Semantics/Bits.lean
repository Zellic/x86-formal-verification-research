import ZellicX86.Spec.Semantics.Basic
/-!
# Instruction semantics: bit operations

`BT`, `BTS`, `BTR`, `BTC`, `BSF`, `BSR`, `TZCNT`, `LZCNT`, `SHLD`, `SHRD`, and the BMI1/BMI2
instructions on general registers (`ANDN`, `BEXTR`, `BLSI`, `BLSMSK`, `BLSR`, `BZHI`, `SHLX`,
`SHRX`, `SARX`, `RORX`, `PDEP`, `PEXT`, `MULX`). Each case follows the
"Operation" and "Flags Affected" sections of the instruction's page in Intel SDM Vol. 2 (rev. 092)
and AMD APM Vol. 3 (rev. 4.10); where the two differ, the case says so and takes what both allow,
or branches on the vendor. Flags the manuals call undefined are left open: each is a value the environment
chooses (`Prog.undefinedBit`), and a theorem holds for every choice. Forms not implemented stop with `notModelled`.
-/
namespace ZellicX86
open Decode Prog

/-- The index of the least significant set bit of `x`, or `w` if `x = 0`. -/
def lowestSetBit {w : Nat} (x : BitVec w) : Nat :=
  ((List.range w).find? fun i => x.getLsbD i).getD w

/-- The index of the most significant set bit of `x`, or `w` if `x = 0`. -/
def highestSetBit {w : Nat} (x : BitVec w) : Nat :=
  ((List.range w).reverse.find? fun i => x.getLsbD i).getD w

/-- What `BTS`, `BTR`, `BTC` do to the selected bit (`BT` leaves it). -/
inductive BitChange | keep | set | reset | complement

/-- The bit `k` of `x` set, cleared or complemented (`ch`); `x` itself for `keep`. -/
def BitChange.apply {w : Nat} (ch : BitChange) (k : Nat) (x : BitVec w) : BitVec w :=
  match ch with
  | .set => x ||| (1 <<< k)
  | .reset => x &&& ~~~((1 : BitVec w) <<< k)
  | .complement => x ^^^ (1 <<< k)
  | .keep => x

/-- `BT`, `BTS`, `BTR`, `BTC` with a memory bit base `x` and bit offset `o` (a register or an
immediate), locked (`LOCK BTS`, ...) if `lock`. Bit 0 of the byte at the operand's address is
bit 0 of the bit string (SDM, APM "BT"). An immediate offset is taken modulo the operand size
`w`; a register offset is signed and not reduced: it selects bit `offset mod w` of the `w`-bit
word at `EA + (w / 8) * (offset SAR log2 w)`, anywhere from `2 ^ (w - 1)` bits before to
`2 ^ (w - 1) - 1` bits after the operand's address.

Which bytes the processor accesses: the APM says the `w / 8` bytes of that word. The SDM says it
"may access" 2 bytes (16-bit) or 4 bytes (32-bit) at `EA + 2 * (offset DIV 16)` or
`EA + 4 * (offset DIV 32)`, "even when only a single byte needs to be accessed", and gives no
rule for 64 bits. Every such access is a run of bytes inside the word that contains the byte
holding the bit; such a run lies on one page (then it faults as that byte does) or on the same
two pages as the word (then it faults as the word does). So on Intel the access is the byte or
the word, a `pick` (alternative 1: the byte); on AMD the word. The open choice is drawn on both vendors, so the
sequence of choices does not depend on the vendor; where the vendor fixes the behaviour, it is not used. The flags
are as with a register bit base. -/
def bitMem (prof : Profile) (ch : BitChange) (lock : Bool) (w : Nat) (x : MemOp) (o : Opd) :
    Prog Ctl := do
  let off ← readOp w o
  let m ← memRef x
  let k := off.toNat % w
  -- the word holding the bit: an immediate offset stays in the operand's own word
  let q : BitVec 64 := match o with
    | .imm _ _ => 0
    | _ => (off.signExtend 64).sshiftRight (if w = 16 then 4 else if w = 32 then 5 else 6)
  let a := m.addr + q * BitVec.ofNat 64 (w / 8)
  let narrow ← choice 1
  let f ← readFlags
  let of ← undefinedBit
  let sf ← undefinedBit
  let af ← undefinedBit
  let pf ← undefinedBit
  let zf ← undefinedBit
  let cf ← if prof.vendor = .intel ∧ narrow.val = 1 then
      accessBit ch lock ⟨a + BitVec.ofNat 64 (k / 8), m.stack⟩ 8 (k % 8)
    else accessBit ch lock ⟨a, m.stack⟩ w k
  writeFlags { f with cf := cf, of := of, sf := sf, af := af, pf := pf,
                      zf := if prof.vendor = .intel then f.zf else zf }
  done
where
  /-- Bit `k` of the `n`-bit value at `r`, after which it is changed (`ch`): a read for `BT`, a
  locked read-modify-write with `LOCK`, else a read for writing and a write. -/
  accessBit (ch : BitChange) (lock : Bool) (r : MemRef) (n k : Nat) : Prog Bool :=
    match ch with
    | .keep => do let v ← read r n; Pure.pure (v.getLsbD k)
    | _ => if lock then do
        let v ← lockedRmw r n (ch.apply k)
        Pure.pure (v.getLsbD k)
      else do
        let v ← read r n .write
        write r n (ch.apply k v)
        Pure.pure (v.getLsbD k)

/-- `BT`, `BTS`, `BTR`, `BTC`: the bit offset (a register or an
immediate) is taken modulo the operand size with a register bit base; `CF` receives the selected
bit, and the instruction sets, clears or complements it (`ch`). `OF`, `SF`, `AF`, `PF` are
undefined. `ZF` is unaffected on Intel (SDM "BT", "BTS", "BTR", "BTC", Flags Affected) and
undefined on AMD (APM, rFLAGS Affected). A memory bit base is `bitMem`. -/
def bitTest (prof : Profile) (ch : BitChange) (i : Inst) : Prog Ctl :=
  let w := i.opsz
  match i.ops with
  | [.reg r, o] => do
    let d := Opd.reg r
    let x ← readOp w d
    let off ← readOp w o
    let k := off.toNat % w
    let bit : BitVec w := 1 <<< k
    let f ← readFlags
    let of ← undefinedBit
    let sf ← undefinedBit
    let af ← undefinedBit
    let pf ← undefinedBit
    let zf ← undefinedBit
    match ch with
    | .set => writeOp d (x ||| bit)
    | .reset => writeOp d (x &&& ~~~bit)
    | .complement => writeOp d (x ^^^ bit)
    | .keep => Pure.pure ()
    writeFlags { f with cf := x.getLsbD k, of := of, sf := sf, af := af, pf := pf,
                        zf := if prof.vendor = .intel then f.zf else zf }
    done
  | [.mem x, o] => bitMem prof ch false w x o
  | _ => formNotModelled i

/-- `BT` (`bitTest`). -/
def Sem.bt (prof : Profile) (i : Inst) : Prog Ctl := bitTest prof .keep i
/-- `BTS` (`bitTest`). -/
def Sem.bts (prof : Profile) (i : Inst) : Prog Ctl := bitTest prof .set i
/-- `BTR` (`bitTest`). -/
def Sem.btr (prof : Profile) (i : Inst) : Prog Ctl := bitTest prof .reset i
/-- `BTC` (`bitTest`). -/
def Sem.btc (prof : Profile) (i : Inst) : Prog Ctl := bitTest prof .complement i

/-- `BSF` (`forward`), `BSR`: the index of the least or most significant set bit of the source. With a zero source
`ZF` is set and the destination is unmodified (APM "BSF", "BSR"; SDM rev. 092, which adds that on some older
processors a 32-bit operand size may clear bits 63–32 of the destination; on Intel whether it does is left open).
`CF`, `OF`, `SF`, `AF`, `PF`: undefined on AMD (APM); on Intel one of the SDM's two behaviours, a `pick`: alternative
0, `CF`, `OF`, `SF`, `AF` cleared and `PF` set iff the whole source (not its low byte) has an even number of set bits;
alternative 1, all five unmodified, as "on some older processors", which the SDM does not name. The open values are
drawn on both vendors, so the sequence of choices does not depend on the vendor; where the vendor fixes the
behaviour, they are not used. -/
def bitScan (prof : Profile) (forward : Bool) (i : Inst) : Prog Ctl :=
  let w := i.opsz
  match i.ops with
  | [.reg r, s] => do
    let x ← readOp w s
    let f ← readFlags
    let cf ← undefinedBit
    let of ← undefinedBit
    let sf ← undefinedBit
    let af ← undefinedBit
    let pf ← undefinedBit
    let clear ← undefinedBit
    let older ← choice 1
    if x = 0 then do
      let old ← readReg (regOf r.num)
      let upperCleared := w = 32 && prof.vendor = .intel && clear
      writeReg (regOf r.num) (if upperCleared then (old.setWidth 32).setWidth 64 else old)
    else
      writeOp (.reg r) (BitVec.ofNat w (if forward then lowestSetBit x else highestSetBit x))
    -- on Intel: the SDM's flags (alternative 0), or the five unmodified (1)
    let intel (sdm old : Bool) (amd : Bool) : Bool :=
      if prof.vendor = .intel then (if older.val = 1 then old else sdm) else amd
    let even := (List.range w).foldl (fun p j => p != x.getLsbD j) true
    writeFlags { f with cf := intel false f.cf cf, of := intel false f.of of, sf := intel false f.sf sf,
                        af := intel false f.af af, pf := intel even f.pf pf, zf := x == 0 }
    done
  | _ => formNotModelled i

/-- `BSF` (`bitScan`). -/
def Sem.bsf (prof : Profile) (i : Inst) : Prog Ctl := bitScan prof true i
/-- `BSR` (`bitScan`). -/
def Sem.bsr (prof : Profile) (i : Inst) : Prog Ctl := bitScan prof false i

/-- `TZCNT` (`trailing`), `LZCNT`: the number of trailing or leading zero bits of the source (the
operand size for a zero source); `CF` is set iff the source is zero, `ZF` iff the result is zero;
`OF`, `SF`, `AF`, `PF` are undefined (SDM, APM "TZCNT", "LZCNT"). The decoder gives these only with
BMI1 or LZCNT; without, the encodings are `BSF` and `BSR`. -/
def countZeros (trailing : Bool) (i : Inst) : Prog Ctl :=
  let w := i.opsz
  match i.ops with
  | [d, s] => do
    let x ← readOp w s
    let f ← readFlags
    let of ← undefinedBit
    let sf ← undefinedBit
    let af ← undefinedBit
    let pf ← undefinedBit
    let n := if trailing then lowestSetBit x
      else if x = 0 then w else w - 1 - highestSetBit x
    writeOp d (BitVec.ofNat w n)
    writeFlags { f with cf := x == 0, zf := n == 0, of := of, sf := sf, af := af, pf := pf }
    done
  | _ => formNotModelled i

/-- `TZCNT` (`countZeros`). -/
def Sem.tzcnt (i : Inst) : Prog Ctl := countZeros true i
/-- `LZCNT` (`countZeros`). -/
def Sem.lzcnt (i : Inst) : Prog Ctl := countZeros false i

/-- `SHLD` (`left`), `SHRD`: shift the destination left (right) by the count, filling from the
source's high (low) bits (SDM, APM "SHLD", "SHRD"). The count is masked to 5 bits, or 6 with a
64-bit operand. `CF` is the last bit shifted out of the destination, `OF` (count 1 only) whether
the sign changed, `SF`, `ZF`, `PF` from the result; `AF` is undefined, and `OF` for a count above
1. A count above the operand size (16-bit forms only) leaves the result undefined, and the flags: all
undefined on Intel (SDM: "If the count is greater than the operand size, the flags are undefined"); on
AMD `SF`, `ZF`, `PF` from that result and `CF` undefined (APM: the result undefined, the table's `SF`,
`ZF`, `PF`, `CF` modified, with no rule past the width for `CF`'s "last bit shifted out"; an AMD Zen 4
clears `CF` and gives `SF`, `ZF`, `PF` of its result in hardware measurements). The open values are drawn on
both vendors, so the sequence of choices does not depend on the vendor; where the vendor fixes the behaviour, they
are not used.
With a count of 0 neither the destination nor the flags change; a 32-bit register destination is
still zero-extended, as for the shifts (`shiftRot`; measured on an AMD Zen 4), and a memory
destination is not modelled. -/
def doubleShift (prof : Profile) (left : Bool) (i : Inst) : Prog Ctl :=
  let w := i.opsz
  match i.ops with
  | [d, s, cnt] => do
    let raw ← readOp 8 cnt
    let c := raw.toNat % (if w = 64 then 64 else 32)
    if c = 0 then
      match d with
      | .reg _ => do let x ← readOp w d; writeOp d x; done
      | _ => unmodelled (.form "double shift of memory by zero")
    else
    let x ← readOp w d .write
    let y ← readOp w s
    let f ← readFlags
    let af ← undefinedBit
    let ofU ← undefinedBit
    if c > w then do
      let r ← undefined w
      let cf ← undefinedBit
      let sf ← undefinedBit
      let zf ← undefinedBit
      let pf ← undefinedBit
      writeOp d r
      writeFlags (if prof.vendor = .amd then f.arith r cf ofU af
        else { f with cf := cf, of := ofU, sf := sf, zf := zf, af := af, pf := pf })
      done
    else
    -- the `2w`-bit value `x:y` (SHLD) or `y:x` (SHRD), shifted, and its relevant half
    let (r, cf) := if left then (((x ++ y) <<< c).extractLsb' w w, x.getLsbD (w - c))
      else (((y ++ x) >>> c).setWidth w, x.getLsbD (c - 1))
    let of := if c = 1 then r.msb != x.msb else ofU
    writeOp d r
    writeFlags (f.arith r cf of af)
    done
  | _ => formNotModelled i

/-- `SHLD` (`doubleShift`). -/
def Sem.shld (prof : Profile) (i : Inst) : Prog Ctl := doubleShift prof true i
/-- `SHRD` (`doubleShift`). -/
def Sem.shrd (prof : Profile) (i : Inst) : Prog Ctl := doubleShift prof false i

/-! ## BMI1 and BMI2

VEX-encoded instructions on general registers (SDM Vol. 2, the instructions' pages; APM Vol. 3,
same flags). The operand size is 32 or 64 bits (`VEX.W`); a 32-bit destination is zero-extended.
`SHLX`, `SHRX`, `SARX`, `RORX`, `PDEP`, `PEXT` and `MULX` leave the flags unchanged. -/

/-- `f` with the flags of a BMI1 result `r`: `ZF` and `SF` from `r`, `OF` cleared, `CF` given,
`AF` and `PF` undefined (SDM Vol. 2, "ANDN", "BLSI", "BLSR", "BZHI", Flags Affected). -/
def bmiFlags {w : Nat} (f : Rflags) (r : BitVec w) (cf : Bool) : Prog Rflags := do
  let af ← undefinedBit
  let pf ← undefinedBit
  Pure.pure { f with zf := r == 0, sf := r.msb, of := false, cf := cf, af := af, pf := pf }

/-- `ANDN d, s₁, s₂`: `(NOT s₁) AND s₂`; `CF` cleared (SDM Vol. 2, "ANDN"). -/
def Sem.andn (i : Inst) : Prog Ctl :=
  let w := i.opsz
  match i.ops with
  | [d, s₁, s₂] => do
    let a ← readOp w s₁
    let b ← readOp w s₂
    let r := ~~~a &&& b
    let f ← readFlags
    writeOp d r
    writeFlags (← bmiFlags f r false)
    done
  | _ => formNotModelled i

/-- `BEXTR d, s, c`: `len` bits of `s` from bit `start`, `start` = bits 7–0 and `len` = bits
15–8 of `c`; bits beyond the operand are 0. `ZF` from the result, `CF` and `OF` cleared, `AF`,
`SF`, `PF` undefined (SDM Vol. 2, "BEXTR"; APM Vol. 3, "BEXTR"). -/
def Sem.bextr (i : Inst) : Prog Ctl :=
  let w := i.opsz
  match i.ops with
  | [d, s, c] => do
    let x ← readOp w s
    let ctl ← readOp w c
    let start := (ctl.toNat % 256)
    let len := (ctl.toNat / 256) % 256
    let r := (x >>> start) &&& BitVec.ofNat w (2 ^ len - 1)
    let f ← readFlags
    let af ← undefinedBit
    let sf ← undefinedBit
    let pf ← undefinedBit
    writeOp d r
    writeFlags { f with zf := r == 0, cf := false, of := false, af := af, sf := sf, pf := pf }
    done
  | _ => formNotModelled i

/-- A BMI1 operation `d := g s` on the lowest set bit of `s`, `CF` from `cfOf s` (`BLSI`,
`BLSMSK`, `BLSR`). -/
def blsOp (i : Inst) (g : {w : Nat} → BitVec w → BitVec w) (cfOf : {w : Nat} → BitVec w → Bool) :
    Prog Ctl :=
  let w := i.opsz
  match i.ops with
  | [d, s] => do
    let x ← readOp w s
    let r := g x
    let f ← readFlags
    writeOp d r
    writeFlags (← bmiFlags f r (cfOf x))
    done
  | _ => formNotModelled i

/-- `BLSI`: `(-s) AND s`, the lowest set bit; `CF` set iff `s ≠ 0` (SDM Vol. 2, "BLSI"). -/
def Sem.blsi (i : Inst) : Prog Ctl := blsOp i (fun x => (-x) &&& x) (fun x => x != 0)
/-- `BLSMSK`: `(s - 1) XOR s`, the bits up to the lowest set bit; `CF` set iff `s = 0`; `ZF`
cleared (the result is never 0; SDM Vol. 2, "BLSMSK"). -/
def Sem.blsmsk (i : Inst) : Prog Ctl := blsOp i (fun x => (x - 1) ^^^ x) (fun x => x == 0)
/-- `BLSR`: `(s - 1) AND s`, `s` without its lowest set bit; `CF` set iff `s = 0` (SDM Vol. 2,
"BLSR"). -/
def Sem.blsr (i : Inst) : Prog Ctl := blsOp i (fun x => (x - 1) &&& x) (fun x => x == 0)

/-- `BZHI d, s, n`: `s` with the bits from bit `n` on cleared, `n` = bits 7–0 of the third
operand; if `n` is at least the operand size, `s` unchanged and `CF` set, else `CF` cleared
(SDM Vol. 2, "BZHI"). -/
def Sem.bzhi (i : Inst) : Prog Ctl :=
  let w := i.opsz
  match i.ops with
  | [d, s, c] => do
    let x ← readOp w s
    let n := (← readOp w c).toNat % 256
    let r := if n < w then x &&& BitVec.ofNat w (2 ^ n - 1) else x
    let f ← readFlags
    writeOp d r
    writeFlags (← bmiFlags f r (decide (w ≤ n)))
    done
  | _ => formNotModelled i

/-- A BMI2 shift `d := s op (c mod w)`, flags unchanged (`SHLX`, `SHRX`, `SARX`: SDM Vol. 2,
"SARX/SHLX/SHRX": the count is masked to 5 bits, or 6 with a 64-bit operand). -/
def shiftX (i : Inst) (g : {w : Nat} → BitVec w → Nat → BitVec w) : Prog Ctl :=
  let w := i.opsz
  match i.ops with
  | [d, s, c] => do
    let x ← readOp w s
    let n ← readOp w c
    writeOp d (g x (n.toNat % w))
    done
  | _ => formNotModelled i

/-- `SHLX` (`shiftX`). -/
def Sem.shlx (i : Inst) : Prog Ctl := shiftX i fun x n => x <<< n
/-- `SHRX` (`shiftX`). -/
def Sem.shrx (i : Inst) : Prog Ctl := shiftX i fun x n => x >>> n
/-- `SARX` (`shiftX`). -/
def Sem.sarx (i : Inst) : Prog Ctl := shiftX i fun x n => x.sshiftRight n

/-- `RORX d, s, imm8`: `s` rotated right by `imm8 mod w`, flags unchanged (SDM Vol. 2,
"RORX"). -/
def Sem.rorx (i : Inst) : Prog Ctl :=
  let w := i.opsz
  match i.ops with
  | [d, s, .imm _ k] => do
    let x ← readOp w s
    writeOp d (x.rotateRight (k % w))
    done
  | _ => formNotModelled i

/-- The positions of the set bits of `x`, in increasing order. -/
def setBits {w : Nat} (x : BitVec w) : List Nat := (List.range w).filter x.getLsbD

/-- `PDEP d, s, mask`: the low bits of `s` deposited, in order, at the set bits of `mask`: bit `m`
of the result is bit `k` of `s` if bit `m` of `mask` is its `k`-th set bit (from 0), else 0; flags
unchanged (SDM Vol. 2, "PDEP"). -/
def Sem.pdep (i : Inst) : Prog Ctl :=
  let w := i.opsz
  match i.ops with
  | [d, s, k] => do
    let x ← readOp w s
    let mask ← readOp w k
    writeOp d (ofBits w fun m => mask.getLsbD m && x.getLsbD ((setBits (mask.setWidth m)).length))
    done
  | _ => formNotModelled i

/-- `PEXT d, s, mask`: the bits of `s` at the set bits of `mask`, packed in order into the low bits
of the result: bit `k` is bit `m` of `s` if `m` is the `k`-th set bit of `mask`, else 0; flags
unchanged (SDM Vol. 2, "PEXT"). -/
def Sem.pext (i : Inst) : Prog Ctl :=
  let w := i.opsz
  match i.ops with
  | [d, s, k] => do
    let x ← readOp w s
    let mask ← readOp w k
    writeOp d (ofBits w fun j => match (setBits mask)[j]? with
      | some m => x.getLsbD m
      | none => false)
    done
  | _ => formNotModelled i

/-- `MULX hi, lo, s`: the unsigned product of `s` and `rDX` (`EDX` or `RDX` by operand size), the
low half to `lo` (the register `VEX.vvvv` names), then the high half to `hi` (so `hi` holds it if
the two are the same register); flags unchanged (SDM Vol. 2, "MULX"). -/
def Sem.mulx (i : Inst) : Prog Ctl :=
  let w := i.opsz
  match i.ops with
  | [hi, lo, s] => do
    let x ← readOp w s
    let y ← readOp w (accOf w 2)
    let p := x.setWidth (2 * w) * y.setWidth (2 * w)
    writeOp lo (p.setWidth w)
    writeOp hi (p.extractLsb' w w)
    done
  | _ => formNotModelled i

/-- Execute bit instruction `i` of mnemonic `m` on processor `prof`, with `rip` already advanced
past it. -/
def execBits (prof : Profile) (m : BitMn) (i : Inst) : Prog Ctl :=
  match m with
  | .bt => Sem.bt prof i | .bts => Sem.bts prof i | .btr => Sem.btr prof i
  | .btc => Sem.btc prof i | .bsf => Sem.bsf prof i | .bsr => Sem.bsr prof i
  | .tzcnt => Sem.tzcnt i | .lzcnt => Sem.lzcnt i | .shld => Sem.shld prof i | .shrd => Sem.shrd prof i
  | .andn => Sem.andn i | .bextr => Sem.bextr i | .blsi => Sem.blsi i | .blsmsk => Sem.blsmsk i
  | .blsr => Sem.blsr i | .bzhi => Sem.bzhi i | .sarx => Sem.sarx i | .shlx => Sem.shlx i
  | .shrx => Sem.shrx i | .rorx => Sem.rorx i | .pdep => Sem.pdep i | .pext => Sem.pext i
  | .mulx => Sem.mulx i

end ZellicX86
