import ZellicX86.Spec.Machine
import ZellicX86.Spec.Decode.Decode
/-!
# Instruction semantics: what every family uses

Condition codes, the status flags of additions, subtractions and logical operations, operand
access, the stack, and how an instruction ends (`Ctl`). The instructions themselves are in the
family modules next to this one; `Spec/Semantics.lean` dispatches to them.
-/
namespace ZellicX86
open Decode Prog

/-- Status-flag condition `c` of `Jcc`, `SETcc`, `CMOVcc` (SDM Vol. 1, Appendix B, Table B-1),
in encoding order `O NO B AE E NE BE A S NS P NP L GE LE G`. -/
def Rflags.cond (f : Rflags) (c : Cond) : Bool :=
  match c with
  | 0 => f.of | 1 => !f.of
  | 2 => f.cf | 3 => !f.cf
  | 4 => f.zf | 5 => !f.zf
  | 6 => f.cf || f.zf | 7 => !(f.cf || f.zf)
  | 8 => f.sf | 9 => !f.sf
  | 10 => f.pf | 11 => !f.pf
  | 12 => f.sf != f.of | 13 => f.sf == f.of
  | 14 => f.zf || (f.sf != f.of) | _ => !(f.zf || (f.sf != f.of))   -- 15: G

/-- `PF`: set iff the least significant byte of `x` has an even number of 1 bits (SDM Vol. 1,
3.4.3.1). -/
def parity {w : Nat} (x : BitVec w) : Bool :=
  (List.range 8).foldl (fun p i => p != x.getLsbD i) true

/-- `f` with the result flags `SF`, `ZF`, `PF` of result `r`, and `CF`, `OF`, `AF` given. -/
def Rflags.arith {w : Nat} (f : Rflags) (r : BitVec w) (cf of af : Bool) : Rflags :=
  { f with cf := cf, of := of, af := af, sf := r.msb, zf := r == 0, pf := parity r }

/-- Unsigned carry out of `x + y + c`. -/
def carryAdd {w : Nat} (x y : BitVec w) (c : Bool) : Bool :=
  decide (2 ^ w ≤ x.toNat + y.toNat + c.toNat)
/-- Signed overflow of `x + y + c` giving `r`: both operands have the same sign and `r` the
other. -/
def overflowAdd {w : Nat} (x y r : BitVec w) : Bool := x.msb == y.msb && r.msb != x.msb
/-- Carry out of bit 3 of `x + y + c`. -/
def auxAdd {w : Nat} (x y : BitVec w) (c : Bool) : Bool :=
  decide (16 ≤ x.toNat % 16 + y.toNat % 16 + c.toNat)
/-- Unsigned borrow of `x - (y + c)`. -/
def borrowSub {w : Nat} (x y : BitVec w) (c : Bool) : Bool := decide (x.toNat < y.toNat + c.toNat)
/-- Signed overflow of `x - y - c` giving `r`: the operands have different signs and `r` has
the sign of `y`. -/
def overflowSub {w : Nat} (x y r : BitVec w) : Bool := x.msb != y.msb && r.msb != x.msb
/-- Borrow into bit 3 of `x - (y + c)`. -/
def auxSub {w : Nat} (x y : BitVec w) (c : Bool) : Bool :=
  decide (x.toNat % 16 < y.toNat % 16 + c.toNat)

/-- Register number `n` (0–15; the decoder produces no other). -/
def regOf (n : Nat) : Reg := Fin.ofNat 16 n

/-- The effective address (offset) of memory operand `x`: `base + index * scale + disp`, or
`rip + disp` for RIP-relative operands, where `rip` is the address of the next instruction.
With an address-size prefix (`67`) the computation is done in 32 bits and zero-extended
(SDM Vol. 1, 3.7.5 "Specifying an Offset"; Vol. 2, 2.2.1.6 "RIP-Relative Addressing"). -/
def effOffset (x : MemOp) : Prog Addr := do
  let base ← if x.ripRel then readRip else
    match x.base with
    | some b => readReg (regOf b)
    | none => Pure.pure 0
  let idx ← match x.index with
    | some i => readReg (regOf i)
    | none => Pure.pure 0
  let off := base + idx * BitVec.ofNat 64 x.scale + BitVec.ofNat 64 x.disp
  if x.addr32 then Pure.pure (off.setWidth 32 |>.setWidth 64) else Pure.pure off

/-- The memory reference of operand `x`: the linear address is the effective address plus the
`FS` or `GS` base with those prefixes (SDM Vol. 1, 3.4.2.1). The reference uses the stack
segment when its base register is `rsp` or `rbp` (with a `67` prefix `esp` or `ebp`) and there is
no `FS`/`GS` prefix (SDM Vol. 1, 3.7.5: "When the ESP or EBP register is used as the base, the SS
segment is the default segment"; 3.3.7.1: with an `FS` or `GS` prefix a canonical fault is `#GP`,
and the `CS`, `DS`, `ES` and `SS` prefixes are ignored, so an `SS` prefix does not make another
reference a stack reference). An index register `rbp` or a base `r12`/`r13` does not either (an AMD
Zen 4 agrees). -/
def memRef (x : MemOp) : Prog MemRef := do
  let off ← effOffset x
  let addr ← match x.seg with
    | some .fs => do let b ← segBase true; Pure.pure (b + off)
    | some .gs => do let b ← segBase false; Pure.pure (b + off)
    | _ => Pure.pure off
  let fsgs := match x.seg with
    | some .fs | some .gs => true
    | _ => false
  Pure.pure ⟨addr, (x.base == some 4 || x.base == some 5) && !x.ripRel && !fsgs⟩

/-- General register `n` as a `w`-bit operand (`accOf w 0` is `AL`, `AX`, `EAX` or `RAX`; `accOf w 2`
is `rDX`), for the implicit operands of `MUL`, `DIV`, `CBW`, ... -/
def accOf (w n : Nat) : Opd := .reg ⟨w, n, false⟩

/-- The width in bits of an operand as decoded. -/
def Decode.Opd.width : Opd → Nat
  | .reg r => r.width
  | .xmm _ => 128
  | .vreg _ w => w
  | .kreg _ => 64
  | .mem m => m.width
  | .imm w _ => w
  | .rel _ => 64
  | .bcst _ w => w
  | .st _ => 80

/-- Element `i` of `k` bits of `x`: bits `k·i + k − 1` to `k·i` (SDM Vol. 1, 4.6 "Packed SIMD Data
Types": element 0 is the least significant). -/
def elem {w : Nat} (k : Nat) (x : BitVec w) (i : Nat) : BitVec k := x.extractLsb' (k * i) k

/-- The `w`-bit value whose `k`-bit element `i` is `f i`, for `i < w / k`. -/
def ofElems (w k : Nat) (f : Nat → BitVec k) : BitVec w :=
  (List.range (w / k)).foldl (fun acc i => acc ||| ((f i).setWidth w <<< (k * i))) 0

/-- The `n`-bit value whose bit `i` is `f i`, for `i < n`. -/
def ofBits (n : Nat) (f : Nat → Bool) : BitVec n :=
  (List.range n).foldl (fun acc i => if f i then acc ||| ((1 : BitVec n) <<< i) else acc) 0

/-- Vector register `ZMMn` of a decoded operand (0–31; the decoder produces no other). -/
def xmmOf (n : Nat) : Fin 32 := Fin.ofNat 32 n

/-- Opmask register `kn` of a decoded operand (0–7; the decoder produces no other). -/
def kOf (n : Nat) : Fin 8 := Fin.ofNat 8 n

/-- Read operand `o` as a `w`-bit value. A register reads its low `w` bits (`AH`–`BH`:
bits 15–8; `XMMn`, `YMMn`: the low bits of `ZMMn`; `kn`: the low bits of the 64-bit opmask
register); an immediate is already extended by the decoder; a broadcast source loads its one
element and repeats it (SDM Vol. 2, 2.7.7).
`acc` is `write` when the instruction then writes the same memory operand. -/
def readOp (w : Nat) (o : Opd) (acc : Access := .read) : Prog (BitVec w) :=
  match o with
  | .reg r => do
    let v ← readReg (regOf r.num)
    if r.high8 then Pure.pure ((v >>> 8).setWidth w) else Pure.pure (v.setWidth w)
  | .mem x => do
    let m ← memRef x
    read m w acc
  | .imm _ v => Pure.pure (BitVec.ofNat w v)
  | .xmm n => do
    let v ← readZmm (xmmOf n)
    Pure.pure (v.setWidth w)
  | .vreg n _ => do
    let v ← readZmm (xmmOf n)
    Pure.pure (v.setWidth w)
  | .kreg n => do
    let v ← readK (kOf n)
    Pure.pure (v.setWidth w)
  | .bcst x _ => do
    let m ← memRef x
    let e ← read m x.width acc
    Pure.pure (ofElems w x.width fun _ => e)
  | _ => unmodelled (.form "operand kind")

/-- Write `v` to operand `d`. A 64- or 32-bit register write replaces the whole register (a
32-bit result is zero-extended, SDM Vol. 1, 3.4.1.1); an 8- or 16-bit write keeps the other
bits. A write to `XMMn` by a legacy (non-VEX) SSE instruction sets bits 127–0 of `ZMMn` to
`v` zero-extended and keeps bits 511–128; a write of a VEX or EVEX instruction to `XMMn`, `YMMn`
or `ZMMn` (`Opd.vreg`) sets all of `ZMMn` to `v` zero-extended (SDM Vol. 1, 15.5 "Accessing XMM,
YMM and ZMM Registers"; Vol. 2, 2.3.10.1 "Vector Length Transition and Programming
Considerations": bits `MAXVL-1` to the destination's width are zeroed). A write to an opmask
register sets all its 64 bits to `v` zero-extended (SDM Vol. 2, "KMOVW/KMOVB/KMOVQ/KMOVD",
"VPCMPB/VPCMPUB": `DEST[MAX_KL-1:...] ← 0`). -/
def writeOp {w : Nat} (d : Opd) (v : BitVec w) : Prog Unit :=
  match d with
  | .reg r =>
    if w = 64 ∨ w = 32 then writeReg (regOf r.num) (v.setWidth 64)
    else do
      let old ← readReg (regOf r.num)
      let sh := if r.high8 then 8 else 0
      let mask : BitVec 64 := BitVec.ofNat 64 ((2 ^ w - 1) * 2 ^ sh)
      writeReg (regOf r.num) ((old &&& ~~~mask) ||| (v.setWidth 64 <<< sh))
  | .mem x => do
    let m ← memRef x
    write m w v
  | .xmm n => do
    let old ← readZmm (xmmOf n)
    writeZmm (xmmOf n) (old.extractLsb' 128 384 ++ v.setWidth 128)
  | .vreg n _ => writeZmm (xmmOf n) (v.setWidth 512)
  | .kreg n => writeK (kOf n) (v.setWidth 64)
  | _ => unmodelled (.form "operand kind")

/-- Whether processor `prof` supports AMD's misaligned SSE mode (`MXCSR.MM`, bit 17): its
`MXCSR_MASK` has bit 17 (APM Vol. 1, 4.2.2 "MXCSR Register": "The corresponding MXCSR_MASK bit (17)
is 1"; the mode's CPUID flag is `Fn8000_0001_ECX[MisAlignSse]`). On Intel the bit is reserved. -/
def Profile.misalignSse (prof : Profile) : Bool := prof.mxcsrMask.getLsbD 17

/-- `#GP(0)` if `o` is a memory operand whose address is not 16-byte aligned, for an access
`acc` of 16 bytes (legacy SSE instructions of exception types 1 and 4, SDM Vol. 2, 2.5.1 and
2.5.4, Tables 2-18 and 2-21). With `mm` set (every such instruction except the aligned moves, on a
processor with `Profile.misalignSse`), the check is skipped while AMD's misaligned SSE mode is on
(`MXCSR.MM`, `Op.checkAligned`). -/
def aligned16 (o : Opd) (acc : Access) (mm : Bool) : Prog Unit :=
  match o with
  | .mem x => do
    let m ← memRef x
    alignedTo m 16 acc 16 mm
  | _ => Pure.pure ()

/-- Continue at `target` if it is canonical, else `#GP(0)` (SDM Vol. 2, "JMP", "CALL",
"RET", "Jcc": the target is checked before control transfers). -/
def jumpTo (feat : Features) (target : Addr) : Prog Unit :=
  if Addr.canonical feat.la57 target then writeRip target else throw (.gp 0)

/-- Push `v` (8 bytes): store at `rsp - 8`, then set `rsp` (SDM Vol. 2, "PUSH"). -/
def push64 (v : BitVec 64) : Prog Unit := do
  let sp ← readReg 4
  write ⟨sp - 8, true⟩ 64 v
  writeReg 4 (sp - 8)

/-- Pop 8 bytes: load at `rsp`, then set `rsp` (SDM Vol. 2, "POP"). -/
def pop64 : Prog (BitVec 64) := do
  let sp ← readReg 4
  let v ← read ⟨sp, true⟩ 64
  writeReg 4 (sp + 8)
  Pure.pure v

/-- A binary ALU operation `d := op d s` or, for `cmp`/`test`, only its flags. -/
def alu (w : Nat) (d s : Opd) (store : Bool)
    (op : BitVec w → BitVec w → Rflags → Prog (BitVec w × Rflags)) : Prog Unit := do
  let x ← readOp w d (if store then .write else .read)
  let y ← readOp w s
  let f ← readFlags
  let (r, f') ← op x y f
  if store then writeOp d r
  writeFlags f'

/-- `x + y + c` with its flags (SDM Vol. 2, "ADD", "ADC"). -/
def addOp {w : Nat} (c : Bool) (x y : BitVec w) (f : Rflags) : Prog (BitVec w × Rflags) :=
  let r := x + y + (BitVec.ofBool c).setWidth w
  Pure.pure (r, f.arith r (carryAdd x y c) (overflowAdd x y r) (auxAdd x y c))

/-- `x - y - c` with its flags (SDM Vol. 2, "SUB", "SBB", "CMP"). -/
def subOp {w : Nat} (c : Bool) (x y : BitVec w) (f : Rflags) : Prog (BitVec w × Rflags) :=
  let r := x - y - (BitVec.ofBool c).setWidth w
  Pure.pure (r, f.arith r (borrowSub x y c) (overflowSub x y r) (auxSub x y c))

/-- A logical operation's result with its flags: `OF` and `CF` cleared, `SF`, `ZF`, `PF` from
the result, `AF` undefined (SDM Vol. 2, "AND", "OR", "XOR", "TEST"). -/
def logicOp {w : Nat} (g : BitVec w → BitVec w → BitVec w) (x y : BitVec w) (f : Rflags) :
    Prog (BitVec w × Rflags) := do
  let af ← undefinedBit
  let r := g x y
  Pure.pure (r, f.arith r false false af)

/-- `BSWAP` of a 32- or 64-bit value: reverse the byte order (SDM Vol. 2, "BSWAP"). -/
def bswap {w : Nat} (x : BitVec w) : BitVec w :=
  ofBytesLE w (toBytesLE x (w / 8)).reverse

/-- The shifts and rotates `shiftRot` implements. -/
inductive ShiftOp | rol | ror | shl | shr | sar

/-- The shift and rotate group (`ROL`, `ROR`, `SHL`, `SHR`, `SAR`) on `w`-bit destination `d`
with count `cnt` (SDM Vol. 2, "SAL/SAR/SHL/SHR", "RCL/RCR/ROL/ROR"). The count is masked to 5
bits, or 6 with a 64-bit operand. `SHL`'s and `SHR`'s `CF` is the last bit shifted out; for a count of
at least the width (8- and 16-bit forms) it is undefined on Intel (SDM "SAL/SAR/SHL/SHR": "it is
undefined for SHL and SHR instructions where the count is greater than or equal to the size (in bits)
of the destination operand") and on AMD still the last bit shifted out: the operand's bit 0 (`SHL`) or
top bit (`SHR`) at the width, 0 above it (APM "SAL/SHL", "SHR", with no exception for large counts; an
AMD Zen 4 gives these at every such count in hardware measurements). The open value is drawn on both vendors,
so the sequence of choices does not depend on the vendor; on AMD it is not used.

With a masked count of 0 no flags change and the value is unchanged. A register destination
is still written, so a 32-bit one is zero-extended: the general rule for 32-bit results (SDM
Vol. 1, 3.4.1.1; AMD APM Vol. 1, 3.1.2.3), observed on an Intel Raptor Lake core. Whether a
memory destination is written (and so needs write access) is not specified, so a zero count
with a memory destination is not modelled. -/
def shiftRot (prof : Profile) (w : Nat) (op : ShiftOp) (d : Opd) (cnt : Opd) : Prog Unit := do
  let raw ← readOp 8 cnt
  let c := raw.toNat % (if w = 64 then 64 else 32)
  if c = 0 then
    match d with
    | .reg _ => do let x ← readOp w d; writeOp d x
    | _ => unmodelled (.form "shift or rotate of memory by zero")
  else
  let x ← readOp w d .write
  let f ← readFlags
  match op with
  | .shl => do
    let r := x <<< c
    -- CF is the last bit shifted out: bit w - c of x; past the width (8/16-bit forms) by the vendor
    let cf ← if c < w then Pure.pure (x.getLsbD (w - c)) else do
      let u ← undefinedBit
      Pure.pure (if prof.vendor = .amd then c = w && x.getLsbD 0 else u)
    let of ← if c = 1 then Pure.pure (r.msb != cf) else undefinedBit
    let af ← undefinedBit
    writeOp d r
    writeFlags (f.arith r cf of af)
  | .shr => do
    let r := x >>> c
    let cf ← if c < w then Pure.pure (x.getLsbD (c - 1)) else do
      let u ← undefinedBit
      Pure.pure (if prof.vendor = .amd then c = w && x.msb else u)
    let of ← if c = 1 then Pure.pure x.msb else undefinedBit
    let af ← undefinedBit
    writeOp d r
    writeFlags (f.arith r cf of af)
  | .sar => do
    let r := x.sshiftRight c
    -- CF is the last bit shifted out; past the width that is the sign bit
    let cf := (x.sshiftRight (c - 1)).getLsbD 0
    -- OF is cleared by a 1-bit shift and undefined for a larger count (SDM and APM "SAR"; an
    -- AMD Zen 4 clears it)
    let of ← if c = 1 then Pure.pure false else undefinedBit
    let af ← undefinedBit
    writeOp d r
    writeFlags (f.arith r cf of af)
  | .rol => do
    let r := x.rotateLeft (c % w)
    let cf := r.getLsbD 0
    let of ← if c = 1 then Pure.pure (r.msb != cf) else undefinedBit
    writeOp d r
    writeFlags { f with cf := cf, of := of }
  | .ror => do
    let r := x.rotateRight (c % w)
    let cf := r.msb
    let of ← if c = 1 then Pure.pure (r.msb != r.getMsbD 1) else undefinedBit
    writeOp d r
    writeFlags { f with cf := cf, of := of }

/-- How an instruction ends when it does not raise an exception. -/
inductive Ctl
  /-- Continue with the next instruction (at the current `rip`). -/
  | next
  /-- `SYSCALL`: control passes to the kernel. -/
  | syscall
  /-- The instruction is not finished: the next step executes it again (an iteration of a
  repeated string instruction that does not end the repetition). -/
  | again

/-- Continue with the next instruction. -/
def done : Prog Ctl := Pure.pure .next

/-- Instruction `i` with operands its definition does not handle: a form the model does not
implement. -/
def formNotModelled (i : Inst) : Prog Ctl := unmodelled (.form (reprStr i.mn))

end ZellicX86
