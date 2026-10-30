import ZellicX86.Spec.Semantics.Basic
/-!
# Instruction semantics: SSE

Each case follows the "Operation" and "Flags Affected" sections of the instruction's page in
Intel SDM Vol. 2 (rev. 092); where AMD APM Vol. 4 (rev. 4.10) differs, the case says so. Forms not
implemented stop with `notModelled`.
-/
namespace ZellicX86
open Decode Prog

/-! ## Lanes

A 128-bit value as lanes: lane `i` of `k` bits is bits `k·i + k − 1` to `k·i` (SDM Vol. 1, 4.6,
"Packed SIMD Data Types": element 0 is the least significant). The packed instructions below compute
each lane of the result from the operands' lanes. -/

/-- Lane `i` of `k` bits of `x`. -/
def lane (k : Nat) (x : BitVec 128) (i : Nat) : BitVec k := x.extractLsb' (k * i) k

/-- The 128-bit value whose byte lane `i` is `f i`. -/
def ofBytes (f : Nat → BitVec 8) : BitVec 128 :=
  f 15 ++ f 14 ++ f 13 ++ f 12 ++ f 11 ++ f 10 ++ f 9 ++ f 8 ++ f 7 ++ f 6 ++ f 5 ++ f 4 ++ f 3 ++
    f 2 ++ f 1 ++ f 0

/-- The 128-bit value whose word lane `i` is `f i`. -/
def ofWords (f : Nat → BitVec 16) : BitVec 128 :=
  f 7 ++ f 6 ++ f 5 ++ f 4 ++ f 3 ++ f 2 ++ f 1 ++ f 0

/-- The 128-bit value whose doubleword lane `i` is `f i`. -/
def ofDwords (f : Nat → BitVec 32) : BitVec 128 := f 3 ++ f 2 ++ f 1 ++ f 0

/-- The 128-bit value whose quadword lane `i` is `f i`. -/
def ofQwords (f : Nat → BitVec 64) : BitVec 128 := f 1 ++ f 0

/-- Lane `j` of the interleaving of the `k`-bit lanes of `a` and `b` from lane `h` on: lane
`h + j / 2` of `a` for even `j`, of `b` for odd `j`. The unpack instructions interleave the low
halves (`h = 0`) or the high halves (`h = 64 / k`) of their operands (SDM Vol. 2,
"PUNPCKLBW/PUNPCKLWD/PUNPCKLDQ/PUNPCKLQDQ", "PUNPCKHBW/PUNPCKHWD/PUNPCKHDQ/PUNPCKHQDQ"). -/
def interleave (k h : Nat) (a b : BitVec 128) (j : Nat) : BitVec k :=
  if j % 2 = 0 then lane k a (h + j / 2) else lane k b (h + j / 2)

/-! ## SHA-256 functions (SDM Vol. 2, 4.2 "Common Transformation and Primitive Functions for
SHA1XXX and SHA256XXX") -/

/-- `Ch(E, F, G) := (E AND F) XOR ((NOT E) AND G)`. -/
def sha256Ch (e f g : BitVec 32) : BitVec 32 := (e &&& f) ^^^ (~~~e &&& g)
/-- `Maj(A, B, C) := (A AND B) XOR (A AND C) XOR (B AND C)`. -/
def sha256Maj (a b c : BitVec 32) : BitVec 32 := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
/-- `Σ0(A) := (A ROR 2) XOR (A ROR 13) XOR (A ROR 22)`. -/
def sha256S0 (a : BitVec 32) : BitVec 32 := a.rotateRight 2 ^^^ a.rotateRight 13 ^^^ a.rotateRight 22
/-- `Σ1(E) := (E ROR 6) XOR (E ROR 11) XOR (E ROR 25)`. -/
def sha256S1 (e : BitVec 32) : BitVec 32 := e.rotateRight 6 ^^^ e.rotateRight 11 ^^^ e.rotateRight 25
/-- `σ0(W) := (W ROR 7) XOR (W ROR 18) XOR (W SHR 3)`. -/
def sha256s0 (w : BitVec 32) : BitVec 32 := w.rotateRight 7 ^^^ w.rotateRight 18 ^^^ (w >>> 3)
/-- `σ1(W) := (W ROR 17) XOR (W ROR 19) XOR (W SHR 10)`. -/
def sha256s1 (w : BitVec 32) : BitVec 32 := w.rotateRight 17 ^^^ w.rotateRight 19 ^^^ (w >>> 10)

/-- `SHA256RNDS2`: two rounds from the state `(C, D, G, H)` in `src1`, `(A, B, E, F)` in `src2`
and the round inputs `WK0`, `WK1` in the low doublewords of `xmm0`; the new `(A, B, E, F)` (SDM
Vol. 2, "SHA256RNDS2", Operation). -/
def sha256Rnds2 (src1 src2 xmm0 : BitVec 128) : BitVec 128 :=
  let round (s : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 ×
      BitVec 32) (wk : BitVec 32) :=
    let (a, b, c, d, e, f, g, h) := s
    let t := sha256Ch e f g + sha256S1 e + wk + h
    (t + sha256Maj a b c + sha256S0 a, a, b, c, t + d, e, f, g)
  let s₀ := (lane 32 src2 3, lane 32 src2 2, lane 32 src1 3, lane 32 src1 2, lane 32 src2 1,
    lane 32 src2 0, lane 32 src1 1, lane 32 src1 0)
  let (a, b, _, _, e, f, _, _) := round (round s₀ (lane 32 xmm0 0)) (lane 32 xmm0 1)
  a ++ b ++ e ++ f

/-- `SHA256MSG1` (SDM Vol. 2, "SHA256MSG1", Operation). -/
def sha256Msg1 (src1 src2 : BitVec 128) : BitVec 128 :=
  let w4 := lane 32 src2 0
  ofDwords fun i => lane 32 src1 i + sha256s0 (if i = 3 then w4 else lane 32 src1 (i + 1))

/-- `SHA256MSG2` (SDM Vol. 2, "SHA256MSG2", Operation). -/
def sha256Msg2 (src1 src2 : BitVec 128) : BitVec 128 :=
  let w16 := lane 32 src1 0 + sha256s1 (lane 32 src2 2)
  let w17 := lane 32 src1 1 + sha256s1 (lane 32 src2 3)
  let w18 := lane 32 src1 2 + sha256s1 w16
  let w19 := lane 32 src1 3 + sha256s1 w17
  w19 ++ w18 ++ w17 ++ w16

/-- A packed operation `dest := f dest src` on 128-bit operands of exception type 4 (a memory
source must be 16-byte aligned, SDM Vol. 2, 2.5.4, Table 2-21, unless `MXCSR.MM`). -/
def packed (prof : Profile) (d s : Opd) (f : BitVec 128 → BitVec 128 → BitVec 128) : Prog Ctl := do
  aligned16 s .read prof.misalignSse
  let a ← readOp 128 d
  let b ← readOp 128 s
  writeOp d (f a b)
  Pure.pure .next

/-! ## The instructions

One definition per instruction, `Sem.<mnemonic>`; `execSse` chooses it by mnemonic. SSE2 is part
of every x86-64 processor, and Linux runs user code with `CR0.EM = 0`, `CR4.OSFXSR = 1` and eager
FPU state, so these raise neither `#UD` nor `#NM`; the decoder raises `#UD` for the SSE3, SSSE3,
SSE4.1, SSE4.2 and SHA forms on a processor without the feature, once the form's bytes are fetched
(modelled only when all 15 bytes an instruction may have can be fetched, `Entry.missing`). A 16-byte memory operand must be
aligned (`aligned16`) for the instructions of exception types 1 and 4 (SDM Vol. 2, 2.5.1 and
2.5.4, Tables 2-18 and 2-21) except `MOVUPS`, `MOVUPD`, `MOVDQU` (the unaligned moves), `PCMPISTRI` and
`PCMPISTRM` (Table 2-21, footnote 1); the other forms (exception types 5 and 7: `MOVD`, `MOVQ`, `MOVHPS`,
`MOVLPS`, `PINSR*`, `PEXTR*`, the shifts by an immediate, `PMOVMSKB`, `MOVLHPS`, `MOVHLPS`) have no
16-byte memory operand. Non-temporal `MOVNTPS`/`MOVNTDQ` stores always require 16-byte
alignment. Two vendor differences: the SHA instructions are checked on Intel only
(`shaAligned`), and with AMD's misaligned SSE mode on (`MXCSR.MM`, `Op.checkAligned`, on a
processor with `Profile.misalignSse`) only the aligned moves and non-temporal stores are. -/

/-- A packed operation of exception type 4 on its two operands (`packed`). -/
def packedOp (prof : Profile) (i : Inst) (f : BitVec 128 → BitVec 128 → BitVec 128) : Prog Ctl :=
  match i.ops with
  | [d, s] => packed prof d s f
  | _ => formNotModelled i

/-- A shift of an `XMM` register, `d := f d count`: by an immediate (exception type 7, register
only), or by the low 64 bits of an `XMM` register or of 16 bytes of memory (exception type 4: the
memory operand aligned as for `packed`; SDM Vol. 2, "PSRLW/PSRLD/PSRLQ", Operation: `COUNT :=
COUNT_SRC[63:0]`). A count from a register or memory is capped at 64, which leaves the result of every
shift of elements of at most 64 bits unchanged (0 from the element width on for a logical shift, all
sign bits from the width less one on for an arithmetic one). -/
def shiftBy (prof : Profile) (i : Inst) (f : BitVec 128 → Nat → BitVec 128) : Prog Ctl :=
  match i.ops with
  | [d, .imm _ k] => do
    let a ← readOp 128 d
    writeOp d (f a k)
    done
  | [d, s] => do
    aligned16 s .read prof.misalignSse
    let a ← readOp 128 d
    let c ← readOp 128 s
    writeOp d (f a (min (c.setWidth 64).toNat 64))
    done
  | _ => formNotModelled i

/-- A move of `w` bits, `d := s` (`writeOp` zero-extends into an `XMM` register). -/
def moveBits (w : Nat) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do
    let v ← readOp w s
    writeOp d v
    done
  | _ => formNotModelled i

/-- A 16-byte move that needs aligned memory operands (`MOVAPS`, `MOVDQA`), also with `MXCSR.MM`
(APM Vol. 1, 4.3.2). -/
def moveAligned (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do
    aligned16 d .write false
    aligned16 s .read false
    let v ← readOp 128 s
    writeOp d v
    done
  | _ => formNotModelled i

/-- `MOVUPS` (SDM Vol. 2, "MOVUPS"): no alignment. -/
def Sem.movups (i : Inst) : Prog Ctl := moveBits 128 i
/-- `MOVDQU` (SDM Vol. 2, "MOVDQU/VMOVDQU8/..."): no alignment. -/
def Sem.movdqu (i : Inst) : Prog Ctl := moveBits 128 i
/-- `MOVAPS` (SDM Vol. 2, "MOVAPS"). -/
def Sem.movaps (i : Inst) : Prog Ctl := moveAligned i
/-- `MOVDQA` (SDM Vol. 2, "MOVDQA/VMOVDQA32/VMOVDQA64"). -/
def Sem.movdqa (i : Inst) : Prog Ctl := moveAligned i

/-- Legacy `MOVNTPS m128, xmm`: store the source's 128 bits, with mandatory 16-byte
alignment, including with AMD's `MXCSR.MM` enabled. No arithmetic or floating-point
exception occurs. SDM Vol. 2B, MOVNTPS, Operation and Type1.SSE (Table 2-18);
AMD APM Vol. 4, MOVNTPS/VMOVNTPS, pp. 324–325. The non-temporal hint's weak
ordering across threads is not modelled, as for `VMOVNTDQ`; this thread sees the store. -/
def Sem.movntps (i : Inst) : Prog Ctl := moveAligned i

/-- Legacy `MOVNTDQ m128, xmm`: store 128 bits with mandatory 16-byte alignment,
including with AMD's `MXCSR.MM` enabled. SDM Vol. 2B, MOVNTDQ, Operation and
Type1.SSE2 (Table 2-18); AMD APM Vol. 4, MOVNTDQ/VMOVNTDQ, pp. 318–320.
The non-temporal hint's ordering across threads is not modelled (`Sem.movntps`). -/
def Sem.movntdq (i : Inst) : Prog Ctl := moveAligned i

/-! `PMINUD` (SSE4.1) -/

/-- Legacy `PMINUD`: the lesser unsigned doubleword of each source pair, preserving
the destination's bits above 127 and all flags. The decoder checks SSE4.1; memory
uses exception type 4 alignment, relaxed by AMD's misaligned SSE mode.
SDM Vol. 2B, PMINUD/PMINUQ, Operation and Table 2-21;
AMD APM Vol. 4, PMINUD/VPMINUD, pp. 553–555. -/
def Sem.pminud (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b =>
  ofDwords fun j => if (lane 32 a j).toNat < (lane 32 b j).toNat then lane 32 a j else lane 32 b j

/-- `MOVD`: 32 bits between an `XMM` register and a general register or memory (SDM Vol. 2,
"MOVD/MOVQ"). -/
def Sem.movd (i : Inst) : Prog Ctl := moveBits 32 i
/-- `MOVQ`: 64 bits between `XMM` registers, general registers and memory (SDM Vol. 2,
"MOVD/MOVQ", "MOVQ"). -/
def Sem.movq (i : Inst) : Prog Ctl := moveBits 64 i

/-- `MOVHPS`: the high quadword of an `XMM` register from 8 bytes of memory, the low one
unchanged, or to memory (SDM Vol. 2, "MOVHPS"; exception type 5). -/
def Sem.movhps (i : Inst) : Prog Ctl :=
  match i.ops with
  | [.xmm n, s] => do
    let a ← readOp 128 (.xmm n)
    let v ← readOp 64 s
    writeOp (.xmm n) (v ++ lane 64 a 0)
    done
  | [d, .xmm n] => do
    let a ← readOp 128 (.xmm n)
    writeOp d (lane 64 a 1)
    done
  | _ => formNotModelled i

/-- `MOVLPS`: the low quadword of an `XMM` register from 8 bytes of memory, the high one
unchanged, or to memory (SDM Vol. 2, "MOVLPS"; exception type 5). -/
def Sem.movlps (i : Inst) : Prog Ctl :=
  match i.ops with
  | [.xmm n, s] => do
    let a ← readOp 128 (.xmm n)
    let v ← readOp 64 s
    writeOp (.xmm n) (lane 64 a 1 ++ v)
    done
  | [d, .xmm n] => do
    let a ← readOp 128 (.xmm n)
    writeOp d (lane 64 a 0)
    done
  | _ => formNotModelled i

/-- `MOVLHPS`: the low quadword of the source to the high one of the destination (SDM Vol. 2,
"MOVLHPS"). -/
def Sem.movlhps (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do
    let a ← readOp 128 d
    let b ← readOp 128 s
    writeOp d (lane 64 b 0 ++ lane 64 a 0)
    done
  | _ => formNotModelled i

/-- `MOVHLPS`: the high quadword of the source to the low one of the destination (SDM Vol. 2,
"MOVHLPS"). -/
def Sem.movhlps (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do
    let a ← readOp 128 d
    let b ← readOp 128 s
    writeOp d (lane 64 a 1 ++ lane 64 b 1)
    done
  | _ => formNotModelled i

/-- `PXOR` (SDM Vol. 2, "PXOR"). -/
def Sem.pxor (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => a ^^^ b
/-- `POR` (SDM Vol. 2, "POR"). -/
def Sem.por (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => a ||| b
/-- `PAND` (SDM Vol. 2, "PAND"). -/
def Sem.pand (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => a &&& b
/-- `PANDN`: `(NOT d) AND s` (SDM Vol. 2, "PANDN"). -/
def Sem.pandn (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => ~~~a &&& b
/-- `XORPS` (SDM Vol. 2, "XORPS"). -/
def Sem.xorps (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => a ^^^ b

/-! ### Typed floating point without arithmetic

Moves, bitwise operations and shuffles of single- and double-precision elements: they move bits
and raise no SIMD floating-point exception (SDM Vol. 2, each page's "SIMD Floating-Point
Exceptions: None"). `XORPS` is above, with the integer logic. -/

/-- `XORPD` (SDM Vol. 2, "XORPD"). -/
def Sem.xorpd (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => a ^^^ b
/-- `ANDPS` (SDM Vol. 2, "ANDPS"). -/
def Sem.andps (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => a &&& b
/-- `ANDPD` (SDM Vol. 2, "ANDPD"). -/
def Sem.andpd (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => a &&& b
/-- `ANDNPS`: `(NOT d) AND s` (SDM Vol. 2, "ANDNPS"). -/
def Sem.andnps (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => ~~~a &&& b
/-- `ANDNPD`: `(NOT d) AND s` (SDM Vol. 2, "ANDNPD"). -/
def Sem.andnpd (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => ~~~a &&& b
/-- `ORPS` (SDM Vol. 2, "ORPS"). -/
def Sem.orps (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => a ||| b
/-- `ORPD` (SDM Vol. 2, "ORPD"). -/
def Sem.orpd (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => a ||| b

/-- `UNPCKLPS` (`interleave` of doublewords, SDM Vol. 2, "UNPCKLPS"). -/
def Sem.unpcklps (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => ofDwords (interleave 32 0 a b)
/-- `UNPCKLPD` (`interleave` of quadwords, SDM Vol. 2, "UNPCKLPD"). -/
def Sem.unpcklpd (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => ofQwords (interleave 64 0 a b)
/-- `UNPCKHPS` (SDM Vol. 2, "UNPCKHPS"). -/
def Sem.unpckhps (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => ofDwords (interleave 32 2 a b)
/-- `UNPCKHPD` (SDM Vol. 2, "UNPCKHPD"). -/
def Sem.unpckhpd (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => ofQwords (interleave 64 1 a b)

/-- `SHUFPS`: doublewords 0 and 1 from the destination, 2 and 3 from the source, each chosen by the
immediate's 2-bit field of its position (SDM Vol. 2, "SHUFPS"; exception type 4). -/
def Sem.shufps (prof : Profile) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s, .imm _ k] => do
    aligned16 s .read prof.misalignSse
    let a ← readOp 128 d
    let b ← readOp 128 s
    writeOp d (ofDwords fun j => lane 32 (if j < 2 then a else b) (k / 4 ^ j % 4))
    done
  | _ => formNotModelled i

/-- `SHUFPD`: quadword 0 from the destination's chosen by bit 0 of the immediate, quadword 1 from
the source's chosen by bit 1 (SDM Vol. 2, "SHUFPD"; exception type 4). -/
def Sem.shufpd (prof : Profile) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s, .imm _ k] => do
    aligned16 s .read prof.misalignSse
    let a ← readOp 128 d
    let b ← readOp 128 s
    writeOp d (ofQwords fun j => lane 64 (if j = 0 then a else b) (k / 2 ^ j % 2))
    done
  | _ => formNotModelled i

/-- `MOVMSKPS`: bit `j` of the general register is the sign bit of doubleword `j`, the other bits 0
(SDM Vol. 2, "MOVMSKPS"). -/
def Sem.movmskps (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do
    let b ← readOp 128 s
    writeOp d (ofBits 32 fun j => j < 4 && (lane 32 b j).msb)
    done
  | _ => formNotModelled i

/-- `MOVMSKPD`: bit `j` of the general register is the sign bit of quadword `j`, the other bits 0
(SDM Vol. 2, "MOVMSKPD"). -/
def Sem.movmskpd (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do
    let b ← readOp 128 s
    writeOp d (ofBits 32 fun j => j < 2 && (lane 64 b j).msb)
    done
  | _ => formNotModelled i

/-- A scalar move of the low `w` bits (`MOVSS`, `MOVSD`): between two registers only the low `w`
bits of the destination change; a load from memory clears the destination's bits 127 to `w`, a store
writes `w` bits (SDM Vol. 2, "MOVSS", "MOVSD": legacy forms keep bits `MAXVL-1:128`; exception
type 5). -/
def scalarMove (w : Nat) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [.xmm d, .xmm s] => do
    let a ← readOp 128 (.xmm d)
    let b ← readOp w (.xmm s)
    writeOp (.xmm d) ((a >>> w <<< w) ||| b.setWidth 128)
    done
  | _ => moveBits w i

/-- `MOVSS` (`scalarMove`). -/
def Sem.movss (i : Inst) : Prog Ctl := scalarMove 32 i
/-- `MOVSD` (`scalarMove`). -/
def Sem.movsd (i : Inst) : Prog Ctl := scalarMove 64 i
/-- `MOVUPD` (SDM Vol. 2, "MOVUPD"): no alignment. -/
def Sem.movupd (i : Inst) : Prog Ctl := moveBits 128 i
/-- `MOVAPD` (SDM Vol. 2, "MOVAPD"). -/
def Sem.movapd (i : Inst) : Prog Ctl := moveAligned i

/-- `MOVDDUP`, `MOVSHDUP`, `MOVSLDUP` and their VEX forms (SDM Vol. 2B, "MOVDDUP", "MOVSHDUP",
"MOVSLDUP"; APM Vol. 4, same): they copy bits, with no floating-point exceptions and no denormals-are-zero.
`MOVDDUP` duplicates the even quadword of each 128-bit lane (its 128-bit form reads only 8 bytes of
memory); `MOVSHDUP` and `MOVSLDUP` duplicate the odd or even doublewords. The legacy `MOVSHDUP`/`MOVSLDUP`
have exception type 4 (aligned memory); `MOVDDUP` has type 5 (no alignment). -/
def Sem.dup (misalignSse : Bool) (double high : Bool) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do
    if !double then
      match d with
      | .xmm _ => aligned16 s .read misalignSse
      | _ => Pure.pure ()
    let w := d.width
    let esz := if double then 64 else 32
    let a ← readOp (if double && w = 128 then 64 else w) s
    writeOp d (ofElems w esz fun j => elem esz a (j / 2 * 2 + if high then 1 else 0))
    done
  | _ => formNotModelled i

/-- `MOVLPD`: as `MOVLPS` (SDM Vol. 2, "MOVLPD"). -/
def Sem.movlpd (i : Inst) : Prog Ctl := Sem.movlps i
/-- `MOVHPD`: as `MOVHPS` (SDM Vol. 2, "MOVHPD"). -/
def Sem.movhpd (i : Inst) : Prog Ctl := Sem.movhps i

/-- `PADDB`: bytewise sums, wrapping (SDM Vol. 2, "PADDB/PADDW/PADDD/PADDQ"). -/
def Sem.paddb (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => ofBytes fun j => lane 8 a j + lane 8 b j
/-- `PADDW`: wordwise sums (SDM Vol. 2, "PADDB/PADDW/PADDD/PADDQ"). -/
def Sem.paddw (prof : Profile) (i : Inst) : Prog Ctl :=
  packedOp prof i fun a b => ofWords fun j => lane 16 a j + lane 16 b j
/-- `PADDD`: doublewordwise sums (SDM Vol. 2, "PADDB/PADDW/PADDD/PADDQ"). -/
def Sem.paddd (prof : Profile) (i : Inst) : Prog Ctl :=
  packedOp prof i fun a b => ofDwords fun j => lane 32 a j + lane 32 b j
/-- `PADDQ`: quadwordwise sums (SDM Vol. 2, "PADDB/PADDW/PADDD/PADDQ"). -/
def Sem.paddq (prof : Profile) (i : Inst) : Prog Ctl :=
  packedOp prof i fun a b => ofQwords fun j => lane 64 a j + lane 64 b j
/-- `PSUBB`: bytewise differences, wrapping (SDM Vol. 2, "PSUBB/PSUBW/PSUBD"). -/
def Sem.psubb (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => ofBytes fun j => lane 8 a j - lane 8 b j
/-- `PSUBW` (SDM Vol. 2, "PSUBB/PSUBW/PSUBD"). -/
def Sem.psubw (prof : Profile) (i : Inst) : Prog Ctl :=
  packedOp prof i fun a b => ofWords fun j => lane 16 a j - lane 16 b j
/-- `PSUBD` (SDM Vol. 2, "PSUBB/PSUBW/PSUBD"). -/
def Sem.psubd (prof : Profile) (i : Inst) : Prog Ctl :=
  packedOp prof i fun a b => ofDwords fun j => lane 32 a j - lane 32 b j
/-- `PSUBQ` (SDM Vol. 2, "PSUBQ"). -/
def Sem.psubq (prof : Profile) (i : Inst) : Prog Ctl :=
  packedOp prof i fun a b => ofQwords fun j => lane 64 a j - lane 64 b j

/-- `PCMPEQB`: each byte all ones where equal, else 0 (SDM Vol. 2, "PCMPEQB/PCMPEQW/PCMPEQD"). -/
def Sem.pcmpeqb (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b =>
  ofBytes fun j => if lane 8 a j = lane 8 b j then BitVec.allOnes 8 else 0
/-- `PCMPEQW` (SDM Vol. 2, "PCMPEQB/PCMPEQW/PCMPEQD"). -/
def Sem.pcmpeqw (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b =>
  ofWords fun j => if lane 16 a j = lane 16 b j then BitVec.allOnes 16 else 0
/-- `PCMPEQD` (SDM Vol. 2, "PCMPEQB/PCMPEQW/PCMPEQD"). -/
def Sem.pcmpeqd (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b =>
  ofDwords fun j => if lane 32 a j = lane 32 b j then BitVec.allOnes 32 else 0
/-- `PCMPGTB`: each byte all ones where the destination's is greater, signed (SDM Vol. 2,
"PCMPGTB/PCMPGTW/PCMPGTD"). -/
def Sem.pcmpgtb (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b =>
  ofBytes fun j => if (lane 8 b j).slt (lane 8 a j) then BitVec.allOnes 8 else 0
/-- `PCMPGTW` (SDM Vol. 2, "PCMPGTB/PCMPGTW/PCMPGTD"). -/
def Sem.pcmpgtw (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b =>
  ofWords fun j => if (lane 16 b j).slt (lane 16 a j) then BitVec.allOnes 16 else 0
/-- `PCMPGTD` (SDM Vol. 2, "PCMPGTB/PCMPGTW/PCMPGTD"). -/
def Sem.pcmpgtd (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b =>
  ofDwords fun j => if (lane 32 b j).slt (lane 32 a j) then BitVec.allOnes 32 else 0
/-- `PMINUB`: the unsigned minimum of each byte (SDM Vol. 2, "PMINUB/PMINUW"). -/
def Sem.pminub (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b =>
  ofBytes fun j => if lane 8 a j ≤ lane 8 b j then lane 8 a j else lane 8 b j
/-- `PMAXUB`: the unsigned maximum of each byte (SDM Vol. 2, "PMAXUB/PMAXUW"). -/
def Sem.pmaxub (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b =>
  ofBytes fun j => if lane 8 a j ≥ lane 8 b j then lane 8 a j else lane 8 b j

/-- `PUNPCKLBW` (`interleave`). -/
def Sem.punpcklbw (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => ofBytes (interleave 8 0 a b)
/-- `PUNPCKLWD` (`interleave`). -/
def Sem.punpcklwd (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => ofWords (interleave 16 0 a b)
/-- `PUNPCKLDQ` (`interleave`). -/
def Sem.punpckldq (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => ofDwords (interleave 32 0 a b)
/-- `PUNPCKLQDQ` (`interleave`). -/
def Sem.punpcklqdq (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => ofQwords (interleave 64 0 a b)
/-- `PUNPCKHBW` (`interleave`). -/
def Sem.punpckhbw (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => ofBytes (interleave 8 8 a b)
/-- `PUNPCKHWD` (`interleave`). -/
def Sem.punpckhwd (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => ofWords (interleave 16 4 a b)
/-- `PUNPCKHDQ` (`interleave`). -/
def Sem.punpckhdq (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => ofDwords (interleave 32 2 a b)
/-- `PUNPCKHQDQ` (`interleave`). -/
def Sem.punpckhqdq (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b => ofQwords (interleave 64 1 a b)

/-- `PSHUFB`: byte `j` is byte `s[j] mod 16` of the destination, or 0 if bit 7 of `s[j]` is set
(SDM Vol. 2, "PSHUFB"). -/
def Sem.pshufb (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b =>
  ofBytes fun j => if (lane 8 b j).msb then 0 else lane 8 a ((lane 8 b j).toNat % 16)

/-- `PSHUFD`: doubleword `j` is the source's doubleword chosen by the immediate's 2-bit field `j`
(SDM Vol. 2, "PSHUFD"). -/
def Sem.pshufd (prof : Profile) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s, .imm _ k] => do
    aligned16 s .read prof.misalignSse
    let b ← readOp 128 s
    writeOp d (ofDwords fun j => lane 32 b (k / 4 ^ j % 4))
    done
  | _ => formNotModelled i

/-- `PSHUFLW`: words 0–3 chosen from the source's words 0–3 by the immediate's 2-bit fields,
words 4–7 copied (SDM Vol. 2, "PSHUFLW"). -/
def Sem.pshuflw (prof : Profile) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s, .imm _ k] => do
    aligned16 s .read prof.misalignSse
    let b ← readOp 128 s
    writeOp d (ofWords fun j => if j < 4 then lane 16 b (k / 4 ^ j % 4) else lane 16 b j)
    done
  | _ => formNotModelled i

/-- `PSHUFHW`: words 4–7 chosen from the source's words 4–7 by the immediate's 2-bit fields,
words 0–3 copied (SDM Vol. 2, "PSHUFHW"). -/
def Sem.pshufhw (prof : Profile) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s, .imm _ k] => do
    aligned16 s .read prof.misalignSse
    let b ← readOp 128 s
    writeOp d (ofWords fun j => if j < 4 then lane 16 b j else lane 16 b (4 + k / 4 ^ (j - 4) % 4))
    done
  | _ => formNotModelled i

/-- `PINSRW`: the low word of the source (a register or 2 bytes of memory) into word `imm8 mod 8`
(SDM Vol. 2, "PINSRW"; exception type 5). -/
def Sem.pinsrw (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s, .imm _ k] => do
    let a ← readOp 128 d
    let v ← readOp 16 s
    writeOp d (ofWords fun j => if j = k % 8 then v else lane 16 a j)
    done
  | _ => formNotModelled i

/-- `PEXTRW`: word `imm8 mod 8` zero-extended into a general register (SDM Vol. 2, "PEXTRW"). -/
def Sem.pextrw (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s, .imm _ k] => do
    let b ← readOp 128 s
    writeOp d ((lane 16 b (k % 8)).setWidth 32)
    done
  | _ => formNotModelled i

/-- Legacy `PINSRB/D/Q`: insert the low `e` source bits at `imm8 mod (128/e)`,
keeping the other elements and ZMM bits above 127. The memory access is exactly `e/8`
bytes, with no SIMD alignment requirement (SDM Vol. 2B, "PINSRB/PINSRD/PINSRQ",
Operation and exception type 5; AMD APM Vol. 4, "PINSRB", "PINSRD", "PINSRQ"). -/
def pinsr (e : Nat) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s, .imm _ k] => do
    let a ← readOp 128 d
    let v ← readOp e s
    writeOp d (ofElems 128 e fun j => if j = k % (128 / e) then v else elem e a j)
    done
  | _ => formNotModelled i

/-- Legacy `PEXTRB/D/Q`: extract element `imm8 mod (128/e)` to memory or a general
register, zero-extending a register destination. The vector source is unchanged.
Memory needs no SIMD alignment (SDM Vol. 2B, "PEXTRB/PEXTRD/PEXTRQ", Operation,
exception type 5; AMD APM Vol. 4, the corresponding instruction pages). -/
def pextr (e : Nat) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s, .imm _ k] => do
    let a ← readOp 128 s
    writeOp d ((elem e a (k % (128 / e))).setWidth d.width)
    done
  | _ => formNotModelled i

/-- `PINSRB` (`pinsr`; SDM Vol. 2B, "PINSRB/PINSRD/PINSRQ"). -/
def Sem.pinsrb (i : Inst) : Prog Ctl := pinsr 8 i
/-- `PINSRD` (`pinsr`; SDM Vol. 2B, "PINSRB/PINSRD/PINSRQ"). -/
def Sem.pinsrd (i : Inst) : Prog Ctl := pinsr 32 i
/-- `PINSRQ` (`pinsr`; SDM Vol. 2B, "PINSRB/PINSRD/PINSRQ"). -/
def Sem.pinsrq (i : Inst) : Prog Ctl := pinsr 64 i
/-- `PEXTRB` (`pextr`; SDM Vol. 2B, "PEXTRB/PEXTRD/PEXTRQ"). -/
def Sem.pextrb (i : Inst) : Prog Ctl := pextr 8 i
/-- `PEXTRD` (`pextr`; SDM Vol. 2B, "PEXTRB/PEXTRD/PEXTRQ"). -/
def Sem.pextrd (i : Inst) : Prog Ctl := pextr 32 i
/-- `PEXTRQ` (`pextr`; SDM Vol. 2B, "PEXTRB/PEXTRD/PEXTRQ"). -/
def Sem.pextrq (i : Inst) : Prog Ctl := pextr 64 i

/-- `PALIGNR`: the low 128 bits of `dest:src` shifted right by `imm8` bytes, 0 from 32 on (SDM
Vol. 2, "PALIGNR"). -/
def Sem.palignr (prof : Profile) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s, .imm _ k] => do
    aligned16 s .read prof.misalignSse
    let a ← readOp 128 d
    let b ← readOp 128 s
    writeOp d (((a ++ b) >>> (8 * k)).setWidth 128)
    done
  | _ => formNotModelled i

/-- `PBLENDW`: word `j` from the source where bit `j` of `imm8` is set (SDM Vol. 2, "PBLENDW"). -/
def Sem.pblendw (prof : Profile) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s, .imm _ k] => do
    aligned16 s .read prof.misalignSse
    let a ← readOp 128 d
    let b ← readOp 128 s
    writeOp d (ofWords fun j => if k.testBit j then lane 16 b j else lane 16 a j)
    done
  | _ => formNotModelled i

/-- The alignment check of a SHA instruction's memory operand. The SDM gives `SHA256RNDS2`,
`SHA256MSG1` and `SHA256MSG2` exception type 4 (`#GP(0)` for a misaligned operand: "SHA256RNDS2",
..., Other Exceptions); the APM lists no alignment check for them (AMD APM Vol. 4, "SHA256RNDS2",
"SHA256MSG1", "SHA256MSG2", Exceptions: only `#AC` with `MXCSR.MM`, which the model does not reach),
and an AMD Zen 4 executes them with a misaligned operand in hardware measurements. -/
def shaAligned (prof : Profile) (s : Opd) : Prog Unit :=
  match s with
  | .mem _ => if prof.vendor = .intel then aligned16 s .read false else Pure.pure ()
  | _ => Pure.pure ()

/-- A SHA message instruction `dest := f dest src` (`shaAligned`). -/
def shaMsg (prof : Profile) (i : Inst) (f : BitVec 128 → BitVec 128 → BitVec 128) : Prog Ctl :=
  match i.ops with
  | [d, s] => do
    shaAligned prof s
    let a ← readOp 128 d
    let b ← readOp 128 s
    writeOp d (f a b)
    done
  | _ => formNotModelled i

/-- `SHA256RNDS2` (`sha256Rnds2`, SDM Vol. 2, "SHA256RNDS2"; `shaAligned`). -/
def Sem.sha256rnds2 (prof : Profile) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s, x0] => do
    shaAligned prof s
    let a ← readOp 128 d
    let b ← readOp 128 s
    let w ← readOp 128 x0
    writeOp d (sha256Rnds2 a b w)
    done
  | _ => formNotModelled i

/-- `SHA256MSG1` (`sha256Msg1`, SDM Vol. 2, "SHA256MSG1"). -/
def Sem.sha256msg1 (prof : Profile) (i : Inst) : Prog Ctl := shaMsg prof i sha256Msg1
/-- `SHA256MSG2` (`sha256Msg2`, SDM Vol. 2, "SHA256MSG2"). -/
def Sem.sha256msg2 (prof : Profile) (i : Inst) : Prog Ctl := shaMsg prof i sha256Msg2

/-- `PSRLW` by an immediate or a count (`shiftBy`): each word shifted right, 0 for a count of 16 or
more (SDM Vol. 2, "PSRLW/PSRLD/PSRLQ"; AMD APM Vol. 4, "PSRLW, VPSRLW", p. 669). -/
def Sem.psrlw (prof : Profile) (i : Inst) : Prog Ctl :=
  shiftBy prof i fun a k => ofWords fun j => lane 16 a j >>> k
/-- `PSRLD` (`shiftBy`; SDM Vol. 2, "PSRLW/PSRLD/PSRLQ"; AMD APM Vol. 4, "PSRLD, VPSRLD", p. 661). -/
def Sem.psrld (prof : Profile) (i : Inst) : Prog Ctl :=
  shiftBy prof i fun a k => ofDwords fun j => lane 32 a j >>> k
/-- `PSRLQ` (`shiftBy`; SDM Vol. 2, "PSRLW/PSRLD/PSRLQ"; AMD APM Vol. 4, "PSRLQ, VPSRLQ", p. 666). -/
def Sem.psrlq (prof : Profile) (i : Inst) : Prog Ctl :=
  shiftBy prof i fun a k => ofQwords fun j => lane 64 a j >>> k
/-- `PSLLW` by an immediate or a count (`shiftBy`): each word shifted left, 0 for a count of 16 or
more (SDM Vol. 2, "PSLLW/PSLLD/PSLLQ"; AMD APM Vol. 4, "PSLLW, VPSLLW", p. 652). -/
def Sem.psllw (prof : Profile) (i : Inst) : Prog Ctl :=
  shiftBy prof i fun a k => ofWords fun j => lane 16 a j <<< k
/-- `PSLLD` (`shiftBy`; SDM Vol. 2, "PSLLW/PSLLD/PSLLQ"; AMD APM Vol. 4, "PSLLD, VPSLLD", p. 644). -/
def Sem.pslld (prof : Profile) (i : Inst) : Prog Ctl :=
  shiftBy prof i fun a k => ofDwords fun j => lane 32 a j <<< k
/-- `PSLLQ` (`shiftBy`; SDM Vol. 2, "PSLLW/PSLLD/PSLLQ"; AMD APM Vol. 4, "PSLLQ, VPSLLQ", p. 649). -/
def Sem.psllq (prof : Profile) (i : Inst) : Prog Ctl :=
  shiftBy prof i fun a k => ofQwords fun j => lane 64 a j <<< k
/-- `PSRAW` by an immediate or a count (`shiftBy`): each word shifted right arithmetically, all
sign bits for a count of 16 or more (SDM Vol. 2, "PSRAW/PSRAD/PSRAQ"; AMD APM Vol. 4, "PSRAW,
VPSRAW", p. 658). -/
def Sem.psraw (prof : Profile) (i : Inst) : Prog Ctl :=
  shiftBy prof i fun a k => ofWords fun j => (lane 16 a j).sshiftRight k
/-- `PSRAD` (`shiftBy`; SDM Vol. 2, "PSRAW/PSRAD/PSRAQ"; AMD APM Vol. 4, "PSRAD, VPSRAD", p. 655). -/
def Sem.psrad (prof : Profile) (i : Inst) : Prog Ctl :=
  shiftBy prof i fun a k => ofDwords fun j => (lane 32 a j).sshiftRight k
/-- `PSRLDQ`: the whole register shifted right by `imm8` bytes, 0 above 15 (SDM Vol. 2,
"PSRLDQ"). -/
def Sem.psrldq (prof : Profile) (i : Inst) : Prog Ctl := shiftBy prof i fun a k => a >>> (8 * k)
/-- `PSLLDQ`: the whole register shifted left by `imm8` bytes, 0 above 15 (SDM Vol. 2,
"PSLLDQ"). -/
def Sem.pslldq (prof : Profile) (i : Inst) : Prog Ctl := shiftBy prof i fun a k => a <<< (8 * k)

/-! ### Saturation, packing and the widening multiply

Shared with the VEX forms (`Avx.lean`), which apply them to each 128-bit lane or element of a wider
vector. -/

/-- `x − y` of unsigned integers, 0 where `y` is the greater (SDM Vol. 2, "PSUBUSB/PSUBUSW":
`SaturateToUnsignedByte`/`Word` of the difference). -/
def subUnsignedSat {e : Nat} (x y : BitVec e) : BitVec e := if x.toNat ≤ y.toNat then 0 else x - y

/-- Clamp an integer to the signed `e`-bit range. SDM Vol. 2, "PADDSB/PADDSW" and
"PSUBSB/PSUBSW"; AMD APM Vol. 4, "PADDSB, VPADDSB" and "PSUBSB, VPSUBSB". -/
def satSigned (e : Nat) (x : Int) : BitVec e :=
  let bound : Int := 2 ^ (e - 1)
  BitVec.ofInt e (if x < -bound then -bound else if bound ≤ x then bound - 1 else x)

/-- Unsigned addition saturated at `2^e - 1`, computed before truncation. SDM Vol. 2,
"PADDUSB/PADDUSW"; AMD APM Vol. 4, "PADDUSB, VPADDUSB", "PADDUSW, VPADDUSW". -/
def addUnsignedSat {e : Nat} (x y : BitVec e) : BitVec e :=
  BitVec.ofNat e (min (2 ^ e - 1) (x.toNat + y.toNat))

/-- Signed addition saturated to the element's range (`satSigned`). SDM Vol. 2,
"PADDSB/PADDSW"; AMD APM Vol. 4, "PADDSB, VPADDSB", "PADDSW, VPADDSW". -/
def addSignedSat {e : Nat} (x y : BitVec e) : BitVec e := satSigned e (x.toInt + y.toInt)

/-- Signed subtraction saturated to the element's range (`satSigned`). SDM Vol. 2,
"PSUBSB/PSUBSW"; AMD APM Vol. 4, "PSUBSB, VPSUBSB", "PSUBSW, VPSUBSW". -/
def subSignedSat {e : Nat} (x y : BitVec e) : BitVec e := satSigned e (x.toInt - y.toInt)

/-- A signed source integer clamped to the unsigned `e`-bit range, before truncation.
SDM Vol. 2, "PACKUSWB", "PACKUSDW"; AMD APM Vol. 4, "PACKUSWB, VPACKUSWB", "PACKUSDW, VPACKUSDW". -/
def satUnsigned (e : Nat) (x : Int) : BitVec e :=
  let limit : Int := 2 ^ e - 1
  BitVec.ofInt e (if x < 0 then 0 else if limit < x then limit else x)

/-- Pack each signed `2*e`-bit source element to an `e`-bit result in a 128-bit lane,
using signed or unsigned saturation. The lower half comes from `a`, the upper from `b`.
SDM Vol. 2, "PACKSSWB/PACKSSDW", "PACKUSWB", "PACKUSDW"; AMD APM Vol. 4,
"PACKSSWB, VPACKSSWB", "PACKSSDW, VPACKSSDW", "PACKUSWB, VPACKUSWB", "PACKUSDW, VPACKUSDW". -/
def packSat (e : Nat) (signed : Bool) (a b : BitVec 128) : BitVec 128 :=
  ofElems 128 e fun j =>
    let half := 128 / (2 * e)
    let v := if j < half then (elem (2 * e) a j).toInt else (elem (2 * e) b (j - half)).toInt
    if signed then satSigned e v else satUnsigned e v

/-- PAVGB/PAVGW: unsigned element average rounded upward. The sum is widened before
adding one and dividing by two, so it cannot wrap at the element width. SDM Vol. 2,
"PAVGB/PAVGW"; AMD APM Vol. 4, "PAVGB, VPAVGB", "PAVGW, VPAVGW". -/
def averageUnsigned {e : Nat} (x y : BitVec e) : BitVec e :=
  BitVec.ofNat e ((x.toNat + y.toNat + 1) / 2)

/-- PSADBW: sum the unsigned-byte absolute differences in each consecutive group of
8 bytes into the low 16 bits of that group's quadword, clearing its upper 48 bits.
SDM Vol. 2, "PSADBW" (grouping description); AMD APM Vol. 4, "PSADBW, VPSADBW".
The APM's prose and the SDM's 512-bit pseudocode can be read otherwise; this follows the SDM's
description, which an AMD Zen 4 agrees with in hardware measurements. -/
def sadBytes {w : Nat} (a b : BitVec w) : BitVec w :=
  ofElems w 64 fun j => BitVec.ofNat 64 ((List.range 8).foldl (fun sum k =>
    let x := (elem 8 a (8 * j + k)).toNat
    let y := (elem 8 b (8 * j + k)).toNat
    sum + (x - y) + (y - x)) 0)

/-- PAVGB on byte elements, through `packedOp`. SDM Vol. 2, "PAVGB/PAVGW";
AMD APM Vol. 4, "PAVGB, VPAVGB". -/
def Sem.pavgb (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b =>
  ofElems 128 8 fun j => averageUnsigned (elem 8 a j) (elem 8 b j)
/-- PAVGW on word elements, through `packedOp`. SDM Vol. 2, "PAVGB/PAVGW";
AMD APM Vol. 4, "PAVGW, VPAVGW". -/
def Sem.pavgw (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b =>
  ofElems 128 16 fun j => averageUnsigned (elem 16 a j) (elem 16 b j)
/-- PSADBW on XMM operands, through `packedOp`, summing each group of eight byte
absolute differences. SDM Vol. 2 and AMD APM Vol. 4, "PSADBW". -/
def Sem.psadbw (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i sadBytes

/-- PMULDQ/PMULUDQ: signed/unsigned products of the low doublewords of each quadword;
ignore the high doublewords. SDM Vol. 2 and AMD APM Vol. 4, "PMULDQ", "PMULUDQ". -/
def mulDQ (signed : Bool) {w : Nat} (a b : BitVec w) : BitVec w :=
  ofElems w 64 fun j =>
    let x := elem 32 a (2 * j)
    let y := elem 32 b (2 * j)
    if signed then BitVec.ofInt 64 (x.toInt * y.toInt)
    else BitVec.ofNat 64 (x.toNat * y.toNat)

/-- `PMULHW`, `PMULHUW`, `PMULLW`: signed or unsigned multiplication, then the high or low word (SDM Vol. 2,
"PMULHW", "PMULHUW", "PMULLW"; AMD APM Vol. 4, "PMULHW, VPMULHW", "PMULHUW, VPMULHUW", "PMULLW, VPMULLW"). -/
def mulWord (signed high : Bool) (x y : BitVec 16) : BitVec 16 :=
  let product : Int := if signed then x.toInt * y.toInt else (x.toNat * y.toNat : Nat)
  if high then (BitVec.ofInt 32 product).extractLsb' 16 16 else BitVec.ofInt 16 product

/-- PMADDWD: adjacent signed word products summed modulo 2^32 (including four 8000h
inputs). PMADDUBSW: unsigned first-source and signed second-source bytes, adjacent
products summed with signed 16-bit saturation. SDM Vol. 2, "PMADDWD", "PMADDUBSW"; AMD APM Vol. 4,
"PMADDWD, VPMADDWD", "PMADDUBSW, VPMADDUBSW". -/
def maddPairs (e : Nat) (unsignedFirst saturated : Bool) {w : Nat}
    (a b : BitVec w) : BitVec w :=
  ofElems w (2 * e) fun j =>
    let product := fun k =>
      let x := elem e a k
      let y := elem e b k
      (if unsignedFirst then (x.toNat : Int) else x.toInt) * y.toInt
    let sum := product (2 * j) + product (2 * j + 1)
    if saturated then satSigned (2 * e) sum else BitVec.ofInt (2 * e) sum

/-- PMULHRSW: signed word product plus 2^14, then bits 30–15. The result truncates;
8000h × 8000h produces 8000h without saturation. SDM Vol. 2 and AMD APM Vol. 4,
"PMULHRSW, VPMULHRSW". -/
def mulRoundWord (x y : BitVec 16) : BitVec 16 :=
  BitVec.ofInt 16 ((x.toInt * y.toInt + 16384) / 32768)

/-- `PSUBUSB`: each byte of the source subtracted from the destination's, saturated at 0 (`packed`,
exception type 4; SDM Vol. 2, "PSUBUSB/PSUBUSW"; AMD APM Vol. 4, "PSUBUSB, VPSUBUSB", p. 687). -/
def Sem.psubusb (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b =>
  ofBytes fun j => subUnsignedSat (lane 8 a j) (lane 8 b j)
/-- `PSUBUSW`: the same on words (SDM Vol. 2, "PSUBUSB/PSUBUSW"; AMD APM Vol. 4, "PSUBUSW,
VPSUBUSW", p. 690). -/
def Sem.psubusw (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b =>
  ofWords fun j => subUnsignedSat (lane 16 a j) (lane 16 b j)
/-- `PADDSB` on 8-bit elements (`addSignedSat`, `packedOp`). SDM Vol. 2,
"PADDSB"; AMD APM Vol. 4, "PADDSB, VPADDSB". -/
def Sem.paddsb (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b =>
  ofElems 128 8 fun j => addSignedSat (elem 8 a j) (elem 8 b j)
/-- `PADDSW` on 16-bit elements (`addSignedSat`, `packedOp`). SDM Vol. 2,
"PADDSW"; AMD APM Vol. 4, "PADDSW, VPADDSW". -/
def Sem.paddsw (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b =>
  ofElems 128 16 fun j => addSignedSat (elem 16 a j) (elem 16 b j)
/-- `PADDUSB` on 8-bit elements (`addUnsignedSat`, `packedOp`). SDM Vol. 2,
"PADDUSB"; AMD APM Vol. 4, "PADDUSB, VPADDUSB". -/
def Sem.paddusb (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b =>
  ofElems 128 8 fun j => addUnsignedSat (elem 8 a j) (elem 8 b j)
/-- `PADDUSW` on 16-bit elements (`addUnsignedSat`, `packedOp`). SDM Vol. 2,
"PADDUSW"; AMD APM Vol. 4, "PADDUSW, VPADDUSW". -/
def Sem.paddusw (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b =>
  ofElems 128 16 fun j => addUnsignedSat (elem 16 a j) (elem 16 b j)
/-- `PSUBSB` on 8-bit elements (`subSignedSat`, `packedOp`). SDM Vol. 2,
"PSUBSB"; AMD APM Vol. 4, "PSUBSB, VPSUBSB". -/
def Sem.psubsb (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b =>
  ofElems 128 8 fun j => subSignedSat (elem 8 a j) (elem 8 b j)
/-- `PSUBSW` on 16-bit elements (`subSignedSat`, `packedOp`). SDM Vol. 2,
"PSUBSW"; AMD APM Vol. 4, "PSUBSW, VPSUBSW". -/
def Sem.psubsw (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i fun a b =>
  ofElems 128 16 fun j => subSignedSat (elem 16 a j) (elem 16 b j)
/-- `PACKUSWB` (`packSat`, `packed`, exception type 4; SDM Vol. 2, "PACKUSWB"; AMD APM Vol. 4, "PACKUSWB, VPACKUSWB",
p. 392). -/
def Sem.packuswb (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i (packSat 8 false)
/-- `PACKSSWB` (`packSat`, exception type 4). SDM Vol. 2, "PACKSSWB";
AMD APM Vol. 4, "PACKSSWB, VPACKSSWB". -/
def Sem.packsswb (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i (packSat 8 true)
/-- `PACKSSDW` (`packSat`, exception type 4). SDM Vol. 2, "PACKSSDW";
AMD APM Vol. 4, "PACKSSDW, VPACKSSDW". -/
def Sem.packssdw (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i (packSat 16 true)
/-- `PACKUSDW` (`packSat`, exception type 4). SDM Vol. 2, "PACKUSDW";
AMD APM Vol. 4, "PACKUSDW, VPACKUSDW". -/
def Sem.packusdw (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i (packSat 16 false)
/-- `PMULUDQ` (`mulDQ`, `packed`, exception type 4). -/
def Sem.pmuludq (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i (mulDQ false)

/-- `PMULDQ`: the signed 64-bit products of the low doublewords of each quadword (exception type 4).
SDM Vol. 2, "PMULDQ"; AMD APM Vol. 4, "PMULDQ, VPMULDQ". -/
def Sem.pmuldq (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i (mulDQ true)
/-- `PMULHW`: the high 16 bits of each signed word product (exception type 4).
SDM Vol. 2, "PMULHW"; AMD APM Vol. 4, "PMULHW, VPMULHW". -/
def Sem.pmulhw (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i (fun a b => ofElems 128 16 fun j => (mulWord true true) (elem 16 a j) (elem 16 b j))
/-- `PMULHUW`: the high 16 bits of each unsigned word product (exception type 4).
SDM Vol. 2, "PMULHUW"; AMD APM Vol. 4, "PMULHUW, VPMULHUW". -/
def Sem.pmulhuw (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i (fun a b => ofElems 128 16 fun j => (mulWord false true) (elem 16 a j) (elem 16 b j))
/-- `PMULLW`: the low 16 bits of each word product (exception type 4).
SDM Vol. 2, "PMULLW"; AMD APM Vol. 4, "PMULLW, VPMULLW". -/
def Sem.pmullw (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i (fun a b => ofElems 128 16 fun j => (mulWord true false) (elem 16 a j) (elem 16 b j))
/-- `PMADDWD`: adjacent signed word products added modulo 2^32 into doublewords (exception type 4).
SDM Vol. 2, "PMADDWD"; AMD APM Vol. 4, "PMADDWD, VPMADDWD". -/
def Sem.pmaddwd (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i (maddPairs 16 false false)
/-- `PMADDUBSW`: unsigned first-source bytes multiplied by signed second-source bytes,
with adjacent products added and saturated to signed words (exception type 4).
SDM Vol. 2, "PMADDUBSW"; AMD APM Vol. 4, "PMADDUBSW, VPMADDUBSW". -/
def Sem.pmaddubsw (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i (maddPairs 8 true true)
/-- `PMULHRSW`: signed word products rounded by adding 2^14, taking bits 30–15;
the result truncates without saturation (8000h times 8000h gives 8000h) (exception type 4).
SDM Vol. 2, "PMULHRSW"; AMD APM Vol. 4, "PMULHRSW, VPMULHRSW". -/
def Sem.pmulhrsw (prof : Profile) (i : Inst) : Prog Ctl := packedOp prof i (fun a b => ofElems 128 16 fun j => (mulRoundWord) (elem 16 a j) (elem 16 b j))

/-- `PMOVMSKB`: bit `j` of the general register is bit 7 of byte `j`, the other bits 0 (SDM
Vol. 2, "PMOVMSKB"). -/
def Sem.pmovmskb (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do
    let b ← readOp 128 s
    writeOp d ((List.range 16).foldl
      (fun m j => m ||| ((BitVec.ofBool (lane 8 b j).msb).setWidth 32 <<< j)) (0 : BitVec 32))
    done
  | _ => formNotModelled i

/-! ## SSE4.2 string comparisons (SDM Vol. 2, 4.1, "Imm8 Control Byte Operation for PCMPESTRI /
PCMPESTRM / PCMPISTRI / PCMPISTRM"; "PCMPISTRI", "PCMPISTRM") -/

/-- The elements of a 128-bit string operand under control byte `imm`: 16 bytes or 8 words
(`imm[0]`), as integers, signed if `imm[1]` (Table 4-1). -/
def strElems (imm : Nat) (x : BitVec 128) : List Int :=
  let k := if imm % 2 = 1 then 16 else 8
  (List.range (128 / k)).map fun j =>
    let e := x.extractLsb' (k * j) k
    if (imm / 2) % 2 = 1 then e.toInt else (e.toNat : Int)

/-- The number of valid elements of an implicit-length string: those below the first null
element (PCMPISTRI, Description). -/
def strLen (es : List Int) : Nat := (es.findIdx? (· = 0)).getD es.length

/-- `IntRes2` of `PCMPISTRI`/`PCMPISTRM` for sources `a` (`xmm1`, the register) and `b`
(`xmm2/m128`) with `la` and `lb` valid elements of `n`, under control byte `imm`: the comparison
`BoolRes[j, i]` of element `j` of `b` with element `i` of `a`, forced by validity (Table 4-7),
aggregated (Tables 4-2, 4-3) and then negated by polarity (Table 4-4). Bit `j` of the result is
element `j`'s. -/
def strIntRes2 (imm : Nat) (a b : List Int) (la lb : Nat) : Nat → Bool :=
  let n := a.length
  let mode := (imm / 4) % 4
  let va (i : Nat) := decide (i < la)
  let vb (j : Nat) := decide (j < lb)
  let ai (i : Nat) := a.getD i 0
  let bj (j : Nat) := b.getD j 0
  -- the comparison of mode `mode`, before validity
  let cmp (j i : Nat) : Bool := match mode with
    | 1 => if i % 2 = 0 then decide (ai i ≤ bj j) else decide (bj j ≤ ai i)
    | _ => decide (bj j = ai i)
  -- `overrideIfDataInvalid(BoolRes[j, i])` (Table 4-7)
  let res (j i : Nat) : Bool :=
    if va i && vb j then cmp j i
    else match mode with
      | 2 => !va i && !vb j
      | 3 => !va i
      | _ => false
  let int1 (j : Nat) : Bool := match mode with
    | 0 => (List.range n).any fun i => res j i
    | 1 => (List.range (n / 2)).any fun p => res j (2 * p) && res j (2 * p + 1)
    | 2 => res j j
    | _ => (List.range (n - j)).all fun i => res (j + i) i
  fun j => match (imm / 16) % 4 with
    | 1 => !int1 j
    | 3 => if vb j then !int1 j else int1 j
    | _ => int1 j

/-- The flags of `PCMPISTRI`/`PCMPISTRM`: `CF` iff `IntRes2 ≠ 0`, `ZF` iff `b` has a null element,
`SF` iff `a` has one, `OF` = `IntRes2[0]`, `AF` and `PF` cleared. -/
def strFlags (f : Rflags) (n : Nat) (r : Nat → Bool) (la lb : Nat) : Rflags :=
  { f with cf := (List.range n).any r, zf := decide (lb < n), sf := decide (la < n), of := r 0,
           af := false, pf := false }

/-- `PCMPISTRI xmm1, xmm2/m128, imm8`: `ECX` is the index of the least (`imm[6] = 0`) or most
significant set bit of `IntRes2`, or the number of elements if none is set (SDM Vol. 2,
"PCMPISTRI"; the memory operand need not be aligned). -/
def Sem.pcmpistri (i : Inst) : Prog Ctl :=
  match i.ops with
  | [s₁, s₂, .imm _ k] => do
    let x ← readOp 128 s₁
    let y ← readOp 128 s₂
    let (a, b) := (strElems k x, strElems k y)
    let (la, lb) := (strLen a, strLen b)
    let n := a.length
    let r := strIntRes2 k a b la lb
    let idx := if (k / 64) % 2 = 1 then ((List.range n).reverse.find? r).getD n
      else ((List.range n).find? r).getD n
    let f ← readFlags
    writeOp (accOf 32 1) (BitVec.ofNat 32 idx)
    writeFlags (strFlags f n r la lb)
    done
  | _ => formNotModelled i

/-- `PCMPISTRM xmm1, xmm2/m128, imm8`: `XMM0` is `IntRes2` as a bit mask in its low bits
(`imm[6] = 0`) or as a byte or word mask, each bit repeated over its element (SDM Vol. 2,
"PCMPISTRM"; Table 4-6). -/
def Sem.pcmpistrm (i : Inst) : Prog Ctl :=
  match i.ops with
  | [s₁, s₂, .imm _ k] => do
    let x ← readOp 128 s₁
    let y ← readOp 128 s₂
    let (a, b) := (strElems k x, strElems k y)
    let (la, lb) := (strLen a, strLen b)
    let n := a.length
    let r := strIntRes2 k a b la lb
    let e := 128 / n
    let mask : BitVec 128 := (List.range n).foldl (fun acc j =>
      if r j then acc ||| (if (k / 64) % 2 = 1 then BitVec.ofNat 128 (2 ^ e - 1) <<< (e * j)
        else (1 : BitVec 128) <<< j) else acc) 0
    let f ← readFlags
    writeOp (.xmm 0) mask
    writeFlags (strFlags f n r la lb)
    done
  | _ => formNotModelled i

/-- Execute legacy SSE instruction `i` of mnemonic `m` on processor `prof`, with `rip` already
advanced past it. -/
def execSse (prof : Profile) (m : SseMn) (i : Inst) : Prog Ctl :=
  match m with
  | .movups => Sem.movups i | .movaps => Sem.movaps i | .movdqa => Sem.movdqa i
  | .movdqu => Sem.movdqu i | .movd => Sem.movd i | .movq => Sem.movq i
  | .movntps => Sem.movntps i | .movntdq => Sem.movntdq i | .pminud => Sem.pminud prof i
  | .movhps => Sem.movhps i | .movlps => Sem.movlps i | .movlhps => Sem.movlhps i
  | .movhlps => Sem.movhlps i
  | .pxor => Sem.pxor prof i | .por => Sem.por prof i | .pand => Sem.pand prof i | .pandn => Sem.pandn prof i
  | .paddb => Sem.paddb prof i | .paddw => Sem.paddw prof i | .paddd => Sem.paddd prof i | .paddq => Sem.paddq prof i
  | .psubb => Sem.psubb prof i | .psubw => Sem.psubw prof i | .psubd => Sem.psubd prof i | .psubq => Sem.psubq prof i
  | .pcmpeqb => Sem.pcmpeqb prof i | .pcmpeqw => Sem.pcmpeqw prof i | .pcmpeqd => Sem.pcmpeqd prof i
  | .pcmpgtb => Sem.pcmpgtb prof i | .pcmpgtw => Sem.pcmpgtw prof i | .pcmpgtd => Sem.pcmpgtd prof i
  | .pminub => Sem.pminub prof i | .pmaxub => Sem.pmaxub prof i | .pmovmskb => Sem.pmovmskb i
  | .psrlw => Sem.psrlw prof i | .psrld => Sem.psrld prof i | .psrlq => Sem.psrlq prof i
  | .psllw => Sem.psllw prof i | .pslld => Sem.pslld prof i | .psllq => Sem.psllq prof i
  | .psraw => Sem.psraw prof i | .psrad => Sem.psrad prof i | .psrldq => Sem.psrldq prof i
  | .pslldq => Sem.pslldq prof i
  | .psubusb => Sem.psubusb prof i | .psubusw => Sem.psubusw prof i
  | .paddsb => Sem.paddsb prof i
  | .paddsw => Sem.paddsw prof i
  | .paddusb => Sem.paddusb prof i
  | .paddusw => Sem.paddusw prof i
  | .psubsb => Sem.psubsb prof i
  | .psubsw => Sem.psubsw prof i
  | .packsswb => Sem.packsswb prof i
  | .packssdw => Sem.packssdw prof i
  | .packusdw => Sem.packusdw prof i
  | .pavgb => Sem.pavgb prof i
  | .pavgw => Sem.pavgw prof i
  | .psadbw => Sem.psadbw prof i
  | .pmuldq => Sem.pmuldq prof i
  | .pmulhw => Sem.pmulhw prof i
  | .pmulhuw => Sem.pmulhuw prof i
  | .pmullw => Sem.pmullw prof i
  | .pmaddwd => Sem.pmaddwd prof i
  | .pmaddubsw => Sem.pmaddubsw prof i
  | .pmulhrsw => Sem.pmulhrsw prof i
  | .packuswb => Sem.packuswb prof i | .pmuludq => Sem.pmuludq prof i
  | .pshufd => Sem.pshufd prof i | .pshuflw => Sem.pshuflw prof i | .pshufhw => Sem.pshufhw prof i
  | .pinsrw => Sem.pinsrw i | .pextrw => Sem.pextrw i
  | .pinsrb => Sem.pinsrb i | .pinsrd => Sem.pinsrd i | .pinsrq => Sem.pinsrq i
  | .pextrb => Sem.pextrb i | .pextrd => Sem.pextrd i | .pextrq => Sem.pextrq i
  | .punpcklbw => Sem.punpcklbw prof i | .punpcklwd => Sem.punpcklwd prof i
  | .punpckldq => Sem.punpckldq prof i | .punpcklqdq => Sem.punpcklqdq prof i
  | .punpckhbw => Sem.punpckhbw prof i | .punpckhwd => Sem.punpckhwd prof i
  | .punpckhdq => Sem.punpckhdq prof i | .punpckhqdq => Sem.punpckhqdq prof i
  | .xorps => Sem.xorps prof i
  | .pshufb => Sem.pshufb prof i | .palignr => Sem.palignr prof i | .pblendw => Sem.pblendw prof i
  | .sha256rnds2 => Sem.sha256rnds2 prof i | .sha256msg1 => Sem.sha256msg1 prof i
  | .sha256msg2 => Sem.sha256msg2 prof i
  | .pcmpistri => Sem.pcmpistri i | .pcmpistrm => Sem.pcmpistrm i
  | .movupd => Sem.movupd i | .movapd => Sem.movapd i | .movss => Sem.movss i | .movsd => Sem.movsd i
  | .movddup => Sem.dup prof.misalignSse true false i
  | .movshdup => Sem.dup prof.misalignSse false true i
  | .movsldup => Sem.dup prof.misalignSse false false i
  | .movlpd => Sem.movlpd i | .movhpd => Sem.movhpd i
  | .andps => Sem.andps prof i | .andpd => Sem.andpd prof i | .andnps => Sem.andnps prof i
  | .andnpd => Sem.andnpd prof i | .orps => Sem.orps prof i | .orpd => Sem.orpd prof i
  | .xorpd => Sem.xorpd prof i
  | .unpcklps => Sem.unpcklps prof i | .unpcklpd => Sem.unpcklpd prof i
  | .unpckhps => Sem.unpckhps prof i | .unpckhpd => Sem.unpckhpd prof i
  | .shufps => Sem.shufps prof i | .shufpd => Sem.shufpd prof i
  | .movmskps => Sem.movmskps i | .movmskpd => Sem.movmskpd i

end ZellicX86
