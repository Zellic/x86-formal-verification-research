import ZellicX86.Spec.Semantics.Sse
/-!
# Instruction semantics: VEX- and EVEX-encoded vector instructions, opmask instructions

Each case follows the "Operation" and "Flags Affected" sections of the instruction's page in
Intel SDM Vol. 2 (rev. 092); where AMD APM Vol. 4 differs, the case says so. Forms not
implemented stop with `notModelled`.

What is common to the family:

- **Width.** A vector operand is `Opd.vreg n w`, `w` the instruction's vector length (128, 256 or
  512 bits: `VEX.L`, `EVEX.L'L`). A register destination is written whole: bits above `w` become
  0 (`writeOp`).
- **Opmask** (EVEX; SDM Vol. 2, 2.7.4; Vol. 1, 15.6.1). `Inst.mask = some k` with `k ≠ 0`
  selects elements by bit `j` of opmask register `k` for element `j` (of the element size the instruction's
  page names). A masked-off element of a register destination keeps its value (merging) or
  becomes 0 (zeroing, `Inst.zero`); one of a memory destination is not written; one of a memory
  source is not read. Neither is accessed: their faults are suppressed (SDM Vol. 2, 2.8,
  exception classes E1, E4 and E6, "If fault suppression not set"; AMD APM Vol. 1, 4.13.5, and
  each instruction's page), so such accesses are `Prog.readSel`/`Prog.writeSel` of the selected
  bytes. The exceptions are the instructions of class E4NF (`VPSHUFB`, `VPMADDWD`, `VPMADDUBSW`, `VPACKSSWB`,
  `VPACKSSDW`, `VPACKUSWB`, `VPACKUSDW`, `VPSADBW`; the APM: "do not support memory fault suppression"), whose
  memory source is read whole under any opmask. With `k = 0` every element is selected
  and the accesses are ordinary ones. An opmask destination (compares, tests) gets the
  results for the selected elements and 0 for the others and above them.
- **Broadcast** (`EVEX.b` with a memory source, `Opd.bcst`; SDM Vol. 2, 2.7.7): one element is
  loaded and repeated. Under an opmask it is loaded only if the opmask selects an element (fault
  suppression, as for the other masked sources; checked on an AMD Zen 4).
- **Alignment.** Only the aligned moves (`VMOVDQA`, `VMOVDQA32`, `VMOVDQA64`, `VMOVAPS`, `VMOVAPD`,
  `VMOVNTDQ`: exception types 1 and E1) need a memory operand aligned to the vector length, also
  with AMD's misaligned SSE mode on (`MXCSR.MM`, APM Vol. 1, 4.3.2); every other form here takes any
  address (types 4, E4 and E6). The SDM checks the alignment whatever the opmask (Table 2-46); an AMD
  Zen 4 does not when the opmask selects no element in hardware measurements,
  so with an empty selection the check is a `pick`.
- **Features** are checked by the decoder (`Spec/Decode/Maps.lean`), which raises `#UD` without
  them once the form's bytes are fetched (modelled only when all 15 bytes an instruction may have can
  be fetched, `Entry.missing`); the OS-enabled state is part of the features (`Features.avx`, `Features.avx512f`).
-/
namespace ZellicX86
open Decode Prog

/-! ## Opmasks, sources and destinations -/

/-- The opmask an EVEX instruction applies: `kk` for `Inst.mask = some k`, `k ≠ 0`; all ones
without masking (SDM Vol. 2, 2.7.4: `aaa = 000` processes every element). -/
def maskBits (i : Inst) : Prog (BitVec 64) :=
  match i.mask with
  | some k => if k = 0 then Pure.pure (BitVec.allOnes 64) else readK (kOf k)
  | none => Pure.pure (BitVec.allOnes 64)

/-- Whether `i` is masked (`Inst.mask = some k`, `k ≠ 0`). -/
def Decode.Inst.masked (i : Inst) : Bool :=
  match i.mask with
  | some k => k != 0
  | none => false

/-- The byte selection of `bytes` bytes of `esz`-bit elements under opmask `km`: byte `b` is
selected iff element `b / (esz / 8)` is. -/
def byteSel (esz bytes : Nat) (km : BitVec 64) : BitVec bytes :=
  ofBits bytes fun b => km.getLsbD (b / (esz / 8))

/-- Whether opmask `km` selects one of the `w / esz` elements of a `w`-bit vector. -/
def anySel (w esz : Nat) (km : BitVec 64) : Bool := (List.range (w / esz)).any km.getLsbD

/-- Read the `e`-bit element `s` that an instruction with a `w`-bit destination repeats (a
broadcast source, `VPBROADCAST*`): from memory under an opmask only if the opmask selects an
element of the destination (fault suppression, SDM Vol. 2, 2.8, exception classes E4 and E6:
"If fault suppression not set"). -/
def readElem (i : Inst) (w e : Nat) (km : BitVec 64) (s : Opd) : Prog (BitVec e) :=
  if i.masked then
    match s with
    | .mem x | .bcst x _ => do
      let m ← memRef x
      let v ← readSel m (e / 8) (if anySel w e km then BitVec.allOnes (e / 8) else 0)
      Pure.pure (v.setWidth e)
    | _ => readOp e s
  else readOp e s

/-- Read source operand `s` of a `w`-bit vector instruction with `esz`-bit elements under
opmask `km`: a memory source of a masked instruction reads only the selected elements' bytes
(the others read as 0 and are not used); a broadcast source its element (`readElem`). -/
def readSrc (i : Inst) (w esz : Nat) (km : BitVec 64) (s : Opd) : Prog (BitVec w) :=
  if i.masked then
    match s with
    | .mem x => do
      let m ← memRef x
      let v ← readSel m (w / 8) (byteSel esz (w / 8) km)
      Pure.pure (v.setWidth w)
    | .bcst x _ => do
      let v ← readElem i w x.width km s
      Pure.pure (ofElems w x.width fun _ => v)
    | _ => readOp w s
  else readOp w s

/-- Write the `w`-bit result `r` of `esz`-bit elements to the register destination `d` under
opmask `km`: a masked-off element keeps `d`'s value, or is 0 with zeroing-masking. Without
masking the write is `writeOp`. -/
def writeMasked (i : Inst) (esz : Nat) (km : BitVec 64) (d : Opd) {w : Nat} (r : BitVec w) :
    Prog Unit :=
  if i.masked then do
    let old ← if i.zero then Pure.pure 0 else readOp w d
    writeOp d (ofElems w esz fun j => if km.getLsbD j then elem esz r j else elem esz old j)
  else writeOp d r

/-- `#GP(0)` unless memory operand `o` of an aligned move is aligned to `w / 8` bytes, for an
access `acc` (SDM Vol. 2, 2.5.1, exception type 1; 2.8, Table 2-46, E1: "EVEX.512: Memory operand
is not 64-byte aligned", whatever the opmask). Which fault a misaligned access that would also
fault raises is a `pick` (`Prog.alignedTo`), between `#GP(0)` and a fault of all `w / 8` bytes,
also under an opmask. -/
def alignedVec (o : Opd) (w : Nat) (acc : Access) : Prog Unit :=
  match o with
  | .mem x => do
    let m ← memRef x
    alignedTo m (w / 8) acc (w / 8) false
  | _ => Pure.pure ()

/-! ## Moves -/

/-- A vector move `d := s` of `esz`-bit elements (`VMOVDQU*`, `VMOVDQA*`), aligned if
`aligned`. A store under an opmask writes only the selected elements (SDM Vol. 2,
"MOVDQU/VMOVDQU8/VMOVDQU16/VMOVDQU32/VMOVDQU64", Operation "VMOVDQU8 (EVEX encoded versions,
store-form)"); a load into a register merges or zeroes. -/
def vmove (esz : Nat) (aligned : Bool) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do
    let w := d.width
    let km ← maskBits i
    if aligned then do
      -- an empty selection: checked (SDM) or not (Zen 4)
      let check ← if i.masked && (List.range (w / esz)).all (fun j => !km.getLsbD j) then do
          let c ← choice 1
          Pure.pure (decide (c.val = 1))
        else Pure.pure true
      if check then do
        alignedVec d w .write
        alignedVec s w .read
    match d with
    | .mem x =>
      if i.masked then do
        let v ← readOp w s
        let m ← memRef x
        writeSel m (w / 8) (byteSel esz (w / 8) km) (v.setWidth (8 * (w / 8)))
        done
      else do
        let v ← readOp w s
        writeOp d v
        done
    | _ => do
      let v ← readSrc i w esz km s
      writeMasked i esz km d v
      done
  | _ => formNotModelled i

/-- `VMOVDQU` (VEX; SDM Vol. 2, "MOVDQU/VMOVDQU8/VMOVDQU16/VMOVDQU32/VMOVDQU64"). -/
def Sem.vmovdqu (i : Inst) : Prog Ctl := vmove 8 false i
/-- `VMOVDQA` (VEX; SDM Vol. 2, "MOVDQA/VMOVDQA32/VMOVDQA64"). -/
def Sem.vmovdqa (i : Inst) : Prog Ctl := vmove 8 true i
/-- `VMOVDQU8` (EVEX). -/
def Sem.vmovdqu8 (i : Inst) : Prog Ctl := vmove 8 false i
/-- `VMOVDQU16` (EVEX). -/
def Sem.vmovdqu16 (i : Inst) : Prog Ctl := vmove 16 false i
/-- `VMOVDQU32` (EVEX). -/
def Sem.vmovdqu32 (i : Inst) : Prog Ctl := vmove 32 false i
/-- `VMOVDQU64` (EVEX). -/
def Sem.vmovdqu64 (i : Inst) : Prog Ctl := vmove 64 false i
/-- `VMOVDQA32` (EVEX). -/
def Sem.vmovdqa32 (i : Inst) : Prog Ctl := vmove 32 true i
/-- `VMOVDQA64` (EVEX). -/
def Sem.vmovdqa64 (i : Inst) : Prog Ctl := vmove 64 true i
/-- `VMOVUPS` (VEX, EVEX; SDM Vol. 2, "MOVUPS"): a move of doublewords. -/
def Sem.vmovups (i : Inst) : Prog Ctl := vmove 32 false i
/-- `VMOVAPS` (VEX, EVEX; SDM Vol. 2, "MOVAPS"): an aligned move of doublewords. -/
def Sem.vmovaps (i : Inst) : Prog Ctl := vmove 32 true i
/-- `VMOVNTDQ` (VEX, EVEX; SDM Vol. 2, "MOVNTDQ"): an aligned store, without an opmask. Its
non-temporal hint and its weaker ordering (SDM Vol. 3A, 11.2.2: such stores are not ordered with
other stores; `SFENCE` orders them) are not visible to the thread itself. The model has one thread and
no memory-ordering model (MODEL-LIMITATIONS.md, "Memory"), so it is an ordinary aligned store. -/
def Sem.vmovntdq (i : Inst) : Prog Ctl := vmove 8 true i

/-- `VPBROADCASTB`, `VPBROADCASTW`, `VPBROADCASTD`, `VPBROADCASTQ` (`e` = 8, 16, 32, 64 bits) from
a general register, the low element of a vector register, or memory: every element of the
destination is the source's low `e` bits (SDM Vol. 2, "VPBROADCAST", "VPBROADCASTB/W/D/Q"). -/
def Sem.vpbroadcast (e : Nat) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do
    let w := d.width
    let km ← maskBits i
    let x ← readElem i w e km s
    writeMasked i e km d (ofElems w e fun _ => x)
    done
  | _ => formNotModelled i

/-- `VBROADCASTSS` (SDM Vol. 2, "VBROADCAST"): as `VPBROADCASTD`; the element is moved as bits,
without floating-point exceptions. -/
def Sem.vbroadcastss (i : Inst) : Prog Ctl := Sem.vpbroadcast 32 i

/-- Bits 511–128 of `ZMM0` to `ZMM(n-1)` become 0. -/
def Sem.zeroUpper : Nat → Prog Unit
  | 0 => Pure.pure ()
  | n + 1 => do
    let v ← readZmm (xmmOf n)
    writeZmm (xmmOf n) ((v.setWidth 128).setWidth 512)
    Sem.zeroUpper n

/-- `VMOVD`, `VMOVQ` (VEX- and EVEX-encoded, 128-bit): the low 32 or 64 bits of the source to the
destination, between a vector register and a general register or memory, or (`VMOVQ`) between
two vector registers and from a vector register to memory. A vector register destination is
written whole, the bits above the moved ones becoming 0 (SDM Vol. 2, "MOVD/MOVQ": `DEST[MAXVL-1:64]
← 0`, "MOVQ": `VMOVQ` with `XMM` operands). The width moved is that of the narrower operand. -/
def vmovLow (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do
    let v ← readOp (min d.width s.width) s
    writeOp d v
    done
  | _ => formNotModelled i

/-- `VMOVD` (`vmovLow`). -/
def Sem.vmovd (i : Inst) : Prog Ctl := vmovLow i
/-- `VMOVQ` (`vmovLow`). -/
def Sem.vmovq (i : Inst) : Prog Ctl := vmovLow i

/-- `VZEROALL` and `VZEROUPPER` with `VEX.W = 1`. The APM (Vol. 4, "VZEROALL", "VZEROUPPER") marks W as
ignored in the encoding but lists W1 as `#UD`, and an AMD Zen 4 executes the W1 form; on AMD both are allowed
(alternative 0: executes, 1: `#UD`). The SDM (Vol. 2C, "VZEROALL", "VZEROUPPER") marks W as ignored and lists
no W1 exception, so on Intel the form executes; this has not been measured on Intel hardware. The decoder
reports W1 for these operand-free forms as `Inst.opsz = 64`. -/
def Sem.vzeroCheck (prof : Profile) (i : Inst) : Prog Unit := do
  if i.opsz = 64 then
    if prof.vendor = .amd then
      let k ← choice 1
      if k.val = 1 then throw .ud

/-- `VZEROUPPER`: bits 511–128 of `ZMM0`–`ZMM15` become 0; `ZMM16`–`ZMM31` are unchanged (SDM
Vol. 2C, p. 5-776, Operation; APM Vol. 4, p. 1762). W1 follows `vzeroCheck`. -/
def Sem.vzeroupper (prof : Profile) (i : Inst) : Prog Ctl := do
  Sem.vzeroCheck prof i
  Sem.zeroUpper 16
  done

/-- Zero the first `n` complete vector registers, counting down; the remaining
registers are unchanged (SDM Vol. 2C, VZEROALL, Operation;
AMD APM Vol. 4, VZEROALL, p. 1761). -/
def Sem.zeroAll : Nat → Prog Unit
  | 0 => Pure.pure ()
  | n + 1 => do
    writeZmm (xmmOf n) 0
    Sem.zeroAll n

/-- `VZEROALL`: zero ZMM0–ZMM15, including their XMM/YMM aliases; leave
ZMM16–ZMM31, MXCSR and flags unchanged. SDM Vol. 2C, VZEROALL, Operation
and Type 8 exceptions (Table 2-25); AMD APM Vol. 4, VZEROALL, p. 1761.
The decoder requires AVX and `vvvv = 1111b`; W1 follows `vzeroCheck`. -/
def Sem.vzeroall (prof : Profile) (i : Inst) : Prog Ctl := do
  Sem.vzeroCheck prof i
  Sem.zeroAll 16
  done

/-! ## Element-wise operations -/

/-- VEX packed shifts by an immediate or by the low 64 bits of an XMM/m128 operand.
Logical shifts saturate to zero at the element width; arithmetic shifts repeat the sign
bit. Capping the count at `e` preserves these results. A count in memory reads all 16
bytes and needs no SIMD alignment (SDM Vol. 2B, "PSRLW/PSRLD/PSRLQ",
"PSLLW/PSLLD/PSLLQ", "PSRAW/PSRAD/PSRAQ", Operation; exception type 7 for immediate forms (MI/VMI), type 4 for count forms;
AMD APM Vol. 4, the corresponding `VPSRL*`, `VPSLL*`, `VPSRA*` pages). -/
def vshift (e : Nat) (i : Inst) (f : BitVec e → Nat → BitVec e) : Prog Ctl :=
  match i.ops with
  | [d, s, c] => do
    let w := d.width
    let a ← readOp w s
    let k ← match c with
      | .imm _ k => Pure.pure k
      | _ => do
        let count ← readOp 128 c
        Pure.pure (count.setWidth 64).toNat
    writeOp d (ofElems w e fun j => f (elem e a j) (min k e))
    done
  | _ => formNotModelled i

/-- VEX `VPSRLW/D/Q`: logical right shift (`vshift`; SDM Vol. 2B, "PSRLW/PSRLD/PSRLQ"). -/
def Sem.vpsrl (e : Nat) (i : Inst) : Prog Ctl := vshift e i fun a k => a >>> k
/-- VEX `VPSLLW/D/Q`: logical left shift (`vshift`; SDM Vol. 2B, "PSLLW/PSLLD/PSLLQ"). -/
def Sem.vpsll (e : Nat) (i : Inst) : Prog Ctl := vshift e i fun a k => a <<< k
/-- VEX `VPSRAW/D`: arithmetic right shift (`vshift`; SDM Vol. 2B, "PSRAW/PSRAD/PSRAQ"). -/
def Sem.vpsra (e : Nat) (i : Inst) : Prog Ctl := vshift e i fun a k => a.sshiftRight k

/-- VEX `VPINSRB/D/Q`: insert the low `e` bits of a general register or memory into
element `imm8 mod (128/e)` of the first vector source. Clear ZMM bits above 127.
Memory reads exactly `e/8` bytes, with no SIMD alignment requirement (SDM Vol. 2B,
"PINSRB/PINSRD/PINSRQ", VEX Operation and exception type 5; AMD APM Vol. 4,
"VPINSRB", "VPINSRD", "VPINSRQ"). -/
def Sem.vpinsr (e : Nat) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s₁, s₂, .imm _ k] => do
    let a ← readOp 128 s₁
    let v ← readOp e s₂
    writeOp d (ofElems 128 e fun j => if j = k % (128 / e) then v else elem e a j)
    done
  | _ => formNotModelled i

/-- VEX `VPEXTRB/D/Q`: extract element `imm8 mod (128/e)` to memory or a general
register, zero-extending a register destination. No vector state is written. Memory
writes exactly `e/8` bytes with no SIMD alignment requirement (SDM Vol. 2B,
"PEXTRB/PEXTRD/PEXTRQ", VEX Operation and exception type 5; AMD APM Vol. 4,
"VPEXTRB", "VPEXTRD", "VPEXTRQ"). -/
def Sem.vpextr (e : Nat) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s, .imm _ k] => do
    let a ← readOp 128 s
    writeOp d ((elem e a (k % (128 / e))).setWidth d.width)
    done
  | _ => formNotModelled i

/-- Interleave the low (`hi=false`) or high quadwords independently in each 128-bit
lane. A memory source reads the full vector with no SIMD alignment requirement (SDM
Vol. 2B, "PUNPCKLBW/PUNPCKLWD/PUNPCKLDQ/PUNPCKLQDQ" and
"PUNPCKHBW/PUNPCKHWD/PUNPCKHDQ/PUNPCKHQDQ", VEX Operation, exception type 4;
AMD APM Vol. 4, "VPUNPCKLQDQ", "VPUNPCKHQDQ"). -/
def vunpackQ (hi : Bool) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s₁, s₂] => do
    let w := d.width
    let a ← readOp w s₁
    let b ← readOp w s₂
    writeOp d (ofElems w 64 fun j =>
      elem 64 (if j % 2 = 0 then a else b) (2 * (j / 2) + if hi then 1 else 0))
    done
  | _ => formNotModelled i

/-- VEX `VPUNPCKLQDQ` (`vunpackQ`; SDM Vol. 2B, "PUNPCKLQDQ"). -/
def Sem.vpunpcklqdq (i : Inst) : Prog Ctl := vunpackQ false i
/-- VEX `VPUNPCKHQDQ` (`vunpackQ`; SDM Vol. 2B, "PUNPCKHQDQ"). -/
def Sem.vpunpckhqdq (i : Inst) : Prog Ctl := vunpackQ true i

/-- Insert an XMM/m128 into half `imm8 mod 2` of a YMM source; clear ZMM bits above
255. Memory reads 16 bytes at any alignment. Floating-point forms move bits, with no
floating-point exceptions (SDM Vol. 2C, "VINSERTI128" and "VINSERTF128", VEX
Operation, exception type 6; AMD APM Vol. 4, "VINSERTI128", "VINSERTF128"). -/
def vinsertHalf (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s₁, s₂, .imm _ k] => do
    let a ← readOp 256 s₁
    let b ← readOp 128 s₂
    writeOp d (ofElems 256 128 fun j => if j = k % 2 then b else elem 128 a j)
    done
  | _ => formNotModelled i

/-- Extract half `imm8 mod 2` of a YMM to XMM/m128; an XMM destination clears ZMM
bits above 127. Memory writes 16 bytes at any alignment (SDM Vol. 2C,
"VEXTRACTI128" and "VEXTRACTF128", VEX Operation, exception type 6;
AMD APM Vol. 4, "VEXTRACTI128", "VEXTRACTF128"). -/
def vextractHalf (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s, .imm _ k] => do
    let a ← readOp 256 s
    writeOp d (elem 128 a (k % 2))
    done
  | _ => formNotModelled i

/-- `VINSERTI128` (`vinsertHalf`; SDM Vol. 2C, "VINSERTI128"). -/
def Sem.vinserti128 (i : Inst) : Prog Ctl := vinsertHalf i
/-- `VINSERTF128` (`vinsertHalf`; SDM Vol. 2C, "VINSERTF128"). -/
def Sem.vinsertf128 (i : Inst) : Prog Ctl := vinsertHalf i
/-- `VEXTRACTI128` (`vextractHalf`; SDM Vol. 2C, "VEXTRACTI128"). -/
def Sem.vextracti128 (i : Inst) : Prog Ctl := vextractHalf i
/-- `VEXTRACTF128` (`vextractHalf`; SDM Vol. 2C, "VEXTRACTF128"). -/
def Sem.vextractf128 (i : Inst) : Prog Ctl := vextractHalf i

/-- A vector operation `d := f s₁ s₂` on `esz`-bit elements, merging or zeroing under the
opmask (exception types 4 and E4: any alignment). Without fault suppression (`nf`, class E4NF)
a memory source is read whole whatever the opmask. -/
def vbinop (esz : Nat) (i : Inst) (f : {w : Nat} → BitVec w → BitVec w → BitVec w) (nf : Bool := false) :
    Prog Ctl :=
  match i.ops with
  | [d, s₁, s₂] => do
    let w := d.width
    let km ← maskBits i
    let a ← readOp w s₁
    let b ← if nf then readOp w s₂ else readSrc i w esz km s₂
    writeMasked i esz km d (f a b)
    done
  | _ => formNotModelled i

/-- `VPXOR` (VEX; SDM Vol. 2, "PXOR"). -/
def Sem.vpxor (i : Inst) : Prog Ctl := vbinop 64 i fun a b => a ^^^ b
/-- `VPXORD` (EVEX; SDM Vol. 2, "PXOR"). -/
def Sem.vpxord (i : Inst) : Prog Ctl := vbinop 32 i fun a b => a ^^^ b
/-- `VPXORQ` (EVEX). -/
def Sem.vpxorq (i : Inst) : Prog Ctl := vbinop 64 i fun a b => a ^^^ b
/-- `VPOR` (VEX; SDM Vol. 2, "POR"). -/
def Sem.vpor (i : Inst) : Prog Ctl := vbinop 64 i fun a b => a ||| b
/-- `VPORD` (EVEX). -/
def Sem.vpord (i : Inst) : Prog Ctl := vbinop 32 i fun a b => a ||| b
/-- `VPORQ` (EVEX). -/
def Sem.vporq (i : Inst) : Prog Ctl := vbinop 64 i fun a b => a ||| b
/-- `VPAND` (VEX; SDM Vol. 2, "PAND"). -/
def Sem.vpand (i : Inst) : Prog Ctl := vbinop 64 i fun a b => a &&& b
/-- `VPANDD` (EVEX). -/
def Sem.vpandd (i : Inst) : Prog Ctl := vbinop 32 i fun a b => a &&& b
/-- `VPANDQ` (EVEX). -/
def Sem.vpandq (i : Inst) : Prog Ctl := vbinop 64 i fun a b => a &&& b
/-- `VPANDN`: `(NOT s₁) AND s₂` (VEX; SDM Vol. 2, "PANDN"). -/
def Sem.vpandn (i : Inst) : Prog Ctl := vbinop 64 i fun a b => ~~~a &&& b
/-- `VPANDND` (EVEX). -/
def Sem.vpandnd (i : Inst) : Prog Ctl := vbinop 32 i fun a b => ~~~a &&& b
/-- `VPANDNQ` (EVEX). -/
def Sem.vpandnq (i : Inst) : Prog Ctl := vbinop 64 i fun a b => ~~~a &&& b

/-- `VANDPS` (VEX; SDM Vol. 2, "ANDPS"). -/
def Sem.vandps (i : Inst) : Prog Ctl := vbinop 32 i fun a b => a &&& b
/-- `VANDPD` (VEX). -/
def Sem.vandpd (i : Inst) : Prog Ctl := vbinop 64 i fun a b => a &&& b
/-- `VANDNPS`: `(NOT s₁) AND s₂` (VEX; SDM Vol. 2, "ANDNPS"). -/
def Sem.vandnps (i : Inst) : Prog Ctl := vbinop 32 i fun a b => ~~~a &&& b
/-- `VANDNPD` (VEX; SDM Vol. 2, "ANDNPD"). -/
def Sem.vandnpd (i : Inst) : Prog Ctl := vbinop 64 i fun a b => ~~~a &&& b
/-- `VORPS` (VEX; SDM Vol. 2, "ORPS"). -/
def Sem.vorps (i : Inst) : Prog Ctl := vbinop 32 i fun a b => a ||| b
/-- `VORPD` (VEX; SDM Vol. 2, "ORPD"). -/
def Sem.vorpd (i : Inst) : Prog Ctl := vbinop 64 i fun a b => a ||| b
/-- `VXORPS` (VEX; SDM Vol. 2, "XORPS"). -/
def Sem.vxorps (i : Inst) : Prog Ctl := vbinop 32 i fun a b => a ^^^ b
/-- `VXORPD` (VEX; SDM Vol. 2, "XORPD"). -/
def Sem.vxorpd (i : Inst) : Prog Ctl := vbinop 64 i fun a b => a ^^^ b

/-- `f` on each 128-bit lane of `a` and `b` (the VEX.256 forms of the unpacks and shuffles work
within each 128-bit lane: SDM Vol. 2, "UNPCKLPS", ..., Operation "VUNPCKLPS (VEX.256 encoded
version)"); `f` gets the lane's index. -/
def perLane128 (f : Nat → BitVec 128 → BitVec 128 → BitVec 128) {w : Nat} (a b : BitVec w) : BitVec w :=
  ofElems w 128 fun l => f l (elem 128 a l) (elem 128 b l)

/-- `VUNPCKLPS` (VEX; SDM Vol. 2, "UNPCKLPS"): `interleave` of the low doublewords per lane. -/
def Sem.vunpcklps (i : Inst) : Prog Ctl := vbinop 32 i (perLane128 fun _ a b => ofDwords (interleave 32 0 a b))
/-- `VUNPCKLPD` (VEX; SDM Vol. 2, "UNPCKLPD"). -/
def Sem.vunpcklpd (i : Inst) : Prog Ctl := vbinop 64 i (perLane128 fun _ a b => ofQwords (interleave 64 0 a b))
/-- `VUNPCKHPS` (VEX; SDM Vol. 2, "UNPCKHPS"). -/
def Sem.vunpckhps (i : Inst) : Prog Ctl := vbinop 32 i (perLane128 fun _ a b => ofDwords (interleave 32 2 a b))
/-- `VUNPCKHPD` (VEX; SDM Vol. 2, "UNPCKHPD"). -/
def Sem.vunpckhpd (i : Inst) : Prog Ctl := vbinop 64 i (perLane128 fun _ a b => ofQwords (interleave 64 1 a b))

/-- `VSHUFPS` (VEX; SDM Vol. 2, "SHUFPS"): in each 128-bit lane, doublewords 0 and 1 from the first
source, 2 and 3 from the second, chosen by the immediate's 2-bit fields (the same in every lane). -/
def Sem.vshufps (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s₁, s₂, .imm _ k] => vbinop 32 { i with ops := [d, s₁, s₂] }
      (perLane128 fun _ a b => ofDwords fun j => lane 32 (if j < 2 then a else b) (k / 4 ^ j % 4))
  | _ => formNotModelled i

/-- `VSHUFPD` (VEX; SDM Vol. 2, "SHUFPD"): in 128-bit lane `l`, quadword 0 from the first source and
quadword 1 from the second, chosen by immediate bits `2l` and `2l + 1`. -/
def Sem.vshufpd (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s₁, s₂, .imm _ k] => vbinop 64 { i with ops := [d, s₁, s₂] }
      (perLane128 fun l a b => ofQwords fun j => lane 64 (if j = 0 then a else b) (k / 2 ^ (2 * l + j) % 2))
  | _ => formNotModelled i

/-- `VMOVMSKPS`, `VMOVMSKPD` (VEX; SDM Vol. 2, "MOVMSKPS", "MOVMSKPD"): bit `j` of the general
register is the sign bit of element `j` of `esz` bits, the other bits 0. -/
def vmovmsk (esz : Nat) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do
    let b ← readOp s.width s
    writeOp d (ofBits 32 fun j => j < s.width / esz && (elem esz b j).msb)
    done
  | _ => formNotModelled i

/-- `VMOVMSKPS` (`vmovmsk`). -/
def Sem.vmovmskps (i : Inst) : Prog Ctl := vmovmsk 32 i
/-- `VMOVMSKPD` (`vmovmsk`). -/
def Sem.vmovmskpd (i : Inst) : Prog Ctl := vmovmsk 64 i

/-- `VMOVSS`, `VMOVSD` (VEX; SDM Vol. 2, "MOVSS", "MOVSD"): from memory the low `w` bits, the rest of
the register cleared; to memory the low `w` bits; between registers (three operands) the low `w`
bits of the second source with bits 127 to `w` of the first, the bits above 127 cleared. -/
def vmovScalar (w : Nat) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s₁, s₂] => do
    let a ← readOp 128 s₁
    let b ← readOp w s₂
    writeOp d ((a >>> w <<< w) ||| b.setWidth 128)
    done
  | [d, s] => do
    let v ← readOp w s
    writeOp d v
    done
  | _ => formNotModelled i

/-- `VMOVSS` (`vmovScalar`). -/
def Sem.vmovss (i : Inst) : Prog Ctl := vmovScalar 32 i
/-- `VMOVSD` (`vmovScalar`). -/
def Sem.vmovsd (i : Inst) : Prog Ctl := vmovScalar 64 i
/-- `VMOVUPD` (VEX; SDM Vol. 2, "MOVUPD"). -/
def Sem.vmovupd (i : Inst) : Prog Ctl := vmove 64 false i
/-- `VMOVAPD` (VEX; SDM Vol. 2, "MOVAPD"). -/
def Sem.vmovapd (i : Inst) : Prog Ctl := vmove 64 true i

/-- `g` on each `e`-bit element of `a` and `b`. -/
def lanes (e : Nat) (g : BitVec e → BitVec e → BitVec e) {w : Nat} (a b : BitVec w) : BitVec w :=
  ofElems w e fun j => g (elem e a j) (elem e b j)

/-- `VPADDB`, `VPADDW`, `VPADDD`, `VPADDQ`: element-wise addition, wrapping (SDM Vol. 2,
"PADDB/PADDW/PADDD/PADDQ"). -/
def Sem.vpadd (e : Nat) (i : Inst) : Prog Ctl := vbinop e i (lanes e fun x y => x + y)
/-- `VPSUBB`, `VPSUBW`, `VPSUBD`, `VPSUBQ`: element-wise subtraction, wrapping (SDM Vol. 2,
"PSUBB/PSUBW/PSUBD", "PSUBQ"). -/
def Sem.vpsub (e : Nat) (i : Inst) : Prog Ctl := vbinop e i (lanes e fun x y => x - y)

/-- VEX/EVEX `VPADDS` on `e`-bit elements with merging/zeroing and element fault
suppression (`addSignedSat`). SDM Vol. 2, "PADDSB/PADDSW"; AMD APM Vol. 4,
"PADDSB, VPADDSB" and the word counterpart. -/
def Sem.vpadds (e : Nat) (i : Inst) : Prog Ctl := vbinop e i (lanes e addSignedSat)

/-- VEX/EVEX `VPADDUS` on `e`-bit elements with merging/zeroing and element fault
suppression (`addUnsignedSat`). SDM Vol. 2, "PADDUSB/PADDUSW"; AMD APM Vol. 4,
"PADDUSB, VPADDUSB" and the word counterpart. -/
def Sem.vpaddus (e : Nat) (i : Inst) : Prog Ctl := vbinop e i (lanes e addUnsignedSat)

/-- VEX/EVEX `VPSUBS` on `e`-bit elements with merging/zeroing and element fault
suppression (`subSignedSat`). SDM Vol. 2, "PSUBSB/PSUBSW"; AMD APM Vol. 4,
"PSUBSB, VPSUBSB" and the word counterpart. -/
def Sem.vpsubs (e : Nat) (i : Inst) : Prog Ctl := vbinop e i (lanes e subSignedSat)

/-- `VPSUBUSB`, `VPSUBUSW`: element-wise unsigned subtraction saturated at 0 (`subUnsignedSat`; SDM
Vol. 2, "PSUBUSB/PSUBUSW"; AMD APM Vol. 4, "PSUBUSB, VPSUBUSB", "PSUBUSW, VPSUBUSW"). -/
def Sem.vpsubus (e : Nat) (i : Inst) : Prog Ctl := vbinop e i (lanes e subUnsignedSat)
/-- `VPMULUDQ`: the unsigned products of the low doublewords of each quadword (`mulDQ`; SDM
Vol. 2, "PMULUDQ"; AMD APM Vol. 4, "PMULUDQ, VPMULUDQ"). -/
def Sem.vpmuludq (i : Inst) : Prog Ctl := vbinop 64 i (mulDQ false)
/-- VPAVGB: upward-rounded unsigned byte averages, with byte masking and fault
suppression. SDM Vol. 2, "PAVGB/PAVGW"; AMD APM Vol. 4, "PAVGB, VPAVGB". -/
def Sem.vpavgb (i : Inst) : Prog Ctl := vbinop 8 i (lanes 8 averageUnsigned)
/-- VPAVGW: upward-rounded unsigned word averages, with word masking and fault
suppression. SDM Vol. 2, "PAVGB/PAVGW"; AMD APM Vol. 4, "PAVGW, VPAVGW". -/
def Sem.vpavgw (i : Inst) : Prog Ctl := vbinop 16 i (lanes 16 averageUnsigned)
/-- VPSADBW: eight-byte absolute-difference sums in consecutive quadwords (`sadBytes`).
EVEX allows no masking or broadcast and has no memory fault suppression (E4NF).
SDM Vol. 2, "PSADBW"; AMD APM Vol. 4, "PSADBW, VPSADBW". -/
def Sem.vpsadbw (i : Inst) : Prog Ctl := vbinop 64 i sadBytes (nf := true)

/-- `VPMULDQ`: the signed 64-bit products of the low doublewords of each quadword, masking 64-bit outputs.
VEX exception type 4; EVEX E4.
SDM Vol. 2, "PMULDQ"; AMD APM Vol. 4, "PMULDQ, VPMULDQ". -/
def Sem.vpmuldq (i : Inst) : Prog Ctl := vbinop 64 i (mulDQ true)
/-- `VPMULHW`: the high 16 bits of each signed word product, masking 16-bit outputs.
VEX exception type 4; EVEX E4.
SDM Vol. 2, "PMULHW"; AMD APM Vol. 4, "PMULHW, VPMULHW". -/
def Sem.vpmulhw (i : Inst) : Prog Ctl := vbinop 16 i (lanes 16 (mulWord true true))
/-- `VPMULHUW`: the high 16 bits of each unsigned word product, masking 16-bit outputs.
VEX exception type 4; EVEX E4.
SDM Vol. 2, "PMULHUW"; AMD APM Vol. 4, "PMULHUW, VPMULHUW". -/
def Sem.vpmulhuw (i : Inst) : Prog Ctl := vbinop 16 i (lanes 16 (mulWord false true))
/-- `VPMULLW`: the low 16 bits of each word product, masking 16-bit outputs.
VEX exception type 4; EVEX E4.
SDM Vol. 2, "PMULLW"; AMD APM Vol. 4, "PMULLW, VPMULLW". -/
def Sem.vpmullw (i : Inst) : Prog Ctl := vbinop 16 i (lanes 16 (mulWord true false))
/-- `VPMADDWD`: adjacent signed word products added modulo 2^32 into doublewords, masking 32-bit outputs.
VEX exception type 4; EVEX E4NF.
The full memory source is read under every opmask (E4NF), without fault suppression.
SDM Vol. 2, "PMADDWD"; AMD APM Vol. 4, "PMADDWD, VPMADDWD". -/
def Sem.vpmaddwd (i : Inst) : Prog Ctl := vbinop 32 i (maddPairs 16 false false) (nf := true)
/-- `VPMADDUBSW`: unsigned first-source bytes multiplied by signed second-source bytes,
with adjacent products added and saturated to signed words, masking 16-bit outputs.
VEX exception type 4; EVEX E4NF.
The full memory source is read under every opmask (E4NF), without fault suppression.
SDM Vol. 2, "PMADDUBSW"; AMD APM Vol. 4, "PMADDUBSW, VPMADDUBSW". -/
def Sem.vpmaddubsw (i : Inst) : Prog Ctl := vbinop 16 i (maddPairs 8 true true) (nf := true)
/-- `VPMULHRSW`: signed word products rounded by adding 2^14, taking bits 30–15;
the result truncates without saturation (8000h times 8000h gives 8000h), masking 16-bit outputs.
VEX exception type 4; EVEX E4.
SDM Vol. 2, "PMULHRSW"; AMD APM Vol. 4, "PMULHRSW, VPMULHRSW". -/
def Sem.vpmulhrsw (i : Inst) : Prog Ctl := vbinop 16 i (lanes 16 (mulRoundWord))

/-- `VPACKUSWB` packs signed 16-bit source elements to unsigned 8-bit outputs with saturation in each 128-bit lane (`packSat`).
Each lane's low half comes from src1 and its high half from src2.
EVEX masks the 8-bit outputs, with no memory fault suppression (E4NF); reads the whole vector.
SDM Vol. 2, "PACKUSWB"; AMD APM Vol. 4, "PACKUSWB, VPACKUSWB". -/
def Sem.vpackuswb (i : Inst) : Prog Ctl :=
  vbinop 8 i (perLane128 fun _ a b => packSat 8 false a b) (nf := true)

/-- `VPACKSSWB` packs signed 16-bit source elements to signed 8-bit outputs with saturation in each 128-bit lane (`packSat`).
Each lane's low half comes from src1 and its high half from src2.
EVEX masks the 8-bit outputs, with no memory fault suppression (E4NF); reads the whole vector.
SDM Vol. 2, "PACKSSWB"; AMD APM Vol. 4, "PACKSSWB, VPACKSSWB". -/
def Sem.vpacksswb (i : Inst) : Prog Ctl :=
  vbinop 8 i (perLane128 fun _ a b => packSat 8 true a b) (nf := true)

/-- `VPACKSSDW` packs signed 32-bit source elements to signed 16-bit outputs with saturation in each 128-bit lane (`packSat`).
Each lane's low half comes from src1 and its high half from src2.
EVEX masks the 16-bit outputs, with no memory fault suppression (E4NF); reads the whole vector or the 32-bit broadcast scalar.
SDM Vol. 2, "PACKSSDW"; AMD APM Vol. 4, "PACKSSDW, VPACKSSDW". -/
def Sem.vpackssdw (i : Inst) : Prog Ctl :=
  vbinop 16 i (perLane128 fun _ a b => packSat 16 true a b) (nf := true)

/-- `VPACKUSDW` packs signed 32-bit source elements to unsigned 16-bit outputs with saturation in each 128-bit lane (`packSat`).
Each lane's low half comes from src1 and its high half from src2.
EVEX masks the 16-bit outputs, with no memory fault suppression (E4NF); reads the whole vector or the 32-bit broadcast scalar.
SDM Vol. 2, "PACKUSDW"; AMD APM Vol. 4, "PACKUSDW, VPACKUSDW". -/
def Sem.vpackusdw (i : Inst) : Prog Ctl :=
  vbinop 16 i (perLane128 fun _ a b => packSat 16 false a b) (nf := true)

/-- `VPMINUB`, `VPMINUW`, `VPMINUD`, `VPMINUQ`: the unsigned minimum of each element (SDM Vol. 2,
"PMINUB/PMINUW", "PMINUD/PMINUQ"). -/
def Sem.vpminu (e : Nat) (i : Inst) : Prog Ctl :=
  vbinop e i (lanes e fun x y => if x ≤ y then x else y)
/-- `VPMAXUB`, `VPMAXUW`, `VPMAXUD`, `VPMAXUQ`: the unsigned maximum (SDM Vol. 2,
"PMAXUB/PMAXUW", "PMAXUD/PMAXUQ"). -/
def Sem.vpmaxu (e : Nat) (i : Inst) : Prog Ctl :=
  vbinop e i (lanes e fun x y => if x ≤ y then y else x)
/-- `VPMINSB`, `VPMINSW`, `VPMINSD`, `VPMINSQ`: the signed minimum (SDM Vol. 2, "PMINSB/PMINSW",
"PMINSD/PMINSQ"). -/
def Sem.vpmins (e : Nat) (i : Inst) : Prog Ctl :=
  vbinop e i (lanes e fun x y => if x.sle y then x else y)
/-- `VPMAXSB`, `VPMAXSW`, `VPMAXSD`, `VPMAXSQ`: the signed maximum (SDM Vol. 2, "PMAXSB/PMAXSW",
"PMAXSD/PMAXSQ"). -/
def Sem.vpmaxs (e : Nat) (i : Inst) : Prog Ctl :=
  vbinop e i (lanes e fun x y => if x.sle y then y else x)

/-- Bit `j` of the result is bit `4·a_j + 2·b_j + c_j` of `imm` (SDM Vol. 2,
"VPTERNLOGD/VPTERNLOGQ": `index ← (DEST[j] << 2) OR (SRC2[j] << 1) OR SRC3[j]`), written as the
`OR` of the minterms whose bit `imm` sets. -/
def ternlog {w : Nat} (imm : Nat) (a b c : BitVec w) : BitVec w :=
  (List.range 8).foldl (fun acc k =>
    if imm / 2 ^ k % 2 = 1 then
      acc ||| ((if k / 4 % 2 = 1 then a else ~~~a) &&& (if k / 2 % 2 = 1 then b else ~~~b) &&&
        (if k % 2 = 1 then c else ~~~c))
    else acc) 0

/-- `VPTERNLOGD`, `VPTERNLOGQ` (`e` = 32, 64): the bitwise function `imm` of the destination and
the two sources, under the opmask of `e`-bit elements (SDM Vol. 2, "VPTERNLOGD/VPTERNLOGQ"). -/
def Sem.vpternlog (e : Nat) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s₂, s₃, .imm _ k] => do
    let w := d.width
    let km ← maskBits i
    let a ← readOp w d
    let b ← readOp w s₂
    let c ← readSrc i w e km s₃
    writeMasked i e km d (ternlog k a b c)
    done
  | _ => formNotModelled i

/-- The bytes of `a` chosen by the bytes of `b` within each 128-bit lane: byte `j` is 0 if bit 7
of byte `j` of `b` is set, else byte `b_j mod 16` of `a`'s lane (SDM Vol. 2, "PSHUFB"). -/
def shufBytes {w : Nat} (a b : BitVec w) : BitVec w :=
  ofElems w 8 fun j =>
    if (elem 8 b j).msb then 0 else elem 8 a (j / 16 * 16 + (elem 8 b j).toNat % 16)

/-- `VPSHUFB` (VEX, EVEX; SDM Vol. 2, "PSHUFB"): without fault suppression (exception class
E4NF; AMD APM Vol. 4, "VPSHUFB"), so under an opmask its memory source is read whole. -/
def Sem.vpshufb (i : Inst) : Prog Ctl := vbinop 8 i (fun a b => shufBytes a b) (nf := true)

/-- An element comparison of `s₁` and `s₂` into opmask `d` (EVEX: `VPCMPEQ*`, `VPCMPGT*`,
`VPCMP*`, `VPTESTM*`, `VPTESTNM*`): bit `j` of the destination is `p` of element `j` of the two
sources where the opmask selects it, else 0; bits from `w / e` on are 0 (SDM Vol. 2, e.g.
"VPCMPB/VPCMPUB": `DEST[MAX_KL-1:KL] ← 0`). -/
def cmpToMask (e : Nat) (i : Inst) (d s₁ s₂ : Opd) (p : BitVec e → BitVec e → Bool) : Prog Ctl := do
  let w := s₁.width
  let km ← maskBits i
  let a ← readOp w s₁
  let b ← readSrc i w e km s₂
  writeOp d (ofBits 64 fun j => j < w / e && km.getLsbD j && p (elem e a j) (elem e b j))
  done

/-- An element comparison: into an opmask (EVEX, `cmpToMask`), or each element all ones where
`p` holds, else 0 (VEX). -/
def vcompare (e : Nat) (i : Inst) (p : BitVec e → BitVec e → Bool) : Prog Ctl :=
  match i.ops with
  | [d@(.kreg _), s₁, s₂] => cmpToMask e i d s₁ s₂ p
  | _ => vbinop e i (lanes e fun x y => if p x y then BitVec.allOnes e else 0)

/-- `VPCMPEQB`, `VPCMPEQW`, `VPCMPEQD`, `VPCMPEQQ`: equality (SDM Vol. 2,
"PCMPEQB/PCMPEQW/PCMPEQD", "PCMPEQQ"). -/
def Sem.vpcmpeq (e : Nat) (i : Inst) : Prog Ctl := vcompare e i fun x y => x == y
/-- `VPCMPGTB`, `VPCMPGTW`, `VPCMPGTD`, `VPCMPGTQ`: signed greater-than (SDM Vol. 2,
"PCMPGTB/PCMPGTW/PCMPGTD", "PCMPGTQ"). -/
def Sem.vpcmpgt (e : Nat) (i : Inst) : Prog Ctl := vcompare e i fun x y => y.slt x

/-- Comparison predicate `k` (bits 2–0 of the immediate) of `VPCMP*`, unsigned if `u`: 0 `EQ`, 1
`LT`, 2 `LE`, 3 `FALSE`, 4 `NEQ`, 5 `NLT`, 6 `NLE`, 7 `TRUE` (SDM Vol. 2, "VPCMPB/VPCMPUB",
Operation and Table 5-19). -/
def cmpPred (u : Bool) (k : Nat) {e : Nat} (a b : BitVec e) : Bool :=
  let lt := if u then a.ult b else a.slt b
  match k % 8 with
  | 0 => a == b | 1 => lt | 2 => lt || a == b | 3 => false
  | 4 => a != b | 5 => !lt | 6 => !(lt || a == b) | _ => true

/-- `VPCMPB`, `VPCMPW`, `VPCMPD`, `VPCMPQ` and (`u`) `VPCMPUB`, `VPCMPUW`, `VPCMPUD`, `VPCMPUQ`:
comparison predicate `imm` into an opmask (SDM Vol. 2, "VPCMPB/VPCMPUB", "VPCMPD/VPCMPUD",
"VPCMPQ/VPCMPUQ", "VPCMPW/VPCMPUW"). -/
def Sem.vpcmp (e : Nat) (u : Bool) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s₁, s₂, .imm _ k] => cmpToMask e i d s₁ s₂ (cmpPred u k)
  | _ => formNotModelled i

/-- `VPTESTMB`, `VPTESTMW`, `VPTESTMD`, `VPTESTMQ`: bit `j` set iff element `j` of
`s₁ AND s₂` is not 0 (SDM Vol. 2, "VPTESTMB/VPTESTMW/VPTESTMD/VPTESTMQ"). -/
def Sem.vptestm (e : Nat) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s₁, s₂] => cmpToMask e i d s₁ s₂ fun x y => (x &&& y) != 0
  | _ => formNotModelled i
/-- `VPTESTNMB`, `VPTESTNMW`, `VPTESTNMD`, `VPTESTNMQ`: bit `j` set iff element `j` of
`s₁ AND s₂` is 0 (SDM Vol. 2, "VPTESTNMB/W/D/Q"). -/
def Sem.vptestnm (e : Nat) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s₁, s₂] => cmpToMask e i d s₁ s₂ fun x y => (x &&& y) == 0
  | _ => formNotModelled i

/-- `VPMOVMSKB` (VEX): bit `j` of the general register is bit 7 of byte `j`, the other bits 0
(SDM Vol. 2, "PMOVMSKB"). -/
def Sem.vpmovmskb (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do
    let w := s.width
    let b ← readOp w s
    writeOp d (ofBits 32 fun j => j < w / 8 && (elem 8 b j).msb)
    done
  | _ => formNotModelled i

/-! ## Opmask instructions -/

/-- `KMOVB`, `KMOVW`, `KMOVD`, `KMOVQ` (`e` = 8, 16, 32, 64 bits): the low `e` bits of the
source, zero-extended into a register destination (SDM Vol. 2, "KMOVW/KMOVB/KMOVQ/KMOVD"). -/
def Sem.kmov (e : Nat) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do
    let v ← readOp e s
    writeOp d (v.setWidth d.width)
    done
  | _ => formNotModelled i

/-- `KORTESTB`, `KORTESTW`, `KORTESTD`, `KORTESTQ` (`e` = 8, 16, 32, 64 bits): `ZF` set iff the
`OR` of the low `e` bits of the two opmasks is 0, `CF` iff it is all ones; `OF`, `SF`, `AF`, `PF`
cleared (SDM Vol. 2, "KORTESTW/KORTESTB/KORTESTQ/KORTESTD"). -/
def Sem.kortest (e : Nat) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [a, b] => do
    let x ← readOp e a
    let y ← readOp e b
    let t := x ||| y
    let f ← readFlags
    writeFlags { f with zf := t == 0, cf := t == BitVec.allOnes e, of := false, sf := false,
                        af := false, pf := false }
    done
  | _ => formNotModelled i

/-- `KTESTB`, `KTESTW`, `KTESTD`, `KTESTQ` (`e` = 8, 16, 32, 64 bits): `ZF` set iff the `AND` of the
low `e` bits of the two opmasks is 0, `CF` iff the second `AND NOT` the first is 0; `OF`, `SF`,
`AF`, `PF` cleared (SDM Vol. 2, "KTESTW/KTESTB/KTESTQ/KTESTD"). -/
def Sem.ktest (e : Nat) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [a, b] => do
    let x ← readOp e a
    let y ← readOp e b
    let f ← readFlags
    writeFlags { f with zf := (x &&& y) == 0, cf := (y &&& ~~~x) == 0, of := false, sf := false,
                        af := false, pf := false }
    done
  | _ => formNotModelled i

/-- A logical operation `g` on the low `e` bits of two opmasks, zero-extended into the
destination (`KANDx`, `KANDNx`, `KORx`, `KXNORx`, `KXORx`; SDM Vol. 2, e.g. "KANDW/KANDB/KANDQ/KANDD":
`DEST[MAX_KL-1:16] ← 0`). -/
def klogic (e : Nat) (i : Inst) (g : BitVec e → BitVec e → BitVec e) : Prog Ctl :=
  match i.ops with
  | [d, a, b] => do
    let x ← readOp e a
    let y ← readOp e b
    writeOp d (g x y)
    done
  | _ => formNotModelled i

/-- `KANDB`, `KANDW`, `KANDD`, `KANDQ`: `AND`. -/
def Sem.kand (e : Nat) (i : Inst) : Prog Ctl := klogic e i fun x y => x &&& y
/-- `KANDNB`, `KANDNW`, `KANDND`, `KANDNQ`: `(NOT first) AND second`. -/
def Sem.kandn (e : Nat) (i : Inst) : Prog Ctl := klogic e i fun x y => ~~~x &&& y
/-- `KORB`, `KORW`, `KORD`, `KORQ`: `OR`. -/
def Sem.kor (e : Nat) (i : Inst) : Prog Ctl := klogic e i fun x y => x ||| y
/-- `KXNORB`, `KXNORW`, `KXNORD`, `KXNORQ`: `NOT (first XOR second)`. -/
def Sem.kxnor (e : Nat) (i : Inst) : Prog Ctl := klogic e i fun x y => ~~~(x ^^^ y)
/-- `KXORB`, `KXORW`, `KXORD`, `KXORQ`: `XOR`. -/
def Sem.kxor (e : Nat) (i : Inst) : Prog Ctl := klogic e i fun x y => x ^^^ y

/-- `KNOTB`, `KNOTW`, `KNOTD`, `KNOTQ`: the complement of the low `e` bits, zero-extended (SDM Vol. 2,
"KNOTW/KNOTB/KNOTQ/KNOTD"). -/
def Sem.knot (e : Nat) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [d, s] => do
    let x ← readOp e s
    writeOp d (~~~x)
    done
  | _ => formNotModelled i

/-- Execute VEX or EVEX instruction `i` of mnemonic `m`, with `rip` already advanced past it. -/
def execAvx (prof : Profile) (m : AvxMn) (i : Inst) : Prog Ctl :=
  match m with
  | .vmovdqu => Sem.vmovdqu i | .vmovdqa => Sem.vmovdqa i | .vmovdqu8 => Sem.vmovdqu8 i
  | .vmovdqu16 => Sem.vmovdqu16 i | .vmovdqu32 => Sem.vmovdqu32 i
  | .vmovdqu64 => Sem.vmovdqu64 i | .vmovdqa32 => Sem.vmovdqa32 i
  | .vmovdqa64 => Sem.vmovdqa64 i
  | .vmovups => Sem.vmovups i | .vmovaps => Sem.vmovaps i | .vmovntdq => Sem.vmovntdq i
  | .vpxor => Sem.vpxor i | .vpxord => Sem.vpxord i | .vpxorq => Sem.vpxorq i
  | .vpor => Sem.vpor i | .vpord => Sem.vpord i | .vporq => Sem.vporq i
  | .vpand => Sem.vpand i | .vpandd => Sem.vpandd i | .vpandq => Sem.vpandq i
  | .vpandn => Sem.vpandn i | .vpandnd => Sem.vpandnd i | .vpandnq => Sem.vpandnq i
  | .vpcmpeq e => Sem.vpcmpeq e i | .vpcmpgt e => Sem.vpcmpgt e i | .vpcmp e u => Sem.vpcmp e u i
  | .vptestm e => Sem.vptestm e i | .vptestnm e => Sem.vptestnm e i
  | .vpminu e => Sem.vpminu e i | .vpmaxu e => Sem.vpmaxu e i
  | .vpmins e => Sem.vpmins e i | .vpmaxs e => Sem.vpmaxs e i
  | .vpadd e => Sem.vpadd e i | .vpsub e => Sem.vpsub e i | .vpternlog e => Sem.vpternlog e i
  | .vpadds e => Sem.vpadds e i
  | .vpaddus e => Sem.vpaddus e i
  | .vpsubs e => Sem.vpsubs e i
  | .vpavgb => Sem.vpavgb i
  | .vpavgw => Sem.vpavgw i
  | .vpsadbw => Sem.vpsadbw i
  | .vpmuldq => Sem.vpmuldq i
  | .vpmulhw => Sem.vpmulhw i
  | .vpmulhuw => Sem.vpmulhuw i
  | .vpmullw => Sem.vpmullw i
  | .vpmaddwd => Sem.vpmaddwd i
  | .vpmaddubsw => Sem.vpmaddubsw i
  | .vpmulhrsw => Sem.vpmulhrsw i
  | .vpacksswb => Sem.vpacksswb i
  | .vpackssdw => Sem.vpackssdw i
  | .vpackusdw => Sem.vpackusdw i
  | .vpsubus e => Sem.vpsubus e i | .vpmuludq => Sem.vpmuludq i | .vpackuswb => Sem.vpackuswb i
  | .vpshufb => Sem.vpshufb i | .vpmovmskb => Sem.vpmovmskb i
  | .vpbroadcast e => Sem.vpbroadcast e i | .vbroadcastss => Sem.vbroadcastss i
  | .vzeroupper => Sem.vzeroupper prof i
  | .vzeroall => Sem.vzeroall prof i
  | .vmovd => Sem.vmovd i | .vmovq => Sem.vmovq i
  | .vpsrl e => Sem.vpsrl e i | .vpsll e => Sem.vpsll e i | .vpsra e => Sem.vpsra e i
  | .vpinsr e => Sem.vpinsr e i | .vpextr e => Sem.vpextr e i
  | .vpunpcklqdq => Sem.vpunpcklqdq i | .vpunpckhqdq => Sem.vpunpckhqdq i
  | .vinserti128 => Sem.vinserti128 i | .vextracti128 => Sem.vextracti128 i
  | .vinsertf128 => Sem.vinsertf128 i | .vextractf128 => Sem.vextractf128 i
  | .vmovupd => Sem.vmovupd i | .vmovapd => Sem.vmovapd i | .vmovss => Sem.vmovss i
  | .vmovddup => Sem.dup false true false i
  | .vmovshdup => Sem.dup false false true i
  | .vmovsldup => Sem.dup false false false i
  | .vmovsd => Sem.vmovsd i
  | .vandps => Sem.vandps i | .vandpd => Sem.vandpd i | .vandnps => Sem.vandnps i
  | .vandnpd => Sem.vandnpd i | .vorps => Sem.vorps i | .vorpd => Sem.vorpd i
  | .vxorps => Sem.vxorps i | .vxorpd => Sem.vxorpd i
  | .vunpcklps => Sem.vunpcklps i | .vunpcklpd => Sem.vunpcklpd i
  | .vunpckhps => Sem.vunpckhps i | .vunpckhpd => Sem.vunpckhpd i
  | .vshufps => Sem.vshufps i | .vshufpd => Sem.vshufpd i
  | .vmovmskps => Sem.vmovmskps i | .vmovmskpd => Sem.vmovmskpd i
  | .kmov e => Sem.kmov e i | .kortest e => Sem.kortest e i | .ktest e => Sem.ktest e i
  | .kand e => Sem.kand e i | .kandn e => Sem.kandn e i | .kor e => Sem.kor e i
  | .kxnor e => Sem.kxnor e i | .kxor e => Sem.kxor e i | .knot e => Sem.knot e i

end ZellicX86
