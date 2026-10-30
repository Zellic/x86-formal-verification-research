import ZellicX86.Spec.Profile
import ZellicX86.Spec.Word
/-!
# Decoder: types

What a decoded x86-64 instruction is, and the notation the opcode maps are written in.
The notation follows the Intel SDM, Vol. 2, Appendix A.2 ("Key to Abbreviations"), so the
tables in `Maps.lean` can be compared line by line with the manual's opcode maps
(Tables A-2, A-3, A-4, A-5, A-6).
-/
namespace ZellicX86.Decode

/-- Operand-size codes of SDM Vol. 2 A.2.2: `b` byte, `w` word, `d` doubleword,
`q` quadword, `v` word/doubleword/quadword by operand size, `z` word for 16-bit operand
size else doubleword, `y` doubleword or quadword (by REX.W), `dq` 128 bits, `x` the vector
length of a VEX or EVEX instruction (128, 256 or 512 bits by `VEX.L` or `EVEX.L'L`; SDM: "x"
and "qq"). -/
inductive Sz | b | w | d | q | v | z | y | dq | x

/-- Operand codes of SDM Vol. 2 A.2.1, plus the fixed operands the tables name. -/
inductive OS
  /-- `E`: ModRM r/m, a general register or memory. -/
  | E (s : Sz)
  /-- `G`: ModRM reg, a general register. -/
  | G (s : Sz)
  /-- `I`: immediate of size `s`; for `z` with 64-bit operand size, a doubleword
  sign-extended to 64 bits. -/
  | I (s : Sz)
  /-- An 8-bit immediate sign-extended to the operand size `s` (SDM: "Ib", with the
  instruction's page saying it is sign-extended). -/
  | Ibs (s : Sz)
  /-- `J`: relative offset of size `s`, added to the address of the next instruction. -/
  | J (s : Sz)
  /-- `M`: ModRM r/m, memory only; no access width (`lea`). -/
  | M
  /-- ModRM r/m, a general register of size `r` or memory of size `m` (SDM: "Ry/Mw", the source
  of `PINSRW`). -/
  | ER (r m : Sz)
  /-- Register in the low three bits of the opcode byte, extended by REX.B (SDM:
  "+rb", "+rw", "+rd", "+ro" in the opcode column). -/
  | Z (s : Sz)
  /-- `AL`, `AX`, `EAX` or `RAX` by size. -/
  | A (s : Sz)
  /-- The constant 1 (shift by one). -/
  | one
  /-- The register `CL` (shift count). -/
  | CL
  /-- The count register by address size: `RCX`, or `ECX` with a `67` prefix (`JRCXZ`, `JECXZ`:
  SDM Vol. 2, "Jcc": "The register checked is determined by the address-size attribute"). -/
  | rCX
  /-- `V`: ModRM reg, an XMM register. -/
  | V
  /-- `W`: ModRM r/m, an XMM register or memory of size `s`. -/
  | W (s : Sz)
  /-- `U`: ModRM r/m, an XMM register only. -/
  | U
  /-- The register `XMM0` (implicit operand of `sha256rnds2`). -/
  | XMM0
  /-- `X`: memory at `DS:rSI` (string source; the segment can be overridden). -/
  | X (s : Sz)
  /-- `Y`: memory at `ES:rDI` (string destination). -/
  | Y (s : Sz)
  /-- A VEX or EVEX instruction's vector register in ModRM reg (SDM: `V`), of size `s`; with
  EVEX one of 32 (`EVEX.R'`). -/
  | vecR (s : Sz)
  /-- A VEX or EVEX instruction's vector register in ModRM r/m (with EVEX one of 32, by
  `EVEX.X`), or memory of size `s` (SDM: `W`). -/
  | vecM (s : Sz)
  /-- A VEX or EVEX instruction's vector register in ModRM r/m, register only (SDM: `U`). -/
  | vecU (s : Sz)
  /-- The vector register `VEX.vvvv` names (SDM: `H`); with EVEX one of 32 (`EVEX.V'`). -/
  | vecV (s : Sz)
  /-- The general register `VEX.vvvv` names, of size `s` (SDM: `B`). -/
  | gprV (s : Sz)
  /-- An opmask register `k0`–`k7` in ModRM reg (SDM Vol. 2, 2.7.3, Table 2-35). -/
  | kR
  /-- An opmask register in ModRM r/m, or memory of size `s`. -/
  | kM (s : Sz)
  /-- The opmask register `VEX.vvvv` names. -/
  | kV
  /-- The x87 register `ST(0)` (SDM Vol. 2, A.5: the escape tables' "ST(0)"). -/
  | ST0
  /-- The x87 register `ST(i)`, `i` the ModRM byte's r/m field (A.5: "ST(i)"; `REX.B` does not
  extend it, there being eight). -/
  | STi
  /-- ModRM r/m, memory only, of `n` bytes: an x87 instruction's memory operand (A.5: "single-real"
  4, "double-real" 8, "extended-real" 10, "word-integer" 2, "dword-integer" 4, "qword-integer" 8,
  "packed-BCD" 10, "14/28 bytes" 28, "2 bytes" 2, "98/108 bytes" 108), and `FXSAVE`'s 512 bytes. -/
  | Mb (n : Nat)

/-- Condition codes, SDM Vol. 1 B.1, in encoding order (`o no b ae e ne be a s ns p np
l ge le g`). -/
abbrev Cond := Nat

/-- Mnemonics of the legacy SSE instructions (and the SHA extensions, which use the same
registers and encodings). -/
inductive SseMn
  | movups | movaps | movdqa | movdqu | movd | movq | movntps | movntdq
  | movhps | movlps | movlhps | movhlps
  | pxor | por | pand | pandn | paddb | paddw | paddd | paddq | psubb | psubw | psubd | psubq
  | pcmpeqb | pcmpeqw | pcmpeqd | pcmpgtb | pcmpgtw | pcmpgtd | pminub | pmaxub | pmovmskb
  | psrlw | psrld | psrlq | psllw | pslld | psllq | psraw | psrad | psrldq | pslldq
  | pshufd | pshuflw | pshufhw | pinsrw | pextrw
  | pinsrb | pinsrd | pinsrq | pextrb | pextrd | pextrq
  | punpcklbw | punpcklwd | punpckldq | punpcklqdq | punpckhbw | punpckhwd | punpckhdq
  | punpckhqdq | xorps
  | pshufb | palignr | pblendw | pminud | sha256rnds2 | sha256msg1 | sha256msg2
  | pavgb | pavgw | psadbw
  | pmuldq | pmulhw | pmulhuw | pmullw | pmaddwd | pmaddubsw | pmulhrsw
  | pmuludq | psubusb | psubusw | packuswb | packsswb | packssdw | packusdw
  | paddsb | paddsw | paddusb | paddusw | psubsb | psubsw
  | pcmpistri | pcmpistrm
  -- typed floating point, but no arithmetic: moves, bitwise operations, shuffles
  | movupd | movapd | movss | movsd | movlpd | movhpd
  | movddup | movshdup | movsldup
  | andps | andpd | andnps | andnpd | orps | orpd | xorpd
  | unpcklps | unpcklpd | unpckhps | unpckhpd | shufps | shufpd | movmskps | movmskpd
  deriving Repr

/-- The element type of an SSE or AVX floating-point instruction, its mnemonic's suffix: packed
single (`PS`), packed double (`PD`), scalar single (`SS`) or scalar double (`SD`) precision. -/
inductive FpTy | ps | pd | ss | sd
  deriving Repr

/-- FMA3 source orders (SDM Vol. 1, 14.5.1, Table 14-17): the digits name the
multiplicands and addend among destination (1), VEX.vvvv (2), and r/m (3). -/
inductive FmaOrder | o132 | o213 | o231
  deriving Repr

/-- Mnemonics of the SSE and AVX instructions that compute with floating-point values
(`Spec/Float.lean`) or access `MXCSR`. A mnemonic with an argument `t` stands for the forms of
element type `t` (`add .sd` is `ADDSD`; `cvtsi2 .sd` is `CVTSI2SD`; `cvt2si .sd` is `CVTSD2SI`;
`comi .ss` is `COMISS`). Legacy SSE and VEX forms share a mnemonic; the operands tell them apart
(a legacy form has `Opd.xmm` registers and the destination as its first source, a VEX form
`Opd.vreg` registers and a separate first source). -/
inductive FpMn
  | add (t : FpTy) | sub (t : FpTy) | mul (t : FpTy) | div (t : FpTy) | min (t : FpTy) | max (t : FpTy)
  | round (t : FpTy)
  | fma (t : FpTy) (order : FmaOrder) (negProduct subAddend : Bool)
  | addsub (t : FpTy) | hadd (t : FpTy) | hsub (t : FpTy)
  | sqrt (t : FpTy)
  | cmp (t : FpTy) | comi (t : FpTy) | ucomi (t : FpTy)
  | cvtsi2 (t : FpTy) | cvt2si (t : FpTy) | cvtt2si (t : FpTy)
  | cvtss2sd | cvtsd2ss | cvtps2pd | cvtpd2ps | cvtdq2ps | cvtps2dq | cvttps2dq | cvtdq2pd
  | cvtpd2dq | cvttpd2dq
  | ldmxcsr | stmxcsr
  deriving Repr

/-- The six arithmetic operations of the x87 instruction set: `ST(0)` or `ST(i)` combined with an
operand (`FADD`, `FMUL`, `FSUB`, `FSUBR`, `FDIV`, `FDIVR`; the `R` forms reverse the operands). -/
inductive FArith | add | mul | sub | subr | div | divr
  deriving Repr

/-- Mnemonics of the x87 instructions (SDM Vol. 2, A.5, Tables A-7 to A-22; Vol. 1, 8.3), and of
`FXSAVE`/`FXRSTOR`, which save and restore the x87 state with the SSE state (`0F AE /0`, `/1`).
`arith o p` stands for the forms of `FADD` etc. on floating-point operands, with `p` the popping
form (`arith .add true` is `FADDP`); `iarith o` for those on an integer in memory (`FIADD`); `com u
n` for `FCOM` (`u = false`) and `FUCOM` (`u = true`) popping `n` times (`FCOMP`, `FCOMPP`); `comi u
p` for `FCOMI`, `FUCOMI` and their popping forms; `icom p` for `FICOM` and `FICOMP`; `fcmov c` for
`FCMOVcc` with the condition `c` of `Jcc` it tests (`B`, `E`, `BE`, `P` (`FCMOVU`) and their negations).
The
mnemonics follow the SDM's, without the `N` of the non-waiting forms the escape tables list
(`FSTSW` is `FNSTSW`; `FSTSW`, with a `9B` before it, is two instructions). -/
inductive X87Mn
  | fld | fst | fstp | fild | fist | fistp | fisttp | fbld | fbstp | fxch | fcmov (c : Cond)
  | arith (o : FArith) (p : Bool) | iarith (o : FArith)
  | com (u : Bool) (n : Nat) | comi (u : Bool) (p : Bool) | icom (p : Bool) | ftst | fxam
  | fchs | fabs | fld1 | fldl2t | fldl2e | fldpi | fldlg2 | fldln2 | fldz
  | f2xm1 | fyl2x | fptan | fpatan | fxtract | fprem1 | fdecstp | fincstp | fprem | fyl2xp1 | fsqrt
  | fsincos | frndint | fscale | fsin | fcos | fnop | ffree
  | fnstsw | fnstcw | fldcw | fnstenv | fldenv | fnsave | frstor | fnclex | fninit | fwait
  | fxsave | fxrstor
  deriving Repr

/-- Mnemonics of the bit-scan, bit-test and double-shift instructions. -/
inductive BitMn
  | bsf | bsr | tzcnt | lzcnt | bt | bts | btr | btc | shld | shrd
  -- BMI1 and BMI2 (VEX-encoded, general registers)
  | andn | bextr | blsi | blsmsk | blsr | bzhi | sarx | shlx | shrx | rorx | pdep | pext | mulx
  deriving Repr

/-- Mnemonics of the VEX- and EVEX-encoded vector instructions and of the opmask
instructions (SDM Vol. 2, chapters 5 and 6; Vol. 1, chapters 14 and 15). Where VEX and EVEX
forms share a mnemonic (`vpcmpeqb`, `vpminub`), the operands tell them apart. A mnemonic with an
argument `e` stands for the SDM's forms of element size `e` bits (8, 16, 32, 64: the `B`, `W`,
`D`, `Q` forms: `vpcmpeq 8` is `VPCMPEQB`; `kmov 16` is `KMOVW`); `vpcmp e u` is `VPCMPUB` etc.
with `u`, `VPCMPB` etc. without. -/
inductive AvxMn
  | vmovdqu | vmovdqa | vmovdqu8 | vmovdqu16 | vmovdqu32 | vmovdqu64 | vmovdqa32 | vmovdqa64
  | vmovups | vmovaps | vmovntdq
  | vpxor | vpxord | vpxorq | vpor | vpord | vporq | vpand | vpandd | vpandq
  | vpandn | vpandnd | vpandnq
  | vpcmpeq (e : Nat) | vpcmpgt (e : Nat) | vpcmp (e : Nat) (u : Bool)
  | vptestm (e : Nat) | vptestnm (e : Nat)
  | vpminu (e : Nat) | vpmaxu (e : Nat) | vpmins (e : Nat) | vpmaxs (e : Nat)
  | vpadd (e : Nat) | vpsub (e : Nat) | vpternlog (e : Nat) | vpshufb
  | vpavgb | vpavgw | vpsadbw
  | vpmuldq | vpmulhw | vpmulhuw | vpmullw | vpmaddwd | vpmaddubsw | vpmulhrsw
  | vpsubus (e : Nat) | vpmuludq | vpackuswb | vpacksswb | vpackssdw | vpackusdw
  | vpadds (e : Nat) | vpaddus (e : Nat) | vpsubs (e : Nat)
  | vpmovmskb | vpbroadcast (e : Nat) | vbroadcastss | vzeroupper | vzeroall
  | vmovd | vmovq
  | vpsrl (e : Nat) | vpsll (e : Nat) | vpsra (e : Nat)
  | vpinsr (e : Nat) | vpextr (e : Nat)
  | vpunpcklqdq | vpunpckhqdq
  | vinserti128 | vextracti128 | vinsertf128 | vextractf128
  | vmovupd | vmovapd | vmovss | vmovsd | vandps | vandpd | vandnps | vandnpd | vorps | vorpd
  | vxorps | vxorpd | vunpcklps | vunpcklpd | vunpckhps | vunpckhpd | vshufps | vshufpd
  | vmovddup | vmovshdup | vmovsldup
  | vmovmskps | vmovmskpd
  | kmov (e : Nat) | kortest (e : Nat) | ktest (e : Nat)
  | kand (e : Nat) | kandn (e : Nat) | kor (e : Nat) | kxnor (e : Nat) | kxor (e : Nat)
  | knot (e : Nat)
  deriving Repr

/-- Mnemonics of the string instructions and of `CLD`/`STD`, which set their direction. -/
inductive StrMn
  | movs | stos | lods | cmps | scas | cld | std
  deriving Repr

/-- Instruction mnemonics the opcode maps name (SDM Vol. 2, chapters 3–6). A mnemonic here
may stand for several SDM entries that differ only in operand size (`cbw` is CBW/CWDE/CDQE).
Families of instructions that the semantics handles together have mnemonics of their own type
(`sse`, `bit`, `str`), so that the semantics chooses an instruction in two small steps. -/
inductive Mn
  | add | or | adc | sbb | and | sub | xor | cmp
  | inc | dec | not | neg | mul | imul | div | idiv | test
  | rol | ror | rcl | rcr | shl | shr | sar
  | mov | movsxd | movzx | movsx | lea | xchg | bswap
  | push | pop | call | jmp | ret | leave
  | jcc (c : Cond) | setcc (c : Cond) | cmovcc (c : Cond)
  /-- `E3`: JRCXZ, or JECXZ with a `67` prefix (the count register an operand, `OS.rCX`). -/
  | jrcxz
  /-- LOOP (`none`), LOOPE (`some true`), LOOPNE (`some false`); count by address size.
  SDM Vol. 2, "LOOP/LOOPcc"; AMD APM Vol. 3, "LOOP". -/
  | loop (zf : Option Bool)
  | cbw | cwd       -- `98`, `99`: CBW/CWDE/CDQE and CWD/CDQ/CQO by operand size
  | nop | pause | endbr64 | rdssp | incssp | hlt | int3 | ud2 | syscall | cpuid | xgetbv | rdtsc
  | cmpxchg | xadd
  | movbe | rdtscp | crc32 | xtest
  /-- `PREFETCHNTA` (`h = 0`), `PREFETCHT0`, `PREFETCHT1`, `PREFETCHT2` (`h` = 1, 2, 3). -/
  | prefetch (h : Nat)
  | lfence | sfence | mfence
  | str (m : StrMn)
  | bit (m : BitMn)
  | sse (m : SseMn)
  | fp (m : FpMn)
  | avx (m : AvxMn)
  | x87 (m : X87Mn)
  deriving Repr

/-- Which opmask an EVEX instruction accepts (SDM Vol. 2, 2.7.4, Table 2-42): none (`EVEX.aaa`
and `EVEX.z` must be 0), merging only (`EVEX.z` must be 0: stores, and instructions whose
destination is an opmask register), or merging and zeroing (`EVEX.z = 1` needs `EVEX.aaa ≠ 0`). -/
inductive Masking | none | merge | full

/-- The scale factor `N` of an EVEX 8-bit displacement, which is `disp8 · N` (SDM Vol. 2, 2.7.5,
Tables 2-36 and 2-37): `full` the vector length in bytes ("Full", "Full Mem" without
broadcast), `scalar n` `n` bytes ("Tuple1 Scalar"). -/
inductive Disp8 | full | scalar (n : Nat)

/-- Superscripts and attributes of an opcode-map entry (SDM Vol. 2 A.2.5). -/
structure Attr where
  /-- `d64`: default operand size 64 in 64-bit mode (a `66` prefix selects 16). -/
  d64 : Bool := false
  /-- `f64`: operand size forced to 64 in 64-bit mode (Intel; AMD honours `66` on near
  branches, so a `66`-prefixed branch without `REX.W` is not modelled; with `REX.W` both vendors
  give 64 bits). -/
  f64 : Bool := false
  /-- `LOCK` is allowed (with a memory destination). -/
  lock : Bool := false
  /-- A string instruction: `F3` acts as `REP` (SDM Vol. 2, "REP"). -/
  str : Bool := false
  /-- A string comparison (`CMPS`, `SCAS`): `F3` acts as `REPE`, `F2` as `REPNE` (SDM Vol. 2,
  "REPE/REPZ", "REPNE/REPNZ"). -/
  strZ : Bool := false
  /-- How an EVEX instruction takes an opmask in `EVEX.aaa` and `EVEX.z`. -/
  masking : Masking := .none
  /-- The factor `N` of an EVEX instruction's compressed 8-bit displacement. -/
  disp8 : Disp8 := .full
  /-- An EVEX instruction that broadcasts its memory source with `EVEX.b`, with elements of
  `some e` bits (the "Full" tuple type of a load-and-operate instruction on doublewords or
  quadwords, SDM Vol. 2, 2.7.5, Table 2-36; 2.7.7). `none`: `EVEX.b` raises `#UD` (Table 2-43,
  the instruction classes of Table 2-37). -/
  bcst : Option Nat := none

/-- CPU features an entry can depend on. -/
inductive Feat
  | ssse3 | sse41 | sse42 | sha | bmi1 | bmi2 | lzcnt | avx | avx2 | avx512f | avx512bw
  | avx512dq | avx512vl | movbe | rdtscp | sse3 | fma | cetSs | rtm | hle

/-- Whether the CPU has feature `f`. -/
def Feat.holds (f : Feat) (p : Features) : Bool :=
  match f with
  | .ssse3 => p.ssse3 | .sse41 => p.sse41 | .sse42 => p.sse42 | .sha => p.sha | .bmi1 => p.bmi1
  | .bmi2 => p.bmi2 | .lzcnt => p.lzcnt | .avx => p.avx | .avx2 => p.avx2
  | .avx512f => p.avx512f | .avx512bw => p.avx512bw | .avx512dq => p.avx512dq
  | .avx512vl => p.avx512vl | .movbe => p.movbe | .rdtscp => p.rdtscp | .sse3 => p.sse3 | .fma => p.fma
  | .cetSs => p.cetSs | .rtm => p.rtm | .hle => p.hle

/-- An opcode-map cell. -/
inductive Entry
  /-- An instruction with its operands, destination first. -/
  | op (mn : Mn) (ops : List OS) (a : Attr)
  /-- Opcode extension by ModRM.reg (SDM Table A-6, "Grp"). -/
  | grp (r0 r1 r2 r3 r4 r5 r6 r7 : Entry)
  /-- Different instructions for a memory (`mod ≠ 3`) and a register (`mod = 3`) r/m. -/
  | byMod (mem reg : Entry)
  /-- Selected by the whole ModRM byte (e.g. `F3 0F 1E FA` is `ENDBR64`). -/
  | byModRM (b : Nat) (hit other : Entry)
  /-- Selected by the ModRM byte's r/m field (bits 2–0), as the x87 escape tables select the
  instructions of a row whose ModRM byte is `C0H` or above (SDM Vol. 2, A.5, Tables A-8 to A-22:
  "the entire ModR/M byte is used as an opcode extension", the row by `mod` and `reg`, the column
  by `r/m`). -/
  | byRM (r0 r1 r2 r3 r4 r5 r6 r7 : Entry)
  /-- Mandatory prefix (SDM Vol. 2 2.1.2 and Table A-3's rows): none, `66`, `F3`, `F2`. -/
  | byPfx (none p66 pF3 pF2 : Entry)
  /-- By REX.W. -/
  | byW (w0 w1 : Entry)
  /-- By REX.B (`90` is `NOP`, but `XCHG r8, rAX` with REX.B). -/
  | byRexB (b0 b1 : Entry)
  /-- By a CPU feature. -/
  | byFeat (f : Feat) (yes no : Entry)
  /-- By the vector length field of a VEX (`VEX.L`: 0 or 1) or EVEX prefix (`EVEX.L'L`: 0 to
  3). -/
  | byL (l0 l1 l2 l3 : Entry)
  /-- An encoding the manuals specify as invalid (in 64-bit mode: the SDM's superscript `i64`):
  `#UD`, after the bytes of the operands `ops` (ModRM, SIB, displacement, immediates), the
  operands of the SDM's cell. The processor fetches an instruction's bytes before it raises `#UD`
  (SDM Vol. 3A, 7.9, Table 7-2; AMD APM Vol. 2, 8.5, Table 8-9: a code page fault has priority
  over an invalid opcode), so a fetch fault on one of them comes first. `ud []`: the opcode is the
  whole encoding. -/
  | ud (ops : List OS)
  /-- The form `e` selects, invalid here (a vector length, `W`, `mod` or mandatory prefix the form
  does not allow): `#UD` after the bytes of that form, as for `ud`. -/
  | invalid (e : Entry)
  /-- The form `e` selects, on a processor without a CPU feature it needs: `#UD` once the form's
  bytes are fetched. How many bytes such a processor fetches first is not settled (a processor that
  does not know the form may decode another length), so the `#UD` is
  modelled only when all 15 bytes an instruction may have can be fetched; a fetch fault on one of
  the form's bytes, or a byte up to the 15th that cannot be fetched, is not modelled
  (`lengthNotSettled`). -/
  | missing (e : Entry)
  /-- A valid encoding the model does not implement. -/
  | nm

/-- Shorthand for table cells without attributes. -/
def op (mn : Mn) (ops : List OS) (a : Attr := {}) : Entry := .op mn ops a

/-- An entry that raises `#UD` unless the CPU has feature `f` (`Entry.missing`). -/
def needs (f : Feat) (e : Entry) : Entry := .byFeat f e (.missing e)

/-- Segment override prefixes. In 64-bit mode only `fs` and `gs` change the address. -/
inductive Seg | es | cs | ss | ds | fs | gs
  deriving DecidableEq, Repr

/-- A general register operand of `width` bits. `high8` selects `AH`/`CH`/`DH`/`BH`
(byte registers 4–7 without a REX prefix). -/
structure GReg where
  width : Nat
  num : Nat
  high8 : Bool
  deriving Repr

/-- A memory operand: `seg:[base + index * scale + disp]`, or `rip + disp`. -/
structure MemOp where
  seg : Option Seg
  base : Option Nat
  index : Option Nat
  scale : Nat
  /-- The displacement, sign-extended to 64 bits (two's complement). -/
  disp : Nat
  ripRel : Bool
  /-- A `67` prefix: 32-bit address computation. -/
  addr32 : Bool
  /-- Access width in bits; 0 for an address-only operand (`lea`). -/
  width : Nat
  deriving Repr

/-- A decoded operand. -/
inductive Opd
  /-- A general register. -/
  | reg (r : GReg)
  /-- Register `XMMn` of a legacy SSE instruction. -/
  | xmm (n : Nat)
  /-- Vector register `n` (0–31) of a VEX or EVEX instruction, `w` bits wide (128: `XMMn`, 256:
  `YMMn`, 512: `ZMMn`). -/
  | vreg (n w : Nat)
  /-- Opmask register `kn`. -/
  | kreg (n : Nat)
  /-- A memory operand. -/
  | mem (m : MemOp)
  /-- An immediate, already extended to `width` bits as the instruction uses it. -/
  | imm (width : Nat) (v : Nat)
  /-- A branch offset from the address of the next instruction, sign-extended to 64 bits
  (two's complement). -/
  | rel (off : Nat)
  /-- An EVEX memory source with embedded broadcast (`EVEX.b`, SDM Vol. 2, 2.7.7): one element of
  `m.width` bits at `m`, repeated to a `w`-bit vector. -/
  | bcst (m : MemOp) (w : Nat)
  /-- The x87 register `ST(i)` (`i` < 8). -/
  | st (i : Nat)
  deriving Repr

/-- A repeat prefix on a string instruction: `F3` (`REP`; `REPE` on `CMPS` and `SCAS`) or
`F2` (`REPNE`, on `CMPS` and `SCAS` only). -/
inductive Rep | rep | repne
  deriving Repr

/-- A decoded instruction. -/
structure Inst where
  mn : Mn
  /-- Operand size in bits (16, 32 or 64; 8 for byte forms). -/
  opsz : Nat
  /-- Operands, destination first. -/
  ops : List Opd
  /-- Length in bytes, prefixes included. -/
  len : Nat
  rep : Option Rep
  /-- A `LOCK` prefix (`F0`). -/
  lock : Bool
  /-- An EVEX instruction that takes an opmask: the register `EVEX.aaa` names (0: no masking).
  `none` for every other instruction. -/
  mask : Option Nat
  /-- Zeroing-masking (`EVEX.z`): masked-off elements of a register destination become 0
  instead of keeping their value. -/
  zero : Bool
  /-- The opcode an x87 instruction leaves in the x87 opcode register `FOP` (SDM Vol. 1, 8.1.9,
  Figure 8-8; APM Vol. 1, 6.2.5.2): bits 10–8 the low three bits of its opcode byte (`D8`–`DF`),
  bits 7–0 its ModRM byte. 0 for every other instruction, `FWAIT` (`9B`) and `FXSAVE`/`FXRSTOR`
  (`0F AE`) included: only the non-control instructions among the escape opcodes set `FOP`
  (`x87Last`). -/
  fop : Nat
  deriving Repr

/-- Result of decoding the bytes at an instruction address. -/
inductive Decoded
  /-- Instruction `i`. -/
  | ok (i : Inst)
  /-- `#UD`: an invalid encoding, or one that needs a feature the CPU lacks, after its bytes
  were fetched. -/
  | ud
  /-- `#GP(0)`: longer than 15 bytes. -/
  | gp
  /-- `#PF`: the byte at this offset from the start cannot be fetched. -/
  | pf (off : Nat)
  /-- A valid encoding the model does not implement, or one whose outcome is not settled: the map (0
  one-byte, `0x0F`, `0x0F38`, `0x0F3A`, `0xC4` for either VEX form, `0x62` EVEX, `0xD5` REX2) and the
  opcode byte (0 where it was not read). Map 0 with opcode `0xC4`, `0xC5` or `0x62` is a VEX or EVEX
  escape whose length is not settled (`decodeInst`, `formatUnknown`). -/
  | nm (map op : Nat)
  deriving Repr

end ZellicX86.Decode
