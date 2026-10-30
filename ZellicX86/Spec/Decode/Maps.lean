import ZellicX86.Spec.Decode.Types
/-!
# Decoder: opcode maps

The one-byte, two-byte (`0F`) and three-byte (`0F 38`, `0F 3A`) opcode maps in 64-bit
mode, in the notation of SDM Vol. 2 Appendix A (Tables A-2 to A-6). Each line is one
cell of the manual's table. Cells not listed are `nm` (not modelled); cells the manual
marks invalid in 64-bit mode (`i64`) are `ud` with the operands of the cell, whose bytes the
processor fetches before it raises `#UD` (`Entry.ud`), as are a few blank cells that both vendors'
decoders treat as invalid (`FF /7`). Prefix bytes (`26 2E 36 3E 40–4F 64–67
F0 F2 F3`) and the escapes (`0F`, `C4`, `C5`, `62`) are handled before the table.

The VEX and EVEX maps (`vex0F`, ..., `evex0F3A`) list, per opcode, the forms of the
instruction pages of SDM Vol. 2 (their "Opcode/Instruction" column: `VEX.L.pp.map.W opcode`),
with the CPU features each needs (its "CPUID Feature Flag" column).
-/
namespace ZellicX86.Decode
open OS Sz

/-- A cell of an SSE instruction. -/
def sse (m : SseMn) (ops : List OS) : Entry := op (.sse m) ops

/-- A cell of an SSE or AVX floating-point instruction (`Mn.fp`). -/
def fp (m : FpMn) (ops : List OS) : Entry := op (.fp m) ops

/-- The four cells of a legacy SSE floating-point arithmetic instruction `m` (`ADDPS`, `ADDPD`,
`ADDSS`, `ADDSD` in the columns of no prefix, `66`, `F3`, `F2`; SDM Table A-3). -/
def fpArith4 (m : FpTy → FpMn) : Entry :=
  .byPfx (fp (m .ps) [V, W dq]) (fp (m .pd) [V, W dq]) (fp (m .ss) [V, W d]) (fp (m .sd) [V, W q])

/-- A cell of a bit instruction (`Mn.bit`). -/
def bit (m : BitMn) (ops : List OS) (a : Attr := {}) : Entry := op (.bit m) ops a

/-- A cell of a string instruction (`Mn.str`). -/
def str (m : StrMn) (ops : List OS) (a : Attr := {}) : Entry := op (.str m) ops a

/-- A cell of a VEX or EVEX vector or opmask instruction (`Mn.avx`). -/
def avx (m : AvxMn) (ops : List OS) (a : Attr := {}) : Entry := op (.avx m) ops a

/-- An entry that needs features `fs`. -/
def needsAll : List Feat → Entry → Entry
  | [], e => e
  | f :: fs, e => needs f (needsAll fs e)

/-- A VEX instruction defined for `VEX.L = 0` only (`VEX.L0`, `VEX.LZ`): `#UD` with `L = 1`. -/
def l0 (e : Entry) : Entry := .byL e (.invalid e) (.invalid e) (.invalid e)

/-- A VEX vector instruction on `XMM` (`L = 0`, feature `f128`) and `YMM` registers (`L = 1`,
feature `f256`). -/
def vexL (f128 f256 : Feat) (e : Entry) : Entry :=
  .byL (needs f128 e) (needs f256 e) (.invalid e) (.invalid e)

/-- An EVEX vector instruction at the three vector lengths (`EVEX.L'L` = 0, 1, 2; 3 is
reserved, SDM Vol. 2, Table 2-38), with the features `fs`; 128 and 256 bits need AVX512VL. A
reserved length is invalid behind the features too (`Entry.missing`: without them it is not settled). -/
def evexL (fs : List Feat) (e : Entry) : Entry :=
  .byL (needsAll (.avx512vl :: fs) e) (needsAll (.avx512vl :: fs) e) (needsAll fs e)
    (needsAll fs (.invalid e))

/-- Group 1 (Table A-6): the eight ALU operations on the operands `ops`. -/
def grp1 (ops : List OS) : Entry :=
  .grp (op .add ops {lock := true}) (op .or ops {lock := true}) (op .adc ops {lock := true})
       (op .sbb ops {lock := true}) (op .and ops {lock := true}) (op .sub ops {lock := true})
       (op .xor ops {lock := true}) (op .cmp ops)

/-- Group 2 (Table A-6): rotates and shifts of `dst` by `cnt`. `/6` is blank in the SDM
(AMD documents it as an alias of `SAL`), so not modelled. -/
def grp2 (dst cnt : OS) : Entry :=
  .grp (op .rol [dst, cnt]) (op .ror [dst, cnt]) (op .rcl [dst, cnt]) (op .rcr [dst, cnt])
       (op .shl [dst, cnt]) (op .shr [dst, cnt]) .nm (op .sar [dst, cnt])

/-- Group 3 (Table A-6) on `E s`; `/0` is `TEST E, I`. `/1` is blank in the SDM. -/
def grp3 (s : Sz) (i : OS) : Entry :=
  .grp (op .test [E s, i]) .nm (op .not [E s] {lock := true}) (op .neg [E s] {lock := true})
       (op .mul [E s]) (op .imul [E s]) (op .div [E s]) (op .idiv [E s])

/-- A cell of an x87 instruction (`Mn.x87`). With a `66`, `F2` or `F3` prefix it is not modelled: the
manuals give the operand-size prefix a meaning only for the format of `FNSTENV`, `FLDENV` (14 bytes
instead of 28) and `FNSAVE`, `FRSTOR` (94 bytes instead of 108), and the others none. -/
def x87 (m : X87Mn) (ops : List OS) : Entry := .byPfx (op (.x87 m) ops) .nm .nm .nm

/-- An x87 escape cell (`D8`–`DF`; SDM Vol. 2, A.5): with a memory operand (`ModRM` below `C0H`)
`ModRM.reg` selects the instruction (`mem`, the eight columns of Tables A-7, A-9, ..., A-21); from
`C0H` on, `ModRM.reg` selects the row half (`reg`: `r0` is `C0`–`C7`, `r1` `C8`–`CF`, ..., `r7`
`F8`–`FF` of Tables A-8, A-10, ..., A-22) and `ModRM.r/m` the column, `ST(i)` or an instruction of its
own (`Entry.byRM`). Blank cells are not modelled. -/
def esc (mem reg : List Entry) : Entry :=
  let g (es : List Entry) : Entry :=
    .grp (es.getD 0 .nm) (es.getD 1 .nm) (es.getD 2 .nm) (es.getD 3 .nm) (es.getD 4 .nm) (es.getD 5 .nm)
      (es.getD 6 .nm) (es.getD 7 .nm)
  .byMod (g mem) (g reg)

/-- A row of an x87 escape table whose eight cells are instructions without operands (`byRM`). -/
def x87Row (ms : List (Option X87Mn)) : Entry :=
  let c (k : Nat) : Entry := match ms.getD k none with
    | some m => x87 m []
    | none => .nm
  .byRM (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6) (c 7)

/-- The six arithmetic instructions of `D8` and `DC` (`FADD` ... `FDIVR`) with operands `ops`, and the
comparisons `FCOM`, `FCOMP` between them (`ModRM.reg` 2 and 3; `com` their operands). -/
def x87Arith (ops com : List OS) : List Entry :=
  [x87 (.arith .add false) ops, x87 (.arith .mul false) ops, x87 (.com false 0) com, x87 (.com false 1) com,
   x87 (.arith .sub false) ops, x87 (.arith .subr false) ops, x87 (.arith .div false) ops,
   x87 (.arith .divr false) ops]

/-- The integer arithmetic of `DA` and `DE` on a memory operand of `n` bytes (`FIADD` ... `FIDIVR`,
with `FICOM`, `FICOMP`). -/
def x87IArith (n : Nat) : List Entry :=
  [x87 (.iarith .add) [Mb n], x87 (.iarith .mul) [Mb n], x87 (.icom false) [Mb n], x87 (.icom true) [Mb n],
   x87 (.iarith .sub) [Mb n], x87 (.iarith .subr) [Mb n], x87 (.iarith .div) [Mb n], x87 (.iarith .divr) [Mb n]]

/-- The one-byte opcode map, SDM Table A-2. -/
def oneByte : Nat → Entry
  | 0x00 => op .add [E b, G b] {lock := true}
  | 0x01 => op .add [E v, G v] {lock := true}
  | 0x02 => op .add [G b, E b]
  | 0x03 => op .add [G v, E v]
  | 0x04 => op .add [A b, I b]
  | 0x05 => op .add [A v, I z]
  | 0x06 => .ud [] | 0x07 => .ud []
  | 0x08 => op .or [E b, G b] {lock := true}
  | 0x09 => op .or [E v, G v] {lock := true}
  | 0x0A => op .or [G b, E b]
  | 0x0B => op .or [G v, E v]
  | 0x0C => op .or [A b, I b]
  | 0x0D => op .or [A v, I z]
  | 0x0E => .ud []
  | 0x10 => op .adc [E b, G b] {lock := true}
  | 0x11 => op .adc [E v, G v] {lock := true}
  | 0x12 => op .adc [G b, E b]
  | 0x13 => op .adc [G v, E v]
  | 0x14 => op .adc [A b, I b]
  | 0x15 => op .adc [A v, I z]
  | 0x16 => .ud [] | 0x17 => .ud []
  | 0x18 => op .sbb [E b, G b] {lock := true}
  | 0x19 => op .sbb [E v, G v] {lock := true}
  | 0x1A => op .sbb [G b, E b]
  | 0x1B => op .sbb [G v, E v]
  | 0x1C => op .sbb [A b, I b]
  | 0x1D => op .sbb [A v, I z]
  | 0x1E => .ud [] | 0x1F => .ud []
  | 0x20 => op .and [E b, G b] {lock := true}
  | 0x21 => op .and [E v, G v] {lock := true}
  | 0x22 => op .and [G b, E b]
  | 0x23 => op .and [G v, E v]
  | 0x24 => op .and [A b, I b]
  | 0x25 => op .and [A v, I z]
  | 0x27 => .ud []
  | 0x28 => op .sub [E b, G b] {lock := true}
  | 0x29 => op .sub [E v, G v] {lock := true}
  | 0x2A => op .sub [G b, E b]
  | 0x2B => op .sub [G v, E v]
  | 0x2C => op .sub [A b, I b]
  | 0x2D => op .sub [A v, I z]
  | 0x2F => .ud []
  | 0x30 => op .xor [E b, G b] {lock := true}
  | 0x31 => op .xor [E v, G v] {lock := true}
  | 0x32 => op .xor [G b, E b]
  | 0x33 => op .xor [G v, E v]
  | 0x34 => op .xor [A b, I b]
  | 0x35 => op .xor [A v, I z]
  | 0x37 => .ud []
  | 0x38 => op .cmp [E b, G b]
  | 0x39 => op .cmp [E v, G v]
  | 0x3A => op .cmp [G b, E b]
  | 0x3B => op .cmp [G v, E v]
  | 0x3C => op .cmp [A b, I b]
  | 0x3D => op .cmp [A v, I z]
  | 0x3F => .ud []
  | 0x50 | 0x51 | 0x52 | 0x53 | 0x54 | 0x55 | 0x56 | 0x57 => op .push [Z v] {d64 := true}
  | 0x58 | 0x59 | 0x5A | 0x5B | 0x5C | 0x5D | 0x5E | 0x5F => op .pop [Z v] {d64 := true}
  | 0x60 => .ud [] | 0x61 => .ud []
  | 0x63 => op .movsxd [G v, E z]   -- the source is 16 bits with a 66 prefix
  | 0x68 => op .push [I z] {d64 := true}
  | 0x69 => op .imul [G v, E v, I z]
  | 0x6A => op .push [Ibs v] {d64 := true}
  | 0x6B => op .imul [G v, E v, Ibs v]
  | 0x70 => op (.jcc 0x0) [J b] {f64 := true}
  | 0x71 => op (.jcc 0x1) [J b] {f64 := true}
  | 0x72 => op (.jcc 0x2) [J b] {f64 := true}
  | 0x73 => op (.jcc 0x3) [J b] {f64 := true}
  | 0x74 => op (.jcc 0x4) [J b] {f64 := true}
  | 0x75 => op (.jcc 0x5) [J b] {f64 := true}
  | 0x76 => op (.jcc 0x6) [J b] {f64 := true}
  | 0x77 => op (.jcc 0x7) [J b] {f64 := true}
  | 0x78 => op (.jcc 0x8) [J b] {f64 := true}
  | 0x79 => op (.jcc 0x9) [J b] {f64 := true}
  | 0x7A => op (.jcc 0xA) [J b] {f64 := true}
  | 0x7B => op (.jcc 0xB) [J b] {f64 := true}
  | 0x7C => op (.jcc 0xC) [J b] {f64 := true}
  | 0x7D => op (.jcc 0xD) [J b] {f64 := true}
  | 0x7E => op (.jcc 0xE) [J b] {f64 := true}
  | 0x7F => op (.jcc 0xF) [J b] {f64 := true}
  | 0x80 => grp1 [E b, I b]
  | 0x81 => grp1 [E v, I z]
  | 0x82 => .ud [E b, I b]   -- Grp 1 Eb, Ib
  | 0x83 => grp1 [E v, Ibs v]
  | 0x84 => op .test [E b, G b]
  | 0x85 => op .test [E v, G v]
  | 0x86 => op .xchg [E b, G b] {lock := true}
  | 0x87 => op .xchg [E v, G v] {lock := true}
  | 0x88 => op .mov [E b, G b]
  | 0x89 => op .mov [E v, G v]
  | 0x8A => op .mov [G b, E b]
  | 0x8B => op .mov [G v, E v]
  | 0x8D => op .lea [G v, M]
  | 0x8F => .grp (op .pop [E v] {d64 := true}) .nm .nm .nm .nm .nm .nm .nm
  | 0x90 => .byRexB (.byPfx (op .nop []) (op .nop []) (op .pause []) (op .nop []))
                   -- `F3` with `REX.B` `90`: `PAUSE` or `XCHG`, which the manuals do not settle: not modelled
                   (.byPfx (op .xchg [Z v, A v]) (op .xchg [Z v, A v]) .nm (op .xchg [Z v, A v]))
  | 0x91 | 0x92 | 0x93 | 0x94 | 0x95 | 0x96 | 0x97 => op .xchg [Z v, A v]
  | 0x98 => op .cbw []
  | 0x99 => op .cwd []
  | 0x9B => x87 .fwait []
  | 0x9A => .ud [I z, I w]   -- far CALL Ap: a 16- or 32-bit offset by operand size and a 16-bit selector
  | 0xA4 => str .movs [Y b, X b] {str := true}
  | 0xA5 => str .movs [Y v, X v] {str := true}
  | 0xA6 => str .cmps [X b, Y b] {str := true, strZ := true}
  | 0xA7 => str .cmps [X v, Y v] {str := true, strZ := true}
  | 0xA8 => op .test [A b, I b]
  | 0xA9 => op .test [A v, I z]
  | 0xAA => str .stos [Y b, A b] {str := true}
  | 0xAB => str .stos [Y v, A v] {str := true}
  | 0xAC => str .lods [A b, X b] {str := true}
  | 0xAD => str .lods [A v, X v] {str := true}
  | 0xAE => str .scas [A b, Y b] {str := true, strZ := true}
  | 0xAF => str .scas [A v, Y v] {str := true, strZ := true}
  | 0xB0 | 0xB1 | 0xB2 | 0xB3 | 0xB4 | 0xB5 | 0xB6 | 0xB7 => op .mov [Z b, I b]
  | 0xB8 | 0xB9 | 0xBA | 0xBB | 0xBC | 0xBD | 0xBE | 0xBF => op .mov [Z v, I v]
  | 0xC0 => grp2 (E b) (I b)
  | 0xC1 => grp2 (E v) (I b)
  | 0xC2 => op .ret [I w] {f64 := true}
  | 0xC3 => op .ret [] {f64 := true}
  | 0xC6 => .grp (op .mov [E b, I b]) .nm .nm .nm .nm .nm .nm .nm
  | 0xC7 => .grp (op .mov [E v, I z]) .nm .nm .nm .nm .nm .nm .nm
  | 0xC9 => op .leave [] {d64 := true}
  | 0xCC => op .int3 []
  | 0xCE => .ud []
  | 0xD0 => grp2 (E b) one
  | 0xD1 => grp2 (E v) one
  | 0xD2 => grp2 (E b) CL
  | 0xD3 => grp2 (E v) CL
  | 0xD4 => .ud [I b] | 0xD5 => .ud [I b]   -- AAM Ib, AAD Ib (D5: REX2 with APX, `decodeInst`)
  | 0xD6 => .ud []
  -- the x87 escapes (SDM Vol. 2, A.5, Tables A-7 to A-22); the SDM's operands, `Mb n` a memory
  -- operand of `n` bytes
  | 0xD8 => esc (x87Arith [Mb 4] [Mb 4]) (x87Arith [ST0, STi] [STi])
  | 0xD9 => esc [x87 .fld [Mb 4], .nm, x87 .fst [Mb 4], x87 .fstp [Mb 4], x87 .fldenv [Mb 28],
                 x87 .fldcw [Mb 2], x87 .fnstenv [Mb 28], x87 .fnstcw [Mb 2]]
                [x87 .fld [STi], x87 .fxch [STi], x87Row [some .fnop], .nm,
                 x87Row [some .fchs, some .fabs, none, none, some .ftst, some .fxam],
                 x87Row [some .fld1, some .fldl2t, some .fldl2e, some .fldpi, some .fldlg2, some .fldln2, some .fldz],
                 x87Row [some .f2xm1, some .fyl2x, some .fptan, some .fpatan, some .fxtract, some .fprem1,
                         some .fdecstp, some .fincstp],
                 x87Row [some .fprem, some .fyl2xp1, some .fsqrt, some .fsincos, some .frndint, some .fscale,
                         some .fsin, some .fcos]]
  | 0xDA => esc (x87IArith 4)
                [x87 (.fcmov 2) [ST0, STi], x87 (.fcmov 4) [ST0, STi], x87 (.fcmov 6) [ST0, STi],
                 x87 (.fcmov 10) [ST0, STi], .nm, x87Row [none, some (.com true 2)]]
  | 0xDB => esc [x87 .fild [Mb 4], needs .sse3 (x87 .fisttp [Mb 4]), x87 .fist [Mb 4], x87 .fistp [Mb 4], .nm,
                 x87 .fld [Mb 10], .nm, x87 .fstp [Mb 10]]
                [x87 (.fcmov 3) [ST0, STi], x87 (.fcmov 5) [ST0, STi], x87 (.fcmov 7) [ST0, STi],
                 x87 (.fcmov 11) [ST0, STi], x87Row [none, none, some .fnclex, some .fninit],
                 x87 (.comi true false) [ST0, STi], x87 (.comi false false) [ST0, STi]]
  -- `DC C0+i` adds `ST(0)` to `ST(i)`; `DC E0+i` is `FSUBR ST(i), ST(0)`, `DC E8+i` `FSUB` (Table A-16)
  | 0xDC => esc (x87Arith [Mb 8] [Mb 8])
                [x87 (.arith .add false) [STi, ST0], x87 (.arith .mul false) [STi, ST0], .nm, .nm,
                 x87 (.arith .subr false) [STi, ST0], x87 (.arith .sub false) [STi, ST0],
                 x87 (.arith .divr false) [STi, ST0], x87 (.arith .div false) [STi, ST0]]
  | 0xDD => esc [x87 .fld [Mb 8], needs .sse3 (x87 .fisttp [Mb 8]), x87 .fst [Mb 8], x87 .fstp [Mb 8],
                 x87 .frstor [Mb 108], .nm, x87 .fnsave [Mb 108], x87 .fnstsw [Mb 2]]
                [x87 .ffree [STi], .nm, x87 .fst [STi], x87 .fstp [STi], x87 (.com true 0) [STi],
                 x87 (.com true 1) [STi]]
  | 0xDE => esc (x87IArith 2)
                [x87 (.arith .add true) [STi, ST0], x87 (.arith .mul true) [STi, ST0], .nm,
                 x87Row [none, some (.com false 2)], x87 (.arith .subr true) [STi, ST0],
                 x87 (.arith .sub true) [STi, ST0], x87 (.arith .divr true) [STi, ST0],
                 x87 (.arith .div true) [STi, ST0]]
  | 0xDF => esc [x87 .fild [Mb 2], needs .sse3 (x87 .fisttp [Mb 2]), x87 .fist [Mb 2], x87 .fistp [Mb 2],
                 x87 .fbld [Mb 10], x87 .fild [Mb 8], x87 .fbstp [Mb 10], x87 .fistp [Mb 8]]
                [.nm, .nm, .nm, .nm, .byRM (x87 .fnstsw [A w]) .nm .nm .nm .nm .nm .nm .nm,
                 x87 (.comi true true) [ST0, STi], x87 (.comi false true) [ST0, STi]]
  -- LOOP/LOOPcc use the address-size count and a 64-bit relative target; `66` is not modelled.
  | 0xE0 => op (.loop (some false)) [J b, rCX] {f64 := true}
  | 0xE1 => op (.loop (some true)) [J b, rCX] {f64 := true}
  | 0xE2 => op (.loop none) [J b, rCX] {f64 := true}
  -- JRCXZ (JECXZ with `67`): the operand size is 64 like every near branch's (`f64`; a `66` without
  -- `REX.W` is not modelled, `finishForm`)
  | 0xE3 => op .jrcxz [J b, rCX] {f64 := true}
  | 0xE8 => op .call [J z] {f64 := true}
  | 0xE9 => op .jmp [J z] {f64 := true}
  | 0xEA => .ud [I z, I w]   -- far JMP Ap
  | 0xEB => op .jmp [J b] {f64 := true}
  | 0xF4 => op .hlt []
  | 0xF6 => grp3 b (I b)
  | 0xF7 => grp3 v (I z)
  | 0xFC => str .cld []
  | 0xFD => str .std []
  | 0xFE => .grp (op .inc [E b] {lock := true}) (op .dec [E b] {lock := true}) .nm .nm .nm .nm .nm .nm
  -- `/7` is blank in both manuals; invalid with its ModRM operand on an AMD Zen 4 and in Intel XED
  | 0xFF => .grp (op .inc [E v] {lock := true}) (op .dec [E v] {lock := true})
                 (op .call [E v] {f64 := true}) .nm (op .jmp [E v] {f64 := true}) .nm
                 (op .push [E v] {d64 := true}) (.ud [E v])
  | _ => .nm

/-- The two-byte opcode map (`0F xx`), SDM Table A-3. SSE rows give the four
mandatory-prefix columns: none, `66`, `F3`, `F2`. -/
def twoByte : Nat → Entry
  -- Group 7 (Table A-6) with a register operand selects by the whole ModRM byte (Table A-6,
  -- "mod 11B"); modelled are `0F 01 D0` (`XGETBV`), `0F 01 D6` (`XTEST`, on a processor with RTM
  -- or HLE: SDM Vol. 2, "XTEST"; blank in the APM's Table A-8, AMD having neither) and `0F 01 F9`
  -- (`RDTSCP`)
  | 0x01 => .byPfx (.byModRM 0xD0 (op .xgetbv [])
                     (.byModRM 0xD6 (.byFeat .rtm (op .xtest []) (needs .hle (op .xtest [])))
                     (.byModRM 0xF9 (needs .rdtscp (op .rdtscp [])) .nm)))
                   .nm .nm .nm
  | 0x05 => op .syscall []
  | 0x0B => op .ud2 []
  | 0x10 => .byPfx (sse .movups [V, W dq]) (sse .movupd [V, W dq]) (sse .movss [V, W d])
                   (sse .movsd [V, W q])
  | 0x11 => .byPfx (sse .movups [W dq, V]) (sse .movupd [W dq, V]) (sse .movss [W d, V])
                   (sse .movsd [W q, V])
  -- `MOVLPD`/`MOVHPD` take a memory operand only (`66 0F 12`/`16` with a register are blank)
  | 0x12 => .byPfx (.byMod (sse .movlps [V, W q]) (sse .movhlps [V, U])) (.byMod (sse .movlpd [V, W q]) .nm)
                   (needs .sse3 (sse .movsldup [V, W dq])) (needs .sse3 (sse .movddup [V, W q]))
  | 0x13 => .byPfx (.byMod (sse .movlps [W q, V]) .nm) (.byMod (sse .movlpd [W q, V]) .nm) .nm .nm
  | 0x14 => .byPfx (sse .unpcklps [V, W dq]) (sse .unpcklpd [V, W dq]) .nm .nm
  | 0x15 => .byPfx (sse .unpckhps [V, W dq]) (sse .unpckhpd [V, W dq]) .nm .nm
  | 0x16 => .byPfx (.byMod (sse .movhps [V, W q]) (sse .movlhps [V, U])) (.byMod (sse .movhpd [V, W q]) .nm)
                   (needs .sse3 (sse .movshdup [V, W dq])) .nm
  | 0x17 => .byPfx (.byMod (sse .movhps [W q, V]) .nm) (.byMod (sse .movhpd [W q, V]) .nm) .nm .nm
  -- Group 16 (Table A-6): the prefetches with a memory operand
  | 0x18 => .byMod (.grp (op (.prefetch 0) [M]) (op (.prefetch 1) [M]) (op (.prefetch 2) [M])
                         (op (.prefetch 3) [M]) .nm .nm .nm .nm) .nm
  -- `0F 1E` is a hint NOP (SDM Vol. 2 "NOP"), except in the F3 column: `F3 0F 1E FA` is
  -- `ENDBR64`, `F3 0F 1E /1` with a register operand is `RDSSPD`/`RDSSPQ`
  | 0x1E => .byPfx (op .nop [E v]) (op .nop [E v])
                   (.byModRM 0xFA (op .endbr64 [])
                     (.byMod (op .nop [E v])
                       (.grp (op .nop [E v]) (op .rdssp [E y]) (op .nop [E v]) (op .nop [E v])
                             (op .nop [E v]) (op .nop [E v]) (op .nop [E v]) (op .nop [E v]))))
                   (op .nop [E v])
  | 0x1F => op .nop [E v]
  | 0x28 => .byPfx (sse .movaps [V, W dq]) (sse .movapd [V, W dq]) .nm .nm
  | 0x29 => .byPfx (sse .movaps [W dq, V]) (sse .movapd [W dq, V]) .nm .nm
  -- `CVTPI2PS`/`CVTPI2PD` (MMX sources) are not modelled
  | 0x2A => .byPfx .nm .nm (fp (.cvtsi2 .ss) [V, E y]) (fp (.cvtsi2 .sd) [V, E y])
  -- NP 0F 2B /r, m128, xmm (SDM MOVNTPS, encoding A; ModRM.mod != 11B).
  | 0x2B =>
    let e := sse .movntps [W dq, V]
    .byPfx (.byMod e (.invalid e)) .nm .nm .nm
  -- `CVTTPS2PI`, `CVTPS2PI` and their `PD` forms (MMX destinations) are not modelled
  | 0x2C => .byPfx .nm .nm (fp (.cvtt2si .ss) [G y, W d]) (fp (.cvtt2si .sd) [G y, W q])
  | 0x2D => .byPfx .nm .nm (fp (.cvt2si .ss) [G y, W d]) (fp (.cvt2si .sd) [G y, W q])
  | 0x2E => .byPfx (fp (.ucomi .ss) [V, W d]) (fp (.ucomi .sd) [V, W q]) .nm .nm
  | 0x2F => .byPfx (fp (.comi .ss) [V, W d]) (fp (.comi .sd) [V, W q]) .nm .nm
  | 0x31 => op .rdtsc []
  | 0x40 => op (.cmovcc 0x0) [G v, E v]
  | 0x41 => op (.cmovcc 0x1) [G v, E v]
  | 0x42 => op (.cmovcc 0x2) [G v, E v]
  | 0x43 => op (.cmovcc 0x3) [G v, E v]
  | 0x44 => op (.cmovcc 0x4) [G v, E v]
  | 0x45 => op (.cmovcc 0x5) [G v, E v]
  | 0x46 => op (.cmovcc 0x6) [G v, E v]
  | 0x47 => op (.cmovcc 0x7) [G v, E v]
  | 0x48 => op (.cmovcc 0x8) [G v, E v]
  | 0x49 => op (.cmovcc 0x9) [G v, E v]
  | 0x4A => op (.cmovcc 0xA) [G v, E v]
  | 0x4B => op (.cmovcc 0xB) [G v, E v]
  | 0x4C => op (.cmovcc 0xC) [G v, E v]
  | 0x4D => op (.cmovcc 0xD) [G v, E v]
  | 0x4E => op (.cmovcc 0xE) [G v, E v]
  | 0x4F => op (.cmovcc 0xF) [G v, E v]
  | 0x50 => .byPfx (.byMod .nm (sse .movmskps [G d, U])) (.byMod .nm (sse .movmskpd [G d, U])) .nm .nm
  | 0x51 => fpArith4 .sqrt
  | 0x54 => .byPfx (sse .andps [V, W dq]) (sse .andpd [V, W dq]) .nm .nm
  | 0x55 => .byPfx (sse .andnps [V, W dq]) (sse .andnpd [V, W dq]) .nm .nm
  | 0x56 => .byPfx (sse .orps [V, W dq]) (sse .orpd [V, W dq]) .nm .nm
  | 0x57 => .byPfx (sse .xorps [V, W dq]) (sse .xorpd [V, W dq]) .nm .nm
  | 0x58 => fpArith4 .add
  | 0x59 => fpArith4 .mul
  | 0x5A => .byPfx (fp .cvtps2pd [V, W q]) (fp .cvtpd2ps [V, W dq]) (fp .cvtss2sd [V, W d])
                   (fp .cvtsd2ss [V, W q])
  | 0x5B => .byPfx (fp .cvtdq2ps [V, W dq]) (fp .cvtps2dq [V, W dq]) (fp .cvttps2dq [V, W dq]) .nm
  | 0x5C => fpArith4 .sub
  | 0x5D => fpArith4 .min
  | 0x5E => fpArith4 .div
  | 0x5F => fpArith4 .max
  | 0x60 => .byPfx .nm (sse .punpcklbw [V, W dq]) .nm .nm
  | 0x61 => .byPfx .nm (sse .punpcklwd [V, W dq]) .nm .nm
  | 0x62 => .byPfx .nm (sse .punpckldq [V, W dq]) .nm .nm
  | 0x63 => .byPfx .nm (sse .packsswb [V, W dq]) .nm .nm
  | 0x64 => .byPfx .nm (sse .pcmpgtb [V, W dq]) .nm .nm
  | 0x65 => .byPfx .nm (sse .pcmpgtw [V, W dq]) .nm .nm
  | 0x66 => .byPfx .nm (sse .pcmpgtd [V, W dq]) .nm .nm
  | 0x67 => .byPfx .nm (sse .packuswb [V, W dq]) .nm .nm
  | 0x68 => .byPfx .nm (sse .punpckhbw [V, W dq]) .nm .nm
  | 0x69 => .byPfx .nm (sse .punpckhwd [V, W dq]) .nm .nm
  | 0x6A => .byPfx .nm (sse .punpckhdq [V, W dq]) .nm .nm
  | 0x6B => .byPfx .nm (sse .packssdw [V, W dq]) .nm .nm
  | 0x6C => .byPfx .nm (sse .punpcklqdq [V, W dq]) .nm .nm
  | 0x6D => .byPfx .nm (sse .punpckhqdq [V, W dq]) .nm .nm
  | 0x6E => .byPfx .nm (.byW (sse .movd [V, E y]) (sse .movq [V, E y])) .nm .nm
  | 0x6F => .byPfx .nm (sse .movdqa [V, W dq]) (sse .movdqu [V, W dq]) .nm
  | 0x70 => .byPfx .nm (sse .pshufd [V, W dq, I b]) (sse .pshufhw [V, W dq, I b])
                   (sse .pshuflw [V, W dq, I b])
  -- Groups 12–14 (Table A-6), shifts of an XMM register by an immediate
  | 0x71 => .byPfx .nm (.byMod .nm (.grp .nm .nm (sse .psrlw [U, I b]) .nm (sse .psraw [U, I b]) .nm
                                            (sse .psllw [U, I b]) .nm)) .nm .nm
  | 0x72 => .byPfx .nm (.byMod .nm (.grp .nm .nm (sse .psrld [U, I b]) .nm (sse .psrad [U, I b]) .nm
                                            (sse .pslld [U, I b]) .nm)) .nm .nm
  | 0x73 => .byPfx .nm (.byMod .nm (.grp .nm .nm (sse .psrlq [U, I b]) (sse .psrldq [U, I b])
                                            .nm .nm (sse .psllq [U, I b]) (sse .pslldq [U, I b])))
                   .nm .nm
  | 0x74 => .byPfx .nm (sse .pcmpeqb [V, W dq]) .nm .nm
  | 0x75 => .byPfx .nm (sse .pcmpeqw [V, W dq]) .nm .nm
  | 0x76 => .byPfx .nm (sse .pcmpeqd [V, W dq]) .nm .nm
  | 0x7C => .byPfx .nm (needs .sse3 (fp (.hadd .pd) [V, W dq])) .nm (needs .sse3 (fp (.hadd .ps) [V, W dq]))
  | 0x7D => .byPfx .nm (needs .sse3 (fp (.hsub .pd) [V, W dq])) .nm (needs .sse3 (fp (.hsub .ps) [V, W dq]))
  | 0x7E => .byPfx .nm (.byW (sse .movd [E y, V]) (sse .movq [E y, V])) (sse .movq [V, W q]) .nm
  | 0x7F => .byPfx .nm (sse .movdqa [W dq, V]) (sse .movdqu [W dq, V]) .nm
  | 0x80 => op (.jcc 0x0) [J z] {f64 := true}
  | 0x81 => op (.jcc 0x1) [J z] {f64 := true}
  | 0x82 => op (.jcc 0x2) [J z] {f64 := true}
  | 0x83 => op (.jcc 0x3) [J z] {f64 := true}
  | 0x84 => op (.jcc 0x4) [J z] {f64 := true}
  | 0x85 => op (.jcc 0x5) [J z] {f64 := true}
  | 0x86 => op (.jcc 0x6) [J z] {f64 := true}
  | 0x87 => op (.jcc 0x7) [J z] {f64 := true}
  | 0x88 => op (.jcc 0x8) [J z] {f64 := true}
  | 0x89 => op (.jcc 0x9) [J z] {f64 := true}
  | 0x8A => op (.jcc 0xA) [J z] {f64 := true}
  | 0x8B => op (.jcc 0xB) [J z] {f64 := true}
  | 0x8C => op (.jcc 0xC) [J z] {f64 := true}
  | 0x8D => op (.jcc 0xD) [J z] {f64 := true}
  | 0x8E => op (.jcc 0xE) [J z] {f64 := true}
  | 0x8F => op (.jcc 0xF) [J z] {f64 := true}
  | 0x90 => op (.setcc 0x0) [E b]
  | 0x91 => op (.setcc 0x1) [E b]
  | 0x92 => op (.setcc 0x2) [E b]
  | 0x93 => op (.setcc 0x3) [E b]
  | 0x94 => op (.setcc 0x4) [E b]
  | 0x95 => op (.setcc 0x5) [E b]
  | 0x96 => op (.setcc 0x6) [E b]
  | 0x97 => op (.setcc 0x7) [E b]
  | 0x98 => op (.setcc 0x8) [E b]
  | 0x99 => op (.setcc 0x9) [E b]
  | 0x9A => op (.setcc 0xA) [E b]
  | 0x9B => op (.setcc 0xB) [E b]
  | 0x9C => op (.setcc 0xC) [E b]
  | 0x9D => op (.setcc 0xD) [E b]
  | 0x9E => op (.setcc 0xE) [E b]
  | 0x9F => op (.setcc 0xF) [E b]
  | 0xA2 => op .cpuid []
  | 0xA3 => bit .bt [E v, G v]
  | 0xA4 => bit .shld [E v, G v, I b]
  | 0xA5 => bit .shld [E v, G v, CL]
  | 0xAB => bit .bts [E v, G v] {lock := true}
  | 0xAC => bit .shrd [E v, G v, I b]
  | 0xAD => bit .shrd [E v, G v, CL]
  -- Group 15 (Table A-6). With a memory operand: `FXSAVE`, `FXRSTOR` (with `REX.W` `FXSAVE64`,
  -- `FXRSTOR64`, operand size 64), `LDMXCSR`, `STMXCSR`; with a register operand: the fences, and in the
  -- `F3` column `/5`, `INCSSPD`/`INCSSPQ` on a processor with CET shadow stacks (without them no manual
  -- specifies it: not modelled)
  | 0xAE => .byPfx (.byMod (.grp (op (.x87 .fxsave) [Mb 512]) (op (.x87 .fxrstor) [Mb 512]) (fp .ldmxcsr [E d])
                                  (fp .stmxcsr [E d]) .nm .nm .nm .nm)
                            (.grp .nm .nm .nm .nm .nm (op .lfence []) (op .mfence []) (op .sfence [])))
                   .nm (.byMod .nm (.grp .nm .nm .nm .nm .nm (.byFeat .cetSs (op .incssp [E y]) .nm) .nm .nm)) .nm
  | 0xAF => op .imul [G v, E v]
  | 0xB0 => op .cmpxchg [E b, G b] {lock := true}
  | 0xB1 => op .cmpxchg [E v, G v] {lock := true}
  | 0xB3 => bit .btr [E v, G v] {lock := true}
  | 0xB6 => op .movzx [G v, E b]
  | 0xB7 => op .movzx [G v, E w]
  -- Group 8 (Table A-6); `/0`–`/3` are blank in the SDM
  | 0xBA => .grp .nm .nm .nm .nm (bit .bt [E v, I b]) (bit .bts [E v, I b] {lock := true})
                 (bit .btr [E v, I b] {lock := true}) (bit .btc [E v, I b] {lock := true})
  | 0xBB => bit .btc [E v, G v] {lock := true}
  | 0xBC => .byPfx (bit .bsf [G v, E v]) (bit .bsf [G v, E v])
                   (.byFeat .bmi1 (bit .tzcnt [G v, E v]) (bit .bsf [G v, E v]))
                   (bit .bsf [G v, E v])
  | 0xBD => .byPfx (bit .bsr [G v, E v]) (bit .bsr [G v, E v])
                   (.byFeat .lzcnt (bit .lzcnt [G v, E v]) (bit .bsr [G v, E v]))
                   (bit .bsr [G v, E v])
  | 0xBE => op .movsx [G v, E b]
  | 0xBF => op .movsx [G v, E w]
  | 0xC0 => op .xadd [E b, G b] {lock := true}
  | 0xC1 => op .xadd [E v, G v] {lock := true}
  | 0xC2 => .byPfx (fp (.cmp .ps) [V, W dq, I b]) (fp (.cmp .pd) [V, W dq, I b]) (fp (.cmp .ss) [V, W d, I b])
                   (fp (.cmp .sd) [V, W q, I b])
  | 0xC4 => .byPfx .nm (sse .pinsrw [V, ER d w, I b]) .nm .nm
  | 0xC5 => .byPfx .nm (.byMod .nm (sse .pextrw [G d, U, I b])) .nm .nm
  | 0xC6 => .byPfx (sse .shufps [V, W dq, I b]) (sse .shufpd [V, W dq, I b]) .nm .nm
  | 0xC8 | 0xC9 | 0xCA | 0xCB | 0xCC | 0xCD | 0xCE | 0xCF => op .bswap [Z v]   -- 16-bit form: result undefined (`Sem.bswap`)
  | 0xD0 => .byPfx .nm (needs .sse3 (fp (.addsub .pd) [V, W dq])) .nm (needs .sse3 (fp (.addsub .ps) [V, W dq]))
  -- shifts by the low 64 bits of an `XMM` register or 16 bytes of memory (the `NP` column, on `MMX`
  -- registers, is not modelled)
  | 0xD1 => .byPfx .nm (sse .psrlw [V, W dq]) .nm .nm
  | 0xD2 => .byPfx .nm (sse .psrld [V, W dq]) .nm .nm
  | 0xD3 => .byPfx .nm (sse .psrlq [V, W dq]) .nm .nm
  | 0xD4 => .byPfx .nm (sse .paddq [V, W dq]) .nm .nm
  | 0xD6 => .byPfx .nm (sse .movq [W q, V]) .nm .nm
  | 0xD7 => .byPfx .nm (sse .pmovmskb [G d, U]) .nm .nm
  | 0xD8 => .byPfx .nm (sse .psubusb [V, W dq]) .nm .nm
  | 0xD9 => .byPfx .nm (sse .psubusw [V, W dq]) .nm .nm
  | 0xDA => .byPfx .nm (sse .pminub [V, W dq]) .nm .nm
  | 0xDB => .byPfx .nm (sse .pand [V, W dq]) .nm .nm
  | 0xDC => .byPfx .nm (sse .paddusb [V, W dq]) .nm .nm
  | 0xDD => .byPfx .nm (sse .paddusw [V, W dq]) .nm .nm
  | 0xDE => .byPfx .nm (sse .pmaxub [V, W dq]) .nm .nm
  | 0xDF => .byPfx .nm (sse .pandn [V, W dq]) .nm .nm
  | 0xE1 => .byPfx .nm (sse .psraw [V, W dq]) .nm .nm
  | 0xE2 => .byPfx .nm (sse .psrad [V, W dq]) .nm .nm
  | 0xE6 => .byPfx .nm (fp .cvttpd2dq [V, W dq]) (fp .cvtdq2pd [V, W q]) (fp .cvtpd2dq [V, W dq])
  -- 66 0F E7 /r, m128, xmm (SDM MOVNTDQ, encoding A; ModRM.mod != 11B).
  | 0xE7 =>
    let e := sse .movntdq [W dq, V]
    .byPfx .nm (.byMod e (.invalid e)) .nm .nm
  | 0xE8 => .byPfx .nm (sse .psubsb [V, W dq]) .nm .nm
  | 0xE9 => .byPfx .nm (sse .psubsw [V, W dq]) .nm .nm
  | 0xEB => .byPfx .nm (sse .por [V, W dq]) .nm .nm
  | 0xEC => .byPfx .nm (sse .paddsb [V, W dq]) .nm .nm
  | 0xED => .byPfx .nm (sse .paddsw [V, W dq]) .nm .nm
  | 0xEF => .byPfx .nm (sse .pxor [V, W dq]) .nm .nm
  | 0xF1 => .byPfx .nm (sse .psllw [V, W dq]) .nm .nm
  | 0xF2 => .byPfx .nm (sse .pslld [V, W dq]) .nm .nm
  | 0xF3 => .byPfx .nm (sse .psllq [V, W dq]) .nm .nm
  | 0xF4 => .byPfx .nm (sse .pmuludq [V, W dq]) .nm .nm
  | 0xF8 => .byPfx .nm (sse .psubb [V, W dq]) .nm .nm
  | 0xF9 => .byPfx .nm (sse .psubw [V, W dq]) .nm .nm
  | 0xFA => .byPfx .nm (sse .psubd [V, W dq]) .nm .nm
  | 0xFB => .byPfx .nm (sse .psubq [V, W dq]) .nm .nm
  | 0xFC => .byPfx .nm (sse .paddb [V, W dq]) .nm .nm
  | 0xFD => .byPfx .nm (sse .paddw [V, W dq]) .nm .nm
  | 0xFE => .byPfx .nm (sse .paddd [V, W dq]) .nm .nm
  | 0xD5 => .byPfx .nm (sse .pmullw [V, W dq]) .nm .nm
  | 0xE4 => .byPfx .nm (sse .pmulhuw [V, W dq]) .nm .nm
  | 0xE5 => .byPfx .nm (sse .pmulhw [V, W dq]) .nm .nm
  | 0xF5 => .byPfx .nm (sse .pmaddwd [V, W dq]) .nm .nm
  | 0xE0 => .byPfx .nm (sse .pavgb [V, W dq]) .nm .nm
  | 0xE3 => .byPfx .nm (sse .pavgw [V, W dq]) .nm .nm
  | 0xF6 => .byPfx .nm (sse .psadbw [V, W dq]) .nm .nm
  | _ => .nm

/-- The three-byte map `0F 38 xx`, SDM Table A-4. -/
def map0F38 : Nat → Entry
  | 0x00 => .byPfx .nm (needs .ssse3 (sse .pshufb [V, W dq])) .nm .nm
  | 0x2B => .byPfx .nm (needs .sse41 (sse .packusdw [V, W dq])) .nm .nm
  -- 66 0F 38 3B /r, xmm, xmm/m128 (SDM PMINUD, encoding A).
  | 0x3B => .byPfx .nm (needs .sse41 (sse .pminud [V, W dq])) .nm .nm
  | 0xCB => .byPfx (needs .sha (sse .sha256rnds2 [V, W dq, XMM0])) .nm .nm .nm
  | 0xCC => .byPfx (needs .sha (sse .sha256msg1 [V, W dq])) .nm .nm .nm
  | 0xCD => .byPfx (needs .sha (sse .sha256msg2 [V, W dq])) .nm .nm .nm
  -- `MOVBE` (memory operand only); the `F2` column (also with `66`, which then selects a 16-bit
  -- source for `F1`) is `CRC32` (SDM Vol. 2, "CRC32"; Table A-4: "66 & F2")
  | 0xF0 => .byPfx (needs .movbe (.byMod (op .movbe [G v, E v]) (.ud [])))
                   (needs .movbe (.byMod (op .movbe [G v, E v]) (.ud []))) .nm
                   (needs .sse42 (op .crc32 [G y, E b]))
  | 0xF1 => .byPfx (needs .movbe (.byMod (op .movbe [E v, G v]) (.ud [])))
                   (needs .movbe (.byMod (op .movbe [E v, G v]) (.ud []))) .nm
                   (needs .sse42 (op .crc32 [G y, E v]))
  | 0x04 => .byPfx .nm (needs .ssse3 (sse .pmaddubsw [V, W dq])) .nm .nm
  | 0x0B => .byPfx .nm (needs .ssse3 (sse .pmulhrsw [V, W dq])) .nm .nm
  | 0x28 => .byPfx .nm (needs .sse41 (sse .pmuldq [V, W dq])) .nm .nm
  | _ => .nm

/-- The three-byte map `0F 3A xx`, SDM Table A-5. -/
def map0F3A : Nat → Entry
  | 0x08 => .byPfx .nm (needs .sse41 (fp (.round .ps) [V, W dq, I b])) .nm .nm
  | 0x09 => .byPfx .nm (needs .sse41 (fp (.round .pd) [V, W dq, I b])) .nm .nm
  | 0x0A => .byPfx .nm (needs .sse41 (fp (.round .ss) [V, W d, I b])) .nm .nm
  | 0x0B => .byPfx .nm (needs .sse41 (fp (.round .sd) [V, W q, I b])) .nm .nm
  | 0x0E => .byPfx .nm (needs .sse41 (sse .pblendw [V, W dq, I b])) .nm .nm
  | 0x0F => .byPfx .nm (needs .ssse3 (sse .palignr [V, W dq, I b])) .nm .nm
  | 0x14 => .byPfx .nm (needs .sse41 (sse .pextrb [ER d b, V, I b])) .nm .nm
  | 0x16 => .byPfx .nm (needs .sse41 (.byW (sse .pextrd [E d, V, I b])
                                                       (sse .pextrq [E q, V, I b]))) .nm .nm
  | 0x20 => .byPfx .nm (needs .sse41 (sse .pinsrb [V, ER d b, I b])) .nm .nm
  | 0x22 => .byPfx .nm (needs .sse41 (.byW (sse .pinsrd [V, E d, I b])
                                                       (sse .pinsrq [V, E q, I b]))) .nm .nm
  | 0x62 => .byPfx .nm (needs .sse42 (sse .pcmpistrm [V, W dq, I b])) .nm .nm
  | 0x63 => .byPfx .nm (needs .sse42 (sse .pcmpistri [V, W dq, I b])) .nm .nm
  | _ => .nm

/-! ## VEX maps -/

/-- An opmask instruction `m e` (VEX-encoded) on the operands `ops`: the forms of its four widths
`e` by prefix and `W`, as the SDM's opmask pages ("KMOVW/KMOVB/KMOVQ/KMOVD", "KANDW/KANDB/KANDQ/
KANDD", ...) encode them: `pp = none` with `W0` the word form (feature `fw`) and with `W1` the
quadword form (AVX512BW); `66` with `W0` the byte form (AVX512DQ) and with `W1` the doubleword
form (AVX512BW). `ops s` are the operands with a memory operand of size `s`. -/
def kWidths (m : Nat → AvxMn) (fw : Feat) (ops : Sz → List OS) : Entry :=
  let np := .byW (needs fw (avx (m 16) (ops .w))) (needs .avx512bw (avx (m 64) (ops .q)))
  .byPfx np (.byW (needs .avx512dq (avx (m 8) (ops .b))) (needs .avx512bw (avx (m 32) (ops .d))))
    (.invalid np) (.invalid np)

/-- An opmask instruction defined for `VEX.L0` (`kWidths`, the word form with AVX512F). -/
def kOp (m : Nat → AvxMn) (ops : Sz → List OS) : Entry := l0 (kWidths m .avx512f ops)

/-- An opmask instruction on two opmask registers and a third in ModRM r/m, defined for `VEX.L1`
(`KAND`, `KOR`, ...: "VEX.L1.0F.W0 41 /r", with `ModRM:[7:6]` 11b). -/
def kOp3 (m : Nat → AvxMn) : Entry :=
  let e := kWidths m .avx512f fun s => [kR, kV, kM s]
  .byMod (.invalid e) (.byL (.invalid e) e (.invalid e) (.invalid e))

/-- A VEX vector instruction at both lengths with AVX and AVX2 (`vexL .avx .avx2`), on a
destination, `vvvv` and a source in ModRM r/m. -/
def vex3 (m : AvxMn) : Entry := vexL .avx .avx2 (avx m [vecR x, vecV x, vecM x])

/-- The four cells of a VEX floating-point arithmetic instruction `m` (`VADDPS`, `VADDPD` on `XMM` and
`YMM` registers, `VADDSS`, `VADDSD` with `VEX.L` ignored: SDM Vol. 2, "ADDPS", ...: `VEX.LIG`), with
the first source in `vvvv`. -/
def vexFp4 (m : FpTy → FpMn) : Entry :=
  .byPfx (vexL .avx .avx (fp (m .ps) [vecR x, vecV x, vecM x]))
         (vexL .avx .avx (fp (m .pd) [vecR x, vecV x, vecM x]))
         (vexL .avx .avx (fp (m .ss) [vecR dq, vecV dq, vecM d]))
         (vexL .avx .avx (fp (m .sd) [vecR dq, vecV dq, vecM q]))

/-- VEX immediate packed shifts: ModRM.reg is the opcode extension, `vvvv` is the
destination, and ModRM.r/m is a register source (SDM Vol. 2B, "PSLLW/PSLLD/PSLLQ",
"PSRLW/PSRLD/PSRLQ", "PSRAW/PSRAD/PSRAQ", operand encoding D). `W` is ignored. -/
def vexShiftImm (m : AvxMn) : Entry :=
  let e := vexL .avx .avx2 (avx m [vecV x, vecU x, I b])
  .byMod (.invalid e) e

/-- VEX packed shifts with an XMM/m128 count, also for a 256-bit destination. The count
is its low 64 bits (SDM Vol. 2B, the packed-shift pages, operand encoding C). -/
def vexShiftCount (m : AvxMn) : Entry :=
  vexL .avx .avx2 (avx m [vecR x, vecV x, vecM dq])

/-- Insert/extract a 128-bit half of a YMM register: `L=1`, `W=0` only (SDM Vol. 2C,
"VINSERTI128", "VEXTRACTI128", "VINSERTF128", "VEXTRACTF128"; AMD APM Vol. 4,
the same instruction pages: `#UD` with `W=1` or `L=0`; the SDM `W=1` rule is
Vol. 2A Table 2-16, "#UD If VEX.W = 1 in All Modes"). -/
def vexHalf (f : Feat) (m : AvxMn) (ops : List OS) : Entry :=
  let e := avx m ops
  needs f (.byL (.invalid e) (.byW e (.invalid e)) (.invalid e) (.invalid e))

/-- The VEX map `0F` (`VEX.mmmmm = 1`). -/
def vex0F : Nat → Entry
  -- `VMOVSS`/`VMOVSD` between registers take three operands (the first source in `vvvv`), to and
  -- from memory two (SDM Vol. 2, "MOVSS", "MOVSD"; `VEX.LIG`)
  | 0x10 => .byPfx (vexL .avx .avx (avx .vmovups [vecR x, vecM x])) (vexL .avx .avx (avx .vmovupd [vecR x, vecM x]))
                   (vexL .avx .avx (.byMod (avx .vmovss [vecR dq, vecM d]) (avx .vmovss [vecR dq, vecV dq, vecM dq])))
                   (vexL .avx .avx (.byMod (avx .vmovsd [vecR dq, vecM q]) (avx .vmovsd [vecR dq, vecV dq, vecM dq])))
  | 0x11 => .byPfx (vexL .avx .avx (avx .vmovups [vecM x, vecR x])) (vexL .avx .avx (avx .vmovupd [vecM x, vecR x]))
                   (vexL .avx .avx (.byMod (avx .vmovss [vecM d, vecR dq]) (avx .vmovss [vecM dq, vecV dq, vecR dq])))
                   (vexL .avx .avx (.byMod (avx .vmovsd [vecM q, vecR dq]) (avx .vmovsd [vecM dq, vecV dq, vecR dq])))
  | 0x12 => .byPfx .nm .nm (vexL .avx .avx (avx .vmovsldup [vecR x, vecM x]))
                   (.byL (needs .avx (avx .vmovddup [vecR dq, vecM q]))
                          (needs .avx (avx .vmovddup [vecR x, vecM x])) .nm .nm)
  | 0x14 => .byPfx (vexL .avx .avx (avx .vunpcklps [vecR x, vecV x, vecM x]))
                   (vexL .avx .avx (avx .vunpcklpd [vecR x, vecV x, vecM x])) .nm .nm
  | 0x15 => .byPfx (vexL .avx .avx (avx .vunpckhps [vecR x, vecV x, vecM x]))
                   (vexL .avx .avx (avx .vunpckhpd [vecR x, vecV x, vecM x])) .nm .nm
  | 0x16 => .byPfx .nm .nm (vexL .avx .avx (avx .vmovshdup [vecR x, vecM x])) .nm
  | 0x28 => .byPfx (vexL .avx .avx (avx .vmovaps [vecR x, vecM x])) (vexL .avx .avx (avx .vmovapd [vecR x, vecM x]))
                   .nm .nm
  | 0x29 => .byPfx (vexL .avx .avx (avx .vmovaps [vecM x, vecR x])) (vexL .avx .avx (avx .vmovapd [vecM x, vecR x]))
                   .nm .nm
  | 0x2A => .byPfx .nm .nm (vexL .avx .avx (fp (.cvtsi2 .ss) [vecR dq, vecV dq, E y]))
                   (vexL .avx .avx (fp (.cvtsi2 .sd) [vecR dq, vecV dq, E y]))
  | 0x2C => .byPfx .nm .nm (vexL .avx .avx (fp (.cvtt2si .ss) [G y, vecM d]))
                   (vexL .avx .avx (fp (.cvtt2si .sd) [G y, vecM q]))
  | 0x2D => .byPfx .nm .nm (vexL .avx .avx (fp (.cvt2si .ss) [G y, vecM d]))
                   (vexL .avx .avx (fp (.cvt2si .sd) [G y, vecM q]))
  | 0x2E => .byPfx (vexL .avx .avx (fp (.ucomi .ss) [vecR dq, vecM d])) (vexL .avx .avx (fp (.ucomi .sd) [vecR dq, vecM q]))
                   .nm .nm
  | 0x2F => .byPfx (vexL .avx .avx (fp (.comi .ss) [vecR dq, vecM d])) (vexL .avx .avx (fp (.comi .sd) [vecR dq, vecM q]))
                   .nm .nm
  | 0x41 => kOp3 .kand
  | 0x42 => kOp3 .kandn
  | 0x44 =>
    let e := kOp .knot fun s => [kR, kM s]
    .byMod (.invalid e) e
  | 0x45 => kOp3 .kor
  | 0x46 => kOp3 .kxnor
  | 0x47 => kOp3 .kxor
  | 0x50 => .byPfx (.byMod .nm (vexL .avx .avx (avx .vmovmskps [G d, vecU x])))
                   (.byMod .nm (vexL .avx .avx (avx .vmovmskpd [G d, vecU x]))) .nm .nm
  -- the packed square roots take one source (`vvvv` 1111b), the scalar ones two
  | 0x51 => .byPfx (vexL .avx .avx (fp (.sqrt .ps) [vecR x, vecM x])) (vexL .avx .avx (fp (.sqrt .pd) [vecR x, vecM x]))
                   (vexL .avx .avx (fp (.sqrt .ss) [vecR dq, vecV dq, vecM d]))
                   (vexL .avx .avx (fp (.sqrt .sd) [vecR dq, vecV dq, vecM q]))
  | 0x54 => .byPfx (vexL .avx .avx (avx .vandps [vecR x, vecV x, vecM x]))
                   (vexL .avx .avx (avx .vandpd [vecR x, vecV x, vecM x])) .nm .nm
  | 0x55 => .byPfx (vexL .avx .avx (avx .vandnps [vecR x, vecV x, vecM x]))
                   (vexL .avx .avx (avx .vandnpd [vecR x, vecV x, vecM x])) .nm .nm
  | 0x56 => .byPfx (vexL .avx .avx (avx .vorps [vecR x, vecV x, vecM x]))
                   (vexL .avx .avx (avx .vorpd [vecR x, vecV x, vecM x])) .nm .nm
  | 0x57 => .byPfx (vexL .avx .avx (avx .vxorps [vecR x, vecV x, vecM x]))
                   (vexL .avx .avx (avx .vxorpd [vecR x, vecV x, vecM x])) .nm .nm
  | 0x58 => vexFp4 .add
  | 0x59 => vexFp4 .mul
  -- the widening conversions read half the destination's width (`VEX.128`: 64 bits, `VEX.256`: 128),
  -- the narrowing ones write an `XMM` register from an `XMM` or `YMM` source
  | 0x5A => .byPfx (.byL (needs .avx (fp .cvtps2pd [vecR x, vecM q])) (needs .avx (fp .cvtps2pd [vecR x, vecM dq])) .nm .nm)
                   (vexL .avx .avx (fp .cvtpd2ps [vecR dq, vecM x]))
                   (vexL .avx .avx (fp .cvtss2sd [vecR dq, vecV dq, vecM d]))
                   (vexL .avx .avx (fp .cvtsd2ss [vecR dq, vecV dq, vecM q]))
  | 0x5B => .byPfx (vexL .avx .avx (fp .cvtdq2ps [vecR x, vecM x])) (vexL .avx .avx (fp .cvtps2dq [vecR x, vecM x]))
                   (vexL .avx .avx (fp .cvttps2dq [vecR x, vecM x])) .nm
  | 0x5C => vexFp4 .sub
  | 0x5D => vexFp4 .min
  | 0x5E => vexFp4 .div
  | 0x5F => vexFp4 .max
  | 0x63 => .byPfx .nm (vex3 .vpacksswb) .nm .nm
  | 0x64 => .byPfx .nm (vex3 (.vpcmpgt 8)) .nm .nm
  | 0x65 => .byPfx .nm (vex3 (.vpcmpgt 16)) .nm .nm
  | 0x66 => .byPfx .nm (vex3 (.vpcmpgt 32)) .nm .nm
  | 0x67 => .byPfx .nm (vex3 .vpackuswb) .nm .nm
  | 0x6B => .byPfx .nm (vex3 .vpackssdw) .nm .nm
  | 0x6C => .byPfx .nm (vex3 .vpunpcklqdq) .nm .nm
  | 0x6D => .byPfx .nm (vex3 .vpunpckhqdq) .nm .nm
  | 0x6E => .byPfx .nm (l0 (needs .avx (.byW (avx .vmovd [vecR x, E y]) (avx .vmovq [vecR x, E y]))))
                   .nm .nm
  | 0x6F => .byPfx .nm (vexL .avx .avx (avx .vmovdqa [vecR x, vecM x]))
                   (vexL .avx .avx (avx .vmovdqu [vecR x, vecM x])) .nm
  | 0x71 => .byPfx .nm (.grp .nm .nm (vexShiftImm (.vpsrl 16)) .nm
                        (vexShiftImm (.vpsra 16)) .nm (vexShiftImm (.vpsll 16)) .nm) .nm .nm
  | 0x72 => .byPfx .nm (.grp .nm .nm (vexShiftImm (.vpsrl 32)) .nm
                        (vexShiftImm (.vpsra 32)) .nm (vexShiftImm (.vpsll 32)) .nm) .nm .nm
  | 0x73 => .byPfx .nm (.grp .nm .nm (vexShiftImm (.vpsrl 64)) .nm
                        .nm .nm (vexShiftImm (.vpsll 64)) .nm) .nm .nm
  | 0x74 => .byPfx .nm (vex3 (.vpcmpeq 8)) .nm .nm
  | 0x75 => .byPfx .nm (vex3 (.vpcmpeq 16)) .nm .nm
  | 0x76 => .byPfx .nm (vex3 (.vpcmpeq 32)) .nm .nm
  -- VEX.128/256.0F.WIG 77 (SDM VZEROUPPER, VZEROALL). APM Vol. 4's exception tables give `#UD` for
  -- `VEX.W = 1`, its encoding tables WIG; an AMD Zen 4 executes both with `W = 1` in hardware measurements
  | 0x77 => .byPfx (.byL (needs .avx (avx .vzeroupper [])) (needs .avx (avx .vzeroall [])) (.ud []) (.ud []))
                   .nm .nm .nm
  | 0x7C => .byPfx .nm (vexL .avx .avx (fp (.hadd .pd) [vecR x, vecV x, vecM x])) .nm
                   (vexL .avx .avx (fp (.hadd .ps) [vecR x, vecV x, vecM x]))
  | 0x7D => .byPfx .nm (vexL .avx .avx (fp (.hsub .pd) [vecR x, vecV x, vecM x])) .nm
                   (vexL .avx .avx (fp (.hsub .ps) [vecR x, vecV x, vecM x]))
  | 0x7E => .byPfx .nm (l0 (needs .avx (.byW (avx .vmovd [E y, vecR x]) (avx .vmovq [E y, vecR x]))))
                   (l0 (needs .avx (avx .vmovq [vecR x, vecM q]))) .nm
  | 0x7F => .byPfx .nm (vexL .avx .avx (avx .vmovdqa [vecM x, vecR x]))
                   (vexL .avx .avx (avx .vmovdqu [vecM x, vecR x])) .nm
  -- opmask moves (k from k or memory, memory from k, k from a general register, a general
  -- register from k) and `KORTEST`
  | 0x90 => kOp .kmov fun s => [kR, kM s]
  | 0x91 => .byMod (kOp .kmov fun s => [kM s, kR]) (.ud [])
  | 0x92 =>
    let w16 := avx (.kmov 16) [kR, E d]
    let w8 := avx (.kmov 8) [kR, E d]
    let e := l0 (.byPfx (needs .avx512f (.byW w16 (.invalid w16))) (needs .avx512dq (.byW w8 (.invalid w8)))
                  (needs .avx512f (.invalid w16))
                  (.byW (needs .avx512bw (avx (.kmov 32) [kR, E d]))
                       (needs .avx512bw (avx (.kmov 64) [kR, E q]))))
    .byMod (.invalid e) e
  | 0x93 =>
    let w16 := avx (.kmov 16) [G d, kM q]
    let w8 := avx (.kmov 8) [G d, kM q]
    let e := l0 (.byPfx (needs .avx512f (.byW w16 (.invalid w16))) (needs .avx512dq (.byW w8 (.invalid w8)))
                  (needs .avx512f (.invalid w16))
                  (.byW (needs .avx512bw (avx (.kmov 32) [G d, kM q]))
                       (needs .avx512bw (avx (.kmov 64) [G q, kM q]))))
    .byMod (.invalid e) e
  | 0x98 =>
    let e := kOp .kortest fun s => [kR, kM s]
    .byMod (.invalid e) e
  -- `KTESTW` needs AVX512DQ (SDM Vol. 2, "KTESTW/KTESTB/KTESTQ/KTESTD")
  | 0x99 =>
    let e := l0 (kWidths .ktest .avx512dq fun s => [kR, kM s])
    .byMod (.invalid e) e
  -- `VLDMXCSR`, `VSTMXCSR`: `VEX.LZ`, memory only
  | 0xAE => .byMod (.byPfx (.grp .nm .nm (l0 (needs .avx (fp .ldmxcsr [E d]))) (l0 (needs .avx (fp .stmxcsr [E d])))
                              .nm .nm .nm .nm) .nm .nm .nm) .nm
  | 0xC2 => .byPfx (vexL .avx .avx (fp (.cmp .ps) [vecR x, vecV x, vecM x, I b]))
                   (vexL .avx .avx (fp (.cmp .pd) [vecR x, vecV x, vecM x, I b]))
                   (vexL .avx .avx (fp (.cmp .ss) [vecR dq, vecV dq, vecM d, I b]))
                   (vexL .avx .avx (fp (.cmp .sd) [vecR dq, vecV dq, vecM q, I b]))
  | 0xC6 => .byPfx (vexL .avx .avx (avx .vshufps [vecR x, vecV x, vecM x, I b]))
                   (vexL .avx .avx (avx .vshufpd [vecR x, vecV x, vecM x, I b])) .nm .nm
  | 0xD0 => .byPfx .nm (vexL .avx .avx (fp (.addsub .pd) [vecR x, vecV x, vecM x])) .nm
                   (vexL .avx .avx (fp (.addsub .ps) [vecR x, vecV x, vecM x]))
  | 0xD1 => .byPfx .nm (vexShiftCount (.vpsrl 16)) .nm .nm
  | 0xD2 => .byPfx .nm (vexShiftCount (.vpsrl 32)) .nm .nm
  | 0xD3 => .byPfx .nm (vexShiftCount (.vpsrl 64)) .nm .nm
  | 0xD4 => .byPfx .nm (vex3 (.vpadd 64)) .nm .nm
  | 0xD6 => .byPfx .nm (l0 (needs .avx (avx .vmovq [vecM q, vecR x]))) .nm .nm
  | 0xD7 => .byPfx .nm (vexL .avx .avx2 (avx .vpmovmskb [G d, vecU x])) .nm .nm
  | 0xD8 => .byPfx .nm (vex3 (.vpsubus 8)) .nm .nm
  | 0xD9 => .byPfx .nm (vex3 (.vpsubus 16)) .nm .nm
  | 0xDA => .byPfx .nm (vex3 (.vpminu 8)) .nm .nm
  | 0xDB => .byPfx .nm (vex3 .vpand) .nm .nm
  | 0xDC => .byPfx .nm (vex3 (.vpaddus 8)) .nm .nm
  | 0xDD => .byPfx .nm (vex3 (.vpaddus 16)) .nm .nm
  | 0xDE => .byPfx .nm (vex3 (.vpmaxu 8)) .nm .nm
  | 0xDF => .byPfx .nm (vex3 .vpandn) .nm .nm
  | 0xE1 => .byPfx .nm (vexShiftCount (.vpsra 16)) .nm .nm
  | 0xE2 => .byPfx .nm (vexShiftCount (.vpsra 32)) .nm .nm
  | 0xE6 => .byPfx .nm (vexL .avx .avx (fp .cvttpd2dq [vecR dq, vecM x]))
                   (.byL (needs .avx (fp .cvtdq2pd [vecR x, vecM q])) (needs .avx (fp .cvtdq2pd [vecR x, vecM dq])) .nm .nm)
                   (vexL .avx .avx (fp .cvtpd2dq [vecR dq, vecM x]))
  | 0xE7 => .byPfx .nm (.byMod (vexL .avx .avx (avx .vmovntdq [vecM x, vecR x])) (.ud [])) .nm .nm
  | 0xE8 => .byPfx .nm (vex3 (.vpsubs 8)) .nm .nm
  | 0xE9 => .byPfx .nm (vex3 (.vpsubs 16)) .nm .nm
  | 0xEA => .byPfx .nm (vex3 (.vpmins 16)) .nm .nm
  | 0xEB => .byPfx .nm (vex3 .vpor) .nm .nm
  | 0xEC => .byPfx .nm (vex3 (.vpadds 8)) .nm .nm
  | 0xED => .byPfx .nm (vex3 (.vpadds 16)) .nm .nm
  | 0xEE => .byPfx .nm (vex3 (.vpmaxs 16)) .nm .nm
  | 0xEF => .byPfx .nm (vex3 .vpxor) .nm .nm
  | 0xF1 => .byPfx .nm (vexShiftCount (.vpsll 16)) .nm .nm
  | 0xF2 => .byPfx .nm (vexShiftCount (.vpsll 32)) .nm .nm
  | 0xF3 => .byPfx .nm (vexShiftCount (.vpsll 64)) .nm .nm
  | 0xF4 => .byPfx .nm (vex3 .vpmuludq) .nm .nm
  | 0xF8 => .byPfx .nm (vex3 (.vpsub 8)) .nm .nm
  | 0xF9 => .byPfx .nm (vex3 (.vpsub 16)) .nm .nm
  | 0xFA => .byPfx .nm (vex3 (.vpsub 32)) .nm .nm
  | 0xFB => .byPfx .nm (vex3 (.vpsub 64)) .nm .nm
  | 0xFC => .byPfx .nm (vex3 (.vpadd 8)) .nm .nm
  | 0xFD => .byPfx .nm (vex3 (.vpadd 16)) .nm .nm
  | 0xFE => .byPfx .nm (vex3 (.vpadd 32)) .nm .nm
  | 0xD5 => .byPfx .nm (vex3 .vpmullw) .nm .nm
  | 0xE4 => .byPfx .nm (vex3 .vpmulhuw) .nm .nm
  | 0xE5 => .byPfx .nm (vex3 .vpmulhw) .nm .nm
  | 0xF5 => .byPfx .nm (vex3 .vpmaddwd) .nm .nm
  | 0xE0 => .byPfx .nm (vex3 .vpavgb) .nm .nm
  | 0xE3 => .byPfx .nm (vex3 .vpavgw) .nm .nm
  | 0xF6 => .byPfx .nm (vex3 .vpsadbw) .nm .nm
  | _ => .nm

/-- A VEX broadcast of a `s`-sized element from memory or a vector register (`VEX.W0`): the
memory form with feature `fm`, the register form with AVX2 (SDM Vol. 2, "VBROADCAST",
"VPBROADCAST"). -/
def vexBcst (m : AvxMn) (s : Sz) (fm : Feat) : Entry :=
  let e := .byMod (vexL fm fm (avx m [vecR x, vecM s])) (vexL .avx2 .avx2 (avx m [vecR x, vecM s]))
  .byPfx .nm (.byW e (.invalid e)) .nm .nm

/-- FMA VEX encodings by `W` (single/double) and opcode (packed/scalar), with
AVX usable and CPUID.FMA. SDM Vol. 2C, "VFMADD132PD", ...; APM Vol. 4, the same pages.
Scalar `L` is ignored; packed lengths are 128 and 256 bits. -/
def vexFma (order : FmaOrder) (np sa scalar : Bool) : Entry :=
  let one (t : FpTy) (sz : Sz) := needs .fma (vexL .avx .avx
    (fp (.fma t order np sa) [vecR (if scalar then dq else x),
      vecV (if scalar then dq else x), vecM sz]))
  .byPfx .nm (.byW (one (if scalar then .ss else .ps) (if scalar then d else x))
                        (one (if scalar then .sd else .pd) (if scalar then q else x))) .nm .nm

/-- The VEX map `0F 38` (`VEX.mmmmm = 2`): vector instructions, and BMI1 and BMI2 on general
registers (`VEX.LZ`). -/
def vex0F38 : Nat → Entry
  | 0x00 => .byPfx .nm (vexL .avx .avx2 (avx .vpshufb [vecR x, vecV x, vecM x])) .nm .nm
  | 0x18 => vexBcst .vbroadcastss d .avx
  | 0x29 => .byPfx .nm (vex3 (.vpcmpeq 64)) .nm .nm
  | 0x2B => .byPfx .nm (vex3 .vpackusdw) .nm .nm
  | 0x37 => .byPfx .nm (vex3 (.vpcmpgt 64)) .nm .nm
  | 0x38 => .byPfx .nm (vex3 (.vpmins 8)) .nm .nm
  | 0x39 => .byPfx .nm (vex3 (.vpmins 32)) .nm .nm
  | 0x3A => .byPfx .nm (vex3 (.vpminu 16)) .nm .nm
  | 0x3B => .byPfx .nm (vex3 (.vpminu 32)) .nm .nm
  | 0x3C => .byPfx .nm (vex3 (.vpmaxs 8)) .nm .nm
  | 0x3D => .byPfx .nm (vex3 (.vpmaxs 32)) .nm .nm
  | 0x3E => .byPfx .nm (vex3 (.vpmaxu 16)) .nm .nm
  | 0x3F => .byPfx .nm (vex3 (.vpmaxu 32)) .nm .nm
  | 0x58 => vexBcst (.vpbroadcast 32) d .avx2
  | 0x59 => vexBcst (.vpbroadcast 64) q .avx2
  | 0x78 => vexBcst (.vpbroadcast 8) b .avx2
  | 0x79 => vexBcst (.vpbroadcast 16) w .avx2
  | 0x98 => vexFma .o132 false false false
  | 0x99 => vexFma .o132 false false true
  | 0x9A => vexFma .o132 false true false
  | 0x9B => vexFma .o132 false true true
  | 0x9C => vexFma .o132 true false false
  | 0x9D => vexFma .o132 true false true
  | 0x9E => vexFma .o132 true true false
  | 0x9F => vexFma .o132 true true true
  | 0xA8 => vexFma .o213 false false false
  | 0xA9 => vexFma .o213 false false true
  | 0xAA => vexFma .o213 false true false
  | 0xAB => vexFma .o213 false true true
  | 0xAC => vexFma .o213 true false false
  | 0xAD => vexFma .o213 true false true
  | 0xAE => vexFma .o213 true true false
  | 0xAF => vexFma .o213 true true true
  | 0xB8 => vexFma .o231 false false false
  | 0xB9 => vexFma .o231 false false true
  | 0xBA => vexFma .o231 false true false
  | 0xBB => vexFma .o231 false true true
  | 0xBC => vexFma .o231 true false false
  | 0xBD => vexFma .o231 true false true
  | 0xBE => vexFma .o231 true true false
  | 0xBF => vexFma .o231 true true true
  | 0xF2 => .byPfx (l0 (needs .bmi1 (bit .andn [G y, gprV y, E y]))) .nm .nm .nm
  -- Group 17 (Table A-6)
  | 0xF3 => .byPfx (l0 (.grp .nm (needs .bmi1 (bit .blsr [gprV y, E y]))
                           (needs .bmi1 (bit .blsmsk [gprV y, E y]))
                           (needs .bmi1 (bit .blsi [gprV y, E y])) .nm .nm .nm .nm)) .nm .nm .nm
  | 0xF5 => .byPfx (l0 (needs .bmi2 (bit .bzhi [G y, E y, gprV y]))) .nm
                   (l0 (needs .bmi2 (bit .pext [G y, gprV y, E y])))
                   (l0 (needs .bmi2 (bit .pdep [G y, gprV y, E y])))
  | 0xF6 => .byPfx .nm .nm .nm (l0 (needs .bmi2 (bit .mulx [G y, gprV y, E y])))
  | 0xF7 => .byPfx (l0 (needs .bmi1 (bit .bextr [G y, E y, gprV y])))
                   (l0 (needs .bmi2 (bit .shlx [G y, E y, gprV y])))
                   (l0 (needs .bmi2 (bit .sarx [G y, E y, gprV y])))
                   (l0 (needs .bmi2 (bit .shrx [G y, E y, gprV y])))
  | 0x04 => .byPfx .nm (vex3 .vpmaddubsw) .nm .nm
  | 0x0B => .byPfx .nm (vex3 .vpmulhrsw) .nm .nm
  | 0x28 => .byPfx .nm (vex3 .vpmuldq) .nm .nm
  | _ => .nm

/-- The VEX map `0F 3A` (`VEX.mmmmm = 3`). -/
def vex0F3A : Nat → Entry
  | 0x08 => .byPfx .nm (vexL .avx .avx (fp (.round .ps) [vecR x, vecM x, I b])) .nm .nm
  | 0x09 => .byPfx .nm (vexL .avx .avx (fp (.round .pd) [vecR x, vecM x, I b])) .nm .nm
  | 0x0A => .byPfx .nm (vexL .avx .avx (fp (.round .ss) [vecR dq, vecV dq, vecM d, I b])) .nm .nm
  | 0x0B => .byPfx .nm (vexL .avx .avx (fp (.round .sd) [vecR dq, vecV dq, vecM q, I b])) .nm .nm
  -- `W1` is ignored for the byte forms in 64-bit mode (SDM PINSRB/PEXTRB, footnote 1).
  | 0x14 => .byPfx .nm (l0 (needs .avx (avx (.vpextr 8) [ER d b, vecR dq, I b]))) .nm .nm
  | 0x16 => .byPfx .nm (l0 (needs .avx (.byW (avx (.vpextr 32) [E d, vecR dq, I b])
                                           (avx (.vpextr 64) [E q, vecR dq, I b])))) .nm .nm
  | 0x18 => .byPfx .nm (vexHalf .avx .vinsertf128 [vecR x, vecV x, vecM dq, I b]) .nm .nm
  | 0x19 => .byPfx .nm (vexHalf .avx .vextractf128 [vecM dq, vecR x, I b]) .nm .nm
  | 0x20 => .byPfx .nm (l0 (needs .avx (avx (.vpinsr 8) [vecR dq, vecV dq, ER d b, I b]))) .nm .nm
  | 0x22 => .byPfx .nm (l0 (needs .avx (.byW (avx (.vpinsr 32) [vecR dq, vecV dq, E d, I b])
                                           (avx (.vpinsr 64) [vecR dq, vecV dq, E q, I b])))) .nm .nm
  | 0x38 => .byPfx .nm (vexHalf .avx2 .vinserti128 [vecR x, vecV x, vecM dq, I b]) .nm .nm
  | 0x39 => .byPfx .nm (vexHalf .avx2 .vextracti128 [vecM dq, vecR x, I b]) .nm .nm
  | 0xF0 => .byPfx .nm .nm .nm (l0 (needs .bmi2 (bit .rorx [G y, E y, I b])))
  | _ => .nm

/-! ## EVEX maps -/

/-- EVEX masking: merging and zeroing. -/
def mz : Attr := { masking := .full }
/-- EVEX masking: merging only. -/
def mm : Attr := { masking := .merge }

/-- EVEX without masking, with an 8-bit displacement scaled by 4 or 8 ("Tuple1 Scalar"). -/
def s4 : Attr := { disp8 := .scalar 4 }
/-- See `s4`. -/
def s8 : Attr := { disp8 := .scalar 8 }

/-- EVEX masking with merging and zeroing, and broadcast of `e`-bit elements. -/
def mzb (e : Nat) : Attr := { masking := .full, bcst := some e }
/-- EVEX masking with merging only (an opmask destination), and broadcast of `e`-bit elements. -/
def mmb (e : Nat) : Attr := { masking := .merge, bcst := some e }

/-- An EVEX instruction `m e` on bytes and words, by opcode (`EVEX.WIG`), with AVX512BW. -/
def evexBW (m : AvxMn) (ops : List OS := [vecR x, vecV x, vecM x]) (a : Attr := mz) : Entry :=
  evexL [.avx512bw] (avx m ops a)

/-- An EVEX instruction `m 32` (`W0`) and `m 64` (`W1`) on doublewords and quadwords, with
broadcast, merging and zeroing (or, `kd`, an opmask destination, merging only). -/
def evexDQ (m : Nat → AvxMn) (ops : List OS := [vecR x, vecV x, vecM x]) (kd : Bool := false) :
    Entry :=
  .byW (evexL [] (avx (m 32) ops (if kd then mmb 32 else mzb 32)))
       (evexL [] (avx (m 64) ops (if kd then mmb 64 else mzb 64)))

/-- An EVEX instruction on doublewords only (`W0`; `W1` is invalid for every cell that uses this:
`#UD`, by the SDM's Opcode column, Intel XED and measurements on an AMD Zen 4). -/
def evexD (m : AvxMn) (ops : List OS := [vecR x, vecV x, vecM x]) (kd : Bool := false) : Entry :=
  let e := evexL [] (avx m ops (if kd then mmb 32 else mzb 32))
  .byW e (.invalid e)

/-- An EVEX instruction on quadwords only (`W1`; `W0` invalid, as for `evexD`). -/
def evexQ (m : AvxMn) (ops : List OS := [vecR x, vecV x, vecM x]) (kd : Bool := false) : Entry :=
  let e := evexL [] (avx m ops (if kd then mmb 64 else mzb 64))
  .byW (.invalid e) e

/-- The operands of an EVEX comparison into an opmask. -/
def toK : List OS := [kR, vecV x, vecM x]

/-- An EVEX instruction defined for `EVEX.L'L = 0` only, with AVX512F (the `EVEX.128` forms of
`VMOVD`/`VMOVQ`); `#UD` at the other lengths. -/
def evex128 (e : Entry) : Entry :=
  needs .avx512f (.byL e (.invalid e) (.invalid e) (.invalid e))

/-- An EVEX move `m` of doublewords without a mandatory prefix (`W0`; `W1` invalid, as for `evexD`),
load (`ld`) or store, with features `fs`: a store to memory merges only, a register destination
may also zero. -/
def evexMov (m : AvxMn) (ld : Bool) (fs : List Feat := []) : Entry :=
  let e := if ld then evexL fs (avx m [vecR x, vecM x] mz)
    else .byMod (evexL fs (avx m [vecM x, vecR x] mm)) (evexL fs (avx m [vecM x, vecR x] mz))
  .byW e (.invalid e)

/-- The EVEX map `0F` (`EVEX.mmm = 1`). -/
def evex0F : Nat → Entry
  | 0x10 => .byPfx (evexMov .vmovups true) .nm .nm .nm
  | 0x11 => .byPfx (evexMov .vmovups false) .nm .nm .nm
  | 0x28 => .byPfx (evexMov .vmovaps true) .nm .nm .nm
  | 0x29 => .byPfx (evexMov .vmovaps false) .nm .nm .nm
  | 0x63 => .byPfx .nm (evexBW .vpacksswb) .nm .nm
  | 0x64 => .byPfx .nm (evexBW (.vpcmpgt 8) toK mm) .nm .nm
  | 0x65 => .byPfx .nm (evexBW (.vpcmpgt 16) toK mm) .nm .nm
  | 0x66 => .byPfx .nm (evexD (.vpcmpgt 32) toK true) .nm .nm
  | 0x67 => .byPfx .nm (evexBW .vpackuswb) .nm .nm
  | 0x6B => .byPfx .nm (needs .avx512bw (evexD .vpackssdw)) .nm .nm
  | 0x6E => .byPfx .nm (evex128 (.byW (avx .vmovd [vecR x, E y] s4) (avx .vmovq [vecR x, E y] s8))) .nm .nm
  | 0x6F => .byPfx .nm
      (.byW (evexL [] (avx .vmovdqa32 [vecR x, vecM x] mz)) (evexL [] (avx .vmovdqa64 [vecR x, vecM x] mz)))
      (.byW (evexL [] (avx .vmovdqu32 [vecR x, vecM x] mz)) (evexL [] (avx .vmovdqu64 [vecR x, vecM x] mz)))
      (.byW (evexL [.avx512bw] (avx .vmovdqu8 [vecR x, vecM x] mz))
           (evexL [.avx512bw] (avx .vmovdqu16 [vecR x, vecM x] mz)))
  | 0x74 => .byPfx .nm (evexBW (.vpcmpeq 8) toK mm) .nm .nm
  | 0x75 => .byPfx .nm (evexBW (.vpcmpeq 16) toK mm) .nm .nm
  | 0x76 => .byPfx .nm (evexD (.vpcmpeq 32) toK true) .nm .nm
  | 0x7E => .byPfx .nm (evex128 (.byW (avx .vmovd [E y, vecR x] s4) (avx .vmovq [E y, vecR x] s8)))
                   (evex128 (.byW (.invalid (avx .vmovq [vecR x, vecM q] s8)) (avx .vmovq [vecR x, vecM q] s8))) .nm
  -- a store to memory merges only; a register destination may also zero
  | 0x7F =>
    let st (m : AvxMn) (fs : List Feat) : Entry :=
      .byMod (evexL fs (avx m [vecM x, vecR x] mm)) (evexL fs (avx m [vecM x, vecR x] mz))
    .byPfx .nm (.byW (st .vmovdqa32 []) (st .vmovdqa64 [])) (.byW (st .vmovdqu32 []) (st .vmovdqu64 []))
      (.byW (st .vmovdqu8 [.avx512bw]) (st .vmovdqu16 [.avx512bw]))
  | 0xD4 => .byPfx .nm (evexQ (.vpadd 64)) .nm .nm
  | 0xD6 => .byPfx .nm (evex128 (.byW (.invalid (avx .vmovq [vecM q, vecR x] s8)) (avx .vmovq [vecM q, vecR x] s8))) .nm .nm
  | 0xD8 => .byPfx .nm (evexBW (.vpsubus 8)) .nm .nm
  | 0xD9 => .byPfx .nm (evexBW (.vpsubus 16)) .nm .nm
  | 0xDA => .byPfx .nm (evexBW (.vpminu 8)) .nm .nm
  | 0xDB => .byPfx .nm (.byW (evexL [] (avx .vpandd [vecR x, vecV x, vecM x] (mzb 32)))
                            (evexL [] (avx .vpandq [vecR x, vecV x, vecM x] (mzb 64)))) .nm .nm
  | 0xDC => .byPfx .nm (evexBW (.vpaddus 8)) .nm .nm
  | 0xDD => .byPfx .nm (evexBW (.vpaddus 16)) .nm .nm
  | 0xDE => .byPfx .nm (evexBW (.vpmaxu 8)) .nm .nm
  | 0xDF => .byPfx .nm (.byW (evexL [] (avx .vpandnd [vecR x, vecV x, vecM x] (mzb 32)))
                            (evexL [] (avx .vpandnq [vecR x, vecV x, vecM x] (mzb 64)))) .nm .nm
  -- a store without an opmask (SDM Vol. 2, "MOVNTDQ": "EVEX.512.66.0F.W0 E7 /r")
  | 0xE7 =>
    let e := .byMod (evexL [] (avx .vmovntdq [vecM x, vecR x])) (.ud [])
    .byPfx .nm (.byW e (.invalid e)) .nm .nm
  | 0xE8 => .byPfx .nm (evexBW (.vpsubs 8)) .nm .nm
  | 0xE9 => .byPfx .nm (evexBW (.vpsubs 16)) .nm .nm
  | 0xEA => .byPfx .nm (evexBW (.vpmins 16)) .nm .nm
  | 0xEB => .byPfx .nm (.byW (evexL [] (avx .vpord [vecR x, vecV x, vecM x] (mzb 32)))
                            (evexL [] (avx .vporq [vecR x, vecV x, vecM x] (mzb 64)))) .nm .nm
  | 0xEC => .byPfx .nm (evexBW (.vpadds 8)) .nm .nm
  | 0xED => .byPfx .nm (evexBW (.vpadds 16)) .nm .nm
  | 0xEE => .byPfx .nm (evexBW (.vpmaxs 16)) .nm .nm
  | 0xEF => .byPfx .nm (.byW (evexL [] (avx .vpxord [vecR x, vecV x, vecM x] (mzb 32)))
                            (evexL [] (avx .vpxorq [vecR x, vecV x, vecM x] (mzb 64)))) .nm .nm
  | 0xF8 => .byPfx .nm (evexBW (.vpsub 8)) .nm .nm
  | 0xF9 => .byPfx .nm (evexBW (.vpsub 16)) .nm .nm
  | 0xFA => .byPfx .nm (evexD (.vpsub 32)) .nm .nm
  | 0xFB => .byPfx .nm (evexQ (.vpsub 64)) .nm .nm
  | 0xFC => .byPfx .nm (evexBW (.vpadd 8)) .nm .nm
  | 0xFD => .byPfx .nm (evexBW (.vpadd 16)) .nm .nm
  | 0xFE => .byPfx .nm (evexD (.vpadd 32)) .nm .nm
  | 0xD5 => .byPfx .nm (evexBW .vpmullw) .nm .nm
  | 0xE4 => .byPfx .nm (evexBW .vpmulhuw) .nm .nm
  | 0xE5 => .byPfx .nm (evexBW .vpmulhw) .nm .nm
  | 0xF5 => .byPfx .nm (evexBW .vpmaddwd) .nm .nm
  | 0xF4 => .byPfx .nm (evexQ .vpmuludq) .nm .nm
  | 0xE0 => .byPfx .nm (evexBW .vpavgb) .nm .nm
  | 0xE3 => .byPfx .nm (evexBW .vpavgw) .nm .nm
  | 0xF6 => .byPfx .nm (evexBW .vpsadbw [vecR x, vecV x, vecM x] {}) .nm .nm
  | _ => .nm

/-- An EVEX broadcast `m` of an element of size `s` (`n` bytes: "Tuple1 Scalar") from memory or
a vector register, with features `fs`. -/
def evexBcst (m : AvxMn) (s : Sz) (n : Nat) (fs : List Feat) : Entry :=
  evexL fs (avx m [vecR x, vecM s] { masking := .full, disp8 := .scalar n })

/-- The EVEX map `0F 38` (`EVEX.mmm = 2`). -/
def evex0F38 : Nat → Entry
  | 0x00 => .byPfx .nm (evexBW .vpshufb) .nm .nm
  | 0x18 => .byPfx .nm (.byW (evexBcst .vbroadcastss d 4 []) (.invalid (evexBcst .vbroadcastss d 4 []))) .nm .nm
  -- `VPTESTM*` with `66`, `VPTESTNM*` with `F3`
  | 0x26 => .byPfx .nm (.byW (evexBW (.vptestm 8) toK mm) (evexBW (.vptestm 16) toK mm))
                   (.byW (evexBW (.vptestnm 8) toK mm) (evexBW (.vptestnm 16) toK mm)) .nm
  | 0x27 => .byPfx .nm (evexDQ .vptestm toK true) (evexDQ .vptestnm toK true) .nm
  | 0x29 => .byPfx .nm (evexQ (.vpcmpeq 64) toK true) .nm .nm
  | 0x2B => .byPfx .nm (needs .avx512bw (evexD .vpackusdw)) .nm .nm
  | 0x37 => .byPfx .nm (evexQ (.vpcmpgt 64) toK true) .nm .nm
  | 0x38 => .byPfx .nm (evexBW (.vpmins 8)) .nm .nm
  | 0x39 => .byPfx .nm (evexDQ .vpmins) .nm .nm
  | 0x3A => .byPfx .nm (evexBW (.vpminu 16)) .nm .nm
  | 0x3B => .byPfx .nm (evexDQ .vpminu) .nm .nm
  | 0x3C => .byPfx .nm (evexBW (.vpmaxs 8)) .nm .nm
  | 0x3D => .byPfx .nm (evexDQ .vpmaxs) .nm .nm
  | 0x3E => .byPfx .nm (evexBW (.vpmaxu 16)) .nm .nm
  | 0x3F => .byPfx .nm (evexDQ .vpmaxu) .nm .nm
  | 0x58 =>
    let e := evexBcst (.vpbroadcast 32) d 4 []
    .byPfx .nm (.byW e (.invalid e)) .nm .nm
  -- `W0` is `VBROADCASTI32X2`
  | 0x59 => .byPfx .nm (.byW .nm (evexBcst (.vpbroadcast 64) q 8 [])) .nm .nm
  | 0x78 =>
    let e := evexBcst (.vpbroadcast 8) b 1 [.avx512bw]
    .byPfx .nm (.byW e (.invalid e)) .nm .nm
  | 0x79 =>
    let e := evexBcst (.vpbroadcast 16) w 2 [.avx512bw]
    .byPfx .nm (.byW e (.invalid e)) .nm .nm
  -- from a general register (`mod = 3`); `W1` is invalid for the byte and word forms
  | 0x7A =>
    let e := evexL [.avx512bw] (avx (.vpbroadcast 8) [vecR x, E d] mz)
    .byPfx .nm (.byW (.byMod (.invalid e) e) (.invalid e)) .nm .nm
  | 0x7B =>
    let e := evexL [.avx512bw] (avx (.vpbroadcast 16) [vecR x, E d] mz)
    .byPfx .nm (.byW (.byMod (.invalid e) e) (.invalid e)) .nm .nm
  | 0x7C =>
    let dw := evexL [] (avx (.vpbroadcast 32) [vecR x, E d] mz)
    let qw := evexL [] (avx (.vpbroadcast 64) [vecR x, E q] mz)
    .byPfx .nm (.byW (.byMod (.invalid dw) dw) (.byMod (.invalid qw) qw)) .nm .nm
  | 0x04 => .byPfx .nm (evexBW .vpmaddubsw) .nm .nm
  | 0x0B => .byPfx .nm (evexBW .vpmulhrsw) .nm .nm
  | 0x28 => .byPfx .nm (evexQ .vpmuldq) .nm .nm
  | _ => .nm

/-- The EVEX map `0F 3A` (`EVEX.mmm = 3`). -/
def evex0F3A : Nat → Entry
  | 0x1E => .byPfx .nm (.byW (evexL [] (avx (.vpcmp 32 true) [kR, vecV x, vecM x, I b] (mmb 32)))
                            (evexL [] (avx (.vpcmp 64 true) [kR, vecV x, vecM x, I b] (mmb 64)))) .nm .nm
  | 0x1F => .byPfx .nm (.byW (evexL [] (avx (.vpcmp 32 false) [kR, vecV x, vecM x, I b] (mmb 32)))
                            (evexL [] (avx (.vpcmp 64 false) [kR, vecV x, vecM x, I b] (mmb 64)))) .nm .nm
  | 0x25 => .byPfx .nm (evexDQ .vpternlog [vecR x, vecV x, vecM x, I b]) .nm .nm
  | 0x3E => .byPfx .nm (.byW (evexBW (.vpcmp 8 true) [kR, vecV x, vecM x, I b] mm)
                            (evexBW (.vpcmp 16 true) [kR, vecV x, vecM x, I b] mm)) .nm .nm
  | 0x3F => .byPfx .nm (.byW (evexBW (.vpcmp 8 false) [kR, vecV x, vecM x, I b] mm)
                            (evexBW (.vpcmp 16 false) [kR, vecV x, vecM x, I b] mm)) .nm .nm
  | _ => .nm

end ZellicX86.Decode
