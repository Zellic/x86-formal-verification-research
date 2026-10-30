import ZellicX86.Spec.Decode.Maps
/-!
# Decoder: decoding

From the bytes at an instruction address to a `Decoded` result, in 64-bit mode
(SDM Vol. 2 chapter 2 "Instruction Format"; 2.2.1 REX; 2.3 VEX; 2.7 EVEX). The bytes are read
one at a time through `fetch`, so a fault is reported at the first byte the instruction
actually needs.
-/
namespace ZellicX86.Decode

/-- Why decoding stopped without an instruction (see `Decoded`). -/
inductive Stop | ud | gp | pf (off : Nat) | nm (map op : Nat)

/-- A decoding step: reads bytes through `fetch`, starting at offset `i` from the
instruction's first byte; returns a value and the new offset. -/
def D (α : Type) : Type := (Nat → Option Byte) → Nat → Except Stop (α × Nat)

/-- Sequencing of decoding steps. -/
instance : Monad D where
  pure a := fun _ i => .ok (a, i)
  bind x f := fun fetch i =>
    match x fetch i with
    | .ok (a, j) => f a fetch j
    | .error e => .error e

/-- Stop decoding with `s`. -/
def stop {α : Type} (s : Stop) : D α := fun _ _ => .error s

/-- The number of bytes read so far. -/
def pos : D Nat := fun _ i => .ok (i, i)

/-- The next instruction byte. An instruction longer than 15 bytes raises `#GP(0)`
(SDM Vol. 2 2.3.11); a byte that cannot be fetched raises `#PF`. -/
def next : D Nat := fun fetch i =>
  if i < 15 then
    match fetch i with
    | some b => .ok (b.toNat, i + 1)
    | none => .error (.pf i)
  else .error .gp

/-- `n` bytes, little-endian. -/
def readLE : Nat → D Nat
  | 0 => pure 0
  | n + 1 => do
    let lo ← next
    let hi ← readLE n
    pure (lo + 256 * hi)

/-- Sign-extend the `bits`-bit value `v` to `w` bits (two's complement). -/
def sext (bits w v : Nat) : Nat :=
  if v < 2 ^ (bits - 1) then v else v + 2 ^ w - 2 ^ bits

/-- The fields of a VEX (`C4`, `C5`) or EVEX (`62`) prefix besides those that stand for legacy
prefixes (`pp`, `R`, `X`, `B`, `W`, kept in `Pfx` as the prefixes they replace), with the
register fields un-inverted (SDM Vol. 2, 2.3.5, Figure 2-9; 2.7.1, Figure 2-11, Table 2-32). -/
structure VexPfx where
  /-- An EVEX prefix. -/
  evex : Bool
  /-- `VEX.L` (0 or 1) or `EVEX.L'L` (0 to 3). -/
  l : Nat
  /-- The register `vvvv` names: `VEX.vvvv`, or `EVEX.V':EVEX.vvvv` (0–31). -/
  vvvv : Nat
  /-- `EVEX.R'`, as the value (16) added to ModRM reg for a vector register. -/
  rhi : Nat
  /-- `EVEX.X`, as the value (16) added to ModRM r/m for a vector register. -/
  xhi : Nat
  /-- `EVEX.aaa`: the opmask register. -/
  aaa : Nat
  /-- `EVEX.z`: zeroing-masking. -/
  z : Bool
  /-- `EVEX.b`: broadcast, rounding control or "suppress all exceptions". -/
  b : Bool

/-- The prefixes seen before the opcode. -/
structure Pfx where
  /-- `66`: operand-size override (or a mandatory prefix). -/
  osz : Bool := false
  /-- `67`: address-size override. -/
  asz : Bool := false
  lock : Bool := false
  /-- The last of `F2`/`F3`, or 0. -/
  rep : Nat := 0
  seg : Option Seg := none
  /-- The REX byte (`40`–`4F`), or 0. A REX prefix counts only if it immediately precedes
  the opcode (SDM Vol. 2 2.2.1). After a VEX or EVEX prefix, the REX byte its `W`, `R`, `X`,
  `B` stand for. -/
  rex : Nat := 0
  /-- A VEX or EVEX prefix. -/
  vex : Option VexPfx := none

/-- `REX.W` (SDM Vol. 2, 2.2.1, Table 2-4): 64-bit operand size. -/
def Pfx.w (p : Pfx) : Bool := p.rex ≥ 0x48
/-- `REX.R`, as the value added to the ModRM `reg` field. -/
def Pfx.r (p : Pfx) : Nat := if (p.rex / 4) % 2 = 1 then 8 else 0
/-- `REX.X`, as the value added to the SIB `index` field. -/
def Pfx.x (p : Pfx) : Nat := if (p.rex / 2) % 2 = 1 then 8 else 0
/-- `REX.B`, as the value added to ModRM `r/m`, SIB `base` or the opcode register. -/
def Pfx.b (p : Pfx) : Nat := if p.rex % 2 = 1 then 8 else 0
/-- The vector length of a VEX or EVEX instruction in bits: 128, 256 or 512 for `L` = 0, 1, 2
(SDM Vol. 2, 2.3.6.2, 2.7.10, Table 2-38). -/
def Pfx.vl (p : Pfx) : Nat := match p.vex with
  | some v => 128 * 2 ^ v.l
  | none => 128
/-- `EVEX.R'` (16 or 0). -/
def Pfx.rhi (p : Pfx) : Nat := match p.vex with | some v => v.rhi | none => 0
/-- `EVEX.X` for a vector register in ModRM r/m (16 or 0). -/
def Pfx.xhi (p : Pfx) : Nat := match p.vex with | some v => v.xhi | none => 0
/-- The register `vvvv` names (0 without a VEX or EVEX prefix). -/
def Pfx.vvvv (p : Pfx) : Nat := match p.vex with | some v => v.vvvv | none => 0

/-- Read prefixes; return them with the first byte that is not a prefix. `fuel` only
bounds the recursion: `next` stops at 15 bytes. -/
def prefixes : Nat → Pfx → D (Pfx × Nat)
  | 0, _ => stop .gp
  | fuel + 1, p => do
    let b ← next
    match b with
    | 0x66 => prefixes fuel { p with osz := true, rex := 0 }
    | 0x67 => prefixes fuel { p with asz := true, rex := 0 }
    | 0xF0 => prefixes fuel { p with lock := true, rex := 0 }
    | 0xF2 => prefixes fuel { p with rep := 0xF2, rex := 0 }
    | 0xF3 => prefixes fuel { p with rep := 0xF3, rex := 0 }
    -- ES, CS, SS, DS overrides are ignored in 64-bit mode (SDM Vol. 1 3.3.7.1)
    | 0x26 => prefixes fuel { p with rex := 0 }
    | 0x2E => prefixes fuel { p with rex := 0 }
    | 0x36 => prefixes fuel { p with rex := 0 }
    | 0x3E => prefixes fuel { p with rex := 0 }
    | 0x64 => prefixes fuel { p with seg := some .fs, rex := 0 }
    | 0x65 => prefixes fuel { p with seg := some .gs, rex := 0 }
    | _ => if 0x40 ≤ b ∧ b < 0x50 then prefixes fuel { p with rex := b } else pure (p, b)

/-- Result of choosing the cell of an opcode map. -/
inductive Sel
  | done (mn : Mn) (ops : List OS) (a : Attr)
  /-- The choice depends on the ModRM byte, which has not been read yet. -/
  | needModRM
  /-- An invalid encoding with the bytes of the operands `ops` (`Entry.ud`, `Entry.invalid`), or,
  not `settled`, of a form whose feature is missing (`Entry.missing`). -/
  | invalid (ops : List OS) (a : Attr) (settled : Bool)
  | nm

/-- Choose within a cell by prefixes, REX, features and (once read) the ModRM byte. -/
def select (feat : Features) (p : Pfx) (m : Option Nat) : Entry → Sel
  | .op mn ops a => .done mn ops a
  | .grp r0 r1 r2 r3 r4 r5 r6 r7 =>
    match m with
    | none => .needModRM
    | some m =>
      match (m / 8) % 8 with
      | 0 => select feat p (some m) r0
      | 1 => select feat p (some m) r1
      | 2 => select feat p (some m) r2
      | 3 => select feat p (some m) r3
      | 4 => select feat p (some m) r4
      | 5 => select feat p (some m) r5
      | 6 => select feat p (some m) r6
      | _ => select feat p (some m) r7
  | .byMod mem reg =>
    match m with
    | none => .needModRM
    | some m => if m / 64 = 3 then select feat p (some m) reg else select feat p (some m) mem
  | .byModRM b hit other =>
    match m with
    | none => .needModRM
    | some m => if m = b then select feat p (some m) hit else select feat p (some m) other
  | .byRM r0 r1 r2 r3 r4 r5 r6 r7 =>
    match m with
    | none => .needModRM
    | some m =>
      match m % 8 with
      | 0 => select feat p (some m) r0
      | 1 => select feat p (some m) r1
      | 2 => select feat p (some m) r2
      | 3 => select feat p (some m) r3
      | 4 => select feat p (some m) r4
      | 5 => select feat p (some m) r5
      | 6 => select feat p (some m) r6
      | _ => select feat p (some m) r7
  | .byPfx np p66 pF3 pF2 =>
    if p.rep = 0xF3 then select feat p m pF3
    else if p.rep = 0xF2 then select feat p m pF2
    else if p.osz then select feat p m p66
    else select feat p m np
  | .byW w0 w1 => if p.w then select feat p m w1 else select feat p m w0
  | .byRexB b0 b1 => if p.b = 8 then select feat p m b1 else select feat p m b0
  | .byFeat f yes no => if f.holds feat then select feat p m yes else select feat p m no
  | .byL l0 l1 l2 l3 =>
    match (p.vex.map (·.l)).getD 0 with
    | 0 => select feat p m l0
    | 1 => select feat p m l1
    | 2 => select feat p m l2
    | _ => select feat p m l3
  | .ud ops => .invalid ops {} true
  | .invalid e =>
    match select feat p m e with
    | .done _ ops a => .invalid ops a true
    | s => s
  | .missing e =>
    match select feat p m e with
    | .done _ ops a | .invalid ops a _ => .invalid ops a false
    | s => s
  | .nm => .nm

/-- Whether an operand is encoded in the ModRM byte. -/
def OS.usesModRM : OS → Bool
  | .E _ | .G _ | .M | .ER _ _ | .V | .W _ | .U | .vecR _ | .vecM _ | .vecU _ | .kR | .kM _ | .STi
  | .Mb _ => true
  | _ => false

/-- Whether an operand is the register `VEX.vvvv` names. -/
def OS.usesVvvv : OS → Bool
  | .vecV _ | .gprV _ | .kV => true
  | _ => false

/-- The operand size (SDM Vol. 2 2.2.1.2, Table 2-4; A.2.5 for `d64`/`f64`). The `66` that a
VEX or EVEX `pp` field stands for is an opcode extension only (SDM Vol. 2, 2.3.6.3). -/
def opSize (p : Pfx) (a : Attr) : Nat :=
  if a.f64 then 64 else if p.w then 64 else if p.osz ∧ p.vex.isNone then 16
  else if a.d64 then 64 else 32

/-- Width in bits of a size code, for operand size `osz`. -/
def Sz.bits (p : Pfx) (osz : Nat) : Sz → Nat
  | .b => 8 | .w => 16 | .d => 32 | .q => 64 | .v => osz
  | .z => if osz = 16 then 16 else 32
  | .y => if p.w then 64 else 32
  | .dq => 128
  | .x => p.vl

/-- A general register operand; byte registers 4–7 are `AH`–`BH` without REX. -/
def gpr (p : Pfx) (w n : Nat) : Opd :=
  if w = 8 ∧ p.rex = 0 ∧ 4 ≤ n ∧ n < 8 then .reg ⟨8, n - 4, true⟩ else .reg ⟨w, n, false⟩

/-- The r/m side of a ModRM byte. -/
inductive RM
  /-- A register (`mod = 3`), number with `REX.B`. -/
  | reg (n : Nat)
  /-- A memory operand. -/
  | mem (m : MemOp)

/-- Read SIB and displacement for ModRM byte `m` (SDM Vol. 2 2.1.5, Tables 2-2, 2-3;
2.2.1.6 RIP-relative addressing). An 8-bit displacement is multiplied by `n8` (1, or an EVEX
instruction's `N`, SDM Vol. 2, 2.7.5). -/
def decodeRM (p : Pfx) (n8 : Nat) (m : Nat) : D RM := do
  let md := m / 64
  let rm := m % 8
  if md = 3 then pure (.reg (rm + p.b))
  else
    let mk (base index : Option Nat) (scale disp : Nat) (rip : Bool) : RM :=
      .mem ⟨p.seg, base, index, scale, disp, rip, p.asz, 0⟩
    let disp (noBase : Bool) : D Nat :=
      if md = 1 then do let d ← next; pure (sext 8 64 d * n8 % 2 ^ 64)
      else if md = 2 ∨ noBase then do let d ← readLE 4; pure (sext 32 64 d)
      else pure 0
    if rm = 4 then do
      let sib ← next
      let idx := (sib / 8) % 8 + p.x
      let index := if idx = 4 then none else some idx
      let scale := 2 ^ (sib / 64)
      let noBase := sib % 8 = 5 ∧ md = 0
      let d ← disp noBase
      pure (mk (if noBase then none else some (sib % 8 + p.b)) index scale d false)
    else if rm = 5 ∧ md = 0 then do
      let d ← readLE 4
      pure (mk none none 1 (sext 32 64 d) true)
    else do
      let d ← disp false
      pure (mk (some (rm + p.b)) none 1 d false)

/-- One operand, or `none` if the encoding of this operand is invalid (`#UD` once the instruction's
bytes are read). `m` is the ModRM byte, `rm` its decoded r/m side, `opc` the opcode byte.
Immediates are read in operand order, after ModRM, SIB and displacement. -/
def operand (p : Pfx) (osz opc : Nat) (m : Nat) (rm : Option RM) : OS → D (Option Opd)
  | .E s =>
    match rm with
    | some (.reg n) => pure (some (gpr p (s.bits p osz) n))
    | some (.mem x) => pure (some (.mem { x with width := s.bits p osz }))
    | none => pure none
  | .G s => pure (some (gpr p (s.bits p osz) ((m / 8) % 8 + p.r)))
  | .I s => do
    let w := s.bits p osz
    match s with
    | .z => do let v ← readLE (w / 8); pure (some (.imm osz (sext w osz v)))
    | _ => do let v ← readLE (w / 8); pure (some (.imm w v))
  | .Ibs s => do let v ← next; pure (some (.imm (s.bits p osz) (sext 8 (s.bits p osz) v)))
  | .J s => do
    let w := s.bits p osz
    let v ← readLE (w / 8)
    pure (some (.rel (sext w 64 v)))
  | .M =>
    match rm with
    | some (.mem x) => pure (some (.mem x))
    | _ => pure none
  | .ER r m =>
    match rm with
    | some (.reg n) => pure (some (gpr p (r.bits p osz) n))
    | some (.mem x) => pure (some (.mem { x with width := m.bits p osz }))
    | none => pure none
  | .Z s => pure (some (gpr p (s.bits p osz) (opc % 8 + p.b)))
  | .A s => pure (some (gpr p (s.bits p osz) 0))
  | .one => pure (some (.imm 8 1))
  | .CL => pure (some (.reg ⟨8, 1, false⟩))
  | .rCX => pure (some (.reg ⟨if p.asz then 32 else 64, 1, false⟩))
  | .V => pure (some (.xmm ((m / 8) % 8 + p.r)))
  | .W s =>
    match rm with
    | some (.reg n) => pure (some (.xmm n))
    | some (.mem x) => pure (some (.mem { x with width := s.bits p osz }))
    | none => pure none
  | .U =>
    match rm with
    | some (.reg n) => pure (some (.xmm n))
    | _ => pure none
  | .XMM0 => pure (some (.xmm 0))
  | .X s => pure (some (.mem ⟨p.seg, some 6, none, 1, 0, false, p.asz, s.bits p osz⟩))
  | .Y s => pure (some (.mem ⟨some .es, some 7, none, 1, 0, false, p.asz, s.bits p osz⟩))
  | .vecR s => pure (some (.vreg ((m / 8) % 8 + p.r + p.rhi) (s.bits p osz)))
  | .vecM s =>
    match rm with
    | some (.reg n) => pure (some (.vreg (n + p.xhi) (s.bits p osz)))
    | some (.mem x) => pure (some (.mem { x with width := s.bits p osz }))
    | none => pure none
  | .vecU s =>
    match rm with
    | some (.reg n) => pure (some (.vreg (n + p.xhi) (s.bits p osz)))
    | _ => pure none
  | .vecV s => pure (some (.vreg p.vvvv (s.bits p osz)))
  -- a general register or an opmask register in `vvvv` is one of `0`–`15` or `k0`–`k7`: with
  -- the other bits set the encoding is invalid (SDM Vol. 2, Tables 2-41 and 2-42)
  | .gprV s => if p.vvvv < 16 then pure (some (gpr p (s.bits p osz) p.vvvv)) else pure none
  | .kV => if p.vvvv < 8 then pure (some (.kreg p.vvvv)) else pure none
  -- an opmask register in ModRM reg needs `R` (and `EVEX.R'`) clear (Table 2-41)
  | .kR => if p.r = 0 ∧ p.rhi = 0 then pure (some (.kreg ((m / 8) % 8))) else pure none
  -- in ModRM r/m, `B` and `X` are ignored (Table 2-41)
  | .kM s =>
    match rm with
    | some (.reg n) => pure (some (.kreg (n % 8)))
    | some (.mem x) => pure (some (.mem { x with width := s.bits p osz }))
    | none => pure none
  | .ST0 => pure (some (.st 0))
  | .STi => pure (some (.st (m % 8)))
  | .Mb n =>
    match rm with
    | some (.mem x) => pure (some (.mem { x with width := 8 * n }))
    | _ => pure none

/-- The operands `os`, in order (`none` for an invalid one, `operand`). -/
def operands (p : Pfx) (osz opc m : Nat) (rm : Option RM) : List OS → D (List (Option Opd))
  | [] => pure []
  | o :: os => do
    let x ← operand p osz opc m rm o
    let xs ← operands p osz opc m rm os
    pure (x :: xs)

/-- All the operands, or `none` if one of them is invalid. -/
def allValid : List (Option Opd) → Option (List Opd)
  | [] => some []
  | none :: _ => none
  | some x :: xs => match allValid xs with
    | some ys => some (x :: ys)
    | none => none

/-- The width reported for an instruction: 8 for byte forms (first operand of size `b`),
else the operand size. -/
def reportedSize (osz : Nat) : List OS → Nat
  | .E .b :: _ | .G .b :: _ | .A .b :: _ | .Z .b :: _ | .X .b :: _ | .Y .b :: _ => 8
  | _ => osz

/-- The opmask fields of an EVEX instruction that takes masking `k`: the mask register and
`EVEX.z`, or `none` for a combination the instruction does not allow (`#UD`; SDM Vol. 2, 2.7.4,
Table 2-42; `EVEX.z` alone on a form without masking and a register destination is not modelled,
`finishForm`). -/
def maskOf (v : VexPfx) : Masking → Option (Option Nat × Bool)
  | .none => if v.aaa = 0 ∧ !v.z then some (none, false) else none
  | .merge => if v.z then none else some (some v.aaa, false)
  | .full => if v.z ∧ v.aaa = 0 then none else some (some v.aaa, v.z)

/-- Decode the rest of an encoding whose form has operands `ops` and attributes `a`, after its
ModRM byte `m`: SIB, displacement, immediates. `form`: its mnemonic, or `none` for an invalid
encoding; `bad`: the encoding is invalid whatever the form (`finish`). An invalid encoding raises
`#UD` only now, after all the bytes of its form are read (`Entry.ud`; an AMD Zen 4 and Intel XED
agree on these lengths). `hle`: the processor has HLE (`Features.hle`), whose prefix hints are not
modelled. -/
def finishForm (hle : Bool) (p : Pfx) (bad : Bool) (map opc : Nat) (m : Option Nat) (form : Option Mn)
    (ops : List OS) (a : Attr) : D Inst := do
  let osz := opSize p a
  -- AMD honours `66` on near branches (APM Vol. 3 1.2.2); CPU-dependent, not modelled. With
  -- `REX.W` both manuals give 64 bits: the APM because `REX.W` takes precedence over `66` (1.2.2),
  -- the SDM because `66` with `REX.W` is ignored (Vol. 2, 2.2.1.2) and
  -- near branches are 64-bit regardless (Vol. 1, 7.3.8.3)
  if form.isSome && a.f64 && p.osz && !p.w then stop (.nm map opc) else do
  -- `vvvv` must be 1111b (with `EVEX.V'`: the register number 0) where no operand uses it
  -- (SDM Vol. 2, 2.3.6; Table 2-41)
  let vvvvOK := ops.any OS.usesVvvv || p.vvvv == 0
  -- EVEX: the opmask fields; `EVEX.b`; the displacement factor (SDM Vol. 2, 2.7.5)
  let (mask, n8, bc) ← match p.vex with
    | some v =>
      if v.evex then
        if v.b then
          -- broadcast of a memory source (2.7.7), `N` the element size (Table 2-36); with a
          -- register source (`regB` below) `EVEX.b` would be rounding control or "suppress all
          -- exceptions", which no integer instruction defines; `#UD` for the instruction classes
          -- of Table 2-37 (Table 2-43)
          match a.bcst, m with
          | some e, some mb =>
            if mb / 64 = 3 then pure (maskOf v a.masking, 1, none)
            else pure (maskOf v a.masking, e / 8, some e)
          | _, _ => pure (none, 1, none)
        else pure (maskOf v a.masking, (match a.disp8 with | .full => p.vl / 8 | .scalar n => n), none)
      else pure (some (none, false), 1, none)
    | none => pure (some (none, false), 1, none)
  let rm ← match m with
    | some mb => do let r ← decodeRM p n8 mb; pure (some r)
    | none => pure none
  let xs ← operands p osz opc (m.getD 0) rm ops
  let len ← pos
  -- every byte of the encoding has been read: an invalid one raises `#UD` now
  -- `EVEX.b` with a register source on a broadcast form: `#UD` by both manuals and Intel XED, while
  -- an AMD Zen 4 executes `VPADDD` and `VPTERNLOGD` with it as without it; so, once the checks every
  -- processor makes have passed, not modelled
  let regB : Bool := match p.vex, a.bcst, m with
    | some v, some _, some mb => v.evex && v.b && mb / 64 == 3
    | _, _, _ => false
  match form, allValid xs, mask with
  | some mn, some xs, some (mask, zero) =>
    if bad || !vvvvOK then stop .ud else do
    if regB then stop (.nm map opc) else do
    -- a broadcast source is one element of the memory operand
    let xs := match bc with
      | some e => xs.map fun
          | .mem x => .bcst { x with width := e } x.width
          | o => o
      | none => xs
    -- `LOCK` needs a lockable instruction with a memory destination (SDM Vol. 2 LOCK)
    let lockOK : Bool := match xs with
      | .mem _ :: _ => a.lock
      | _ => false
    if p.lock && !lockOK then stop .ud else do
    -- on a processor with HLE, `F2` (`XACQUIRE`) or `F3` (`XRELEASE`), the last of them, on the
    -- instructions that take the hint (SDM Vol. 2, "XACQUIRE/XRELEASE"): a lockable form with a memory
    -- destination and `LOCK`, `XCHG` with a memory operand, and with `F3` `MOV` to memory (`88`, `89`,
    -- `C6`, `C7`). The processor may then elide the lock and run the code up to the matching release
    -- as a transaction (SDM Vol. 1, 17.2.1): not modelled. Without HLE the hints are ignored (below).
    let hinted : Bool := p.rep != 0 && match xs with
      | .mem _ :: _ =>
        (lockOK && (p.lock || mn matches .xchg)) ||
          (p.rep == 0xF3 && map == 0 && [0x88, 0x89, 0xC6, 0xC7].contains opc)
      | _ => false
    if hinted && hle then stop (.nm map opc) else do
    -- F2 on MOVS, STOS, LODS is defined by neither manual (REPNE is for CMPS and SCAS): not
    -- modelled
    if a.str ∧ !a.strZ ∧ p.rep = 0xF2 then stop (.nm map opc) else do
    let rep := if a.str ∧ p.rep = 0xF3 then some Rep.rep
      else if a.strZ ∧ p.rep = 0xF2 then some Rep.repne else none
    -- the `FOP` of an x87 escape opcode (`D8`–`DF`): the opcode byte's low three bits and the ModRM
    -- byte; `FWAIT` (`9B`) and `FXSAVE`/`FXRSTOR` (`0F AE`) have none
    let fop := if map = 0 ∧ 0xD8 ≤ opc ∧ opc ≤ 0xDF then (opc % 8) * 256 + m.getD 0 else 0
    pure ⟨mn, reportedSize osz ops, xs, len, rep, p.lock, mask, zero, fop⟩
  -- `EVEX.z` with `EVEX.aaa = 000` on any EVEX form without masking (`Masking.none`: `VMOVD`, `VMOVQ`
  -- among others) is `#UD` by the SDM (Table 2-42, "Instructions with EVEX.aaa = 000b") and the APM
  -- (Vol. 4, "Illegal EVEX Encoding Exceptions": "EVEX.z == 1 && EVEX.aaa == 000b", all instructions);
  -- an AMD Zen 4 executes it as without `EVEX.z` for a register destination, so every such form with a
  -- register destination is not modelled
  | some _, some (d :: _), none =>
    let zOnly := match p.vex with
      | some v => v.evex && a.masking matches .none && v.z && v.aaa == 0 && !v.b
      | none => false
    if zOnly && !bad && vvvvOK && !(d matches .mem _) then stop (.nm map opc) else stop .ud
  | _, _, _ => stop .ud

/-- Whether all 15 bytes from the instruction's first can be fetched, the most any processor fetches
for one instruction (SDM Vol. 2, 2.3.11; APM Vol. 3, 1.1). -/
def allFetchable (fetch : Nat → Option Byte) : Bool :=
  (List.range 15).all fun k => (fetch k).isSome

/-- Run `x`, the decoding of an encoding whose length is not settled (a form whose feature the processor
lacks, `Entry.missing`): a processor that does not know the form may decode another length. Its `#UD`
is therefore certain only when all 15 bytes an instruction may have can be fetched (`allFetchable`);
otherwise, and at a fetch fault (`#PF`, or `#GP` for more than 15 bytes), the outcome is not modelled. -/
def lengthNotSettled {α : Type} (map opc : Nat) (x : D α) : D α := fun fetch i =>
  match x fetch i with
  | .error (.pf _) | .error .gp => .error (.nm map opc)
  | .error .ud => if allFetchable fetch then .error .ud else .error (.nm map opc)
  | r => r

/-- Decode the instruction selected by cell `e` of map `map` at opcode `opc`, reading the ModRM
byte if the cell's choice or its operands need it (`finishForm`). `bad`: the encoding is invalid
whatever the cell says (a prefix before `VEX` or `EVEX` that is not allowed there, reserved bits
of an `EVEX` prefix, `EVEX` without AVX-512). -/
def finish (feat : Features) (p : Pfx) (bad : Bool) (map opc : Nat) (e : Entry) : D Inst :=
  match select feat p none e with
  | .needModRM => do
    let m ← next
    match select feat p (some m) e with
    | .done mn ops a => finishForm feat.hle p bad map opc (some m) (some mn) ops a
    | .invalid ops a true => finishForm feat.hle p bad map opc (some m) none ops a
    | .invalid ops a false => lengthNotSettled map opc (finishForm feat.hle p bad map opc (some m) none ops a)
    | _ => stop (.nm map opc)
  | .done mn ops a =>
    if ops.any OS.usesModRM then do let m ← next; finishForm feat.hle p bad map opc (some m) (some mn) ops a
    else finishForm feat.hle p bad map opc none (some mn) ops a
  | .invalid ops a settled =>
    let rest : D Inst :=
      if ops.any OS.usesModRM then do let m ← next; finishForm feat.hle p bad map opc (some m) none ops a
      else finishForm feat.hle p bad map opc none none ops a
    if settled then rest else lengthNotSettled map opc rest
  | .nm => stop (.nm map opc)

/-- The legacy prefixes a VEX or EVEX `pp` field stands for (SDM Vol. 2, 2.3.6.3): none, `66`,
`F3`, `F2`. -/
def withPP (p : Pfx) (pp : Nat) : Pfx :=
  match pp with
  | 1 => { p with osz := true }
  | 2 => { p with rep := 0xF3 }
  | 3 => { p with rep := 0xF2 }
  | _ => p

/-- The REX byte with bits `W`, `R`, `X`, `B`. -/
def rexOf (w r x b : Bool) : Nat :=
  0x40 + (if w then 8 else 0) + (if r then 4 else 0) + (if x then 2 else 0) + (if b then 1 else 0)

/-- Decode the rest of an instruction after a VEX prefix `C4`/`C5` (`b`): the prefix's payload,
the opcode in the map it names, and what follows (SDM Vol. 2, 2.3.5, Figure 2-9). `R`, `X`,
`B` and `vvvv` are stored inverted. `bad` as for `finish`. -/
def decodeVex (feat : Features) (p : Pfx) (bad : Bool) (b : Nat) : D Inst := do
  let bit (x i : Nat) : Bool := (x / 2 ^ i) % 2 = 1
  let (rex, map, v1) ← if b = 0xC5 then do
      let v1 ← next
      pure (rexOf false (!bit v1 7) false false, 1, v1)
    else do
      let v0 ← next
      let v1 ← next
      pure (rexOf (bit v1 7) (!bit v0 7) (!bit v0 6) (!bit v0 5), v0 % 32, v1)
  let p : Pfx := { withPP p (v1 % 4) with
    rex, vex := some ⟨false, (v1 / 4) % 2, 15 - (v1 / 8) % 16, 0, 0, 0, false, false⟩ }
  let opc ← next
  match map with
  | 1 => finish feat p bad 0xC4 opc (vex0F opc)
  | 2 => finish feat p bad 0xC4 opc (vex0F38 opc)
  | 3 => finish feat p bad 0xC4 opc (vex0F3A opc)
  -- map 0 is reserved (`#UD`), but how many bytes the processor fetches first is not settled
  -- (an AMD Zen 4 takes a ModRM byte, SIB and displacement; Intel XED stops at the map field);
  -- maps from 4 on are used by later extensions
  | _ => stop (.nm 0xC4 opc)

/-- Decode the rest of an instruction after an EVEX prefix `62`: the three payload bytes `P0`,
`P1`, `P2`, the opcode in the map `EVEX.mmm` names, and what follows (SDM Vol. 2, 2.7.1,
Figure 2-11, Table 2-32; the opcode-independent `#UD` conditions of 2.7.11.2, Table 2-40).
`R`, `X`, `B`, `R'`, `vvvv` and `V'` are stored inverted. With APX the reserved bits carry
register bits of its own (not modelled); without, they make the encoding invalid. `bad` as for
`finish`. -/
def decodeEvex (feat : Features) (p : Pfx) (bad : Bool) : D Inst := do
  let p0 ← next
  let p1 ← next
  let p2 ← next
  let bit (x i : Nat) : Bool := (x / 2 ^ i) % 2 = 1
  let reserved : Bool := bit p0 3 || !bit p1 2
  if reserved ∧ feat.apx then stop (.nm 0x62 0) else do
  let p : Pfx := { withPP p (p1 % 4) with
    rex := rexOf (bit p1 7) (!bit p0 7) (!bit p0 6) (!bit p0 5)
    vex := some ⟨true, (p2 / 32) % 4, 15 - (p1 / 8) % 16 + (if bit p2 3 then 0 else 16),
      if bit p0 4 then 0 else 16, if bit p0 6 then 0 else 16, p2 % 8, bit p2 7, bit p2 4⟩ }
  let opc ← next
  match p0 % 8 with
  | 1 => finish feat p (bad || reserved) 0x62 opc (evex0F opc)
  | 2 => finish feat p (bad || reserved) 0x62 opc (evex0F38 opc)
  | 3 => finish feat p (bad || reserved) 0x62 opc (evex0F3A opc)
  -- maps 5 and 6 (AVX512-FP16), map 4 APX's; maps 0 and 7 are reserved (`#UD`), but how many
  -- bytes the processor fetches first is not settled (an AMD Zen 4 takes a ModRM byte in map 0,
  -- more in map 7; Intel XED stops at the map field in map 0)
  | _ => stop (.nm 0x62 opc)

/-- The outcome of `x`, the decoding of a `VEX` or `EVEX` instruction after its escape byte `b`
(`C4`, `C5`, `62`), on a processor that may not know the format (`unknown`: for VEX one without AVX,
for EVEX one without AVX512F). Such a processor may take `b` as `LES`, `LDS` or `BOUND`, invalid in 64-bit mode with a
ModRM operand (SDM Vol. 2, Table A-2, superscript `i64`): `#UD` after its ModRM, SIB and
displacement. An instruction `x` decodes is one the processor knows; otherwise the outcome is
`#UD` where both readings give `#UD` and all 15 bytes an instruction may have can be fetched
(`allFetchable`, as for `lengthNotSettled`), and not modelled where a byte cannot be fetched or the
readings differ: how many bytes such a processor fetches before its `#UD` is not settled (an AMD Zen 4,
for example, raises the `#UD` of `UD0` before fetching its ModRM byte), so a fetch fault or an
instruction longer than 15 bytes is not certain even where both readings reach it. -/
def formatUnknown (unknown : Bool) (p : Pfx) (b : Nat) (x : D Inst) : D Inst := fun fetch i =>
  match x fetch i with
  | .ok r => .ok r
  | r =>
    if !unknown then r else
    let legacy : D Unit := do let m ← next; let _ ← decodeRM p 1 m; pure ()
    match r, legacy fetch i with
    | .error .ud, .ok _ => if allFetchable fetch then r else .error (.nm 0 b)
    | .error (.nm map op), _ => .error (.nm map op)
    | _, _ => .error (.nm 0 b)

/-- Decode one instruction in 64-bit mode (SDM Vol. 2, 2.1, Figure 2-1: prefixes, opcode,
ModRM, SIB, displacement, immediate). -/
def decodeInst (feat : Features) : D Inst := do
  let (p, b) ← prefixes 16 {}
  if b = 0x0F then do
    let b2 ← next
    if b2 = 0x38 then do let b3 ← next; finish feat p false 0x0F38 b3 (map0F38 b3)
    else if b2 = 0x3A then do let b3 ← next; finish feat p false 0x0F3A b3 (map0F3A b3)
    else finish feat p false 0x0F b2 (twoByte b2)
  -- VEX and EVEX (SDM Vol. 2 2.3.2, 2.7.11). After a REX prefix they raise `#UD`, but the
  -- length the processor fetches first is not settled (an AMD Zen 4 takes `C4`, `C5`, `62` as
  -- `LES`, `LDS`, `BOUND` with a ModRM byte, Intel XED as `VEX`/`EVEX`): not modelled. After 66,
  -- F2, F3 or F0 they raise `#UD` after their bytes (the prefixes' own meaning dropped). EVEX
  -- needs AVX-512 enabled (Table 2-39, `#UD` after its bytes); VEX's needs are per instruction
  -- (BMI needs no AVX). A processor without AVX (AVX-512F) may not know the format at all
  -- (`formatUnknown`).
  else if b = 0xC4 ∨ b = 0xC5 ∨ b = 0x62 then
    if p.rex ≠ 0 then stop (.nm 0 b) else do
    let bad : Bool := p.osz || p.rep != 0 || p.lock
    let q := { p with osz := false, rep := 0, lock := false }
    if b = 0x62 then formatUnknown (!feat.avx512f) p b (decodeEvex feat q (bad || !feat.avx512f))
    else formatUnknown (!feat.avx) p b (decodeVex feat q bad b)
  -- APX REX2 prefix; without APX, `D5` is `AAD Ib`, invalid in 64-bit mode (`oneByte`)
  else if b = 0xD5 ∧ feat.apx then stop (.nm 0xD5 0)
  else finish feat p false 0 b (oneByte b)

/-- Decode the instruction whose bytes are `fetch 0`, `fetch 1`, …; `fetch i = none` means
byte `i` cannot be fetched. Bytes are requested in order and only as far as the
instruction extends. -/
def decode (feat : Features) (fetch : Nat → Option Byte) : Decoded :=
  match decodeInst feat fetch 0 with
  | .ok (i, _) => .ok i
  | .error .ud => .ud
  | .error .gp => .gp
  | .error (.pf o) => .pf o
  | .error (.nm map o) => .nm map o

end ZellicX86.Decode
