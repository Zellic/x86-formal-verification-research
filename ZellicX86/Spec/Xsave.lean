import ZellicX86.Spec.State
import ZellicX86.Spec.Profile
/-!
# The `XSAVE` area

The area `XSAVE` writes and `XRSTOR` reads, in the standard format (SDM Vol. 1, ch. 13 "Managing
State Using the XSAVE Feature Set"; AMD APM Vol. 2, 11.5): its layout on a processor, what `XSAVE`
writes there for the state components the model holds, and what `XRSTOR` and `FXRSTOR` load from
it. The kernel puts one in every signal frame and loads it back at `rt_sigreturn`
(`Spec/Linux/Signal.lean`). The model has state for the x87, SSE, AVX, opmask, `ZMM_Hi256`,
`Hi16_ZMM` and `PKRU` components (0, 1, 2, 5, 6, 7, 9); a frame on a processor whose kernel saves
another component (MPX, AMX tile configuration, APX) is not modelled there.

The layout of the extended region is the processor's: component `i` lies at
`CPUID.(EAX=0DH,ECX=i):EBX` and is `CPUID.(EAX=0DH,ECX=i):EAX` bytes long (SDM 13.4.3), as the
kernel reads them at boot on the boot processor (`setup_xstate_cache`,
`arch/x86/kernel/fpu/xstate.c`), here the profile's CPU 0.

Where the manuals leave a byte unspecified, `XSAVE` writes a value the caller supplies (`rsv`):
byte 5 and the upper six bytes of each x87 register's 16 (SDM Table 13-1, "Rsvd."), the four bytes
after `PKRU`, and on an AMD processor the x87 error pointers when no x87 exception is pending and the
processor does not promise zeros (APM Vol. 2, 11.5.10).
-/
namespace ZellicX86

/-- The state components the model holds (SDM Vol. 1, 13.1): x87 (0), SSE (1), AVX (2), opmask
(5), `ZMM_Hi256` (6), `Hi16_ZMM` (7), `PKRU` (9). -/
def xHeld : BitVec 64 := 0x2E7

/-- The offset of state component `i` in the standard format (`CPUID.(EAX=0DH,ECX=i):EBX`, on CPU
0). -/
def Profile.xOffset (prof : Profile) (i : Nat) : Nat :=
  (prof.cpuid 0 0xD (BitVec.ofNat 32 i)).ebx.toNat

/-- The size of state component `i` (`CPUID.(EAX=0DH,ECX=i):EAX`, on CPU 0). -/
def Profile.xSize (prof : Profile) (i : Nat) : Nat :=
  (prof.cpuid 0 0xD (BitVec.ofNat 32 i)).eax.toNat

/-- The user state components the kernel saves for a process (`fpstate->user_xfeatures`; for a
process that has not asked for AMX, `fpu_user_cfg.default_features`, `arch/x86/kernel/fpu/xstate.c`
`fpu__init_system_xstate`): those enabled in `XCR0` but AMX tile data (component 18), which a process
gets only on request (`arch_prctl(ARCH_REQ_XCOMP_PERM)`, not modelled). -/
def Profile.userXfeatures (prof : Profile) : BitVec 64 :=
  prof.xcr0.getD 0 &&& ~~~((1 : BitVec 64) <<< 18)

/-- The size of the area for the user components (`fpstate->user_size`, `xstate_calculate_size`):
the end of the highest component, at least the 512-byte legacy region and the 64-byte header. -/
def Profile.xUserSize (prof : Profile) : Nat :=
  let f := prof.userXfeatures
  match ((List.range 64).reverse.find? fun i => f.getLsbD i) with
  | some i => if i ≤ 1 then 576 else prof.xOffset i + prof.xSize i
  | none => 576

/-- The size of the area for every user component the kernel enabled, AMX tile data too
(`fpu_user_cfg.max_size`, `xstate_calculate_size` of `max_features`): as `xUserSize`, over all of
`XCR0`. -/
def Profile.xMaxSize (prof : Profile) : Nat :=
  let f := prof.xcr0.getD 0
  match ((List.range 64).reverse.find? fun i => f.getLsbD i) with
  | some i => if i ≤ 1 then 576 else prof.xOffset i + prof.xSize i
  | none => 576

/-- Whether `MXCSR` value `v` sets only bits the processor supports (`MXCSR_MASK`, or `FFBFH` when
the processor stores 0 there: SDM Vol. 1, 11.6.6). -/
def Profile.mxcsrOk (prof : Profile) (v : BitVec 32) : Bool :=
  let m := if prof.mxcsrMask = 0 then 0xFFBF else prof.mxcsrMask
  v &&& ~~~m == 0

/-- The byte at offset `o` of `v`. -/
def byteOf {w : Nat} (v : BitVec w) (o : Nat) : Byte := (v >>> (8 * o)).setWidth 8

/-! ## x87 tags -/

/-- The tag of a register that is not empty, from its contents (SDM Vol. 1, 8.1.7, Figure 8-7; APM
Vol. 1, 6.2.4, Table 6-3): 1 (zero) for +0 and -0, 2 (special) for a NaN, an infinity, a denormal or
an unsupported format (exponent all ones, or exponent zero with a fraction, or the integer bit clear
with a nonzero exponent), 0 (valid) otherwise; an empty register's tag is 3. -/
def x87TagOfValue (v : BitVec 80) : BitVec 2 :=
  let e := v.extractLsb' 64 15
  let j := v.getLsbD 63
  let frac := v.extractLsb' 0 63
  if e = 0x7FFF then 2
  else if e = 0 then (if !j && frac = 0 then 1 else 2)
  else if j then 0 else 2

/-- The full tag word `FNSTENV` and `FNSAVE` store (SDM Vol. 1, 8.1.7): two bits per physical register
`j`, 3 for an empty one (bit `j` of `full` clear), else its contents' tag (`x87TagOfValue`). -/
def x87TagsFrom (full : BitVec 8) (st : Fin 8 → BitVec 80) : BitVec 16 :=
  (List.range 8).foldl (fun w j =>
    let t : BitVec 2 := if full.getLsbD j then x87TagOfValue (st (Fin.ofNat 8 j)) else 3
    w ||| (t.setWidth 16 <<< (2 * j))) 0

/-- The x87 state in its initial configuration (SDM Vol. 1, 13.6; `FNINIT`): `FCW` `037FH`,
everything else zero, every register empty. -/
def X87.init : X87 := ⟨fun _ => 0, 0x37F, 0, 0, 0, 0, 0⟩

/-- Physical register `R((TOP + i) mod 8)`, which is `ST(i)`; `TOP` is `FSW` bits 13–11. -/
def X87.stIdx (fsw : BitVec 16) (i : Nat) : Fin 8 :=
  Fin.ofNat 8 ((fsw >>> 11).toNat % 8 + i)

/-! ## `XSAVE` -/

/-- Whether processor `prof` deprecates the x87 selectors `FCS` and `FDS`, storing them as 0000H: an
Intel processor with `Profile.fcsDeprecated` (SDM Vol. 1, 8.1.8; Vol. 2, "FXSAVE", Table 3-53: "this
field is saved as 0000H"). -/
def Profile.zeroesSelectors (prof : Profile) : Bool :=
  prof.vendor = .intel && prof.fcsDeprecated

/-- Whether state component `i` of `c` (with `PKRU` value `pkru`) counts as in its initial configuration for the lower
bound on `XINUSE`: a component this returns `false` for has its `XINUSE` bit set; one it returns `true` for may have
either value (SDM Vol. 1, 13.6). For the x87 component the check ignores `FIP`, `FDP` and `FOP` on both vendors: an AMD
Zen 4 clears `XINUSE[0]` after `FNINIT` followed by `FNOP`, although `FNOP` updates `FIP` and `FOP`, and the APM does
not define the initial configuration (APM Vol. 3, `XGETBV`, `XSAVEC`). So the pointers alone never require bit 0, a
bound that holds on both vendors. The other components the model holds are initial when their registers are zero,
`PKRU` included. -/
def Cpu.xInit (c : Cpu) (pkru : BitVec 32) (i : Nat) : Bool :=
  let zs (lo hi : Nat) (f : BitVec 512 → Bool) := (List.range (hi - lo)).all fun n => f (c.vec.zmm (Fin.ofNat 32 (lo + n)))
  match i with
  | 0 => c.x87.fcw == 0x37F && c.x87.fsw == 0 && c.x87.full == 0 &&
      (List.range 8).all fun j => c.x87.st (Fin.ofNat 8 j) == 0
  | 1 => zs 0 16 fun v => v.setWidth 128 == 0
  | 2 => zs 0 16 fun v => v.extractLsb' 128 128 == 0
  | 5 => (List.range 8).all fun j => c.vec.k (Fin.ofNat 8 j) == 0
  | 6 => zs 0 16 fun v => v.extractLsb' 256 256 == 0
  | 7 => zs 16 32 fun v => v == 0
  | 9 => pkru == 0
  | _ => true

/-- The bytes `XSAVE` (in 64-bit mode, with `REX.W`: `XSAVE64`) writes for the components in `rfbm`
(at most those the model holds) of the x87 state `x`, the vector state `v` and `PKRU` `pkru`, as runs
of bytes at offsets into the area: the x87 state (`FCW`, `FSW`, the abridged tag word, `FOP`, the
64-bit `FIP` and `FDP`, `ST0`–`ST7` in stack order), `MXCSR` and `MXCSR_MASK` with SSE or AVX state,
`XMM0`–`XMM15`, the upper halves of `YMM0`–`YMM15`, `k0`–`k7`, the upper halves of `ZMM0`–`ZMM15`,
`ZMM16`–`ZMM31`, and `PKRU` (SDM Vol. 1, 13.4–13.5 and 13.7). The header's `XSTATE_BV` is not among
them (`xsaveBv`). Unspecified bytes take their value from `rsv` at the same offset. Without `w64` the
legacy region has the format of `FXSAVE` without `REX.W` (SDM Vol. 2, "FXSAVE", Table 3-53): `FIP` and
`FDP` as their low 32 bits, at 8 and 16, each followed by a selector (`FCS`, `FDS`) and two reserved
bytes, which take their values from `rsv`; the selectors are 0 on a processor that deprecates them
(`Profile.zeroesSelectors`), else they take their values from `rsv` too (`x87EnvImage` says why the
selectors are not known). -/
def xsaveRuns (prof : Profile) (x : X87) (v : VecRegs) (pkru : BitVec 32) (rfbm : BitVec 64) {w : Nat}
    (rsv : BitVec w) (w64 : Bool) : List (Nat × List Byte) :=
  let has (i : Nat) := rfbm.getLsbD i
  let r (o n : Nat) : Nat × List Byte := (o, (List.range n).map fun k => byteOf rsv (o + k))
  let ptrs := prof.vendor = .intel || x.fsw.getLsbD 7 || prof.amdErrPtrs
  -- an AMD processor that promises to save the pointers zeroes them when no exception is pending
  let keep := prof.vendor = .intel || x.fsw.getLsbD 7
  let ptrVal {m : Nat} (v : BitVec m) : BitVec m := if keep then v else 0
  let sel (o : Nat) : Nat × List Byte := if prof.zeroesSelectors then (o, [0, 0]) else r o 2
  let x87 : List (Nat × List Byte) :=
    [(0, toBytesLE x.fcw 2), (2, toBytesLE x.fsw 2), (4, [x.full]), r 5 1] ++
    (if ptrs then
       (6, toBytesLE ((ptrVal x.fop).setWidth 16) 2) ::
       (if w64 then [(8, toBytesLE (ptrVal x.fip) 8), (16, toBytesLE (ptrVal x.fdp) 8)]
        else [(8, toBytesLE (ptrVal x.fip) 4), sel 12, r 14 2, (16, toBytesLE (ptrVal x.fdp) 4), sel 20, r 22 2])
     else [r 6 18]) ++
    (List.range 8).flatMap fun i => [(32 + 16 * i, toBytesLE (x.st (X87.stIdx x.fsw i)) 10), r (42 + 16 * i) 6]
  let zmm (i : Nat) := v.zmm (Fin.ofNat 32 i)
  (if has 0 then x87 else []) ++
  (if has 1 || has 2 then [(24, toBytesLE v.mxcsr 4), (28, toBytesLE prof.mxcsrMask 4)] else []) ++
  (if has 1 then (List.range 16).map fun i => (160 + 16 * i, toBytesLE (zmm i) 16) else []) ++
  (if has 2 then (List.range 16).map fun i =>
      (prof.xOffset 2 + 16 * i, toBytesLE ((zmm i).extractLsb' 128 128) 16) else []) ++
  (if has 5 then (List.range 8).map fun i =>
      (prof.xOffset 5 + 8 * i, toBytesLE (v.k (Fin.ofNat 8 i)) 8) else []) ++
  (if has 6 then (List.range 16).map fun i =>
      (prof.xOffset 6 + 32 * i, toBytesLE ((zmm i).extractLsb' 256 256) 32) else []) ++
  (if has 7 then (List.range 16).map fun i => (prof.xOffset 7 + 64 * i, toBytesLE (zmm (16 + i)) 64) else []) ++
  (if has 9 then [(prof.xOffset 9, toBytesLE pkru 4), r (prof.xOffset 9 + 4) 4] else [])

/-- The bits of `XSTATE_BV` `XSAVE` sets for the components in `rfbm` (SDM Vol. 1, 13.7): 1 for a
component the conservative `Cpu.xInit` check excludes from initial state; otherwise 0 or 1
as the processor's init optimization has it, here bit `i` of `inuse`. -/
def xsaveBv (c : Cpu) (pkru : BitVec 32) (rfbm inuse : BitVec 64) : BitVec 64 :=
  (List.range 64).foldl (fun bv i =>
    if rfbm.getLsbD i && (!c.xInit pkru i || inuse.getLsbD i) then bv ||| (1 <<< i) else bv) 0

/-- The bits XGETBV(1) must return for the enabled components of `c`: every component
excluded from initial state by the conservative `Cpu.xInit` check, plus SSE when MXCSR differs from 1F80H (SDM Vol. 1, 13.6;
APM Vol. 3, XGETBV: XCR0 AND XINUSE). The caller refuses enabled components whose state the
model does not hold (`xHeld`); this bound describes the held components only. -/
def Cpu.xInuseRequired (c : Cpu) (enabled : BitVec 64) : BitVec 64 :=
  xsaveBv c c.pkru enabled 0 ||| (if c.vec.mxcsr ≠ 0x1f80 then enabled &&& 2 else 0)

/-! ## `XRSTOR` and `FXRSTOR` -/

/-- What loading an area gives: the loaded state (`α`), `#GP` (the instruction faults), or a case the
model does not cover. -/
inductive XLoad (α : Type)
  | ok (c : α)
  | gp
  | notModelled (what : String)

/-- The loaded state transformed by `f`. -/
def XLoad.map {α β : Type} (f : α → β) : XLoad α → XLoad β
  | .ok c => .ok (f c)
  | .gp => .gp
  | .notModelled w => .notModelled w

/-- `c` with state component `i` in its initial configuration (SDM Vol. 1, 13.6). `MXCSR` is not
part of it. -/
def Cpu.xSetInit (c : Cpu) (i : Nat) : Cpu :=
  let setZ (lo hi : Nat) (f : BitVec 512 → BitVec 512) : Cpu :=
    { c with vec := { c.vec with zmm := fun j => if lo ≤ j.val ∧ j.val < hi then f (c.vec.zmm j) else c.vec.zmm j } }
  match i with
  | 0 => { c with x87 := X87.init }
  | 1 => setZ 0 16 fun v => v &&& ~~~(BitVec.allOnes 512 >>> 384)
  | 2 => setZ 0 16 fun v => v &&& ~~~((BitVec.allOnes 512 >>> 384) <<< 128)
  | 5 => { c with vec := { c.vec with k := fun _ => 0 } }
  | 6 => setZ 0 16 fun v => v.setWidth 256 |>.setWidth 512
  | 7 => setZ 16 32 fun _ => 0
  | 9 => { c with pkru := 0 }
  | _ => c

/-- `FSW` with its exception summary `ES` (bit 7) and busy bit `B` (bit 15) set if and only if an
exception flag (bits 5–0) is set whose mask bit in `FCW` is clear: `ES` "is set when any of the
unmasked exception flags are set", `B` "reflects the contents of the ES flag" (SDM Vol. 1, 8.1.3.3).
On an AMD processor `XRSTOR` and `FXRSTOR` compute them so rather than load them (APM Vol. 5,
"FXRSTOR": "after recomputing it from the error mask bits in FCW and error status bits in FSW"; an
AMD Zen 4 does so for `XRSTOR` too, as observed). The SDM's `FXRSTOR` and `XRSTOR` pages say
nothing about it, so on an Intel processor a restore whose loaded `FSW` differs from its summary is
not modelled (`x87SummaryKnown`). -/
def x87Summary (fcw fsw : BitVec 16) : BitVec 16 :=
  let es := (fsw &&& ~~~fcw &&& 0x3F) != 0
  (fsw &&& ~~~0x8080) ||| (if es then 0x8080 else 0)

/-- The control word a load of `v` gives (`FLDCW`, `FLDENV`, `FXRSTOR`, `XRSTOR`): bits 15–13 and 7 read
as 0 and bit 6 as 1, the others as loaded. The manuals call those bits reserved (SDM Vol. 1, 8.1.5,
Figure 8-6; APM Vol. 1, 6.2.3, Figure 6-4); an AMD Zen 4 keeps exactly this for each of the four
loads, as observed, and `FNINIT`'s `037FH` has the same form. -/
def x87Fcw (v : BitVec 16) : BitVec 16 := (v &&& 0x1F3F) ||| 0x40

/-- Whether the model knows the control word a load of `v` gives on processor `prof`: on an AMD
processor always (`x87Fcw`); on an Intel processor, whose manual does not say what it keeps of the
reserved bits, if `v` already has them as `x87Fcw` gives them (as every value `FNSTCW` stores does). -/
def x87FcwKnown (prof : Profile) (v : BitVec 16) : Bool := prof.vendor = .amd || x87Fcw v == v

/-- Whether the model knows the `FSW` a restore of the legacy region `rd` loads: on an AMD processor
always (`x87Summary`), on an Intel processor only if the stored `FSW` already equals its summary
(the SDM does not say whether `ES` and `B` are loaded or recomputed). -/
def x87SummaryKnown (prof : Profile) (rd : Nat → Byte) : Bool :=
  let w (o : Nat) : BitVec 16 := ofBytesLE 16 [rd o, rd (o + 1)]
  prof.vendor = .amd || x87Summary (w 0) (w 2) == w 2

/-- The x87 state `XRSTOR` or `FXRSTOR` loads from the legacy region `rd` (SDM Vol. 1, 13.5.1;
`FXRSTOR`): `FCW`, `FSW` with `ES` and `B` computed from the loaded words (`x87Summary`), `FOP`,
`FIP`, `FDP`, the registers from `ST0`–`ST7` in stack order, and the abridged tag word as it is
(`X87.full`). On an AMD processor that does not promise to restore them, the error pointers keep
their values unless the loaded state has an exception pending (`ES`; `amdErrPtrs`, APM Vol. 2,
11.5.10). Without `w64` (`FXRSTOR` without `REX.W`) `FIP` and `FDP` are loaded from their low 32 bits
with the upper bits cleared, and the selectors beside them are not used (SDM Vol. 1, 8.1.8). -/
def x87Load (prof : Profile) (old : X87) (rd : Nat → Byte) (w64 : Bool) : X87 :=
  let w (o n : Nat) (m : Nat) : BitVec m := ofBytesLE m ((List.range n).map fun k => rd (o + k))
  let fcw := x87Fcw (w 0 2 16)
  let fsw : BitVec 16 := x87Summary fcw (w 2 2 16)
  let regs : Fin 8 → BitVec 80 := fun j =>
    -- physical register j is ST((j - TOP) mod 8)
    let i := (j.val + 8 - (fsw >>> 11).toNat % 8) % 8
    w (32 + 16 * i) 10 80
  let ptrs := prof.vendor = .intel || fsw.getLsbD 7 || prof.amdErrPtrs
  { st := regs, fcw, fsw, full := rd 4,
    fop := if ptrs then w 6 2 11 else old.fop,
    fip := if ptrs then (if w64 then w 8 8 64 else w 8 4 64) else old.fip,
    fdp := if ptrs then (if w64 then w 16 8 64 else w 16 4 64) else old.fdp }

/-- `XRSTOR` (with `REX.W`) of the area `rd` (offset to byte, 64-byte aligned) for the components in
`rfbm`, on processor state `c` (SDM Vol. 1, 13.8.1, the standard form): `#GP` if `XSTATE_BV` sets a
bit not in `XCR0`, if bytes 8–23 of the header are not zero, or if `MXCSR` would be loaded with a bit
the processor does not support; a compacted area (`XCOMP_BV` bit 63, on a processor with the
compaction extensions, `CPUID.(EAX=0DH,ECX=1):EAX[1]`) is not modelled, nor on an Intel processor a
loaded `FSW` whose `ES`/`B` disagree with its exceptions (`x87SummaryKnown`). Each component in `rfbm`
is loaded if its `XSTATE_BV` bit is set and put in its initial configuration otherwise; `MXCSR` is
loaded whenever `rfbm` has SSE or AVX. `rfbm` holds only components the model holds. -/
def xrstor (prof : Profile) (c : Cpu) (rd : Nat → Byte) (rfbm : BitVec 64) : XLoad Cpu :=
  let w (o n : Nat) (m : Nat) : BitVec m := ofBytesLE m ((List.range n).map fun k => rd (o + k))
  let bv : BitVec 64 := w 512 8 64
  let xcomp : BitVec 64 := w 520 8 64
  let mxcsr : BitVec 32 := w 24 4 32
  let has (i : Nat) := rfbm.getLsbD i
  let loads (i : Nat) := has i && bv.getLsbD i
  if xcomp.getLsbD 63 && (prof.cpuid 0 0xD 1).eax.getLsbD 1 then .notModelled "compacted XSAVE area"
  else if xcomp ≠ 0 ∨ (w 528 8 64 : BitVec 64) ≠ 0 then .gp
  else if bv &&& ~~~(prof.xcr0.getD 0) ≠ 0 then .gp
  else if (has 1 || has 2) && !prof.mxcsrOk mxcsr then .gp
  else if loads 0 && !x87SummaryKnown prof rd then .notModelled "XRSTOR: FSW.ES/B on Intel"
  else if loads 0 && !x87FcwKnown prof (w 0 2 16) then .notModelled "XRSTOR: reserved FCW bits on Intel"
  else
    let c₀ := (List.range 10).foldl (fun c i => if has i && !bv.getLsbD i then c.xSetInit i else c) c
    let part (lo n o : Nat) (v : BitVec 512) : BitVec 512 :=
      let mask : BitVec 512 := (BitVec.allOnes 512 >>> (512 - n)) <<< lo
      (v &&& ~~~mask) ||| ((w o (n / 8) 512) <<< lo)
    let zmm' : Fin 32 → BitVec 512 := fun j =>
      let v := c₀.vec.zmm j
      let v := if loads 1 && j.val < 16 then part 0 128 (160 + 16 * j.val) v else v
      let v := if loads 2 && j.val < 16 then part 128 128 (prof.xOffset 2 + 16 * j.val) v else v
      let v := if loads 6 && j.val < 16 then part 256 256 (prof.xOffset 6 + 32 * j.val) v else v
      if loads 7 && 16 ≤ j.val then w (prof.xOffset 7 + 64 * (j.val - 16)) 64 512 else v
    .ok { c₀ with
      x87 := if loads 0 then x87Load prof c.x87 rd true else c₀.x87
      vec := { zmm := zmm'
               k := fun j => if loads 5 then w (prof.xOffset 5 + 8 * j.val) 8 64 else c₀.vec.k j
               mxcsr := if has 1 || has 2 then mxcsr else c₀.vec.mxcsr }
      pkru := if loads 9 then w (prof.xOffset 9) 4 32 else c₀.pkru }

/-- The x87 and vector state `FXRSTOR` (`w64`: with `REX.W`) loads from the 512-byte area `rd` on x87
state `x` and vector state `v` (SDM Vol. 2, "FXRSTOR"): the x87 state (`x87Load`), `MXCSR`, and
`XMM0`–`XMM15`, the rest of `ZMM0`–`ZMM15` and `ZMM16`–`ZMM31` kept. -/
def fxLoad (prof : Profile) (x : X87) (v : VecRegs) (rd : Nat → Byte) (w64 : Bool) : X87 × VecRegs :=
  let w (o n : Nat) (m : Nat) : BitVec m := ofBytesLE m ((List.range n).map fun k => rd (o + k))
  (x87Load prof x rd w64,
   { v with
     zmm := fun j => if j.val < 16 then
         (v.zmm j &&& ~~~(BitVec.allOnes 512 >>> 384)) ||| w (160 + 16 * j.val) 16 512
       else v.zmm j
     mxcsr := w 24 4 32 })

/-- `FXRSTOR` (`w64`: with `REX.W`) of the 512-byte area `rd` (16-byte aligned) on x87 state `x` and
vector state `v` (SDM Vol. 2, "FXRSTOR"; APM Vol. 5, "FXRSTOR"): `#GP` if `MXCSR` would be loaded with a
bit the processor does not support; not modelled on an Intel processor if `FSW`'s `ES`/`B` disagree
with its exceptions (`x87SummaryKnown`) or the control word's reserved bits are not known
(`x87FcwKnown`); otherwise the x87 state, `MXCSR` and `XMM0`–`XMM15` (`fxLoad`). -/
def fxrstor (prof : Profile) (x : X87) (v : VecRegs) (rd : Nat → Byte) (w64 : Bool) :
    XLoad (X87 × VecRegs) :=
  let mxcsr : BitVec 32 := ofBytesLE 32 ((List.range 4).map fun k => rd (24 + k))
  if !prof.mxcsrOk mxcsr then .gp
  else if !x87SummaryKnown prof rd then .notModelled "FXRSTOR: FSW.ES/B on Intel"
  else if !x87FcwKnown prof (ofBytesLE 16 [rd 0, rd 1]) then .notModelled "FXRSTOR: reserved FCW bits on Intel"
  else .ok (fxLoad prof x v rd w64)

end ZellicX86
