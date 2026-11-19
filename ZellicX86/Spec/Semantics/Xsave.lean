import ZellicX86.Spec.Semantics.Basic
/-!
# XSAVE-family instruction execution

Intel SDM Vol. 1 §§13.4–13.10, 13.13; Vol. 2D XSAVE, XSAVEC, XRSTOR;
AMD APM Vol. 2 §11.5, Vol. 4 the corresponding instruction entries.
The fixed 576-byte legacy/header prefix and full possible operated-component
footprint must be accessible, including components whose save
may be omitted by init optimization. An access fault in that footprint ends
explicitly not modelled; no fault-byte/order or partial-state policy is imposed.
-/
namespace ZellicX86
open Decode Prog

/-- RFBM: enabled XCR0 bits selected by the low 32 bits of EDX:EAX (SDM Vol. 1 §13.7).
Bits above bit 31 in either GPR are ignored, also with REX.W. -/
def xInstructionMask (prof : Profile) : Prog (BitVec 64) := do
  let a ← readReg 0
  let d ← readReg 2
  Pure.pure (((d.setWidth 32 |>.setWidth 64) <<< 32 ||| (a.setWidth 32 |>.setWidth 64)) &&& prof.xcr0.getD 0)

/-- The standard or compacted offset of an extended component on the executing
logical CPU (SDM Vol. 1 §13.4.3). `format` is RFBM for XSAVEC or XCOMP_BV for XRSTOR. -/
def xInstructionOffset (prof : Profile) (cpu : Nat) (format : BitVec 64) (compact : Bool)
    (i : Nat) : Nat :=
  if compact then xCompactOffset prof cpu format i
  else (prof.cpuid cpu 0xD (BitVec.ofNat 32 i)).ebx.toNat

/-- Regions of an operated held component which may be accessed (offset, byte count).
Legacy x87 comprises 0–23 and 32–159; SSE 24–31 and 160–415 (SDM Vol. 1 §13.4.1).
Standard AVX also accesses MXCSR. Extended allocated components use their full CPUID
extent, including init-optimized ones (§13.13). Compacted absent components have no
extended bytes allocated; restoring them initializes their state. -/
def xComponentRegions (prof : Profile) (cpu : Nat) (rfbm format : BitVec 64)
    (compact : Bool) : List (Nat × Nat) :=
  (if rfbm.getLsbD 0 then [(0,24),(32,128)] else []) ++
  (if rfbm.getLsbD 1 then [(24,8),(160,256)] else if !compact && rfbm.getLsbD 2 then [(24,8)] else []) ++
  ([2,5,6,7,9] : List Nat).filterMap fun i =>
    if rfbm.getLsbD i && (!compact || format.getLsbD i) then
      let used := match i with | 2 => 256 | 5 => 64 | 6 => 512 | 7 => 1024 | _ => 8
      some (xInstructionOffset prof cpu format compact i,
        max used (prof.cpuid cpu 0xD (BitVec.ofNat 32 i)).eax.toNat)
    else none

/-- Check every possible component access before execution or validation. Any failed
access stops NM rather than inventing an exception address or rolled-back state
(SDM Vol. 1 §13.13). The 64-byte header is checked by the caller as well. -/
def xCheckRegions (m : MemRef) (acc : Access) (regions : List (Nat × Nat)) : Prog Unit :=
  checkAccesses (regions.map fun (o,n) => (⟨m.addr + BitVec.ofNat 64 o,m.stack⟩,acc,n))
    (some (.feature "XSAVE-family access fault in possible state footprint"))

/-- Canonical-base and 64-byte alignment checks before any area access. Intel permits
GP or AC with alignment checking enabled; AMD specifies GP (SDM Vol. 2D,
XSAVE/XSAVEC/XRSTOR 64-bit exceptions; APM Vol. 4, corresponding exceptions). -/
def xAreaChecks (prof : Profile) (m : MemRef) : Prog Unit := do
  if !m.addr.canonical prof.feat.la57 then throw (if m.stack then .ss 0 else .gp 0)
  if m.addr.toNat % 64 != 0 then
    let f ← readFlags
    if prof.vendor = .intel && f.ac then
      let which ← choice 1
      throw (if which.val == 0 then .gp 0 else .ac)
    else throw (.gp 0)

/-- Read a sparse set of XSAVE component regions. Accesses have already passed
`xCheckRegions`; PKRU is unchanged until all reads finish (SDM Vol. 1 §13.5.7). -/
def xReadRegions (m : MemRef) (regions : List (Nat × Nat)) : Prog (List (Nat × List Byte)) :=
  regions.mapM fun (o,n) => do
    let v ← read ⟨m.addr + BitVec.ofNat 64 o,m.stack⟩ (8*n)
    Pure.pure (o,toBytesLE v n)

/-- Byte `o` from the read component regions; unused bytes default to 0. Every field
restored by `xrstorArea` is among these regions or the separately read header. -/
def xRegionByte (regions : List (Nat × List Byte)) (o : Nat) : Byte :=
  (regions.findSome? fun (p,bs) => if p ≤ o then bs[o-p]? else none).getD 0

/-- Write exactly the runs saved by XSAVE/XSAVEC, leaving unselected components,
software bytes 464–511 and header reserved bytes unchanged (SDM Vol. 1 §13.7/13.10). -/
def xWriteRegions (m : MemRef) (regions : List (Nat × List Byte)) : Prog Unit := do
  for (o,bs) in regions do
    write ⟨m.addr + BitVec.ofNat 64 o,m.stack⟩ (8*bs.length) (ofBytesLE (8*bs.length) bs)

/-- XSAVE (`compact=false`) or XSAVEC, with REX.W selecting 64-bit x87 pointers.
XSAVE preserves unrequested XSTATE_BV bits and every other header field. XSAVEC
writes XSTATE_BV anew and XCOMP_BV = bit 63 | RFBM, saving only non-init components;
nondefault MXCSR forces SSE saved when SSE is requested. Unsupported components or
an inaccessible possible footprint end NM. SDM Vol. 1 §§13.7,13.10,13.13; APM Vol. 4
XSAVE/XSAVEC and Vol. 2 §11.5.9. AMD standard requests involving x87 or AVX
without SSE are NM: APM Vol. 4 XSAVE selects MXCSR using bits 0/1, whereas
SDM §13.7 and Zen 4 select bits 1/2. No measurement overrides the manual. -/
def Sem.xsave (compact : Bool) (prof : Profile) (i : Inst) : Prog Ctl :=
  if prof.xcr0.isNone || (compact && !prof.feat.xsavec) then throw .ud else
  match i.ops with
  | [.mem mo] => do
    let m ← memRef mo
    xAreaChecks prof m
    let rfbm ← xInstructionMask prof
    if rfbm &&& ~~~xHeld != 0 then unmodelled (.feature "XSAVE unheld state component") else do
    if !compact && prof.vendor = .amd && !rfbm.getLsbD 1 &&
        (rfbm.getLsbD 0 || rfbm.getLsbD 2) then
      unmodelled (.feature "XSAVE: AMD MXCSR selection without SSE") else do
    let cpu ← choice (prof.cpus-1)
    let regions := xComponentRegions prof cpu.val rfbm rfbm compact
    xCheckRegions m .write ((0,576)::regions)
    let old ← if compact then Pure.pure (0 : BitVec 64) else read ⟨m.addr+512,m.stack⟩ 64
    let c ← readCpu
    let inuse ← undefined 64
    let bv := xsaveBv c c.pkru rfbm inuse
    let bv := if compact && rfbm.getLsbD 1 && c.vec.mxcsr != 0x1f80 then bv ||| 2 else bv
    let bytes := regions.foldl (fun n r => max n (r.1+r.2)) 576
    let rsv ← undefined (8*bytes)
    let offset := xInstructionOffset prof cpu.val rfbm compact
    let runs := xsaveRuns prof c.x87 c.vec c.pkru (if compact then bv else rfbm) rsv (i.opsz==64) offset
    let runs := runs.filter fun (o,_) => !(compact && (o==24 || o==28) && !bv.getLsbD 1)
    xWriteRegions m runs
    write ⟨m.addr+512,m.stack⟩ 64 (if compact then bv else (old &&& ~~~rfbm) ||| bv)
    if compact then write ⟨m.addr+520,m.stack⟩ 64 (rfbm ||| ((1 : BitVec 64) <<< 63))
    done
  | _ => formNotModelled i

/-- XRSTOR with standard/compacted header and 32/64-bit x87 pointer format. Read
all possible operated component bytes before validating/restoring; failure of an
access is explicitly NM. Header/MXCSR errors with accessible footprint raise GP.
The CPU snapshot is changed only in its selected x87/vector/PKRU fields, by
`xrstorArea` (SDM Vol. 1 §13.8/13.13; APM Vol. 4 XRSTOR). -/
def Sem.xrstor (prof : Profile) (i : Inst) : Prog Ctl :=
  if prof.xcr0.isNone then throw .ud else
  match i.ops with
  | [.mem mo] => do
    let m ← memRef mo
    xAreaChecks prof m
    let rfbm ← xInstructionMask prof
    if rfbm &&& ~~~xHeld != 0 then unmodelled (.feature "XRSTOR unheld state component") else do
    let cpu ← choice (prof.cpus-1)
    xCheckRegions m .read [(0,576)]
    let header ← read ⟨m.addr+512,m.stack⟩ 512
    let format : BitVec 64 := header.extractLsb' 64 64
    let regions := xComponentRegions prof cpu.val rfbm format (format.getLsbD 63)
    xCheckRegions m .read regions
    let image ← xReadRegions m regions
    let rd := xRegionByte ((512,toBytesLE header 64)::image)
    let c ← readCpu
    match xrstorArea prof cpu.val c rd rfbm (i.opsz==64) with
    | .gp => throw (.gp 0)
    | .notModelled w => unmodelled (.feature w)
    | .ok c' => writeCpu c'; done
  | _ => formNotModelled i

end ZellicX86
