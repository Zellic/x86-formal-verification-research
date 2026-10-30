import ZellicX86.Spec.Request
import ZellicX86.Spec.Xsave
import ZellicX86.Spec.Outcome
/-!
# Instruction programs

The semantics of an instruction is a program (`Prog`) of primitive steps (`Op`): register and flag
accesses, memory loads and stores in program order, requests for values the manuals leave
undefined, and the ways an instruction can stop (an exception, or something not modelled). A
program is a step and what follows from its result, like a request program (`Req`).

The memory accesses are data: an interpretation sees each one, in order, with its address
and width. `Prog.run` is the interpretation for one thread: each instruction is atomic, and
its memory accesses happen in order. An exception discards every effect of the instruction
(x86 exceptions are precise: SDM Vol. 3A, 7.5 "Exception Classifications"), so a store that
faults on a later byte writes none; what a `#XM` leaves in `MXCSR` is part of the exception
(`Exception.xm`). Faults come in program order too: of two accesses of one
instruction that would both fault (`PUSH m`, `POP m`, `CALL m`), the first raises its exception.
This order is taken from observed behaviour on an AMD Zen 4 only (every such pair observed: two
page faults, a page fault and a non-canonical address); no Intel processor was tested, and the
manuals do not order the two faults (AMD's `CALL (Near)` operation reads a memory target before
the push, without saying which fault comes first). Where an instruction's faults are known to come
otherwise, its program says so (`checkAll` for `MOVS` and `CMPS`, `CALL` to a non-canonical
target). A
multi-threaded interpretation can interleave other agents between accesses. Locked
read-modify-write (`rmw`) and fences are single steps of their own, so such an
interpretation keeps them atomic and ordered (SDM Vol. 3A, 11.1.2 "Bus Locking", 11.2
"Memory Ordering").
-/
namespace ZellicX86

/-- A memory reference of an instruction: the linear address and whether the reference uses
the stack segment: a memory operand whose base register is `rsp` or `rbp` without an `FS` or `GS`
prefix (`memRef`), and the implicit stack accesses of `PUSH`, `POP`, `CALL`, `RET` and `LEAVE`. A
non-canonical address raises `#SS(0)` in a stack reference and `#GP(0)` in any other (SDM Vol. 1,
3.3.7.1 "Canonical Addressing"; Vol. 3A, 7.15, "Interrupt 12" and "Interrupt 13"). -/
structure MemRef where
  addr : Addr
  stack : Bool

/-- Memory-ordering instructions (SDM Vol. 3A, 11.2.5 "Strengthening or Weakening the
Memory-Ordering Model"; 11.3 "Serializing Instructions"). -/
inductive Fence
  | load
  | store
  | full
  | serializing
  deriving DecidableEq, Repr

/-- A primitive step of an instruction program: a register or flag access, a memory access, a
check, a fence, a request for a value the manuals leave open, or a stop. -/
inductive Op
  | getReg (r : Reg)
  | setReg (r : Reg) (v : BitVec 64)
  /-- The address of the next instruction: `rip` has already been advanced past the
  current one (SDM Vol. 1, 3.5 "Instruction Pointer"). -/
  | getRip
  | setRip (v : Addr)
  | getFlags
  | setFlags (f : Rflags)
  /-- The `FS` base (`fs = true`) or `GS` base. -/
  | getSegBase (fs : Bool)
  /-- The kernel's state of the thread (whether `CPUID` faults). -/
  | getThread
  /-- Vector register `ZMMn`, all 512 bits (`XMMn` and `YMMn` are its low 128 and 256). -/
  | getZmm (n : Fin 32)
  | setZmm (n : Fin 32) (v : BitVec 512)
  /-- Opmask register `kn` (SDM Vol. 1, 15.1.3). -/
  | getK (n : Fin 8)
  | setK (n : Fin 8) (v : BitVec 64)
  /-- `MXCSR` (SDM Vol. 1, 10.2.3). -/
  | getMxcsr
  | setMxcsr (v : BitVec 32)
  /-- The x87 state (SDM Vol. 1, 8.1): registers, control, status, tags, pointers. -/
  | getX87
  | setX87 (x : X87)
  /-- Load `w / 8` bytes at `m`. `acc` is `write` for the read half of an instruction that
  then writes the same operand: such a read already needs write permission (a
  read-for-ownership, SDM Vol. 3A, 5.7, error-code bit W). -/
  | load (m : MemRef) (w : Nat) (acc : Access)
  /-- Store `v` (`w / 8` bytes) at `m`. -/
  | store (m : MemRef) (w : Nat) (v : BitVec w)
  /-- Load the bytes `i < n` at `m` for which bit `i` of `sel` is set; the others read as 0.
  Only the selected bytes are accessed: an EVEX load under an opmask suppresses the faults of
  masked-off elements (SDM Vol. 2, 2.8, Tables 2-46 and 2-51, "If fault suppression not set"). -/
  | loadSel (m : MemRef) (n : Nat) (sel : BitVec n) (acc : Access)
  /-- Store byte `i` of `v` at `m.addr + i` for each `i < n` for which bit `i` of `sel` is set;
  only those bytes are accessed (an EVEX store under an opmask). -/
  | storeSel (m : MemRef) (n : Nat) (sel : BitVec n) (v : BitVec (8 * n))
  /-- Locked read-modify-write: atomically replace the `w / 8` bytes at `m` by `f` of their
  value; the result is the old value. -/
  | rmw (m : MemRef) (w : Nat) (f : BitVec w → BitVec w)
  /-- Continue if `m`'s address is a multiple of `n`; otherwise the operand is misaligned for
  the access `acc` of `b` bytes that follows, which raises `#GP(0)`. With `mm` (the operand of a
  legacy SSE instruction other than an aligned move, on a processor that supports AMD's misaligned
  SSE mode, `Profile.misalignSse`) a misaligned operand is also allowed while bit 17 of `MXCSR` is
  set (`MXCSR.MM`; APM Vol. 1, 4.2.2 "Misaligned Exception Mask", 4.3.2 "Data Alignment":
  `MOVAPS`, `MOVDQA`, `MOVNTDQ`, ... are checked whatever `MM`). -/
  | checkAligned (m : MemRef) (n : Nat) (acc : Access) (b : Nat) (mm : Bool)
  /-- Continue if none of the accesses `as` (reference, kind, bytes) faults; otherwise raise the
  exception of one that does. For an instruction with several memory operands (`MOVS`, `CMPS`)
  this comes before the accesses themselves: which operand's fault is reported when more than
  one faults is not specified (SDM Vol. 3A, 7.9, after Table 7-2; AMD APM Vol. 2, 8.5,
  Table 8-9, one priority class), and an AMD Zen 4 reports the source's for `MOVS` and
  `REPE CMPS` but the destination's for `CMPS` without a prefix. -/
  | checkAll (as : List (MemRef × Access × Nat))
  | fence (f : Fence)
  /-- A `w`-bit value the manuals leave undefined. -/
  | choose (w : Nat)
  /-- One of `n + 1` alternatives the processor may take where the manuals leave the choice open (which of several
  faults it reports, say). -/
  | pick (n : Nat)
  /-- The time-stamp counter (`Request.tsc`). -/
  | tsc
  /-- XCR0 AND XINUSE for the enabled, held state components (`Cpu.xInuseRequired`,
  `Request.xinuse`; SDM Vol. 1, 13.6). -/
  | xinuse (enabled : BitVec 64)
  | raise (e : Exception)
  | notModelled (what : NotModelled)

/-- What a step gives the rest of the program: the value read, or nothing; a stop gives nothing
to continue with. -/
def Op.Ret : Op → Type
  | .getReg _ => BitVec 64
  | .getRip => Addr
  | .getFlags => Rflags
  | .getSegBase _ => Addr
  | .getThread => ThreadK
  | .getZmm _ => BitVec 512
  | .getK _ => BitVec 64
  | .getMxcsr => BitVec 32
  | .getX87 => X87
  | .load _ w _ => BitVec w
  | .loadSel _ n _ _ => BitVec (8 * n)
  | .rmw _ w _ => BitVec w
  | .choose w => BitVec w
  | .pick n => Fin (n + 1)
  | .tsc => BitVec 64
  | .xinuse _ => BitVec 64
  | .raise _ | .notModelled _ => Empty
  | .setReg .. | .setRip _ | .setFlags _ | .setZmm .. | .setK .. | .setMxcsr _ | .setX87 _ | .store ..
  | .storeSel ..
  | .checkAligned .. | .checkAll _ | .fence _ => Unit

/-- An instruction program returning `α`: steps, each continued with what it gives. -/
inductive Prog (α : Type) where
  | pure (a : α)
  | op (o : Op) (k : o.Ret → Prog α)

/-- Sequencing. -/
def Prog.bind {α β : Type} : Prog α → (α → Prog β) → Prog β
  | .pure a, f => f a
  | .op o k, f => .op o fun v => (k v).bind f

/-- Instruction programs form a monad (do-notation in `Spec/Semantics/`). -/
instance : Monad Prog where
  pure := .pure
  bind := Prog.bind

namespace Prog
/-! The primitive steps as monadic operations. -/
/-- Read general register `r`. -/
def readReg (r : Reg) : Prog (BitVec 64) := .op (.getReg r) .pure
/-- Write general register `r`. -/
def writeReg (r : Reg) (v : BitVec 64) : Prog Unit := .op (.setReg r v) .pure
/-- The address of the next instruction. -/
def readRip : Prog Addr := .op .getRip .pure
/-- Continue at `v`. -/
def writeRip (v : Addr) : Prog Unit := .op (.setRip v) .pure
/-- Read `RFLAGS`. -/
def readFlags : Prog Rflags := .op .getFlags .pure
/-- Write `RFLAGS`. -/
def writeFlags (f : Rflags) : Prog Unit := .op (.setFlags f) .pure
/-- The `FS` (`fs = true`) or `GS` base. -/
def segBase (fs : Bool) : Prog Addr := .op (.getSegBase fs) .pure
/-- The kernel's state of the thread. -/
def readThread : Prog ThreadK := .op .getThread .pure
/-- Read vector register `ZMMn`. -/
def readZmm (n : Fin 32) : Prog (BitVec 512) := .op (.getZmm n) .pure
/-- Write vector register `ZMMn`. -/
def writeZmm (n : Fin 32) (v : BitVec 512) : Prog Unit := .op (.setZmm n v) .pure
/-- Read opmask register `kn`. -/
def readK (n : Fin 8) : Prog (BitVec 64) := .op (.getK n) .pure
/-- Write opmask register `kn`. -/
def writeK (n : Fin 8) (v : BitVec 64) : Prog Unit := .op (.setK n v) .pure
/-- Read `MXCSR`. -/
def readMxcsr : Prog (BitVec 32) := .op .getMxcsr .pure
/-- Write `MXCSR`. -/
def writeMxcsr (v : BitVec 32) : Prog Unit := .op (.setMxcsr v) .pure
/-- Read the x87 state. -/
def readX87 : Prog X87 := .op .getX87 .pure
/-- Write the x87 state. -/
def writeX87 (x : X87) : Prog Unit := .op (.setX87 x) .pure
/-- Load the bytes of `n` at `m` that `sel` selects (the others 0). -/
def readSel (m : MemRef) (n : Nat) (sel : BitVec n) (acc : Access := .read) : Prog (BitVec (8 * n)) :=
  .op (.loadSel m n sel acc) .pure
/-- Store the bytes of `v` that `sel` selects at `m`. -/
def writeSel (m : MemRef) (n : Nat) (sel : BitVec n) (v : BitVec (8 * n)) : Prog Unit :=
  .op (.storeSel m n sel v) .pure
/-- Load `w / 8` bytes at `m`. -/
def read (m : MemRef) (w : Nat) (acc : Access := .read) : Prog (BitVec w) :=
  .op (.load m w acc) .pure
/-- Store `v` at `m`. -/
def write (m : MemRef) (w : Nat) (v : BitVec w) : Prog Unit := .op (.store m w v) .pure
/-- Atomically replace the `w / 8` bytes at `m` by `f` of their value; the old value. -/
def lockedRmw (m : MemRef) (w : Nat) (f : BitVec w → BitVec w) : Prog (BitVec w) :=
  .op (.rmw m w f) .pure
/-- `#GP(0)` unless `m`'s address is a multiple of `n` (for an access `acc` of `b` bytes), or,
with `mm`, `MXCSR.MM` is set (`Op.checkAligned`). -/
def alignedTo (m : MemRef) (n : Nat) (acc : Access) (b : Nat) (mm : Bool) : Prog Unit :=
  .op (.checkAligned m n acc b mm) .pure
/-- Raise the exception of one of the accesses `as` that faults, if any. -/
def checkAccesses (as : List (MemRef × Access × Nat)) : Prog Unit := .op (.checkAll as) .pure
/-- A `w`-bit value the manuals leave undefined. -/
def undefined (w : Nat) : Prog (BitVec w) := .op (.choose w) .pure
/-- One of `n + 1` alternatives. -/
def choice (n : Nat) : Prog (Fin (n + 1)) := .op (.pick n) .pure
/-- The time-stamp counter. -/
def readTsc : Prog (BitVec 64) := .op .tsc .pure
/-- Order memory accesses and instruction execution as fence `f` does. -/
def fenceOp (f : Fence) : Prog Unit := .op (.fence f) .pure
/-- An undefined flag. -/
def undefinedBit : Prog Bool := do let v ← undefined 1; Pure.pure (v.getLsbD 0)
/-- Raise exception `e`. -/
def throw {α : Type} (e : Exception) : Prog α := .op (.raise e) Empty.elim
/-- Stop: `what` is not modelled. -/
def unmodelled {α : Type} (what : NotModelled) : Prog α := .op (.notModelled what) Empty.elim
end Prog

/-- How one interpreted instruction ends. -/
inductive Result (α : Type) where
  | ok (a : α) (s : State)
  | exception (e : Exception)
  | notModelled (what : NotModelled)

/-- The addresses `a`, `a + 1`, ..., `a + n - 1` (wrapping). -/
def byteAddrs (a : Addr) (n : Nat) : List Addr := (List.range n).map a.add

/-- The first address, in increasing order, of each page on which access `acc` to the bytes
`addrs` faults, with the reason. -/
def faultingPages (feat : Features) (pkru : BitVec 32) (mem : Memory) (acc : Access) :
    List Addr → List (Addr × AccessFault)
  | [] => []
  | a :: as =>
    let rest := faultingPages feat pkru mem acc as
    match mem.check feat pkru acc a with
    | none => rest
    | some f => (a, f) :: rest.filter fun x => pageOf x.1 ≠ pageOf a

/-- Check access `acc` to the bytes `addrs` of a reference that uses the stack segment if
`stack`, for one thread with state `s`: the exception the access raises, or `none`. A byte that is
not canonical raises `#SS(0)` or `#GP(0)` (`MemRef`), before any page is checked, also when the
access only crosses into the non-canonical range; then each page is checked (`Memory.check`), and a
fault raises `#PF` at the first byte of the access on the faulting page (what the operating system
does with it, such as growing a stack, is its handling of the exception). An access with alignment
checking enabled (`RFLAGS.AC = 1`; Linux sets `CR0.AM`, so `#AC` is then possible, SDM Vol. 3A, 7.15
"Interrupt 17") stops with `notModelled`.

When the access faults on two pages, which one the processor reports is not specified; it
is a `pick` (an AMD Zen 4 reports the lower). -/
def checkBytes (feat : Features) (s : State) (stack : Bool) (addrs : List Addr) (acc : Access) :
    Req (Option (Except NotModelled Exception)) :=
  if s.cpu.rflags.ac then Pure.pure (some (.error (.feature "alignment check (RFLAGS.AC)")))
  else if addrs.any (fun a => !a.canonical feat.la57) then
    Pure.pure (some (.ok (if stack then .ss 0 else .gp 0)))
  else
    match faultingPages feat s.cpu.pkru s.proc.mm.mem acc addrs with
    | [] => Pure.pure none
    | [(a, f)] => Pure.pure (some (.ok (.pf a acc (f = .pkey))))
    | fs => do
      let i ← Req.request (.pick (fs.length - 1))
      match fs[i.val]? with
      | some (a, f) => Pure.pure (some (.ok (.pf a acc (f = .pkey))))
      -- unreachable: the pick is below the list's length
      | none => Pure.pure (some (.error (.feature "fault selection")))

/-- Check access `acc` of `n` bytes at `m` (`checkBytes`). -/
def checkAccess (feat : Features) (s : State) (m : MemRef) (acc : Access) (n : Nat) :
    Req (Option (Except NotModelled Exception)) :=
  checkBytes feat s m.stack (byteAddrs m.addr n) acc

/-- The addresses `a + i` for `i < n` with bit `i` of `sel` set. -/
def selAddrs (a : Addr) (n : Nat) (sel : BitVec n) : List Addr :=
  (List.range n).filterMap fun i => if sel.getLsbD i then some (a.add i) else none

/-- The results of `checkAccess` for each access of `as` that does not pass, in order. -/
def checkEach (feat : Features) (s : State) :
    List (MemRef × Access × Nat) → Req (List (Except NotModelled Exception))
  | [] => Pure.pure []
  | (m, acc, n) :: as => do
    let r ← checkAccess feat s m acc n
    let rs ← checkEach feat s as
    Pure.pure (r.toList ++ rs)

/-- Read `n` bytes at `a` (after `checkAccess`). -/
def readBytes (mem : Memory) (a : Addr) (n : Nat) : List Byte :=
  (byteAddrs a n).map mem.readByte

/-- Write bytes `bs` at `a` (after `checkAccess`). -/
def writeBytes (mem : Memory) (a : Addr) (bs : List Byte) : Memory :=
  (List.zip (byteAddrs a bs.length) bs).foldl (fun m (x, b) => m.writeByte x b) mem

/-- The `n` bytes at `a`, those `sel` does not select as 0 (after `checkBytes` of the selected
ones). -/
def readSelBytes (mem : Memory) (a : Addr) (n : Nat) (sel : BitVec n) : List Byte :=
  (List.range n).map fun i => if sel.getLsbD i then mem.readByte (a.add i) else 0

/-- Write byte `i` of `bs` at `a + i` where bit `i` of `sel` is set (after `checkBytes`). -/
def writeSelBytes (mem : Memory) (a : Addr) (n : Nat) (sel : BitVec n) (bs : List Byte) : Memory :=
  ((List.range n).zip bs).foldl
    (fun m (i, b) => if sel.getLsbD i then m.writeByte (a.add i) b else m) mem

/-- `s` with memory `mem`. -/
def State.withMem (s : State) (mem : Memory) : State :=
  { s with proc.mm.mem := mem }

/-- `s` with the position and status flags of the open file description `f` set to `p`. -/
def State.setFilePos (s : State) (f : OpenFile) (p : FilePos) : State :=
  { s with proc.opens.pos := fun g => if g = f then p else s.proc.opens.pos g }

/-- `s` with processor state changed by `f`. -/
def State.modCpu (s : State) (f : Cpu → Cpu) : State := { s with cpu := f s.cpu }

/-- Run instruction program `p` for one thread from state `s`, with CPU features `feat`, under the
kernel's treatment of split locks `sl` (`LinuxBoot.splitLock`). -/
def Prog.run {α : Type} (feat : Features) (sl : SplitLock) : Prog α → State → Req (Result α)
  | .pure a, s => Pure.pure (.ok a s)
  | .op (.getReg r) k, s => (k (s.cpu.gpr.get r)).run feat sl s
  | .op (.setReg r v) k, s =>
    (k ()).run feat sl (s.modCpu fun c => { c with gpr := c.gpr.set r v })
  | .op .getRip k, s => (k s.cpu.rip).run feat sl s
  | .op (.setRip v) k, s => (k ()).run feat sl (s.modCpu fun c => { c with rip := v })
  | .op .getFlags k, s => (k s.cpu.rflags).run feat sl s
  | .op (.setFlags f) k, s => (k ()).run feat sl (s.modCpu fun c => { c with rflags := f })
  | .op (.getSegBase fs) k, s =>
    (k (if fs then s.cpu.seg.fsBase else s.cpu.seg.gsBase)).run feat sl s
  | .op .getThread k, s => (k s.thread).run feat sl s
  | .op (.getZmm n) k, s => (k (s.cpu.vec.zmm n)).run feat sl s
  | .op (.setZmm n v) k, s =>
    (k ()).run feat sl
      (s.modCpu fun c => { c with vec := { c.vec with zmm := withZmm c.vec.zmm n v } })
  | .op (.getK n) k, s => (k (s.cpu.vec.k n)).run feat sl s
  | .op (.setK n v) k, s =>
    (k ()).run feat sl (s.modCpu fun c => { c with vec := { c.vec with k := withK c.vec.k n v } })
  | .op .getMxcsr k, s => (k s.cpu.vec.mxcsr).run feat sl s
  | .op (.setMxcsr v) k, s =>
    (k ()).run feat sl (s.modCpu fun c => { c with vec := { c.vec with mxcsr := v } })
  | .op .getX87 k, s => (k s.cpu.x87).run feat sl s
  | .op (.setX87 x) k, s => (k ()).run feat sl (s.modCpu fun c => { c with x87 := x })
  | .op (.load m w acc) k, s => do
    match ← checkAccess feat s m acc (w / 8) with
    | some (.ok e) => Pure.pure (.exception e)
    | some (.error nm) => Pure.pure (.notModelled nm)
    | none => (k (ofBytesLE w (readBytes s.proc.mm.mem m.addr (w / 8)))).run feat sl s
  | .op (.store m w v) k, s => do
    match ← checkAccess feat s m .write (w / 8) with
    | some (.ok e) => Pure.pure (.exception e)
    | some (.error nm) => Pure.pure (.notModelled nm)
    | none =>
      (k ()).run feat sl (s.withMem (writeBytes s.proc.mm.mem m.addr (toBytesLE v (w / 8))))
  | .op (.loadSel m n sel acc) k, s => do
    match ← checkBytes feat s m.stack (selAddrs m.addr n sel) acc with
    | some (.ok e) => Pure.pure (.exception e)
    | some (.error nm) => Pure.pure (.notModelled nm)
    | none => (k (ofBytesLE (8 * n) (readSelBytes s.proc.mm.mem m.addr n sel))).run feat sl s
  | .op (.storeSel m n sel v) k, s => do
    match ← checkBytes feat s m.stack (selAddrs m.addr n sel) .write with
    | some (.ok e) => Pure.pure (.exception e)
    | some (.error nm) => Pure.pure (.notModelled nm)
    | none =>
      (k ()).run feat sl (s.withMem (writeSelBytes s.proc.mm.mem m.addr n sel (toBytesLE v n)))
  | .op (.rmw m w f) k, s => do
    -- A locked access that crosses a 64-byte cache line is a split lock (`SplitLock`): atomic as
    -- any other, or `#AC` before the instruction, which with the access's own faults is in one class
    -- of unordered faults (SDM Vol. 3A, 7.9, Table 7-2; APM Vol. 2, 8.5, Table 8-9), so which one is
    -- raised is a `pick`; or a trap after it, not modelled.
    if (m.addr.toNat % 64) + w / 8 > 64 ∧ sl ≠ .atomic then
      if sl = .trap then Pure.pure (.notModelled (.feature "split lock under bus-lock detection")) else
      match ← checkAccess feat s m .write (w / 8) with
      | none => Pure.pure (.exception .ac)
      | some (.error nm) => Pure.pure (.notModelled nm)
      | some (.ok e) => do
        let i ← Req.request (.pick 1)
        Pure.pure (.exception (if i.val = 0 then .ac else e))
    else
    match ← checkAccess feat s m .write (w / 8) with
    | some (.ok e) => Pure.pure (.exception e)
    | some (.error nm) => Pure.pure (.notModelled nm)
    | none =>
      let old := ofBytesLE w (readBytes s.proc.mm.mem m.addr (w / 8))
      (k old).run feat sl (s.withMem (writeBytes s.proc.mm.mem m.addr (toBytesLE (f old) (w / 8))))
  | .op (.checkAligned m n acc b mm) k, s =>
    if m.addr.toNat % n = 0 ∨ (mm ∧ s.cpu.vec.mxcsr.getLsbD 17) then (k ()).run feat sl s else do
    -- The misaligned operand's `#GP(0)` and a fault of the access itself are not ordered:
    -- Intel leaves the priority of faults during execution open (SDM Vol. 3A, 7.9, after
    -- Table 7-2), AMD puts `#GP` and data page faults in one class (APM Vol. 2, 8.5,
    -- Table 8-9, priority 7). Which one is raised is a `pick`.
    match ← checkAccess feat s m acc b with
    | none => Pure.pure (.exception (.gp 0))
    | some (.error nm) => Pure.pure (.notModelled nm)
    | some (.ok e) => do
      let i ← Req.request (.pick 1)
      Pure.pure (.exception (if i.val = 0 then .gp 0 else e))
  | .op (.checkAll as) k, s => do
    match ← checkEach feat s as with
    | [] => (k ()).run feat sl s
    | [.ok e] => Pure.pure (.exception e)
    | rs =>
      -- an access that needs something not modelled makes the instruction not modelled;
      -- among faults, which one is raised is a `pick`
      match rs.findSome? (fun | .error nm => some nm | .ok _ => none) with
      | some nm => Pure.pure (.notModelled nm)
      | none => do
        let i ← Req.request (.pick (rs.length - 1))
        match rs[i.val]? with
        | some (.ok e) => Pure.pure (.exception e)
        -- unreachable: the pick is below the list's length
        | _ => Pure.pure (.notModelled (.feature "fault selection"))
  | .op (.fence _) k, s => (k ()).run feat sl s
  | .op (.choose w) k, s => do
    let v ← Req.request (.undefined w)
    (k v).run feat sl s
  | .op (.pick n) k, s => do
    let i ← Req.request (.pick n)
    (k i).run feat sl s
  | .op .tsc k, s => do
    let v ← Req.request .tsc
    (k v).run feat sl s
  | .op (.xinuse enabled) k, s => do
    let v ← Req.request (.xinuse (s.cpu.xInuseRequired enabled))
    (k (enabled &&& v.val)).run feat sl s
  | .op (.raise e) _, _ => Pure.pure (.exception e)
  | .op (.notModelled w) _, _ => Pure.pure (.notModelled w)

end ZellicX86
