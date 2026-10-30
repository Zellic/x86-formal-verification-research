import ZellicX86.Spec.Semantics.Arith
import ZellicX86.Spec.Semantics.Move
import ZellicX86.Spec.Semantics.Bits
/-!
# Instruction semantics: `LOCK`-prefixed instructions

The decoder accepts `LOCK` only on the instructions the SDM lists as lockable, and only with a
memory destination (SDM Vol. 2, "LOCK"; otherwise `#UD`). Each such instruction replaces its
memory destination by one locked read-modify-write (`Prog.lockedRmw`: atomic for every other
agent, SDM Vol. 3A, 11.1.2 "Bus Locking"), whose function is the instruction's result as a
function of the old value; the flags and any register result follow from the old value as
without `LOCK`. For one thread the effect is that of the instruction without `LOCK`, except that
a locked access across a cache line is a split lock (`Prog.run`).

`XCHG` with a memory operand is locked with or without the prefix (`Sem.xchg`), and `CMPXCHG`
takes the prefix into account itself (`Sem.cmpxchg`).
-/
namespace ZellicX86
open Decode Prog

/-- A locked two-operand ALU instruction on memory destination `x` and source `s`: the memory
becomes `g f old y` atomically, and the flags are those `op` gives for `old` and `y` (`op` and
`g` compute the same result: the instruction's definition without `LOCK`). -/
def lockedAlu (i : Inst) (g : Rflags → BitVec i.opsz → BitVec i.opsz → BitVec i.opsz)
    (op : BitVec i.opsz → BitVec i.opsz → Rflags → Prog (BitVec i.opsz × Rflags)) : Prog Ctl :=
  match i.ops with
  | [.mem x, s] => do
    let y ← readOp i.opsz s
    let f ← readFlags
    let m ← memRef x
    let old ← lockedRmw m i.opsz (fun v => g f v y)
    let (_, f') ← op old y f
    writeFlags f'
    done
  | _ => formNotModelled i

/-- `LOCK ADD` (`Sem.add`). -/
def Sem.lockAdd (i : Inst) : Prog Ctl := lockedAlu i (fun _ x y => x + y) (addOp false)
/-- `LOCK ADC` (`Sem.adc`). -/
def Sem.lockAdc (i : Inst) : Prog Ctl :=
  lockedAlu i (fun f x y => x + y + (BitVec.ofBool f.cf).setWidth i.opsz) fun x y f => addOp f.cf x y f
/-- `LOCK SUB` (`Sem.sub`). -/
def Sem.lockSub (i : Inst) : Prog Ctl := lockedAlu i (fun _ x y => x - y) (subOp false)
/-- `LOCK SBB` (`Sem.sbb`). -/
def Sem.lockSbb (i : Inst) : Prog Ctl :=
  lockedAlu i (fun f x y => x - y - (BitVec.ofBool f.cf).setWidth i.opsz) fun x y f => subOp f.cf x y f
/-- `LOCK AND` (`Sem.and`). -/
def Sem.lockAnd (i : Inst) : Prog Ctl := lockedAlu i (fun _ x y => x &&& y) (logicOp (· &&& ·))
/-- `LOCK OR` (`Sem.or`). -/
def Sem.lockOr (i : Inst) : Prog Ctl := lockedAlu i (fun _ x y => x ||| y) (logicOp (· ||| ·))
/-- `LOCK XOR` (`Sem.xor`). -/
def Sem.lockXor (i : Inst) : Prog Ctl := lockedAlu i (fun _ x y => x ^^^ y) (logicOp (· ^^^ ·))

/-- `LOCK INC` (`Sem.inc`: `CF` unchanged). -/
def Sem.lockInc (i : Inst) : Prog Ctl :=
  match i.ops with
  | [.mem x] => do
    let f ← readFlags
    let m ← memRef x
    let old ← lockedRmw m i.opsz (· + 1)
    let (_, f') ← addOp false old 1 f
    writeFlags { f' with cf := f.cf }
    done
  | _ => formNotModelled i

/-- `LOCK DEC` (`Sem.dec`: `CF` unchanged). -/
def Sem.lockDec (i : Inst) : Prog Ctl :=
  match i.ops with
  | [.mem x] => do
    let f ← readFlags
    let m ← memRef x
    let old ← lockedRmw m i.opsz (· - 1)
    let (_, f') ← subOp false old 1 f
    writeFlags { f' with cf := f.cf }
    done
  | _ => formNotModelled i

/-- `LOCK NOT` (`Sem.not`: no flags). -/
def Sem.lockNot (i : Inst) : Prog Ctl :=
  match i.ops with
  | [.mem x] => do
    let m ← memRef x
    let _ ← lockedRmw m i.opsz (~~~ ·)
    done
  | _ => formNotModelled i

/-- `LOCK NEG` (`Sem.neg`). -/
def Sem.lockNeg (i : Inst) : Prog Ctl :=
  match i.ops with
  | [.mem x] => do
    let f ← readFlags
    let m ← memRef x
    let old ← lockedRmw m i.opsz (0 - ·)
    let (_, f') ← subOp false 0 old f
    writeFlags f'
    done
  | _ => formNotModelled i

/-- `LOCK XADD` (`Sem.xadd`): the memory becomes the sum atomically, the register the old
value. -/
def Sem.lockXadd (i : Inst) : Prog Ctl :=
  match i.ops with
  | [.mem x, s] => do
    let y ← readOp i.opsz s
    let f ← readFlags
    let m ← memRef x
    let old ← lockedRmw m i.opsz (· + y)
    let (_, f') ← addOp false old y f
    writeOp s old
    writeFlags f'
    done
  | _ => formNotModelled i

/-- `LOCK BTS`, `LOCK BTR`, `LOCK BTC` (`bitMem`). -/
def lockBit (prof : Profile) (ch : BitChange) (i : Inst) : Prog Ctl :=
  match i.ops with
  | [.mem x, o] => bitMem prof ch true i.opsz x o
  | _ => formNotModelled i

/-- Execute `LOCK`-prefixed instruction `i` (with `rip` advanced past it): the locked form of its
mnemonic. -/
def execLocked (prof : Profile) (i : Inst) : Prog Ctl :=
  match i.mn with
  | .add => Sem.lockAdd i | .adc => Sem.lockAdc i | .sub => Sem.lockSub i
  | .sbb => Sem.lockSbb i | .and => Sem.lockAnd i | .or => Sem.lockOr i | .xor => Sem.lockXor i
  | .inc => Sem.lockInc i | .dec => Sem.lockDec i | .not => Sem.lockNot i | .neg => Sem.lockNeg i
  | .xadd => Sem.lockXadd i | .xchg => Sem.xchg i | .cmpxchg => Sem.cmpxchg i
  | .bit .bts => lockBit prof .set i | .bit .btr => lockBit prof .reset i
  | .bit .btc => lockBit prof .complement i
  | _ => unmodelled (.form s!"lock {reprStr i.mn}")

end ZellicX86
