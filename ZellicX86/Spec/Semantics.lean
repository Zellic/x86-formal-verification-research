import ZellicX86.Spec.Semantics.Move
import ZellicX86.Spec.Semantics.Arith
import ZellicX86.Spec.Semantics.Control
import ZellicX86.Spec.Semantics.Sse
import ZellicX86.Spec.Semantics.SseFloat
import ZellicX86.Spec.Semantics.String
import ZellicX86.Spec.Semantics.Bits
import ZellicX86.Spec.Semantics.Avx
import ZellicX86.Spec.Semantics.Lock
import ZellicX86.Spec.Semantics.X87
/-!
# Instruction semantics

What each decoded instruction does, as an instruction program (`Spec/Machine.lean`), one module per family of
instructions under `Spec/Semantics/` (`Move`, `Arith`, `Bits`, `Control`, `Sse`, `SseFloat`, `Avx`, `X87`, `String`,
`Lock`), with the helpers they share in `Basic`. Each instruction, or each family of instructions that differ only in
element size (`Sem.vpadd e`), has one definition `Sem.<mnemonic>`, which keeps each definition small and separately
readable; a few helpers shared by several of them also carry the `Sem.` prefix (`Sem.dup`, `Sem.zeroUpper`,
`Sem.zeroAll`, `Sem.vzeroCheck`), and the string instructions share `execString`. `exec` sends a `LOCK`-prefixed
instruction to `execLocked` (the decoder admits `LOCK` only where it is valid) and otherwise chooses the definition by
mnemonic, the SSE, SSE floating-point, bit, AVX and x87 instructions through their family's table (`execSse`,
`execFp`, `execBits`, `execAvx`, `execX87`). A mnemonic without a definition stops with `notModelled`. The decoder
gives a repeat prefix (`Inst.rep`) only to string instructions.
-/
namespace ZellicX86
open Decode Prog

/-- Execute instruction `i` on processor `prof`, with `rip` already advanced past it: the
definition of its mnemonic. -/
def exec (prof : Profile) (i : Inst) : Prog Ctl :=
  let feat := prof.feat
  -- `LOCK` reaches only lockable instructions with a memory destination (the decoder)
  if i.lock then execLocked prof i else
  match i.mn with
  | .add => Sem.add i | .or => Sem.or i | .adc => Sem.adc i | .sbb => Sem.sbb i
  | .and => Sem.and i | .sub => Sem.sub i | .xor => Sem.xor i | .cmp => Sem.cmp i
  | .inc => Sem.inc i | .dec => Sem.dec i | .not => Sem.not i | .neg => Sem.neg i
  | .mul => Sem.mul i | .imul => Sem.imul i | .div => Sem.div i | .idiv => Sem.idiv i
  | .test => Sem.test i
  | .rol => Sem.rol prof i | .ror => Sem.ror prof i | .shl => Sem.shl prof i | .shr => Sem.shr prof i
  | .sar => Sem.sar prof i
  | .mov => Sem.mov i | .movsxd => Sem.movsxd i | .movzx => Sem.movzx i | .movsx => Sem.movsx i
  | .lea => Sem.lea i | .xchg => Sem.xchg i | .bswap => Sem.bswap i
  | .push => Sem.push i | .pop => Sem.pop i | .leave => Sem.leave i
  | .call => Sem.call prof i | .jmp => Sem.jmp feat i | .ret => Sem.ret feat i
  | .jcc c => Sem.jcc feat c i | .setcc c => Sem.setcc c i | .cmovcc c => Sem.cmovcc c i
  | .jrcxz => Sem.jrcxz feat i
  | .loop zf => Sem.loop feat zf i
  | .cbw => Sem.cbw i | .cwd => Sem.cwd i
  | .nop => Sem.nop i | .endbr64 => Sem.endbr64 i | .hlt => Sem.hlt i | .int3 => Sem.int3 i
  | .ud2 => Sem.ud2 i | .syscall => Sem.syscall i | .cpuid => Sem.cpuid prof i
  | .xgetbv => Sem.xgetbv prof i
  | .str m => execString m i
  | .bit m => execBits prof m i
  | .sse m => execSse prof m i
  | .fp m => execFp prof m i
  | .avx m => execAvx prof m i
  | .x87 m => execX87 prof m i
  | .cmpxchg => Sem.cmpxchg i | .xadd => Sem.xadd i
  | .rdtsc => Sem.rdtsc i | .rdtscp => Sem.rdtscp prof i
  | .movbe => Sem.movbe i | .prefetch _ => Sem.prefetch i | .crc32 => Sem.crc32 i
  | .lfence => Sem.lfence i | .sfence => Sem.sfence i | .mfence => Sem.mfence i
  | .rdssp => Sem.rdssp i | .incssp => Sem.incssp i | .xtest => Sem.xtest i
  | .rcl | .rcr | .pause => unmodelled (.form (reprStr i.mn))

end ZellicX86
