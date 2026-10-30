import ZellicX86.Spec.Memory
import ZellicX86.Spec.Signal
/-!
# Exceptions, outcomes and observable events

An instruction either completes, raises an architectural exception, enters the kernel with
`syscall`, or hits something the model does not implement. The exception is kept as its own
value next to its Linux consequence (a signal), so theorems can say "no `#PF`" as well as
"not killed by `SIGSEGV`". "Not modelled" is always its own outcome, never a fault or a
no-op.
-/
namespace ZellicX86

/-- An exception an instruction can raise in 64-bit user mode (SDM Vol. 3A, 7.15,
Table 7-1). `#OF` and `#BR` cannot occur in 64-bit mode (`INTO` and `BOUND` are invalid);
`#DF`, `#TS`, `#NP`, `#MC` and `#VE` are not raised by user instructions in the modelled
environment. -/
inductive Exception
  /-- `#DE`, divide error. -/
  | de
  /-- `#DB`, debug. -/
  | db
  /-- `#BP`, breakpoint (`INT3`). -/
  | bp
  /-- `#UD`, invalid opcode. -/
  | ud
  /-- `#NM`, device not available. -/
  | nm
  /-- `#SS(err)`, stack-segment fault: a non-canonical address in a stack reference. -/
  | ss (err : BitVec 16)
  /-- `#GP(err)`, general protection. -/
  | gp (err : BitVec 16)
  /-- `#PF`, page fault at linear address `addr` for an access of kind `acc`; `pkey` is the
  error code's PK bit: the page's protection key forbids the access (`AccessFault.pkey`). The error
  code's P bit depends on the kernel's page tables and is not recorded (SDM Vol. 3A, 5.7). -/
  | pf (addr : Addr) (acc : Access) (pkey : Bool)
  /-- `#MF`, x87 floating-point error. -/
  | mf
  /-- `#AC(0)`, alignment check. -/
  | ac
  /-- `#XM`, SIMD floating-point exception, leaving `MXCSR` as `mxcsr`: the faulting instruction has
  set the flags of the conditions it detected and changed nothing else (SDM Vol. 1, 11.5.3.2; APM
  Vol. 1, 4.10.4.2). -/
  | xm (mxcsr : BitVec 32)
  /-- `#CP(err)`, control-protection exception. -/
  | cp (err : BitVec 16)
  deriving DecidableEq, Repr

/-- What the model does not implement. Reaching it ends the run with outcome
`notModelled`, carrying enough to identify what was hit. -/
inductive NotModelled
  /-- A valid encoding the decoder does not implement: opcode map (0 one-byte, `0x0F`,
  `0x0F38`, `0x0F3A`, `0xC4` VEX, `0x62` EVEX, `0xD5` REX2) and opcode byte. -/
  | encoding (map : Nat) (opcode : Nat)
  /-- A decoded instruction whose semantics is not implemented for these operands,
  operand size or prefixes (named by its mnemonic). -/
  | form (mnemonic : String)
  /-- A system call the model does not implement (its number, `rax`). -/
  | syscall (nr : BitVec 64)
  /-- Delivery of a signal to a handler the process installed, where the model does not deliver
  (a signal from outside, one `write` sends, the `SIGSEGV` of a failed `rseq` update at a return to
  user mode, the signal of `#DB`, `#MF` or `#CP`). -/
  | signalHandler (sig : Signal)
  /-- A processor or kernel feature the model does not cover, by name. -/
  | feature (what : String)
  deriving Repr

/-- Why a process was killed by a signal. -/
inductive KillCause
  /-- The signal the kernel sent because an instruction raised exception `e`. -/
  | exception (e : Exception)
  /-- A signal sent from outside the process. -/
  | external
  /-- A signal the kernel sent on its own account: `SIGPIPE` from `write` to a broken pipe,
  `SIGXFSZ` from `write` at the file size limit, `SIGSEGV` when it cannot update the thread's `rseq`
  area or write a signal frame, when `rt_sigreturn` finds a bad frame, or when `execve` fails past
  its point of no return. -/
  | kernel
  /-- A signal the process sent itself (`kill`, `tkill`, `tgkill` to its own process or thread). -/
  | self
  deriving Repr

/-- The system call that ended the process. `exit(2)` ends the calling thread
(`kernel/exit.c` `do_exit`), and the process with it when that thread is its last;
`exit_group(2)` ends every thread of the process (`do_group_exit`). -/
inductive ExitCall
  | exit
  | exitGroup
  deriving DecidableEq, Repr

/-- How a run ends. -/
inductive Outcome
  /-- The process exited through `call` with this status: the low 8 bits of the argument. -/
  | exited (call : ExitCall) (status : BitVec 8)
  | killed (sig : Signal) (cause : KillCause)
  | notModelled (what : NotModelled)
  deriving Repr

/-- An observable event: a system call with its number, argument registers
(`rdi rsi rdx r10 r8 r9`), result (`rax`), the bytes the kernel read from the process's
memory for it (the buffer of `write`), and the bytes it wrote into the process's memory
(the data of `read`). -/
structure Event where
  nr : BitVec 64
  args : List (BitVec 64)
  ret : BitVec 64
  fromProc : List Byte
  toProc : List Byte

end ZellicX86
