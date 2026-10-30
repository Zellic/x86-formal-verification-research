import ZellicX86.Spec.Word
/-!
# Signals

Signal numbers, dispositions and default actions as Linux defines them for x86-64
(`arch/x86/include/uapi/asm/signal.h`, `kernel/signal.c`, `signal(7)`).
-/
namespace ZellicX86

/-- A signal number, 1 to 64 (`_NSIG = 64`); the type does not enforce the range. -/
abbrev Signal := Nat

namespace Signal
/-- Hangup (`signal(7)`). -/
def SIGHUP : Signal := 1
/-- Interrupt from keyboard (`signal(7)`). -/
def SIGINT : Signal := 2
/-- Quit from keyboard (`signal(7)`). -/
def SIGQUIT : Signal := 3
/-- Illegal instruction (`signal(7)`). -/
def SIGILL : Signal := 4
/-- Trace or breakpoint trap (`signal(7)`). -/
def SIGTRAP : Signal := 5
/-- Abort (`signal(7)`). -/
def SIGABRT : Signal := 6
/-- Bus error (bad memory access) (`signal(7)`). -/
def SIGBUS : Signal := 7
/-- Arithmetic exception (`signal(7)`). -/
def SIGFPE : Signal := 8
/-- Kill; cannot be caught, blocked or ignored (`signal(7)`). -/
def SIGKILL : Signal := 9
/-- User-defined signal 1 (`signal(7)`). -/
def SIGUSR1 : Signal := 10
/-- Invalid memory reference (`signal(7)`). -/
def SIGSEGV : Signal := 11
/-- User-defined signal 2 (`signal(7)`). -/
def SIGUSR2 : Signal := 12
/-- Broken pipe: write to a pipe with no readers (`signal(7)`). -/
def SIGPIPE : Signal := 13
/-- Timer signal from `alarm(2)` (`signal(7)`). -/
def SIGALRM : Signal := 14
/-- Termination (`signal(7)`). -/
def SIGTERM : Signal := 15
/-- Stack fault on coprocessor (unused) (`signal(7)`). -/
def SIGSTKFLT : Signal := 16
/-- Child stopped, continued or terminated (`signal(7)`). -/
def SIGCHLD : Signal := 17
/-- Continue if stopped (`signal(7)`). -/
def SIGCONT : Signal := 18
/-- Stop; cannot be caught, blocked or ignored (`signal(7)`). -/
def SIGSTOP : Signal := 19
/-- Stop typed at terminal (`signal(7)`). -/
def SIGTSTP : Signal := 20
/-- Terminal input for a background process (`signal(7)`). -/
def SIGTTIN : Signal := 21
/-- Terminal output for a background process (`signal(7)`). -/
def SIGTTOU : Signal := 22
/-- Urgent condition on a socket (`signal(7)`). -/
def SIGURG : Signal := 23
/-- CPU time limit exceeded (`signal(7)`). -/
def SIGXCPU : Signal := 24
/-- File size limit exceeded (`signal(7)`). -/
def SIGXFSZ : Signal := 25
/-- Virtual alarm clock (`signal(7)`). -/
def SIGVTALRM : Signal := 26
/-- Profiling timer expired (`signal(7)`). -/
def SIGPROF : Signal := 27
/-- Window resize (`signal(7)`). -/
def SIGWINCH : Signal := 28
/-- I/O now possible (`signal(7)`). -/
def SIGIO : Signal := 29
/-- Power failure (`signal(7)`). -/
def SIGPWR : Signal := 30
/-- Bad system call (`signal(7)`). -/
def SIGSYS : Signal := 31
end Signal

/-- What a signal does when it is delivered and its disposition is the default
(`signal(7)`, "Standard signals"; real-time signals 32–64 terminate). -/
inductive DefaultAction
  /-- Terminate the process. -/
  | term
  /-- Terminate the process and dump core (whether a core file is written depends on
  `RLIMIT_CORE` and the system, which the process cannot observe). -/
  | core
  /-- Discard the signal. -/
  | ign
  /-- Stop the process until `SIGCONT`. Nothing the process can observe changes. -/
  | stop
  /-- Continue a stopped process; otherwise discard. -/
  | cont
  deriving DecidableEq, Repr

/-- The default action of signal `s` (`signal(7)`; `kernel/signal.c` `sig_kernel_*`). -/
def defaultAction (s : Signal) : DefaultAction :=
  match s with
  | 3 | 4 | 5 | 6 | 7 | 8 | 11 | 24 | 25 | 31 => .core
  | 17 | 23 | 28 => .ign
  | 19 | 20 | 21 | 22 => .stop
  | 18 => .cont
  | _ => .term

/-- How a process handles a signal (`sigaction(2)`): `sa_handler` is `SIG_DFL` (0), `SIG_IGN` (1),
or the address of a handler. -/
inductive Disposition
  | default
  | ignore
  | handler (addr : Addr)

/-- A set of signals as the kernel's `sigset_t`: bit `s - 1` for signal `s`. -/
abbrev SigSet := BitVec 64

/-- Whether signal `s` is in set `m`. -/
def SigSet.mem (m : SigSet) (s : Signal) : Bool := m.getLsbD (s - 1)

/-- `m` with signal `s` added. -/
def SigSet.insert (m : SigSet) (s : Signal) : SigSet := m ||| (1 <<< (s - 1))

/-- `m` without `SIGKILL` and `SIGSTOP`, which no mask blocks (`sigdelsetmask(.., sigmask(SIGKILL)
| sigmask(SIGSTOP))` wherever the kernel takes a mask from the process, `kernel/signal.c`). -/
def SigSet.unblockable (m : SigSet) : SigSet := m &&& ~~~(((1 : SigSet) <<< 8) ||| ((1 : SigSet) <<< 18))

/-- A signal action as the kernel keeps it (`struct sigaction`, `arch/x86/include/uapi/asm/signal.h`;
`struct k_sigaction`): the disposition, `sa_flags`, `sa_mask` and `sa_restorer`. The kernel keeps the
flags, mask and restorer also for `SIG_DFL` and `SIG_IGN`, and `rt_sigaction` reports them back. -/
structure SigAction where
  disp : Disposition
  flags : BitVec 64
  mask : SigSet
  restorer : Addr

/-- The action of every signal after `execve`, unless ignored (`flush_signal_handlers`,
`kernel/signal.c`): the default, with no flags, mask or restorer. -/
def SigAction.dfl : SigAction := ⟨.default, 0, 0, 0⟩

/-! ## `sa_flags` and `ss_flags`

`include/uapi/asm-generic/signal-defs.h`, `arch/x86/include/uapi/asm/signal.h`,
`include/uapi/linux/signal.h`. -/

def SA_NOCLDSTOP : BitVec 64 := 0x00000001
def SA_NOCLDWAIT : BitVec 64 := 0x00000002
/-- The handler takes `siginfo_t` and `ucontext` arguments; the frame carries the `siginfo`. -/
def SA_SIGINFO : BitVec 64 := 0x00000004
def SA_EXPOSE_TAGBITS : BitVec 64 := 0x00000800
/-- `sa_restorer` holds the address the handler returns to (glibc's `__restore_rt`, which calls
`rt_sigreturn`). A 64-bit frame needs it. -/
def SA_RESTORER : BitVec 64 := 0x04000000
/-- Run the handler on the alternate signal stack, if one is set up. -/
def SA_ONSTACK : BitVec 64 := 0x08000000
/-- Restart a system call the signal interrupts. -/
def SA_RESTART : BitVec 64 := 0x10000000
/-- Do not block the signal while its handler runs. -/
def SA_NODEFER : BitVec 64 := 0x40000000
/-- Reset the action to `SIG_DFL` when the signal is delivered (`SA_ONESHOT`). -/
def SA_RESETHAND : BitVec 64 := 0x80000000

/-- The flags `rt_sigaction` keeps; it clears the others (`UAPI_SA_FLAGS`,
`include/linux/signal_types.h`, with x86's `SA_RESTORER`). -/
def uapiSaFlags : BitVec 64 :=
  SA_NOCLDSTOP ||| SA_NOCLDWAIT ||| SA_SIGINFO ||| SA_ONSTACK ||| SA_RESTART ||| SA_NODEFER |||
  SA_RESETHAND ||| SA_EXPOSE_TAGBITS ||| SA_RESTORER

/-- `ss_flags`: the thread is on its alternate stack (reported only). -/
def SS_ONSTACK : BitVec 32 := 1
/-- `ss_flags`: no alternate stack. -/
def SS_DISABLE : BitVec 32 := 2
/-- `ss_flags`: the alternate stack is disabled while a handler runs on it. -/
def SS_AUTODISARM : BitVec 32 := 0x80000000

/-- The smallest alternate stack `sigaltstack` accepts (`MINSIGSTKSZ`,
`arch/x86/include/uapi/asm/signal.h`). -/
def MINSIGSTKSZ : Nat := 2048

/-! ## `siginfo` -/

/-- `si_code` values (`include/uapi/asm-generic/siginfo.h`), as the 32-bit integers they are. -/
def SI_USER : BitVec 32 := 0
def SI_KERNEL : BitVec 32 := 0x80
def SI_QUEUE : BitVec 32 := -1
def SI_TKILL : BitVec 32 := -6
def ILL_ILLOPN : BitVec 32 := 2
def FPE_INTDIV : BitVec 32 := 1
def FPE_FLTDIV : BitVec 32 := 3
def FPE_FLTOVF : BitVec 32 := 4
def FPE_FLTUND : BitVec 32 := 5
def FPE_FLTRES : BitVec 32 := 6
def FPE_FLTINV : BitVec 32 := 7
def SEGV_MAPERR : BitVec 32 := 1
def SEGV_ACCERR : BitVec 32 := 2
def SEGV_PKUERR : BitVec 32 := 4
def BUS_ADRALN : BitVec 32 := 1
def BUS_ADRERR : BitVec 32 := 2

/-- What the kernel records about a signal it sends (`struct kernel_siginfo`,
`include/linux/signal_types.h`; the first 48 bytes of `siginfo_t`,
`include/uapi/asm-generic/siginfo.h`): the signal, an error number, the code saying where the
signal came from, and the 32 bytes of the union `_sifields` (offsets 16–47), whose layout depends
on the signal and the code: the sender's process id and user id (offsets 16 and 20) for a signal a
process sent, the address (offset 16) and the protection key (offset 32) for a fault. Whatever a
sender does not set is zero (`clear_siginfo`). -/
structure SigInfo where
  signo : Signal
  errno : BitVec 32
  code : BitVec 32
  fields : BitVec 256

/-- The 128 bytes of `siginfo_t` the kernel copies to a signal frame (`copy_siginfo_to_user`,
`kernel/signal.c`): the 48 bytes of the `kernel_siginfo`, the 4 after `si_code` zero, and 80 bytes
of zeros after it. -/
def SigInfo.bytes (i : SigInfo) : List Byte :=
  toBytesLE (BitVec.ofNat 32 i.signo) 4 ++ toBytesLE i.errno 4 ++ toBytesLE i.code 4 ++
  [0, 0, 0, 0] ++ toBytesLE i.fields 32 ++ List.replicate 80 0

/-- A signal a process sent (`kill`, `tgkill`, the kernel's `SEND_SIG_NOINFO`): code `code`, the
sender's process id `pid` and user id `uid` (`prepare_kill_siginfo`, `kernel/signal.c`). -/
def SigInfo.ofSender (sig : Signal) (code : BitVec 32) (pid uid : Nat) : SigInfo :=
  ⟨sig, 0, code, BitVec.ofNat 256 pid ||| (BitVec.ofNat 256 (uid % 2 ^ 32) <<< 32)⟩

/-- A signal the kernel sends on its own account (`force_sig`, `SEND_SIG_PRIV`): `SI_KERNEL`, no
sender. -/
def SigInfo.kernel (sig : Signal) : SigInfo := ⟨sig, 0, SI_KERNEL, 0⟩

/-- A fault: code `code` and the faulting address `addr` (`force_sig_fault`). -/
def SigInfo.fault (sig : Signal) (code : BitVec 32) (addr : Addr) : SigInfo :=
  ⟨sig, 0, code, addr.setWidth 256⟩

/-- The information a lost queue entry leaves (`collect_signal`, `kernel/signal.c`): `SI_USER`
with process and user id 0. -/
def SigInfo.lost (sig : Signal) : SigInfo := ⟨sig, 0, SI_USER, 0⟩

end ZellicX86
