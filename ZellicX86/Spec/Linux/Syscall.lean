import ZellicX86.Spec.Linux.Syscall.Writev
import ZellicX86.Spec.Linux.Syscall.ReadWrite
import ZellicX86.Spec.Linux.Syscall.Mm
import ZellicX86.Spec.Linux.Syscall.Task
import ZellicX86.Spec.Linux.Syscall.Files
import ZellicX86.Spec.Linux.Syscall.Fd
import ZellicX86.Spec.Linux.Syscall.Random
import ZellicX86.Spec.Linux.Syscall.Signal
import ZellicX86.Spec.Linux.Syscall.Time
import ZellicX86.Spec.Linux.Syscall.Futex
/-!
# Linux system calls: the dispatcher

The kernel's `syscall` entry: the number's range checks, the numbers without a 64-bit entry
point, and the table of the implemented calls, one module per group of calls under
`Spec/Linux/Syscall/`. Every other number in the table is `notModelled`.

Sources: `arch/x86/entry/syscall_64.c`, `arch/x86/entry/syscalls/syscall_64.tbl`,
`arch/x86/entry/entry_64.S`, `kernel/sys_ni.c`, `kernel/exit.c`.
-/
namespace ZellicX86

/-- `NR_syscalls` for x86-64 in v6.18 (`arch/x86/entry/syscalls/syscall_64.tbl`, highest
number 469). -/
def nrSyscalls : Nat := 470

/-- The x32 system-call bit `__X32_SYSCALL_BIT` (`arch/x86/include/uapi/asm/unistd.h`). -/
def x32Bit : Nat := 0x40000000
/-- The size of the x32 system-call table (`arch/x86/entry/syscalls/syscall_64.tbl`: the x32 range ends at 547). -/
def x32NrSyscalls : Nat := 548

/-- The numbers below `NR_syscalls` for which the 64-bit table has no entry point, so that the
kernel calls `sys_ni_syscall`, which returns `-ENOSYS` (`do_syscall_x64`'s default,
`kernel/sys_ni.c`): 337–423, never assigned on x86-64 (`syscall_64.tbl` goes from 336 to 424), and
the entries listed without one (`uselib`, `create_module`, `get_kernel_syms`, `query_module`,
`nfsservctl`, `getpmsg`, `putpmsg`, `afs_syscall`, `tuxcall`, `security`, `set_thread_area`,
`get_thread_area`, `lookup_dcookie`, `epoll_ctl_old`, `epoll_wait_old`, `vserver`). -/
def niSyscall (nr : Nat) : Bool :=
  (337 ≤ nr && nr ≤ 423) ||
    [134, 174, 177, 178, 180, 181, 182, 183, 184, 185, 205, 211, 212, 214, 215, 236].contains nr

/-- The kernel's handling of `syscall` (`arch/x86/entry/syscall_64.c` `do_syscall_64`): the
number is `eax` as a signed 32-bit integer. Numbers outside the table, including negative
ones, and those without an entry point (`niSyscall`) return `-ENOSYS`; numbers in the x32 range depend on `CONFIG_X86_X32_ABI` and are not
modelled. `rcx` and `r11` were set by the `SYSCALL` instruction and are restored unchanged
on return (`arch/x86/entry/entry_64.S`), except by `rt_sigreturn` and a signal handler's entry. -/
def syscall (prof : Profile) (s : State) : Req StepResult :=
  let feat := prof.feat
  let nr := s.cpu.gpr.rax.toNat % 2 ^ 32
  if nr ≥ 2 ^ 31 then Pure.pure (sysReturn s (errRet ENOSYS) [] [])
  else if nr ≥ x32Bit then
    if nr - x32Bit < x32NrSyscalls then Pure.pure (.stopped (.notModelled (.syscall s.cpu.gpr.rax)))
    else Pure.pure (sysReturn s (errRet ENOSYS) [] [])
  else if nr ≥ nrSyscalls then Pure.pure (sysReturn s (errRet ENOSYS) [] [])
  else if niSyscall nr then Pure.pure (sysReturn s (errRet ENOSYS) [] [])
  else
    match nr with
    | 0 => sysRead prof s
    | 1 => sysWrite prof s
    | 3 => sysClose s
    | 5 => sysFstat prof s
    | 8 => sysLseek s
    | 9 => sysMmap feat s
    | 10 => sysMprotect feat s
    | 11 => sysMunmap feat s
    | 12 => sysBrk feat s
    | 13 => sysRtSigaction prof s
    | 14 => sysRtSigprocmask prof s
    | 15 => sysRtSigreturn prof s
    | 16 => sysIoctl prof s
    | 17 => sysPread64 prof s
    | 18 => sysPwrite64 prof s
    | 20 => sysWritev prof s
    | 25 => sysMremap feat s
    | 28 => sysMadvise feat s
    | 32 => sysDup s
    | 33 => sysDup2 s
    | 39 => sysGetpid s
    | 62 => sysKill prof s
    | 72 => sysFcntl s
    | 96 => sysGettimeofday prof s
    | 97 => sysGetrlimit prof s
    | 127 => sysRtSigpending prof s
    | 131 => sysSigaltstack prof s
    | 158 => sysArchPrctl prof s
    | 160 => sysSetrlimit prof s
    | 186 => sysGetpid s
    | 200 => sysTgkill prof s none (argInt s.cpu.gpr.rdi) (argInt s.cpu.gpr.rsi)
    | 201 => sysTime prof s
    | 202 => sysFutex prof s
    | 218 => sysSetTidAddress s
    | 228 => sysClockGettime prof s
    | 234 => sysTgkill prof s (some (argInt s.cpu.gpr.rdi)) (argInt s.cpu.gpr.rsi) (argInt s.cpu.gpr.rdx)
    | 257 => sysOpenat prof s
    | 267 => sysReadlinkat prof s
    | 273 => sysSetRobustList s
    | 292 => sysDup3 s
    | 302 => sysPrlimit prof s
    | 309 => sysGetcpu prof s
    | 318 => sysGetrandom prof s
    | 334 => sysRseq prof s
    -- `exit` of the only thread ends the process; the status is the low 8 bits of `rdi`
    | 60 => Pure.pure (.stopped (.exited .exit (s.cpu.gpr.rdi.setWidth 8)))
    | 231 => Pure.pure (.stopped (.exited .exitGroup (s.cpu.gpr.rdi.setWidth 8)))
    | _ => Pure.pure (.stopped (.notModelled (.syscall s.cpu.gpr.rax)))

end ZellicX86
