import ZellicX86.Spec.Linux.Syscall.Common
/-!
# Linux system calls: `futex`

Only the wake of a private futex is modelled (`FUTEX_WAKE` and `FUTEX_WAKE_BITSET` with
`FUTEX_PRIVATE_FLAG`), which a C library's `pthread_once` and its kin call after the first run of an
initializer, and the commands the kernel refuses whatever the state (`ENOSYS`). The kernel computes the
answer from the arguments alone: it checks the bitset, the alignment and `access_ok`, and returns the
number of threads it woke, which is 0 because no thread waits (`sysFutex` says why).

Not modelled: every other command (the waits, requeues, `FUTEX_WAKE_OP`, the priority-inheritance
locks), a wake of a shared futex (another process may wait on it through a shared mapping), and the
`futex2` system calls (`futex_wake`, `futex_wait`, `futex_waitv`, `futex_requeue`).

Sources: Linux v6.18 `kernel/futex/syscalls.c` (`sys_futex`, `do_futex`, `futex_cmd_has_timeout`),
`kernel/futex/futex.h` (`futex_to_flags`, `futex_size`), `kernel/futex/waitwake.c` (`futex_wake`),
`kernel/futex/core.c` (`get_futex_key`), `include/uapi/linux/futex.h`, `futex(2)`.
-/
namespace ZellicX86

/-- `futex` command: wake up to `val` waiters (`include/uapi/linux/futex.h`). -/
def FUTEX_WAKE : Nat := 1
/-- `futex` command: wake up to `val` waiters whose bitset shares a bit with `val3`. -/
def FUTEX_WAKE_BITSET : Nat := 10
/-- `futex` flag: the futex is private to the process's address space. -/
def FUTEX_PRIVATE_FLAG : Nat := 128
/-- `futex` flag: a timeout is measured on `CLOCK_REALTIME`. -/
def FUTEX_CLOCK_REALTIME : Nat := 256

/-- The `futex` commands that take a timeout (`kernel/futex/syscalls.c` `futex_cmd_has_timeout`):
`FUTEX_WAIT`, `FUTEX_LOCK_PI`, `FUTEX_WAIT_BITSET`, `FUTEX_WAIT_REQUEUE_PI`, `FUTEX_LOCK_PI2`. -/
def futexHasTimeout (cmd : Nat) : Bool := [0, 6, 9, 11, 13].contains cmd

/-- `futex(uaddr, op, val, timeout, uaddr2, val3)` (`kernel/futex/syscalls.c`); `op`, `val` and
`val3` are 32-bit. The command is `op` without `FUTEX_PRIVATE_FLAG` and `FUTEX_CLOCK_REALTIME`
(`FUTEX_CMD_MASK`; every other bit stays in it).
- A command without a timeout (`futexHasTimeout`) does not read `timeout`; for it, `ENOSYS` if `op`
  has `FUTEX_CLOCK_REALTIME`, which only `FUTEX_WAIT_BITSET`, `FUTEX_WAIT_REQUEUE_PI` and
  `FUTEX_LOCK_PI2` accept (`do_futex`), or if it is no command (beyond `FUTEX_LOCK_PI2`, 13, or
  negative as an `int`).
- `FUTEX_WAKE` and `FUTEX_WAKE_BITSET` with `FUTEX_PRIVATE_FLAG` (`futex_wake`, with the bitset
  `val3`, or every bit for `FUTEX_WAKE`): a bitset of 0 is `EINVAL`; then the futex word, 4 bytes,
  must be aligned to 4 (`EINVAL`) and pass `access_ok` (`EFAULT`; `get_futex_key`). The word's size is
  computed (`futex_size`), but bounded far below a page, so that the compiler folds the check to the
  pointer's alone as for a constant size (`accessOkFixed`; on a running Linux 6.18 kernel a wake at
  `uaddr = USER_PTR_MAX` succeeds). A private futex's key is the address space and the address, without
  a lookup of the mapping, so the word need not be mapped. The kernel then wakes, up to `val`, the
  threads that wait on that key, and returns their number: here 0. A waiter is a task that shares
  this address space and sleeps in `futex_wait`; the model's process has one thread (`State`, its
  `thread`), which is the caller, and no other task shares its address space (one would come from a
  `clone` with `CLONE_VM`, not modelled, since `execve` gave the process an address space of its
  own).
- every other command, and a wake of a shared futex, is not modelled.

Fault injection's `fail_futex` (`should_fail_futex`, `CONFIG_FAIL_FUTEX`, a debugging option) is
taken as not configured. -/
def sysFutex (prof : Profile) (s : State) : Req StepResult :=
  let uaddr := s.cpu.gpr.rdi
  let op := arg32 s.cpu.gpr.rsi
  let cmd := op % FUTEX_PRIVATE_FLAG + op / (2 * FUTEX_CLOCK_REALTIME) * (2 * FUTEX_CLOCK_REALTIME)
  let isPrivate := op / FUTEX_PRIVATE_FLAG % 2 = 1
  let clockRt := op / FUTEX_CLOCK_REALTIME % 2 = 1
  let bitset := if cmd = FUTEX_WAKE then 0xffffffff else arg32 s.cpu.gpr.r9
  let ret (v : BitVec 64) : Req StepResult := Pure.pure (sysReturn s v [] [])
  let stop (what : String) : Req StepResult := Pure.pure (.stopped (.notModelled (.feature what)))
  if !futexHasTimeout cmd ∧ (clockRt ∨ cmd > 13) then ret (errRet ENOSYS)
  else if (cmd = FUTEX_WAKE ∨ cmd = FUTEX_WAKE_BITSET) ∧ isPrivate then
    if bitset = 0 then ret (errRet EINVAL)
    else if uaddr.toNat % 4 ≠ 0 then ret (errRet EINVAL)
    else if !accessOkFixed prof.feat uaddr 4 then ret (errRet EFAULT)
    else ret 0
  else if cmd = FUTEX_WAKE ∨ cmd = FUTEX_WAKE_BITSET then stop "futex wake of a shared futex"
  else stop "futex command other than a private wake"

end ZellicX86
