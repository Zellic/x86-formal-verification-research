import ZellicX86.Spec.Linux.Env
import ZellicX86.Spec.Linux.Syscall
/-!
# The Linux process model

What Linux v6.18 (x86-64) does for the process at the boundary with user mode, in the modules
below `Spec/Linux/`: the booted kernel's settings (`Boot`); the signal it sends for an exception,
sending and taking pending signals, and the kernel's access to user memory (`Basic`); growing a
stack on a fault (`Stack`); what environment events do (`Env`); delivery to signal handlers
(`Signal`); `execve` of a static executable (`Exec`); the legacy vsyscall page (`Vsyscall`); and the
system calls the model implements (`Syscall`, one module per group under `Syscall/`). Every other
system call ends the run as not modelled, except the numbers for which the kernel itself returns
`-ENOSYS` (outside its table, negative, or without an entry point: `syscall`, `niSyscall`).
-/
