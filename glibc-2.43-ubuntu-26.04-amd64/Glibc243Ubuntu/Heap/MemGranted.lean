import ZellicX86.Spec.Statement
/-!
# The kernel grants memory: an assumption about the environment

`MemGranted`, the runs in which no request for memory fails for a reason the model leaves to the environment
(`Request.memFail`). A module of its own, so that a statement can name it without importing the proofs that use it.
-/
namespace Glibc243Ubuntu.Heap
open ZellicX86

/-- The kernel grants every request for memory that the model leaves to the environment (`Request.memFail`), whatever
the reason it could refuse: the system's (lack of memory and its accounting, `vm.max_map_count`, `vm.mmap_min_addr`,
the security module's policy, limits another process may lower), and also reasons the process's own state decides
that the syscall models leave to this request: its `RLIMIT_DATA`, `RLIMIT_AS` or `RLIMIT_MEMLOCK`, set by the
process or inherited from the one that started it, and for `brk` the
stack guard gap below a mapping that grows down (the kernel's `vm_start_gap`, `stack_guard_gap`, 256 pages by default;
`sysBrk` tests one page past the new break). An assumption about the system and about those parts of the process's
state, as `Undisturbed` is about other agents. This hypothesis rules out refusals expressed by `Request.memFail`; the model's
placement checks remain independent. A `brk` into pages already mapped or an `mmap` at an occupied place can still
fail, so an allocation can still return null. Sources: Linux v6.18 `mm/mmap.c` (`brk`), `mm/vma.c`, and the syscall
models in `ZellicX86/Spec/Linux/Syscall/Mm.lean`. The assumption is stronger than the programs need: their proofs do not
cover the paths where the kernel refuses the allocator's memory (`sysmalloc`'s `mmap` fallback where `brk` fails, and
`malloc` returning null where that fails too). -/
def MemGranted (o : Oracle) : Prop := ∀ t p, o t (.memFail p) = none

end Glibc243Ubuntu.Heap
