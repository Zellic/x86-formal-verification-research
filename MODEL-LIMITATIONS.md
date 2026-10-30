# What the model covers, and what it does not

The theorems in this repository are about a model (`ZellicX86/Spec/`) of one Linux process on x86-64. This page says
where that model stops. It is about the model, not about any one theorem: a theorem's own assumptions are in its
statement and in the README.

The model is built so that its limits show. Where a run reaches something the model does not cover (an instruction it
does not implement, a system call it does not know, a processor feature it does not follow), the run ends with an
explicit outcome, "not modelled", that names what was hit. Such a case is never approximated by a fault, a no-op or an
arbitrary value. Every theorem here rules this outcome out, so a theorem says, among other things, that its runs never
reach the model's limits. Where the manuals or the kernel leave a choice open (an undefined flag, which of two faults
is reported, where the kernel places a mapping, whether a memory request fails), the model leaves it open too, and the
theorems hold for every choice; the exceptions, where the model follows what a processor was observed to do, are
listed under "Processors".

What follows lists the limits by area. It is a summary; the model's definitions are the precise statement.

## Scope

- **One process, one thread.** The model is a single-threaded Linux process (Linux 6.18, x86-64) in 64-bit user mode.
  The kernel appears only through what the process can observe of it: system-call results, signals, and events
  between instructions.
- **Programs started from a static executable.** `execve` of a statically linked, non-position-independent ELF
  executable (`ET_EXEC`). Dynamically linked programs (`PT_INTERP`), position-independent executables (`ET_DYN`) and the
  `MMAP_PAGE_ZERO` personality are not modelled.
- **Not modelled:** creating processes or threads (`fork`, `vfork`, `clone`), `execve` from a running process, waiting
  for children, compatibility mode and 32-bit code, the x32 system-call interface.

## Instructions

- **Encodings.** Legacy prefixes, `REX`, the one-byte, `0F`, `0F 38` and `0F 3A` maps, and `VEX`/`EVEX` in those
  maps. Not modelled: `REX2` and the `EVEX` maps 4–6 (APX, AVX512-FP16), `VEX` maps 4 and up, and encodings whose
  meaning or length the vendors' manuals do not settle or that the two vendors decode differently (for example `C4`,
  `C5` or `62` after a `REX` prefix). Where an instruction has several prefixes of one group, which the manuals say
  it should not, the model takes the last `F2`/`F3` and the last `FS`/`GS`, and `F2`/`F3` over `66` as a mandatory
  prefix.
- **Implemented:** the general-purpose integer instructions compilers emit, BMI1/BMI2, LZCNT, the x87 unit, and large
  parts of SSE through AVX2. For AVX-512, the integer subset: moves, logic, add/subtract, min/max, compares into opmasks,
  broadcasts, packs, multiplies, and the opmask instructions.
- **Not implemented** (a run that reaches one ends as not modelled):
  - AVX-512 floating point, gathers and scatters, the lane-crossing shuffles and permutes, and the other SSE/AVX
    instructions outside the implemented part (the decoder's tables, `ZellicX86/Spec/Decode/Maps.lean`, are the exact list);
  - all MMX instructions;
  - the x87 transcendentals (`FSIN`, `FCOS`, `FPTAN`, `FPATAN`, `F2XM1`, `FYL2X`, …);
  - `POPCNT`, `CMPXCHG8B`/`CMPXCHG16B`, `RDRAND`/`RDSEED`, ADX, AES-NI, PCLMULQDQ;
  - `RCL`, `RCR` and `PAUSE` (decoded, not executed);
  - flags and system instructions such as `PUSHF`/`POPF`, `LAHF`/`SAHF`, `CLC`/`STC`, `ENTER`, `XLAT`, segment-register
    moves, far returns, `INT n`, `IN`/`OUT`;
  - transactional memory (`XBEGIN`/`XEND`/`XABORT`), and the shadow-stack instructions;
  - a few narrow cases of implemented instructions (a shift or rotate of memory by a masked count of 0, `F2` on string
    moves, 16-bit `PUSH`, `POP` and `LEAVE`, the `66`-prefixed forms of `JRCXZ`, `LOOP` and `Jcc`, x87 rounding under
    the reserved precision control, among others).
- **Processor features that end a run as not modelled:** single-stepping (`RFLAGS.TF`), alignment checking
  (`RFLAGS.AC`), split-lock detection set to fatal on a processor that detects only bus locks (a `#DB` trap after
  the instruction; with split-lock detection proper the `#AC` is modelled), a user-mode `#NM`, an enabled user shadow stack (for `CALL`/`RET`),
  and register state the model does not hold (MPX, AMX, APX).

## Processors

- **The processor is a parameter.** Vendor, feature set, the `CPUID` answers and a few behaviour bits form a profile
  that theorems quantify over; a statement that needs a feature has it as a hypothesis.
- **Where the vendors differ or leave a result undefined,** the model leaves it open (undefined flags and values,
  vendor-dependent results such as `BSF`/`BSR` on a zero source on Intel, which of two simultaneous faults is reported).
- **Measured mainly on AMD.** The model follows the Intel and AMD manuals, and was checked against hardware mainly on
  an AMD Zen 4 (some behaviour also on an Intel Raptor Lake core). Where the manuals do not settle a detail, or the two
  vendors' manuals disagree, the model mostly leaves it open; in these cases it follows what the Zen 4 does instead,
  for every processor of the vendor named or for both:
  - the order of the faults of two memory accesses of one instruction (`PUSH`, `POP`, `CALL` with a memory target),
    and whether a memory operand with base `r12` or `r13` is a stack reference (`#SS` or `#GP`), on both vendors;
  - the flags after a faulting iteration of a repeated `CMPS` or `SCAS`;
  - the x87 environment's fault byte, `#XM` for precision, the placement of a NaN's fraction when single or double
    precision is widened to double extended, the internal precision of the x87 constants, and `FXSAVE` leaving bytes
    416–463 unwritten;
  - on AMD: an unmasked denormal operand does not stop `FLD`, `FILD` or `FBLD` (the APM's Table 6-22 says the stack is
    not changed), `FCOM`/`FCOMI`'s condition codes under an unmasked exception, and the reserved immediate bits of
    `ROUND` being ignored;
  - the decoding of a few encodings both manuals leave blank or disagree on: `FF /7` is `#UD`, and `VZEROUPPER`/
    `VZEROALL` with `VEX.W=1` execute.

  The docstrings that cite "an AMD Zen 4" name such observations; the measurements themselves are not part of this
  release.
- **The time-stamp counter** (`RDTSC`) reads an arbitrary value: nothing relates two readings.

## Faults and exceptions

- `#DE`, `#DB`, `#BP`, `#UD`, `#NM`, `#SS`, `#GP`, `#PF`, `#MF`, `#AC`, `#XM` and `#CP` are modelled, each with the
  signal Linux delivers for it. Delivery of `#DB`'s, `#MF`'s and `#CP`'s signals to a handler is not modelled.
- Where an instruction's length depends on bytes that cannot be fetched (a fetch fault inside a possibly invalid
  encoding), the outcome is not modelled. So is the `#UD` of an instruction whose feature the processor lacks unless
  all 15 bytes from the instruction's start can be fetched (a processor without the feature may decode another
  length).

## Memory

- **The address space is real:** a page map onto backings, so two pages can alias. Private file mappings are
  copy-on-write, shared mappings write the file and every mapping of it sees the write, pages past a file's end raise
  `SIGBUS`, and code is fetched from memory as it is (modified code is seen by the next instruction).
- **No concurrency.** One thread's accesses happen in order. There is no memory-ordering model, so the weaker ordering
  of non-temporal stores is not modelled. Other agents' writes (a debugger, `/proc/PID/mem`, a file written through
  another mapping) are events between instructions: each instruction is atomic to them, which real hardware does not
  guarantee (a torn access or a lost update of an unlocked read-modify-write is not covered). The kernel's reclaim of
  lazily freed (`MADV_FREE`) pages also happens between instructions. The theorems here assume no writes by others.
- **Caches, timing and speculative execution** are not modelled; side channels are out of scope.
- **Not modelled mappings:** devices and special files (`/dev/zero`, hugetlbfs, DAX), `MAP_SYNC`, `MAP_HUGETLB`,
  `MAP_DROPPABLE`, `MAP_LOCKED`, private `MAP_GROWSDOWN`, `PROT_GROWSDOWN`/`PROT_GROWSUP`, execute-only memory with
  protection keys, changes over the vDSO or the initial stack's first page, `mremap` of stack pages, and the
  configuration-dependent `madvise` advice (KSM, transparent huge pages, memory poisoning).

## Linux

- **System calls.** These are modelled:
  - I/O on descriptors: `read`, `write`, `writev`, `pread64`, `pwrite64`, `lseek`, `close`, `dup`/`dup2`/`dup3`,
    `fcntl`, `fstat`, `ioctl` (only `TCGETS2`), `openat`, `readlinkat`;
  - memory: `mmap`, `munmap`, `mprotect`, `mremap`, `madvise`, `brk`;
  - signals: `rt_sigaction`, `rt_sigprocmask`, `rt_sigreturn`, `rt_sigpending`, `sigaltstack`, and `kill`/`tkill`/
    `tgkill` to the process itself;
  - the process and a C library's startup: `exit`, `exit_group`, `getpid`, `gettid`, `getrlimit`, `setrlimit`,
    `prlimit64`, `arch_prctl`, `set_tid_address`, `set_robust_list`, `rseq`, `futex` (private wake only);
  - time and randomness: `clock_gettime`, `gettimeofday`, `time`, `getcpu`, `getrandom`.

  Every other system call is not modelled. Among the consequences: no pipes, sockets or polling, no `stat` or
  directory listing, no file creation or truncation (`openat` with `O_CREAT`, `O_TRUNC` or `O_TMPFILE`), no sleeping.
  Within the modelled calls, some options and cases are not modelled, for example `fcntl` locks and leases and
  `F_SETFL` changing `FASYNC`, other `ioctl` commands, `futex` waits, `kill` of another process, `prlimit64` of
  another process, `arch_prctl`'s AMX, tagged-address and shadow-stack options, a `write` from a mapping of the file
  being written, a `read` into memory the process cannot write, a `write` or `writev` that takes only part of a buffer
  after the kernel grew a stack for it, `lseek` with `SEEK_DATA`/`SEEK_HOLE`, `pread64`/`pwrite64` on files without
  pages, `clock_gettime` with negative or auxiliary clock ids, and `madvise`'s `MADV_GUARD_INSTALL`/`MADV_GUARD_REMOVE`.
- **`execve`.** Not modelled: files the ELF loader rejects, segments that overlap the initial stack, execute-only
  segments with protection keys, a `vm.max_map_count` below what the image needs, and a security module's credential
  transition. One placement the kernel can choose is not admitted: with `stack_guard_gap=0` on the kernel command line,
  or with loadable segments filling the space below the initial stack, the kernel can place the vDSO in pages the stack
  must then grow into, and kills the new program before its first instruction; the theorems do not cover such
  launches.
- **No file system.** Which file a path names, file metadata beyond a regular file's size and type, the contents of
  files that are not mapped (pipes, terminals, devices), and `getrandom`'s bytes are the environment's answers, over
  which theorems quantify. There is no working directory. Credentials and security modules are not modelled; their
  effect is that a call may fail, which the model allows.
- **Signals.** Sending, blocking, pending, and delivery to handlers of signals the process causes (by an exception) or
  sends itself are modelled, with the full 64-bit signal frame, alternate stacks and `rt_sigreturn`. Not modelled:
  delivery to a handler of a signal from outside the process or of `write`'s `SIGPIPE`/`SIGXFSZ`, a blocked real-time
  signal from outside, `SIGKILL` from outside to a PID namespace's init, the stop signals and stopping default actions,
  `rseq` critical sections, an `rseq` update or a tracer's access for which the kernel would grow a stack, frames with
  MPX/AMX/APX state or a shadow stack. A signal from
  outside can still end the process or stay pending. System calls are not interrupted (`EINTR` does not arise): they
  complete, and outside signals arrive between instructions. Nor do they block: a call that would wait (a `read` from
  an empty pipe or an idle terminal) returns in the model when the environment answers it, so a theorem that a run
  ends holds for the runs in which every call returns.
- **The vDSO** is a parameter: its image, and contracts its functions are assumed to meet. No real image is shown to
  meet them; the vDSO's data pages are not described. No theorem of this repository assumes such a contract.
- **Kernel settings** that change behaviour (the stack guard gap, split-lock handling, the `vsyscall=` mode, and others)
  are parameters of the theorems; settings an administrator can change are read at `execve`.
- **Assumed of the environment, not modelled:** no seccomp filter changes results, no tracer stops the process for
  signals, the running executable is not written by others. (A process that is a PID namespace's init is modelled,
  with the kernel's `SIGNAL_UNKILLABLE`, but for `SIGKILL` sent to it from outside, above.) Kernel failures for want
  of memory or other resources are always possible in the model; a theorem can assume them away, as the programs'
  theorems here do (`Heap.MemGranted`, README).

## What the model does not claim

The model describes what a correct processor and Linux 6.18 kernel do. It does not cover hardware errata or faults,
kernel bugs, or timing.
