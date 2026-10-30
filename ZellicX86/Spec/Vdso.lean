import ZellicX86.Spec.Process
/-!
# Statement vocabulary for the vDSO

The vDSO is a shared object the kernel maps into every process (`LinuxBoot.vdso`, `LinuxBoot.vdsoText`;
`arch/x86/entry/vdso/vma.c` `map_vdso`): data pages the kernel keeps up to date, then the image, whose functions
read the time, the CPU and random bytes, by reading those pages or by making the system call (vdso(7)). A C
library finds them by name in the image's dynamic symbol table and calls them. The model runs the image's code as
any code of the process; the image is a parameter of the booted kernel, as its build has it. So a statement about a
program that calls a function of the vDSO treats it as a callee it has not verified: it assumes that the code at the
function's entry point implements the function's contract (`VdsoImplements`), as it would for a library function.
**What such an assumption covers.** `ImplementsCall` covers every call state the contract's precondition allows,
and the real image's time functions read the vDSO's data pages, at a fixed distance below the image (six pages):
they fault where those pages are not there, and loop where the time data's sequence counter stays odd. The
preconditions do not describe the data pages, so no real kernel's image is known to meet `vdsoClockGettime`,
`vdsoGettimeofday` or `vdsoTime`; nor `vdsoGetcpu`, whose real code reads the CPU by `RDPID` or `LSL`, which the
model does not decode. A statement assuming one of them is not inconsistent (simple code meets each), but it says
something about a real kernel only where the contract has a precondition on the data pages (their place, and what the
kernel keeps in them) and is proved of that kernel's image. No statement of this repository assumes one.
`vdsoGetrandomQuery` reads no data page.

- the functions by their symbols (`VdsoFn`), where the image's tables put them (`LinuxBoot.vdsoEntry`), and the
  images a statement covers, by their ELF tables (`VdsoImage`);
- the contracts: `clock_gettime` for the clocks the vDSO reads itself (`vdsoClockGettime`), `gettimeofday`
  (`vdsoGettimeofday`), `time` (`vdsoTime`), `getcpu` (`vdsoGetcpu`), and `getrandom`'s query of its parameters
  (`vdsoGetrandomQuery`), each with what the real image needs before it can meet it (below);
- the assumption that the booted kernel's image implements one (`VdsoImplements`).

Each contract is under the psABI (`sysv`) and takes `n`, the bytes of stack below `rsp` the function may use (its
frames: `frame`), which the caller must have writable; a contract says what the function does whatever the image's
build, so its system-call fallback is allowed (events of the call's number) and the values read from a clock are
any.

Sources: Linux v6.18 `arch/x86/entry/vdso/` (`vdso.lds.S`, `vclock_gettime.c`, `vgetcpu.c`, `vgetrandom.c`),
`lib/vdso/gettimeofday.c`, `lib/vdso/getrandom.c`, `include/uapi/linux/random.h` (`vgetrandom_opaque_params`),
`include/uapi/linux/mman.h`, vdso(7), the psABI.
-/
namespace ZellicX86

/-- The vDSO's functions the vocabulary has contracts for. -/
inductive VdsoFn
  | clockGettime
  | gettimeofday
  | time
  | getcpu
  | getrandom
  deriving DecidableEq, Repr

/-- The function's symbol in the image (`arch/x86/entry/vdso/vdso.lds.S`). -/
def VdsoFn.symbol : VdsoFn → String
  | .clockGettime => "__vdso_clock_gettime"
  | .gettimeofday => "__vdso_gettimeofday"
  | .time => "__vdso_time"
  | .getcpu => "__vdso_getcpu"
  | .getrandom => "__vdso_getrandom"

/-- The offset of function `f`'s entry point in the image of `lb`: the value of its symbol in the image's dynamic
symbol table (`dynSymbol`; the image is linked at address 0, so a symbol's value is its offset), if it has one. -/
def LinuxBoot.vdsoEntry (lb : LinuxBoot) (f : VdsoFn) : Option Nat :=
  dynSymbol lb.vdsoByte (f.symbol.toUTF8.toList.map fun u => BitVec.ofNat 8 u.toNat)

/-- The booted kernel `lb` maps the vDSO, and its image is `pages` pages long and begins with the bytes `tables`:
the image's ELF header, program headers, dynamic section and the tables they lead to (hash, symbol, string and
version tables), as a kernel's build has them. These tables say where the image's functions are
(`LinuxBoot.vdsoEntry`), and a C library reads them to find the functions (glibc's static startup:
`_dl_non_dynamic_init`, `setup_vdso`), so a statement about such a program names the images it covers this way
(`VdsoImage l.prof.linux tables pages`), the kernel builds whose tables it was proved for (their tables as constants:
`Spec/VdsoImages.lean`). -/
def VdsoImage (lb : LinuxBoot) (tables : List Byte) (pages : Nat) : Prop :=
  lb.vdso = true ∧ lb.vdsoText.length = pages ∧ ∀ i, i < tables.length → lb.vdsoByte i = tables.getD i 0

/-- The events of a call of a function of the vDSO that may make the system call `nr` itself (its fallback, where it
cannot answer from user mode): only system calls of that number (in `rax`'s low 32 bits, as the kernel reads it). -/
def VdsoEvents (nr : Nat) (evs : List Event) : Prop :=
  ∀ e ∈ evs, arg32 e.nr = nr

/-- The clocks `clock_gettime` of the vDSO reads itself (`lib/vdso/gettimeofday.c`: the high-resolution, coarse and
raw clocks): `CLOCK_REALTIME` (0), `CLOCK_MONOTONIC` (1), `CLOCK_MONOTONIC_RAW` (4), `CLOCK_REALTIME_COARSE` (5),
`CLOCK_MONOTONIC_COARSE` (6), `CLOCK_BOOTTIME` (7), `CLOCK_TAI` (11). -/
def vdsoClocks : List Int := [0, 1, 4, 5, 6, 7, 11]

/-- `clock_gettime(clk, tp)` for a clock of `vdsoClocks` (`clk` in `edi`, an `int`): returns 0 with some time at
`tp`, 8 bytes of seconds and 8 of nanoseconds below 10⁹ (`struct __kernel_timespec`). `tp`'s 16 bytes are
written, apart from the frames. Not met by a real image without a precondition on the data pages (module header). -/
def vdsoClockGettime (n : Nat) : Contract where
  conv := sysv
  reads _ := []
  writes s := [frame s n, ⟨s.cpu.gpr.rsi, 16⟩]
  pre s := argInt s.cpu.gpr.rdi ∈ vdsoClocks ∧ Apart [frame s n] [⟨s.cpu.gpr.rsi, 16⟩]
  post s X := X.cpu.gpr.rax = 0 ∧ ∃ t : Timespec, Bytes X s.cpu.gpr.rsi t.bytes
  events _ _ evs := VdsoEvents 228 evs

/-- `gettimeofday(tv, tz)` with `tv` not 0: returns 0 with some wall-clock time at `tv`, 8 bytes of seconds and 8
of microseconds below 10⁶ (`struct __kernel_old_timeval`), and unless `tz` is 0 some time zone at `tz`, 8 bytes.
The regions written lie apart from the frames and from each other. Not met by a real image without a precondition on
the data pages (module header). -/
def vdsoGettimeofday (n : Nat) : Contract where
  conv := sysv
  reads _ := []
  writes s := [frame s n, ⟨s.cpu.gpr.rdi, 16⟩] ++ (if s.cpu.gpr.rsi = 0 then [] else [⟨s.cpu.gpr.rsi, 8⟩])
  pre s := s.cpu.gpr.rdi ≠ 0 ∧ Apart [frame s n] [⟨s.cpu.gpr.rdi, 16⟩] ∧
    (s.cpu.gpr.rsi ≠ 0 → Apart [frame s n, ⟨s.cpu.gpr.rdi, 16⟩] [⟨s.cpu.gpr.rsi, 8⟩])
  post s X := X.cpu.gpr.rax = 0 ∧
    ∃ sec usec : BitVec 64, usec.toNat < 1000000 ∧ Bytes X s.cpu.gpr.rdi (toBytesLE sec 8 ++ toBytesLE usec 8)
  events _ _ evs := VdsoEvents 96 evs

/-- `time(tloc)`: returns some number of seconds, which it also stores at `tloc` (8 bytes) unless `tloc` is 0. Not
met by a real image without a precondition on the data pages (module header). -/
def vdsoTime (n : Nat) : Contract where
  conv := sysv
  reads _ := []
  writes s := [frame s n] ++ (if s.cpu.gpr.rdi = 0 then [] else [⟨s.cpu.gpr.rdi, 8⟩])
  pre s := s.cpu.gpr.rdi ≠ 0 → Apart [frame s n] [⟨s.cpu.gpr.rdi, 8⟩]
  post s X := s.cpu.gpr.rdi ≠ 0 → Bytes X s.cpu.gpr.rdi (toBytesLE X.cpu.gpr.rax 8)
  events _ _ evs := VdsoEvents 201 evs

/-- `getcpu(cpu, node, cache)`: returns 0, having stored some CPU number at `cpu` and some node number at `node`
(4 bytes each), each unless 0. Not met by a real image in the model: its code reads the CPU by `RDPID` (`F3 0F C7
/7`) or `LSL` of a per-CPU segment, which the model does not decode (module header). -/
def vdsoGetcpu (n : Nat) : Contract where
  conv := sysv
  reads _ := []
  writes s := [frame s n] ++ (if s.cpu.gpr.rdi = 0 then [] else [⟨s.cpu.gpr.rdi, 4⟩]) ++
    (if s.cpu.gpr.rsi = 0 then [] else [⟨s.cpu.gpr.rsi, 4⟩])
  pre s := (s.cpu.gpr.rdi ≠ 0 → Apart [frame s n] [⟨s.cpu.gpr.rdi, 4⟩]) ∧
    (s.cpu.gpr.rsi ≠ 0 → Apart [frame s n] [⟨s.cpu.gpr.rsi, 4⟩]) ∧
    (s.cpu.gpr.rdi ≠ 0 → s.cpu.gpr.rsi ≠ 0 → Apart [⟨s.cpu.gpr.rdi, 4⟩] [⟨s.cpu.gpr.rsi, 4⟩])
  post _ X := X.cpu.gpr.rax = 0
  events _ _ evs := VdsoEvents 309 evs

/-- `getrandom(NULL, 0, 0, params, ~0)`, the query of its parameters (`lib/vdso/getrandom.c`): returns 0, having
written `struct vgetrandom_opaque_params` at `params` (`rcx`; 64 bytes): some size of its per-thread state, the
protection and flags of the state's memory (`PROT_READ | PROT_WRITE`, `MAP_DROPPABLE | MAP_ANONYMOUS`: 3 and
`0x28`, as v6.18 sets them: another kernel version may ask for others), and 13 reserved words 0. No system call. -/
def vdsoGetrandomQuery (n : Nat) : Contract where
  conv := sysv
  reads _ := []
  writes s := [frame s n, ⟨s.cpu.gpr.rcx, 64⟩]
  pre s := s.cpu.gpr.rdi = 0 ∧ s.cpu.gpr.rsi = 0 ∧ arg32 s.cpu.gpr.rdx = 0 ∧ s.cpu.gpr.r8 = -1 ∧
    Apart [frame s n] [⟨s.cpu.gpr.rcx, 64⟩]
  post s X := X.cpu.gpr.rax = 0 ∧ ∃ size : BitVec 32,
    Bytes X s.cpu.gpr.rcx (toBytesLE size 4 ++ toBytesLE (3 : BitVec 32) 4 ++ toBytesLE (0x28 : BitVec 32) 4 ++
      List.replicate 52 0)
  events _ _ evs := evs = []

/-- The vDSO's image of the booted kernel (`prof.linux`) implements contract `C` at function `f`'s entry point,
wherever the image lies: for every address `base` of its first byte, the image's bytes there implement `C` at
`base` plus `f`'s offset (`ImplementsCall`, with the image as the function's code segment). The assumption a
statement about a program that calls `f` makes, as about a callee it has not verified; for which contracts a real
image can meet it, see the module header. -/
def VdsoImplements (prof : Profile) (f : VdsoFn) (C : Contract) : Prop :=
  ∀ off, prof.linux.vdsoEntry f = some off → ∀ base : Addr,
    ImplementsCall prof (base.add off) [(base, prof.linux.vdsoBytes)] C

end ZellicX86
