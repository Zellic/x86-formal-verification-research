import ZellicX86.Spec.Lib.C.Unistd
import ZellicX86.Spec.Lib.C.Malloc
import ZellicX86.Spec.Lib.C.Start
import ZellicX86.Spec.Executable
import ZellicX86.Spec.ExecCode
import ZellicX86.Spec.Process
import Glibc243Ubuntu.Heap.MemGranted
import Glibc243UbuntuClients.Files.Admin
import Glibc243UbuntuClients.Program.Demo
/-!
# Statement: `holds`, the admin program end to end under named carve-outs

`clients/admin.c`'s program, as the program `clients/admin` has it (`gcc -O2 -static` against this build's `libc.a`):

```c
int main(void) {
  char *name = malloc(NAME_SIZE);              // NAME_SIZE 32
  volatile char *admin = malloc(1);
  if (name == NULL || admin == NULL) return 2;
  *admin = 0;
  ssize_t n = read(0, name, READ_LEN);         // READ_LEN NAME_SIZE
  if (n < 0) return 1;
  if (write(1, "Hello, ", 7) != 7) return 1;
  if (write(1, name, n) != n) return 1;
  if (*admin) {
    if (write(1, "! admin: yes\n", 13) != 13) return 1;
  } else {
    if (write(1, "! admin: no\n", 12) != 12) return 1;
  }
  return 0;
}
```

`holds` says, in two parts, for every process `execve` starts from this file (`Launch.Of`) within the carve-outs below:
- *safety*, on every run, at every point (`Always`): with `name` the bytes the run has read from standard input so far,
  at most 32 of them, what it has written to standard output is a first part of `line name` (`SoFar`), whose end says
  `admin: no`; and if the process has ended, it ended (exited or was killed: not an end where the model stops,
  `Outcome.Modelled`) having made only a startup's system calls, in any way the model describes (any exit status or
  killing signal; glibc's startup itself ends the process after a refused memory request, with `exit_group(127)` after
  a diagnostic on standard error), or as `Done` says;
- *liveness*, on every run that reaches `main`'s entry: the process ends, as `Done` says: with `name` the bytes the run
  read from standard input, at most 32 of them, it exited with 0 having written exactly `line name` to standard output,
  or with 1 having written a first part of it after a `read` or `write` that failed or a short `write`, or with 2 having
  read and written nothing (a `malloc` returned null), or it was killed in a `write` having written a first part of it.

A run need not get past the startup: glibc's may loop for ever on the clock's readings for the heap's key or end the
process after a refused memory request (the safety part covers those runs); a statement that it gets to `main`, and
when, is a separate startup property, beyond the conditional liveness asserted here: `holds` does not say it.

The code is the file's: glibc's startup, `malloc`, `read`, `write` and exit, crtbeginT.o's and libgcc_eh's handlers and
`main`, all as the file holds them; the statement assumes no contract of the C library.
The carve-outs (the hypotheses that restrict the launches, processors, kernels and runs the theorem covers; the
theorem with them is a *demonstration*), each a named definition, here or (those admin2's statement shares) in
`Program/Demo.lean`:
- the launch (`DemoArgs`): not secure (`AT_SECURE` 0), no tunables in the environment (neither `GLIBC_TUNABLES` nor any
  of the tunables' aliases: `NoTunables`), so every tunable keeps its default, and no `LD_LIBRARY_PATH`;
- the launch's stack (`StackRoom`: room for the startup, `startStack` and `_start`'s 32 bytes) and memory limits
  (`DemoLimits`): `RLIMIT_DATA` and `RLIMIT_AS` at least the stated bounds; `DemoLimits` explains how this restriction
  interacts with the memory-grant assumption;
- the kernel (`LinuxBoot.Modest`): its stack guard gap and vDSO image of ordinary size;
- the processor (`ThisProcessor`): an AMD one that answers the `CPUID` queries glibc's startup can make as the
  development VM's virtual CPU does (a KVM guest on an AMD Ryzen 9 7950X3D, Zen 4: `cpuidRecord`, with the hypervisor
  bit and the VM's topology; a bare-metal 7950X3D does not meet it), up to the APIC ids and L3 size fields,
  a leaf without subleaves whatever `ECX` holds, with the same state components enabled in `XCR0`; and one a real
  machine can be (`Profile.Consistent`);
- the kernel's vDSO (`ThisVdso`): none, or the development machine's (Linux 6.18.35's image, `VdsoImages.dev6_18_35`), whose
  tables glibc's startup reads;
- the runs (`DemoEnv`): undisturbed, so no signal from outside and no other writer, `/proc/self/exe` procfs's link
  (`StartEnv`), and the kernel never refuses memory for want of it (`Heap.MemGranted`; a `brk` or `mmap` into pages not
  free still fails), whatever the reason, a limit's too.

The theorem admits every signal mask: where the launch blocks `SIGPIPE` or `SIGXFSZ`, a `write` that raises it leaves
it pending and returns an error.

The theorem `holds_proof : holds` is proved by the export `admin` (`checks/admin/`).
-/
namespace Clients.Admin
open ZellicX86 Glibc243Ubuntu

/-! ## What the program reads and writes -/

/-- The most bytes a name has: the name buffer's size, `read(0, name, 32)`. -/
def nameMax : Nat := 32

/-- The line the program writes for the name `name` (the bytes its `read` delivered, whatever they are):
`Hello, `, the name, `! admin: no` and a newline. The flag's part is the line's fixed end: a name may itself contain
the text `admin: yes`. -/
def line (name : List Byte) : List Byte := utf8 "Hello, " ++ name ++ utf8 "! admin: no\n"

/-- The last `read` or `write` among the events `evs` (system call 0 or 1, by `rax`'s low 32 bits as the kernel reads
it) failed (`Event.Failed`: it returned an error number), or was a `write` to descriptor 1 that took fewer bytes than it
was asked to write. Calls of other kinds may follow it: the memory calls of the library's exit. -/
def LastShort (evs : List Event) : Prop :=
  ∃ pre ev post, evs = pre ++ ev :: post ∧ (arg32 ev.nr = 0 ∨ arg32 ev.nr = 1) ∧
    (ev.Failed ∨ ∃ b n bs, ev.IsWriteFault 1 b n bs ∧ ev.ret.toNat < n) ∧ ∀ e ∈ post, arg32 e.nr ≠ 0 ∧ arg32 e.nr ≠ 1

/-- What a run of `admin` has read and written so far, the events `evs`: with `name` the bytes it has read from standard
input (descriptor 0), at most `nameMax` of them, what it has written to standard output (descriptor 1) is a first part
of `line name`. -/
def SoFar (evs : List Event) : Prop :=
  (Input 0 evs).length ≤ nameMax ∧ Output 1 evs <+: line (Input 0 evs)

/-- How a run of `admin` that got past the startup ends, `out`, with the system calls `evs` (the C library's startup's,
`malloc`'s, the `read`, the `write`s, the exit's memory calls): with `name` the bytes the run read from standard input
(descriptor 0), at most `nameMax` of them, exactly one of:
- exit status 0, and standard output (descriptor 1) received exactly `line name`;
- exit status 1, a first part of `line name` written, the last `read` or `write` one that failed or a `write` that took
  fewer bytes than asked (`LastShort`);
- exit status 2 (a `malloc` returned a null pointer), nothing read and nothing written;
- killed in a `write` (`Outcome.KilledInWrite`: `SIGPIPE`, `SIGXFSZ`), a first part of `line name` written. -/
def Done (out : Outcome) (evs : List Event) : Prop :=
  (Input 0 evs).length ≤ nameMax ∧
    ((out = .exited .exitGroup 0 ∧ Output 1 evs = line (Input 0 evs)) ∨
      (out = .exited .exitGroup 1 ∧ Output 1 evs <+: line (Input 0 evs) ∧ LastShort evs) ∨
      (out = .exited .exitGroup 2 ∧ Output 1 evs = [] ∧ Input 0 evs = []) ∨
      (out.KilledInWrite ∧ Output 1 evs <+: line (Input 0 evs)))

/-! ## The file's code -/

/-- The file's ELF header (`ZellicX86/Spec/Elf.lean`). -/
noncomputable def elfHdr : ElfHeader := ElfHeader.read Clients.Admin.file.img

/-- The file's program headers (`e_phnum` of them at `e_phoff`). -/
noncomputable def phdrs : List Phdr := readPhdrs Clients.Admin.file.img elfHdr.phoff elfHdr.phnum

/-- The file's executable segment (its loadable program header with the execute flag) as the code a run of the program
may execute: its bytes at its address (`execSegments`). -/
noncomputable def code : List (Addr × List Byte) := execSegments Clients.Admin.file.img phdrs

/-- The code glibc's startup executes before it calls `main` (`C.CStart.startup`'s code list): the file's executable
segments (`code`) without `main`'s bytes (its address and its symbol's size, `Exe.seg`; `codeWithout`). -/
noncomputable def startCode : List (Addr × List Byte) :=
  codeWithout code (Exe.seg Clients.Admin.file.blob "main")

/-! ## The processor, the launches and the vDSO -/

/-! The carve-outs that do not depend on the program, the same for every program's demonstration
(`Program/Demo.lean`): the processor (`ThisProcessor`, with `cpuidRecord`, `SameAnswer`, `subleaflessLeaves`), the
launches (`DemoArgs`, with `tunableVars`, `NoTunables`) and the kernel's vDSO (`ThisVdso`). -/
export Glibc243Ubuntu.Program.Demo (cpuidRecord SameAnswer subleaflessLeaves ThisProcessor tunableVars NoTunables
  DemoArgs ThisVdso)

/-! ## The launch's stack and limits, and the runs -/

/-- The bytes of stack below its entry `rsp` that glibc's startup may write, for the launches the theorem covers: its own
frames, with a copy of `LD_LIBRARY_PATH`'s value of at most `libPathMax` bytes on it (`_dl_init_paths`' `strdupa`,
`elf/dl-load.c`, the startup's only use of stack that grows with its input), and the stack `main` (`0x420` bytes)
and the exit use below `main`'s entry, which lies in the startup's
frame. Measured on this program: the startup writes 4,616 bytes below the initial `rsp` with no `LD_LIBRARY_PATH` and
8,840 with one of 8,192 bytes, and calls `main` 280 bytes below it. The declared budget is 16 KiB. -/
abbrev startStack : Nat := 0x4000

/-- **Demonstration carve-out**: the launch's memory limits, `a` the arguments, environment and limits `execve` started
the process with (the limits inherited from the process that called it): the soft `RLIMIT_DATA` at least 4 MiB and the
soft `RLIMIT_AS` at least 8 MiB above the initial stack's strings (`RLIM_INFINITY` meets both). What the runs of `holds`
map, with their bounds: the image's segments (`0x400000` to the writable segment's end below `0x4b8000`, under 1 MiB;
the writable segment's 12 pages count as data), the initial stack (its strings' pages and the 128 KiB `execve` adds,
`StackRoom`, within which the runs stay), the vDSO (`ThisVdso`: a few pages), and the break's growth, at most 3 MiB
(the startup's; `main`'s blocks lie in the top chunk the startup leaves); nothing by `mmap` where
the kernel grants `brk`. So the data the kernel counts (`check_data_rlimit` at a `brk`: the break's distance from its
start and the data segment's size; `may_expand_vm`'s `data_vm`) stays below 4 MiB and the mappings (`total_vm`) below 8
MiB with the strings: no `brk` or `mmap` of these runs, and no mapping `execve` makes, is refused for the limits
(`mm/mmap.c` `brk`, `may_expand_vm`; `mm/vma.c`). Measured on `admin` (on the development machine, one argument): with `RLIMIT_DATA`
192 KiB and `RLIMIT_AS` 2 MiB it runs to its end; with `RLIMIT_DATA` 64 KiB the startup's `brk` is refused and it ends
with status 127 ("cannot create search path array"), with 44 KiB or less (the writable segment's 12 pages) `execve`
itself kills it (`SIGSEGV`).

The model's `execve` checks `RLIMIT_AS` and `RLIMIT_DATA` as the kernel does (`ZellicX86/Spec/Linux/Exec.lean`), so a launch
whose limits are too small for the image has no `ExecStart` and is not among `holds`' runs anyway. Its `brk` and `mmap` leave a refusal
for them to `Request.memFail` (with the kernel's other reasons), which `DemoEnv`'s `Heap.MemGranted` rules out whatever
the reason. Thus `DemoLimits` is an explicit restriction on the launches covered by the demonstration; the syscall
models leave refusals for these limits to the environment request. -/
def DemoLimits (a : ExecArgs) : Prop :=
  0x400000 ≤ (a.signal.rlimits RLIMIT_DATA).cur.toNat ∧
    0x800000 + pageUp (8 + a.strings.length) ≤ (a.signal.rlimits RLIMIT_AS).cur.toNat

/-- The runs `holds` covers, apart from `DemoEnv`'s memory: undisturbed (`Undisturbed`), `/proc/self/exe` procfs's link
(`ProcSelfExe`: glibc's startup reads the executable's path there). -/
def StartEnv (o : Oracle) : Prop :=
  Undisturbed o ∧ ProcSelfExe o

/-- **Demonstration carve-out**: the runs of the demonstration: undisturbed, with `/proc/self/exe` procfs's link
(`StartEnv`), in which the kernel never refuses memory for want of it (`Heap.MemGranted`: no
`Request.memFail`). Placement checks can still fail independently of this hypothesis (`sysBrk`, `Request.place`),
so `malloc` may return null in such a run. A refusal for the process's limits, set by it or inherited from the one
that started it, is one of those it rules out: the `brk` and `mmap` models leave refusals for them to this request. So
it also leaves out every launch whose `RLIMIT_DATA` or `RLIMIT_AS` is too small for the startup's and `main`'s memory
(with a data limit of 64 KiB the real startup ends with status 127), whatever `DemoLimits` says. -/
def DemoEnv (o : Oracle) : Prop := StartEnv o ∧ Heap.MemGranted o

/-! ## The theorem -/

/-- **`admin` end to end, under the demonstration's carve-outs**: every process started from `admin` (`Launch.Of`) on a processor a
real machine can be (`Profile.Consistent`), on a kernel whose stack guard gap and vDSO image are of ordinary size
(`LinuxBoot.Modest`), with room on its stack for the startup (`StackRoom`), the demonstration's launch
(`DemoArgs`: not secure, no tunables, no `LD_LIBRARY_PATH`) with its memory limits at least the runs' needs
(`DemoLimits`) on the development VM's virtual CPU (`ThisProcessor`) and kernel's vDSO (`ThisVdso`), on every run the
demonstration admits (`DemoEnv`):
- *safety*: at every point, what it has read and written is as `SoFar` says (standard output a first part of
  `line name`), and if it has ended, it ended (`Outcome.Modelled`) having made only a startup's system calls (then in
  any way the model describes), or as `Done` says;
- *liveness*: if it reaches `main`'s entry, it ends, as `Done` says.

Its first conjunct is a fact about the file, proved with the rest: the file defines the symbol
`__libc_single_threaded` (`Exe.HasData`). -/
def holds : Prop :=
  Exe.HasData Clients.Admin.file.blob ["__libc_single_threaded"] ∧
  ∀ l : Launch, l.Of Clients.Admin.file.img Clients.Admin.file.size → l.prof.Consistent →
    l.prof.linux.Modest → StackRoom l.args (startStack + 32) →
    DemoArgs l.args → DemoLimits l.args → ThisProcessor l.prof → ThisVdso l.prof.linux →
    Always l.prof DemoEnv l.s₀ (fun _ evs => SoFar evs)
      (fun out evs => (out.Modelled ∧ ∀ ev ∈ evs, C.Event.IsStartup ev) ∨ Done out evs) ∧
    EndsIf l.prof DemoEnv l.s₀ (fun s _ => s.cpu.rip = Exe.entry Clients.Admin.file.blob "main") Done

end Clients.Admin
