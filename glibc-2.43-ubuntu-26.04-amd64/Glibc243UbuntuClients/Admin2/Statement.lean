import ZellicX86.Spec.Lib.C.Start
import ZellicX86.Spec.Process
import ZellicX86.Spec.Executable
import ZellicX86.Spec.ExecCode
import Glibc243UbuntuClients.Program.Demo
import Glibc243UbuntuClients.Files.Admin2
/-!
# Statement: `admin2` greets a name without a newline, rejects one with a newline, and never reports an admin

`clients/admin2.c`'s program, as the program `clients/admin2` has it (`gcc -O2 -static` against this build's `libc.a`):

```c
int main(void) {
  char *name = malloc(NAME_SIZE);              // NAME_SIZE 32
  volatile char *admin = malloc(1);
  if (name == NULL || admin == NULL) return 2;
  *admin = 0;
  ssize_t n = read(0, name, NAME_SIZE);
  if (n < 0) return 1;
  for (ssize_t i = 0; i < n; i++) {
    if (name[i] == '\n') {
      write(2, "admin2: bad name\n", 17);
      return 3;
    }
  }
  if (write(1, "Hello, ", 7) != 7) return 1;
  if (write(1, name, n) != n) return 1;
  if (write(1, "!\n", 2) != 2) return 1;
  if (*admin) {
    if (write(1, "admin: yes\n", 11) != 11) return 1;
  } else {
    if (write(1, "admin: no\n", 10) != 10) return 1;
  }
  return 0;
}
```

`holds` says, for glibc 2.43 as this program links it, with glibc's own code proved wherever it is, for the
launches, processors, vDSOs and runs that the carve-outs of `Program/Demo.lean` admit (admin's, but for its memory
limits), on every run:
- *safety*, at every point (`Always`): with `name` the bytes the run has read from standard input so far, at most 32 of
  them, what it has written to standard output is a first part of `line name`, and nothing if `name` holds a newline
  (`SoFar`); and if the process has ended, it ended (exited or was killed: `Outcome.Modelled`) having made only a
  startup's system calls (then in any way the model describes: any exit status or killing signal), or as `Done` says;
- *liveness*, on every run that reaches `main`'s entry: the process ends, as `Done` says.

A run need not get past the startup (glibc's may loop for ever on the clock's readings for the heap's key or end the
process after a refused memory request): the safety part covers those runs, and `holds` does not say that a run
gets to `main`. The strings `main` writes are in the
file's read-only data, which the startup hands `main` as `execve` loaded it. The theorem `holds_proof : holds` is proved by the export `admin2` (`checks/admin2/`).
-/
namespace Clients.Admin2
open ZellicX86 Glibc243Ubuntu Glibc243Ubuntu.Program.Demo

/-- The most bytes a name has: the name buffer's size, `read(0, name, 32)`. -/
def nameMax : Nat := 32

/-- The newline byte (`utf8 "\n"`'s one byte, 10). -/
def newline : Byte := 10

/-- The name `name` (the bytes the `read` delivered, whatever they are) holds a newline byte somewhere. -/
def HasNewline (name : List Byte) : Prop := newline ∈ name

/-- The lines the program writes to standard output for a name without a newline: `Hello, `, the name, `!` and a
newline, then `admin: no` and a newline. The flag's line is the output's fixed end: a name may itself contain the text
`admin: yes`, but not a newline, so not on a line of its own. -/
def line (name : List Byte) : List Byte := utf8 "Hello, " ++ name ++ utf8 "!\n" ++ utf8 "admin: no\n"

/-- The line the program writes to standard error for a name with a newline. -/
def errLine : List Byte := utf8 "admin2: bad name\n"

/-- The last `read` or `write` among the events `evs` (system call 0 or 1, by `rax`'s low 32 bits as the kernel reads
it) failed (`Event.Failed`: it returned an error number), or was a `write` to descriptor 1 that took fewer bytes than it
was asked to write. Calls of other kinds may follow it: the memory calls of the library's exit. -/
def LastShort (evs : List Event) : Prop :=
  ∃ pre ev post, evs = pre ++ ev :: post ∧ (arg32 ev.nr = 0 ∨ arg32 ev.nr = 1) ∧
    (ev.Failed ∨ ∃ b n bs, ev.IsWriteFault 1 b n bs ∧ ev.ret.toNat < n) ∧ ∀ e ∈ post, arg32 e.nr ≠ 0 ∧ arg32 e.nr ≠ 1

/-- The last `read` or `write` among the events `evs` was a `write` of `errLine` to descriptor 2 (`Event.IsWrite`:
it took a first part of it, or failed). Calls of other kinds may follow it: the memory calls of the library's exit. -/
def LastErr (evs : List Event) : Prop :=
  ∃ pre ev post, evs = pre ++ ev :: post ∧ (∃ b, ev.IsWrite 2 b errLine) ∧
    ∀ e ∈ post, arg32 e.nr ≠ 0 ∧ arg32 e.nr ≠ 1

/-- What a run of `admin2` has read and written so far, the events `evs`: with `name` the bytes it has read from
standard input (descriptor 0), at most `nameMax` of them, what it has written to standard output (descriptor 1) is a
first part of `line name`, and nothing if `name` holds a newline. -/
def SoFar (evs : List Event) : Prop :=
  (Input 0 evs).length ≤ nameMax ∧ Output 1 evs <+: line (Input 0 evs) ∧
    (HasNewline (Input 0 evs) → Output 1 evs = [])

/-- How a run of `admin2` that got past the startup ends, `out`, with the system calls `evs` (the C library's
startup's, `malloc`'s, the `read`, the `write`s, the exit's memory calls): with `name` the bytes the run read from
standard input (descriptor 0), at most `nameMax` of them, exactly one of:
- exit status 0, `name` without a newline, and standard output (descriptor 1) received exactly `line name`;
- exit status 1, `name` without a newline, a first part of `line name` written, the last `read` or `write` one that
  failed or a `write` that took fewer bytes than asked (`LastShort`);
- exit status 2 (a `malloc` returned a null pointer), nothing read and nothing written;
- exit status 3, `name` with a newline, nothing written to standard output, the last `read` or `write` the `write` of
  `errLine` to standard error (`LastErr`; it may have taken only a first part of it, or failed);
- killed in a `write` (`Outcome.KilledInWrite`: `SIGPIPE`, `SIGXFSZ`), a first part of `line name` written, nothing if
  `name` holds a newline. -/
def Done (out : Outcome) (evs : List Event) : Prop :=
  (Input 0 evs).length ≤ nameMax ∧
    ((out = .exited .exitGroup 0 ∧ ¬ HasNewline (Input 0 evs) ∧ Output 1 evs = line (Input 0 evs)) ∨
      (out = .exited .exitGroup 1 ∧ ¬ HasNewline (Input 0 evs) ∧ Output 1 evs <+: line (Input 0 evs) ∧
        LastShort evs) ∨
      (out = .exited .exitGroup 2 ∧ Output 1 evs = [] ∧ Input 0 evs = []) ∨
      (out = .exited .exitGroup 3 ∧ HasNewline (Input 0 evs) ∧ Output 1 evs = [] ∧ LastErr evs) ∨
      (out.KilledInWrite ∧ Output 1 evs <+: line (Input 0 evs) ∧ (HasNewline (Input 0 evs) → Output 1 evs = [])))

/-- The file's ELF header (`ZellicX86/Spec/Elf.lean`). -/
noncomputable def elfHdr : ElfHeader := ElfHeader.read Clients.Admin2.file.img

/-- The file's program headers (`e_phnum` of them at `e_phoff`). -/
noncomputable def phdrs : List Phdr := readPhdrs Clients.Admin2.file.img elfHdr.phoff elfHdr.phnum

/-- The file's executable segment (its loadable program header with the execute flag) as the code a run of the program
may execute: its bytes at its address (`execSegments`). -/
noncomputable def code : List (Addr × List Byte) := execSegments Clients.Admin2.file.img phdrs

/-- The code glibc's startup executes before it calls `main`: the file's executable segments (`code`) without `main`'s
bytes (its address and its symbol's size, `Exe.seg`; `codeWithout`). -/
noncomputable def startCode : List (Addr × List Byte) :=
  codeWithout code (Exe.seg Clients.Admin2.file.blob "main")

/-- The bytes of stack below its entry `rsp` that glibc's startup may write, `main`'s and the exit's below `main`'s
entry included: the same 16 KiB bound as admin's statement's `startStack`, based on measurements of `admin`. -/
abbrev startStack : Nat := 0x4000

/-- **`admin2` end to end, for the demonstration**: every process started from `admin2` (`Launch.Of`) on a processor a
real machine can be (`Profile.Consistent`), on a kernel whose stack guard gap and vDSO image are of ordinary size
(`LinuxBoot.Modest`), with room on its stack for the startup (`StackRoom`: `startStack` and `_start`'s 32 bytes), the
demonstration's launch (`DemoArgs`: not secure, no tunables, no `LD_LIBRARY_PATH`) on the development VM's virtual CPU
(`ThisProcessor`) and kernel's vDSO (`ThisVdso`), on every run the demonstration admits (`DemoRuns`: undisturbed,
`/proc/self/exe` procfs's link, the kernel never refusing memory for want of it):
- *safety*: at every point, what it has read and written is as `SoFar` says, and if it has ended, it ended
  (`Outcome.Modelled`) having made only a startup's system calls (then in any way the model describes), or as `Done`
  says;
- *liveness*: if it reaches `main`'s entry, it ends, as `Done` says. -/
def holds : Prop :=
  ∀ l : Launch, l.Of Clients.Admin2.file.img Clients.Admin2.file.size → l.prof.Consistent →
    l.prof.linux.Modest → StackRoom l.args (startStack + 32) →
    DemoArgs l.args → ThisProcessor l.prof → ThisVdso l.prof.linux →
    Always l.prof DemoRuns l.s₀ (fun _ evs => SoFar evs)
      (fun out evs => (out.Modelled ∧ ∀ ev ∈ evs, C.Event.IsStartup ev) ∨ Done out evs) ∧
    EndsIf l.prof DemoRuns l.s₀ (fun s _ => s.cpu.rip = Exe.entry Clients.Admin2.file.blob "main") Done

end Clients.Admin2
