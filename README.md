# Verified x86-64 Linux binaries: statements and checkable proofs

This repository states, in Lean 4, theorems about machine code as it runs under Linux on x86-64: compiled C functions and
statically linked programs, taken as binaries (the bytes the compiler and linker produced, not their source). It
carries the theorems' **statements** as Lean source, and their **proofs** as exported Lean terms that anyone can check
with Lean's kernel. The tools that produced the proofs are not part of this release (see "How the proofs were made").

Every theorem is about one binary or function and says what it does on every run its hypotheses admit: for a
function, its result, the memory it may write and that it makes no system call; for a program, what it
reads from standard input and writes to standard output, and how it may end. What the theorems mean
rests on three things, all in this repository or in Lean itself:

1. **The model** (`ZellicX86/Spec/`). It covers x86-64 user-mode execution (decoding, the instructions' semantics,
   memory, faults) and the Linux process around it (`execve`'s initial state, system calls, signals as far as
   modelled). It also holds the vocabulary the statements are written in (contracts, `ImplementsCall`, `Always`,
   `EndsIf`, …). Anything the model does not cover ends in an explicit "not modelled" outcome, and every theorem
   here proves that its runs never reach one. (A launch at which the model's `execve` itself is not modelled is
   outside the theorems' hypotheses.) `MODEL-LIMITATIONS.md` says where the model stops. It also names the few places
   where the model, instead of leaving a choice open, follows the behaviour observed on the processor it was checked
   against.
2. **The statements** (`Examples/*/Statement.lean`, `glibc-2.43-ubuntu-26.04-amd64/Glibc243UbuntuClients/*/`): each
   theorem's proposition, with the definitions it uses.
3. **The loader** (`ZellicX86/Load/FileImage.lean`): `#file_image "path" sha256 "…"` reads a binary into Lean
   constants and refuses it unless its SHA-256 is the one written in the source, so a statement about a program is
   about exactly that file.

## Status: a research preview

This is a research preview, not an audited result. Lean's kernel guarantees that each proof proves its statement. It
cannot tell whether the statement means what it is meant to: that rests on the model of the processor and of Linux,
and on the definitions the statements are built from. None of these has been audited yet, and much of them has not
yet been read by a human. Expect gaps and mistakes in them. To illustrate, the mistakes found during development so
far have broadly been of two kinds:

- **The model differs from real hardware in some corner.** For example, where two faults are possible at once, the
  model may report a different one than the processor does. A theorem then holds of the model, but not of every run
  on a real machine.
- **A statement is vacuous.** Its hypotheses cannot all hold together, so the theorem is true but says nothing. One
  case: an assumption about addresses that are symbolic in the statement looked harmless, but could not hold once
  the addresses were known.

## What is stated

| theorem | binary | in short |
|---|---|---|
| `Memcmp.gccO1_holds`, `gccO2_holds`, `gccOs_holds`, `clangO2_holds`, `clangOs_holds` (each `Memcmp.holds` of its build, `Examples/Memcmp/Statement.lean`; the theorems are named in `ReleaseChallenges/`) | `memcmp.c` compiled by GCC 15 (`-O1`, `-O2`, `-Os`) and Clang 21 (`-O2`, `-Os`): `Examples/Memcmp/Code.lean` | each build, placed at any address, implements C's `memcmp` on every processor. |
| `Clients.Admin.holds`, proved by `Clients.Admin.holds_proof` (`Glibc243UbuntuClients/Admin/Statement.lean`; the proof is the export) | `clients/admin`, a small C program (`clients/admin.c`; these paths under `glibc-2.43-ubuntu-26.04-amd64/`) statically linked against glibc 2.43 | under the hypotheses below, the program never reports an admin: its standard output is always a first part of `Hello, <name>! admin: no` and a newline. |
| `Clients.Admin2.holds`, proved by `Clients.Admin2.holds_proof` (`Glibc243UbuntuClients/Admin2/Statement.lean`) | `clients/admin2` (`clients/admin2.c`): admin, but it rejects a name that contains a newline, and writes its answer as two lines | as admin, but the output is a first part of the two lines `Hello, <name>!` and `admin: no`, and a name with a newline is rejected. |

The table only summarises. What each theorem says precisely follows, and what it assumes is in the next section.

### The functions' theorems

They say that the code implements a contract (`ImplementsCall`). Take every call of the code at its entry that is a
call as `CallOf` defines it: the calling convention, the contract's precondition, a thread that can make a call, and
memory for the call's data that is ordinary (for `memcmp`, see "What the theorems assume"). Take it on every run in
which no other agent acts on the process (`Undisturbed`). Every such call:

- returns to its caller, with the contract's postcondition;
- keeps the registers the calling convention preserves;
- writes only the memory the contract allows;
- until it returns, executes only the code the statement names.

So it does not fault, loop for ever or reach a case the model does not cover. For `memcmp`, the postcondition is
that the sign of the result is the order of the two byte strings, for every length. The call makes no system call,
and writes nothing but its return address's slot (and the ids the kernel itself writes into the thread's `rseq` area,
if it has one, at every return to user mode).

### The programs' theorems

They are stated with `Always` (what holds at every point of every run) and `EndsIf` (that every run that reaches a
given point ends, and how). For admin, on every launch and run the hypotheses admit (next section):

- **Output.** What the process writes to standard output (its `write`/`writev` calls on descriptor 1) is always a
  first part of `Hello, <name>! admin: no` and a newline. `<name>` is the at most 32 bytes that its `read`s on
  descriptor 0 delivered.
- **How a run may end.** Every run that ends either ends as `Done` lists (below), or ends in some other way the model
  describes (not "not modelled") having made only system calls of the startup's class (`Event.IsStartup`: none of
  them reads a descriptor, and none writes to one but standard error).
- **From `main` on.** If the process reaches `main`, it ends, in one of the ways `Done` lists:
  - exit 0, having written the whole line;
  - exit 1, after a failed or short `read` or `write`;
  - exit 2, having read and written nothing (`main`'s path when a `malloc` returns null);
  - killed by `SIGPIPE` or `SIGXFSZ` (a `write` to a pipe without readers, or past the file size limit).

  `main`'s entry is the address the file's symbol table gives `main` (`Exe.entry`); both files define it.
- **No claim that `main` is reached.** **The theorem does not say that glibc's startup reaches `main`**, nor that a run
  that does not get there ends. Of such a run, it says only what the first two points say.
- **glibc runs from the file.** glibc's code in the file (its startup, `malloc`, `free`, `read`, `write`, the exit)
  runs from the file's bytes, with no contract of glibc assumed.
- **One more conjunct**, proved, not assumed: the file defines the symbol `__libc_single_threaded` (`Exe.HasData`).

admin2's theorem says the same, but for what is written and one more way to end:

- A name with a newline (among the at most 32 bytes read) is rejected. Nothing is written to standard output. If the
  process reaches `main`, it ends with exit 3, after a `write` of `admin2: bad name` to standard error (which may be
  partial or fail), or it is killed by `SIGPIPE` or `SIGXFSZ`.
- A name without a newline gives at most the two lines `Hello, <name>!` and `admin: no`, and exactly those when the
  exit status is 0.
- admin2's statement has no `Exe.HasData` conjunct.

### What the theorems assume

The assumptions are hypotheses in the statements themselves. Each is a named definition with its own docstring.

- **`memcmp`**: any processor (every `Profile`) and any placement of the code (`CodeIn`). Each call must be a call as
  `CallOf` and the contract define it:
  - the System V calling convention: the stack aligned, `DF` clear, the x87 stack empty;
  - a thread without single-stepping, alignment checking, a user shadow stack, `CPUID` faulting or an active `rseq`
    critical section (`Ready`);
  - both strings readable, apart from the return address's slot and the code;
  - both strings on ordinary pages (`Footprint.Ok`): not the vDSO's data or lazily freed pages, and no page of them
    aliased through another virtual page;
  - the run undisturbed.
- **admin and admin2.** Each statement has the same hypotheses, except `DemoLimits`, which only admin's has.
  - **Any start.** Every start `execve` can give the program (`Launch.Of`): any arguments, environment and
    credentials a caller can pass; any kernel configuration and any choice the kernel can make; any open descriptors,
    signal mask and dispositions.
  - **Processor, kernel and stack.** A processor profile whose features agree with its `CPUID` answers (`Profile.Consistent`). A
    kernel whose stack guard gap and vDSO are of ordinary size (`LinuxBoot.Modest`). Room on the stack for the startup
    (`StackRoom`): a soft stack limit of at least 128 KiB above the argument strings, and at most about 13,000
    argument and environment strings.
  - **The launch** (`DemoArgs`). Not a secure exec (`AT_SECURE` 0: no set-user-ID or set-group-ID file, no file
    capabilities). No environment string setting `GLIBC_TUNABLES` or one of the tunables' nine aliases. No
    `LD_LIBRARY_PATH`.
  - **admin's limits** (`DemoLimits`, admin only). A soft `RLIMIT_DATA` of at least 4 MiB, and a soft `RLIMIT_AS` of
    at least 8 MiB above the strings. The proof does not need it. It keeps the covered launches within what the real
    kernel allows (see `Heap.MemGranted` below).
  - **The processor** (`ThisProcessor`). Every CPU answers the `CPUID` queries glibc's startup makes as the
    development machine's virtual CPU does, hypervisor bit and topology included, but for the APIC ids and the L3
    size. That machine is a KVM guest on an AMD Ryzen 9 7950X3D; a bare-metal processor does not meet this. So the
    theorems cover the paths glibc takes on that CPU.
  - **The vDSO** (`ThisVdso`). The vDSO is the code and data the kernel maps into every process. The hypothesis: the
    kernel maps none, or one whose two pages begin with the development kernel's ELF tables. Its code is not
    assumed, and no theorem here assumes a contract of it. glibc's startup reads these tables, as it reads `CPUID`.
  - **The runs** (`DemoEnv` in admin's statement, `DemoRuns` in admin2's: the same conditions):
    - no other agent acts on the process (`Undisturbed`): no signal from outside, no other writer of its memory,
      registers or files, no change of its limits;
    - `/proc/self/exe` is procfs's link, or absent (`ProcSelfExe`; glibc's startup reads the executable's path
      there);
    - the kernel grants every memory request the model leaves to the environment (`Heap.MemGranted`). No refusal
      for want of memory, nor for the process's own `RLIMIT_DATA`, `RLIMIT_AS` or `RLIMIT_MEMLOCK`,
      `vm.max_map_count` or the security module. (A request for pages that are not free still fails.) So for a
      launch whose limits are too small for the program, the theorem covers no real run. admin's `DemoLimits` leaves
      those launches out; admin2's statement does not.
  - **Liveness** ("it ends") is relative to the model, in which every system call returns. A `read` that would block
    for ever is not covered.
  - **No contract of a library.** Every function the programs run, glibc's and libgcc's included, runs from the
    bytes of the file. That does not make these theorems a verification of glibc. Not every glibc function the
    programs run is proved on its own in full generality: some are proved only under conditions that hold for the
    calls these programs make. What is claimed is the theorems about the two programs.

## How to check

A check has two sides: the **challenge**, the theorem's statement built from this repository's source and proved by
`sorry`, and the **solution**, our proof, which you download. Each side is an **export**, a file of Lean's kernel terms;
Lean's `lake comparator` checks that the solution proves exactly the challenge's statement. Each theorem has an
**id** (`memcmp-gcc-o1`, …, `admin`; the directories in `checks/`).

You need:

- [elan](https://github.com/leanprover/elan), Lean's toolchain manager (on Linux:
  `curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh`), with the toolchains
  `leanprover/lean4:v4.34.0` (the statements') and `leanprover/lean4:v4.35.0` (its `lake comparator` and kernels):
  `elan toolchain install leanprover/lean4:v4.34.0 leanprover/lean4:v4.35.0` (≈ 6 GB of disk together);
- `git`, `curl`, `zstd`, `sha256sum`;
- for the comparator's sandbox, `bwrap` with unprivileged user namespaces (see "Environment" below);
- optionally, Rust's `cargo`, to build a newer nanoda (see "Independent kernels").

0. **The exporter**, once, beside this repository (it builds with Lean 4.34, its own `lean-toolchain`), at the commit
   of its tag `v4.34.0`:

       (git clone https://github.com/leanprover/lean4export ../lean4export && cd ../lean4export &&
          git checkout --detach 076e8e57707e813375e8f9da8bf989799ace9680 && lake build)

   The parentheses run the command in a subshell, so its `cd` does not change your shell's directory; step 2 uses
   them the same way. All commands here run in this repository's checkout, and take the exporter at
   `../lean4export/.lake/build/bin/lean4export`.
1. **The statements elaborate and the binaries are the ones named:**

       lake build

   builds the model and every statement's proposition with Lean only (no dependency, no download; the theorems
   themselves are stated by the challenges, step 2), and `#file_image` checks each program's SHA-256, printing one
   `info:` line per file with its size. The functions' bytes are written out in `Examples/*/Code.lean` instead (see
   "Trust base"). It takes a few minutes at most, and under 2 GB of memory.
2. **The proofs.** Download the proof exports (`ID.solution.ndjson.zst`, one per theorem id:
   `memcmp-gcc-o1`, `memcmp-gcc-o2`, …; `ls checks` lists the ids) from
   `https://research-assets.zellic.io/x86fv/proofs/` into `exports/`, and check them against the checksums this
   repository carries (`exports/SHA256SUMS`). The files:

   - <https://research-assets.zellic.io/x86fv/proofs/memcmp-gcc-o1.solution.ndjson.zst>
   - <https://research-assets.zellic.io/x86fv/proofs/memcmp-gcc-o2.solution.ndjson.zst>
   - <https://research-assets.zellic.io/x86fv/proofs/memcmp-gcc-os.solution.ndjson.zst>
   - <https://research-assets.zellic.io/x86fv/proofs/memcmp-clang-o2.solution.ndjson.zst>
   - <https://research-assets.zellic.io/x86fv/proofs/memcmp-clang-os.solution.ndjson.zst>
   - <https://research-assets.zellic.io/x86fv/proofs/admin.solution.ndjson.zst>
   - <https://research-assets.zellic.io/x86fv/proofs/admin2.solution.ndjson.zst>

   The same with `curl` and the check:

       (cd exports && for f in $(awk '{print $2}' SHA256SUMS); do
          curl -fLO "https://research-assets.zellic.io/x86fv/proofs/$f"; done)
       (cd exports && sha256sum -c --ignore-missing SHA256SUMS)

   Then, for one id (`memcmp-gcc-o1` here):

       ln -f exports/memcmp-gcc-o1.solution.ndjson.zst checks/memcmp-gcc-o1/solution.ndjson.zst
       bash checks/memcmp-gcc-o1/verify-source.sh . ../lean4export/.lake/build/bin/lean4export

   (`ln -f` puts the export beside the check's script without a second copy; `cp` works as well) or for every id:

       opts=""   # --inadvisably-no-sandbox where the sandbox cannot run: see "Environment"
       failed=""
       for id in $(ls -r checks); do   # (reverse order: the quick checks of functions first)
         ln -f exports/$id.solution.ndjson.zst checks/$id/solution.ndjson.zst &&
           bash checks/$id/verify-source.sh . ../lean4export/.lake/build/bin/lean4export $opts || failed="$failed $id"
       done
       if [ -n "$failed" ]; then echo "FAILED:$failed"; false; else echo "all passed"; fi

   (it ends non-zero if any check failed or any export is missing)

   `verify-source.sh` builds the theorem's challenge (in `ReleaseChallenges/`) with Lean 4.34 and exports it. Then
   it runs Lean 4.35's `lake comparator` on that challenge and the downloaded proof export, configured by
   `checks/ID/comparator.json`. The comparator accepts only if:

   - the solution proves exactly the challenge's proposition;
   - every constant the statement mentions is the same in both;
   - no axiom occurs but `propext`, `Quot.sound` and `Classical.choice`;
   - Lean's kernel replays the whole proof and accepts it, and so do the independently implemented kernels that
     Lean 4.35 ships (con-leche and con-ron, and for the functions also nanoda: see "Independent kernels").

   The kernels run one after the other. Each is announced by a line (`Running Lean default kernel on solution`, …)
   and prints nothing more until its verdict. A passing check ends with `Your solution is okay!` and exit status 0.

   Building the challenge prints Lean's warning ``declaration uses `sorry` `` for the challenge's file. That is
   expected. The challenge is the theorem's statement without its proof, as `lake comparator` requires (the theorems
   it names are "complete in the solution, but `sorry` in the challenge"). The proof comes from the export. A proof
   that used `sorry` would be rejected: `sorry` is an axiom (`sorryAx`) that the configuration does not permit.

   Time and memory, on one core:

   - the functions: a few minutes at most in all (each `memcmp` build ≈ 20 s), under 1.5 GB of memory; their exports are a few MB
     each;   - admin and admin2: 45 to 60 minutes each, and ≈ 14 GB of free memory (the comparator's peak is 13.4 GB, almost
     all of it the kernels' replay of the proof). con-leche and con-ron take a few minutes each. Lean's own kernel
     runs last and takes most of the time (≈ 38 minutes in one reader's run), printing nothing until its verdict;   - disk: the toolchains (≈ 6 GB) and the exporter (≈ 0.25 GB); the downloads (≈ 1.1 GB in all);
     and the export being checked, uncompressed while it is checked and removed after (≈ 4.5 GB for
     admin or admin2).

### Environment

`lake comparator` runs the checkers that read the downloaded proof export in a sandbox (`bwrap`), which needs
unprivileged user namespaces. A container or VM may not have them. There the check stops with `bwrap: Creating new
namespace failed` (`ENOSPC` or `EPERM`) for every kernel. It then prints for each kernel that it `rejected the
solution` (`con-leche kernel rejected the solution`, …, `Lean default kernel rejected the solution`), and ends with
exit status 1. No kernel has actually run: that is the environment, not the proof. In such an environment, give
`verify-source.sh` the comparator's option to run without the sandbox (in the loop above:
`opts="--inadvisably-no-sandbox"`):

    bash checks/ID/verify-source.sh . /path/to/lean4export --inadvisably-no-sandbox

This runs the same checks, Lean's kernel included, without the sandbox. The comparator then prints `WARNING:
Sandbox disabled, this run is not trustworthy.` What the option gives up is the sandbox's protection of your machine
while the checkers read a file you downloaded. That protection is a defence against an export crafted to exploit a
bug in a checker, and so to take over the check (or your machine). An export that does not do that gets the same
verdict either way. Prefer the sandboxed command where it runs, above all for an export you have reason to distrust.

### Checking the check

`verify-source.sh` is short and uses Lean's own tools only; read it before you run it. You can also do its three
steps by hand, or with your own challenge, without trusting anything of ours but the statements' source:

- **The challenge.** `ReleaseChallenges/<ID with `_` for `-`>.lean` (the `challenge_module` of
  `checks/ID/comparator.json`) imports the theorem's statement module and states the theorem by
  `sorry`, nothing else. Any file of your own that does the same, with the theorem's name as `comparator.json`'s
  `theorem_names` gives it, serves as well. Kept outside this repository (in `DIR`), it is built from the repository's
  checkout with the repository's modules on the path:

      # DIR/MyCh.lean:  import Examples.Memcmp.Statement
      #                 theorem Memcmp.gccOs_holds : Memcmp.holds Memcmp.gccOs := by sorry
      lake env lean --root=DIR -o DIR/MyCh.olean DIR/MyCh.lean
- **Its export.** `lake env /path/to/lean4export MODULE -- THEOREM <the constants the script names>` exports the
  theorem's statement, and every constant it mentions, from the modules Lean built from this repository's source.
  For a module of your own in `DIR`: `lake env sh -c 'LEAN_PATH=DIR:$LEAN_PATH exec /path/to/lean4export MyCh -- …'`.
  The further constants the script names are those the kernel treats specially (`Nat`'s operations, the
  constructors of `String` and `Char` literals, `eagerReduce`), the auxiliary constants Lean's elaborator inserts
  (`optParam`, `autoParam`, …) and the permitted axioms, which `lake comparator` requires both exports to contain.
  `lean4export`
  is the Lean project's exporter ([leanprover/lean4export](https://github.com/leanprover/lean4export), tag
  `v4.34.0`, commit `076e8e5`).
- **The judgment.** `lake comparator --challenge-from-export CHALLENGE --solution-from-export SOLUTION`, in a directory
  with a `comparator.json` of your own: `challenge_module` and `solution_module` are module names, `theorem_names` the
  theorem, `permitted_axioms` the axioms you accept. With both exports given, the comparator judges them as they are
  and builds neither module; `solution_module` then only names the module of our development sources the proof was
  exported from, which is not in this repository. The directory needs no Lean project, and `external_kernels` (as
  in `checks/ID/comparator.json`) adds the independent kernels.

What `lake comparator` checks and what it protects against is documented by the Lean project: the Lean reference
manual's chapter [Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/) (this is its
"gold standard" check) and its [`lake comparator`](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)
section (`lake help comparator` prints the same), and the [comparator](https://github.com/leanprover/comparator)
repository, whose front end `lake comparator` is.

**Independent kernels.** The manual's gold standard also replays the proof in kernels implemented independently of
Lean's, and the checks here do. Lean 4.35 ships several external checkers (its release notes); the checks use three:

- nanoda, written in Rust and developed independently of Lean ([nanoda_lib](https://github.com/ammkrn/nanoda_lib));
- con-ron, which does not use Lean's runtime either;
- con-leche, which is built on Lean's runtime, so it shares more with Lean's kernel than the other two.

Each `comparator.json` lists them (`external_kernels`), and `verify-source.sh` puts the 4.35 toolchain's `bin`
directory, where they are, first on `PATH`. The comparator accepts only if Lean's kernel and every listed kernel
accept.

The functions' checks list all three. admin's and admin2's list con-leche and con-ron only. The nanoda Lean 4.35
ships (nanoda_lib 0.4.19) stops with a stack overflow on these exports, without a verdict: a crash, not a rejection.
nanoda_lib fixed this in 0.4.25 ([PR #58](https://github.com/ammkrn/nanoda_lib/pull/58), commit `6239144`; see also
issue #55), a version Lean's toolchain does not ship yet. To run a newer nanoda:

1. build `nanoda_bin` from [nanoda_lib](https://github.com/ammkrn/nanoda_lib), 0.4.25 or later (`cargo build
   --release`, which puts it in `target/release/`);
2. set `NANODA_BIN` to it. `verify-source.sh` then runs it as a further kernel, for every theorem.

In our runs, nanoda_lib 0.4.30 (commit `d0a02cc`) accepts admin's and admin2's proofs this way, beside the other
kernels. Each check then takes about an hour, at the same peak memory.

`lake comparator --paranoid` would add every checker Lean ships, `lean4lean` among them. The 4.35 `lean4lean` cannot
read exports made with Lean 4.34, whatever the proof: it stops at an unknown constant, `Decidable.intro`, which 4.35
introduced.

## How the proofs were made, and why you can check them without that

The proofs were produced by our own proof automation for machine code (symbolic execution, decision procedures and
generated lemmas), which is not part of this release. You do not need it to check them. Lean's kernel checks proof
terms, not the programs that found them, and each export holds the complete proof term of its theorem: every
definition and lemma it uses, each with its own proof. `verify-source.sh` has the kernel check all of it against the
statement in this repository. What you rely on is therefore what is here, the model, the statements and the loader,
together with Lean's kernel.

Most of the programs' proofs are not specific to them: the proofs of glibc's functions and startup are written once
for the library, not for these programs, and the files that depend on a binary's layout are
generated from the binary. What is written by hand for each program is 647 lines of Lean for admin and 739 for
admin2: code lines, comments left out, of the program's own proof files and its statement, and its entry in a shared
table of `main`'s stack use. Not counted: the generated files, the library's proofs and the proof automation.

## Trust base

- `ZellicX86/Spec/` (the model and the vocabulary) and `ZellicX86/Load/` (`#file_image`): read them to know what the
  theorems mean. They import Lean's core only.
- The statement files named above, and the definitions they use.
- Lean's kernel (4.35's, through `lake comparator`), the Lean 4.34 elaborator that builds the statements, the
  exporter `lean4export` that exports the challenge's statement from them (the solution's export is untrusted input),
  and `lake comparator`'s comparison of the two exports.
- The code: the functions' bytes are written in the statements (`Examples/*/Code.lean`), and the
  programs' binaries are fixed by their SHA-256 in the statements (`#file_image`). Which compiler or
  linker produced them does not matter to the theorems; `Examples/*/build.sh` and
  `clients/build.sh` record how they were built and check the recorded bytes against a rebuild.
- The hypotheses: what a theorem assumes of the processor, the launch and the run (above) is for the reader to check
  of the system they care about.

## Layout

- `ZellicX86/Spec/`, `ZellicX86/Load/`: the model, the vocabulary, the loader; `MODEL-LIMITATIONS.md`: what the model
  covers and what it does not.
- `Examples/Memcmp/`: each function's statement (`Statement.lean`), its
  functional specification (`Spec.lean`) and its bytes (`Code.lean`).
- `glibc-2.43-ubuntu-26.04-amd64/`: the programs' statements (`Glibc243UbuntuClients/`), the glibc definitions they use
  (`Glibc243Ubuntu/`: the environment assumption `Heap.MemGranted` and glibc's tunables, whose names the launch
  hypotheses use), and the binaries (`clients/`).
- `ReleaseChallenges/`: each exported theorem stated by `sorry`, the challenges `checks/ID/verify-source.sh` builds.
- `checks/ID/`: each theorem's checker configuration and script; `exports/SHA256SUMS`: the proof exports' checksums (the
  exports themselves are downloaded into `exports/`).
- `THIRD-PARTY-NOTICES.md` and `LICENSES/`: the material from glibc and the Linux kernel that this repository and the
  proof exports contain (the programs' binaries, the vDSO's tables), its licenses and
  where its source is.

## Who wrote this

This repository comes from a project at Zellic led by Malte Leip. Malte Leip directed the project, the proof work
included: its goals and scope, the ground rules for the model and the proofs, what to prove and how to approach it,
which tools the agents should build, and design questions throughout. Malte Leip wrote none of the project's code or
text.

All of that code and text was written by AI agents: most of it by Claude (Anthropic's Claude Opus 5.5, in Claude
Code), with contributions by Codex (OpenAI's GPT-6.1 Sol). That covers this repository (the model, the statements,
the example programs' sources, this README and `MODEL-LIMITATIONS.md`; not the third-party material listed in
`THIRD-PARTY-NOTICES.md`, nor the compilers' output), the proofs in the downloaded exports, and the proof automation
that produced them, which is not released. Codex also tested this README's instructions by following them. No part
has been audited (see "Status").

## License

Copyright (c) 2026 Zellic. Except for the third-party material listed in `THIRD-PARTY-NOTICES.md`, which keeps its
own license, this repository is licensed under either of

- the Apache License, Version 2.0 (`LICENSE-APACHE`), or
- the MIT License (`LICENSE-MIT`),

at your option. The same holds for the proof exports, apart from the third-party bytes they contain.
