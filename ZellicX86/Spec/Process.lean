import ZellicX86.Spec.Statement
import ZellicX86.Spec.Linux.Exec
/-!
# Statement vocabulary for processes

What a statement about a whole process, from `execve` on, is written in, besides
`Spec/Statement.lean`:

- a start of the program (`Launch`: processor, files, executable, arguments, kernel configuration and
  start state) of an executable with given bytes (`Launch.Of`);
- the executable's bytes as the file holds them (`FileHolds`), and so the bytes of any other file,
  and the zeros past a file's end in its last page (`TailZero`);
- the states `execve` starts the program in, for a kernel configuration and arguments, over
  every choice the kernel can make (`ExecStart`);
- the bytes of a file as a list (`FileBytes`), for statements whose functions take the input as one;
- the descriptors the program starts with, as far as a statement needs them: one open for reading
  on a file's pages at a position (`OpenOnFile`), one that is not on a file (`NotOnFile`), one that is open
  and not on a file (`OpenOffFile`).
- room on the stack below the initial `rsp` (`StackRoom`), for a program that pushes or calls there, and room above
  the program break (`BreakRoom`, on a kernel `LinuxBoot.Modest`), for a C library whose startup grows the break;
- the initial stack's vectors (`InitialStack`, with its regions named: `InitialStackIn`) and the loadable segments
  (`SegmentsLoaded`, their pages `segmentPages`) as `execve` leaves them, what a C library's startup assumes of the state
  it is called in.

A process-level statement then reads: for every start of the program (`Launch`, `Launch.Of`: every
processor, files holding the executable, arguments, kernel configuration and start state), the run
from it `Ends` with the outcome and events claimed.
-/
namespace ZellicX86

/-- File `file` of `fs` is `n` bytes long and holds the bytes `img 0, …, img (n - 1)`. -/
def FileHolds (fs : Files) (file : FileId) (img : Nat → Byte) (n : Nat) : Prop :=
  fs.size file = n ∧ ∀ i, i < n → fs.byte file i = img i

/-- The bytes of file `file`'s last page past its end are zeros (the file's size `n`, its pages up to
`⌈n / 4096⌉`): what a mapping of the file shows there. The kernel fills that part of a page with zeros
when it reads the page in (`mm/filemap.c`, the file systems' `read_folio`), when a write extends the
file and when the file is truncated, but a store through a shared mapping of the file lands there
and stays in the page (until writeback zeroes it, on a file system that writes back; `tmpfs` does
not), where a later mapping of the file sees it: so whether these bytes are zeros is a hypothesis
about the file, not a fact. -/
def TailZero (fs : Files) (file : FileId) : Prop :=
  ∀ i, fs.size file ≤ i → i < 4096 * ((fs.size file + 4095) / 4096) →
    fs.page ⟨file, i / 4096⟩ (BitVec.ofNat 12 i) = 0

/-- `s₀` is a state in which `execve` of file `exe` with arguments `a` starts the program on
processor `prof` (with the kernel's build and boot settings, `Profile.linux`), under the settings `k`
(which the kernel accepts), for some choice the kernel can make for this file's program headers. -/
def ExecStart (prof : Profile) (files : Files) (exe : FileId) (a : ExecArgs) (k : KernelConfig)
    (s₀ : State) : Prop :=
  k.Valid ∧ ∃ c, (∀ hdr phs, readElf files exe = some (hdr, phs) → c.Valid prof.linux phs a k) ∧
    execve prof files exe a k c = .ok s₀

/-- A start of a program by `execve`: the processor `prof` it runs on, the files `files` (the executable
among them), the executable `exe`, the arguments `args` the caller passes (argument and environment
strings, open descriptors, settings), the kernel's settings as `execve` reads them `kcfg`, and the state `s₀` the program
starts in. -/
structure Launch where
  prof : Profile
  files : Files
  exe : FileId
  args : ExecArgs
  kcfg : KernelConfig
  s₀ : State

/-- `l` starts the program whose file is `n` bytes long and holds `img`: file `l.exe` holds those bytes
(`FileHolds`), `execve` of it starts the program in `l.s₀` (`ExecStart`), and its arguments are what a caller can pass
(`ExecArgs.Ok`: C strings, its thread id a process id, …). -/
def Launch.Of (img : Nat → Byte) (n : Nat) (l : Launch) : Prop :=
  FileHolds l.files l.exe img n ∧ ExecStart l.prof l.files l.exe l.args l.kcfg l.s₀ ∧ l.args.Ok

/-- Descriptor `fd` of the program `execve` starts with arguments `a` is open for reading on the
pages of file `file` (`FileMap.pages`: a regular file, say, as standard input is in `prog < file`),
at position `off`, and `execve` does not close it (no `FD_CLOEXEC`). A `mmap` of it maps the file's
pages, and a `read` of it delivers the file's bytes from the position on. -/
def OpenOnFile (a : ExecArgs) (fd : Nat) (file : FileId) (off : Nat) : Prop :=
  ∃ f, a.files fd = some ⟨f, false⟩ ∧ f.readable = true ∧ f.map = .pages file ∧
    (a.filePos f).offset = off

/-- File `file` of `fs` holds exactly the bytes `bs`: its size is their number. -/
def FileBytes (fs : Files) (file : FileId) (bs : List Byte) : Prop :=
  FileHolds fs file (fun i => bs.getD i 0) bs.length

/-- Descriptor `fd` of the program `execve` starts with arguments `a`, if open, is not on the pages
of file `file`, so that a `write` to it does not change that file (`sysWrite` writes into the pages
of the file its descriptor is on): standard output is not the input file, say. -/
def NotOnFile (a : ExecArgs) (fd : Nat) (file : FileId) : Prop :=
  ∀ e, a.files fd = some e → e.file.map ≠ .pages file

/-- Descriptor `fd` of the program `execve` starts with arguments `a` is open, `execve` does not close it
(no `FD_CLOEXEC`), and it is not on the pages of file `file`: a `write` to it does not change that file,
and a file the program opens gets another descriptor (`openat` takes the lowest free one). Standard
output, open and not the input file, of a program that opens its input itself, say. -/
def OpenOffFile (a : ExecArgs) (fd : Nat) (file : FileId) : Prop :=
  ∃ f, a.files fd = some ⟨f, false⟩ ∧ f.map ≠ .pages file

/-- `execve` with arguments `a` leaves at least `n` bytes of the new stack's mapping below the initial
`rsp`, so that the program can push and call there without growing the stack (`growStack`, whose success
depends on the environment and the layout below the stack). A sufficient condition, from where the kernel
puts things (`fs/exec.c`; `stackLayout`): `setup_arg_pages` maps 128 KiB below the pages of the
argument strings if the soft stack limit (`ExecArgs.stackRlimit`) allows those pages and the 128 KiB, and
`create_elf_tables` puts below the strings, inside those 128 KiB, the `argv` and `envp` pointers and
fewer than 8640 bytes more (the random alignment of the stack's top, below 8 KiB; `AT_RANDOM`'s bytes, the
platform string, the auxiliary vector, `argc` and the two zeros ending the pointer arrays); `n` bytes of
what is left of them lie below `rsp`. Any program run with few arguments under the usual 8 MiB limit
meets it for a few KiB. It holds for no `a` once `n` exceeds 122,424 (131,072 − 8,640 − 8, with the one
`argv` pointer every launch has, `ExecArgs.argv'`), though the kernel grows the stack further, up to the
limit: a statement with a larger `n` holds vacuously. -/
def StackRoom (a : ExecArgs) (n : Nat) : Prop :=
  pageUp (8 + a.strings.length) + 131072 ≤ a.stackRlimit.cur.toNat ∧
    n + 8 * (a.argv'.length + a.envp.length) + 8640 ≤ 131072

/-- The booted kernel's stack guard gap and vDSO image are no larger than an ordinary boot's: the gap at most `2 ^ 32`
pages (16 TiB; 256 pages, 1 MiB, without `stack_guard_gap=` on the command line) and the image at most `2 ^ 20` pages
(4 GiB; Linux 6.18's x86-64 image is two). The kernel takes any gap and maps any image, but `execve` puts the vDSO below
the stack's guard gap (`ExecChoice.VdsoPlace`), so with a gap of about the address space's size, or an image that
large, the vDSO may lie right above the program break. With these bounds it lies more than 5 TiB up or below a loadable
segment, so `execve` leaves room above the break (`BreakRoom`) of a program loaded low. -/
def LinuxBoot.Modest (lb : LinuxBoot) : Prop := lb.stackGuardGap ≤ 2 ^ 32 ∧ lb.vdsoText.length ≤ 2 ^ 20

/-- Room in `s` for the program break to grow by `n` bytes: the pages from the break's page boundary up to that of
`brk + n`, and the page after them, are unmapped, and that boundary lies at or below `DEFAULT_MAP_WINDOW`
(`stackTopMax`), so a `brk` to anywhere up to `brk + n` maps them unless the kernel refuses memory for a reason the model
leaves to the environment (`sysBrk`). What a C library whose startup grows the break may assume at its entry; `execve`
leaves it for a program loaded low on a kernel `LinuxBoot.Modest`. -/
def BreakRoom (s : State) (n : Nat) : Prop :=
  pageUp (s.proc.mm.brk.toNat + n) ≤ stackTopMax ∧
    s.proc.mm.mem.free (pageUp s.proc.mm.brk.toNat / 4096)
      ((pageUp (s.proc.mm.brk.toNat + n) - pageUp s.proc.mm.brk.toNat) / 4096 + 1) = true

/-- The bytes of the vDSO's image of the booted kernel `lb`, from its first byte: its pages' bytes, 0 past them. -/
def LinuxBoot.vdsoByte (lb : LinuxBoot) (i : Nat) : Byte :=
  lb.vdsoText.getD (i / 4096) zeroFrame (BitVec.ofNat 12 i)

/-- The image's bytes as a list, its pages one after the other: the code a call of its functions runs. -/
def LinuxBoot.vdsoBytes (lb : LinuxBoot) : List Byte :=
  (List.range (4096 * lb.vdsoText.length)).map lb.vdsoByte

/-- In `s`, on processor `prof`, the initial stack of a program `execve` started with arguments `a` from an executable
with ELF header `hdr` and program headers `phs` lies from `argv` on as `execve` writes it, for some choice the kernel
can make (`ExecChoice.Valid`, for some kernel configuration; psABI section 3.4.1; `create_elf_tables` in
`fs/binfmt_elf.c`; `stackLayout`, `stackWords`, `auxv`): `argv` is where that choice puts the words after the argument
count; from there the `argv` pointers and a null word, the `envp` pointers and a null word, and the auxiliary vector
(`auxv`: the program headers' address and count, the page size, the entry point, the ids, `AT_SECURE`, the
`AT_RANDOM` and `AT_PLATFORM` addresses, the vDSO's address, the hardware capabilities, ending with `AT_NULL`); the 16
random bytes and the platform string `AT_RANDOM` and `AT_PLATFORM` point to; the argument and environment strings the
pointers point to (`ExecArgs.strings`); and, where the kernel maps the vDSO, its image at `AT_SYSINFO_EHDR`
(`LinuxBoot.vdsoBytes`). All of it can be read. What a C library's startup reads (glibc's `__libc_start_main`,
`_dl_aux_init`, `__libc_init_secure`, `_dl_setup_stack_chk_guard` with `AT_RANDOM`'s bytes, `_dl_non_dynamic_init`
with the program headers, `setup_vdso` with the image), so its contract assumes it (`Spec/Lib/C/Start.lean`); every
process started by `execve` meets it at its first instruction, with `argv` `rsp + 8`, and so does every state that
left these bytes and pages as they were. -/
def InitialStack (prof : Profile) (s : State) (a : ExecArgs) (hdr : ElfHeader) (phs : List Phdr) (argv : Addr) :
    Prop :=
  ∃ (k : KernelConfig) (c : ExecChoice), c.Valid prof.linux phs a k ∧
    argv.toNat = (stackLayout a prof.linux c).sp + 8 ∧
    Bytes s argv (wordBytes ((stackWords (auxv prof hdr (phdrAddr hdr phs) a c (stackLayout a prof.linux c)) a
      (stackLayout a prof.linux c)).drop 1)) ∧
    Accessible prof.feat s .read ⟨argv, 8 * ((stackWords (auxv prof hdr (phdrAddr hdr phs) a c
      (stackLayout a prof.linux c)) a (stackLayout a prof.linux c)).length - 1)⟩ ∧
    Bytes s (BitVec.ofNat 64 ((stackLayout a prof.linux c).platform - platformString.length - 16))
      (toBytesLE c.random 16 ++ platformString) ∧
    Accessible prof.feat s .read ⟨BitVec.ofNat 64 ((stackLayout a prof.linux c).platform - platformString.length - 16),
      16 + platformString.length⟩ ∧
    Bytes s (BitVec.ofNat 64 (stackLayout a prof.linux c).strings) a.strings ∧
    Accessible prof.feat s .read ⟨BitVec.ofNat 64 (stackLayout a prof.linux c).strings, a.strings.length⟩ ∧
    (prof.linux.vdso = true → Bytes s (BitVec.ofNat 64 c.vdsoText) prof.linux.vdsoBytes ∧
      Accessible prof.feat s .read ⟨BitVec.ofNat 64 c.vdsoText, prof.linux.vdsoBytes.length⟩)

/-- The regions `InitialStack` speaks of for the arguments `a` at `execve`'s choice `c` (`stackLayout`), `argv` where the
words after the argument count start: those words (the `argv` and `envp` pointers, the auxiliary vector), the 16 random
bytes with the platform string, the argument and environment strings, and the vDSO's image where the kernel maps one. -/
def initialRgns (prof : Profile) (a : ExecArgs) (hdr : ElfHeader) (phs : List Phdr) (c : ExecChoice) (argv : Addr) :
    List Rgn :=
  [⟨argv, 8 * ((stackWords (auxv prof hdr (phdrAddr hdr phs) a c (stackLayout a prof.linux c)) a
      (stackLayout a prof.linux c)).length - 1)⟩,
    ⟨BitVec.ofNat 64 ((stackLayout a prof.linux c).platform - platformString.length - 16), 16 + platformString.length⟩,
    ⟨BitVec.ofNat 64 (stackLayout a prof.linux c).strings, a.strings.length⟩] ++
  if prof.linux.vdso then [⟨BitVec.ofNat 64 c.vdsoText, prof.linux.vdsoBytes.length⟩] else []

/-- `InitialStack` with its regions named: in `s`, the initial stack is as `execve` wrote it for the arguments `a` from
`argv` on, at a choice whose regions (`initialRgns`) each lie in one of the regions `IS`. A statement can then say what
else holds of those regions (that they are ordinary memory, apart from others), and a state that left the bytes and
pages of `IS` as they were keeps it. -/
def InitialStackIn (prof : Profile) (s : State) (a : ExecArgs) (hdr : ElfHeader) (phs : List Phdr) (argv : Addr)
    (IS : List Rgn) : Prop :=
  ∃ (k : KernelConfig) (c : ExecChoice), c.Valid prof.linux phs a k ∧
    argv.toNat = (stackLayout a prof.linux c).sp + 8 ∧
    Bytes s argv (wordBytes ((stackWords (auxv prof hdr (phdrAddr hdr phs) a c (stackLayout a prof.linux c)) a
      (stackLayout a prof.linux c)).drop 1)) ∧
    Accessible prof.feat s .read ⟨argv, 8 * ((stackWords (auxv prof hdr (phdrAddr hdr phs) a c
      (stackLayout a prof.linux c)) a (stackLayout a prof.linux c)).length - 1)⟩ ∧
    Bytes s (BitVec.ofNat 64 ((stackLayout a prof.linux c).platform - platformString.length - 16))
      (toBytesLE c.random 16 ++ platformString) ∧
    Accessible prof.feat s .read ⟨BitVec.ofNat 64 ((stackLayout a prof.linux c).platform - platformString.length - 16),
      16 + platformString.length⟩ ∧
    Bytes s (BitVec.ofNat 64 (stackLayout a prof.linux c).strings) a.strings ∧
    Accessible prof.feat s .read ⟨BitVec.ofNat 64 (stackLayout a prof.linux c).strings, a.strings.length⟩ ∧
    (prof.linux.vdso = true → Bytes s (BitVec.ofNat 64 c.vdsoText) prof.linux.vdsoBytes ∧
      Accessible prof.feat s .read ⟨BitVec.ofNat 64 c.vdsoText, prof.linux.vdsoBytes.length⟩) ∧
    ∀ r ∈ initialRgns prof a hdr phs c argv, ∃ q ∈ IS, q.base.toNat ≤ r.base.toNat ∧
      r.base.toNat + r.len ≤ q.base.toNat + q.len

/-- In `s`, on a processor with features `feat`, the loadable segments `phs` of an executable file holding the bytes
`img` are as `execve` maps them (`load_elf_binary`; `segmentRegions`): each `PT_LOAD` segment's `p_filesz` bytes from
`p_vaddr` hold the file's bytes from `p_offset` and a readable one's (`PF_R`) can be read, and a writable one's (`PF_W`) further bytes up to `p_memsz`
are zeros (`.bss`) and can be written. What a C library's startup reads of its own data (its relocations,
`.rela.iplt`, the program headers, the TLS image), so its contract assumes it (`Spec/Lib/C/Start.lean`). A process
started by `execve` meets it at its first instruction where no segment's pages overlap a later one's (a later
segment's mapping replaces them). -/
def SegmentsLoaded (feat : Features) (s : State) (img : Nat → Byte) (phs : List Phdr) : Prop :=
  ∀ ph ∈ phs, ph.type = PT_LOAD →
    Bytes s (BitVec.ofNat 64 ph.vaddr) ((List.range ph.filesz).map fun i => img (ph.offset + i)) ∧
    (ph.hasFlag 4 = true → Accessible feat s .read ⟨BitVec.ofNat 64 ph.vaddr, ph.filesz⟩) ∧
    (ph.hasFlag 2 = true → Bytes s (BitVec.ofNat 64 (ph.vaddr + ph.filesz)) (List.replicate (ph.memsz - ph.filesz) 0) ∧
      Accessible feat s .write ⟨BitVec.ofNat 64 (ph.vaddr + ph.filesz), ph.memsz - ph.filesz⟩)

/-- The read-only data of an executable whose program headers are `phs`, as `execve` maps it: the region of each
loadable segment (`PT_LOAD`) that is readable and neither writable nor executable (`PF_R` alone: `.rodata`, the ELF
header's page), its `p_filesz` bytes from `p_vaddr` (`SegmentsLoaded`'s, the file's bytes). What a program's functions
may read as their constants (`Spec/Lib/C/Start.lean`'s `CStart.room`); the executable segments are their code, given
to them as such (`CodeIn`), not as data. An executable linked with `-z noseparate-code` has `.rodata` in its executable
segment and so no read-only data here: a statement whose functions read constants is then not provable over it. -/
def roSegments (phs : List Phdr) : List Rgn :=
  (phs.filter fun ph => ph.type == PT_LOAD && ph.hasFlag 4 && !ph.hasFlag 2 && !ph.hasFlag 1).map fun ph =>
    ⟨BitVec.ofNat 64 ph.vaddr, ph.filesz⟩

/-- The pages of the loadable segments of an executable whose program headers are `phs`, as `execve` maps them: for each
`PT_LOAD` segment with memory (`p_memsz` not 0), its memory (`p_memsz` bytes from `p_vaddr`) widened to whole pages (`load_elf_binary` maps from the
page of `p_vaddr` to the page boundary after its end: `elf_load` in `fs/binfmt_elf.c`). No other mapping `execve` makes (the stack,
the vDSO) lies in them. -/
def segmentPages (phs : List Phdr) : List Rgn :=
  (phs.filter fun ph => ph.type == PT_LOAD && ph.memsz != 0).map fun ph =>
    ⟨BitVec.ofNat 64 (pageDown ph.vaddr), pageUp (ph.vaddr + ph.memsz) - pageDown ph.vaddr⟩

end ZellicX86
