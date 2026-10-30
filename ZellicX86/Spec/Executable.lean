import ZellicX86.Spec.Object
import ZellicX86.Spec.Statement
/-!
# A function of an executable, by its symbol

What a statement about a program's functions names (a client of a library, whose functions are instances of theorems
proved from the library's objects, and its own code): the bytes of the function a symbol of the executable's file
names, at the address the symbol gives, as the file's loadable segments place them; the bytes of a section by its name
(`Exe.sec`: `.init`, whose symbol `_init` has size 0); and the address of a global variable of the program, by
its symbol (`Exe.symAddr`). The file is a `Blob`, the bytes
the loader took from it (`#file_image`, checked by its SHA-256); everything here is a definition over those bytes, which
the kernel evaluates.

A function is found by its symbol in the file's symbol table (`SHT_SYMTAB`, which a linker writes and `strip` removes):
the definition of its name a call from another object reaches, which must be a function symbol (`STT_FUNC`), or else
the one `static` function of the name; its value the function's address and its size the number of its bytes. Its bytes are those the last loadable segment (`PT_LOAD`) whose pages meet them holds in its file part: what
`execve` maps there (`loadRegions`, `Spec/Linux/Exec.lean`: a segment's file pages mapped from `p_offset` on, a later
segment's mapping replacing an earlier one's).

A statement about a function of the program says `ImplementsCallIn F.blob prof "fn" ["callee", …] C`: the file has
the function and the callees named, and their code, each at its symbol's address, implements `C` at the function's
address (`ImplementsCall`, `Spec/Statement.lean`). That is a statement about those bytes in memory at those addresses
(`CallOf`), from wherever they came: in a dynamically linked `ET_EXEC` (`PT_INTERP`) the file's bytes are what `execve`
maps, and a dynamic linker that changes code (`DT_TEXTREL`) changes what a later call runs, which such a statement's
use at a call site has to account for. A contract that names a global variable of the program takes its address as
`Exe.dataAddr F.blob "var"`, and the statement says beside it that the file has it (`Exe.HasData F.blob ["var"]`).

Sources: the System V gABI, "Sections", "Symbol Table" (the value of a symbol in an executable file is its address),
"Program Header"; the fields as Linux v6.18 `include/uapi/linux/elf.h` declares them, read by `Spec/Elf.lean`'s
`ElfHeader.read` and `readPhdrs` and `Spec/Object.lean`'s `Obj.shdrs`, `Obj.symtab`, `Obj.sym` and `Obj.named`, which
read any ELF file's section headers and symbols.

Not modelled (no function, `none`): a position-independent executable (`ET_DYN`, whose symbols' values are offsets from
its load base) and a shared object; a file with a `PT_LOAD` segment Linux refuses (`p_offset` and `p_vaddr` not equal
modulo the page size, `p_filesz` above `p_memsz`); a function whose bytes are not all in one segment's file part (past
`p_filesz`, where the mapping has the file's bytes to the page's end or, for a writable segment with `p_memsz` above
`p_filesz`, zeros; or across two segments); a name whose definition other objects reach is not a function symbol (an
`STT_GNU_IFUNC` symbol, chosen at load time by its resolver; an assembly label without `.type`, `STT_NOTYPE`), and a
name defined more than once but by `static` functions alone (two `static` functions of one name in different
objects). Of the data symbols (no address, `none`): a `static` variable (local: several objects may each have one of
the name), a thread-local variable (`STT_TLS`: its value is an offset in the thread's TLS block), and a name whose one
non-local definition is no `STT_OBJECT`.
-/
namespace ZellicX86

/-- The bytes `e` are an executable file this reader reads: at least the 64 bytes of the file header, the ELF magic
number, 64-bit (`EI_CLASS`, byte 4, is `ELFCLASS64` = 2), little-endian (`EI_DATA`, byte 5, is `ELFDATA2LSB` = 1),
`e_type` `ET_EXEC`, `e_machine` `EM_X86_64`, `e_phentsize` 56 with the program header table in the file, `e_shentsize`
(offset 58, 2 bytes) 64 with the section header table in the file, and each section's bytes in the file (but a
`SHT_NOBITS` one's, which has none there); every `PT_LOAD` segment one Linux maps (`load_elf_binary`, `elf_map`): one
with bytes in the file (`p_filesz` not 0) has `p_offset` and `p_vaddr` equal modulo the page size, and `p_filesz` is
at most `p_memsz`. -/
def Exe.valid (e : Blob) : Bool :=
  let rd := e.bytes
  let h := ElfHeader.read rd
  64 ≤ e.size && elfMagic rd && rd 4 == 2 && rd 5 == 1 && h.type == ET_EXEC && h.machine == EM_X86_64 &&
    h.phentsize == phdrSize && h.phoff + phdrSize * h.phnum ≤ e.size &&
    leNat rd 58 2 == 64 && leNat rd 40 8 + 64 * leNat rd 60 2 ≤ e.size &&
    (Obj.shdrs e).all (fun s => s.type == SHT_NOBITS || s.offset + s.size ≤ e.size) &&
    (readPhdrs rd h.phoff h.phnum).all fun p => p.type != PT_LOAD ||
      ((p.filesz == 0 || p.offset % 4096 == p.vaddr % 4096) && p.filesz ≤ p.memsz)

/-- The function symbol named by the bytes `name` in the symbol table `st` (string table `str`) of `e`, its entries
read 24 bytes apart (`Elf64_Sym`; `sh_entsize` is not read). Among the definitions of that name (a section index other
than `SHN_UNDEF`, `SHN_ABS` included: its value is an address too): the only one that is not local (`STB_GLOBAL` or
`STB_WEAK`, of any type: a static link leaves at most one such definition of a name, the one calls from other objects
reach), if it is a function symbol (`STT_FUNC`); with none, the only local one, which must be a function symbol;
`none` otherwise (a non-local definition of another type: the name is not a function of this reader, even where a
`static` function shares it). -/
def Exe.fnSym (e : Blob) (st str : Shdr) (name : List Byte) : Option Sym :=
  let defs := ((List.range (st.size / 24)).filterMap (Obj.sym e st)).filter fun s =>
    (s.type == STT_FUNC || s.bind != STB_LOCAL) && Obj.named e str s name && s.shndx != SHN_UNDEF
  match defs.filter (·.bind != STB_LOCAL), defs with
  | [s], _ => if s.type == STT_FUNC then some s else none
  | [], [s] => some s
  | _, _ => none

/-- The `n` bytes of `e` at the address `a` as `execve` maps them: those of the last loadable segment (`PT_LOAD`) whose
pages, from the one holding `p_vaddr` to the one holding its last byte in memory (`p_vaddr + p_memsz - 1`; a segment
with `p_memsz` 0 has none, and Linux maps nothing for it), meet the bytes' pages, read from the file at `p_offset + (a - p_vaddr)` on. `none` where the bytes do not all lie in that
segment's file part (`p_vaddr` to `p_vaddr + p_filesz`) or past the file's end, or where no loadable segment's pages meet
them. -/
def Exe.bytesAt (e : Blob) (a n : Nat) : Option (List Byte) :=
  let h := ElfHeader.read e.bytes
  let meets (p : Phdr) := p.type == PT_LOAD && 0 < p.memsz && p.vaddr / 4096 * 4096 < a + n &&
    a < (p.vaddr + p.memsz + 4095) / 4096 * 4096
  match ((readPhdrs e.bytes h.phoff h.phnum).filter meets).getLast? with
  | some p =>
    if p.vaddr ≤ a && a + n ≤ p.vaddr + p.filesz && p.offset + (a - p.vaddr) + n ≤ e.size then
      some ((List.range n).map fun i => e.bytes (p.offset + (a - p.vaddr) + i))
    else none
  | none => none

/-- The function named by the bytes `name` of the executable `e`: its address (the symbol's value, `Exe.fnSym`) and
its bytes there (the symbol's size of them, `Exe.bytesAt`). `none` where `e` is no executable this reader reads
(`Exe.valid`), without a symbol table and its string table (`SHT_STRTAB`), without the one function symbol of the name,
where the symbol's size is 0 or its bytes end past the 64-bit address space, or where its bytes are not mapped from one
segment's file part. -/
def Exe.fnOf (e : Blob) (name : List Byte) : Option (Addr × List Byte) := do
  if !Exe.valid e then none
  let (_, st) ← Obj.symtab e
  let str ← Obj.shdr e st.link
  if str.type ≠ SHT_STRTAB then none
  let f ← Exe.fnSym e st str name
  if f.size = 0 ∨ 2 ^ 64 < f.value + f.size then none
  let bs ← Exe.bytesAt e f.value f.size
  some (BitVec.ofNat 64 f.value, bs)

/-- The function `name` (its UTF-8 encoding, `utf8`) of the executable `e` (`Exe.fnOf`). -/
def Exe.fn (e : Blob) (name : String) : Option (Addr × List Byte) := Exe.fnOf e (utf8 name)

/-- The function named by the bytes `name` of the executable `e` with `n` bytes: its address (the symbol's value,
`Exe.fnSym`) and the `n` bytes there (`Exe.bytesAt`), whatever the symbol's size. For a function whose symbol has size
0, whose code runs to a `ret` that no symbol bounds (gcc's `crtbeginT.o`: `frame_dummy`, `__do_global_dtors_aux`): a
statement about it names the bytes its proof covers, as `Obj.fnRestOf` reads the function in its object
(`Spec/Object.lean`). `none` where `Exe.fnOf` is `none` for a reason other than the symbol's size, where `n` is 0, or
where the bytes end past the 64-bit address space. -/
def Exe.fnBytesOf (e : Blob) (name : List Byte) (n : Nat) : Option (Addr × List Byte) := do
  if !Exe.valid e then none
  let (_, st) ← Obj.symtab e
  let str ← Obj.shdr e st.link
  if str.type ≠ SHT_STRTAB then none
  let f ← Exe.fnSym e st str name
  if n = 0 ∨ 2 ^ 64 < f.value + n then none
  let bs ← Exe.bytesAt e f.value n
  some (BitVec.ofNat 64 f.value, bs)

/-- The function `name` (its UTF-8 encoding) of the executable `e` with `n` bytes (`Exe.fnBytesOf`). -/
def Exe.fnBytes (e : Blob) (name : String) (n : Nat) : Option (Addr × List Byte) := Exe.fnBytesOf e (utf8 name) n

/-- The executable `e` has each of the functions `names`, as `Exe.fn` reads them. -/
def Exe.Has (e : Blob) (names : List String) : Prop := ∀ n ∈ names, (Exe.fn e n).isSome

/-- The function `name` of the executable `e` as a code segment, its address and its bytes (`Exe.fn`), as a statement
lists a program's code (`ImplementsCall`'s segments). Where the file has no such function, the address 0 and no bytes,
for which only a contract that allows anything can be proved; a statement says that the file has its functions
(`Exe.Has`, `ImplementsCallIn`) beside what it says of them. -/
def Exe.seg (e : Blob) (name : String) : Addr × List Byte := (Exe.fn e name).getD (0, [])

/-- The address of the function `name` of the executable `e`, the entry of a call of it (`Exe.seg`). -/
def Exe.entry (e : Blob) (name : String) : Addr := (Exe.seg e name).1

/-- The section named by the bytes `name` of the executable `e`: its address (`sh_addr`) and its `sh_size` bytes there
as `execve` maps them (`Exe.bytesAt`). For code no symbol spans: `.init`, which GNU ld assembles from `crti.o`'s and
`crtn.o`'s and whose symbol `_init` has size 0 (`Obj.linkedOutOf`, `Spec/Object.lean`). `none` where `e` is no
executable this reader reads (`Exe.valid`), has not exactly one section of the name (`Obj.secNamedOf`), where the
section has no bytes in the file (`SHT_NOBITS`), is empty or ends past the 64-bit address space, or where its bytes are
not mapped from one segment's file part. -/
def Exe.secOf (e : Blob) (name : List Byte) : Option (Addr × List Byte) := do
  if !Exe.valid e then none
  let (_, h) ← Obj.secNamedOf e name
  if h.type = SHT_NOBITS ∨ h.size = 0 ∨ 2 ^ 64 < h.addr + h.size then none
  let bs ← Exe.bytesAt e h.addr h.size
  some (BitVec.ofNat 64 h.addr, bs)

/-- The section `name` (its UTF-8 encoding) of the executable `e` (`Exe.secOf`): its address and its bytes. -/
def Exe.sec (e : Blob) (name : String) : Option (Addr × List Byte) := Exe.secOf e (utf8 name)

/-- The data symbol named by the bytes `name` in the symbol table `st` (string table `str`) of `e`: the only
definition of that name that is not local (`STB_GLOBAL` or `STB_WEAK`, a section index other than `SHN_UNDEF`), if it
is a data object (`STT_OBJECT`); `none` otherwise: no such definition (a `static` variable, local, is not read: several
objects may each have one of the name), more than one, or one of another type (a function; a thread-local variable,
`STT_TLS`, whose value is an offset in the thread's TLS block, not an address; a label, `STT_NOTYPE`). -/
def Exe.dataSym (e : Blob) (st str : Shdr) (name : List Byte) : Option Sym :=
  match ((List.range (st.size / 24)).filterMap (Obj.sym e st)).filter fun s =>
      s.bind != STB_LOCAL && Obj.named e str s name && s.shndx != SHN_UNDEF with
  | [s] => if s.type == STT_OBJECT then some s else none
  | _ => none

/-- The address of the data object named by the bytes `name` of the executable `e`: its symbol's value
(`Exe.dataSym`; in an executable file a symbol's value is an address, gABI "Symbol Table"). `none` where `e` is no
executable this reader reads (`Exe.valid`), without a symbol table and its string table (`SHT_STRTAB`), or without
the one data symbol of the name. Only the address is read: neither the symbol's size nor whether a segment maps it
(a statement's precondition says what it needs of the memory there). -/
def Exe.symAddrOf (e : Blob) (name : List Byte) : Option Addr := do
  if !Exe.valid e then none
  let (_, st) ← Obj.symtab e
  let str ← Obj.shdr e st.link
  if str.type ≠ SHT_STRTAB then none
  let s ← Exe.dataSym e st str name
  some (BitVec.ofNat 64 s.value)

/-- The address of the data object `name` (its UTF-8 encoding) of the executable `e` (`Exe.symAddrOf`): what a
statement names a program's global variable by (glibc's `__libc_single_threaded`), beside its functions (`Exe.fn`). -/
def Exe.symAddr (e : Blob) (name : String) : Option Addr := Exe.symAddrOf e (utf8 name)

/-- The executable `e` has each of the data objects `names`, as `Exe.symAddr` reads them. -/
def Exe.HasData (e : Blob) (names : List String) : Prop := ∀ n ∈ names, (Exe.symAddr e n).isSome

/-- The address of the data object `name` of the executable `e` (`Exe.symAddr`), as a statement writes it in a contract;
0 where the file has none, so a statement says that the file has it (`Exe.HasData`) beside what it says there. -/
def Exe.dataAddr (e : Blob) (name : String) : Addr := (Exe.symAddr e name).getD 0

/-- The function `fn` of the executable `e`, with the functions `callees` of `e` it calls, implements the contract `C`
on processor `prof`: `e` has each of them (`Exe.Has`), and their code segments (`Exe.seg`, the function's first)
implement `C` at the function's address (`ImplementsCall`). The names are one list for both, so a name the file does
not have makes the statement false rather than a statement about other code. -/
def ImplementsCallIn (e : Blob) (prof : Profile) (fn : String) (callees : List String) (C : Contract) : Prop :=
  Exe.Has e (fn :: callees) ∧ ImplementsCall prof (Exe.entry e fn) ((fn :: callees).map (Exe.seg e)) C

end ZellicX86
