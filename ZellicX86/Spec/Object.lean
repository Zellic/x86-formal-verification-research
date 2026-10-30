import ZellicX86.Spec.Elf
/-!
# Relocatable objects, static archives, and a function as a static link places it

What a statement about a library's function proved from its relocatable object (`.o`, `ET_REL`) names: the object's
bytes, read as the ELF format lays them out (section headers, the symbol table, the relocation entries), the member
of a static archive (`libc.a`) that holds them, and the function's bytes as a static link leaves them, with the
relocations in its range applied in the linker's terms (`S + A - P`, `Reloc.apply`) when each fits its field
(`Reloc.Fit`, the linker's check).

A file's bytes are a `Blob`: its bytes and its size. Every reader here checks that what it reads lies in the file and
in the section it belongs to, and refuses (`none`) what does not: a statement is never about bytes past a member's
end, nor about a malformed object read as something else.

A link (`Link`) is where it places each of the object's sections, the address or thread-pointer offset it gives each
symbol the object takes from elsewhere, and the PLT entries it made. A symbol the object defines has its section's
address plus its value (`SymRef.value`), so two functions of one section lie at the distance their values say,
whatever the link: a call from one to the other that the assembler resolved without a relocation reaches the other in
every link. What a link writes for each relocation is GNU ld's in a static executable (`Reloc.apply`), so "every link"
of a statement means every such link.

Sources: the System V gABI, "Sections", "Symbol Table", "Relocation" (the field offsets as Linux v6.18
`include/uapi/linux/elf.h` declares `Elf64_Ehdr`, `Elf64_Shdr`, `Elf64_Sym`, `Elf64_Rela`); the x86-64 psABI
(`object-files.tex`, §"Relocation", table "Relocation Types", and §"Symbol Table" on
`STT_GNU_IFUNC`); the archive format of glibc 2.43 `misc/ar.h` (`ARMAG`, `struct ar_hdr`, `ARFMAG`) with the System V
names `/`, `//` and `/n` that GNU ar writes (`ar(1)`; checked against GNU ar's `ar t` and `ar p` on `libc.a`).

What is not modelled (no bytes, so no statement about the function): relocation kinds other than `R_X86_64_64`,
`PC32`, `PLT32`, `32`, `32S` and `TPOFF32`; of `GOTTPOFF` and `REX_GOTPCRELX` everything but a `mov` that GNU ld relaxes
in a static executable that is not position-independent; of `GOTPCREL` everything but an instruction other than a
`mov`, whose GOT slot ld keeps (`Reloc.apply` gives `none`);
a relocation against the section symbol of a mergeable section (`SHF_MERGE`), which a linker resolves by its addend; a
symbol the object defines non-weakly with a section index reserved other than `SHN_ABS` and `SHN_COMMON` (`SHN_XINDEX`:
more than `0xff00` sections); `SHT_REL` entries for the function's section (x86-64 objects use `SHT_RELA`, psABI); relocations whose
fields overlap.
-/
namespace ZellicX86

/-- A file's bytes: `bytes i` is byte `i` for `i` below `size`. What lies at `size` and beyond is not the file's, and no
reader below reads it. -/
structure Blob where
  bytes : Nat → Byte
  size : Nat

/-- The empty file. -/
def Blob.empty : Blob := ⟨fun _ => 0, 0⟩

/-! ## Section headers -/

/-- A section header (`Elf64_Shdr`, 64 bytes), the fields a reader of an object needs. -/
structure Shdr where
  /-- `sh_name` (offset 0, 4 bytes): the name's offset in the section-name string table. -/
  name : Nat
  /-- `sh_type` (offset 4, 4 bytes): `SHT_SYMTAB` = 2, `SHT_RELA` = 4, `SHT_NOBITS` = 8, `SHT_REL` = 9, … -/
  type : Nat
  /-- `sh_flags` (offset 8, 8 bytes): `SHF_MERGE` = 0x10, `SHF_TLS` = 0x400, … -/
  flags : Nat
  /-- `sh_addr` (offset 16, 8 bytes): in an executable, the address of the section's first byte in memory; 0 in a
  relocatable object. -/
  addr : Nat
  /-- `sh_offset` (offset 24, 8 bytes): the section's bytes' offset in the file. -/
  offset : Nat
  /-- `sh_size` (offset 32, 8 bytes): the section's size in bytes. -/
  size : Nat
  /-- `sh_link` (offset 40, 4 bytes): of a symbol table, its string table's index; of a relocation section, its
  symbol table's. -/
  link : Nat
  /-- `sh_info` (offset 44, 4 bytes): of a relocation section, the index of the section it applies to. -/
  info : Nat

/-- The section header at file offset `off` of the bytes `rd`. -/
def Shdr.read (rd : Nat → Byte) (off : Nat) : Shdr :=
  { name := leNat rd off 4, type := leNat rd (off + 4) 4, flags := leNat rd (off + 8) 8,
    addr := leNat rd (off + 16) 8, offset := leNat rd (off + 24) 8, size := leNat rd (off + 32) 8, link := leNat rd (off + 40) 4,
    info := leNat rd (off + 44) 4 }

/-- `e_type` of a relocatable object. -/
def ET_REL : Nat := 1
/-- `sh_type` of an unused section header. -/
def SHT_NULL : Nat := 0
/-- `sh_type` of a symbol table. -/
def SHT_SYMTAB : Nat := 2
/-- `sh_type` of a string table. -/
def SHT_STRTAB : Nat := 3
/-- `sh_type` of relocation entries with addends (`Elf64_Rela`). -/
def SHT_RELA : Nat := 4
/-- `sh_type` of a section with no bytes in the file (`.bss`). -/
def SHT_NOBITS : Nat := 8
/-- `sh_type` of relocation entries without addends (`Elf64_Rel`). -/
def SHT_REL : Nat := 9
/-- `sh_flags` bit of a section whose pieces a linker may merge with equal ones (`SHF_MERGE`). -/
def SHF_MERGE : Nat := 0x10
/-- The section index of an undefined symbol. -/
def SHN_UNDEF : Nat := 0
/-- Section indices from here on are reserved, not sections (`SHN_LORESERVE`). -/
def SHN_LORESERVE : Nat := 0xff00
/-- The section index of a symbol with an absolute value (`SHN_ABS`). -/
def SHN_ABS : Nat := 0xfff1
/-- The section index of a common symbol, which the linker allocates (`SHN_COMMON`). -/
def SHN_COMMON : Nat := 0xfff2

/-- The object's `e_shnum` (file header offset 60, 2 bytes) section headers, from `e_shoff` (offset 40, 8 bytes) on,
64 bytes apart. -/
def Obj.shdrs (o : Blob) : List Shdr :=
  (List.range (leNat o.bytes 60 2)).map fun i => Shdr.read o.bytes (leNat o.bytes 40 8 + 64 * i)

/-- Section `i` of the object `o`, `none` from `e_shnum` on. -/
def Obj.shdr (o : Blob) (i : Nat) : Option Shdr := (Obj.shdrs o)[i]?

/-- The bytes `o` are a relocatable object this reader reads: at least the 64 bytes of the file header, the ELF magic
number, 64-bit (`EI_CLASS`, byte 4, is `ELFCLASS64` = 2), little-endian (`EI_DATA`, byte 5, is `ELFDATA2LSB` = 1),
`e_type` `ET_REL`, `e_machine` `EM_X86_64` (`ElfHeader.read`), `e_shentsize` (offset 58, 2 bytes) 64; the section
header table in the file, and each section's bytes (but a `SHT_NOBITS` one's, which has none in the file; the null
section header has size 0). -/
def Obj.valid (o : Blob) : Bool :=
  let rd := o.bytes
  64 ≤ o.size && elfMagic rd && rd 4 == 2 && rd 5 == 1 && (ElfHeader.read rd).type == ET_REL &&
    (ElfHeader.read rd).machine == EM_X86_64 && leNat rd 58 2 == 64 &&
    leNat rd 40 8 + 64 * leNat rd 60 2 ≤ o.size &&
    (Obj.shdrs o).all fun h => h.type == SHT_NOBITS || h.offset + h.size ≤ o.size

/-! ## Symbols -/

/-- A symbol table entry (`Elf64_Sym`, 24 bytes). -/
structure Sym where
  /-- `st_name` (offset 0, 4 bytes): the name's offset in the symbol table's string table. -/
  name : Nat
  /-- The low four bits of `st_info` (offset 4, 1 byte): `STT_FUNC` = 2, `STT_SECTION` = 3, `STT_TLS` = 6,
  `STT_GNU_IFUNC` = 10, … -/
  type : Nat
  /-- The high four bits of `st_info`: `STB_LOCAL` = 0, `STB_GLOBAL` = 1, `STB_WEAK` = 2. -/
  bind : Nat
  /-- `st_shndx` (offset 6, 2 bytes): the index of the section it is defined in, or `SHN_UNDEF`, `SHN_ABS`, … -/
  shndx : Nat
  /-- `st_value` (offset 8, 8 bytes): in a relocatable object, its offset in its section. -/
  value : Nat
  /-- `st_size` (offset 16, 8 bytes). -/
  size : Nat

/-- The symbol table entry at file offset `off` of the bytes `rd`. -/
def Sym.read (rd : Nat → Byte) (off : Nat) : Sym :=
  { name := leNat rd off 4, type := (rd (off + 4)).toNat % 16, bind := (rd (off + 4)).toNat / 16,
    shndx := leNat rd (off + 6) 2, value := leNat rd (off + 8) 8, size := leNat rd (off + 16) 8 }

/-- `STT_OBJECT`: a data object (a variable, an array). -/
def STT_OBJECT : Nat := 1
/-- `STT_FUNC`: a function. -/
def STT_FUNC : Nat := 2
/-- `STT_SECTION`: the symbol of a section, value 0. -/
def STT_SECTION : Nat := 3
/-- `STT_GNU_IFUNC`: a function chosen at load time by its resolver (psABI, "Symbol Table"). -/
def STT_GNU_IFUNC : Nat := 10
/-- `STB_LOCAL`: a symbol only its object sees. -/
def STB_LOCAL : Nat := 0
/-- `STB_WEAK`: a definition another object's global one replaces. -/
def STB_WEAK : Nat := 2

/-- The object's symbol table: the index and header of its first `SHT_SYMTAB` section (a relocatable object has
one), `none` without. -/
def Obj.symtab (o : Blob) : Option (Nat × Shdr) :=
  ((Obj.shdrs o).zipIdx.find? (·.1.type = SHT_SYMTAB)).map fun (h, i) => (i, h)

/-- Entry `i` of the symbol table `st` of `o`, for `i` below its `sh_size / 24` entries. -/
def Obj.sym (o : Blob) (st : Shdr) (i : Nat) : Option Sym :=
  if i < st.size / 24 then some (Sym.read o.bytes (st.offset + 24 * i)) else none

/-! Names are bytes: a symbol table's or an archive's name is the bytes before its NUL (any but NUL; ELF and `ar` set
no encoding), compared and used as keys as such, so that two names are one only where their bytes are. A statement
writes a name as a string, which stands for its UTF-8 encoding (`utf8`): what C and C++ compilers write for an
identifier (gcc 15 and clang 21: `café` is `63 61 66 c3 a9`); Rust and Swift encode identifiers in ASCII. A name
whose bytes are not UTF-8 (possible from assembly: `"na\xe9me"`) is written as its bytes, with the functions ending in
`Of`. -/

/-- The UTF-8 encoding of the character `c` (RFC 3629 section 3): one byte below `0x80`, else a lead byte with the count of
bytes in its high bits and continuation bytes `10xxxxxx` of six bits each, most significant first. (A `Char` is a
Unicode scalar value: not a surrogate, at most `0x10FFFF`.) -/
def utf8Char (c : Char) : List Byte :=
  let n := c.toNat
  if n < 0x80 then [BitVec.ofNat 8 n]
  else if n < 0x800 then [BitVec.ofNat 8 (0xc0 + n / 64), BitVec.ofNat 8 (0x80 + n % 64)]
  else if n < 0x10000 then
    [BitVec.ofNat 8 (0xe0 + n / 4096), BitVec.ofNat 8 (0x80 + n / 64 % 64), BitVec.ofNat 8 (0x80 + n % 64)]
  else
    [BitVec.ofNat 8 (0xf0 + n / 262144), BitVec.ofNat 8 (0x80 + n / 4096 % 64), BitVec.ofNat 8 (0x80 + n / 64 % 64),
     BitVec.ofNat 8 (0x80 + n % 64)]

/-- The UTF-8 encoding of the string `s`, a name's bytes as a statement writes the name. -/
def utf8 (s : String) : List Byte := s.toList.flatMap utf8Char

/-- The bytes of the NUL-terminated string at offset `off` of `rd` among the next `n` bytes; `none` where no NUL is
among them. -/
def cstrBytes (rd : Nat → Byte) (off : Nat) : Nat → Option (List Byte)
  | 0 => none
  | n + 1 => if rd off = 0 then some [] else (cstrBytes rd (off + 1) n).map (rd off :: ·)

/-- The name of symbol `s` of `o`, its string table `str`: the bytes of the string at `st_name` there, which must
begin in the table and end with a NUL in it; `none` otherwise. -/
def Obj.symName (o : Blob) (str : Shdr) (s : Sym) : Option (List Byte) :=
  if s.name < str.size then cstrBytes o.bytes (str.offset + s.name) (str.size - s.name) else none

/-- The bytes of `rd` from offset `off` on begin with the bytes `bs`. (Each pair compared as numbers by `Nat.beq`, which
the kernel evaluates directly: a reader compares every symbol's name with the one it looks for.) -/
def bytesMatch (rd : Nat → Byte) (off : Nat) : List Byte → Bool
  | [] => true
  | b :: bs => Nat.beq (rd off).toNat b.toNat && bytesMatch rd (off + 1) bs

/-- The symbol `s` of `o` (string table `str`) is named `name`: its name is in the table and is those bytes. -/
def Obj.named (o : Blob) (str : Shdr) (s : Sym) (name : List Byte) : Bool :=
  s.name + name.length + 1 ≤ str.size && bytesMatch o.bytes (str.offset + s.name) (name ++ [0])

/-- The defined function symbol named by the bytes `name` (`STT_FUNC`, in a section): the only one; `none` where there
is none or more than one. -/
def Obj.fnSym (o : Blob) (st str : Shdr) (name : List Byte) : Option Sym :=
  let hits := ((List.range (st.size / 24)).filterMap (Obj.sym o st)).filter fun s =>
    s.type = STT_FUNC && s.shndx ≠ SHN_UNDEF && s.shndx < SHN_LORESERVE && Obj.named o str s name
  match hits with
  | [s] => some s
  | _ => none

/-! ## Relocation entries -/

/-- A relocation entry with an addend (`Elf64_Rela`, 24 bytes). -/
structure Rela where
  /-- `r_offset` (offset 0, 8 bytes): in a relocatable object, the field's offset in the section it applies to. -/
  offset : Nat
  /-- The low 32 bits of `r_info` (offset 8, 8 bytes): the relocation's type (`R_X86_64_*`). -/
  type : Nat
  /-- The high 32 bits of `r_info`: the index of its symbol in the symbol table. -/
  sym : Nat
  /-- `r_addend` (offset 16, 8 bytes), a signed 64-bit number, as the 64-bit word the linker adds. -/
  addend : Addr

/-- The relocation entry at file offset `off` of the bytes `rd`. -/
def Rela.read (rd : Nat → Byte) (off : Nat) : Rela :=
  { offset := leNat rd off 8, type := leNat rd (off + 8) 4, sym := leNat rd (off + 12) 4,
    addend := BitVec.ofNat 64 (leNat rd (off + 16) 8) }

/-- The relocation entries for section `sec` of `o` against the symbol table `stIdx`: those of every `SHT_RELA`
section whose `sh_info` is `sec` and whose `sh_link` is `stIdx`, in the order of the sections and of their entries;
`none` where a relocation section for `sec` has entries without addends (`SHT_REL`) or names another symbol table. -/
def Obj.relas (o : Blob) (stIdx sec : Nat) : Option (List Rela) :=
  let rs := (Obj.shdrs o).filter fun r => (r.type = SHT_RELA ∨ r.type = SHT_REL) ∧ r.info = sec
  if rs.all (fun r => r.type == SHT_RELA && r.link == stIdx) then
    some (rs.flatMap fun r => (List.range (r.size / 24)).map fun k => Rela.read o.bytes (r.offset + 24 * k))
  else none

/-! ## A function of the object, as it reads -/

/-- What a relocation's symbol stands for in a link (`symRef`): a place in a section of the object (`sec i v`: offset
`v` of section `i`), a place in a mergeable section of it (`piece i v`), an absolute value, or the symbol of that name
the link resolves (`ext`). -/
inductive SymRef where
  | sec (shndx value : Nat)
  | piece (shndx value : Nat)
  | abs (value : Nat)
  | ext (name : List Byte)

/-- `sh_flags`' bit `SHF_MERGE` is set in `h`. -/
def Shdr.merges (h : Shdr) : Bool := h.flags / SHF_MERGE % 2 == 1

/-- What the symbol `s` of `o` (string table `str`) stands for:
- an absolute symbol (`SHN_ABS`): its value;
- an `STT_GNU_IFUNC` symbol, or one the object does not define (`SHN_UNDEF`, `SHN_COMMON`) or defines weakly: the
  symbol of its name, which the link resolves (a weak definition may give way to another object's; an IFUNC's
  references go through its PLT entry in a static executable, wherever it is defined);
- a symbol defined in a section of the object: its place there, a piece of a mergeable section (`SHF_MERGE`: equal
  strings or constants, which a linker keeps once) if the section is one.
`none` (not modelled) for a local symbol the object does not define (the null symbol), a symbol the link resolves by a
name that is not in the string table, a symbol of a section the object does not have (an index from `e_shnum` on) or
with another reserved section index (`SHN_XINDEX`; a weak or IFUNC one is resolved by its name, as above), and a
mergeable section's own symbol (`STT_SECTION`), which a linker resolves by the addend rather than the symbol's
value. -/
def symRef (o : Blob) (str : Shdr) (s : Sym) : Option SymRef :=
  if s.shndx = SHN_ABS then some (.abs s.value)
  else if s.type = STT_GNU_IFUNC ∨ s.shndx = SHN_UNDEF ∨ s.shndx = SHN_COMMON ∨ s.bind = STB_WEAK then
    if s.bind = STB_LOCAL ∧ s.shndx = SHN_UNDEF then none else (Obj.symName o str s).map .ext
  else if SHN_LORESERVE ≤ s.shndx then none
  else match Obj.shdr o s.shndx with
    | none => none
    | some h =>
      if h.merges then (if s.type = STT_SECTION then none else some (.piece s.shndx s.value))
      else some (.sec s.shndx s.value)

/-- A relocation of a function's bytes: the field's offset `off` from the function's start, the relocation's type
(`R_X86_64_*`), its addend, and what its symbol stands for. -/
structure FnReloc where
  off : Nat
  type : Nat
  addend : Addr
  target : SymRef

/-- A function of a relocatable object as it reads: the index of its section, its offset there (`st_value`), its
`st_size` bytes from the section, and the relocations whose fields lie among them, by ascending offset. -/
structure ObjFn where
  shndx : Nat
  value : Nat
  bytes : List Byte
  relocs : List FnReloc

/-- `R_X86_64_64`. -/
def R_X86_64_64 : Nat := 1
/-- `R_X86_64_PC32`. -/
def R_X86_64_PC32 : Nat := 2
/-- `R_X86_64_PLT32`. -/
def R_X86_64_PLT32 : Nat := 4
/-- `R_X86_64_GOTPCREL`. -/
def R_X86_64_GOTPCREL : Nat := 9
/-- `R_X86_64_32`. -/
def R_X86_64_32 : Nat := 10
/-- `R_X86_64_32S`. -/
def R_X86_64_32S : Nat := 11
/-- `R_X86_64_GOTTPOFF`. -/
def R_X86_64_GOTTPOFF : Nat := 22
/-- `R_X86_64_TPOFF32`. -/
def R_X86_64_TPOFF32 : Nat := 23
/-- `R_X86_64_REX_GOTPCRELX`. -/
def R_X86_64_REX_GOTPCRELX : Nat := 42

/-- The size of the field a relocation of type `t` writes, the psABI's table "Relocation Types", column "Field": 8 bytes
(`word64`) for `R_X86_64_64`, `DTPMOD64`, `DTPOFF64`, `TPOFF64`, `PC64`, `GOTOFF64`, `SIZE64`, `IRELATIVE`,
`RELATIVE64` (and `wordclass` in LP64: `GLOB_DAT`, `JUMP_SLOT`, `RELATIVE`), 16 for `TLSDESC` (two `word64`), 2 for
`R_X86_64_16` and `PC16`, 1 for `R_X86_64_8` and `PC8`, none for `R_X86_64_NONE`, `COPY` and `TLSDESC_CALL`, 4
(`word32`) for the others. -/
def Reloc.width (t : Nat) : Nat :=
  if t ∈ [1, 6, 7, 8, 16, 17, 18, 24, 25, 33, 37, 38] then 8
  else if t = 36 then 16
  else if t = 12 ∨ t = 13 then 2
  else if t = 14 ∨ t = 15 then 1
  else if t = 0 ∨ t = 5 ∨ t = 35 then 0
  else 4

/-- The relocations `rs` in ascending order of their offsets (an insertion sort, stable). The order in which a linker
applies relocations whose fields do not overlap does not matter (`ObjFn.link` requires that they do not). -/
def FnReloc.sort (rs : List FnReloc) : List FnReloc :=
  let rec ins (r : FnReloc) : List FnReloc → List FnReloc
    | [] => [r]
    | q :: qs => if q.off ≤ r.off then q :: ins r qs else r :: q :: qs
  rs.foldl (fun acc r => ins r acc) []

/-- The function named by the bytes `name` of the relocatable object `o`, read from its offset in its section
(`fromStart` false) or from the section's start (`fromStart` true), its `st_size` bytes (`toEnd` false: from the
section's start with `fromStart`, a combination no reader uses) or to the end of its section (`toEnd` true): its symbol (`Obj.fnSym`), those bytes of its section, and
the relocation entries for that section whose fields meet them (`Obj.relas`), with their symbols (`symRef`), by ascending
offset (`FnReloc.sort`); the reading's `value` is the offset its bytes start at. `none` where `o` is no relocatable object
of x86-64 this reader reads (`Obj.valid`), without a symbol table and its string table (`SHT_STRTAB`), without exactly
one defined function `name`, where the function does not lie in its section's bytes (a `SHT_NOBITS` section has none),
where a relocation's field begins before the bytes read, where a relocation's symbol is out of the table or not modelled
(`symRef`), or where an `R_X86_64_REX_GOTPCRELX` relocation's symbol is an `STT_GNU_IFUNC` one (not modelled,
`Reloc.apply`). -/
def Obj.readFnOf (o : Blob) (name : List Byte) (toEnd : Bool) (fromStart : Bool := false) : Option ObjFn := do
  if !Obj.valid o then none
  let (stIdx, st) ← Obj.symtab o
  let str ← Obj.shdr o st.link
  if str.type ≠ SHT_STRTAB then none
  let f ← Obj.fnSym o st str name
  let sec ← Obj.shdr o f.shndx
  if sec.type = SHT_NOBITS ∨ sec.size < f.value + f.size then none
  let start := if fromStart then 0 else f.value
  let len := if toEnd then sec.size - start else f.size
  let rs := (← Obj.relas o stIdx f.shndx).filter fun r =>
    r.offset < start + len ∧ start < r.offset + Reloc.width r.type
  if rs.any (·.offset < start) then none
  let relocs ← rs.mapM fun r => do
    let s ← Obj.sym o st r.sym
    -- (a load of an IFUNC's address the object defines: ld keeps its GOT slot, `Reloc.apply`)
    if r.type = R_X86_64_REX_GOTPCRELX ∧ s.type = STT_GNU_IFUNC then none
    let t ← symRef o str s
    some { off := r.offset - start, type := r.type, addend := r.addend, target := t }
  some { shndx := f.shndx, value := start,
         bytes := (List.range len).map fun i => o.bytes (sec.offset + start + i), relocs := FnReloc.sort relocs }

/-- The function named by the bytes `name` of the relocatable object `o`: its `st_size` bytes and the relocations
meeting them (`Obj.readFnOf`). -/
def Obj.fnOf (o : Blob) (name : List Byte) : Option ObjFn := Obj.readFnOf o name false

/-- The function `name` (its UTF-8 encoding, `utf8`) of the relocatable object `o` (`Obj.fnOf`). -/
def Obj.fn (o : Blob) (name : String) : Option ObjFn := Obj.fnOf o (utf8 name)

/-- The function named by the bytes `name` of the relocatable object `o` with the rest of its section: its bytes from
its offset to the section's end rather than its `st_size`, and the relocations meeting them (`Obj.readFnOf`). For code
that runs past its symbol into the section's next one: glibc's `memset` variants are assembly whose entries jump
forward into the next entry's body (`sysdeps/x86_64/multiarch/memset-vec-unaligned-erms.S`: below 16 and above 32
bytes `__memset_sse2_unaligned` runs `__memset_sse2_unaligned_erms`' code), so what a call of `name` runs is the section
from `name` on; GNU ld copies an input section whole. `none` where `Obj.fnOf` is, and also where a relocation in the
rest of the section has a symbol `symRef` refuses or is an `R_X86_64_REX_GOTPCRELX` of an `STT_GNU_IFUNC` symbol
(`Obj.fnOf` reads those relocations only where they meet the function's own bytes). -/
def Obj.fnRestOf (o : Blob) (name : List Byte) : Option ObjFn := Obj.readFnOf o name true

/-- The function `name` (its UTF-8 encoding) of the relocatable object `o` with the rest of its section
(`Obj.fnRestOf`). -/
def Obj.fnRest (o : Blob) (name : String) : Option ObjFn := Obj.fnRestOf o (utf8 name)

/-- The section of the relocatable object `o` that holds the function named by the bytes `name`, read whole: its bytes
from the section's start to its end and every relocation of it (`Obj.readFnOf`, an `ObjFn` at `value` 0). For code
entered at the function that runs anywhere in its section, before the function as after it: glibc's
`__memset_evex_unaligned_erms` jumps back into `__memset_evex_unaligned`'s body below 32 bytes
(`sysdeps/x86_64/multiarch/memset-vec-unaligned-erms.S`). `none` where `o` is no object this reader reads, without
exactly one defined function `name`, where the function does not lie in its section's bytes, or where a relocation of
the section has a symbol `symRef` refuses or is an `R_X86_64_REX_GOTPCRELX` of an `STT_GNU_IFUNC` symbol
(`Obj.readFnOf`). Unlike `Obj.fnOf` it reads a relocation that begins before the function and reaches into it;
`Obj.linkedSecOf` asks for `Obj.fnOf` too. -/
def Obj.secFnOf (o : Blob) (name : List Byte) : Option ObjFn := Obj.readFnOf o name true true

/-- The section of the relocatable object `o` that holds the function `name` (its UTF-8 encoding), read whole
(`Obj.secFnOf`). -/
def Obj.secFn (o : Blob) (name : String) : Option ObjFn := Obj.secFnOf o (utf8 name)

/-! ## A section by its name -/

/-- The index of the section that holds the sections' names, `e_shstrndx` (file header offset 62, 2 bytes). -/
def Obj.shstrndx (o : Blob) : Nat := leNat o.bytes 62 2

/-- The section of the ELF file `o` named by the bytes `name`: its index and header, for the only section whose name
(`sh_name`, an offset in the section-name string table `e_shstrndx`) is those bytes. `none` where that table is no
section of `o` or no string table (`SHT_STRTAB`; an `e_shstrndx` of `SHN_XINDEX`, whose index is in section 0's
`sh_link`, is not read), or where no section or more than one has the name. Section headers are the gABI's in any ELF
file, so this reads an executable's sections as well as an object's. -/
def Obj.secNamedOf (o : Blob) (name : List Byte) : Option (Nat × Shdr) := do
  let sstr ← Obj.shdr o (Obj.shstrndx o)
  if sstr.type ≠ SHT_STRTAB then none
  match (Obj.shdrs o).zipIdx.filter fun (h, _) =>
      h.name + name.length + 1 ≤ sstr.size && bytesMatch o.bytes (sstr.offset + h.name) (name ++ [0]) with
  | [(h, i)] => some (i, h)
  | _ => none

/-- The section named by the bytes `name` of the relocatable object `o`, read whole: its index (`Obj.secNamedOf`), its
bytes from its start (`value` 0) to its end, and every relocation entry for it (`Obj.relas`) with its symbol (`symRef`),
by ascending offset, as `Obj.readFnOf` reads a function's section. For code no symbol spans: `crti.o`'s `.init`, the
start of a function that `crtn.o`'s `.init` ends (`Obj.linkedOutOf`). `none` where `o` is no relocatable object of
x86-64 this reader reads (`Obj.valid`), without exactly one section of the name, where the section has no bytes in the
file (`SHT_NOBITS`), where `o` has a symbol table without its string table (`SHT_STRTAB`) or none while a relocation
section applies to the section (an object without symbols, `crtn.o`, has no relocations), or where a relocation's
symbol is out of the table, not modelled (`symRef`), or an `STT_GNU_IFUNC` one of an `R_X86_64_REX_GOTPCRELX`
relocation. -/
def Obj.secOf (o : Blob) (name : List Byte) : Option ObjFn := do
  if !Obj.valid o then none
  let (i, sec) ← Obj.secNamedOf o name
  if sec.type = SHT_NOBITS then none
  let relocs ← match Obj.symtab o with
    | none =>
      if (Obj.shdrs o).any fun r => (r.type == SHT_RELA || r.type == SHT_REL) && r.info == i then none else some []
    | some (stIdx, st) => do
      let str ← Obj.shdr o st.link
      if str.type ≠ SHT_STRTAB then none
      (← Obj.relas o stIdx i).mapM fun r => do
        let s ← Obj.sym o st r.sym
        if r.type = R_X86_64_REX_GOTPCRELX ∧ s.type = STT_GNU_IFUNC then none
        let t ← symRef o str s
        some { off := r.offset, type := r.type, addend := r.addend, target := t }
  some { shndx := i, value := 0, bytes := (List.range sec.size).map fun k => o.bytes (sec.offset + k),
         relocs := FnReloc.sort relocs }

/-! ## A static link -/

/-- A static link of an object into an executable by GNU ld, with the relaxations ld makes in a static executable
(`Reloc.apply`). Each name a key below is a symbol's name, its bytes; a statement names a symbol by a string through
`Link.addr`, `Link.tlsOff`, `Link.callTo`, `Link.gotSlot`.

- `sec i`: the address where it places section `i` (for a section of thread-local storage, `SHF_TLS`, its offset from
  the thread pointer, as a 64-bit word: below it in x86-64's TLS layout). A section other than a mergeable one is
  placed whole: its bytes at its address on, in their order;
- `merged i v`: the address it gives the byte at offset `v` of a mergeable section `i` (`SHF_MERGE`: the linker keeps
  one copy of equal strings or constants of such sections, of this object and others, anywhere in its output section);
- `sym n`: the address it gives the symbol named `n` that the object takes from elsewhere (`SymRef.ext`), its address
  in the executable (an `STT_GNU_IFUNC` symbol's is its PLT entry in a static executable, which ld makes the symbol's
  address so that pointers to it compare equal; psABI, "Symbol Table"), and 0 for an undefined weak symbol (gABI,
  "Symbol Table": an unresolved weak reference has the value zero);
- `tpoff n`: the offset from the thread pointer it gives the thread-local symbol named `n` (`STT_TLS`) that the object
  takes from elsewhere, as a 64-bit word;
- `plt n`: the procedure linkage table entry it made for the symbol named `n`, if any, where a call through `PLT32`
  goes (psABI, "Relocation Types": `L`): in a static executable only for an `STT_GNU_IFUNC` symbol (the entry jumps
  through a slot glibc's startup fills with the resolver's choice), in a position-independent executable or shared
  object for a symbol another module may define;
- `ifunc n`: whether the symbol named `n` may be an `STT_GNU_IFUNC` symbol of the executable: `false` only for a name
  the link resolves to a symbol of another type (or to none, an undefined weak one); `true` by default, which models no
  relaxation that depends on it (`Reloc.apply` of `R_X86_64_REX_GOTPCRELX`: ld keeps an IFUNC's load from its GOT slot,
  whether or not it made a PLT entry for it);
- `got n`: the address of the global offset table's slot it made for the symbol named `n`, which an
  `R_X86_64_GOTPCREL` field it keeps reaches (psABI, "Relocation Types": `G + GOT`). In a static executable the slot is
  in the executable's `.got` and holds the symbol's address (0 for an undefined weak symbol). Exceptions observed
  with GNU ld 2.46: an `STT_GNU_IFUNC` symbol with a PLT entry is reached through that entry's `.got.plt` slot, which
  holds the lazy stub's address until glibc's startup applies its `IRELATIVE` relocation (the resolver's choice), one
  without through a `.got` slot filled the same way; for a thread-local symbol ld accepts the relocation and the slot
  holds the TLS template's link-time address, not the thread's variable. What the word is, is memory, the process's
  and not the
  link's: a statement that relies on it states it as its hypothesis. Only the names of the `GOTPCREL` fields the link
  keeps matter; a link of an object without one need not give it (the default). -/
structure Link where
  sec : Nat → Addr
  merged : Nat → Nat → Addr
  sym : List Byte → Addr
  tpoff : List Byte → Addr
  plt : List Byte → Option Addr
  ifunc : List Byte → Bool := fun _ => true
  got : List Byte → Addr := fun _ => 0

/-- Where a call through a PLT to the symbol named by the bytes `n` goes in the link `L`: its PLT entry if the link
made one, its address otherwise. -/
def Link.callToOf (L : Link) (n : List Byte) : Addr := (L.plt n).getD (L.sym n)

/-- The address the link `L` gives the symbol `n` (`Link.sym` of its UTF-8 encoding). -/
def Link.addr (L : Link) (n : String) : Addr := L.sym (utf8 n)

/-- The offset from the thread pointer the link `L` gives the thread-local symbol `n` (`Link.tpoff` of its UTF-8
encoding). -/
def Link.tlsOff (L : Link) (n : String) : Addr := L.tpoff (utf8 n)

/-- Where a call to the symbol `n` goes in the link `L` (`Link.callToOf` of its UTF-8 encoding). -/
def Link.callTo (L : Link) (n : String) : Addr := L.callToOf (utf8 n)

/-- The address of the GOT slot the link `L` made for the symbol `n` (`Link.got` of its UTF-8 encoding). -/
def Link.gotSlot (L : Link) (n : String) : Addr := L.got (utf8 n)

/-- The value `S` a relocation's symbol has in the link `L`: a place in a section the section's address plus the
offset, a place in a mergeable section where the link put that byte, an absolute value itself, another symbol the
link's address of it. -/
def SymRef.value (L : Link) : SymRef → Addr
  | .sec i v => L.sec i + BitVec.ofNat 64 v
  | .piece i v => L.merged i v
  | .abs v => BitVec.ofNat 64 v
  | .ext n => L.sym n

/-- The offset from the thread pointer of a thread-local relocation's symbol in the link `L`: a place in a section
of thread-local storage that section's offset (`Link.sec`) plus the place's, another symbol the link's offset of it
(`Link.tpoff`). -/
def SymRef.tlsValue (L : Link) : SymRef → Addr
  | .ext n => L.tpoff n
  | r => r.value L

/-- Where a call through `PLT32` to a relocation's symbol goes in the link `L`: for a symbol the link resolves by
name, `Link.callToOf`; for one the object defines, its place. -/
def SymRef.callValue (L : Link) : SymRef → Addr
  | .ext n => L.callToOf n
  | r => r.value L

/-- The GOT slot a `GOTPCREL` relocation's symbol reaches in the link `L`: for a symbol the link resolves by name, its
slot (`Link.got`); for a place of the object, which `Reloc.apply` does not model with this kind, its value. -/
def SymRef.gotValue (L : Link) : SymRef → Addr
  | .ext n => L.got n
  | r => r.value L

/-- The symbol is one the link resolves by name (`SymRef.ext`). -/
def SymRef.byName : SymRef → Bool
  | .ext _ => true
  | _ => false

/-- The value the link `L` gives the symbol named by the bytes `name` of the object `o`, as a relocation against it
uses it (`symRef`, `SymRef.value`): for a symbol the object defines (not weakly), its section's address plus its
offset there. `none` where `o` is no object this reader reads (`Obj.valid`, a string table `SHT_STRTAB`), the
object has not exactly one symbol so named that is not a section's, or it is not modelled (`symRef`). -/
def Obj.symAddrOf (o : Blob) (L : Link) (name : List Byte) : Option Addr := do
  if !Obj.valid o then none
  let (_, st) ← Obj.symtab o
  let str ← Obj.shdr o st.link
  if str.type ≠ SHT_STRTAB then none
  match ((List.range (st.size / 24)).filterMap (Obj.sym o st)).filter fun s =>
      s.type ≠ STT_SECTION && Obj.named o str s name with
  | [s] => (symRef o str s).map (·.value L)
  | _ => none

/-- The value the link `L` gives the symbol `name` (its UTF-8 encoding) of the object `o` (`Obj.symAddrOf`): what a
statement about an object's function names its static data by (`main_arena`, a `static` variable of the object). For a
thread-local symbol of the object (`STT_TLS`, in an `SHF_TLS` section) it is its offset from the thread pointer, as
`Link.sec` places that section (glibc's `__libc_tsd_CTYPE_B`). -/
def Obj.symAddr (o : Blob) (L : Link) (name : String) : Option Addr := Obj.symAddrOf o L (utf8 name)

/-! ## Relocations in the linker's terms -/

/-- The value `v` fits a signed 32-bit field: it is the sign extension of its low 32 bits. GNU ld checks this of the
fields below (`complain_overflow_signed`); a `rip`-relative displacement, a `call rel32` and a sign-extended
immediate need it to reach `v`. -/
def Reloc.Fit (v : Addr) : Prop := (v.setWidth 32).signExtend 64 = v

instance (v : Addr) : Decidable (Reloc.Fit v) := inferInstanceAs (Decidable (_ = _))

/-- The `n` bytes of `v` from the field at offset `off` on, least significant first. -/
def Reloc.field (off : Nat) (v : Addr) (n : Nat) : List (Nat × Byte) :=
  (List.range n).map fun j => (off + j, (v >>> (8 * j)).setWidth 8)

/-- What a static link writes for the relocation `r` of a function whose bytes are `bs`, where its symbol's value is
`S` (`FnReloc.symValue`), the field's address is `P` and `ifunc` says whether the symbol may be an `STT_GNU_IFUNC` one
(`FnReloc.mayIfunc`): the bytes at offsets of the function (the field's, and for a
relaxed instruction the ones before it), or `none` where the relocation is not modelled or does not fit. With `A`
the addend, as the psABI's table "Relocation Types" says:

- `R_X86_64_64`: the 8 bytes of `S + A`;
- `R_X86_64_PC32`: the 4 bytes of `S + A - P`, which must fit (`Reloc.Fit`);
- `R_X86_64_PLT32`: the 4 bytes of `L + A - P` with `L` where the call goes, the symbol's PLT entry or, without one,
  the symbol (`FnReloc.symValue`, `Link.callTo`), passed here as `S`; it must fit;
- `R_X86_64_32` and `R_X86_64_32S`: the 4 bytes of `S + A`, which must zero-extend (`32`: below `2 ^ 32`) or
  sign-extend (`32S`: `Reloc.Fit`) to it, the check the psABI asks of the linker ("Relocation Types": "the linker must
  verify that the generated value for the R_X86_64_32 (R_X86_64_32S) relocation zero-extends (sign-extends) to the
  original 64-bit value"); an absolute address in code that is not position-independent (gcc's `crtbeginT.o`:
  `mov $sym, %eax`, `cmp $sym, %rax`);
- `R_X86_64_TPOFF32`: the 4 bytes of `S + A`, `S` the thread-local symbol's offset from the thread pointer, which must
  fit;
- `R_X86_64_GOTTPOFF` of `mov sym@gottpoff(%rip), %reg` (the bytes `48 8b` or `4c 8b` and a ModRM byte `00 reg 101`
  before the field): GNU ld rewrites it in a static executable to `mov $tpoff, %reg` (`48 c7` or `49 c7` and the ModRM
  byte `11 000 reg`) with the 4 bytes of `S`, the thread-local symbol's offset from the thread pointer, as the
  immediate (the initial-exec access relaxed to local-exec; the addend, which points the original at its GOT slot, is
  not used). It must fit here: whether ld checks it was not established, so a link
  where it does not fit has no bytes here rather than ld's. Another instruction with this relocation, or a link that
  keeps the GOT slot, is not modelled;
- `R_X86_64_REX_GOTPCRELX` of `mov sym@GOTPCREL(%rip), %reg` with a 64-bit register (the bytes `48 8b` or `4c 8b` and a
  ModRM byte `00 reg 101` before the field, the addend `-4`) against a symbol that is no `STT_GNU_IFUNC` one (`ifunc`
  false): GNU ld rewrites it in an executable that is not position-independent to `mov $sym, %reg` (`48 c7` or `49 c7`
  and the ModRM byte `11 000 reg`) with the 4 bytes of `S`, the symbol's address (`Link.sym`: 0 for an undefined weak
  one), as the immediate, which the processor sign-extends: the psABI's "Optimize GOTPCRELX Relocations", "Convert
  mov", for a symbol "defined locally"; ld's check is that the address fits the sign-extended immediate (an absolute
  `0xffffffff80001000` is relaxed too), here `Reloc.Fit`. Where ld keeps the load from the GOT slot, nothing is
  modelled: an IFUNC (its slot gets the resolver's choice), an address that does not fit, `--no-relax`; so is another
  instruction with this relocation and a position-independent link (ld writes `lea sym(%rip), %reg` there);
- `R_X86_64_GOTPCREL` of an instruction that is no `mov` (the byte before the ModRM byte is not `8b`), against a symbol
  the link resolves by name (`SymRef.byName`): the 4 bytes of `G + GOT + A - P` with `G + GOT` the symbol's GOT slot
  (`Link.got`), passed here as `S`; it must fit. GNU ld keeps the slot for such an instruction (glibc's `cmp qword
  [rip + sym@GOTPCREL], 0` of a weak function, a `movq` into an SSE register; observed: `call *`, `add` too); it
  rewrites a `mov` with this relocation to `lea sym(%rip), %reg` (observed in a static executable: with the addend `-4`,
  an undefined weak symbol's too; not with another addend), which is not modelled, nor is a place of the object (a
  symbol the object defines non-weakly, local or global, `symRef`'s `sec` or `piece`, whose slot the link does not
  name). A thread-local symbol's slot holds the TLS template's link-time address (`Link.got`); the field is the
  slot's address all the same.

The relaxations are GNU ld's (binutils 2.46, with which the programs here were linked); the psABI, "Relocation
Types" and "Linker Optimization", names the instruction forms and leaves the relaxation to the linker. -/
def Reloc.apply (bs : List Byte) (r : FnReloc) (S P : Addr) (ifunc : Bool) : Option (List (Nat × Byte)) :=
  if r.type = R_X86_64_64 then some (Reloc.field r.off (S + r.addend) 8)
  else if r.type = R_X86_64_PC32 ∨ r.type = R_X86_64_PLT32 then
    if Reloc.Fit (S + r.addend - P) then some (Reloc.field r.off (S + r.addend - P) 4) else none
  else if r.type = R_X86_64_32 then
    if (S + r.addend).toNat < 2 ^ 32 then some (Reloc.field r.off (S + r.addend) 4) else none
  else if r.type = R_X86_64_32S then
    if Reloc.Fit (S + r.addend) then some (Reloc.field r.off (S + r.addend) 4) else none
  else if r.type = R_X86_64_TPOFF32 then
    if Reloc.Fit (S + r.addend) then some (Reloc.field r.off (S + r.addend) 4) else none
  else if r.type = R_X86_64_GOTTPOFF ∧ 3 ≤ r.off then
    let rex := bs.getD (r.off - 3) 0
    let modrm := bs.getD (r.off - 1) 0
    if (rex = 0x48 ∨ rex = 0x4c) ∧ bs.getD (r.off - 2) 0 = 0x8b ∧ modrm &&& 0xc7 = 0x05 ∧ Reloc.Fit S then
      some ([(r.off - 3, if rex = 0x4c then (0x49 : Byte) else 0x48), (r.off - 2, 0xc7),
             (r.off - 1, 0xc0 ||| ((modrm >>> 3) &&& 7))] ++ Reloc.field r.off S 4)
    else none
  else if r.type = R_X86_64_REX_GOTPCRELX ∧ 3 ≤ r.off then
    let rex := bs.getD (r.off - 3) 0
    let modrm := bs.getD (r.off - 1) 0
    if (rex = 0x48 ∨ rex = 0x4c) ∧ bs.getD (r.off - 2) 0 = 0x8b ∧ modrm &&& 0xc7 = 0x05 ∧ r.addend = -4 ∧
        ifunc = false ∧ Reloc.Fit S then
      some ([(r.off - 3, if rex = 0x4c then (0x49 : Byte) else 0x48), (r.off - 2, 0xc7),
             (r.off - 1, 0xc0 ||| ((modrm >>> 3) &&& 7))] ++ Reloc.field r.off S 4)
    else none
  else if r.type = R_X86_64_GOTPCREL ∧ 2 ≤ r.off then
    if bs.getD (r.off - 2) 0 ≠ 0x8b ∧ r.target.byName ∧ Reloc.Fit (S + r.addend - P) then
      some (Reloc.field r.off (S + r.addend - P) 4)
    else none
  else none

/-- The value `S` (for `PLT32`, `L`; for `GOTPCREL`, `G + GOT`) the link `L` gives the relocation `r`'s symbol, as its
kind computes with it: a thread-local symbol's offset from the thread pointer for `R_X86_64_TPOFF32` and `GOTTPOFF`
(`SymRef.tlsValue`), the call's target for `PLT32` (`SymRef.callValue`), the symbol's GOT slot for `GOTPCREL`
(`SymRef.gotValue`), the symbol's value otherwise (`SymRef.value`). -/
def FnReloc.symValue (L : Link) (r : FnReloc) : Addr :=
  if r.type = R_X86_64_TPOFF32 ∨ r.type = R_X86_64_GOTTPOFF then r.target.tlsValue L
  else if r.type = R_X86_64_PLT32 then r.target.callValue L
  else if r.type = R_X86_64_GOTPCREL then r.target.gotValue L
  else r.target.value L

/-! ## A function as the link places it -/

/-- Whether the relocation `r`'s symbol may be an `STT_GNU_IFUNC` one in the link `L`: one the link resolves by name
(`SymRef.ext`, also an IFUNC the object defines, `symRef`) where the link says so (`Link.ifunc`); a place in the
object's own sections is none. -/
def FnReloc.mayIfunc (L : Link) (r : FnReloc) : Bool :=
  match r.target with
  | .ext n => L.ifunc n
  | _ => false

/-- The bytes a relocation writes, `[start, end)` from the function's start: its field (`Reloc.width`), and for a
`GOTTPOFF` or `REX_GOTPCRELX` the instruction's three bytes before it. -/
def FnReloc.span (r : FnReloc) : Nat × Nat :=
  (if r.type = R_X86_64_GOTTPOFF ∨ r.type = R_X86_64_REX_GOTPCRELX then r.off - 3 else r.off,
    r.off + Reloc.width r.type)

/-- The relocations `rs`, by ascending offset, write bytes apart from each other's (`FnReloc.span`). -/
def FnReloc.apart : List FnReloc → Bool
  | a :: b :: rest => a.span.2 ≤ b.span.1 && FnReloc.apart (b :: rest)
  | _ => true

/-- The bytes `bs` with those of `ps` (offset, byte) in their place, the first pair for an offset counting. -/
def patchBytes (bs : List Byte) (ps : List (Nat × Byte)) : List Byte :=
  bs.zipIdx.map fun (b, i) => (ps.lookup i).getD b

/-- The function `f` as the link `L` places it: its address, its section's address plus its offset there, and its
bytes with each relocation applied (`Reloc.apply` with its symbol's value `FnReloc.symValue`, the field's address the
function's plus the field's offset, whether the symbol may be an IFUNC `FnReloc.mayIfunc`). `none` where two relocations write the same bytes (`FnReloc.apart`), where a
relocation is not modelled or does not fit, or where it writes past the function's bytes. -/
def ObjFn.link (f : ObjFn) (L : Link) : Option (Addr × List Byte) := do
  if !FnReloc.apart f.relocs then none
  let e := L.sec f.shndx + BitVec.ofNat 64 f.value
  let pss ← f.relocs.mapM fun r => Reloc.apply f.bytes r (r.symValue L) (e + BitVec.ofNat 64 r.off) (r.mayIfunc L)
  let ps := pss.flatten
  if ps.all (·.1 < f.bytes.length) then some (e, patchBytes f.bytes ps) else none

/-- The function `name` (its UTF-8 encoding) of the relocatable object `o` as the link `L` places it (`Obj.fn`,
`ObjFn.link`): its address and its bytes there. A statement about the function names it so: for every link under
which this is `some (e, bs)`, the bytes `bs` at `e` do what it says (and nothing for a link under which it is `none`:
a statement's instances show that their links give `some`). -/
def Obj.linkedFn (o : Blob) (L : Link) (name : String) : Option (Addr × List Byte) :=
  (Obj.fn o name).bind (·.link L)

/-- The function named by the bytes `name` of the relocatable object `o` as the link `L` places it (`Obj.fnOf`). -/
def Obj.linkedFnOf (o : Blob) (L : Link) (name : List Byte) : Option (Addr × List Byte) :=
  (Obj.fnOf o name).bind (·.link L)

/-- The function `name` of the relocatable object `o` with the rest of its section (`Obj.fnRest`) as the link `L`
places it: its address and the bytes from there to the section's end. A statement about code that runs on into its
section's next symbol names it so, as `Obj.linkedFn` a function's own bytes. -/
def Obj.linkedFnRest (o : Blob) (L : Link) (name : String) : Option (Addr × List Byte) :=
  (Obj.fnRest o name).bind (·.link L)

/-- The function named by the bytes `name` of the relocatable object `o` with its whole section around it as the link `L`
places it: the section's address `b` and its bytes there (`Obj.secFnOf`, `ObjFn.link`), and between them the function's
entry, `b` plus the function's offset in the section (`Obj.fnOf`'s `value`). A statement about code that runs anywhere
in its section names it so: for every link under which this is `some (b, e, bs)`, a call of the function at `e` with
the bytes `bs` at `b` does what it says. -/
def Obj.linkedSecOf (o : Blob) (L : Link) (name : List Byte) : Option (Addr × Addr × List Byte) := do
  let f ← Obj.fnOf o name
  let (b, bs) ← (← Obj.secFnOf o name).link L
  some (b, b + BitVec.ofNat 64 f.value, bs)

/-- The function `name` (its UTF-8 encoding) of the relocatable object `o` with its whole section around it as the link
`L` places it (`Obj.linkedSecOf`): the section's address, the function's entry, the section's bytes. -/
def Obj.linkedSec (o : Blob) (L : Link) (name : String) : Option (Addr × Addr × List Byte) :=
  Obj.linkedSecOf o L (utf8 name)

/-- The output section named by the bytes `name` that a static link assembles from the sections of that name of the
objects `parts`, each with the link `L` that places it, in link order: each object's section read whole (`Obj.secOf`)
and placed whole by its own link with its relocations applied (`ObjFn.link`), the next one where it ends. The address
of the first and the bytes of all, one after the other. `none` where a part has no section of the name as `Obj.secOf`
reads it, a link gives it no bytes, a part does not begin where the one before ends (GNU ld pads input sections to
their alignment, with a fill this reader does not know), or there are no parts.

GNU ld builds a function from several objects this way: its default linker script puts the input sections `.init` in
the order of the input files (`KEEP (*(SORT_NONE(.init)))`, as `ld --verbose` prints it), among which gcc's driver
puts `crti.o` before and `crtn.o` after every other object, so `_init` is `crti.o`'s `.init` (its prologue and the call
of `__gmon_start__`), the `.init` of any object linked between, then `crtn.o`'s (its epilogue), and its symbol has size
0 (glibc 2.43 `sysdeps/x86_64/crti.S`, `crtn.S`). A statement about `_init` lists the parts its program links; the
program's own bytes there (`Exe.sec`) are what a client compares. -/
def Obj.linkedOutOf : List (Blob × Link) → List Byte → Option (Addr × List Byte)
  | [], _ => none
  | [(o, L)], name => (Obj.secOf o name).bind (·.link L)
  | (o, L) :: ps, name => do
    let (a, bs) ← (← Obj.secOf o name).link L
    let (b, cs) ← Obj.linkedOutOf ps name
    if b = a + BitVec.ofNat 64 bs.length then some (a, bs ++ cs) else none

/-- The output section `name` (its UTF-8 encoding) a static link assembles from the objects `parts` (`Obj.linkedOutOf`):
its address and its bytes. -/
def Obj.linkedOut (parts : List (Blob × Link)) (name : String) : Option (Addr × List Byte) :=
  Obj.linkedOutOf parts (utf8 name)

/-! ## Static archives -/

/-- The archive's magic string `!<arch>\n` (`ARMAG`, 8 bytes) begins the bytes `rd`. -/
def arMagic (rd : Nat → Byte) : Bool :=
  (List.range 8).map rd == [0x21, 0x3c, 0x61, 0x72, 0x63, 0x68, 0x3e, 0x0a]

/-- The decimal number in ASCII in the `n` bytes at `off` of `rd`, up to the first byte that is not a digit (the
fields of `struct ar_hdr` are padded with spaces). -/
def arDecimal (rd : Nat → Byte) (off : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc =>
    let c := (rd off).toNat
    if 48 ≤ c ∧ c < 58 then arDecimal rd (off + 1) n (10 * acc + (c - 48)) else acc

/-- The member header (`struct ar_hdr`, 60 bytes) at `h` names the member `name`: its `ar_name` (16 bytes) is the name
followed by `/` (System V's form for names up to 15 bytes), or `/` and the decimal offset of the name in the archive's
name table `//` (its data at `t`, `len` bytes: `names = some (t, len)`), where the name is followed by `/` and a
newline. -/
def arNamed (rd : Nat → Byte) (names : Option (Nat × Nat)) (h : Nat) (name : List Byte) : Bool :=
  let short := name.length < 16 &&
    (List.range (name.length + 1)).map (fun j => rd (h + j)) == name ++ [0x2f]
  let long := match names with
    | some (t, len) =>
      let o := arDecimal rd (h + 1) 15 0
      rd h == 0x2f && 48 ≤ (rd (h + 1)).toNat && (rd (h + 1)).toNat < 58 && o + name.length + 2 ≤ len &&
        (List.range (name.length + 2)).map (fun j => rd (t + o + j)) == name ++ [0x2f, 0x0a]
    | none => false
  short || long

/-- The member named by the bytes `name` of the archive `a`: the offset of its data and its size (`ar_size`, offset
48 of its header, 10 bytes), for the first member so named. After the magic string, each member is its 60-byte header,
which ends with `ARFMAG` (`` `\n ``), and its data, padded to an even offset; the member `//` holds the long names.
`none` where `a` is no archive, a header or a member's data does not lie in the file, or no member has the name. -/
def Ar.findOf (a : Blob) (name : List Byte) : Option (Nat × Nat) :=
  let rec go (fuel h : Nat) (names : Option (Nat × Nat)) : Option (Nat × Nat) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      if a.size < h + 60 then none else
      let size := arDecimal a.bytes (h + 48) 10 0
      if !(a.bytes (h + 58) == 0x60 && a.bytes (h + 59) == 0x0a) || a.size < h + 60 + size then none else
      if arNamed a.bytes names h name then some (h + 60, size) else
      let names :=
        if (List.range 3).map (fun j => a.bytes (h + j)) == [0x2f, 0x2f, 0x20] then some (h + 60, size) else names
      go fuel (h + 60 + size + size % 2) names
  if 8 ≤ a.size && arMagic a.bytes then go (a.size / 60) 8 none else none

/-- The member named by the bytes `name` of the archive `a` (`Ar.findOf`): its bytes and size; the empty file
(`Blob.empty`, which no reader accepts) where it has none. -/
def Ar.memberOf (a : Blob) (name : List Byte) : Blob :=
  match Ar.findOf a name with
  | some (off, size) => ⟨fun i => a.bytes (off + i), size⟩
  | none => Blob.empty

/-- The member `name` (its UTF-8 encoding) of the archive `a` (`Ar.memberOf`). -/
def Ar.member (a : Blob) (name : String) : Blob := Ar.memberOf a (utf8 name)

end ZellicX86
