import ZellicX86.Spec.Word
/-!
# The ELF file format: header, program headers, dynamic symbols

The parts of a 64-bit little-endian ELF file that Linux reads to start a program: the file
header and the program header table. Sections and relocations are not read by the kernel and are
not here. What Linux does with these fields is `Spec/Linux/Exec.lean`. And the dynamic symbol table
of a shared object, by which the vDSO's functions are found (`LinuxBoot.vdsoEntry`, `Spec/Vdso.lean`).

Source: Linux v6.18 `include/uapi/linux/elf.h` (`Elf64_Ehdr`, `Elf64_Phdr`, `Elf64_Dyn`,
`Elf64_Sym`, the `PT_`, `PF_`, `ET_`, `EM_` and `DT_` constants), which follows the System V gABI,
"ELF Header", "Program Header", "Dynamic Section", "Symbol Table" and "Hash Table".
-/
namespace ZellicX86

/-- The little-endian number in the `n` bytes at offset `off` of the byte sequence `rd`. -/
def leNat (rd : Nat → Byte) (off : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (rd off).toNat + 256 * leNat rd (off + 1) n

/-- The fields of the ELF file header (`Elf64_Ehdr`, 64 bytes) that Linux reads, besides the
magic number. -/
structure ElfHeader where
  /-- `e_type` (offset 16, 2 bytes): `ET_EXEC` = 2, `ET_DYN` = 3. -/
  type : Nat
  /-- `e_machine` (offset 18, 2 bytes): `EM_X86_64` = 62. -/
  machine : Nat
  /-- `e_entry` (offset 24, 8 bytes): the entry point. -/
  entry : Nat
  /-- `e_phoff` (offset 32, 8 bytes): file offset of the program header table. -/
  phoff : Nat
  /-- `e_phentsize` (offset 54, 2 bytes): size of one program header. -/
  phentsize : Nat
  /-- `e_phnum` (offset 56, 2 bytes): number of program headers. -/
  phnum : Nat

/-- Whether `rd` starts with the ELF magic number `7f 'E' 'L' 'F'` (`ELFMAG`). -/
def elfMagic (rd : Nat → Byte) : Bool :=
  rd 0 == 0x7f && rd 1 == 0x45 && rd 2 == 0x4c && rd 3 == 0x46

/-- The file header in the bytes `rd`. -/
def ElfHeader.read (rd : Nat → Byte) : ElfHeader :=
  { type := leNat rd 16 2, machine := leNat rd 18 2, entry := leNat rd 24 8,
    phoff := leNat rd 32 8, phentsize := leNat rd 54 2, phnum := leNat rd 56 2 }

/-- `e_type` of an executable file. -/
def ET_EXEC : Nat := 2
/-- `e_type` of a shared object, also used for position-independent executables. -/
def ET_DYN : Nat := 3
/-- `e_machine` of x86-64. -/
def EM_X86_64 : Nat := 62

/-- A program header (`Elf64_Phdr`, 56 bytes), without `p_paddr` and `p_align`, which Linux
ignores for an `ET_EXEC` file. -/
structure Phdr where
  /-- `p_type` (offset 0, 4 bytes). -/
  type : Nat
  /-- `p_flags` (offset 4, 4 bytes): `PF_X` = 1, `PF_W` = 2, `PF_R` = 4. -/
  flags : Nat
  /-- `p_offset` (offset 8, 8 bytes): file offset of the segment. -/
  offset : Nat
  /-- `p_vaddr` (offset 16, 8 bytes): virtual address of the segment. -/
  vaddr : Nat
  /-- `p_filesz` (offset 32, 8 bytes): bytes of the segment in the file. -/
  filesz : Nat
  /-- `p_memsz` (offset 40, 8 bytes): bytes of the segment in memory. -/
  memsz : Nat

/-- The size of a program header, `sizeof (Elf64_Phdr)`. -/
def phdrSize : Nat := 56

/-- The program header at file offset `off` of the bytes `rd`. -/
def Phdr.read (rd : Nat → Byte) (off : Nat) : Phdr :=
  { type := leNat rd off 4, flags := leNat rd (off + 4) 4, offset := leNat rd (off + 8) 8,
    vaddr := leNat rd (off + 16) 8, filesz := leNat rd (off + 32) 8,
    memsz := leNat rd (off + 40) 8 }

/-- The `n` program headers of the table at file offset `off`. -/
def readPhdrs (rd : Nat → Byte) (off n : Nat) : List Phdr :=
  (List.range n).map fun i => Phdr.read rd (off + phdrSize * i)

/-- `p_type` of a loadable segment. -/
def PT_LOAD : Nat := 1
/-- `p_type` of the program interpreter's path. -/
def PT_INTERP : Nat := 3
/-- `p_type` of the header for the stack's permissions (`PF_X`: executable stack). -/
def PT_GNU_STACK : Nat := 0x6474e551

/-- Whether flag bit `bit` (`PF_X` = 1, `PF_W` = 2, `PF_R` = 4) is set in `p_flags`. -/
def Phdr.hasFlag (ph : Phdr) (bit : Nat) : Bool := ph.flags / bit % 2 == 1

/-! ## Dynamic symbols

Of an image whose addresses are its offsets: linked at address 0 and loaded from offset 0, as the
vDSO is (`arch/x86/entry/vdso/vdso-layout.lds.S`), so that the dynamic section's addresses can be
read as offsets. -/

/-- `p_type` of the dynamic section. -/
def PT_DYNAMIC : Nat := 2
/-- `d_tag` of the dynamic section's last entry. -/
def DT_NULL : Nat := 0
/-- `d_tag` of the address of the symbol hash table, whose second word is the number of symbols
(`nchain`). -/
def DT_HASH : Nat := 4
/-- `d_tag` of the address of the string table. -/
def DT_STRTAB : Nat := 5
/-- `d_tag` of the address of the symbol table (`Elf64_Sym`, 24 bytes each). -/
def DT_SYMTAB : Nat := 6

/-- The value (`d_val`) of the first entry with tag `tag` among the `n` entries (`Elf64_Dyn`, 16 bytes:
`d_tag`, `d_val`) of the dynamic section at offset `off` of the bytes `rd`, before the first `DT_NULL`. -/
def dynValue (rd : Nat → Byte) (off n tag : Nat) : Option Nat :=
  let tags := (List.range n).map fun i => (leNat rd (off + 16 * i) 8, leNat rd (off + 16 * i + 8) 8)
  ((tags.takeWhile (·.1 ≠ DT_NULL)).find? (·.1 = tag)).map (·.2)

/-- The value (`st_value`) of the first symbol of the dynamic symbol table in the bytes `rd` whose name
is `name` and which is defined (`st_shndx`, offset 6, not `SHN_UNDEF` = 0): the table at `DT_SYMTAB`,
with as many entries as the hash table says (`nchain`, at `DT_HASH` + 4), each naming its string
(`st_name`, offset 0, 4 bytes) as an offset into the string table at `DT_STRTAB`, where it ends with a
NUL. `none` without a dynamic section, without one of the three tags (an image with only `DT_GNU_HASH`
has no `DT_HASH`: not covered), or without such a symbol. Symbol versions (`DT_VERSYM`) are not read: the first
symbol of the name is taken, which a C library's lookup by name and version (`LINUX_2.6`) finds too where the image
defines each name once, as Linux's vDSO images do. -/
def dynSymbol (rd : Nat → Byte) (name : List Byte) : Option Nat :=
  let h := ElfHeader.read rd
  match (readPhdrs rd h.phoff h.phnum).find? (·.type = PT_DYNAMIC) with
  | none => none
  | some d =>
    let n := d.filesz / 16
    match dynValue rd d.offset n DT_SYMTAB, dynValue rd d.offset n DT_STRTAB,
      dynValue rd d.offset n DT_HASH with
    | some sym, some str, some hash =>
      (List.range (leNat rd (hash + 4) 4)).findSome? fun i =>
        let e := sym + 24 * i
        let nm := str + leNat rd e 4
        if leNat rd (e + 6) 2 ≠ 0 ∧ (List.range (name.length + 1)).map (fun j => rd (nm + j)) = name ++ [0]
        then some (leNat rd (e + 8) 8) else none
    | _, _, _ => none

end ZellicX86
