import ZellicX86.Spec.Linux.Exec
/-!
# What `__tunables_init` makes of the environment (glibc 2.43, this build)

A transcription of glibc 2.43's `__tunables_init (envp)` (`elf/dl-tunables.c`, with `get_next_env`,
`parse_tunables`, `parse_tunables_string`, `tunable_initialize`, `tunable_parse_num`, `do_tunable_update_val`, and
`tunable_is_name` of `elf/dl-tunables.h`) and of `_dl_strtoul` (`elf/dl-misc.c`), as functions of the environment's
strings: `run tunables secure envp` is the tunables' list, `__libc_enable_secure` and whether a warning was printed,
after the call. Over strings of bytes: an environment string is its bytes without the terminating NUL (`ExecArgs.envp`),
and a position past its end reads the NUL (`charAt`).

`tunables` is this build's list (`dl-tunable-list.h`, generated from `dl-tunables.list` files; read from
`dl-tunables.o`'s `.data.rel.ro`): 37 tunables in the order of their ids, each with its name, type, bounds, default and
environment alias. String tunables keep where their value lies (`Val.str`: the environment string's index, the
value's offset in it and its length), which `__tunables_init` stores as a pointer into the string.

The statements of this repository use only `bytesOf` from this module (`Program/Demo.lean`'s `NoTunables`); the
rest is the transcription the proofs build on. `ArgsOk a` restricts the launches the proofs of glibc's startup
cover: the launch is not secure (`AT_SECURE` 0), no warning is printed, the environment does not ask for secure mode
(`glibc.rtld.enable_secure=1`), and every tunable it sets is one of `listed`. The transcription `run` describes all 37
tunables.
-/
namespace Glibc243Ubuntu.Tunables
open ZellicX86

/-- A string literal's bytes (UTF-8; the names here are ASCII). -/
def bytesOf (s : String) : List Byte := s.toUTF8.toList.map fun u => BitVec.ofNat 8 u.toNat

/-- The byte at position `p` of the string `s`: its terminating NUL at `s.length` (and past it). -/
def charAt (s : List Byte) (p : Nat) : Byte := s.getD p 0

theorem lt_of_charAt {s : List Byte} {p : Nat} (h : ¬charAt s p = 0) : p < s.length :=
  Nat.lt_of_not_le fun hp => h (by simp [charAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none hp])

/-- A tunable's type (`elf/dl-tunable-types.h`, `tunable_type_code_t`): `TUNABLE_TYPE_INT_32` (code 0),
`TUNABLE_TYPE_UINT_64` (1), `TUNABLE_TYPE_SIZE_T` (2), `TUNABLE_TYPE_STRING` (3). -/
inductive Ty where
  | int32 | uint64 | sizeT | string
  deriving DecidableEq, Repr

/-- A tunable's value (`tunable_val_t`): a number (`numval`, 64 bits), or a string tunable's value, where it lies in the
environment: the bytes from offset `off` of environment string `env`, `len` of them (`strval`, a pointer and a
length). -/
inductive Val where
  | num (n : BitVec 64)
  | str (env off len : Nat)
  deriving DecidableEq, Repr

/-- A tunable (`tunable_t`, `elf/dl-tunables.h`): its name, type, bounds (`type.min`, `type.max`; compared signed for
`int32`, unsigned for the others), default (`def`), environment alias (`env_alias`, empty for none), value (`val`) and
whether it was set (`initialized`). -/
structure Tunable where
  name : List Byte
  ty : Ty
  min : BitVec 64
  max : BitVec 64
  dflt : BitVec 64
  envAlias : List Byte
  val : Val
  init : Bool
  deriving DecidableEq, Repr

/-- A tunable as the build's list has it before `__tunables_init`: its value the default, not set. -/
def mk (name : String) (ty : Ty) (min max dflt : BitVec 64) (envAlias : String := "") : Tunable :=
  { name := bytesOf name, ty, min, max, dflt, envAlias := bytesOf envAlias, val := .num dflt, init := false }

/-- This build's tunables, by id (`tunable_list`, `dl-tunable-list.h`). -/
def tunables : List Tunable :=
  [mk "glibc.cpu.hwcaps" .string 0 0 0,
   mk "glibc.cpu.plt_rewrite" .int32 0 2 0,
   mk "glibc.cpu.prefer_map_32bit_exec" .int32 0 1 0 "LD_PREFER_MAP_32BIT_EXEC",
   mk "glibc.cpu.x86_data_cache_size" .sizeT 0 (-1) 0,
   mk "glibc.cpu.x86_ibt" .string 0 0 0,
   mk "glibc.cpu.x86_memset_non_temporal_threshold" .sizeT 0 (-1) 0,
   mk "glibc.cpu.x86_non_temporal_threshold" .sizeT 0 (-1) 0,
   mk "glibc.cpu.x86_rep_movsb_threshold" .sizeT 1 (-1) 0,
   mk "glibc.cpu.x86_rep_stosb_threshold" .sizeT 1 (-1) 2048,
   mk "glibc.cpu.x86_shared_cache_size" .sizeT 0 (-1) 0,
   mk "glibc.cpu.x86_shstk" .string 0 0 0,
   mk "glibc.gmon.maxarcs" .int32 50 0x7fffffff 1048576,
   mk "glibc.gmon.minarcs" .int32 50 0x7fffffff 50,
   mk "glibc.malloc.arena_max" .sizeT 1 (-1) 0 "MALLOC_ARENA_MAX",
   mk "glibc.malloc.arena_test" .sizeT 1 (-1) 0 "MALLOC_ARENA_TEST",
   mk "glibc.malloc.check" .int32 0 3 0 "MALLOC_CHECK_",
   mk "glibc.malloc.hugetlb" .sizeT 0 (-1) 0,
   mk "glibc.malloc.mmap_max" .int32 0 0x7fffffff 0 "MALLOC_MMAP_MAX_",
   mk "glibc.malloc.mmap_threshold" .sizeT 0 (-1) 0 "MALLOC_MMAP_THRESHOLD_",
   mk "glibc.malloc.mxfast" .sizeT 0 (-1) 0,
   mk "glibc.malloc.perturb" .int32 0 0xff 0 "MALLOC_PERTURB_",
   mk "glibc.malloc.tcache_count" .sizeT 0 (-1) 0,
   mk "glibc.malloc.tcache_max" .sizeT 0 (-1) 0,
   mk "glibc.malloc.tcache_unsorted_limit" .sizeT 0 (-1) 0,
   mk "glibc.malloc.top_pad" .sizeT 0 (-1) 131072 "MALLOC_TOP_PAD_",
   mk "glibc.malloc.trim_threshold" .sizeT 0 (-1) 0 "MALLOC_TRIM_THRESHOLD_",
   mk "glibc.mem.decorate_maps" .int32 0 1 0,
   mk "glibc.mem.tagging" .int32 0 0xff 0,
   mk "glibc.pthread.mutex_spin_count" .int32 0 0x7fff 100,
   mk "glibc.pthread.rseq" .int32 0 1 1,
   mk "glibc.pthread.stack_cache_size" .sizeT 0 (-1) 41943040,
   mk "glibc.pthread.stack_hugetlb" .int32 0 1 1,
   mk "glibc.rtld.dynamic_sort" .int32 1 2 2,
   mk "glibc.rtld.enable_secure" .int32 0 1 0,
   mk "glibc.rtld.execstack" .int32 0 2 1,
   mk "glibc.rtld.nns" .sizeT 1 16 4,
   mk "glibc.rtld.optional_static_tls" .sizeT 0 (-1) 512]

/-- A tunable's type code (`tunable_type_code_t`). -/
def Ty.code : Ty → Nat
  | .int32 => 0 | .uint64 => 1 | .sizeT => 2 | .string => 3

/-- `bs` padded with NULs to `n` bytes (a `char[n]` holding a string shorter than `n`). -/
def padTo (n : Nat) (bs : List Byte) : List Byte := bs ++ List.replicate (n - bs.length) 0

/-- A value's 16 bytes (`tunable_val_t`): a number's word, then 8 zero bytes; a string's address and length, the
environment string `k` at `envAt k`. -/
def Val.bytes (envAt : Nat → Addr) : Val → List Byte
  | .num n => toBytesLE n 8 ++ List.replicate 8 0
  | .str k off len => toBytesLE (envAt k + BitVec.ofNat 64 off) 8 ++ toBytesLE (BitVec.ofNat 64 len) 8

/-- A tunable's `0x88` bytes as this build lays out `tunable_t` (`elf/dl-tunables.h`, x86-64): `name[48]`, `type`
(`type_code` 4 bytes and 4 of padding, `min`, `max`), `def`, `val`, `initialized`, `env_alias[31]`. -/
def Tunable.bytes (envAt : Nat → Addr) (t : Tunable) : List Byte :=
  padTo 48 t.name ++ toBytesLE (BitVec.ofNat 32 t.ty.code) 4 ++ List.replicate 4 0 ++ toBytesLE t.min 8 ++
    toBytesLE t.max 8 ++ (Val.num t.dflt).bytes envAt ++ t.val.bytes envAt ++ [if t.init then 1 else 0] ++
    padTo 31 t.envAlias

/-- The ids of the tunables with an environment alias, in the order `__tunables_init` tries them
(`tunable_env_alias_list`, `dl-tunable-list.h`). -/
def aliasIds : List Nat := [2, 13, 14, 15, 17, 18, 20, 24, 25]

/-- The id of `glibc.rtld.enable_secure`. -/
def enableSecureId : Nat := 33

/-- `f` with the value at `i` replaced by `x`. -/
def upd {α : Type} (f : Nat → α) (i : Nat) (x : α) : Nat → α := fun j => if j = i then x else f j

/-! ## `_dl_strtoul` -/

/-- Whether `c` is a digit of `base` (8, 10 or 16): `'0'` to `'7'`, `'0'` to `'9'`, or those and `'a'`–`'f'`,
`'A'`–`'F'`; its value. -/
def digit (base : Nat) (c : Byte) : Option Nat :=
  let n := c.toNat
  if 0x30 ≤ n ∧ n ≤ 0x30 + (if base = 8 then 7 else 9) then some (n - 0x30)
  else if base = 16 ∧ 0x61 ≤ n ∧ n ≤ 0x66 then some (n - 0x61 + 10)
  else if base = 16 ∧ 0x41 ≤ n ∧ n ≤ 0x46 then some (n - 0x41 + 10)
  else none

/-- Where `_dl_strtoul`'s loop over the digits ends: after the last digit, with the value read (`ok`), or at a digit that
would take the value past `2 ^ 64 - 1` (`overflow`). -/
inductive Digits where
  | ok (r p : Nat)
  | overflow (p : Nat)

/-- `_dl_strtoul`'s loop over the digits of `base` from position `p` of `s`, with the value `r` so far. A digit
overflows where `result > cutoff || (result == cutoff && digval > cutlim)`, `cutoff` and `cutlim` the quotient and
remainder of `2 ^ 64 - 1` by `base`. -/
def digits (s : List Byte) (base : Nat) (p r : Nat) : Digits :=
  match hd : digit base (charAt s p) with
  | none => .ok r p
  | some d =>
    if r > (2 ^ 64 - 1) / base ∨ (r = (2 ^ 64 - 1) / base ∧ d > (2 ^ 64 - 1) % base) then .overflow p
    else digits s base (p + 1) (r * base + d)
termination_by s.length + 1 - p
decreasing_by
  have : p < s.length := lt_of_charAt fun h0 => by simp [h0, digit] at hd
  omega

/-- The blanks `_dl_strtoul` skips from position `p` of `s` (`' '`, `'\t'`): the position of the first other byte. -/
def skipBlanks (s : List Byte) (p : Nat) : Nat :=
  if charAt s p = 0x20 ∨ charAt s p = 0x09 then skipBlanks s (p + 1) else p
termination_by s.length + 1 - p
decreasing_by
  have : p < s.length := lt_of_charAt fun h0 => by simp [h0] at *
  omega

/-- What `_dl_strtoul` returns where its loop over the digits ends as `d` says, for a number of the sign `pos`: the
value read (negated modulo `2 ^ 64` for a negative number) or, past `2 ^ 64 - 1`, `2 ^ 64 - 1` whatever the sign; and
the position `endptr` points to. -/
def finish (pos : Bool) : Digits → BitVec 64 × Nat
  | .ok r q => (if pos then BitVec.ofNat 64 r else -BitVec.ofNat 64 r, q)
  | .overflow q => (-1, q)

/-- `_dl_strtoul`'s number at position `p` of `s`, where a digit stands (after the blanks and the sign `pos`): a leading
`0` makes it octal, `0x` or `0X` hexadecimal (the position after it, whatever follows), else decimal. -/
def number (s : List Byte) (pos : Bool) (p : Nat) : BitVec 64 × Nat :=
  let (base, p) :=
    if charAt s p = 0x30 then (if charAt s (p + 1) = 0x78 ∨ charAt s (p + 1) = 0x58 then (16, p + 2) else (8, p)) else (10, p)
  finish pos (digits s base p 0)

/-- `_dl_strtoul (s + p, &endptr)` (`elf/dl-misc.c`): the value and the position `endptr` points to. Blanks skipped, an
optional sign; no digit: 0 at the position after the sign; else the `number` there. A negative number's value is
negated modulo `2 ^ 64`; one that does not fit gives `2 ^ 64 - 1` whatever its sign. -/
def strtoul (s : List Byte) (p : Nat) : BitVec 64 × Nat :=
  let p := skipBlanks s p
  let (pos, p) := if charAt s p = 0x2d then (false, p + 1) else if charAt s p = 0x2b then (true, p + 1) else (true, p)
  if (digit 10 (charAt s p)).isNone then (0, p) else number s pos p

/-! ## The parse -/

/-- `tunable_is_name (orig, envname)`, `envname` the string `s` from position `p`: `s` there begins with `orig`
followed by `'='`. -/
def isName (orig s : List Byte) (p : Nat) : Bool := (orig ++ [0x3d]).isPrefixOf (s.drop p)

/-- The end of a name or a value in `GLIBC_TUNABLES`' string `s` from position `p`: the first `'='`, `':'` or the
end. -/
def scan (s : List Byte) (p : Nat) : Nat :=
  if charAt s p = 0x3d ∨ charAt s p = 0x3a ∨ charAt s p = 0 then p else scan s (p + 1)
termination_by s.length + 1 - p
decreasing_by
  have : p < s.length := lt_of_charAt fun h0 => by simp [h0] at *
  omega

theorem le_scan (s : List Byte) (p : Nat) : p ≤ scan s p := by
  induction p using scan.induct s with
  | case1 p h => rw [scan]; simp only [h, ↓reduceIte]; exact Nat.le_refl p
  | case2 p h ih => rw [scan]; simp only [h, ↓reduceIte]; omega

/-- What `parse_tunables_string` finds for each tunable: the value's offset in the string and its length. -/
abbrev Found := Nat → Option (Nat × Nat)

/-- The first tunable of `tbl` whose name `tunable_is_name` finds at position `p` of `s`. -/
def nameAt (tbl : List Tunable) (s : List Byte) (p : Nat) : Option Nat :=
  tbl.findIdx? fun t => isName t.name s p

/-- `parse_tunables_string`'s loop from a name's position `p` in `GLIBC_TUNABLES`' value `s` (`name = p`), with what it
has found so far: what it finds, `none` for an ill-formatted string (a name or a value that runs to the end without
`=`, or a value that ends at `'='`). A name ending at `':'` is skipped; a pair whose name is no tunable's is ignored; a
later pair for the same tunable overrides an earlier one. -/
def pairs (tbl : List Tunable) (s : List Byte) (p : Nat) (f : Found) : Option Found :=
  let q := scan s p
  if charAt s q = 0 then none
  else if charAt s q = 0x3a then pairs tbl s (q + 1) f
  else
    let v := q + 1
    let r := scan s v
    if charAt s r = 0x3d then none
    else
      let f := match nameAt tbl s p with
        | some i => upd f i (some (v, r - v))
        | none => f
      if charAt s r = 0 then some f else pairs tbl s r f
termination_by s.length + 1 - p
decreasing_by
  · have := le_scan s p
    have := lt_of_charAt (s := s) (p := scan s p) (by assumption)
    omega
  · have := le_scan s p
    have := le_scan s (scan s p + 1)
    have := lt_of_charAt (s := s) (p := scan s (scan s p + 1)) (by assumption)
    omega

/-- `parse_tunables_string (s + v, tunables)`: nothing for an empty string, else `pairs` from `v`. -/
def parseString (tbl : List Tunable) (s : List Byte) (v : Nat) : Option Found :=
  if charAt s v = 0 then some (fun _ => none) else pairs tbl s v (fun _ => none)

/-! ## Setting a tunable -/

/-- `do_tunable_update_val (cur, &val, NULL, NULL)`: a string tunable takes the value; a numeric one takes it (an
`int32` one the low 32 bits sign-extended) where it lies within the tunable's bounds (signed for `int32`, unsigned
for the others), else nothing changes. Setting marks it `initialized`. -/
def update (t : Tunable) (v : Val) : Tunable :=
  match t.ty, v with
  | .string, _ => { t with val := v, init := true }
  | _, .str .. => t
  | ty, .num n =>
    let x := if ty = .int32 then (n.setWidth 32).signExtend 64 else n
    let ok := if ty = .int32 then t.min.sle x && x.sle t.max else t.min ≤ x && x ≤ t.max
    if ok then { t with val := .num x, init := true } else t

/-- `tunable_initialize (cur, s + off, len)`, the value in environment string `k` (`s`): a string tunable takes it; a
numeric one the number `_dl_strtoul` reads where it reads exactly the `len` bytes (`tunable_parse_num`), else
`none`, which glibc reports with a warning. -/
def initTunable (t : Tunable) (k : Nat) (s : List Byte) (off len : Nat) : Option Tunable :=
  if t.ty = .string then some (update t (.str k off len))
  else
    let (n, e) := strtoul s off
    if e = off + len then some (update t (.num n)) else none

/-! ## `__tunables_init` -/

/-- What `__tunables_init` keeps while it walks the environment: the tunables, the values the aliases found
(`tunables_env_alias`: the environment string's index, the value's offset and length, for each of `aliasIds`),
`__libc_enable_secure`, and whether it printed a warning. -/
structure St where
  tbl : List Tunable
  envAlias : Nat → Option (Nat × Nat × Nat)
  secure : Bool
  warned : Bool

/-- Tunable `i` set as `initTunable` does, or the warning. -/
def setFrom (st : St) (i k : Nat) (s : List Byte) (off len : Nat) : St :=
  match st.tbl[i]? with
  | none => st
  | some t => match initTunable t k s off len with
    | some t => { st with tbl := st.tbl.set i t }
    | none => { st with warned := true }

/-- `parse_tunables (s + v)`, `GLIBC_TUNABLES`' value at position `v` of environment string `k`: an ill-formatted
string is ignored with a warning. Where `glibc.rtld.enable_secure` is found and its value a number (else a warning)
equal to 1, `__libc_enable_secure` becomes 1 and nothing else changes. Otherwise each tunable found is set in the
order of the ids. -/
def parseTunables (st : St) (k : Nat) (s : List Byte) (v : Nat) : St :=
  match parseString st.tbl s v with
  | none => { st with warned := true }
  | some f =>
    let (st, stop) := match f enableSecureId with
      | none => (st, false)
      | some (off, len) =>
        let (n, e) := strtoul s off
        if e ≠ off + len then ({ st with warned := true }, false)
        else if n = 1 then ({ st with secure := true }, true)
        else (st, false)
    if stop then st
    else
      (List.range st.tbl.length).foldl
        (fun st i => match f i with
          | some (off, len) => setFrom st i k s off len
          | none => st)
        st

/-- The position of the first `'='` in `s`. -/
def eqPos (s : List Byte) : Option Nat := s.findIdx? (· = 0x3d)

/-- The first alias (its index in `aliasIds`) that `tunable_is_name` finds at the start of `s`; empty aliases are
skipped. -/
def aliasAt (tbl : List Tunable) (s : List Byte) : Option Nat :=
  aliasIds.findIdx? fun id => match tbl[id]? with
    | some t => !t.envAlias.isEmpty && isName t.envAlias s 0
    | none => false

/-- One round of `__tunables_init`'s loop, for environment string `k`, `s` (`get_next_env`): a string without `'='` is
skipped; `GLIBC_TUNABLES=…` is parsed at once; a string that begins with an alias and `'='` records its value (the
rest of the string after the first `'='`) for the alias, a later one overriding an earlier one. -/
def envStep (st : St) (k : Nat) (s : List Byte) : St :=
  match eqPos s with
  | none => st
  | some q =>
    if isName (bytesOf "GLIBC_TUNABLES") s 0 then parseTunables st k s (q + 1)
    else match aliasAt st.tbl s with
      | some i => { st with envAlias := upd st.envAlias i (some (k, q + 1, s.length - (q + 1))) }
      | none => st

/-- The aliases' values set after the loop, in `aliasIds`' order, each only where the tunable is not yet set
(`initialized`: by `GLIBC_TUNABLES`); a value that is no number for a numeric tunable is reported with a warning. -/
def aliasInit (envp : List (List Byte)) (st : St) : St :=
  (List.range aliasIds.length).foldl
    (fun st i => match st.envAlias i, aliasIds[i]? with
      | some (k, off, len), some id =>
        match st.tbl[id]? with
        | some t => if t.init then st else setFrom st id k (envp.getD k []) off len
        | none => st
      | _, _ => st)
    st

/-- The outcome of `__tunables_init`: the tunables, `__libc_enable_secure`, whether a warning was printed. -/
structure Outcome where
  tbl : List Tunable
  secure : Bool
  warned : Bool
  deriving Repr

/-- `__tunables_init (envp)` with the tunables `tbl` and `__libc_enable_secure` `secure` (nonzero: nothing is done):
the loop over the environment's strings (`envStep`), then, unless `glibc.rtld.enable_secure` asked for secure mode,
the aliases' values (`aliasInit`). -/
def run (tbl : List Tunable) (secure : Bool) (envp : List (List Byte)) : Outcome :=
  if secure then ⟨tbl, true, false⟩
  else
    let st := (envp.zipIdx).foldl (fun st (s, k) => envStep st k s)
      { tbl, envAlias := fun _ => none, secure := false, warned := false }
    let st := if st.secure then st else aliasInit envp st
    ⟨st.tbl, st.secure, st.warned⟩

/-- A string without NUL bytes (`ExecArgs.Valid`'s strings). -/
def NulFree (s : List Byte) : Prop := ∀ b ∈ s, b ≠ 0

/-! ## The restriction on the environment that the startup's proofs assume -/

/-- The tunables an environment may set under `ArgsOk`: `glibc.pthread.mutex_spin_count`, `glibc.pthread.rseq`,
`glibc.pthread.stack_cache_size`, `glibc.pthread.stack_hugetlb`, `glibc.rtld.nns`, `glibc.rtld.optional_static_tls`. -/
def listed : List Nat := [28, 29, 30, 31, 35, 36]

/-- The restriction on launch arguments that the proofs of glibc's startup assume: `AT_SECURE` is 0, and
`__tunables_init` on the environment prints no warning, does not enter secure mode, and sets no tunable but those
`listed`. This excludes launches with other tunables or a warning; it does not restrict the environment parser `run`
itself. -/
def ArgsOk (a : ExecArgs) : Prop :=
  a.secure = false ∧
  let o := run tunables false a.envp
  o.warned = false ∧ o.secure = false ∧ ∀ i t, o.tbl[i]? = some t → t.init = true → i ∈ listed

end Glibc243Ubuntu.Tunables
