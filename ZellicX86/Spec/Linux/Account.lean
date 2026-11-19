import ZellicX86.Spec.Linux.Basic
import ZellicX86.Spec.MemoryEval
/-!
# The address space's accounting and its limits

What `may_expand_vm` (`mm/mmap.c`) compares with `RLIMIT_AS` and `RLIMIT_DATA`: the pages of the process's VMAs
(`mm->total_vm`) and of its data mappings (`mm->data_vm`), counted over the page map rather than kept as state (the
kernel's counters follow every change of a VMA, `vm_stat_account`; the mm test compares them with `VmSize` and
`VmData`), and the check itself (`mayExpand`). Here, after `Spec/MemoryEval.lean`, so that evaluation counts over the
memory's cover (`Memory.nextMapped`).
-/
namespace ZellicX86

/-- The next mapped page among the `n` after page `p` lies among them. -/
theorem Memory.nextMapped_range (mem : Memory) :
    ∀ {p n q : Nat} {m : Mapping}, mem.nextMapped p n = some (q, m) → p < q ∧ q ≤ p + n
  | _, 0, _, _, h => by simp [Memory.nextMapped] at h
  | p, n + 1, q, m, h => by
    unfold Memory.nextMapped at h
    split at h
    · cases h; omega
    · have := mem.nextMapped_range h; omega

/-- The number of the pages among the `n` after page `p` that are mapped by a mapping satisfying `P` (of the
page number and the mapping), counted from one mapped page to the next (`Memory.nextMapped`). -/
def Memory.countMapped (mem : Memory) (P : Nat → Mapping → Bool) (p n : Nat) : Nat :=
  match h : mem.nextMapped p n with
  | none => 0
  | some (q, m) => (if P q m then 1 else 0) + mem.countMapped P q (p + n - q)
termination_by n
decreasing_by have := mem.nextMapped_range h; omega

/-- The number of the mapped pages whose mapping satisfies `P`, among all `2 ^ 52`. -/
def Memory.pagesWhere (mem : Memory) (P : Nat → Mapping → Bool) : Nat :=
  (match mem.mapAt 0 with
    | some m => if P 0 m then 1 else 0
    | none => 0) + mem.countMapped P 0 (2 ^ 52 - 1)

/-- The pages of the process's VMAs (`mm->total_vm`, `vm_stat_account` in `mm/mmap.c`): every mapped page but the
vsyscall gate's, which is no VMA; the vDSO's pages are VMAs. -/
def Memory.totalVm (mem : Memory) : Nat :=
  mem.pagesWhere fun p m => !(m.special && p == vsyscallPage.toNat)

/-- Whether a backing is a shared mapping's (`.file`: `MAP_SHARED`, shared anonymous memory too). -/
def Backing.isFile : Backing → Bool
  | .file _ => true
  | _ => false

/-- The pages of data mappings (`mm->data_vm`; `is_data_mapping`, `mm/vma.h`): writable, not shared (no `.file`
backing: a shared mapping of a file opened read-only, which the kernel makes private, cannot be made writable) and
not a stack (`VM_STACK`, `VM_GROWSDOWN` on x86-64). -/
def Memory.dataVm (mem : Memory) : Nat :=
  mem.pagesWhere fun _ m => m.prot.write && !m.growsDown && !(mem.backings m.backing).isFile

/-- The number of mapped pages among the `n` from page `first`. -/
def Memory.mappedIn (mem : Memory) (first n : Nat) : Nat :=
  if first = 0 then
    (if n = 0 then 0 else if (mem.mapAt 0).isSome then 1 else 0) + mem.countMapped (fun _ _ => true) 0 (n - 1)
  else mem.countMapped (fun _ _ => true) (first - 1) n

/-! ## The check -/

/-- A resource limit's soft value in pages, as `may_expand_vm` compares with it (`rlimit(r) >> PAGE_SHIFT`). -/
def Rlimit.pages (r : Rlimit) : Nat := r.cur.toNat / 4096

/-- Whether `may_expand_vm` (`mm/mmap.c`) lets an area of `n` pages be added to `total` pages of mappings and, for a
private writable area (`data`, `is_data_mapping`: `VM_WRITE` without `VM_SHARED` or `VM_STACK`), to `dataVm` pages of
such areas, under the limits `as` (`RLIMIT_AS`) and `dat` (`RLIMIT_DATA`): the first not above `as`, the second
not above `dat` unless `dat` is 0 and the area fits the hard limit (a workaround the kernel keeps for Valgrind) or
the kernel ignores `RLIMIT_DATA` (`ignoreData`: `ignore_rlimit_data`, `Request.dataLimitIgnored`). -/
def mayExpand (as dat : Rlimit) (ignoreData : Bool) (total dataVm n : Nat) (data : Bool) : Bool :=
  total + n ≤ as.pages &&
    (!data || dataVm + n ≤ dat.pages || (dat.cur = 0 && dataVm + n ≤ dat.max.toNat / 4096) || ignoreData)

end ZellicX86
