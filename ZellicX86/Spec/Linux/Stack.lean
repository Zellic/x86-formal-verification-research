import ZellicX86.Spec.Linux.Basic
import ZellicX86.Spec.MemoryEval
/-!
# Linux: growing a stack

What the kernel's page-fault handler does for a fault at an address no mapping covers
(`arch/x86/mm/fault.c` `do_user_addr_fault`, `mm/mmap_lock.c` `lock_mm_and_find_vma`, `mm/vma.c`
`expand_downwards` and `acct_stack_growth`): if the first VMA above the address grows down
(`VM_GROWSDOWN`, `Mapping.growsDown`: the initial stack), the kernel moves its start down to the
address's page, within the stack's limit and the guard gap, and the faulting access is made again.
There is no check against `rsp`: any address the limits allow grows the stack.

The same handler serves a fault of the process (`raiseException`) and a fault of the kernel's own
access to user memory (`growFor`). A tracer's remote reads and writes, which grow a stack with the
tracer's limits, are not modelled where they would (`EnvEvent.remoteRead`, `EnvEvent.remoteWrite`).
-/
namespace ZellicX86

/-- Whether mapping `m` allows some access (`vma_is_accessible`, `include/linux/mm.h`: `VM_READ`,
`VM_WRITE` or `VM_EXEC`): not `PROT_NONE`. -/
def Mapping.accessible (m : Mapping) : Bool := m.prot.read || m.prot.write || m.prot.exec

/-- The pages a stack in state `s` may span, by its limit: the soft `RLIMIT_STACK` in pages
(`Rlimit.cur`, read at the fault; `acct_stack_growth`). -/
def stackLimitPages (s : State) : Nat := (s.proc.signal.rlimits RLIMIT_STACK).cur.toNat / 4096

/-- The stack a fault at `a` would grow in memory `mem` with a stack limit of `lim` pages: the first mapped
page above `a`'s page and its mapping (`find_vma`: the first VMA that ends above the address; every VMA
lies below `TASK_SIZE`), if that mapping grows down and the page lies within `lim` pages above (one
farther away is refused by the limit, `growStack`). The kernel may still refuse the growth. -/
def Memory.stackAbove (feat : Features) (mem : Memory) (lim : Nat) (a : Addr) : Option (Nat × Mapping) :=
  let p := (pageOf a).toNat
  match mem.nextMapped p (min lim (taskSize feat / 4096 - 1 - p)) with
  | some (q, m) => if m.growsDown then some (q, m) else none
  | none => none

/-- The stack a fault at `a` would grow in state `s`, within the stack's limit (`stackLimitPages`). -/
def stackAbove (feat : Features) (s : State) (a : Addr) : Option (Nat × Mapping) :=
  s.proc.mm.mem.stackAbove feat (stackLimitPages s) a

/-- The kernel growing a stack for a fault at `a`, an address below `TASK_SIZE` on a page no mapping
covers, in state `s`, on the machine `prof` (its kernel's settings `prof.linux`): the state with the stack grown down to
`a`'s page, or `none` if it does not grow one (`lock_mm_and_find_vma`, `expand_downwards`,
`acct_stack_growth`). Writing `p` for `a`'s page:

- the first mapped page above `p`, `q`, belongs to a mapping that grows down (`stackAbove`; the VMA
  `find_vma` finds, the first that ends above `a`); none within as many pages as the stack's limit
  allows is as none at all, since the limit refuses it;
- the guard gap: the last mapped page below `p` within the gap (`prof.linux.stackGuardGap` pages), if
  any, belongs to a mapping that grows down or allows no access; otherwise the mapping below would end
  within the gap (`stack_guard_gap`);
- the stack's limit: the VMA after the growth, from `p` to its end, spans at most the soft
  `RLIMIT_STACK` (`stackLimitPages`). Where the VMA ends is not exact in the model: contiguous pages
  of one area (`Mapping.area`) are in one VMA, and the kernel may have merged more into it (an
  `mprotect` of a part of the stack and back again gives the part new areas, where the kernel merges
  the VMAs back). It ends at least at the end of the pages of `q`'s area and at most at the end of the
  pages that grow down with `q`'s protection, key and maximum protection (a VMA's flags are the same on
  all its pages); where the two give different answers, the kernel's is one of them (`Request.pick`);
- the refusals the model does not track (`Request.growFail`): `RLIMIT_AS`, `RLIMIT_MEMLOCK`, the
  overcommit policy, `vm.mmap_min_addr`, memory for the kernel's structures;
- `expand_downwards` also refuses a growth by more pages than the VMA's offset (`vm_pgoff`): never for
  the stacks the model has (the initial stack's offset is that of `STACK_TOP_MAX`, `mm/vma_exec.c`
  `create_init_stack_vma`, and `mremap` of a stack's pages is not modelled).

The growth maps the pages from `p` up to `q` as new zeros of `q`'s mapping (`Memory.growDown`). -/
def growStack (prof : Profile) (s : State) (a : Addr) : Req (Option State) :=
  let mem := s.proc.mm.mem
  let p := (pageOf a).toNat
  let lim := stackLimitPages s
  match stackAbove prof.feat s a with
  | none => Pure.pure none
  | some (q, m) =>
    if (mem.prevMapped p prof.linux.stackGuardGap).any fun mp => !mp.growsDown && mp.accessible then
      Pure.pure none
    else do
    -- the VMA's pages after the growth: at least `short`, at most `long`
    let short := q - p + mem.pagesWhile (·.area == m.area) q (lim + 1)
    let long := q - p + mem.pagesWhile (fun x =>
      x.growsDown && x.prot == m.prot && x.pkey == m.pkey && x.maxProt == m.maxProt) q (lim + 1)
    let fits ← if lim < short then Pure.pure false else if long ≤ lim then Pure.pure true else do
      let c ← Req.request (.pick 1)
      Pure.pure (c.val = 1)
    if !fits then Pure.pure none else do
    let refused : Bool ← Req.request .growFail
    if refused then Pure.pure none
    else Pure.pure (some (s.withMem (mem.growDown p (q - p) m)))

/-- Whether the kernel can make access `acc` to the byte at `a` with user access rights in state `s`
(`kernelRead`'s and `kernelWrite`'s check). -/
def userAccessible (feat : Features) (s : State) (acc : Access) (a : Addr) : Bool :=
  a.canonical feat.la57 && (s.proc.mm.mem.check feat s.cpu.pkru acc a).isNone

/-- Where an access through the `n` bytes from `a` in increasing order, allowed at the bytes where `ok`
holds, may make the page-fault handler grow a stack in memory `mem`: the first byte `ok` rejects, if it
lies below `TASK_SIZE` on a page no mapping covers. `none` if `ok` allows every byte, or if the first it
rejects lies elsewhere: there the access stops without a growth (`arch/x86/mm/fault.c`
`do_user_addr_fault`, `lock_mm_and_find_vma`). -/
def growthFault (feat : Features) (mem : Memory) (ok : Addr → Bool) (a : Addr) (n : Nat) : Option Addr :=
  match (firstRejected (fun i => ok (a.add i)) 0 n).map a.add with
  | some x => if (mem.map (pageOf x)).isNone && decide (x.toNat < taskSize feat) then some x else none
  | none => none

/-- The stack growths that the kernel's access `acc` to the `n` user bytes from `a` makes, with user
access rights (`copy_to_user`, `copy_from_user`, `put_user`, `get_user`, `clear_user`), in state `s`:
the state after them. The kernel's accesses go through the bytes in increasing order. The first it
cannot make (`userAccessible`) faults into the kernel's page-fault handler, which treats it as a fault
of the process (`arch/x86/mm/fault.c` `do_user_addr_fault`; the exception table is consulted only when
the fault cannot be handled): on a page no mapping covers, below `TASK_SIZE` (`growthFault`), it may grow
a stack down to it (`growStack`), and the access is made again and goes on; otherwise, or if the access
is still forbidden on the grown page (`access_error` on the grown VMA), the access stops there. The
access itself is then `kernelRead` or `kernelWrite` on the state returned. Each growth maps the page of
a byte of the range, so there are at most as many as its pages (`fuel`). -/
def growFor (prof : Profile) (s : State) (acc : Access) (a : Addr) (n : Nat) : Req State :=
  go s (n / 4096 + 2)
where
  /-- At most `fuel` more growths from state `s`. -/
  go (s : State) : Nat → Req State
    | 0 => Pure.pure s
    | fuel + 1 =>
      match growthFault prof.feat s.proc.mm.mem (userAccessible prof.feat s acc) a n with
      | none => Pure.pure s
      | some x => do
        match ← growStack prof s x with
        | some s' => go s' fuel
        | none => Pure.pure s

/-- Whether the kernel's access `acc` to the `n` user bytes from `a` in state `s` may grow a stack
(`growFor`): the first byte it cannot make lies below `TASK_SIZE` on a page no mapping covers
(`growthFault`), with a stack above it within its limit (`stackAbove`). Where the model does not follow
a growth (a kernel access computed without asking the environment, a call whose answer leaves open which
bytes the kernel touched), a case where this holds is not modelled. -/
def mayGrowFor (feat : Features) (s : State) (acc : Access) (a : Addr) (n : Nat) : Bool :=
  (growthFault feat s.proc.mm.mem (userAccessible feat s acc) a n).any fun x => (stackAbove feat s x).isSome

end ZellicX86
