import ZellicX86.Spec.Word
/-!
# Statement vocabulary: linked structures in memory

A library layer over the statement vocabulary (`Spec/Statement.lean`): the shapes of data structures an
invariant states, with the nodes as a list and the links or sizes as functions, which the invariant
defines by reading memory (`readAddr`, `readNat`). Each pairs a node with the next one by `zip` or compares
two lists, so that checking one on concrete data is linear in its length.

- Lists linked through their nodes: null-terminated (`Chain`), circular and doubly linked (`Ring`).
- Blocks laid end to end, each found from the one before by its size (`Tiling`): the chunks of an
  in-band allocator's heap.
-/
namespace ZellicX86

/-- `xs` is the null-terminated singly linked list from `head` whose links `next` gives (a node's link
as read from memory, by an allocator's invariant from its `Heap.View`, say): `head` is `xs`'s first
node, or `0` for the empty list; each node paired with the one after it (the last with `0`), the
first's `next` is the second; and no node is `0`. A node cannot occur twice: its links would lead
round again instead of to `0`. -/
def Chain (next : Addr → Addr) (head : Addr) (xs : List Addr) : Prop :=
  0 ∉ xs ∧ head = xs.headD 0 ∧ ∀ q ∈ xs.zip (xs.tail ++ [0]), next q.1 = q.2

/-- `xs` is the circular doubly linked list entered at `head` whose links `prev` and `next` give (the
`queue`/`dequeue` idiom of C, as musl's `struct meta` lists): empty with `head = 0`, or `head` is its
first node; each node paired with the one after it (the last with the first), the first's `next` is
the second and the second's `prev` the first; no node is `0`, and `head` occurs once. So no node occurs
twice: the links from a repeated node would return to `head` early. -/
def Ring (prev next : Addr → Addr) (head : Addr) (xs : List Addr) : Prop :=
  0 ∉ xs ∧ head = xs.headD 0 ∧ head ∉ xs.tail ∧
    ∀ q ∈ xs.zip (xs.tail ++ xs.take 1), next q.1 = q.2 ∧ prev q.2 = q.1

/-- The chunks `cs` lie end to end over the `len` bytes at `base`, each `size c` bytes long and none empty:
the first starts at `base`, every other one where the chunk before it ends, and the last ends at
`base + len`, which is at most `2 ^ 64`. Positions are numbers (`toNat`): the chunks follow each other upwards,
and none reaches past the top of the address space. Stated as one equation of lists: the chunks' starts followed by
the region's end are the region's start followed by the chunks' ends. The empty list tiles the empty region
(`len = 0`) only. Since no chunk is empty, `size`, `base` and `len` determine the chunks, and none occurs twice.

For example, with `size 0x1000 = 0x20`, `size 0x1020 = 0x30` and `size 0x1050 = 0xfb0`,
`Tiling size 0x1000 0x1000 [0x1000, 0x1020, 0x1050]` holds: both sides are `[0x1000, 0x1020, 0x1050, 0x2000]`.

A heap of an in-band allocator has this shape: each chunk carries its size in a header, and the next chunk
begins where it ends. In glibc (2.43, `malloc/malloc.c`, `struct malloc_chunk`), a chunk `p` holds
`mchunk_prev_size` at `p` and `mchunk_size` at `p + 8`, whose three low bits are flags (`PREV_INUSE`,
`IS_MMAPPED`, `NON_MAIN_ARENA`) that `chunksize (p)` clears, and the chunk after `p` is
`next_chunk (p) = p + chunksize (p)`. An invariant over the bytes `v` with
`size c = readNat v (c.add 8) 8 / 8 * 8` then says by `Tiling size base len cs` that the chunks from `base`
by `next_chunk` are `cs`, up to `base + len`: the chunks of one contiguous heap segment of an arena (the last ends at
the top chunk's end, or at the fenceposts where a segment ends; a non-main arena's heaps each start after their
`heap_info`, and `mmap`ped chunks lie in none). -/
def Tiling (size : Addr → Nat) (base : Addr) (len : Nat) (cs : List Addr) : Prop :=
  (∀ c ∈ cs, 0 < size c) ∧ base.toNat + len ≤ 2 ^ 64 ∧
    cs.map BitVec.toNat ++ [base.toNat + len] = base.toNat :: cs.map fun c => c.toNat + size c

end ZellicX86
