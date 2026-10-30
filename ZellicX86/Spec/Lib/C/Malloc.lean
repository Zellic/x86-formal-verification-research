import ZellicX86.Spec.Lib.C.Runtime
/-!
# Statement vocabulary: the C library's `malloc` and `free`

A library layer over the statement vocabulary (`Spec/Statement.lean`): what the C library's `malloc` and
`free` promise, as the core contracts of an allocator (`Heap.malloc`, `Heap.free`, which hold for any
allocator) strengthened by what C and POSIX add. A program whose statement assumes these contracts at its
calls holds for every C library that keeps them (musl 1.2.5's keeps `free`'s clause, `mallocng/free.c`; glibc 2.43's
`free` does not always: below).

- A C library's allocator is a part of its runtime (`Spec/Lib/C/Runtime.lean`): at the runtime's ghost `g`, the
  allocator `Runtime.heap L g`, which owns what the library owns (`g.own`), with the program's blocks `g.live` live, whose
  invariant is the library's, and whose only bytes it changes without owning them are the C library's `errno`
  (`Spec/Lib/C/Errno.lean`).
- `malloc(n)` (`C.malloc`): `Heap.malloc`, and
  - on failure (a null result for a request of at least 1 byte) `errno` set to `ENOMEM` (POSIX.1-2024,
    `malloc`: "Otherwise, it shall return a null pointer and set `errno` to indicate the error", the error
    `ENOMEM`); for `malloc(0)` POSIX allows a null result with an implementation-defined `errno`, so a null
    result of `malloc(0)` says nothing of it (glibc sets `ENOMEM` there too: a property of glibc, not
    of every C library); on success `errno` any value (C17 7.5 allows that; glibc 2.43 sets it when `sbrk` fails and
    the `mmap` fallback succeeds, `misc/sbrk.c`, `sysdeps/unix/sysv/linux/brk.c`);
  - the new block, also for `n = 0`, an object apart from every live block: C17 7.22.3 makes the result
    of `malloc(0)` either null or "as if the size were some nonzero value", and the pointers of two
    allocations that are both live distinct (`object`: a block counted as at least 1 byte). The core
    contract does not promise this: a block of 0 bytes lies apart from everything.
- `free(p)` (`C.free`): `Heap.free`, and `errno` kept (POSIX.1-2024, `free`: "The `free()` function shall
  not modify `errno` if `ptr` is a null pointer or a pointer previously returned by" the allocation
  functions). glibc 2.43 does not keep this in every case: it saves and restores `errno` around
  `_int_free_chunk` (`malloc/malloc.c`), but the first `free` of a thread whose cache is not yet created goes through
  `tcache_init`, which may set `ENOMEM` when the heap cannot grow (`tcache_init`, `malloc/malloc.c`). So glibc 2.43
  keeps `C.free` only where the calling thread's cache was set up before the call.
- Code that keeps them (`C.MallocAt`, `C.FreeAt`, `C.ImplementedBy`).

Not covered: `calloc`, `realloc`, `posix_memalign`, `aligned_alloc`, `malloc_usable_size`, and
`__errno_location`'s contract.
-/
namespace ZellicX86.C

/-- The bytes of a block as a C object: the block, counted as at least 1 byte (C17 7.22.3: the result of
`malloc(0)`, if not null, is "as if the size were some nonzero value"). -/
def object (r : Rgn) : Rgn := ⟨r.base, max r.len 1⟩

/-- The C library `L`'s `malloc(n)` at the ghost `g` (what the library owns, the program's blocks `g.live`), on a
processor with features `feat` (C17 7.22.3.4, POSIX.1-2024 `malloc`; `n` in `rdi`, the result in `rax`), as a contract:
the core allocator's `Heap.malloc` of the runtime's allocator (`Runtime.heap`), and at the return
- for a null result of a request of at least 1 byte, `errno` set to `ENOMEM`;
- for a block, the block as an object (`object`, at least 1 byte) apart from every live block as an object:
  even a block of 0 bytes is distinct from every other live block.
At the return the library's ghost is `g` with what it owns then and the new block among the program's (`Heap.malloc`'s
post: the invariant for both). -/
def malloc (L : Runtime) (feat : Features) (g : Ghost) : Contract :=
  { (L.heap g).malloc feat g.own g.live with
    post := fun s X => ((L.heap g).malloc feat g.own g.live).post s X ∧
      (X.cpu.gpr.rax = 0 → s.cpu.gpr.rdi ≠ 0 → Errno.set L.errnoOff ENOMEM X) ∧
      (X.cpu.gpr.rax ≠ 0 → Apart [object ⟨X.cpu.gpr.rax, s.cpu.gpr.rdi.toNat⟩] (g.live.map object)) }

/-- The C library `L`'s `free(p)` at the ghost `g` (what the library owns, its streams; the program's blocks are
`front ++ b :: back`, given here, and `g.live` is not read), for the program's block `some b` (`p = b.base`), or of a null pointer (`b = none`), on a
processor with features `feat` (C17 7.22.3.3, POSIX.1-2024 `free`), as a contract: the core allocator's `Heap.free` of
the runtime's allocator (`Runtime.heap`) for those blocks, and `errno` at the return as at the call (`Errno.keeps`). -/
def free (L : Runtime) (feat : Features) (g : Ghost) (front : List Rgn) (b : Option Rgn) (back : List Rgn) :
    Contract :=
  { (L.heap g).free feat g.own front b back with
    post := fun s X => ((L.heap g).free feat g.own front b back).post s X ∧ Errno.keeps L.errnoOff s X }

/-- The code segments `code` implement, at `entry` on processor `prof`, the C library `L`'s `malloc`: its contract
`C.malloc` at every ghost. -/
def MallocAt (L : Runtime) (prof : Profile) (entry : Addr) (code : List (Addr × List Byte)) : Prop :=
  ∀ g, ImplementsCall prof entry code (malloc L prof.feat g)

/-- The code segments `code` implement, at `entry` on processor `prof`, the C library `L`'s `free`: its contract
`C.free` at every ghost, for every block and a null pointer, and every set of other blocks. -/
def FreeAt (L : Runtime) (prof : Profile) (entry : Addr) (code : List (Addr × List Byte)) : Prop :=
  ∀ g front b back, ImplementsCall prof entry code (free L prof.feat g front b back)

/-- The code segments `code` implement the C library `L`'s `malloc` (at `mallocE`) and `free` (at `freeE`) on processor
`prof` (`MallocAt`, `FreeAt`). -/
def ImplementedBy (L : Runtime) (prof : Profile) (code : List (Addr × List Byte)) (mallocE freeE : Addr) : Prop :=
  MallocAt L prof mallocE code ∧ FreeAt L prof freeE code

end ZellicX86.C
