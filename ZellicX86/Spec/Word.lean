/-!
# Bytes, words and addresses

Fixed-width values are Lean's `BitVec`. Memory is byte-addressed and little-endian: the
byte at the lowest address is the least significant (Intel SDM Vol. 1, 1.3.1 "Bit and Byte
Order"; AMD APM Vol. 1, 2.2.1 "Byte Ordering").
-/
namespace ZellicX86

/-- A byte. -/
abbrev Byte := BitVec 8

/-- A 64-bit linear (virtual) address. Segmentation adds only the `FS`/`GS` bases in 64-bit
mode (SDM Vol. 1, 3.4.2.1 "Segment Registers in 64-Bit Mode"). -/
abbrev Addr := BitVec 64

/-- The `n` bytes of `v`, least significant first. Bits of `v` above `8 * n` are dropped;
missing bits read as zero. -/
def toBytesLE {w : Nat} (v : BitVec w) (n : Nat) : List Byte :=
  (List.range n).map fun i => (v >>> (8 * i)).setWidth 8

/-- The value of little-endian bytes `bs` as a `w`-bit word (bits beyond `w` dropped). -/
def ofBytesLE (w : Nat) : List Byte → BitVec w
  | [] => 0
  | b :: bs => b.setWidth w ||| (ofBytesLE w bs <<< 8)

/-- The address `a + i`, wrapping modulo `2 ^ 64` like the processor's address arithmetic. -/
def Addr.add (a : Addr) (i : Nat) : Addr := a + BitVec.ofNat 64 i

/-- Whether `a` is canonical: bits 63 down to `n - 1` are all equal, where `n` is the linear
address width, 48 with 4-level and 57 with 5-level paging (SDM Vol. 1, 3.3.7.1;
Vol. 3A, 5.1.1). -/
def Addr.canonical (la57 : Bool) (a : Addr) : Bool :=
  let n := if la57 then 57 else 48
  let top := a >>> (n - 1)
  top == 0 || top == BitVec.ofNat 64 (2 ^ (65 - n) - 1)

end ZellicX86
