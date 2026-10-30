import ZellicX86.Spec.Word
/-!
# What `memcmp` computes

The C standard's `memcmp` (C17 7.24.4.1): "The `memcmp` function compares the first `n`
characters of the object pointed to by `s1` to the first `n` characters of the object pointed to
by `s2`", and returns an integer greater than, equal to, or less than zero accordingly; "the sign
of a nonzero value returned ... is determined by the sign of the difference between the values of
the first pair of characters (both interpreted as `unsigned char`) that differ" (7.24.4). The
value itself is not specified.
-/
namespace Memcmp
open ZellicX86

/-- The order of two byte strings of the same length: that of the first pair of bytes that
differ, as unsigned numbers, or `eq` if none does. -/
def cmpBytes : List Byte → List Byte → Ordering
  | x :: xs, y :: ys => if x = y then cmpBytes xs ys else compare x.toNat y.toNat
  | _, _ => .eq

end Memcmp
