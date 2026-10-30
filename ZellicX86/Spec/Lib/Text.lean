import ZellicX86.Spec.Word
/-!
# Statement vocabulary: text a program writes

A library layer over the statement vocabulary (`Spec/Statement.lean`): how numbers look as the bytes a
program writes, for statements about its output (`Output`, `Event.IsWrite`).

- The decimal rendering of a number (`decimal`).
-/
namespace ZellicX86

/-- The decimal rendering of `n` in ASCII, as `printf("%lu", n)` writes it: its digits, most significant
first, without leading zeros, `0` for 0 (Lean core's `Nat.toDigits 10`, whose characters are the digits
`'0'` to `'9'`, bytes 48 to 57). -/
def decimal (n : Nat) : List Byte := (Nat.toDigits 10 n).map fun c => BitVec.ofNat 8 c.toNat

end ZellicX86
