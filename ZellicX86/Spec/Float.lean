/-!
# Binary floating point: formats, values, rounding

The arithmetic of the SSE, AVX and x87 floating-point instructions as the manuals define it: the
infinitely precise result of the operation, rounded once to the destination format (IEEE 754;
SDM Vol. 1, 4.8.4 "Rounding"; AMD APM Vol. 1, 4.4.4 "Floating-Point Rounding"). Nothing here is
specific to one instruction set: a format is a precision and an exponent range, the rounding
control is an argument, and the exception conditions are reported as flags for the caller to
mask, record or raise (`Spec/Semantics/SseFloat.lean` for SSE and AVX, `Spec/Semantics/X87.lean` for
the x87 unit).

The definitions compute with natural numbers and integers only: an exact result is a rational
number (or the square root of one) given by integers (`Exact`), and rounding compares it with
multiples of a power of two. No floating-point type of Lean's is used.
-/
namespace ZellicX86

/-! ## Formats and values -/

/-- A binary interchange format (SDM Vol. 1, 4.2.2 "Floating-Point Data Types", Table 4-3; APM
Vol. 1, 4.4.3 "Floating-Point Number Representation", Table 4-3): a sign bit, `ebits` bits of
biased exponent and `prec - 1` bits of fraction; the significand has `prec` bits with the
integer bit implicit. Also used, with `ebits = 15`, as the rounding target of the x87 unit's double
extended exponent range (`extRound`). -/
structure FFormat where
  ebits : Nat
  prec : Nat

/-- Single precision (binary32). -/
def binary32 : FFormat := ⟨8, 24⟩
/-- Double precision (binary64). -/
def binary64 : FFormat := ⟨11, 53⟩

/-- The number of fraction bits. -/
def FFormat.fbits (f : FFormat) : Nat := f.prec - 1
/-- The width of an encoding in bits. -/
def FFormat.width (f : FFormat) : Nat := 1 + f.ebits + f.fbits
/-- The exponent bias, `2 ^ (ebits - 1) - 1` (127, 1023). -/
def FFormat.bias (f : FFormat) : Nat := 2 ^ (f.ebits - 1) - 1
/-- The largest exponent of a finite value (127, 1023). -/
def FFormat.emax (f : FFormat) : Int := f.bias
/-- The exponent of the smallest normal value (−126, −1022). -/
def FFormat.emin (f : FFormat) : Int := 1 - (f.bias : Int)

/-- A floating-point datum by class (SDM Vol. 1, 4.8.3 "Real Number and Non-number Encodings",
Table 4-3; APM Vol. 1, 4.4.3, Table 4-6):
- `zero neg`: `+0` or `−0`;
- `finite neg m e`: the number `(−1)^neg · m · 2^e` with `m > 0` (normal or denormal: the class is
  the encoding's business, `FFormat.decode`);
- `inf neg`: `+∞` or `−∞`;
- `nan neg quiet payload`: a NaN, quiet (`QNaN`) if the fraction's most significant bit is set,
  else signaling (`SNaN`), with the fraction's other bits as `payload`. -/
inductive FNum
  | zero (neg : Bool)
  | finite (neg : Bool) (m : Nat) (e : Int)
  | inf (neg : Bool)
  | nan (neg : Bool) (quiet : Bool) (payload : Nat)
  deriving DecidableEq, Repr

/-- Whether `x` is a NaN. -/
def FNum.isNaN : FNum → Bool
  | .nan .. => true
  | _ => false

/-- Whether `x` is a signaling NaN. -/
def FNum.isSNaN : FNum → Bool
  | .nan _ q _ => !q
  | _ => false

/-- The sign bit of `x`. -/
def FNum.neg : FNum → Bool
  | .zero n | .finite n .. | .inf n | .nan n .. => n

/-- `x` with its sign changed. -/
def FNum.negate : FNum → FNum
  | .zero n => .zero !n
  | .finite n m e => .finite (!n) m e
  | .inf n => .inf !n
  | .nan n q p => .nan (!n) q p

/-- A NaN made quiet: a signaling NaN becomes a quiet one by setting the fraction's most
significant bit (SDM Vol. 1, 4.8.3.5; APM Vol. 1, Table 4-5, footnote 2); other data are unchanged. -/
def FNum.quiet : FNum → FNum
  | .nan n _ p => .nan n true p
  | x => x

/-- The QNaN floating-point indefinite: negative, quiet, payload 0 (SDM Vol. 1, 4.8.3.7, Table 4-3;
APM Vol. 1, Table 4-7: `FFC00000H`, `FFF8000000000000H`). -/
def FNum.indefinite : FNum := .nan true true 0

/-- The datum a bit pattern `x` (below `2 ^ f.width`) of format `f` encodes: a biased exponent of
0 is a zero or a denormal with exponent `emin`, the all-ones exponent an infinity or a NaN, any
other exponent a normal number with the integer bit 1 (SDM Vol. 1, 4.8.2, 4.8.3, Table 4-3; APM
Vol. 1, 4.4.3, Table 4-6). -/
def FFormat.decode (f : FFormat) (x : Nat) : FNum :=
  let neg := x / 2 ^ (f.width - 1) % 2 = 1
  let ex := x / 2 ^ f.fbits % 2 ^ f.ebits
  let fr := x % 2 ^ f.fbits
  if ex = 0 then
    if fr = 0 then .zero neg else .finite neg fr (f.emin - f.fbits)
  else if ex = 2 ^ f.ebits - 1 then
    if fr = 0 then .inf neg
    else .nan neg (fr / 2 ^ (f.fbits - 1) = 1) (fr % 2 ^ (f.fbits - 1))
  else .finite neg (2 ^ f.fbits + fr) (ex - f.bias - f.fbits)

/-- Whether the bit pattern `x` of format `f` is a denormal: biased exponent 0, fraction not 0 (SDM
Vol. 1, 4.8.3.2; APM Vol. 1, 4.4.3 "Denormalized (Tiny) Numbers"). -/
def FFormat.isDenormal (f : FFormat) (x : Nat) : Bool :=
  x / 2 ^ f.fbits % 2 ^ f.ebits = 0 && x % 2 ^ f.fbits ≠ 0

/-- `⌊n · 2^k⌋` for an integer `k`. -/
def mulPow2 (n : Nat) (k : Int) : Nat :=
  if 0 ≤ k then n * 2 ^ k.toNat else n / 2 ^ (-k).toNat

/-- The bit pattern of format `f` that encodes `x`, for an `x` the format represents: a value
`m · 2^e` that is a multiple of the smallest denormal `2 ^ (emin − fbits)` and has at most `prec`
significant bits at its exponent (what `roundExact` delivers), a NaN whose payload fits. The
significand counted in units of the smallest denormal is `N`: below `2 ^ fbits` the value is a
denormal (biased exponent 0, fraction `N`); otherwise, with `N` in `[2 ^ (fbits + k), 2 ^ (fbits + k + 1))`,
the biased exponent is `k + 1` and the fraction the bits of `N / 2 ^ k` below the integer bit. -/
def FFormat.encode (f : FFormat) : FNum → Nat
  | .zero neg => sgn neg
  | .inf neg => sgn neg + (2 ^ f.ebits - 1) * 2 ^ f.fbits
  | .nan neg q p => sgn neg + (2 ^ f.ebits - 1) * 2 ^ f.fbits + (if q then 2 ^ (f.fbits - 1) else 0) +
      p % 2 ^ (f.fbits - 1)
  | .finite neg m e =>
    let n := mulPow2 m (e - (f.emin - f.fbits))
    if n < 2 ^ f.fbits then sgn neg + n
    else
      let k := n.log2 - f.fbits
      sgn neg + (k + 1) * 2 ^ f.fbits + (n / 2 ^ k - 2 ^ f.fbits)
where
  sgn (neg : Bool) : Nat := if neg then 2 ^ (f.width - 1) else 0

/-- The largest finite value of format `f`, `(2 ^ prec − 1) · 2 ^ (emax − prec + 1)`. -/
def FFormat.maxFinite (f : FFormat) (neg : Bool) : FNum :=
  .finite neg (2 ^ f.prec - 1) (f.emax - f.prec + 1)

/-! ## Double extended precision -/

/-- The datum an 80-bit value `x` (below `2 ^ 80`) of the double extended precision format encodes,
the x87 unit's register format (SDM Vol. 1, 4.2.2, Table 4-3, and 8.2.2, Table 8-3; APM Vol. 1,
6.3.3): sign bit 79, biased exponent in bits 78–64 (bias 16383), an explicit integer bit 63 and the
fraction in bits 62–0. With exponent 0 it is a zero (integer bit and fraction 0) or else a denormal,
or with the integer bit set a pseudo-denormal, which an operation reads as a denormal with biased
exponent 1: either is the value `m · 2 ^ (−16382 − 63)` with `m` the 64-bit significand (SDM 8.2.2;
APM 6.3.3.3). With the integer bit clear and any other exponent the encoding is unsupported (an
unnormal, a pseudo-infinity, a pseudo-NaN), `none`: such an operand raises the invalid-operation
exception (SDM 8.2.2; APM 6.3.4.2). Otherwise the all-ones exponent is an infinity (fraction 0) or a
NaN, quiet if bit 62 is set, with bits 61–0 as payload; any other exponent a normal number. -/
def extDecode (x : Nat) : Option FNum :=
  let neg := x / 2 ^ 79 % 2 = 1
  let ex : Nat := x / 2 ^ 64 % 2 ^ 15
  let m := x % 2 ^ 64
  let fr := x % 2 ^ 63
  if ex = 0 then some (if m = 0 then .zero neg else .finite neg m (-16382 - 63))
  else if m / 2 ^ 63 = 0 then none
  else if ex = 2 ^ 15 - 1 then
    some (if fr = 0 then .inf neg else .nan neg (fr / 2 ^ 62 = 1) (fr % 2 ^ 62))
  else some (.finite neg m ((ex : Int) - 16383 - 63))

/-- The 80-bit encoding of `x`, for an `x` the double extended format represents: a finite value
`m · 2^e` that is a multiple of the smallest denormal `2 ^ (−16382 − 63)` with at most 64 significant
bits at its exponent (what `roundExact` delivers for the format), a NaN whose payload fits in 62 bits.
The value counted in units of the smallest denormal is `N`: below `2 ^ 63` it is a denormal (biased
exponent 0, significand `N`); otherwise, with `N` in `[2 ^ (63 + k), 2 ^ (64 + k))`, the biased
exponent is `k + 1` and the significand `N / 2 ^ k`, its integer bit set (SDM Vol. 1, 4.2.2, 8.2.2;
APM Vol. 1, 6.3.3). The encodings of infinities and NaNs have the integer bit set. -/
def extEncode : FNum → Nat
  | .zero neg => sgn neg
  | .inf neg => sgn neg + (2 ^ 15 - 1) * 2 ^ 64 + 2 ^ 63
  | .nan neg q p => sgn neg + (2 ^ 15 - 1) * 2 ^ 64 + 2 ^ 63 + (if q then 2 ^ 62 else 0) + p % 2 ^ 62
  | .finite neg m e =>
    let n := mulPow2 m (e + 16382 + 63)
    if n < 2 ^ 63 then sgn neg + n
    else
      let k := n.log2 - 63
      sgn neg + (k + 1) * 2 ^ 64 + n / 2 ^ k
where
  sgn (neg : Bool) : Nat := if neg then 2 ^ 79 else 0

/-- Whether the 80-bit value `x` is a denormal or a pseudo-denormal: biased exponent 0, significand
not 0 (SDM Vol. 1, 8.2.2; APM Vol. 1, 6.3.3.2–6.3.3.3). -/
def extIsDenormal (x : Nat) : Bool :=
  x / 2 ^ 64 % 2 ^ 15 = 0 && x % 2 ^ 64 ≠ 0

/-- The QNaN floating-point indefinite in double extended precision: sign 1, exponent all ones,
integer bit and quiet bit set, the rest 0 (SDM Vol. 1, 4.8.3.7, Table 4-3; APM Vol. 1, Table 6-10). -/
def extIndefinite : BitVec 80 := 0xFFFFC000000000000000

/-! ## Exact results -/

/-- `⌊√n⌋`: the root's bits from the highest possible one down, each kept if the square stays at
most `n`. -/
def isqrt (n : Nat) : Nat := go (n.log2 / 2 + 1) 0
where
  go : Nat → Nat → Nat
    | 0, r => r
    | k + 1, r => go k (if (r + 2 ^ k) * (r + 2 ^ k) ≤ n then r + 2 ^ k else r)

/-- A positive real number given exactly by natural numbers: the infinitely precise magnitude of an
operation's result. `ratio num den e` is `num / den · 2^e` (sums, products, quotients, conversions),
`sqrt num e` is `√(num · 2^e)` (square roots); `num` and `den` are positive. -/
inductive Exact
  | ratio (num den : Nat) (e : Int)
  | sqrt (num : Nat) (e : Int)

/-- `⌊v · 2^k⌋`, and whether `v · 2^k` is an integer. For a square root, `⌊√y⌋ = ⌊√⌊y⌋⌋`, and
`√y` is an integer iff `y` is an integer that is a perfect square. -/
def Exact.scaled (v : Exact) (k : Int) : Nat × Bool :=
  match v with
  | .ratio num den e =>
    let s := e + k
    if 0 ≤ s then
      let n := num * 2 ^ s.toNat
      (n / den, n % den = 0)
    else
      let d := den * 2 ^ (-s).toNat
      (num / d, num % d = 0)
  | .sqrt num e =>
    let s := e + 2 * k
    let (y, exact) := if 0 ≤ s then (num * 2 ^ s.toNat, true)
      else (num / 2 ^ (-s).toNat, num % 2 ^ (-s).toNat = 0)
    let r := isqrt y
    (r, exact && r * r = y)

/-- `⌊log₂ v⌋`. For a ratio, with `a = ⌊log₂ num⌋` and `b = ⌊log₂ den⌋`, `num / den` lies in
`(2 ^ (a − b − 1), 2 ^ (a − b + 1))`, and it is at least `2 ^ (a − b)` iff `num · 2^b ≥ den · 2^a`; for a
square root, `⌊log₂ √y⌋ = ⌊⌊log₂ y⌋ / 2⌋` (`Int` division rounds down for a positive divisor). -/
def Exact.log2 : Exact → Int
  | .ratio num den e =>
    let a := num.log2
    let b := den.log2
    (if num * 2 ^ b ≥ den * 2 ^ a then (a : Int) - b else (a : Int) - b - 1) + e
  | .sqrt num e => ((num.log2 : Int) + e) / 2

/-! ## Rounding -/

/-- The rounding modes (SDM Vol. 1, 4.8.4, Table 4-9; APM Vol. 1, 4.4.4): the rounding-control
field `RC` of `MXCSR` (bits 14–13) and of the x87 control word (bits 11–10). -/
inductive Round
  /-- `00B`: to nearest, ties to the even value. -/
  | nearest
  /-- `01B`: toward −∞. -/
  | down
  /-- `10B`: toward +∞. -/
  | up
  /-- `11B`: toward zero (truncate). -/
  | zero
  deriving DecidableEq, Repr

/-- The rounding mode of a 2-bit `RC` field. -/
def Round.ofBits (rc : Nat) : Round :=
  match rc % 4 with
  | 0 => .nearest | 1 => .down | 2 => .up | _ => .zero

/-- The magnitude `v` of a result with sign `neg`, rounded under `rc` to an integer multiple of
`2^q`: the multiple's factor, whether it differs from `v`, and whether it was rounded up (in
magnitude: the factor is above `v / 2^q`). With `t = ⌊v · 2^(1−q)⌋`, the
truncated factor is `n = ⌊t / 2⌋`, the remainder `v / 2^q − n` is at least one half iff `t` is
odd, and it is 0 or exactly one half iff `v · 2^(1−q)` is an integer. Rounding goes up to `n + 1`
to nearest when the remainder is above one half, or exactly one half and `n` odd; toward −∞
for a negative result and toward +∞ for a positive one whenever there is a remainder; never toward
zero (Table 4-9). -/
def roundAt (rc : Round) (neg : Bool) (v : Exact) (q : Int) : Nat × Bool × Bool :=
  let (t, exact) := v.scaled (1 - q)
  let n := t / 2
  let half := t % 2 = 1
  let inexact := half || !exact
  let up := match rc with
    | .nearest => half && (!exact || n % 2 = 1)
    | .down => neg && inexact
    | .up => !neg && inexact
    | .zero => false
  (if up then n + 1 else n, inexact, up)

/-- `v · 2^k`. -/
def Exact.scale (v : Exact) (k : Int) : Exact :=
  match v with
  | .ratio num den e => .ratio num den (e + k)
  | .sqrt num e => .sqrt num (e + 2 * k)

/-- A result rounded to a format, before the instruction set's masked responses to underflow
(`FTZ`) are applied:
- `val`: the rounded result, a zero, a finite value or, after overflow, the masked response of
  Table 4-11;
- `inexact`: `val` differs from the infinitely precise result;
- `up`: `val`'s magnitude is above the infinitely precise result's (it was rounded up; the x87 unit
  reports this in `C1`, SDM Vol. 1, 8.5.6; APM Vol. 1, 6.2.2);
- `overflow`: the result rounded to `prec` bits with unbounded exponent is at least
  `2 ^ (emax + 1)`, beyond the largest finite value (SDM Vol. 1, 4.9.1.4, Table 4-10; APM Vol. 1,
  4.10.2.6: "Result_round > Maxnormal");
- `tiny`: the result rounded to `prec` bits with unbounded exponent is not zero and below `2 ^ emin`,
  the smallest normal value: tininess detected after rounding (SDM Vol. 1, 4.9.1.5, Table 4-12 and
  its note; APM Vol. 1, 4.10.2.7: "Result_round < Minnormal");
- `inexactWide`: the result rounded to `prec` bits with unbounded exponent differs from the infinitely
  precise result. This is the precision condition that goes with an unmasked overflow or underflow,
  whose response adjusts that result's exponent instead of delivering `val` (SDM Vol. 1,
  4.9.1.4–4.9.1.6). -/
structure Rounded where
  val : FNum
  inexact : Bool
  up : Bool
  overflow : Bool
  tiny : Bool
  inexactWide : Bool

/-- Round the result `(−1)^neg · v` to format `f` under `rc` (SDM Vol. 1, 4.8.4; APM Vol. 1, 4.4.4).
With `E = ⌊log₂ v⌋`, rounding with unbounded exponent keeps `prec` bits from bit `E` down (multiples
of `2 ^ (E − prec + 1)`), which decides overflow and tininess; the delivered result keeps the bits
from bit `max E emin` down, so that a tiny result is rounded to a multiple of the smallest denormal
(denormalization; a result below half of it may round to zero). After overflow the result is `∞` or
the largest finite value by `rc` and the sign: `∞` to nearest, toward +∞ for a positive and toward −∞
for a negative result, the largest finite value otherwise (SDM Vol. 1, Table 4-11; APM Vol. 1,
Table 4-15). -/
def roundExact (f : FFormat) (rc : Round) (neg : Bool) (v : Exact) : Rounded :=
  let E := v.log2
  -- rounded with unbounded exponent: `mu · 2 ^ (E - prec + 1)`, where `mu` is at most `2 ^ prec`
  let (mu, wide, _) := roundAt rc neg v (E - f.prec + 1)
  let overflow := decide (E > f.emax) || (decide (E = f.emax) && mu = 2 ^ f.prec)
  let tiny := decide (E < f.emin) && !(decide (E + 1 = f.emin) && mu = 2 ^ f.prec)
  let q := max E f.emin - f.prec + 1
  let (m, inexact, up) := roundAt rc neg v q
  if overflow then
    let toInf := match rc with
      | .nearest => true | .up => !neg | .down => neg | .zero => false
    ⟨if toInf then .inf neg else f.maxFinite neg, true, toInf, true, tiny, wide⟩
  else ⟨if m = 0 then .zero neg else .finite neg m q, inexact, up, false, tiny, wide⟩

/-! ## Exception conditions -/

/-- The floating-point exception conditions an operation detects (SDM Vol. 1, 4.9; APM Vol. 1,
4.10.2), in the order of their flag bits in `MXCSR` (bits 0–5) and the x87 status word (bits
0–5): invalid operation, denormal operand, divide by zero, overflow, underflow, precision
(inexact result). -/
structure FFlags where
  ie : Bool := false
  de : Bool := false
  ze : Bool := false
  oe : Bool := false
  ue : Bool := false
  pe : Bool := false
  deriving DecidableEq, Repr

/-- The conditions of either. -/
def FFlags.or (a b : FFlags) : FFlags :=
  ⟨a.ie || b.ie, a.de || b.de, a.ze || b.ze, a.oe || b.oe, a.ue || b.ue, a.pe || b.pe⟩

/-- The six conditions as the bits of the flag field (bit 0 `IE` … bit 5 `PE`). -/
def FFlags.bits (a : FFlags) : Nat :=
  a.ie.toNat + 2 * a.de.toNat + 4 * a.ze.toNat + 8 * a.oe.toNat + 16 * a.ue.toNat + 32 * a.pe.toNat

/-- The pre-computation conditions: invalid operation, denormal operand, divide by zero (SDM
Vol. 1, 4.9; APM Vol. 1, Table 4-13). -/
def FFlags.pre (a : FFlags) : FFlags := { ie := a.ie, de := a.de, ze := a.ze }

/-- The post-computation conditions: overflow, underflow, precision. -/
def FFlags.post (a : FFlags) : FFlags := { oe := a.oe, ue := a.ue, pe := a.pe }

/-! ## Controls and the operations' results -/

/-- What an operation needs of the controls (SSE: `MXCSR`): the rounding mode; whether denormal
operands are read as zeros (`DAZ`); whether tiny results are flushed to zero (`FTZ`); whether the
overflow (`OM`) and underflow (`UM`) exceptions are masked, on which the conditions reported with
them depend (`FFormat.result`). -/
structure FCtl where
  rc : Round
  daz : Bool
  ftz : Bool
  om : Bool
  um : Bool

/-- The operand a bit pattern `x` of format `f` gives an arithmetic operation, and whether it raises
the denormal-operand condition: a denormal is read as a zero of its sign under `DAZ`, without the
condition, and as itself with it otherwise (SDM Vol. 1, 4.9.1.2, 10.2.3.4; APM Vol. 1, 4.2.2 "DAZ",
4.10.2.4). -/
def FFormat.operand (f : FFormat) (c : FCtl) (x : Nat) : FNum × Bool :=
  let v := f.decode x
  if f.isDenormal x then (if c.daz then (.zero v.neg, false) else (v, true)) else (v, false)

/-- The result of a rounded operation as a bit pattern of format `f`, with its post-computation
conditions: the result `(−1)^neg · v` rounded (`roundExact`); overflow as found; underflow if the
result is tiny and, with the underflow exception masked, inexact (SDM Vol. 1, 4.9.1.5; APM Vol. 1,
4.10.2.7); precision if the result is inexact, and with an overflow or an underflow whose exception
is unmasked (no result is delivered then) if the result rounded with unbounded exponent is inexact
(`inexactWide`): the inexactness of the result with its exponent adjusted, which is what the SDM's
"If an inexact result occurs along with unmasked overflow or underflow and the destination operand
is a register, the OE or UE flag and the PE flag are set, the result is stored as described for the
overflow or underflow exceptions" (Vol. 1, 4.9.1.6) refers to, and what an AMD Zen 4 reports
(measured: `MULSD` of the largest finite value by 2 sets `OE` alone, by 1.5 `OE` and `PE`; a tiny
product exact with unbounded exponent but not as a denormal `UE` alone). The
APM (Vol. 1, 4.10.2.8) says in prose that with a masked overflow or underflow precision is reported
only for an imprecise result, but its formula's first term reports it for every inexact result,
whatever the masks, and its third term for every tiny one with the underflow masked, exact or not. With `FTZ` and the
underflow exception masked, a tiny result is replaced by a zero of the result's sign, and both
underflow and precision are reported, also for an exact one (SDM Vol. 1, 10.2.3.3; APM Vol. 1,
4.2.2 "FZ": "This naturally causes the result to be inexact, which causes both PE and UE to be
set"). -/
def FFormat.result (f : FFormat) (c : FCtl) (neg : Bool) (v : Exact) : Nat × FFlags :=
  let r := roundExact f c.rc neg v
  if c.ftz && c.um && r.tiny then (f.encode (.zero neg), { ue := true, pe := true })
  else
    let trapped := (r.overflow && !c.om) || (r.tiny && !c.um)
    (f.encode r.val, { oe := r.overflow, ue := r.tiny && (!c.um || r.inexact),
                       pe := if trapped then r.inexactWide else r.inexact })

/-- The conditions `fl` of an operation with the denormal-operand condition added, for operands of
which one is a denormal if `den` (`FFormat.operand`) and one a NaN if `nan`: it is reported unless a
NaN operand, an invalid operation or a division by zero takes precedence (SDM Vol. 1, 4.9.2,
priorities 1–3 before 4; APM Vol. 1, Table 4-13; a Zen 4 reports none of them together with it). -/
def FFlags.withDenormal (fl : FFlags) (nan den : Bool) : FFlags :=
  { fl with de := den && !nan && !fl.ie && !fl.ze }

/-- The result in format `f` of an operation on `a` and `b` of which one is a NaN: the first
operand if it is a NaN, else the second, made quiet, with the invalid-operation condition iff either
is a signaling NaN (SDM Vol. 1, 4.8.3.5, Table 4-8, the SSE column: "First source operand"; APM
Vol. 1, Table 4-5: "Value of operand 1"). -/
def FFormat.nanResult (f : FFormat) (a b : FNum) : Nat × FFlags :=
  (f.encode (if a.isNaN then a.quiet else b.quiet), { ie := a.isSNaN || b.isSNaN })

/-- The two finite or zero operands `a`, `b` of an addition as integers over a common power of two:
`(sa, sb, e)` with `a = sa · 2^e` and `b = sb · 2^e`. -/
def addends (a b : FNum) : Int × Int × Int :=
  let parts : FNum → Int × Int := fun
    | .finite n m e => (if n then -(m : Int) else m, e)
    | _ => (0, 0)
  let (ma, ea) := parts a
  let (mb, eb) := parts b
  let e := if a matches .finite .. then (if b matches .finite .. then min ea eb else ea) else eb
  (ma * 2 ^ (ea - e).toNat, mb * 2 ^ (eb - e).toNat, e)

/-- What an operation gives before its result is rounded to a format and before an instruction set's
rule for NaN operands applies:
- `exact x fl`: a result that needs no rounding (a zero, an infinity, or the QNaN indefinite of an
  invalid operation), with the conditions `fl` (invalid operation, divide by zero);
- `round neg v`: the nonzero finite result `(−1)^neg · v`, to be rounded;
- `nan a b`: an operand is a NaN; the instruction set chooses the result from the operands `a` and `b`
  (`FFormat.nanResult` for SSE; the x87 unit's rule differs, SDM Vol. 1, Table 4-8). An operation of
  one operand gives `nan a a`. -/
inductive FOut
  | exact (x : FNum) (fl : FFlags)
  | round (neg : Bool) (v : Exact)
  | nan (a b : FNum)

/-- The sum of `a` and `b` under rounding mode `rc` (IEEE 754 addition; SDM Vol. 2, "ADDSD", "FADD"):
- a NaN operand: `nan`;
- infinities of opposite signs: invalid, the QNaN indefinite (SDM Vol. 1, Table 11-1 and Table 8-10;
  APM Vol. 1, Table 4-12);
- an infinity: that infinity;
- otherwise the exact sum; an exact sum of zero is `+0`, or `−0` when rounding toward −∞, except that
  two zeros of the same sign give that zero (IEEE 754, 6.3; SDM Vol. 2, "FADD"). -/
def addOut (rc : Round) (a b : FNum) : FOut :=
  match a, b with
  | .nan .., _ | _, .nan .. => .nan a b
  | .inf na, .inf nb => if na = nb then .exact (.inf na) {} else .exact .indefinite { ie := true }
  | .inf n, _ | _, .inf n => .exact (.inf n) {}
  | _, _ =>
    let (sa, sb, e) := addends a b
    let s := sa + sb
    if s = 0 then
      let neg := match a, b with
        | .zero na, .zero nb => if na = nb then na else rc = .down
        | _, _ => rc = .down
      .exact (.zero neg) {}
    else .round (s < 0) (.ratio s.natAbs 1 e)

/-- The difference `a − b`: the sum with `b` negated, except that a NaN `b` keeps its sign (`nan` before
the negation). -/
def subOut (rc : Round) (a b : FNum) : FOut :=
  if a.isNaN || b.isNaN then .nan a b else addOut rc a b.negate

/-- The product of `a` and `b` (SDM Vol. 2, "MULSD", "FMUL"): a NaN operand `nan`; zero times infinity
invalid, the QNaN indefinite; with an infinity, an infinity, with a zero, a zero, the sign the exclusive
or of the operands'; otherwise the exact product. -/
def mulOut (a b : FNum) : FOut :=
  let neg := a.neg != b.neg
  match a, b with
  | .nan .., _ | _, .nan .. => .nan a b
  | .inf _, .zero _ | .zero _, .inf _ => .exact .indefinite { ie := true }
  | .inf _, _ | _, .inf _ => .exact (.inf neg) {}
  | .zero _, _ | _, .zero _ => .exact (.zero neg) {}
  | .finite _ ma ea, .finite _ mb eb => .round neg (.ratio (ma * mb) 1 (ea + eb))

/-- Round a value to an integral floating-point value (SDM Vol. 2, "ROUNDPS", "FRNDINT";
APM Vol. 4, "ROUNDPS", Vol. 5, "FRNDINT"). This uses `roundAt` at exponent zero;
zeros and infinities keep their sign, NaNs are handled by the instruction set, and a finite
value that rounds to zero keeps its sign. Precision is reported exactly when the value changes. -/
def roundIntOut (rc : Round) (a : FNum) : FOut :=
  match a with
  | .nan .. => .nan a a
  | .finite neg m e =>
    let (k, inexact, _) := roundAt rc neg (.ratio m 1 e) 0
    .exact (if k = 0 then .zero neg else .finite neg k 0) { pe := inexact }
  | _ => .exact a {}

/-- The fused operation `(±a·b) ± c` before rounding (SDM Vol. 1, 14.5.1–14.5.2,
Tables 14-16–14-17; APM Vol. 1, 4.7.5, Figure 4-49; Vol. 4, "VFMADD132PD", ...).
The finite product retains its entire significand and exponent for `addOut`; only the final
sum is rounded. A NaN is selected in arithmetic operand order `a`, `b`, `c`, before sign
changes, invalid if any is signaling. This also gives a quiet NaN addend precedence over
`∞·0` (SDM Table 14-17; APM Vol. 1, Table 4-5). Opposite infinities and `∞·0` without a
NaN give indefinite with invalid. Exact zeros follow addition's signed-zero rule. -/
def fmaOut (rc : Round) (negProduct subAddend : Bool) (a b c : FNum) : FOut :=
  let neg := (a.neg != b.neg) != negProduct
  let signedC := if subAddend then c.negate else c
  match a, b, c with
  | .nan .., _, _ | _, .nan .., _ | _, _, .nan .. =>
    let n := if a.isNaN then a else if b.isNaN then b else c
    .exact n.quiet { ie := a.isSNaN || b.isSNaN || c.isSNaN }
  | .inf _, .zero _, _ | .zero _, .inf _, _ => .exact .indefinite { ie := true }
  | .inf _, _, _ | _, .inf _, _ => addOut rc (.inf neg) signedC
  | .zero _, _, _ | _, .zero _, _ => addOut rc (.zero neg) signedC
  | .finite _ ma ea, .finite _ mb eb, _ =>
    addOut rc (.finite neg (ma * mb) (ea + eb)) signedC

/-- The quotient `a / b` (SDM Vol. 2, "DIVSD", "FDIV"): a NaN operand `nan`; `0 / 0` and `∞ / ∞` invalid,
the QNaN indefinite; a finite nonzero dividend over zero the divide-by-zero condition and an infinity
(SDM Vol. 1, 4.9.1.3); `∞ / x` an infinity, `x / ∞` and `0 / x` a zero; otherwise the exact quotient.
The sign is the exclusive or of the operands'. -/
def divOut (a b : FNum) : FOut :=
  let neg := a.neg != b.neg
  match a, b with
  | .nan .., _ | _, .nan .. => .nan a b
  | .zero _, .zero _ | .inf _, .inf _ => .exact .indefinite { ie := true }
  | .inf _, _ => .exact (.inf neg) {}
  | _, .inf _ => .exact (.zero neg) {}
  | .zero _, _ => .exact (.zero neg) {}
  | _, .zero _ => .exact (.inf neg) { ze := true }
  | .finite _ ma ea, .finite _ mb eb => .round neg (.ratio ma mb (ea - eb))

/-- The square root of `a` (SDM Vol. 2, "SQRTSD", "FSQRT"): a NaN `nan a a`; a zero itself (`√−0 = −0`);
`+∞` itself; any other negative operand invalid, the QNaN indefinite (SDM Vol. 1, Table 11-1 and
Table 8-10); otherwise the exact root. -/
def sqrtOut (a : FNum) : FOut :=
  match a with
  | .nan .. => .nan a a
  | .zero _ => .exact a {}
  | .inf false => .exact a {}
  | .finite false m e => .round false (.sqrt m e)
  | _ => .exact .indefinite { ie := true }

/-- An operation's result in format `f` under the controls `c`, as SSE and AVX deliver it: an exact
result encoded, a finite one rounded (`FFormat.result`), a NaN operand's by `nanResult`. -/
def FFormat.finish (f : FFormat) (c : FCtl) : FOut → Nat × FFlags
  | .exact x fl => (f.encode x, fl)
  | .round neg v => f.result c neg v
  | .nan a b => f.nanResult a b

/-- The sum of `a` and `b` in format `f` (`addOut`; SDM Vol. 2, "ADDSD", "ADDSS", ...). -/
def FFormat.add (f : FFormat) (c : FCtl) (a b : FNum) : Nat × FFlags := f.finish c (addOut c.rc a b)

/-- The difference `a − b` in format `f` (`subOut`). -/
def FFormat.sub (f : FFormat) (c : FCtl) (a b : FNum) : Nat × FFlags := f.finish c (subOut c.rc a b)

/-- The product of `a` and `b` in format `f` (`mulOut`; SDM Vol. 2, "MULSD", ...). -/
def FFormat.mul (f : FFormat) (c : FCtl) (a b : FNum) : Nat × FFlags := f.finish c (mulOut a b)

/-- The quotient `a / b` in format `f` (`divOut`; SDM Vol. 2, "DIVSD", ...). -/
def FFormat.div (f : FFormat) (c : FCtl) (a b : FNum) : Nat × FFlags := f.finish c (divOut a b)

/-- The square root of `a` in format `f` (`sqrtOut`; SDM Vol. 2, "SQRTSD", ...). -/
def FFormat.sqrt (f : FFormat) (c : FCtl) (a : FNum) : Nat × FFlags := f.finish c (sqrtOut a)

/-! ## Comparisons -/

/-- How two operands compare: by value, with `−0 = +0`, or unordered when either is a NaN (SDM
Vol. 2, "UCOMISD", "CMPPD"). -/
inductive FOrder | lt | eq | gt | unordered
  deriving DecidableEq, Repr

/-- The value of a zero, finite or infinite datum as an extended number, for comparisons:
`none` for `±∞` and NaNs, else the integer `±m` and exponent `e`. -/
def FNum.signedParts : FNum → Option (Int × Int)
  | .zero _ => some (0, 0)
  | .finite n m e => some (if n then -(m : Int) else m, e)
  | _ => none

/-- Compare `a` with `b`. Two finite values `x · 2^ex` and `y · 2^ey` are compared over the smaller
exponent; an infinity is beyond every finite value. -/
def fcompare (a b : FNum) : FOrder :=
  if a.isNaN || b.isNaN then .unordered else
  let rank : FNum → Int := fun
    | .inf n => if n then -1 else 1
    | _ => 0
  match a.signedParts, b.signedParts with
  | some (x, ex), some (y, ey) =>
    let e := min ex ey
    let x' := x * 2 ^ (ex - e).toNat
    let y' := y * 2 ^ (ey - e).toNat
    if x' < y' then .lt else if x' = y' then .eq else .gt
  | _, _ =>
    let ra := rank a
    let rb := rank b
    if ra < rb then .lt else if ra = rb then .eq else .gt

/-! ## Conversions -/

/-- `a` (format `g`) converted to format `f` (SDM Vol. 2, "CVTSD2SS", "CVTSS2SD"): a NaN keeps its
sign and the high bits of its fraction, made quiet, invalid if signaling (SDM Vol. 1, Table 11-1:
"Return the SNaN converted to a QNaN"); zeros and infinities are kept; a finite value is rounded to
`f` (exact when `f` is the wider format). -/
def FFormat.convert (f g : FFormat) (c : FCtl) (a : FNum) : Nat × FFlags :=
  match a with
  | .nan n _ p =>
    (f.encode (.nan n true (mulPow2 p ((f.fbits : Int) - g.fbits))), { ie := a.isSNaN })
  | .zero _ | .inf _ => (f.encode a, {})
  | .finite n m e => f.result c n (.ratio m 1 e)

/-- The signed integer `i` converted to format `f` (SDM Vol. 2, "CVTSI2SD", "CVTSI2SS"): zero is
`+0`; any other value is rounded by `rc`, which reports precision but never overflow or underflow
for the integers of at most 64 bits these instructions take. -/
def FFormat.ofInt (f : FFormat) (rc : Round) (i : Int) : Nat × FFlags :=
  if i = 0 then (f.encode (.zero false), {})
  else
    let r := roundExact f rc (i < 0) (.ratio i.natAbs 1 0)
    (f.encode r.val, { pe := r.inexact })

/-- `a` converted to a signed integer of `w` bits, rounded by `rc` (SDM Vol. 2, "CVTSD2SI",
"CVTTSD2SI": the truncating forms round toward zero, SDM Vol. 1, 4.8.4.2): a NaN, an infinity or a
value whose rounded result is outside the `w`-bit range gives the integer indefinite `2 ^ (w − 1)`
(the most negative integer) and the invalid-operation condition (SDM Vol. 1, Table 11-1; APM Vol. 1,
Table 4-7); otherwise the rounded integer, with the precision condition if it differs from `a`. The
result is the integer's `w`-bit two's complement encoding. -/
def FNum.toInt (a : FNum) (w : Nat) (rc : Round) : Nat × FFlags :=
  let indefinite := (2 ^ (w - 1), ({ ie := true } : FFlags))
  match a with
  | .zero _ => (0, {})
  | .finite n m e =>
    let (k, inexact, _) := roundAt rc n (.ratio m 1 e) 0
    let i : Int := if n then -(k : Int) else k
    if -(2 ^ (w - 1) : Int) ≤ i ∧ i < 2 ^ (w - 1) then ((i % 2 ^ w).toNat, { pe := inexact })
    else indefinite
  | _ => indefinite

end ZellicX86
