import Lean
import ZellicX86.Spec.Object
/-!
# Loading a file's bytes as constants: `#file_image`

The loader, one of the things a statement's meaning rests on (README, "Trust base"): a statement about a file's
bytes is about the constants this command defines.
`#file_image "path" sha256 "hex" as F` runs once, when Lean elaborates the command: it reads the file at `path` (an
absolute path, or relative to the directory of the source file the command is in, so that it is found wherever the
project is built, as a dependency of another too), computes its SHA-256 and stops with an error unless that is `hex`,
and adds these definitions, which the module's `.olean` then holds (importers never read the file):

- `F.size : Nat`, the file's size `n` in bytes;
- `F.p0`, `F.p1`, … : `Nat`, page `k` of the file as one number, `∑ j < 4096, b (4096 k + j) · 256 ^ j` with `b i`
  the file's byte `i` (0 from `n` on): byte `j` of the page is bits `8 j` to `8 j + 7`;
- `F.page : Nat → Nat`, page `k`'s number for `k` below the number of pages `m`, `0` from there on
  (`F.page k = Bool.rec (F.t0_m k) 0 (Nat.ble m k)`): chosen by a balanced tree of definitions
  `F.t<lo>_<hi> k = Bool.rec (left k) (right k) (Nat.ble mid k)` over the page numbers `lo ≤ k < hi`, `mid` their
  middle, `left` the tree of those below it, `right` of the others (`Bool.rec x y b` is `x` for `b = false`, `y` for
  `b = true`: `right k` where `mid ≤ k`), each leaf a page's constant;
- `F.img : Nat → Byte`, `F.img i = BitVec.ofNat 8 (Nat.shiftRight (F.page (Nat.div i 4096)) (Nat.mul 8 (Nat.mod i
  4096)))`, the byte `i % 4096` of page `i / 4096`: the file's byte `i` for `i < n`, `0` from `n` on;
- `F.blob : Blob`, `⟨F.img, F.size⟩`: the file as `Spec/Object.lean`'s readers take it.

So the statement's source names the file by its hash, and `F.img` is the bytes of the file with that hash. The pages
are `Nat` literals (a bignum each in the kernel) rather than lists of bytes, so that a file of megabytes is a few
thousand constants: the kernel reads a byte by a descent of the tree and one shift. The tree's
nodes and `F.img` are written with `Bool.rec`, `Nat.ble` and `Nat`'s functions themselves rather than `cond`, `<` and
the operators' notation, which the kernel would unfold to them on every byte it reads.

What it is trusted for. The command runs ordinary compiled Lean code when Lean elaborates it (reading the file,
hashing it, building the terms); Lean's kernel then checks the definitions it adds like any others. No proof depends on
that code: a proof is checked against the constants themselves, and `lake comparator` requires every constant a
statement mentions to be the same in the statement's challenge and in the proof's export. What rests on the code is
only the link between those constants and the file the source names: that `sha256Hex` is FIPS 180-4's SHA-256 (every
`#file_image` of this repository compares it with a digest `sha256sum` printed, so `lake build` checks it on those
files), that a page's number holds the page's bytes in the order above (`leNatOf`), that the tree selects page `k`
(`defineFileImage`), and that `F.img` is the byte formula above. The definitions are `noncomputable` and have the
`abbrev` reducibility hint; both affect only evaluation, not what the definitions mean.
-/
namespace ZellicX86.Load
open Lean Meta Elab

/-! ## SHA-256 (NIST FIPS 180-4, section 4.2.2 the constants, section 5.1.1 the padding, section 5.3.3 the initial value, section 6.2 the
computation) -/

/-- The 64 constants `K₀ … K₆₃` (FIPS 180-4 section 4.2.2). -/
private def shaK : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value `H⁽⁰⁾` (FIPS 180-4 section 5.3.3). -/
private def shaH0 : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Rotation right by `n` of a 32-bit word (`ROTR`, FIPS 180-4 section 3.2). -/
private def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- The message `b` padded (FIPS 180-4 section 5.1.1): a 1 bit (the byte `0x80`), zeros up to 56 bytes modulo 64, and the
message's length in bits as a 64-bit big-endian number. -/
private def shaPad (b : ByteArray) : ByteArray := Id.run do
  let mut m := b.push 0x80
  while m.size % 64 != 56 do m := m.push 0
  for j in [0:8] do m := m.push ((8 * b.size) >>> (8 * (7 - j)) % 256).toUInt8
  return m

/-- The big-endian 32-bit word at offset `o` of `m`. -/
private def word (m : ByteArray) (o : Nat) : UInt32 :=
  (m[o]!.toUInt32 <<< 24) ||| (m[o + 1]!.toUInt32 <<< 16) ||| (m[o + 2]!.toUInt32 <<< 8) ||| m[o + 3]!.toUInt32

/-- The hash value after the 512-bit block at offset `o` of the padded message `m` (FIPS 180-4 section 6.2.2: the message
schedule `W`, the 64 rounds, the sum with the previous value `h`). -/
private def shaBlock (m : ByteArray) (o : Nat) (h : Array UInt32) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := (Array.range 16).map fun t => word m (o + 4 * t)
  for t in [16:64] do
    let s0 := rotr w[t - 15]! 7 ^^^ rotr w[t - 15]! 18 ^^^ (w[t - 15]! >>> 3)
    let s1 := rotr w[t - 2]! 17 ^^^ rotr w[t - 2]! 19 ^^^ (w[t - 2]! >>> 10)
    w := w.push (s1 + w[t - 7]! + s0 + w[t - 16]!)
  let mut a := h[0]!; let mut b := h[1]!; let mut c := h[2]!; let mut d := h[3]!
  let mut e := h[4]!; let mut f := h[5]!; let mut g := h[6]!; let mut k := h[7]!
  for t in [0:64] do
    let t1 := k + (rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25) + ((e &&& f) ^^^ ((~~~e) &&& g)) + shaK[t]! + w[t]!
    let t2 := (rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22) + ((a &&& b) ^^^ (a &&& c) ^^^ (b &&& c))
    k := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
  return #[a + h[0]!, b + h[1]!, c + h[2]!, d + h[3]!, e + h[4]!, f + h[5]!, g + h[6]!, k + h[7]!]

/-- The SHA-256 digest of `b` in lowercase hexadecimal, as `sha256sum` prints it. -/
def sha256Hex (b : ByteArray) : String := Id.run do
  let m := shaPad b
  let mut h := shaH0
  for blk in [0:m.size / 64] do h := shaBlock m (64 * blk) h
  let hex (x : UInt32) : String :=
    let s := String.ofList (Nat.toDigits 16 x.toNat)
    String.ofList (List.replicate (8 - s.length) '0') ++ s
  return String.join (h.toList.map hex)

/-! ## The definitions -/

/-- The little-endian number of the bytes `lo ≤ i < hi` of `b` (`∑ b[i] · 256 ^ (i - lo)`): up to eight bytes one by
one, more as the low half's number plus the high half's shifted above it, so that a page costs `O(n log n)` in the
bignum operations. -/
def leNatOf (b : ByteArray) (lo hi : Nat) : Nat :=
  if hi ≤ lo + 8 then Id.run do
    let mut n := 0
    for j in [0:hi - lo] do
      n := n ||| ((b.get! (lo + j)).toNat <<< (8 * j))
    return n
  else
    let mid := (lo + hi) / 2
    leNatOf b lo mid ||| (leNatOf b mid hi <<< (8 * (mid - lo)))
termination_by hi - lo
decreasing_by all_goals omega

/-- Add the definition `n : ty := v`, `noncomputable`: it is for the kernel, and compiled code never runs it (`#eval`
of it is an error rather than a missing definition). -/
private def addDef (n : Name) (ty v : Expr) : MetaM Unit := do
  addDecl <| .defnDecl (mkDefinitionValEx n [] ty v .abbrev .safe [n])
  modifyEnv (addNoncomputable · n)

/-- Add the module's description: `F.size`, the pages `F.p<k>`, the tree `F.t<lo>_<hi>`, `F.page` and `F.img` of the
bytes `b`. -/
def defineFileImage (F : Name) (b : ByteArray) : MetaM Unit := do
  let natT := mkConst ``Nat
  let nPages := (b.size + 4095) / 4096
  addDef (F ++ `size) natT (mkRawNatLit b.size)
  for k in [0:nPages] do
    addDef (F ++ Name.mkSimple s!"p{k}") natT (mkRawNatLit (leNatOf b (4096 * k) (min b.size (4096 * k + 4096))))
  let nodeT ← mkArrow natT natT
  -- `Bool.rec l r (Nat.ble m k)` (`l` where `k < m`, `r` where `m ≤ k`), `k` the bound variable of the definition's
  -- `fun k`
  let choose (m : Nat) (l r : Expr) : Expr :=
    mkApp4 (mkConst ``Bool.rec [1]) (mkLambda `b .default (mkConst ``Bool) natT) l r
      (mkApp2 (mkConst ``Nat.ble) (mkRawNatLit m) (.bvar 0))
  -- the selection among the pages `lo ≤ k < hi` as a term of `k`: a page's constant, or a node's application to `k`
  let rec node (lo hi fuel : Nat) : MetaM Expr := do
    match fuel with
    | 0 => throwError "file_image: the tree is deeper than 64"
    | fuel + 1 =>
      if hi ≤ lo + 1 then return mkConst (F ++ Name.mkSimple s!"p{lo}")
      let mid := (lo + hi) / 2
      let nm := F ++ Name.mkSimple s!"t{lo}_{hi}"
      addDef nm nodeT (mkLambda `k .default natT (choose mid (← node lo mid fuel) (← node mid hi fuel)))
      return mkApp (mkConst nm) (.bvar 0)
  -- (an empty file has no page: `F.page` is `0` everywhere)
  let root ← if nPages = 0 then pure (mkRawNatLit 0) else node 0 nPages 64
  addDef (F ++ `page) nodeT (mkLambda `k .default natT (choose nPages root (mkRawNatLit 0)))
  -- `fun i => BitVec.ofNat 8 (Nat.shiftRight (F.page (Nat.div i 4096)) (Nat.mul 8 (Nat.mod i 4096)))`
  let img ← withLocalDeclD `i natT fun i => do
    let sh := mkApp2 (mkConst ``Nat.shiftRight) (mkApp (mkConst (F ++ `page)) (mkApp2 (mkConst ``Nat.div) i (mkRawNatLit 4096)))
      (mkApp2 (mkConst ``Nat.mul) (mkRawNatLit 8) (mkApp2 (mkConst ``Nat.mod) i (mkRawNatLit 4096)))
    mkLambdaFVars #[i] (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 8) sh)
  addDef (F ++ `img) (← inferType img) img
  addDef (F ++ `blob) (mkConst ``Blob) (mkApp2 (mkConst ``Blob.mk) (mkConst (F ++ `img)) (mkConst (F ++ `size)))

/-- `#file_image "path" sha256 "hex" as F`: the file at `path` (relative to the directory of the command's source file)
as `F.size`, `F.page`, `F.img`, `F.blob` (`defineFileImage`), if its SHA-256 is `hex`; an error otherwise, or where
`F.size` exists. -/
syntax (name := fileImageCmd) "#file_image " str &" sha256 " str &" as " ident : command

@[command_elab fileImageCmd] def elabFileImage : Command.CommandElab := fun stx => do
  let path := stx[1].isStrLit?.getD ""
  let want := stx[3].isStrLit?.getD ""
  let F := (← getCurrNamespace) ++ stx[5].getId
  Command.liftTermElabM do
    if (← getEnv).contains (F ++ `size) then throwError "file_image: {F} is defined already"
    let src ← getFileName
    let file : System.FilePath :=
      if (System.FilePath.mk path).isAbsolute then path
      else ((System.FilePath.mk src).parent.getD ".") / path
    let b ← IO.FS.readBinFile file
    let got := sha256Hex b
    unless got == want do throwError "file_image: {path} has SHA-256 {got}, not {want}"
    defineFileImage F b
    logInfo m!"{F}: {file}, {b.size} bytes, {(b.size + 4095) / 4096} pages"

end ZellicX86.Load
