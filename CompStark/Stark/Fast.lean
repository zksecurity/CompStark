/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Plonky3.Prover
public import CompStark.Mont32.Challenge
public import CompStark.Poseidon2.PackedField
public import CompStark.Merkle.Packed
public import CompPoly.Univariate.NTTFast.Packed.CosetLde
public import CompStark.Stark.Words
public import CompStark.Stark.ExtWords

/-! # The fast prover backend

The kernels of `Backend` on packed Montgomery words, over a Montgomery field `FastField p` with its
domains (`Mont32BaseField`), the quartic extension `Ext4 p` (`Binomial4`), Plonky3's Poseidon2
(`Poseidon2Field`) on packed groups (`PackedPoseidon2`) and CompPoly's compiled coset LDE
(`PackedCosetLde`):

* The transcript is Plonky3's duplex challenger on the field's Poseidon2 implementation. Grinding
  tries eight candidates per packed permutation, as Plonky3 does, and returns the smallest that
  passes.
* Low-degree extension is CompPoly's batched coset LDE.
* The Merkle digest layers of matrices of one height come from the packed Merkle commitment, on
  their rows side by side.

The kernels compute the specification's functions on the shapes the prover gives them
(`Fri.Refines`): matrices of `2 ^ k` rows within the two-adic subgroups, addressable by machine
indices, and opening points outside the base field.

Every function is generic in the modulus. The compiler specializes it where a field instantiates
it, with the field's Montgomery constants as immediates; that module belongs to the CPU-targeted
native library.
-/

@[expose] public section
namespace CompStark.Stark.Fast
open CompStark.Fri CompStark.Poseidon2 Montgomery.Native32
open CompPoly.CPolynomial.NTTFast.Packed (LdePlan PackedCosetLde)

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p
local notation "EF" => Ext4 p

/-- A row-major matrix of base elements as packed Montgomery words. -/
structure PMat where
  width : Nat
  height : Nat
  words : ByteArray

/-- A field element from a packed word. -/
def word (b : ByteArray) (i : Nat) : F :=
  CompPoly.CPolynomial.NTTFast.Packed.ofWord p (CompPoly.CPolynomial.NTTFast.Packed.Native.read b i)

/-- The first passing candidate of batch `b`, `8 b, …, 8 b + 7`: `group` holds eight copies of the
duplexed state as a packed group, and the candidates go into coordinate `wi`. -/
def grindBatch (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p] (group :
    @& ByteArray)
    (wi bits b : Nat) : Option Nat :=
  let W := (List.range 8).foldl (fun W l ↦ CompPoly.CPolynomial.NTTFast.Packed.Native.write W
    (8 * wi + l) ((8 * b + l : Nat) : FastField p).val)
    (group.copySlice 0 ByteArray.empty 0 group.size)
  let out := PackedPoseidon2.permute24 p W
  ((List.range 8).find? fun l ↦ 8 * b + l < p &&
    FastField.toNat (word (p := p) out (8 * 15 + l)) % 2 ^ bits == 0).map (8 * b + ·)

/-- The first passing candidate of the `nb` batches from `b`, if any. -/
def grindRange (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p] (group :
    @& ByteArray)
    (wi bits : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | nb + 1, b =>
    match grindBatch p group wi bits b with
    | some m => some m
    | none => grindRange p group wi bits nb (b + 1)

/-- The smallest passing candidate from wave `wave` on: each wave splits 1024 batches of eight
candidates among 16 tasks, and the first wave with a passing candidate has the smallest. -/
def grindWaves (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p] (group :
    ByteArray) (wi bits : Nat) :
    Nat → Nat → FastField p
  | 0, _ => 0
  | fuel + 1, wave =>
    let ts := (Array.range 16).map fun k ↦ Task.spawn fun _ ↦
      grindRange p group wi bits 64 (1024 * wave + 64 * k)
    match (ts.map Task.get).findSome? id with
    | some c => (c : FastField p)
    | none => grindWaves p group wi bits fuel (wave + 1)

/-- The smallest grinding witness for `bits`, eight candidates per packed permutation as Plonky3
grinds, in parallel waves. With a full state the candidates go to coordinate 24, past the group,
and are dropped as `Hash.overwrite` drops them. -/
def grind [Poseidon2Field (FastField p)] [PackedPoseidon2 p] (c : Challenger F 24) (bits : Nat) : F
    :=
  let base := Hash.overwrite c.state c.input.toList
  let group := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields
    (Array.ofFn (n := 192) fun k ↦ base.toArray.getD (k / 8) 0)
  grindWaves p group (min c.input.size 24) bits (p / 8192 + 1) 0

/-- The fast transcript. -/
def transcript [Mont32BaseField p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p] :
    Transcript F 24 :=
  Transcript.initWith Poseidon2.duplex grind

/-- The domain of order `2 ^ k` of the base field, `k ≤ twoAdicity`. -/
def domain [Mont32BaseField p] (k : Nat) (h : k ≤ twoAdicity F) :
    CompPoly.CPolynomial.NTT.Domain F :=
  ⟨k, twoAdicGen k, BaseField.isPrimitiveRoot_twoAdicGen k h⟩

/-- CompPoly's plan for extensions of `2 ^ logH`-row matrices by `2 ^ bits` onto `shift · ⟨ω_N⟩`,
`ω_N = twoAdicGen (logH + bits)`. -/
def plan? [Mont32BaseField p] (logH bits : Nat) (shift : F) : Option (LdePlan p) :=
  if h : logH + bits ≤ twoAdicity F then
    have h29 : logH + bits ≤ 29 := le_trans h (Mont32BaseField.twoAdicity_le_29 p)
    some (LdePlan.ofDomain (domain (logH + bits) h) bits
      (by change bits ≤ logH + bits; omega) shift (by change logH + bits ≤ 32; omega) (by
        have hp : 2 ^ (logH + bits) ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) h29
        have := USize.le_size
        change 4 * 2 ^ (logH + bits) < USize.size
        omega))
  else none

/-- CompPoly's batched coset LDE, bit-reversed rows, packed: `ldeRef` on words. Plans come from
`plans` when one matches, else are built; there is none beyond the two-adic subgroups. -/
def ldeWith [Mont32BaseField p] [PackedCosetLde p] (plans : List (Nat × Nat × F × LdePlan p))
    (logH bits : Nat) (shift : F) (w : Nat) (m : Array F) : PMat :=
  let found := plans.find? fun (h, b, s, _) ↦ h == logH && b == bits && s == shift
  match found.map (·.2.2.2) <|> plan? logH bits shift with
  | some P =>
    let out := CompPoly.CPolynomial.NTTFast.Packed.Native.joinRows
      (P.cosetLde w (CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields m))
    { width := w, height := 2 ^ (logH + bits), words := out }
  | none => { width := w, height := 0, words := .empty }

/-- The extension without cached plans. -/
def lde [Mont32BaseField p] [PackedCosetLde p] (logH bits : Nat) (shift : F) (w : Nat)
    (m : Array F) : PMat :=
  ldeWith [] logH bits shift w m

/-- The extension plans of a proof of a `2 ^ logN`-row trace and `2 ^ logChunks` quotient chunks:
the trace's extension on `g · ⟨ω_N⟩` and every chunk's. -/
def ldePlans [Mont32BaseField p] (logN logBlowup logChunks : Nat) : List (Nat × Nat × F × LdePlan
    p) :=
  let qlog := logN + logChunks
  let shifts : List F := gen :: (List.range (2 ^ logChunks)).map fun c ↦
    gen * (gen * powF (twoAdicGen qlog) c)⁻¹
  shifts.filterMap fun s ↦ (plan? logN logBlowup s).map fun P ↦ (logN, logBlowup, s, P)

/-- `out` followed by at most `fuel` layers above `layer` of `n` digests, up to the root. -/
def upperPacked (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p] (layer :
    ByteArray) (n : Nat)
    (out : Array ByteArray) : Nat → Array ByteArray
  | 0 => out
  | fuel + 1 =>
    if n ≤ 1 then out else
    let (l, n') := Merkle.Packed.nextLayer p layer n
    upperPacked p l n' (out.push l) fuel

/-- The packed digest layers of the Merkle tree of one matrix of width `w` given as one chunk of
rows. -/
def packedLayers (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p] (w :
    Nat) (m : ByteArray) :
    Array ByteArray :=
  let h := if w = 0 then 0 else m.size / (4 * w)
  let parts := if h < 1024 then 1 else 16
  let rows := h / parts
  let chunks := (Array.range parts).map fun k ↦
    m.extract (4 * w * (k * rows)) (if k + 1 = parts then m.size else 4 * w * ((k + 1) * rows))
  let (first, h) := Merkle.Packed.leaves p w chunks
  let padded := if h = 1 then 1 else h + h % 2
  let layer := Merkle.Packed.padDigests first h padded
  upperPacked p layer padded #[layer] 64

/-- The rows of matrices of one height side by side, packed. -/
def sideBySide (ms : List PMat) (h : Nat) : ByteArray :=
  match ms with
  | [m] => m.words
  | _ => Id.run do
    let w := ms.foldl (· + ·.width) 0
    let mut out := CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords (h * w)
    for r in [0:h] do
      let mut off := r * w
      for m in ms do
        out := m.words.copySlice (4 * r * m.width) out (4 * off) (4 * m.width)
        off := off + m.width
    return out

/-- Digests as consecutive packed words. -/
def encodeDigests (ds : Array (Digest F)) : ByteArray :=
  CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields (ds.flatMap (·.toArray))

/-- Packed matrices under one Merkle tree, with the packed digest layers, leaves first. -/
structure Commit where
  mats : List PMat
  layers : Array ByteArray

/-- Commit to packed matrices of one height: the packed Merkle commitment on their rows side by
side. -/
def commit (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p] (ms : List
    PMat) : Commit :=
  ⟨ms, match ms with
    | m :: _ => packedLayers p (ms.foldl (· + ·.width) 0) (sideBySide ms m.height)
    | [] => #[]⟩

namespace Commit

/-- The largest matrix height. -/
def maxHeight (c : Commit) : Nat := c.mats.foldl (fun m a ↦ max m a.height) 0

/-- Row `r` of a packed matrix, read without bounds: a query reads a few rows, so its reads need
no `USize` index. -/
def readRow (m : PMat) (r : Nat) : Array F :=
  let a : Array F := CompPoly.PackedRepr.decode (m.words.extract (4 * (r * m.width))
    (4 * (r * m.width + m.width)))
  Array.ofFn (n := m.width) fun j ↦ a.getD j.val 0

/-- Digest `k` of a packed layer: its 32 bytes, copied out, whose word reads always fit. -/
def readDigest (b : ByteArray) (k : Nat) : Digest F :=
  let d := b.extract (32 * k) (32 * k + 32)
  Vector.ofFn fun j ↦ word d j.val

/-- The Merkle root. -/
def root (c : Commit) : Digest F := readDigest (c.layers.back?.getD .empty) 0

/-- `Committed.openAt` on packed rows and layers. -/
def openAt (c : Commit) (index : Nat) : BatchOpening F :=
  let logMax := Merkle.log2Ceil c.maxHeight
  let rows := c.mats.map fun m ↦ readRow m (index >>> (logMax - Merkle.log2Ceil m.height))
  ⟨rows.toArray, Array.ofFn (n := logMax) fun i ↦
    readDigest (c.layers.getD i.val .empty) ((index >>> i.val) ^^^ 1)⟩

end Commit

/-- Words `i, …, i + B - 1` of `b`. -/
def slice (b : ByteArray) (i B : Nat) : ByteArray := b.extract (4 * i) (4 * (i + B))

/-- Word `(c, r)` of the trace on the quotient domain held as pieces of `R` rows each, every piece
column-major, the pieces one after another: rows in the extension's bit-reversed order. -/
@[inline] def cell (cols : @& ByteArray) (w R c r : Nat) : UInt32 :=
  CompPoly.CPolynomial.NTTFast.Packed.Native.read cols (r / R * (R * w) + c * R + r % R)

/-- Column `c` at the rows `idx[r0], …, idx[r0 + B - 1]`. -/
def gather (cols : @& ByteArray) (w R c : Nat) (idx : @& Array Nat) (r0 B : Nat) : ByteArray :=
  Id.run do
  let mut out := CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords B
  for k in [0:B] do
    out := CompPoly.CPolynomial.NTTFast.Packed.Native.write out k
      (cell cols w R c (idx.getD (r0 + k) 0))
  return out

/-- The packed values of `e` on the rows `r0, …, r0 + B - 1` of the quotient domain in the
extension's bit-reversed order, `B` dividing the piece height `R`: `evalBlock` on words. The
next row of row `r` is `next[r]`, and `first`, `last`, `trans` are the selectors in that order.
Next rows of a block are almost always a block themselves: `contiguous` gives its first row, and
it is read as one slice. -/
def evalWords (cols : ByteArray) (w R B : Nat) (next : Array Nat) (contiguous : Array (Option Nat))
    (pis : List F) (first last trans : ByteArray) (r0 : Nat) : Expr F → ByteArray
  | .cur c => slice cols (r0 / R * (R * w) + c * R + r0 % R) B
  | .next c =>
    match contiguous.getD (r0 / B) none with
    | some n0 => slice cols (n0 / R * (R * w) + c * R + n0 % R) B
    | none => gather cols w R c next r0 B
  | .pub j => Words.replicateWord (pis.getD j 0).val B
  | .const c => Words.replicateWord c.val B
  | .isFirstRow => slice first r0 B
  | .isLastRow => slice last r0 B
  | .isTransition => slice trans r0 B
  | .add a b => Words.addWords p (evalWords cols w R B next contiguous pis first last trans r0 a)
      (evalWords cols w R B next contiguous pis first last trans r0 b) B
  | .sub a b => Words.subWords p (evalWords cols w R B next contiguous pis first last trans r0 a)
      (evalWords cols w R B next contiguous pis first last trans r0 b) B
  | .mul a b => Words.mulWords p (evalWords cols w R B next contiguous pis first last trans r0 a)
      (evalWords cols w R B next contiguous pis first last trans r0 b) B

/-- The rows `perm[i0], …, perm[i0 + len - 1]` of a packed row-major matrix of width `w`,
copied whole. -/
def permuteRange (m : @& ByteArray) (w : Nat) (perm : @& Array Nat) (i0 len : Nat) : ByteArray :=
  Id.run do
  let mut out := CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords (len * w)
  for k in [0:len] do
    out := m.copySlice (4 * w * perm.getD (i0 + k) 0) out (4 * w * k) (4 * w)
  return out

/-- The rows `perm[0], perm[1], …` of a packed row-major matrix of width `w`, by parallel ranges. -/
def permuteWords (m : ByteArray) (w : Nat) (perm : Array Nat) : ByteArray :=
  let n := perm.size
  let parts := if n < 4096 then 1 else 16
  let size := n / parts
  let ts := (Array.range parts).map fun k ↦ Task.spawn fun _ ↦
    permuteRange m w perm (k * size) (if k + 1 = parts then n - k * size else size)
  ts.foldl (fun acc t ↦ acc ++ t.get) ByteArray.empty

/-- The tables of the quotient on the quotient domain of a `2 ^ degreeBits`-row trace with
`2 ^ logChunks` chunks, rows in the extension's bit-reversed order: the order, the selectors, the
inverse vanishing polynomial (period `2 ^ logChunks`), the next rows, and per block of `B` rows
the first next row when the next rows form a block. They depend only on the shape. -/
structure QuotientTables (q : ℕ) [Mont32Field q] where
  degreeBits : Nat
  logChunks : Nat
  perm : Array Nat
  invZh : Array (FastField q)
  first : ByteArray
  last : ByteArray
  trans : ByteArray
  next : Array Nat
  B : Nat
  contiguous : Array (Option Nat)

/-- The quotient tables of a shape. -/
def quotientTables [Mont32BaseField p] (degreeBits logChunks : Nat) : QuotientTables p :=
  let qlog := degreeBits + logChunks
  let n := 2 ^ qlog
  let perm := bitRevPerm qlog
  let xs := cosetPoints gen qlog
  let gInv : F := (twoAdicGen degreeBits)⁻¹
  let period := 2 ^ logChunks
  let zhs := Array.ofFn (n := period) fun k ↦ powF (xs.getD k 0) (2 ^ degreeBits) - 1
  let invFirst := batchInv (xs.map (· - 1))
  let invLast := batchInv (xs.map (· - gInv))
  let next := perm.map fun i ↦ perm.getD ((i + period) % n) 0
  let R := n / (if n < 4096 then 1 else 16)
  let B := min R 256
  { degreeBits, logChunks, perm, invZh := batchInv zhs, next, B
    first := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields (perm.map fun i ↦
      zhs.getD (i % period) 0 * invFirst.getD i 0)
    last := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields (perm.map fun i ↦
      zhs.getD (i % period) 0 * invLast.getD i 0)
    trans := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields (perm.map fun i ↦
      xs.getD i 0 - gInv)
    contiguous := (Array.range (n / B)).map fun b ↦
      let n0 := next.getD (b * B) 0
      if n0 % B == 0 && (List.range B).all fun k ↦ next.getD (b * B + k) 0 == n0 + k then some n0
      else none }

/-- `quotientOfLde` on packed words with the shape's tables `T`. The trace on the quotient domain
is the extension's first rows, transposed in parallel pieces; constraints are evaluated in that
bit-reversed row order, every node one vectorized operation per block of rows, in parallel block
ranges, and the result is put in natural order. -/
def quotientWith [Mont32BaseField p] [Binomial4 p] (T : QuotientTables p) (A : Air F)
    (pis : List F) (ext : PMat) (alpha : EF) : Array EF := Id.run do
  let n := 2 ^ (T.degreeBits + T.logChunks)
  let w := ext.width
  let period := 2 ^ T.logChunks
  let perm := T.perm
  let parts := if n < 4096 then 1 else 16
  let R := n / parts
  let pieces := (Array.range parts).map fun k ↦ Task.spawn fun _ ↦
    CompPoly.CPolynomial.NTTFast.Packed.Native.transposeRows ext.words w (k * R) R
  let cols := pieces.foldl (fun acc t ↦ acc ++ t.get) ByteArray.empty
  let K := A.constraints.length
  let weights := (List.range K).map fun k ↦ (Ext.coeffs (Ext.pow alpha (K - 1 - k))).map (·.val)
  let B := T.B
  let blocks := n / B
  let byRow := parChunks blocks (min blocks 16) fun b0 nb ↦ Id.run do
    let mut out := Array.emptyWithCapacity (nb * B)
    for blk in [b0:b0 + nb] do
      let r0 := blk * B
      let z0 := CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords B
      let mut acc := #[z0, z0, z0, z0]
      for (c, wk) in A.constraints.zip weights do
        let v := evalWords cols w R B T.next T.contiguous pis T.first T.last T.trans r0 c
        acc := (acc.zip wk.toArray).map fun (a, x) ↦ Words.mulAddWords p a v x B
      for i in [0:B] do
        let z := T.invZh.getD (perm.getD (r0 + i) 0 % period) 0
        out := out.push (Ext4.smul z
          ⟨word acc[0]! i, word acc[1]! i, word acc[2]! i, word acc[3]! i⟩)
    return out
  return perm.map fun r ↦ byRow.getD r 0

/-- `quotientOfLde` on packed words. -/
def quotient [Mont32BaseField p] [Binomial4 p] (A : Air F) (pis : List F)
    (degreeBits logChunks : Nat) (ext : PMat) (alpha : EF) : Array EF :=
  quotientWith (quotientTables degreeBits logChunks) A pis ext alpha

/-- The column sums `∑_r m[r][j] · x_r / (z - x_r)` over the stored rows `r0, …, r0 + len - 1` of a
packed matrix of width `w`, for every point `z` of `zs`: per point four planes of `w` words. The
range is transposed once; each column is a dot product with each weight plane. -/
def weightedColumns [Mont32BaseField p] [Binomial4 p] (m : @& ByteArray) (w : Nat)
    (zs : @& Array EF) (xs : @& ByteArray) (r0 len : Nat) : Array ByteArray := Id.run do
  let cols := CompPoly.CPolynomial.NTTFast.Packed.Native.transposeRows m w r0 len
  let xr := slice xs r0 len
  let mut out := #[]
  for z in zs do
    let wt := (invDenoms z xr len).mulBase xr
    for pl in #[wt.c0, wt.c1, wt.c2, wt.c3] do
      let mut sums := CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords w
      for j in [0:w] do
        sums := CompPoly.CPolynomial.NTTFast.Packed.Native.write sums j
          (Words.dotAt p cols (j * len) pl len)
      out := out.push sums
  return out

/-- `openedAt` on packed words, at all points of a matrix: the barycentric weights `x / (z - x)` in
the stored bit-reversed row order, as planes by the norm, and the column sums over parallel row
ranges, each range transposed once for all points. -/
def openedAt [Mont32BaseField p] [Binomial4 p] (logBlowup : Nat) (m : PMat) (zs : List EF) :
    List (Array EF) :=
  let logH := Nat.log2 m.height - logBlowup
  let h := 2 ^ logH
  let w := m.width
  let xs := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields (cosetPointsBitRev (gen : F)
      logH)
  let parts := if h < 4096 then 1 else 16
  let size := h / parts
  let tasks := (Array.range parts).map fun k ↦ Task.spawn fun _ ↦
    weightedColumns m.words w zs.toArray xs (k * size)
      (if k + 1 = parts then h - k * size else size)
  let sums := tasks.foldl (fun acc t ↦ (acc.zip t.get).map fun (a, b) ↦ Words.addWords p a b w)
    (Array.replicate (4 * zs.length) (CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords w))
  zs.zipIdx.map fun (z, k) ↦
    let factor := Fri.cosetFactor logH gen z
    Array.ofFn (n := w) fun j ↦
      factor * ⟨word (sums.getD (4 * k) .empty) j, word (sums.getD (4 * k + 1) .empty) j,
        word (sums.getD (4 * k + 2) .empty) j, word (sums.getD (4 * k + 3) .empty) j⟩

/-- Rows `r0, …, r0 + len - 1` of a packed matrix of width `w` batched by the powers of `α`, given
as four coordinate planes `a0, …, a3`: four planes of `len` words. -/
def compressRange (p : ℕ) [Mont32Field p] (m : @& ByteArray) (w : Nat)
    (a0 a1 a2 a3 : @& ByteArray) (r0 len : Nat) : Array ByteArray := Id.run do
  -- The range transposed, column `j` at words `j * len`: every plane is a sum of columns times
  -- scalars, in place.
  let cols := CompPoly.CPolynomial.NTTFast.Packed.Native.transposeRows m w r0 len
  let z := CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords len
  let mut p0 := z
  let mut p1 := z
  let mut p2 := z
  let mut p3 := z
  for j in [0:w] do
    let read := CompPoly.CPolynomial.NTTFast.Packed.Native.read
    p0 := Words.mulAddInto p p0 cols (j * len) (read a0 j) len
    p1 := Words.mulAddInto p p1 cols (j * len) (read a1 j) len
    p2 := Words.mulAddInto p p2 cols (j * len) (read a2 j) len
    p3 := Words.mulAddInto p p3 cols (j * len) (read a3 j) len
  return #[p0, p1, p2, p3]

/-- Concatenate parallel pieces of planes. -/
def joinPlanes (p : ℕ) (n : Nat) (pieces : Array (Task (Array ByteArray))) : EVec p :=
  let cat (j : Nat) := pieces.foldl (fun acc t ↦ acc ++ t.get.getD j .empty) ByteArray.empty
  ⟨n, cat 0, cat 1, cat 2, cat 3⟩

/-- Every row of a packed matrix batched by the powers `ap` of `α`, in parallel row ranges. -/
def compressPlanes (m : PMat) (ap : Array EF) : EVec p :=
  let a := EVec.ofArray ap
  let n := m.height
  let parts := if n < 4096 then 1 else 16
  let size := n / parts
  joinPlanes p n <| (Array.range parts).map fun k ↦ Task.spawn fun _ ↦
    compressRange p m.words m.width a.c0 a.c1 a.c2 a.c3 (k * size)
      (if k + 1 = parts then n - k * size else size)

/-- Rows `r0, …, r0 + len - 1` of the batched quotient of one height: for every matrix, its rows
batched by the planes `a` of the powers of `α`, and for every point `(z, yz, offset)` the term
`offset · (yz - comp) / (z - x)`, `xs` the height's points. -/
def reduceRange [Mont32BaseField p] [Binomial4 p]
    (items : @& Array (ByteArray × Nat × EVec p × List (EF × EF × EF))) (xs : @& ByteArray)
    (r0 len : Nat) : EVec p := Id.run do
  let xr := slice xs r0 len
  let mut acc := EVec.zeros len
  -- `1 / (z - x)` once per distinct point.
  let mut invs : List (EF × EVec p) := []
  for (words, w, a, pts) in items do
    let comp := compressRange p words w a.c0 a.c1 a.c2 a.c3 r0 len
    let comp : EVec p := ⟨len, comp.getD 0 .empty, comp.getD 1 .empty, comp.getD 2 .empty,
      comp.getD 3 .empty⟩
    for (z, yz, offset) in pts do
      let inv ← match invs.lookup z with
        | some v => pure v
        | none => do
          let v := invDenoms z xr len
          invs := (z, v) :: invs
          pure v
      acc := acc.add (((EVec.rsub yz comp).mul inv).smul offset)
  return acc

/-- `Fri.reduce` on planes, every height in parallel row ranges: rows batched by word dot
products, `1 / (z - x)` by the norm. -/
def reduce [Mont32BaseField p] [Binomial4 p] (alpha : EF) (items : List (PMat × List (EF × Array
    EF))) :
    List (Nat × EVec p) :=
  Id.run do
  -- Per height: the matrices with their points, opened sums and powers of `α`, in order.
  let mut groups : List (Nat × Nat × Array (ByteArray × Nat × EVec p × List (EF × EF × EF))) := []
  for (m, pts) in items do
    let logH := Nat.log2 m.height
    let (cnt, g) := (groups.lookup logH).getD (0, #[])
    let ap := Array.ofFn (n := m.width) fun i ↦ Ext.pow alpha i.val
    let mut cnt := cnt
    let mut terms := []
    for (z, ys) in pts do
      let yz := (List.range m.width).foldl (fun s i ↦ s + ap.getD i 0 * ys.getD i 0) 0
      terms := terms ++ [(z, yz, Ext.pow alpha cnt)]
      cnt := cnt + m.width
    groups := (logH, cnt, g.push (m.words, m.width, EVec.ofArray ap, terms)) ::
      groups.filter (·.1 != logH)
  let out := groups.map fun (logH, _, g) ↦
    let n := 2 ^ logH
    let xs := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields (cosetPointsBitRev (gen : F)
        logH)
    let parts := if n < 4096 then 1 else 16
    let size := n / parts
    let ts := (Array.range parts).map fun k ↦ Task.spawn fun _ ↦
      let v := reduceRange g xs (k * size) (if k + 1 = parts then n - k * size else size)
      #[v.c0, v.c1, v.c2, v.c3]
    (logH, joinPlanes p n ts)
  return out.mergeSort fun a b ↦ b.1 ≤ a.1

/-- Words `0, 2, 4, …` and `1, 3, 5, …` of the first `2 n` words of `b`. -/
def deinterleave (b : @& ByteArray) (n : Nat) : ByteArray × ByteArray := Id.run do
  let mut e := CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords n
  let mut o := CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords n
  for i in [0:n] do
    e := CompPoly.CPolynomial.NTTFast.Packed.Native.write e i
      (CompPoly.CPolynomial.NTTFast.Packed.Native.read b (2 * i))
    o := CompPoly.CPolynomial.NTTFast.Packed.Native.write o i
      (CompPoly.CPolynomial.NTTFast.Packed.Native.read b (2 * i + 1))
  return (e, o)

/-- Pairs `r0, …, r0 + len - 1` of the arity-2 fold of planes `v` at `β`; `twoX` holds `2 x` of
every pair. -/
def fold2Range [Mont32BaseField p] [Binomial4 p] (v : @& EVec p) (twoX : @& ByteArray) (beta : EF)
    (r0 len : Nat) :
    EVec p :=
  let split (b : ByteArray) := deinterleave (slice b (2 * r0) (2 * len)) len
  let (l0, h0) := split v.c0
  let (l1, h1) := split v.c1
  let (l2, h2) := split v.c2
  let (l3, h3) := split v.c3
  let lo : EVec p := ⟨len, l0, l1, l2, l3⟩
  let hi : EVec p := ⟨len, h0, h1, h2, h3⟩
  let inv2x := batchInvRange p twoX r0 len
  ((lo.add hi).smul (Ext.ofBase (2 : F)⁻¹)).add (((lo.sub hi).mulBase inv2x).smul beta)

/-- `Fri.foldPairs` on planes, `(lo + hi) / 2 + β (lo - hi) / (2 x)`, in parallel ranges. -/
def fold2 [Mont32BaseField p] [Binomial4 p] (v : EVec p) (beta : EF) (logRows : Nat) : EVec p :=
  let rows := 2 ^ logRows
  let pw := cosetPoints (1 : F) (logRows + 1)
  let twoX := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields
    ((bitRevPerm logRows).map fun i ↦ 2 * pw.getD i 0)
  let parts := if rows < 4096 then 1 else 16
  let size := rows / parts
  joinPlanes p rows <| (Array.range parts).map fun k ↦ Task.spawn fun _ ↦
    let f := fold2Range v twoX beta (k * size) (if k + 1 = parts then rows - k * size else size)
    #[f.c0, f.c1, f.c2, f.c3]

/-- The coordinates of elements `i0, …, i0 + len - 1` of planes, interleaved. -/
def interleaveRange (a0 a1 a2 a3 : @& ByteArray) (i0 len : Nat) : ByteArray := Id.run do
  let mut out := CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords (4 * len)
  for k in [0:len] do
    let i := i0 + k
    out := CompPoly.CPolynomial.NTTFast.Packed.Native.write out (4 * k)
      (CompPoly.CPolynomial.NTTFast.Packed.Native.read a0 i)
    out := CompPoly.CPolynomial.NTTFast.Packed.Native.write out (4 * k + 1)
      (CompPoly.CPolynomial.NTTFast.Packed.Native.read a1 i)
    out := CompPoly.CPolynomial.NTTFast.Packed.Native.write out (4 * k + 2)
      (CompPoly.CPolynomial.NTTFast.Packed.Native.read a2 i)
    out := CompPoly.CPolynomial.NTTFast.Packed.Native.write out (4 * k + 3)
      (CompPoly.CPolynomial.NTTFast.Packed.Native.read a3 i)
  return out

/-- The matrix of rows of `k` elements, flattened, packed in parallel ranges. -/
def leaves (k : Nat) (v : EVec p) : PMat :=
  let n := v.n
  let parts := if n < 4096 then 1 else 16
  let size := n / parts
  let ts := (Array.range parts).map fun p ↦ Task.spawn fun _ ↦
    interleaveRange v.c0 v.c1 v.c2 v.c3 (p * size) (if p + 1 = parts then n - p * size else size)
  { width := 4 * k, height := n / k, words := ts.foldl (fun acc t ↦ acc ++ t.get) .empty }

/-- `a + x · b`. -/
def addScaled [Binomial4 p] (a b : EVec p) (x : EF) : EVec p := a.add (b.smul x)

variable [Mont32BaseField p] [Binomial4 p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p]
    [PackedCosetLde p]

/-- The fast backend. -/
def backend : Backend F EF 24 where
  transcript := transcript
  M := PMat
  C := Commit
  lde := lde
  commit := commit p
  root := Commit.root
  openAt := Commit.openAt
  logHeight c := Nat.log2 c.maxHeight
  quotient := quotient
  openedAt := openedAt
  V := EVec p
  toArray := EVec.toArray
  ofArray := EVec.ofArray
  size := (·.n)
  reduce := reduce
  fold2 := fold2
  addScaled := addScaled
  leaves := leaves

/-- The fast backend with the extension plans and quotient tables of a proof of a `2 ^ logN`-row
trace and `2 ^ logChunks` quotient chunks prepared: the trace's extension on `g · ⟨ω_N⟩` and every
chunk's. -/
def backendFor (logN logBlowup logChunks : Nat) : Backend F EF 24 :=
  let T := quotientTables logN logChunks
  { backend with
    lde := ldeWith (ldePlans logN logBlowup logChunks)
    quotient := fun A pis db lc ext alpha ↦
      if db == logN && lc == logChunks then quotientWith T A pis ext alpha
      else quotient A pis db lc ext alpha }

end CompStark.Stark.Fast
