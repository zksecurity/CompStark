/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Prover
public import CompStark.Merkle.Packed
public import CompPoly.Univariate.NTTFast.Packed.CosetLde
public import CompPoly.Univariate.NTT.KoalaBear
public import CompStark.Stark.Words
public import CompStark.Stark.ExtWords

/-! # The fast prover backend

The kernels of `Backend` on packed Montgomery words:

* The transcript permutes with the packed width-24 Poseidon2, the state in lane 0 of a group.
  Grinding tries eight candidates per packed permutation, as Plonky3 does, and returns the
  smallest that passes.
* Low-degree extension is CompPoly's batched coset LDE.
* The Merkle digest layers of matrices of one height come from the packed Merkle commitment, on
  their rows side by side; other shapes fall back to the specification.
-/

@[expose] public section
namespace CompStark.Stark.Fast
open CompStark.Fri CompStark.KoalaBear CompStark.Poseidon2.Packed

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4

/-- The packed constants of the width-24 permutation. -/
def K24 : Packed24 := Packed24.ofParams (Poseidon2.KoalaBear.width24 F)

/-- The packed constants of the width-16 permutation. -/
def K16 : Packed16 := Packed16.ofParams (Poseidon2.KoalaBear.width16 F)

/-- A field element from a packed word. -/
def word (b : ByteArray) (i : Nat) : F :=
  CompPoly.CPolynomial.NTTFast.Packed.ofWord (CompPoly.CPolynomial.NTTFast.Packed.Native.read b i)

/-- Words `s, …, s + len - 1` of `b` as field elements. The buffer is borrowed, so parallel
ranges share it without touching its reference count per word. -/
def decodeRange (b : @& ByteArray) (s len : Nat) : Array F := Id.run do
  let mut out := Array.emptyWithCapacity len
  for i in [s:s + len] do
    out := out.push (word b i)
  return out

/-- The first `n` words of `b` as field elements, decoded by parallel ranges. -/
def decodeAll (b : ByteArray) (n : Nat) : Array F :=
  parChunks n (if n < 4096 then 1 else 16) fun s len ↦ decodeRange b s len

/-- The width-24 permutation of one state, in lane 0 of a packed group. -/
def perm24 (s : Vector F 24) : Vector F 24 :=
  let W : Array F := Array.ofFn (n := 192) fun k ↦
    if k.val % 8 = 0 then s.toArray.getD (k / 8) 0 else 0
  let out := permute24 K24 (CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields W) 0
  Vector.ofFn fun j ↦ word out (8 * j.val)

/-- The transcript's duplex on the packed permutation. -/
def duplex : Duplex F 24 := { KoalaBear.duplex with perm := perm24 }

/-- The first candidate of `8 b, …, 8 b + 7` that passes, from batch `b` on: the duplexed
states with the candidates in the witness's coordinate `wi` are permuted as one packed group. -/
def grindFrom (base : Vector F 24) (wi bits : Nat) : Nat → Nat → F
  | 0, _ => 0
  | fuel + 1, b =>
    let W : Array F := Array.ofFn (n := 192) fun k ↦
      let j := k.val / 8
      if j = wi then ((8 * b + k.val % 8 : Nat) : F) else base.toArray.getD j 0
    let out := permute24 K24 (CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields W) 0
    let pass (l : Nat) := 8 * b + l < _root_.KoalaBear.fieldSize &&
      (Montgomery.Native32.FastField.toNat (word out (8 * 15 + l))) % 2 ^ bits == 0
    match (List.range 8).find? pass with
    | some l => ((8 * b + l : Nat) : F)
    | none => grindFrom base wi bits fuel (b + 1)

/-- The first passing candidate of the batches `b0, …, b0 + nb - 1`, if any. `group` is the packed
group of eight copies of the duplexed state; each batch writes its candidates into coordinate
`wi`. -/
def grindRange (group : @& ByteArray) (wi bits b0 nb : Nat) : Option Nat := Id.run do
  for b in [b0:b0 + nb] do
    let mut W := group.copySlice 0 ByteArray.empty 0 group.size
    for l in [0:8] do
      W := CompPoly.CPolynomial.NTTFast.Packed.Native.write W (8 * wi + l)
        ((8 * b + l : Nat) : F).val
    let out := permute24 K24 W 0
    for l in [0:8] do
      if 8 * b + l < _root_.KoalaBear.fieldSize &&
          (Montgomery.Native32.FastField.toNat (word out (8 * 15 + l))) % 2 ^ bits == 0 then
        return some (8 * b + l)
  return none

/-- The smallest passing candidate from wave `wave` on: each wave splits 1024 batches of eight
candidates among 16 tasks, and the first wave with a passing candidate has the smallest. -/
def grindWaves (group : ByteArray) (wi bits : Nat) : Nat → Nat → F
  | 0, _ => 0
  | fuel + 1, wave =>
    let ts := (Array.range 16).map fun k ↦ Task.spawn fun _ ↦
      grindRange group wi bits (1024 * wave + 64 * k) 64
    match (ts.map Task.get).findSome? id with
    | some c => (c : F)
    | none => grindWaves group wi bits fuel (wave + 1)

/-- The smallest grinding witness for `bits`, eight candidates per packed permutation as Plonky3
grinds, in parallel waves. -/
def grind (c : Challenger F 24) (bits : Nat) : F :=
  let base := Hash.overwrite c.state c.input.toList
  let group := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields
    (Array.ofFn (n := 192) fun k ↦ base.toArray.getD (k / 8) 0)
  grindWaves group c.input.size bits (_root_.KoalaBear.fieldSize / 8192 + 1) 0

/-- The fast transcript. -/
def transcript : Transcript := Transcript.initWith duplex grind

/-- A matrix of packed rows. -/
def ofRows (w h : Nat) (vals : Array F) : Mat :=
  { width := w, height := h, words := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields vals }

/-- Row `r` of a packed matrix. -/
def row (m : Mat) (r : Nat) : Array F := decodeRange m.words (r * m.width) m.width

/-- CompPoly's plan for extensions of `2 ^ logH`-row matrices by `2 ^ bits` onto `shift · ⟨ω_N⟩`. -/
def plan? (logH bits : Nat) (shift : F) : Option CompPoly.CPolynomial.NTTFast.Packed.LdePlan :=
  if h : logH + bits ≤ 24 then
    let D := CompPoly.CPolynomial.NTT.KoalaBear.fastDomainOfLogN (logH + bits) h
    have h32 : D.logN ≤ 32 := by change logH + bits ≤ 32; omega
    have hu : 4 * D.n < USize.size := by
      have hp : 2 ^ (logH + bits) ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) h
      have := USize.le_size
      change 4 * 2 ^ (logH + bits) < USize.size
      omega
    some (CompPoly.CPolynomial.NTTFast.Packed.LdePlan.ofDomain D bits
      (by change bits ≤ logH + bits; omega) shift h32 hu)
  else none

/-- CompPoly's batched coset LDE, bit-reversed rows, packed: `ldeRef` on words. Plans come from
`plans` when one matches, else are built. -/
def ldeWith (plans : List (Nat × Nat × F × CompPoly.CPolynomial.NTTFast.Packed.LdePlan))
    (logH bits : Nat) (shift : F) (w : Nat) (m : Array F) : Mat :=
  let found := plans.find? fun (h, b, s, _) ↦ h == logH && b == bits && s == shift
  match found.map (·.2.2.2) <|> plan? logH bits shift with
  | some P =>
    let out := CompPoly.CPolynomial.NTTFast.Packed.Native.joinRows
      (CompPoly.CPolynomial.NTTFast.Packed.Native.cosetLde P w
        (CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields m))
    { width := w, height := 2 ^ (logH + bits), words := out }
  | none => ofRows w (2 ^ (logH + bits)) (ldeRef logH bits shift w m).values

/-- The extension without cached plans. -/
def lde (logH bits : Nat) (shift : F) (w : Nat) (m : Array F) : Mat :=
  ldeWith [] logH bits shift w m

/-- Digest `k` of a packed layer. -/
def digestAt (b : ByteArray) (k : Nat) : Digest := Vector.ofFn fun j ↦ word b (8 * k + j.val)

/-- The packed digest layers of the Merkle tree of one matrix of width `w` given as one chunk of
rows. -/
def packedLayers (w : Nat) (m : ByteArray) : Array ByteArray := Id.run do
  let h := if w = 0 then 0 else m.size / (4 * w)
  let parts := if h < 1024 then 1 else 16
  let rows := h / parts
  let chunks := (Array.range parts).map fun k ↦
    m.extract (4 * w * (k * rows)) (if k + 1 = parts then m.size else 4 * w * ((k + 1) * rows))
  let (first, h) := Merkle.Packed.leaves K24 w chunks
  let padded := if h = 1 then 1 else h + h % 2
  let mut layer := Merkle.Packed.padDigests first h padded
  let mut n := padded
  let mut out := #[layer]
  for _ in List.range 64 do
    if n ≤ 1 then break
    let (l, n') := Merkle.Packed.nextLayer K16 layer n
    layer := l
    n := n'
    out := out.push layer
  return out

/-- The rows of matrices of one height side by side, packed. -/
def sideBySide (ms : List Mat) (h : Nat) : ByteArray :=
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

/-- The Merkle digest layers: packed for matrices of one height, side by side; otherwise the
specification's. -/
def layers (ms : List Mat) : Layers :=
  match ms with
  | m :: rest =>
    if rest.all (·.height == m.height) && 0 < m.height then
      let ls := packedLayers (ms.foldl (· + ·.width) 0) (sideBySide ms m.height)
      ⟨ls.size, fun i k ↦ digestAt (ls.getD i ByteArray.empty) k⟩
    else Backend.spec.layers ms
  | [] => Backend.spec.layers ms

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
    (pis : List F) (first last trans : ByteArray) (r0 : Nat) : Expr → ByteArray
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
  | .add a b => Words.addWords (evalWords cols w R B next contiguous pis first last trans r0 a)
      (evalWords cols w R B next contiguous pis first last trans r0 b) B
  | .sub a b => Words.subWords (evalWords cols w R B next contiguous pis first last trans r0 a)
      (evalWords cols w R B next contiguous pis first last trans r0 b) B
  | .mul a b => Words.mulWords (evalWords cols w R B next contiguous pis first last trans r0 a)
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
structure QuotientTables where
  degreeBits : Nat
  logChunks : Nat
  perm : Array Nat
  invZh : Array F
  first : ByteArray
  last : ByteArray
  trans : ByteArray
  next : Array Nat
  B : Nat
  contiguous : Array (Option Nat)

/-- The quotient tables of a shape. -/
def quotientTables (degreeBits logChunks : Nat) : QuotientTables :=
  let qlog := degreeBits + logChunks
  let n := 2 ^ qlog
  let perm := bitRevPerm qlog
  let xs := cosetPoints gen qlog
  let gInv := (twoAdicGen degreeBits)⁻¹
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
def quotientWith (T : QuotientTables) (A : Air) (pis : List F) (ext : Mat) (alpha : EF) :
    Array EF := Id.run do
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
        acc := (acc.zip wk.toArray).map fun (a, x) ↦ Words.mulAddWords a v x B
      for i in [0:B] do
        let z := T.invZh.getD (perm.getD (r0 + i) 0 % period) 0
        out := out.push (KoalaBear.Fast.Ext4.smul z
          ⟨word acc[0]! i, word acc[1]! i, word acc[2]! i, word acc[3]! i⟩)
    return out
  return perm.map fun r ↦ byRow.getD r 0

/-- `quotientOfLde` on packed words. -/
def quotient (A : Air) (pis : List F) (degreeBits logChunks : Nat) (ext : Mat) (alpha : EF) :
    Array EF :=
  quotientWith (quotientTables degreeBits logChunks) A pis ext alpha

/-- Rows `i0, …, i0 + len - 1` (natural order, stored at `perm[i]`) of a packed matrix of width
`w`, accumulated with the extension weights `wt[i]`: four coordinate planes of `w` words. -/
def weightedRows (m : @& ByteArray) (w : Nat) (perm : @& Array Nat) (wt : @& EVec)
    (i0 len : Nat) : Array ByteArray := Id.run do
  let z := CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords w
  let mut p0 := z
  let mut p1 := z
  let mut p2 := z
  let mut p3 := z
  for i in [i0:i0 + len] do
    let r := perm.getD i 0 * w
    p0 := Words.mulAddInto p0 m r (CompPoly.CPolynomial.NTTFast.Packed.Native.read wt.c0 i) w
    p1 := Words.mulAddInto p1 m r (CompPoly.CPolynomial.NTTFast.Packed.Native.read wt.c1 i) w
    p2 := Words.mulAddInto p2 m r (CompPoly.CPolynomial.NTTFast.Packed.Native.read wt.c2 i) w
    p3 := Words.mulAddInto p3 m r (CompPoly.CPolynomial.NTTFast.Packed.Native.read wt.c3 i) w
  return #[p0, p1, p2, p3]

/-- `openedAt` on packed words: the barycentric weights `x / (z - x)` as planes, by the norm, and
the sums accumulated row by row in parallel ranges. -/
def openedAt (logBlowup : Nat) (m : Mat) (z : EF) : Array EF :=
  let logH := Nat.log2 m.height - logBlowup
  let h := 2 ^ logH
  let w := m.width
  let xs := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields (cosetPoints gen logH)
  let wt := (invDenoms z xs h).mulBase xs
  let factor := KoalaBear.Fast.cosetFactor logH gen z
  let perm := bitRevPerm logH
  let parts := if h < 4096 then 1 else 16
  let size := h / parts
  let tasks := (Array.range parts).map fun k ↦ Task.spawn fun _ ↦
    weightedRows m.words w perm wt (k * size) (if k + 1 = parts then h - k * size else size)
  let planes := tasks.foldl (fun acc t ↦ (acc.zip t.get).map fun (a, b) ↦ Words.addWords a b w)
    (Array.replicate 4 (CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords w))
  Array.ofFn (n := w) fun j ↦
    factor * ⟨word (planes.getD 0 .empty) j, word (planes.getD 1 .empty) j,
      word (planes.getD 2 .empty) j, word (planes.getD 3 .empty) j⟩

/-- Rows `r0, …, r0 + len - 1` of a packed matrix of width `w` batched by the powers of `α`, given
as four coordinate planes `a0, …, a3`: four planes of `len` words. -/
def compressRange (m : @& ByteArray) (w : Nat) (a0 a1 a2 a3 : @& ByteArray) (r0 len : Nat) :
    Array ByteArray := Id.run do
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
    p0 := Words.mulAddInto p0 cols (j * len) (read a0 j) len
    p1 := Words.mulAddInto p1 cols (j * len) (read a1 j) len
    p2 := Words.mulAddInto p2 cols (j * len) (read a2 j) len
    p3 := Words.mulAddInto p3 cols (j * len) (read a3 j) len
  return #[p0, p1, p2, p3]

/-- Concatenate parallel pieces of planes. -/
def joinPlanes (n : Nat) (pieces : Array (Task (Array ByteArray))) : EVec :=
  let cat (j : Nat) := pieces.foldl (fun acc t ↦ acc ++ t.get.getD j .empty) ByteArray.empty
  ⟨n, cat 0, cat 1, cat 2, cat 3⟩

/-- Every row of a packed matrix batched by the powers `ap` of `α`, in parallel row ranges. -/
def compressPlanes (m : Mat) (ap : Array EF) : EVec :=
  let a := EVec.ofArray ap
  let n := m.height
  let parts := if n < 4096 then 1 else 16
  let size := n / parts
  joinPlanes n <| (Array.range parts).map fun k ↦ Task.spawn fun _ ↦
    compressRange m.words m.width a.c0 a.c1 a.c2 a.c3 (k * size)
      (if k + 1 = parts then n - k * size else size)

/-- Rows `r0, …, r0 + len - 1` of the batched quotient of one height: for every matrix, its rows
batched by the planes `a` of the powers of `α`, and for every point `(z, yz, offset)` the term
`offset · (yz - comp) / (z - x)`, `xs` the height's points. -/
def reduceRange (items : @& Array (ByteArray × Nat × EVec × List (EF × EF × EF)))
    (xs : @& ByteArray) (r0 len : Nat) : EVec := Id.run do
  let xr := slice xs r0 len
  let mut acc := EVec.zeros len
  -- `1 / (z - x)` once per distinct point.
  let mut invs : List (EF × EVec) := []
  for (words, w, a, pts) in items do
    let comp := compressRange words w a.c0 a.c1 a.c2 a.c3 r0 len
    let comp : EVec := ⟨len, comp.getD 0 .empty, comp.getD 1 .empty, comp.getD 2 .empty,
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
def reduce (alpha : EF) (items : List (Mat × List (EF × Array EF))) : List (Nat × EVec) :=
  Id.run do
  -- Per height: the matrices with their points, opened sums and powers of `α`, in order.
  let mut groups : List (Nat × Nat × Array (ByteArray × Nat × EVec × List (EF × EF × EF))) := []
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
    let xs := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields (cosetPointsBitRev gen logH)
    let parts := if n < 4096 then 1 else 16
    let size := n / parts
    let ts := (Array.range parts).map fun k ↦ Task.spawn fun _ ↦
      let v := reduceRange g xs (k * size) (if k + 1 = parts then n - k * size else size)
      #[v.c0, v.c1, v.c2, v.c3]
    (logH, joinPlanes n ts)
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
def fold2Range (v : @& EVec) (twoX : @& ByteArray) (beta : EF) (r0 len : Nat) : EVec :=
  let split (b : ByteArray) := deinterleave (slice b (2 * r0) (2 * len)) len
  let (l0, h0) := split v.c0
  let (l1, h1) := split v.c1
  let (l2, h2) := split v.c2
  let (l3, h3) := split v.c3
  let lo : EVec := ⟨len, l0, l1, l2, l3⟩
  let hi : EVec := ⟨len, h0, h1, h2, h3⟩
  let inv2x := batchInvRange twoX r0 len
  ((lo.add hi).smul (Ext.ofBase (2 : F)⁻¹)).add (((lo.sub hi).mulBase inv2x).smul beta)

/-- `Fri.foldPairs` on planes, `(lo + hi) / 2 + β (lo - hi) / (2 x)`, in parallel ranges. -/
def fold2 (v : EVec) (beta : EF) (logRows : Nat) : EVec :=
  let rows := 2 ^ logRows
  let pw := cosetPoints 1 (logRows + 1)
  let twoX := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields
    ((bitRevPerm logRows).map fun i ↦ 2 * pw.getD i 0)
  let parts := if rows < 4096 then 1 else 16
  let size := rows / parts
  joinPlanes rows <| (Array.range parts).map fun k ↦ Task.spawn fun _ ↦
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
def leaves (k : Nat) (v : EVec) : Mat :=
  let n := v.n
  let parts := if n < 4096 then 1 else 16
  let size := n / parts
  let ts := (Array.range parts).map fun p ↦ Task.spawn fun _ ↦
    interleaveRange v.c0 v.c1 v.c2 v.c3 (p * size) (if p + 1 = parts then n - p * size else size)
  { width := 4 * k, height := n / k, words := ts.foldl (fun acc t ↦ acc ++ t.get) .empty }

/-- The fast backend. -/
def backend : Backend where
  transcript := transcript
  lde := lde
  ofRows := ofRows
  layers := layers
  row := row
  quotient := quotient
  openedAt := openedAt
  V := EVec
  toArray := EVec.toArray
  ofArray := EVec.ofArray
  size := (·.n)
  reduce := reduce
  fold2 := fold2
  addScaled a b x := a.add (b.smul x)
  leaves := leaves

/-- The fast backend with the extension plans and quotient tables of a proof of a `2 ^ logN`-row
trace and `2 ^ logChunks` quotient chunks prepared: the trace's extension on `g · ⟨ω_N⟩` and every
chunk's. -/
def backendFor (logN logBlowup logChunks : Nat) : Backend :=
  let qlog := logN + logChunks
  let shifts := gen :: (List.range (2 ^ logChunks)).map fun c ↦
    gen * (gen * powF (twoAdicGen qlog) c)⁻¹
  let plans := shifts.filterMap fun s ↦ (plan? logN logBlowup s).map fun P ↦ (logN, logBlowup, s, P)
  let T := quotientTables logN logChunks
  { backend with
    lde := ldeWith plans
    quotient := fun A pis db lc ext alpha ↦
      if db == logN && lc == logChunks then quotientWith T A pis ext alpha
      else quotient A pis db lc ext alpha }

end CompStark.Stark.Fast
