/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Poseidon2.Packed24
public import CompStark.Poseidon2.PackedField
public import CompPoly.Data.Tasks
import CompStark.Poseidon2.Unrolled

/-! # Packed Merkle commitments

Plonky3's Poseidon2 Merkle tree over a matrix of Montgomery words, eight digests at a time, on the
packed permutations of a `PackedPoseidon2` field:

* Leaves: eight consecutive rows share one width-24 group, one row per lane. Every block of up
  to sixteen columns overwrites the rate coordinates of the lanes, then the group is permuted;
  coordinates `0, …, 7` of a lane are its row's digest.
* Layers: eight consecutive pairs of digests share one width-16 group, the left digest in
  coordinates `0, …, 7` and the right in `8, …, 15`; the first eight coordinates after the
  permutation are the parent digests.

Digest `k` of a layer is words `8 k, …, 8 k + 7` of a `ByteArray`. Rows come in chunks, as the
coset LDE returns them; tasks hash the chunks, and the larger layers in ranges.
-/

@[expose] public section
namespace CompStark.Merkle.Packed
open CompStark.Poseidon2 CompStark.Poseidon2.Packed Montgomery.Native32
open CompPoly.CPolynomial.NTTFast.Packed.Native (read write zeroWords readUOffset putWords
  size_putWords wordOffset_toNat)

/-- Eight words stored at word `p`, as a `store8` at offset `0`. -/
theorem storeAt {b : ByteArray} {p : USize} (h : Fits b p 7) :
    ((p + 0) * 4).toNat + 4 * 8 ≤ b.size ∧ ((p + 0) * 4).toNat + 4 * 8 < USize.size := by
  rw [wordOffset_toNat _ _ (by simp only [USize.reduceToNat]; omega)]
  simp only [USize.reduceToNat]
  omega

set_option maxRecDepth 16384 in
/-- Lines `q0, …, q7` of sixteen words of `m` into coordinates `0, …, 15` of the width-24 group
at `i`. -/
@[noinline] def load16x24 (m : @& ByteArray) (q0 q1 q2 q3 q4 q5 q6 q7 : USize) (b : ByteArray)
    (i : USize) (h0 : Fits m q0 15) (h1 : Fits m q1 15) (h2 : Fits m q2 15) (h3 : Fits m q3 15)
    (h4 : Fits m q4 15) (h5 : Fits m q5 15) (h6 : Fits m q6 15) (h7 : Fits m q7 15)
    (hb : GroupFits24 b i) : ByteArray :=
  p2_load16% 24

set_option maxRecDepth 16384 in
/-- Lines `q0, …, q7` of sixteen words of `m` into coordinates `0, …, 15` of the width-16 group
at `i`. -/
@[noinline] def load16x16 (m : @& ByteArray) (q0 q1 q2 q3 q4 q5 q6 q7 : USize) (b : ByteArray)
    (i : USize) (h0 : Fits m q0 15) (h1 : Fits m q1 15) (h2 : Fits m q2 15) (h3 : Fits m q3 15)
    (h4 : Fits m q4 15) (h5 : Fits m q5 15) (h6 : Fits m q6 15) (h7 : Fits m q7 15)
    (hb : GroupFits b i) : ByteArray :=
  p2_load16% 16

set_option maxRecDepth 16384 in
/-- Coordinates `0, …, 7` of the eight lanes of the group at `i`, as digests at words
`p0, …, p7` of `out`. -/
@[noinline] def store8x8 (st : @& ByteArray) (i : USize) (out : ByteArray)
    (p0 p1 p2 p3 p4 p5 p6 p7 : USize) (hb : Fits st i 63) (g0 : Fits out p0 7)
    (g1 : Fits out p1 7) (g2 : Fits out p2 7) (g3 : Fits out p3 7) (g4 : Fits out p4 7)
    (g5 : Fits out p5 7) (g6 : Fits out p6 7) (g7 : Fits out p7 7) : ByteArray :=
  p2_store8x8%

/-- Words `q l, …, q l + 15`, `l < 8`, of `m` into coordinates `0, …, 15` of the width-24 group
at word `0` of `st`, if they fit. -/
def loadLines24 (m : @& ByteArray) (q : Nat → Nat) (st : ByteArray) : ByteArray :=
  let u (l : Nat) : USize := (q l).toUSize
  if h : Fits m (u 0) 15 ∧ Fits m (u 1) 15 ∧ Fits m (u 2) 15 ∧ Fits m (u 3) 15 ∧
      Fits m (u 4) 15 ∧ Fits m (u 5) 15 ∧ Fits m (u 6) 15 ∧ Fits m (u 7) 15 ∧ GroupFits24 st 0 then
    load16x24 m (u 0) (u 1) (u 2) (u 3) (u 4) (u 5) (u 6) (u 7) st 0 h.1 h.2.1 h.2.2.1
      h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2
  else st

/-- Words `q l, …, q l + 15`, `l < 8`, of `m` into coordinates `0, …, 15` of the width-16 group
at word `0` of `st`, if they fit. -/
def loadLines16 (m : @& ByteArray) (q : Nat → Nat) (st : ByteArray) : ByteArray :=
  let u (l : Nat) : USize := (q l).toUSize
  if h : Fits m (u 0) 15 ∧ Fits m (u 1) 15 ∧ Fits m (u 2) 15 ∧ Fits m (u 3) 15 ∧
      Fits m (u 4) 15 ∧ Fits m (u 5) 15 ∧ Fits m (u 6) 15 ∧ Fits m (u 7) 15 ∧ GroupFits st 0 then
    load16x16 m (u 0) (u 1) (u 2) (u 3) (u 4) (u 5) (u 6) (u 7) st 0 h.1 h.2.1 h.2.2.1
      h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2
  else st

/-- The digests in coordinates `0, …, 7` of the eight lanes of `st` as digests `d, …, d + 7`
of `out`, if they fit. -/
def storeDigests (st : @& ByteArray) (out : ByteArray) (d : Nat) : ByteArray :=
  let u (l : Nat) : USize := (8 * (d + l)).toUSize
  if h : Fits st 0 63 ∧ Fits out (u 0) 7 ∧ Fits out (u 1) 7 ∧ Fits out (u 2) 7 ∧
      Fits out (u 3) 7 ∧ Fits out (u 4) 7 ∧ Fits out (u 5) 7 ∧ Fits out (u 6) 7 ∧
      Fits out (u 7) 7 then
    store8x8 st 0 out (u 0) (u 1) (u 2) (u 3) (u 4) (u 5) (u 6) (u 7) h.1 h.2.1 h.2.2.1
      h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2
  else out

/-- Block `blk` of the rows `r0, …, r0 + 7` of the row-major words `m` of width `w` into
coordinates `0, …, 15` of the lanes of the group at word `0` of `st`, word by word: column
`16 blk + j` of row `r0 + l` becomes coordinate `j` of lane `l`, for rows below `rows` and columns
below `w`. -/
@[inline] def scatterRows (m : @& ByteArray) (w rows r0 blk : Nat) (st : ByteArray) :
    ByteArray := Id.run do
  let mut st := st
  for l in [:8] do
    if r0 + l < rows then
      for j in [:min 16 (w - 16 * blk)] do
        st := write st (8 * j + l) (read m ((r0 + l) * w + 16 * blk + j))
  return st

/-- `scatterRows` into a width-24 group, by the load kernel for full blocks of eight rows. -/
@[inline] def absorbBlock (m : @& ByteArray) (w rows r0 blk : Nat) (st : ByteArray) :
    ByteArray :=
  if r0 + 8 ≤ rows ∧ min 16 (w - 16 * blk) = 16 then
    loadLines24 m (fun l ↦ (r0 + l) * w + 16 * blk) st
  else scatterRows m w rows r0 blk st

/-- The width-24 group absorbing the rows `r0, …, r0 + 7` of the row-major words `m` of width
`w`, one lane per row. -/
@[inline] def absorbRows (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p]
    (m : @& ByteArray)
    (w rows r0 : Nat) : ByteArray :=
  (List.range ((w + 15) / 16)).foldl (fun st blk ↦
    PackedPoseidon2.permute24 p (absorbBlock m w rows r0 blk st)) (zeroWords 192)

/-- The digests in coordinates `0, …, 7` of the lanes of `st` as digests `r0, …, r0 + 7` of
`out`, for rows below `rows`. -/
@[inline] def storeRows (st : @& ByteArray) (rows r0 : Nat) (out : ByteArray) : ByteArray :=
  Id.run do
  if r0 + 8 ≤ rows then return storeDigests st out r0
  let mut out := out
  for l in [:8] do
    if r0 + l < rows then
      for j in [:8] do
        out := write out (8 * (r0 + l) + j) (read st (8 * j + l))
  return out

/-- The digests of the eight rows `r0, …, r0 + 7` of the row-major words `m` of width `w`, as
digests `r0, …, r0 + 7` of `out`; rows past `rows` read as zeros and are not stored. -/
@[specialize] def hashRows8 (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2
    p] (m : @& ByteArray)
    (w rows r0 : Nat) (out : ByteArray) : ByteArray :=
  storeRows (absorbRows p m w rows r0) rows r0 out

/-- The leaf digests of a chunk of `rows` rows of width `w`. -/
@[specialize] def hashChunk (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2
    p] (m : @& ByteArray)
    (w rows : Nat) : ByteArray :=
  (List.range ((rows + 7) / 8)).foldl (fun out g ↦ hashRows8 p m w rows (8 * g) out)
    (zeroWords (8 * rows))

/-- The pairs `o, …, o + 7` of the layer `prev` of `n` digests into the lanes of a width-16
group; pairs past `n / 2` read zeros. -/
@[inline] def loadPairs (prev : @& ByteArray) (n o : Nat) : ByteArray :=
  if o + 8 ≤ n / 2 then loadLines16 prev (fun l ↦ (o + l) * 16 + 16 * 0) (zeroWords 128)
  else scatterRows prev 16 (n / 2) o 0 (zeroWords 128)

/-- Parents `o, …, o + 7` of the layer `prev` of `n` digests as digests `o - o0, …` of `out`;
parents past `o0 + count` are not stored. -/
@[specialize] def compress8 (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2
    p] (prev : @& ByteArray)
    (n o o0 count : Nat) (out : ByteArray) : ByteArray :=
  storeRows (PackedPoseidon2.permute16 p (loadPairs prev n o)) count (o - o0) out

/-- Parents `o0, …, o0 + count - 1` of the layer `prev` of `n` digests. -/
@[specialize] def compressRange (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)]
    [PackedPoseidon2 p]
    (prev : @& ByteArray) (n o0 count : Nat) : ByteArray :=
  (List.range ((count + 7) / 8)).foldl (fun out g ↦ compress8 p prev n (o0 + 8 * g) o0 count out)
    (zeroWords (8 * count))

/-- `n` digests padded with zero digests to `padded`. -/
def padDigests (d : ByteArray) (n padded : Nat) : ByteArray :=
  d ++ zeroWords (8 * (padded - n))

/-- The next layer of a layer of `n` digests, padded to even length unless it is the root;
large layers are compressed by parallel range tasks. -/
@[specialize] def nextLayer (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2
    p] (prev : ByteArray)
    (n : Nat) : ByteArray × Nat :=
  let half := n / 2
  let padded := if n = 2 then 1 else (half + 1) / 2 * 2
  let parts := if half < 64 then 1 else min 16 (half / 32)
  let size := (half + parts - 1) / parts
  let tasks := CompPoly.Tasks.spawnAll parts fun k ↦
    compressRange p prev n (k * size) (min size (half - min half (k * size)))
  let out := tasks.foldl (fun acc t ↦ acc ++ t.get) (ByteArray.emptyWithCapacity (32 * padded))
  (padDigests out half padded, padded)

/-- The leaf digests of a matrix of width `w` given as `chunks` of rows, hashed by parallel
tasks, and the number of rows. -/
@[noinline, specialize] def leaves (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)]
    [PackedPoseidon2 p] (w : Nat)
    (chunks : Array ByteArray) : ByteArray × Nat :=
  let rowsOf (c : ByteArray) := if w = 0 then 0 else c.size / (4 * w)
  let tasks := CompPoly.Tasks.join (chunks.map fun c ↦ Task.spawn fun _ ↦
    hashChunk p c w (rowsOf c))
  let h := chunks.foldl (fun acc c ↦ acc + rowsOf c) 0
  (tasks.get.foldl (· ++ ·) (ByteArray.emptyWithCapacity (32 * (h + 1))), h)

/-- The root above the first layer of `h` leaf digests. -/
@[noinline, specialize] def rootOfLeaves (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)]
    [PackedPoseidon2 p] (first : ByteArray)
    (h : Nat) : ByteArray :=
  let padded := if h = 1 then 1 else h + h % 2
  ((List.range 64).foldl (fun (acc : ByteArray × Nat) _ ↦
      if acc.2 ≤ 1 then acc else nextLayer p acc.1 acc.2)
    (padDigests first h padded, padded)).1

/-- The root of the Merkle tree of a single matrix of width `w`, given as `chunks` of rows. -/
@[specialize] def root (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p]
    (w : Nat)
    (chunks : Array ByteArray) : ByteArray :=
  let (first, h) := leaves p w chunks
  rootOfLeaves p first h

end CompStark.Merkle.Packed
