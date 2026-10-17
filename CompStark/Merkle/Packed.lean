/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Poseidon2.Packed24
public import CompPoly.Data.Tasks

/-! # Packed Merkle commitments

Plonky3's Poseidon2 Merkle tree over a matrix of Montgomery words, eight digests at a time:

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
open CompStark.Poseidon2.Packed
open CompPoly.CPolynomial.NTTFast.Packed.Native (read write zeroWords)

/-- The digests of the eight rows `r0, …, r0 + 7` of the row-major words `m` of width `w`,
rows past `rows` reading as zeros. -/
def hashRows8 (K : @& Packed24) (m : @& ByteArray) (w rows r0 : Nat) : ByteArray := Id.run do
  let mut st := zeroWords 192
  for blk in [:(w + 15) / 16] do
    let cnt := min 16 (w - 16 * blk)
    for l in [:8] do
      if r0 + l < rows then
        for j in [:cnt] do
          st := write st (8 * j + l) (read m ((r0 + l) * w + 16 * blk + j))
    st := permute24 K st 0
  let mut out := zeroWords 64
  for l in [:8] do
    for j in [:8] do
      out := write out (8 * l + j) (read st (8 * j + l))
  return out

/-- The leaf digests of a chunk of `rows` rows of width `w`. -/
def hashChunk (K : @& Packed24) (m : @& ByteArray) (w rows : Nat) : ByteArray :=
  (List.range ((rows + 7) / 8)).foldl (fun acc g ↦
    let d := hashRows8 K m w rows (8 * g)
    acc ++ d.extract 0 (4 * 8 * min 8 (rows - 8 * g)))
    (ByteArray.emptyWithCapacity (32 * rows))

/-- Parents `o, …, o + 7` of the layer `prev` of `n` digests; pairs past `n / 2` read zeros. -/
def compress8 (K : @& Packed16) (prev : @& ByteArray) (n o : Nat) : ByteArray := Id.run do
  let mut st := zeroWords 128
  for l in [:8] do
    if o + l < n / 2 then
      for j in [:8] do
        st := write st (8 * j + l) (read prev (8 * (2 * (o + l)) + j))
        st := write st (8 * (8 + j) + l) (read prev (8 * (2 * (o + l) + 1) + j))
  st := permute16 K st 0
  let mut out := zeroWords 64
  for l in [:8] do
    for j in [:8] do
      out := write out (8 * l + j) (read st (8 * j + l))
  return out

/-- Parents `o, …, o + count - 1` of the layer `prev` of `n` digests. -/
def compressRange (K : @& Packed16) (prev : @& ByteArray) (n o count : Nat) : ByteArray :=
  (List.range ((count + 7) / 8)).foldl (fun acc g ↦
    let d := compress8 K prev n (o + 8 * g)
    acc ++ d.extract 0 (4 * 8 * min 8 (count - 8 * g)))
    (ByteArray.emptyWithCapacity (32 * count))

/-- `n` digests padded with zero digests to `padded`. -/
def padDigests (d : ByteArray) (n padded : Nat) : ByteArray :=
  d ++ zeroWords (8 * (padded - n))

/-- The next layer of a layer of `n` digests, padded to even length unless it is the root;
large layers are compressed by parallel range tasks. -/
def nextLayer (K : Packed16) (prev : ByteArray) (n : Nat) : ByteArray × Nat :=
  let half := n / 2
  let padded := if n = 2 then 1 else (half + 1) / 2 * 2
  let parts := if half < 4096 then 1 else 16
  let size := (half + parts - 1) / parts
  let tasks := CompPoly.Tasks.spawnAll parts fun k ↦
    compressRange K prev n (k * size) (min size (half - min half (k * size)))
  let out := tasks.foldl (fun acc t ↦ acc ++ t.get) (ByteArray.emptyWithCapacity (32 * padded))
  (padDigests out half padded, padded)

/-- The root of the Merkle tree of a single matrix of width `w`, given as `chunks` of rows. -/
def root (K24 : Packed24) (K16 : Packed16) (w : Nat) (chunks : Array ByteArray) : ByteArray :=
  let rowsOf (c : ByteArray) := if w = 0 then 0 else c.size / (4 * w)
  let leaves := CompPoly.Tasks.join (chunks.map fun c ↦ Task.spawn fun _ ↦ hashChunk K24 c w (rowsOf c))
  let h := chunks.foldl (fun acc c ↦ acc + rowsOf c) 0
  let first := leaves.get.foldl (· ++ ·) (ByteArray.emptyWithCapacity (32 * (h + 1)))
  let padded := if h = 1 then 1 else h + h % 2
  let go := fun (fuel : Nat) (layer : ByteArray) (n : Nat) ↦
    (List.range fuel).foldl (fun (acc : ByteArray × Nat) _ ↦
      if acc.2 ≤ 1 then acc else nextLayer K16 acc.1 acc.2) (layer, n)
  (go 64 (padDigests first h padded) padded).1

end CompStark.Merkle.Packed
