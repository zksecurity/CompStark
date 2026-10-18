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

/-- The smallest grinding witness for `bits`, eight candidates per packed permutation, as Plonky3
grinds. -/
def grind (c : Challenger F 24) (bits : Nat) : F :=
  grindFrom (Hash.overwrite c.state c.input.toList) c.input.size bits
    (_root_.KoalaBear.fieldSize / 8 + 1) 0

/-- The fast transcript. -/
def transcript : Transcript := Transcript.initWith duplex grind

/-- CompPoly's batched coset LDE, bit-reversed rows: `ldeRef` on packed words. -/
def lde (logH bits : Nat) (shift : F) (w : Nat) (m : Array F) : Mat :=
  if h : logH + bits ≤ 24 then
    let D := CompPoly.CPolynomial.NTT.KoalaBear.fastDomainOfLogN (logH + bits) h
    have h32 : D.logN ≤ 32 := by change logH + bits ≤ 32; omega
    have hu : 4 * D.n < USize.size := by
      have hp : 2 ^ (logH + bits) ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) h
      have := USize.le_size
      change 4 * 2 ^ (logH + bits) < USize.size
      omega
    let P := CompPoly.CPolynomial.NTTFast.Packed.LdePlan.ofDomain D bits
      (by change bits ≤ logH + bits; omega) shift h32 hu
    let out := CompPoly.CPolynomial.NTTFast.Packed.Native.joinRows
      (CompPoly.CPolynomial.NTTFast.Packed.Native.cosetLde P w
        (CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields m))
    ⟨w, 2 ^ (logH + bits), decodeAll out (2 ^ (logH + bits) * w)⟩
  else ldeRef logH bits shift w m

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
  | [m] => CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields m.values
  | _ => Id.run do
    let w := ms.foldl (· + ·.width) 0
    let mut out := Array.emptyWithCapacity (h * w)
    for r in [0:h] do
      for m in ms do
        for j in [0:m.width] do
          out := out.push (m.values.getD (r * m.width + j) 0)
    return CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields out

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

/-- The packed values of `e` on the rows `r0, …, r0 + B - 1` of the quotient domain of size `n`:
`evalBlock` on words, `cols` the trace's columns there and `first`, `last`, `trans` the
selectors. -/
def evalWords (cols : ByteArray) (n period B : Nat) (pis : List F)
    (first last trans : ByteArray) (r0 : Nat) : Expr → ByteArray
  | .cur c => slice cols (c * n + r0) B
  | .next c =>
    let s := (r0 + period) % n
    if s + B ≤ n then slice cols (c * n + s) B
    else slice cols (c * n + s) (n - s) ++ slice cols (c * n) (B - (n - s))
  | .pub j => Words.replicateWord (pis.getD j 0).val B
  | .const c => Words.replicateWord c.val B
  | .isFirstRow => slice first r0 B
  | .isLastRow => slice last r0 B
  | .isTransition => slice trans r0 B
  | .add a b => Words.addWords (evalWords cols n period B pis first last trans r0 a)
      (evalWords cols n period B pis first last trans r0 b) B
  | .sub a b => Words.subWords (evalWords cols n period B pis first last trans r0 a)
      (evalWords cols n period B pis first last trans r0 b) B
  | .mul a b => Words.mulWords (evalWords cols n period B pis first last trans r0 a)
      (evalWords cols n period B pis first last trans r0 b) B

/-- `quotientValues` on packed words: the trace transposed into columns, every node of a
constraint one vectorized operation per block of 256 rows. -/
def quotient (A : Air) (pis : List F) (degreeBits logChunks : Nat) (tq : Mat) (alpha : EF) :
    Array EF := Id.run do
  let qlog := degreeBits + logChunks
  let n := 2 ^ qlog
  let w := tq.width
  let xs := cosetPoints gen qlog
  let gInv := (twoAdicGen degreeBits)⁻¹
  let period := 2 ^ logChunks
  let zhs := Array.ofFn (n := period) fun k ↦ powF (xs.getD k 0) (2 ^ degreeBits) - 1
  let invZh := batchInv zhs
  let invFirst := batchInv (xs.map (· - 1))
  let invLast := batchInv (xs.map (· - gInv))
  let first := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields (Array.ofFn (n := n) fun i ↦
    zhs.getD (i.val % period) 0 * invFirst.getD i 0)
  let last := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields (Array.ofFn (n := n) fun i ↦
    zhs.getD (i.val % period) 0 * invLast.getD i 0)
  let trans := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields (xs.map (· - gInv))
  let cols := CompPoly.CPolynomial.NTTFast.Packed.Native.transposeRows
    (CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields tq.values) w 0 n
  let K := A.constraints.length
  let weights := (List.range K).map fun k ↦ (Ext.coeffs (Ext.pow alpha (K - 1 - k))).map (·.val)
  let B := min n 256
  let blocks := n / B
  parChunks blocks (min blocks 16) fun b0 nb ↦ Id.run do
  let mut out := Array.emptyWithCapacity (nb * B)
  for blk in [b0:b0 + nb] do
    let r0 := blk * B
    let z0 := CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords B
    let mut acc := #[z0, z0, z0, z0]
    for (c, wk) in A.constraints.zip weights do
      let v := evalWords cols n period B pis first last trans r0 c
      acc := (acc.zip wk.toArray).map fun (a, x) ↦ Words.mulAddWords a v x B
    for i in [0:B] do
      let z := invZh.getD ((r0 + i) % period) 0
      out := out.push (KoalaBear.Fast.Ext4.smul z
        ⟨word acc[0]! i, word acc[1]! i, word acc[2]! i, word acc[3]! i⟩)
  return out

/-- The fast backend. -/
def backend : Backend where
  transcript := transcript
  lde := lde
  layers := layers
  quotient := quotient

end CompStark.Stark.Fast
