/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Poseidon2.PackedCorrectness24
public import CompStark.Poseidon2.BabyBear
public import CompPoly.Fields.BabyBear.Fast
import CompStark.Poseidon2.Unrolled
import all CompStark.Poseidon2.Packed
import all CompStark.Poseidon2.PackedLanes
import all CompPoly.Univariate.NTTFast.Packed.Native

/-! # Packed Poseidon2 kernels over BabyBear

The round kernels generated for BabyBear's shape: the S-box `x ^ 7` and Plonky3's internal
diagonals of widths 16 and 24, whose entries after the ninth are `±2 ^ (-k)` with `k ≤ 27`. Each
kernel equals its model (`PackedKernels`), so `permute16` and `permute24` over BabyBear are the
specification (`permute16_spec`, `permute24_spec`).
-/

@[expose] public section
namespace CompStark.Poseidon2.BabyBear.Packed
open CompStark.Poseidon2.Packed
open Montgomery.Native32.Words (Fits Fits.mono Fits.of_size inBounds)
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTTFast.Packed (add sub reduceOnce)
open CompPoly.CPolynomial.NTTFast.Packed.Native (readUOffset)

local notation "F" => _root_.BabyBear.Fast.Field

/-- The entries after the ninth of the width-16 internal diagonal, as `(k, negative)` for
`±2 ^ (-k)`. -/
def tail16 : List (Nat × Bool) :=
  [(8, false), (2, false), (3, false), (27, false), (8, true), (4, true), (27, true)]

/-- The entries after the ninth of the width-24 internal diagonal. -/
def tail24 : List (Nat × Bool) :=
  [(8, false), (2, false), (3, false), (4, false), (7, false), (9, false), (27, false), (8, true),
    (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (27, true)]

/-! ### Width 16 -/

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- A partial round with constant `c` on the eight states at `i`. -/
@[inline] def partial16 (c : UInt32) (b : ByteArray) (i : USize) (hb : GroupFits b i) :
    { x : ByteArray // x.size = b.size } :=
  p2_partial% babybear 16 8

set_option maxHeartbeats 4000000 in
/-- The partial rounds of `C`, `partial16` inlined into the loop. -/
@[noinline] def partials16 {n : Nat} (C : @& Packed16) (i : USize) (h : Room16 n i) (b : Buf n) :
    Buf n :=
  partialsLoop16 partial16 C i h 0 b

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- The constant additions and S-boxes of a full round on the eight states at `i`. -/
@[noinline] def sbox16 (rc : @& ByteArray) (r : USize) (b : ByteArray) (i : USize)
    (hb : GroupFits b i) (hr : Fits rc r 15) : { x : ByteArray // x.size = b.size } :=
  p2_sbox% babybear 16 8

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- `mat4` on every block of four coordinates of the eight states at `i`, words below `2 p`. -/
@[noinline] def mat4x16 (b : ByteArray) (i : USize) (hb : GroupFits b i) :
    { x : ByteArray // x.size = b.size } :=
  p2_mat4% babybear 16 8

set_option maxRecDepth 16384 in
/-- The block-sum mixing of the external matrix on the eight states at `i`. -/
@[noinline] def mix16 (b : ByteArray) (i : USize) (hb : GroupFits b i) :
    { x : ByteArray // x.size = b.size } :=
  p2_mix% babybear 16 8

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem sbox16_encode (rc W : Array F) (r i : USize) (hb) (hr) :
    (sbox16 (encode rc) r (encode W) i hb hr).1 =
      encode (sboxWords (pow7Lazy _root_.BabyBear.fieldSize) coords16 rc W r.toNat i.toNat) := by
  p2_sbox_encode sbox16

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem mat4x16_encodeWords (U : Array UInt32) (i : USize) (hb)
    (hU : ∀ k, (U.getD k 0).toNat < 2 * _root_.BabyBear.fieldSize) :
    (mat4x16 (encode U) i hb).1 =
      encode (mat4Words _root_.BabyBear.fieldSize coords16 U i.toNat) := by
  p2_mat4_encode mat4x16

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem mix16_encode (W : Array F) (i : USize) (hb) :
    (mix16 (encode W) i hb).1 = encode (mixModel coords16 [4, 8, 12] W i.toNat) := by
  p2_mix_encode mix16

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem partial16_encode (c : F) (W : Array F) (i : USize) (hb) :
    (partial16 c.val (encode W) i hb).1 = encode (partialModel 7 tail16 coords16 c W i.toNat) := by
  p2_partial_encode partial16 [tail16]

theorem partialModel16_eq (c : F) (W : Array F) (i : Nat) :
    partialModel 7 tail16 coords16 c W i =
      spliceRows coords16 W i fun j ↦
        (partialRows 7 tail16 coords16.tail c W i).getD j fun _ ↦ 0 := by
  p2_partialModel_eq [tail16]

/-- The partial-round model is a partial round, lane by lane, for the width-16 diagonal. -/
theorem lane_partial16 (P : Params F 16) (hd : P.degree = 7) (hD : P.diagonal = diagonal16 F)
    (c : F) (W : Array F) (i : Nat) (hW : i + 8 * 16 ≤ W.size) (l : Nat) (hl : l < 8) :
    lane 16 (spliceRows coords16 W i fun j ↦ (partialRows 7 tail16 coords16.tail c W i).getD j
      fun _ ↦ 0) i l = partialRound P (lane 16 W i l) c := by
  rw [lane_spliceRows coords16_spec _ _ _ hW l hl]
  p2_lane_partial [tail16, diagonal16]

/-! ### Width 24 -/

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- A width-24 partial round with constant `c`. -/
@[inline] def partial24 (c : UInt32) (b : ByteArray) (i : USize) (hb : GroupFits24 b i) :
    { x : ByteArray // x.size = b.size } :=
  p2_partial% babybear 24 8

set_option maxHeartbeats 4000000 in
/-- The width-24 partial rounds of `C`, `partial24` inlined into the loop. -/
@[noinline] def partials24 {n : Nat} (C : @& Packed24) (i : USize) (h : Room24 n i) (b : Buf n) :
    Buf n :=
  partialsLoop24 partial24 C i h 0 b

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- The constant additions and S-boxes of a width-24 full round. -/
@[noinline] def sbox24 (rc : @& ByteArray) (r : USize) (b : ByteArray) (i : USize)
    (hb : GroupFits24 b i) (hr : Fits rc r 23) : { x : ByteArray // x.size = b.size } :=
  p2_sbox% babybear 24 8

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- `mat4` on every block of four coordinates of a width-24 group, words below `2 p`. -/
@[noinline] def mat4x24 (b : ByteArray) (i : USize) (hb : GroupFits24 b i) :
    { x : ByteArray // x.size = b.size } :=
  p2_mat4% babybear 24 8

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- The block-sum mixing of the width-24 external matrix. -/
@[noinline] def mix24 (b : ByteArray) (i : USize) (hb : GroupFits24 b i) :
    { x : ByteArray // x.size = b.size } :=
  p2_mix% babybear 24 8

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem sbox24_encode (rc W : Array F) (r i : USize) (hb) (hr) :
    (sbox24 (encode rc) r (encode W) i hb hr).1 =
      encode (sboxWords (pow7Lazy _root_.BabyBear.fieldSize) coords24 rc W r.toNat i.toNat) := by
  p2_sbox_encode sbox24

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem mat4x24_encodeWords (U : Array UInt32) (i : USize) (hb)
    (hU : ∀ k, (U.getD k 0).toNat < 2 * _root_.BabyBear.fieldSize) :
    (mat4x24 (encode U) i hb).1 =
      encode (mat4Words _root_.BabyBear.fieldSize coords24 U i.toNat) := by
  p2_mat4_encode mat4x24

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem mix24_encode (W : Array F) (i : USize) (hb) :
    (mix24 (encode W) i hb).1 = encode (mixModel coords24 [4, 8, 12, 16, 20] W i.toNat) := by
  p2_mix_encode mix24

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem partial24_encode (c : F) (W : Array F) (i : USize) (hb) :
    (partial24 c.val (encode W) i hb).1 = encode (partialModel 7 tail24 coords24 c W i.toNat) := by
  p2_partial_encode partial24 [tail24]

theorem partialModel24_eq (c : F) (W : Array F) (i : Nat) :
    partialModel 7 tail24 coords24 c W i =
      spliceRows coords24 W i fun j ↦
        (partialRows 7 tail24 coords24.tail c W i).getD j fun _ ↦ 0 := by
  p2_partialModel_eq [tail24]

/-- The partial-round model is a partial round, lane by lane, for the width-24 diagonal. -/
theorem lane_partial24 (P : Params F 24) (hd : P.degree = 7) (hD : P.diagonal = diagonal24 F)
    (c : F) (W : Array F) (i : Nat) (hW : i + 8 * 24 ≤ W.size) (l : Nat) (hl : l < 8) :
    lane 24 (spliceRows coords24 W i fun j ↦ (partialRows 7 tail24 coords24.tail c W i).getD j
      fun _ ↦ 0) i l = partialRound P (lane 24 W i l) c := by
  rw [lane_spliceRows coords24_spec _ _ _ hW l hl]
  p2_lane_partial [tail24, diagonal24]

/-- BabyBear's packed Poseidon2 kernels. -/
instance instPackedKernels : PackedKernels _root_.BabyBear.fieldSize where
  degree := 7
  diagonal16 := diagonal16 F
  diagonal24 := diagonal24 F
  lazyPow := pow7Lazy _root_.BabyBear.fieldSize
  lazyPow_lt := pow7Lazy_lt
  reduceOnce_lazyPow := reduceOnce_pow7Lazy
  sbox16 := sbox16
  mat4x16 := mat4x16
  mix16 := mix16
  partial16 := partial16
  partials16 := partials16
  partials16_eq _ _ _ _ := rfl
  sbox24 := sbox24
  mat4x24 := mat4x24
  mix24 := mix24
  partial24 := partial24
  partials24 := partials24
  partials24_eq _ _ _ _ := rfl
  sbox16_encode := sbox16_encode
  mat4x16_encodeWords := mat4x16_encodeWords
  mix16_encode := mix16_encode
  partial16_spec P hd hD c W i hb hW :=
    partial_spec_of coords16_spec P c W i.toNat _ hW (lane_partial16 P hd hD c W i.toNat hW) _
      ((partial16_encode c W i hb).trans (congrArg encode (partialModel16_eq c W i.toNat)))
  sbox24_encode := sbox24_encode
  mat4x24_encodeWords := mat4x24_encodeWords
  mix24_encode := mix24_encode
  partial24_spec P hd hD c W i hb hW :=
    partial_spec_of coords24_spec P c W i.toNat _ hW (lane_partial24 P hd hD c W i.toNat hW) _
      ((partial24_encode c W i hb).trans (congrArg encode (partialModel24_eq c W i.toNat)))


/-- Plonky3's width-16 Poseidon2 on packed Montgomery words: every lane of the group at `i`,
read in the spec field `BabyBear.Field`, goes through the specification permutation. -/
theorem permute16_width16 (W : Array F) (i : USize) (hfit : GroupFits (encode W) i) :
    ∃ W', permute16 _root_.BabyBear.fieldSize (Packed16.ofParams (width16 F)) (encode W) i =
        encode W' ∧
      W'.size = W.size ∧
      (∀ l < 8, (lane 16 W' i.toNat l).map _root_.BabyBear.Fast.ringEquiv =
        permute (width16 _root_.BabyBear.Field)
          ((lane 16 W i.toNat l).map _root_.BabyBear.Fast.ringEquiv)) ∧
      ∀ k, (k < i.toNat ∨ i.toNat + 8 * 16 ≤ k) → W'.getD k 0 = W.getD k 0 := by
  obtain ⟨W', e, hs, hl, ho⟩ := permute16_spec (width16 F) rfl rfl rfl rfl W i hfit
  exact ⟨W', e, hs, fun l hl' ↦ by rw [hl l hl', fast_width16], ho⟩

/-- Plonky3's width-24 Poseidon2 on packed Montgomery words, read in the spec field. -/
theorem permute24_width24 (W : Array F) (i : USize) (hfit : GroupFits24 (encode W) i) :
    ∃ W', permute24 _root_.BabyBear.fieldSize (Packed24.ofParams (width24 F)) (encode W) i =
        encode W' ∧
      W'.size = W.size ∧
      (∀ l < 8, (lane 24 W' i.toNat l).map _root_.BabyBear.Fast.ringEquiv =
        permute (width24 _root_.BabyBear.Field)
          ((lane 24 W i.toNat l).map _root_.BabyBear.Fast.ringEquiv)) ∧
      ∀ k, (k < i.toNat ∨ i.toNat + 8 * 24 ≤ k) → W'.getD k 0 = W.getD k 0 := by
  obtain ⟨W', e, hs, hl, ho⟩ := permute24_spec (width24 F) rfl rfl rfl rfl W i hfit
  exact ⟨W', e, hs, fun l hl' ↦ by rw [hl l hl', fast_width24], ho⟩

end CompStark.Poseidon2.BabyBear.Packed
