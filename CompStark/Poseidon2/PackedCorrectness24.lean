/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Poseidon2.PackedCorrectness
public import CompStark.Poseidon2.Packed24
import all CompStark.Poseidon2.Packed24
public import CompStark.Poseidon2.ArithmeticLemmas
public import CompStark.Poseidon2.Map
import all CompStark.Poseidon2.Packed
import all CompPoly.Univariate.NTTFast.Packed.Native

/-! # Correctness of the packed width-24 Poseidon2

Each kernel of `permute24` refines a model of `PackedLanes`, whose lanes are the rounds of the
specification; the round loops thread `Holds` through them (`permute24_spec`), and
`permute24_width24` reads the lanes of Plonky3's instance in the spec field.
-/

@[expose] public section
namespace CompStark.Poseidon2.Packed
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTTFast.Packed (size_encode_fields add_val sub_val
  Native.encodeFields_eq)
open CompPoly.CPolynomial.NTTFast.Packed.Native (readUOffset_encode usize_numeral)

local notation "F" => KoalaBear.Fast.Field

/-- The coordinates of a width-24 state. -/
def coords24 : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

theorem coords24_spec : Coords 24 coords24 :=
  ⟨by decide, fun j hj ↦ by interval_cases j <;> decide⟩

/-- The rows of a width-24 partial round: `V_j · x + sum` for the width-24 diagonal `V`, as
`partial24` computes them, coordinate `0` as `rest - y = -2 y + (y + rest)`. -/
def partialRows24 (c : F) (W : Array F) (i : Nat) : List (Nat → F) :=
  let x (j l : Nat) := word W i j l
  let r (l : Nat) := restSum [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
    20, 21, 22, 23] W i l
  let s (l : Nat) := rowSum [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
    20, 21, 22, 23] c W i l
  [fun l ↦ r l - cubeAdd c (x 0 l),
   fun l ↦ s l + x 1 l,
   fun l ↦ s l + (x 2 l + x 2 l),
   fun l ↦ s l + x 3 l * half,
   fun l ↦ s l + (x 4 l + x 4 l + x 4 l),
   fun l ↦ s l + (x 5 l + x 5 l + (x 5 l + x 5 l)),
   fun l ↦ s l - x 6 l * half,
   fun l ↦ s l - (x 7 l + x 7 l + x 7 l),
   fun l ↦ s l - (x 8 l + x 8 l + (x 8 l + x 8 l)),
   fun l ↦ s l + x 9 l * invPow2 8,
   fun l ↦ s l + x 10 l * invPow2 2,
   fun l ↦ s l + x 11 l * invPow2 3,
   fun l ↦ s l + x 12 l * invPow2 4,
   fun l ↦ s l + x 13 l * invPow2 5,
   fun l ↦ s l + x 14 l * invPow2 6,
   fun l ↦ s l + x 15 l * invPow2 24,
   fun l ↦ s l - x 16 l * invPow2 8,
   fun l ↦ s l - x 17 l * invPow2 3,
   fun l ↦ s l - x 18 l * invPow2 4,
   fun l ↦ s l - x 19 l * invPow2 5,
   fun l ↦ s l - x 20 l * invPow2 6,
   fun l ↦ s l - x 21 l * invPow2 7,
   fun l ↦ s l - x 22 l * invPow2 9,
   fun l ↦ s l - x 23 l * invPow2 24]

/-- The model of `partial24`. -/
def partialModel24 (c : F) (W : Array F) (i : Nat) : Array F :=
  spliceList coords24 W i (partialRows24 c W i)

/-! ### Kernels -/

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem sbox24_encode (rc W : Array F) (r i : USize) (hb) (hr) :
    (sbox24 (encode rc) r (encode W) i hb hr).1 =
      encode (sboxModel coords24 rc W r.toNat i.toNat) := by
  have hs := hb
  simp only [GroupFits24, Fits, size_encode_fields] at hs
  unfold sbox24
  simp only [touch8_encode, readUOffset_encode, add_val, cube_val, USize.reduceToNat]
  simp (disch := (simp only [USize.reduceToNat, size_encode_fields]; omega)) only [store8_encode']
  simp only [USize.reduceToNat, sboxModel, spliceRows, word, coords24, lit8, List.foldl_cons,
    List.foldl_nil, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem mat4x24_encode (W : Array F) (i : USize) (hb) :
    (mat4x24 (encode W) i hb).1 = encode (mat4Model coords24 W i.toNat) := by
  have hs := hb
  simp only [GroupFits24, Fits, size_encode_fields] at hs
  unfold mat4x24
  simp only [touch8_encode, readUOffset_encode, add_val, USize.reduceToNat]
  simp (disch := (simp only [USize.reduceToNat, size_encode_fields]; omega)) only [store8_encode']
  simp only [USize.reduceToNat, mat4Model, spliceRows, word, coords24, lit8, List.foldl_cons,
    List.foldl_nil, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.add_zero,
    mat4Word]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem mix24_encode (W : Array F) (i : USize) (hb) :
    (mix24 (encode W) i hb).1 = encode (mixModel coords24 [4, 8, 12, 16, 20] W i.toNat) := by
  have hs := hb
  simp only [GroupFits24, Fits, size_encode_fields] at hs
  unfold mix24
  simp only [touch8_encode, readUOffset_encode, add_val, USize.reduceToNat]
  simp (disch := (simp only [USize.reduceToNat, size_encode_fields]; omega)) only [store8_encode']
  simp only [USize.reduceToNat, mixModel, blockSum, spliceRows, word, coords24, lit8,
    List.foldl_cons, List.foldl_nil, Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.add_zero]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem partial24_encode (c : F) (d : ByteArray) (W : Array F) (i : USize) (hb) (hd) :
    (partial24 c.val d (encode W) i hb hd).1 = encode (partialModel24 c W i.toNat) := by
  have hs := hb
  simp only [GroupFits24, Fits, size_encode_fields] at hs
  unfold partial24
  simp (disch := decide) only [touch8_encode, readUOffset_encode, add_val, sub_val, cube_val,
    halve_val,
    mulInvPow2_val, USize.reduceToNat, UInt32.reduceToNat]
  simp (disch := (simp only [USize.reduceToNat, size_encode_fields]; omega)) only [store8_encode']
  simp only [USize.reduceToNat, partialModel24, partialRows24, spliceList, rowSum, restSum,
    treeSum, pairSums, List.map_cons, List.map_nil, List.headD_cons, cubeAdd, word,
    coords24, lit8, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil,
    Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, Nat.zero_add]

/-! ### Lanes -/

/-- The partial-round model is a row splice of its rows. -/
theorem partialModel24_eq (c : F) (W : Array F) (i : Nat) :
    partialModel24 c W i =
      spliceRows coords24 W i fun j ↦ (partialRows24 c W i).getD j fun _ ↦ 0 := by
  simp only [partialModel24, spliceList, spliceRows, partialRows24, coords24, List.zip_cons_cons,
    List.zip_nil_right, List.foldl_cons, List.foldl_nil, List.getD_cons_zero,
    List.getD_cons_succ]

theorem sum_blocks6 (f : Nat → F) :
    ∑ b : Fin (24 / 4), f b.val = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  rw [show 24 / 4 = 6 from rfl, Fin.sum_univ_eq_sum_range f 6]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

/-- `mat4` then the block-sum mixing is the external matrix, lane by lane. -/
theorem lane_mix_mat4_24 (W : Array F) (i : Nat) (hW : i + 8 * 24 ≤ W.size) (l : Nat)
    (hl : l < 8) :
    lane 24 (mixModel coords24 [4, 8, 12, 16, 20] (mat4Model coords24 W i) i) i l =
      externalLinear (lane 24 W i l) := by
  have hc := coords24_spec
  have hW' : i + 8 * 24 ≤ (mat4Model coords24 W i).size := by
    rw [mat4Model, size_spliceRows hc _ _ _ hW]; exact hW
  ext j hj
  simp only [lane, Vector.getElem_ofFn]
  rw [mixModel, word_spliceRows hc _ _ _ hW' j hj l hl]
  simp only [blockSum, List.foldl_cons, List.foldl_nil, mat4Model,
    word_spliceRows hc _ _ _ hW _ (show j % 4 < 24 by omega) l hl,
    word_spliceRows hc _ _ _ hW _ (show 4 + j % 4 < 24 by omega) l hl,
    word_spliceRows hc _ _ _ hW _ (show 8 + j % 4 < 24 by omega) l hl,
    word_spliceRows hc _ _ _ hW _ (show 12 + j % 4 < 24 by omega) l hl,
    word_spliceRows hc _ _ _ hW _ (show 16 + j % 4 < 24 by omega) l hl,
    word_spliceRows hc _ _ _ hW _ (show 20 + j % 4 < 24 by omega) l hl,
    word_spliceRows hc _ _ _ hW _ hj l hl]
  simp only [externalLinear, Vector.getElem_ofFn]
  rw [sum_blocks6 fun b ↦ mat4 (Vector.ofFn fun j : Fin 24 ↦ word W i j.val l) b (j % 4)]
  simp only [mat4]
  interval_cases j <;>
    simp (disch := omega) only [Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd,
      Nat.zero_mod, mat4Word, Vector.getElem?_ofFn, Nat.reduceLT, ↓reduceDIte,
      Option.getD_some] <;> ring

/-- The S-box kernel then the external matrix is a full round, lane by lane. -/
theorem lane_full24 (P : Params F 24) (hd : P.degree = 3) (rc W : Array F) (r i : Nat)
    (hW : i + 8 * 24 ≤ W.size) (l : Nat) (hl : l < 8) :
    lane 24 (mixModel coords24 [4, 8, 12, 16, 20]
      (mat4Model coords24 (sboxModel coords24 rc W r i) i) i) i l =
        fullRound P (lane 24 W i l) (row 24 rc r) := by
  have hW' : i + 8 * 24 ≤ (sboxModel coords24 rc W r i).size := by
    rw [sboxModel, size_spliceRows coords24_spec _ _ _ hW]; exact hW
  rw [lane_mix_mat4_24 _ i hW' l hl, lane_sbox coords24_spec rc W r i hW l hl, fullRound, hd]

/-- The partial-round kernel is a partial round, lane by lane, for the width-24 diagonal. -/
theorem lane_partial24 (P : Params F 24) (hd : P.degree = 3)
    (hD : P.diagonal = KoalaBear.diagonal24 F) (c : F) (W : Array F) (i : Nat)
    (hW : i + 8 * 24 ≤ W.size) (l : Nat) (hl : l < 8) :
    lane 24 (partialModel24 c W i) i l = partialRound P (lane 24 W i l) c := by
  rw [partialModel24_eq, lane_spliceRows coords24_spec _ _ _ hW l hl]
  ext j hj
  simp only [Vector.getElem_ofFn, Fin.getElem_fin, partialRound, internalLinear, hd, hD, lane,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, ↓reduceIte,
    Nat.add_one_ne_zero, add_zero]
  interval_cases j <;>
    simp only [partialRows24, List.getD_cons_zero, List.getD_cons_succ, rowSum, restSum, cubeAdd,
      treeSum, pairSums, List.map_cons, List.map_nil, List.headD_cons, half, invPow2,
      KoalaBear.diagonal24, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, ↓reduceIte,
      Nat.reduceEqDiff] <;> ring

/-! ### The round loops -/

theorem le_of_room24 {n : Nat} (W : Array F) (i : USize) (hn : (encode W).size = n)
    (h : Room24 n i) : i.toNat + 8 * 24 ≤ W.size := by
  rw [size_encode_fields] at hn
  omega

/-- The external matrix on a group that holds `S`. -/
theorem external24_holds {n : Nat} (W0 W : Array F) (i : USize) (S : Nat → Vector F 24)
    (h : Holds 24 W0 i.toNat S W) (hr : Room24 n i) (s : Buf n) (hs : s.1 = encode W) :
    ∃ W', (external24 s i hr).1 = encode W' ∧
      Holds 24 W0 i.toNat (fun l ↦ externalLinear (S l)) W' := by
  obtain ⟨b, hb⟩ := s
  dsimp only at hs
  subst hs
  have hW := le_of_room24 W i hb hr
  have hs1 : (mat4Model coords24 W i.toNat).size = W.size := by
    rw [mat4Model, size_spliceRows coords24_spec _ _ _ hW]
  refine ⟨mixModel coords24 [4, 8, 12, 16, 20] (mat4Model coords24 W i.toNat) i.toNat, ?_, ?_⟩
  · obtain ⟨hb1, e⟩ := Buf.val_eq (s := Buf.of ⟨encode W, hb⟩
      (mat4x24 (encode W) i (hr.fits ⟨encode W, hb⟩)))
      ((Buf.of_val _ _).trans (mat4x24_encode W i _))
    unfold external24
    dsimp only
    rw [e, Buf.of_val]
    exact mix24_encode _ i _
  · have hW1 : i.toNat + 8 * 24 ≤ (mat4Model coords24 W i.toNat).size := by rw [hs1]; exact hW
    refine ⟨?_, fun l hl ↦ by rw [lane_mix_mat4_24 W i.toNat hW l hl, h.2.1 l hl], fun k hk ↦ ?_⟩
    · rw [mixModel, size_spliceRows coords24_spec _ _ _ hW1, hs1, h.1]
    · rw [mixModel, getD_spliceRows_outside coords24_spec _ _ _ hW1 k hk, mat4Model,
        getD_spliceRows_outside coords24_spec _ _ _ hW k hk, h.2.2 k hk]

theorem toNat_twentyfour_mul (k : USize) (hk : k < 4) : (24 * k).toNat = 24 * k.toNat := by
  have hk' := lt_four_toNat hk
  have := USize.le_size
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  rw [USize.toNat_mul, usize_numeral 24 (by decide), hsize]
  exact Nat.mod_eq_of_lt (by omega)

/-- Full rounds `k, …, 3` with the constant rows of `rcW`. -/
theorem fullRounds24Go_holds {n : Nat} (P : Params F 24) (hd : P.degree = 3) (rcW W0 : Array F)
    (hrc : Rows24 (encode rcW)) (i : USize) (hr : Room24 n i) :
    ∀ (m : Nat) (k : USize), 4 - k.toNat = m → ∀ (W : Array F) (S : Nat → Vector F 24),
      Holds 24 W0 i.toNat S W → ∀ s : Buf n, s.1 = encode W →
      ∃ W', (fullRounds24Go (encode rcW) hrc i hr k s).1 = encode W' ∧
        Holds 24 W0 i.toNat (fun l ↦ (List.range' k.toNat (4 - k.toNat)).foldl
          (fun s r ↦ fullRound P s (row 24 rcW (24 * r))) (S l)) W' := by
  intro m
  induction m with
  | zero =>
    intro k hm W S h s hs
    have hk : ¬ k < 4 := fun hk ↦ by have := lt_four_toNat hk; omega
    refine ⟨W, ?_, by rw [show 4 - k.toNat = 0 by omega]; exact h⟩
    rw [fullRounds24Go, dite_eq_right hk, hs]
  | succ m ih =>
    intro k hm W S h s hs
    have hk : k < 4 := by
      rw [USize.lt_iff_toNat_lt, usize_numeral 4 (by decide)]; omega
    obtain ⟨b, hb⟩ := s
    dsimp only at hs
    subst hs
    have hW := le_of_room24 W i hb hr
    have e24 : (24 * k).toNat = 24 * k.toNat := toNat_twentyfour_mul k hk
    have hsz : (sboxModel coords24 rcW W (24 * k.toNat) i.toNat).size = W.size := by
      rw [sboxModel, size_spliceRows coords24_spec _ _ _ hW]
    have hsb : Holds 24 W0 i.toNat (fun l ↦ Vector.ofFn fun j : Fin 24 ↦
        ((S l)[j] + (row 24 rcW (24 * k.toNat))[j]) ^ 3)
        (sboxModel coords24 rcW W (24 * k.toNat) i.toNat) :=
      ⟨by rw [hsz, h.1], fun l hl ↦ by rw [lane_sbox coords24_spec _ _ _ _ hW l hl, h.2.1 l hl],
        fun k' hk' ↦ by
          rw [sboxModel, getD_spliceRows_outside coords24_spec _ _ _ hW k' hk', h.2.2 k' hk']⟩
    obtain ⟨W2, e2, h2⟩ := external24_holds W0 _ i _ hsb hr
      (Buf.of ⟨encode W, hb⟩ (sbox24 (encode rcW) (24 * k) (encode W) i (hr.fits ⟨encode W, hb⟩)
        (hrc.fits k hk))) (by rw [Buf.of_val, sbox24_encode, e24])
    obtain ⟨W3, e3, h3⟩ := ih (k + 1) (by rw [toNat_succ_of_lt_four k hk]; omega) W2 _ h2 _ e2
    refine ⟨W3, ?_, ?_⟩
    · rw [fullRounds24Go, dite_eq_left hk]
      exact e3
    · refine ⟨h3.1, fun l hl ↦ ?_, h3.2.2⟩
      rw [h3.2.1 l hl, toNat_succ_of_lt_four k hk,
        show 4 - k.toNat = (4 - (k.toNat + 1)) + 1 by omega, List.range'_succ]
      simp only [List.foldl_cons, fullRound, hd]

/-- The partial rounds with the constants `k, …` of `Packed24.ofParams P`. -/
theorem partialRounds24Go_holds {n : Nat} (P : Params F 24) (hd : P.degree = 3)
    (hD : P.diagonal = KoalaBear.diagonal24 F) (W0 : Array F) (i : USize) (hr : Room24 n i)
    (hdf : Fits (Packed24.ofParams P).diagonal 0 23) :
    ∀ (m k : Nat), P.internal.length - k = m → ∀ (W : Array F) (S : Nat → Vector F 24),
      Holds 24 W0 i.toNat S W → ∀ s : Buf n, s.1 = encode W →
      ∃ W', (partialRounds24Go (Packed24.ofParams P) hdf i hr k s).1 = encode W' ∧
        Holds 24 W0 i.toNat (fun l ↦ (P.internal.drop k).foldl (partialRound P) (S l)) W' := by
  intro m
  induction m with
  | zero =>
    intro k hm W S h s hs
    have hk : ¬ k < (Packed24.ofParams P).internal.size := by
      simp only [Packed24.ofParams, List.size_toArray, List.length_map]; omega
    refine ⟨W, ?_, by rw [List.drop_eq_nil_of_le (by omega)]; exact h⟩
    rw [partialRounds24Go, dite_eq_right hk, hs]
  | succ m ih =>
    intro k hm W S h s hs
    have hk : k < (Packed24.ofParams P).internal.size := by
      simp only [Packed24.ofParams, List.size_toArray, List.length_map]; omega
    have hk' : k < P.internal.length := by omega
    obtain ⟨b, hb⟩ := s
    dsimp only at hs
    subst hs
    have hW := le_of_room24 W i hb hr
    set c := P.internal[k] with hc
    have hp : Holds 24 W0 i.toNat (fun l ↦ partialRound P (S l) c)
        (partialModel24 c W i.toNat) := by
      rw [partialModel24_eq]
      refine ⟨by rw [size_spliceRows coords24_spec _ _ _ hW, h.1], fun l hl ↦ ?_, fun k hk ↦ by
        rw [getD_spliceRows_outside coords24_spec _ _ _ hW k hk, h.2.2 k hk]⟩
      rw [← partialModel24_eq, lane_partial24 P hd hD c W i.toNat hW l hl, h.2.1 l hl]
    have hkc : (Packed24.ofParams P).internal[k] = c.val := by
      simp only [Packed24.ofParams, List.getElem_toArray, List.getElem_map, hc]
    have hs1 : (Buf.of ⟨encode W, hb⟩ (partial24 (Packed24.ofParams P).internal[k]
        (Packed24.ofParams P).diagonal (encode W) i (hr.fits ⟨encode W, hb⟩) hdf)).1 =
          encode (partialModel24 c W i.toNat) := by
      rw [Buf.of_val, hkc]
      exact partial24_encode c _ W i _ hdf
    obtain ⟨W', e, h'⟩ := ih (k + 1) (by omega) _ _ hp _ hs1
    refine ⟨W', ?_, ?_⟩
    · rw [partialRounds24Go, dite_eq_left hk]
      exact e
    · refine ⟨h'.1, fun l hl ↦ ?_, h'.2.2⟩
      rw [h'.2.1 l hl, List.drop_eq_getElem_cons hk']
      simp only [List.foldl_cons, hc]

/-- **The packed permutation is correct.** On a group of eight states at word `i` of a packed
buffer, `permute24` applies the Poseidon2 permutation to every state, and leaves the rest of the
buffer unchanged. This covers Plonky3's default width-24 instance, `KoalaBear.width24`. -/
theorem permute24_spec (P : Params F 24) (hd : P.degree = 3)
    (hD : P.diagonal = KoalaBear.diagonal24 F) (hi : P.initial.length = 4)
    (ht : P.terminal.length = 4) (W : Array F) (i : USize) (hfit : GroupFits24 (encode W) i) :
    ∃ W', permute24 (Packed24.ofParams P) (encode W) i = encode W' ∧ W'.size = W.size ∧
      (∀ l < 8, lane 24 W' i.toNat l = permute P (lane 24 W i.toNat l)) ∧
      ∀ k, (k < i.toNat ∨ i.toNat + 8 * 24 ≤ k) → W'.getD k 0 = W.getD k 0 := by
  have hsize (rows : List (Vector F 24)) (hr : rows.length = 4) :
      (rows.foldl (fun acc c ↦ acc ++ c.toArray) #[]).size = 96 := by
    rw [(concat_rows rows #[]).1, hr]; rfl
  have hu : 4 * 96 < USize.size := by have := USize.le_size; omega
  have hK : (Packed24.ofParams P).Fits := by
    simp only [Packed24.Fits, Rows24, Packed24.ofParams, Native.encodeFields_eq,
      size_encode_fields, hsize _ hi, hsize _ ht, Fits, Vector.size_toArray, USize.reduceToNat]
    omega
  have h0 : Holds 24 W i.toNat (fun l ↦ lane 24 W i.toNat l) W :=
    ⟨rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  have hr : Room24 (encode W).size i := hfit
  obtain ⟨W1, e1, h1⟩ := external24_holds W W i _ h0 hr ⟨encode W, rfl⟩ rfl
  obtain ⟨W2, e2, h2⟩ := fullRounds24Go_holds P hd _ W (by
      simpa only [Packed24.ofParams, Native.encodeFields_eq] using hK.1) i hr 4 0 rfl W1 _ h1 _ e1
  obtain ⟨W3, e3, h3⟩ := partialRounds24Go_holds P hd hD W i hr hK.2.2 _ 0 rfl W2 _ h2 _ e2
  obtain ⟨W4, e4, h4⟩ := fullRounds24Go_holds P hd _ W (by
      simpa only [Packed24.ofParams, Native.encodeFields_eq] using hK.2.1) i hr 4 0 rfl W3 _ h3
      _ e3
  refine ⟨W4, ?_, h4.1, fun l hl ↦ ?_, h4.2.2⟩
  · rw [permute24, dite_eq_left ⟨hfit, hK⟩]
    simpa only [Packed24.ofParams, Native.encodeFields_eq] using e4
  · rw [h4.2.1 l hl]
    simp only [USize.toNat_zero, Nat.sub_zero, List.drop_zero, ← List.range_eq_range']
    rw [fullRounds_spec P _ hi, fullRounds_spec P _ ht]
    rfl

/-- Plonky3's width-24 Poseidon2 on packed Montgomery words: every lane of the group at `i`,
read in the spec field `KoalaBear.Field`, goes through the specification permutation. -/
theorem permute24_width24 (W : Array F) (i : USize) (hfit : GroupFits24 (encode W) i) :
    ∃ W', permute24 (Packed24.ofParams (KoalaBear.width24 F)) (encode W) i = encode W' ∧
      W'.size = W.size ∧
      (∀ l < 8, (lane 24 W' i.toNat l).map KoalaBear.Fast.ringEquiv =
        permute (KoalaBear.width24 _root_.KoalaBear.Field)
          ((lane 24 W i.toNat l).map KoalaBear.Fast.ringEquiv)) ∧
      ∀ k, (k < i.toNat ∨ i.toNat + 8 * 24 ≤ k) → W'.getD k 0 = W.getD k 0 := by
  obtain ⟨W', e, hs, hl, ho⟩ := permute24_spec (KoalaBear.width24 F) rfl rfl rfl rfl W i hfit
  exact ⟨W', e, hs, fun l hl' ↦ by rw [hl l hl', KoalaBear.fast_width24], ho⟩

end CompStark.Poseidon2.Packed
