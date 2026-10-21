/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Poseidon2.PackedLanes
public import CompStark.Poseidon2.ArithmeticLemmas
public import CompStark.Poseidon2.Map
import all CompStark.Poseidon2.Packed
import all CompPoly.Univariate.NTTFast.Packed.Native

/-! # Correctness of the packed width-16 Poseidon2

Each kernel of `permute16` refines a model of `PackedLanes`, whose lanes are the rounds of the
specification; the round loops thread `Holds` through them (`permute16_spec`), and
`permute16_width16` reads the lanes of Plonky3's instance in the spec field.
-/

@[expose] public section
namespace CompStark.Poseidon2.Packed
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTTFast.Packed (size_encode_fields add_val sub_val
  Native.encodeFields_eq)
open CompPoly.CPolynomial.NTTFast.Packed.Native (readUOffset_encode)

local notation "F" => KoalaBear.Fast.Field

/-- The coordinates of a width-16 state. -/
def coords16 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

theorem coords16_spec : Coords 16 coords16 :=
  ⟨by decide, fun j hj ↦ by interval_cases j <;> decide⟩

/-- The rows of a width-16 partial round: `V_j · x + sum` for the width-16 diagonal `V`, as
`partial16` computes them. -/
def partialRows16 (c : F) (W : Array F) (i : Nat) : List (Nat → F) :=
  let x (j l : Nat) := word W i j l
  let s (l : Nat) := rowSum [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] c W i l
  [fun l ↦ s l - (cubeAdd c (x 0 l) + cubeAdd c (x 0 l)),
   fun l ↦ s l + x 1 l,
   fun l ↦ s l + (x 2 l + x 2 l),
   fun l ↦ s l + x 3 l * half,
   fun l ↦ s l + (x 4 l + x 4 l + x 4 l),
   fun l ↦ s l + (x 5 l + x 5 l + (x 5 l + x 5 l)),
   fun l ↦ s l - x 6 l * half,
   fun l ↦ s l - (x 7 l + x 7 l + x 7 l),
   fun l ↦ s l - (x 8 l + x 8 l + (x 8 l + x 8 l)),
   fun l ↦ s l + x 9 l * invPow2 8,
   fun l ↦ s l + x 10 l * invPow2 3,
   fun l ↦ s l + x 11 l * invPow2 24,
   fun l ↦ s l - x 12 l * invPow2 8,
   fun l ↦ s l - x 13 l * invPow2 3,
   fun l ↦ s l - x 14 l * invPow2 4,
   fun l ↦ s l - x 15 l * invPow2 24]

/-- The model of `partial16`. -/
def partialModel16 (c : F) (W : Array F) (i : Nat) : Array F :=
  spliceList coords16 W i (partialRows16 c W i)

/-! ### Kernels -/

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem sbox16_encode (rc W : Array F) (r i : USize) (hb) (hr) :
    sbox16 (encode rc) r (encode W) i hb hr = encode (sboxModel coords16 rc W r.toNat i.toNat) := by
  have hs := hb
  simp only [GroupFits, Fits, size_encode_fields] at hs
  unfold sbox16
  simp only [readUOffset_encode, add_val, cube_val, USize.reduceToNat]
  simp (disch := (simp only [USize.reduceToNat, size_encode_fields]; omega)) only [store8_encode']
  simp only [USize.reduceToNat, sboxModel, spliceRows, word, coords16, lit8, List.foldl_cons,
    List.foldl_nil, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem mat4x16_encode (W : Array F) (i : USize) (hb) :
    mat4x16 (encode W) i hb = encode (mat4Model coords16 W i.toNat) := by
  have hs := hb
  simp only [GroupFits, Fits, size_encode_fields] at hs
  unfold mat4x16
  simp only [readUOffset_encode, add_val, USize.reduceToNat]
  simp (disch := (simp only [USize.reduceToNat, size_encode_fields]; omega)) only [store8_encode']
  simp only [USize.reduceToNat, mat4Model, spliceRows, word, coords16, lit8, List.foldl_cons,
    List.foldl_nil, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.add_zero,
    mat4Word]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem mix16_encode (W : Array F) (i : USize) (hb) :
    mix16 (encode W) i hb = encode (mixModel coords16 [4, 8, 12] W i.toNat) := by
  have hs := hb
  simp only [GroupFits, Fits, size_encode_fields] at hs
  unfold mix16
  simp only [readUOffset_encode, add_val, USize.reduceToNat]
  simp (disch := (simp only [USize.reduceToNat, size_encode_fields]; omega)) only [store8_encode']
  simp only [USize.reduceToNat, mixModel, blockSum, spliceRows, word, coords16, lit8,
    List.foldl_cons, List.foldl_nil, Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.add_zero]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem partial16_encode (c : F) (D W : Array F) (i : USize) (hb) (hd) :
    partial16 c.val (encode D) (encode W) i hb hd = encode (partialModel16 c W i.toNat) := by
  have hs := hb
  simp only [GroupFits, Fits, size_encode_fields] at hs
  unfold partial16
  simp (disch := decide) only [readUOffset_encode, add_val, sub_val, cube_val, halve_val,
    mulInvPow2_val, USize.reduceToNat, UInt32.reduceToNat]
  simp (disch := (simp only [USize.reduceToNat, size_encode_fields]; omega)) only [store8_encode']
  simp only [USize.reduceToNat, partialModel16, partialRows16, spliceList, rowSum,
    treeSum, pairSums, List.map_cons, List.map_nil, List.headD_cons, cubeAdd, word,
    coords16, lit8, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil,
    Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, Nat.zero_add]

/-! ### Lanes -/

/-- The partial-round model is a row splice of its rows. -/
theorem partialModel16_eq (c : F) (W : Array F) (i : Nat) :
    partialModel16 c W i =
      spliceRows coords16 W i fun j ↦ (partialRows16 c W i).getD j fun _ ↦ 0 := by
  simp only [partialModel16, spliceList, spliceRows, partialRows16, coords16, List.zip_cons_cons,
    List.zip_nil_right, List.foldl_cons, List.foldl_nil, List.getD_cons_zero,
    List.getD_cons_succ]

theorem sum_blocks4 (f : Nat → F) : ∑ b : Fin (16 / 4), f b.val = f 0 + f 1 + f 2 + f 3 := by
  rw [show 16 / 4 = 4 from rfl, Fin.sum_univ_four]
  rfl

/-- `mat4` then the block-sum mixing is the external matrix, lane by lane. -/
theorem lane_mix_mat4_16 (W : Array F) (i : Nat) (hW : i + 8 * 16 ≤ W.size) (l : Nat)
    (hl : l < 8) :
    lane 16 (mixModel coords16 [4, 8, 12] (mat4Model coords16 W i) i) i l =
      externalLinear (lane 16 W i l) := by
  have hc := coords16_spec
  have hW' : i + 8 * 16 ≤ (mat4Model coords16 W i).size := by
    rw [mat4Model, size_spliceRows hc _ _ _ hW]; exact hW
  ext j hj
  simp only [lane, Vector.getElem_ofFn]
  rw [mixModel, word_spliceRows hc _ _ _ hW' j hj l hl]
  simp only [blockSum, List.foldl_cons, List.foldl_nil, mat4Model,
    word_spliceRows hc _ _ _ hW _ (show j % 4 < 16 by omega) l hl,
    word_spliceRows hc _ _ _ hW _ (show 4 + j % 4 < 16 by omega) l hl,
    word_spliceRows hc _ _ _ hW _ (show 8 + j % 4 < 16 by omega) l hl,
    word_spliceRows hc _ _ _ hW _ (show 12 + j % 4 < 16 by omega) l hl,
    word_spliceRows hc _ _ _ hW _ hj l hl]
  simp only [externalLinear, Vector.getElem_ofFn]
  rw [sum_blocks4 fun b ↦ mat4 (Vector.ofFn fun j : Fin 16 ↦ word W i j.val l) b (j % 4)]
  simp only [mat4]
  interval_cases j <;>
    simp (disch := omega) only [Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd,
      Nat.zero_mod, mat4Word, Vector.getElem?_ofFn, Nat.reduceLT, ↓reduceDIte,
      Option.getD_some] <;> ring

/-- The S-box kernel then the external matrix is a full round, lane by lane. -/
theorem lane_full16 (P : Params F 16) (hd : P.degree = 3) (rc W : Array F) (r i : Nat)
    (hW : i + 8 * 16 ≤ W.size) (l : Nat) (hl : l < 8) :
    lane 16 (mixModel coords16 [4, 8, 12] (mat4Model coords16 (sboxModel coords16 rc W r i) i) i)
      i l = fullRound P (lane 16 W i l) (row 16 rc r) := by
  have hW' : i + 8 * 16 ≤ (sboxModel coords16 rc W r i).size := by
    rw [sboxModel, size_spliceRows coords16_spec _ _ _ hW]; exact hW
  rw [lane_mix_mat4_16 _ i hW' l hl, lane_sbox coords16_spec rc W r i hW l hl, fullRound, hd]

/-- The partial-round kernel is a partial round, lane by lane, for the width-16 diagonal. -/
theorem lane_partial16 (P : Params F 16) (hd : P.degree = 3)
    (hD : P.diagonal = KoalaBear.diagonal16 F) (c : F) (W : Array F) (i : Nat)
    (hW : i + 8 * 16 ≤ W.size) (l : Nat) (hl : l < 8) :
    lane 16 (partialModel16 c W i) i l = partialRound P (lane 16 W i l) c := by
  rw [partialModel16_eq, lane_spliceRows coords16_spec _ _ _ hW l hl]
  ext j hj
  simp only [Vector.getElem_ofFn, Fin.getElem_fin, partialRound, internalLinear, hd, hD, lane,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, ↓reduceIte,
    Nat.add_one_ne_zero, add_zero]
  interval_cases j <;>
    simp only [partialRows16, List.getD_cons_zero, List.getD_cons_succ, rowSum, cubeAdd,
      treeSum, pairSums, List.map_cons, List.map_nil, List.headD_cons, half, invPow2,
      KoalaBear.diagonal16, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, ↓reduceIte,
      Nat.reduceEqDiff] <;> ring

/-! ### The round loops -/

theorem groupFits_of_size (W W0 : Array F) (i : USize) (hs : W.size = W0.size)
    (h : GroupFits (encode W0) i) : GroupFits (encode W) i := by
  simp only [GroupFits, Fits, size_encode_fields, hs] at h ⊢
  exact h

theorem le_of_groupFits (W : Array F) (i : USize) (h : GroupFits (encode W) i) :
    i.toNat + 8 * 16 ≤ W.size := by
  simp only [GroupFits, Fits, size_encode_fields] at h
  omega

/-- The external matrix on a group that holds `S`. -/
theorem external16_holds (W0 W : Array F) (i : USize) (S : Nat → Vector F 16)
    (h : Holds 16 W0 i.toNat S W) (hfit : GroupFits (encode W0) i) :
    ∃ W', external16 (encode W) i = encode W' ∧
      Holds 16 W0 i.toNat (fun l ↦ externalLinear (S l)) W' := by
  have hg := groupFits_of_size W W0 i h.1 hfit
  have hW := le_of_groupFits W i hg
  have hs1 : (mat4Model coords16 W i.toNat).size = W.size := by
    rw [mat4Model, size_spliceRows coords16_spec _ _ _ hW]
  have hg1 : GroupFits (encode (mat4Model coords16 W i.toNat)) i := groupFits_of_size _ W i hs1 hg
  refine ⟨mixModel coords16 [4, 8, 12] (mat4Model coords16 W i.toNat) i.toNat, ?_, ?_⟩
  · unfold external16
    rw [dite_eq_left_of_eq_true (eq_true hg), mat4x16_encode,
      dite_eq_left_of_eq_true (eq_true hg1), mix16_encode]
  · have hW1 : i.toNat + 8 * 16 ≤ (mat4Model coords16 W i.toNat).size := by rw [hs1]; exact hW
    refine ⟨?_, fun l hl ↦ by rw [lane_mix_mat4_16 W i.toNat hW l hl, h.2.1 l hl], fun k hk ↦ ?_⟩
    · rw [mixModel, size_spliceRows coords16_spec _ _ _ hW1, hs1, h.1]
    · rw [mixModel, getD_spliceRows_outside coords16_spec _ _ _ hW1 k hk, mat4Model,
        getD_spliceRows_outside coords16_spec _ _ _ hW k hk, h.2.2 k hk]

/-- The full-round loop is the fold of its rounds over `List.range`. -/
theorem fullRounds_eq_foldl (rc : ByteArray) (n : Nat) (b : ByteArray) (i : USize) :
    fullRounds rc n b i = (List.range n).foldl (fun b r ↦
      if h : GroupFits b i ∧ 4 * (16 * r + 15) + 3 < rc.size ∧ rc.size < USize.size then
        let b := sbox16 rc (USize.ofNatLT (16 * r) (by omega)) b i h.1
          (by simp only [Fits, USize.toNat_ofNatLT]; exact h.2)
        external16 b i
      else b) b := by
  have go : ∀ n r b, fullRoundsGo rc i n r b = (List.range' r n).foldl (fun b r ↦
      if h : GroupFits b i ∧ 4 * (16 * r + 15) + 3 < rc.size ∧ rc.size < USize.size then
        let b := sbox16 rc (USize.ofNatLT (16 * r) (by omega)) b i h.1
          (by simp only [Fits, USize.toNat_ofNatLT]; exact h.2)
        external16 b i
      else b) b := by
    intro n
    induction n with
    | zero => intro r b; rfl
    | succ n ih => intro r b; rw [List.range'_succ, List.foldl_cons, ← ih]; rfl
  rw [fullRounds, go, List.range_eq_range']

/-- The first `n` full rounds with the constant rows of `rcW`. -/
theorem fullRounds_holds (P : Params F 16) (hd : P.degree = 3) (rcW W0 : Array F) (i : USize)
    (hfit : GroupFits (encode W0) i) (hrc : 4 * rcW.size < USize.size) (n : Nat)
    (hn : 16 * n ≤ rcW.size) (W : Array F) (S : Nat → Vector F 16)
    (h : Holds 16 W0 i.toNat S W) :
    ∃ W', fullRounds (encode rcW) n (encode W) i = encode W' ∧
      Holds 16 W0 i.toNat (fun l ↦
        (List.range n).foldl (fun s r ↦ fullRound P s (row 16 rcW (16 * r))) (S l)) W' := by
  induction n with
  | zero => exact ⟨W, rfl, h⟩
  | succ n ih =>
    obtain ⟨W1, e1, h1⟩ := ih (by omega)
    have hg := groupFits_of_size W1 W0 i h1.1 hfit
    have hW := le_of_groupFits W1 i hg
    have hr : 4 * (16 * n + 15) + 3 < (encode rcW).size ∧ (encode rcW).size < USize.size := by
      simp only [size_encode_fields]; omega
    have hs : (sboxModel coords16 rcW W1 (16 * n) i.toNat).size = W0.size := by
      rw [sboxModel, size_spliceRows coords16_spec _ _ _ hW, h1.1]
    have hsb : Holds 16 W0 i.toNat (fun l ↦ Vector.ofFn fun j : Fin 16 ↦
        (((List.range n).foldl (fun s r ↦ fullRound P s (row 16 rcW (16 * r))) (S l))[j] +
          (row 16 rcW (16 * n))[j]) ^ 3) (sboxModel coords16 rcW W1 (16 * n) i.toNat) :=
      ⟨hs, fun l hl ↦ by rw [lane_sbox coords16_spec _ _ _ _ hW l hl, h1.2.1 l hl], fun k hk ↦ by
        rw [sboxModel, getD_spliceRows_outside coords16_spec _ _ _ hW k hk, h1.2.2 k hk]⟩
    obtain ⟨W2, e2, h2⟩ := external16_holds W0 _ i _ hsb hfit
    refine ⟨W2, ?_, ?_⟩
    · rw [fullRounds_eq_foldl] at e1 ⊢
      rw [List.range_succ, List.foldl_append, e1, List.foldl_cons, List.foldl_nil,
        dite_eq_left_of_eq_true (eq_true ⟨hg, hr⟩)]
      dsimp only
      rw [sbox16_encode, USize.toNat_ofNatLT, e2]
    · refine ⟨h2.1, fun l hl ↦ ?_, h2.2.2⟩
      rw [h2.2.1 l hl]
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, fullRound,
        hd]

/-- The partial rounds with constants `L`, diagonal of the width-16 instance. -/
theorem partialRounds_holds (P : Params F 16) (hd : P.degree = 3)
    (hD : P.diagonal = KoalaBear.diagonal16 F) (W0 : Array F) (i : USize)
    (hfit : GroupFits (encode W0) i) (L : List F) (W : Array F) (S : Nat → Vector F 16)
    (h : Holds 16 W0 i.toNat S W) :
    ∃ W', (L.map Subtype.val).foldl (fun b c ↦
        if h : GroupFits b i ∧ Fits (encode P.diagonal.toArray) 0 15 then
          partial16 c (encode P.diagonal.toArray) b i h.1 h.2
        else b) (encode W) = encode W' ∧
      Holds 16 W0 i.toNat (fun l ↦ L.foldl (partialRound P) (S l)) W' := by
  induction L generalizing W S with
  | nil => exact ⟨W, rfl, h⟩
  | cons c L ih =>
    have hg := groupFits_of_size W W0 i h.1 hfit
    have hW := le_of_groupFits W i hg
    have hdf : Fits (encode P.diagonal.toArray) 0 15 := by
      simp only [Fits, size_encode_fields, Vector.size_toArray, USize.reduceToNat]
      have := USize.le_size
      omega
    have hp : Holds 16 W0 i.toNat (fun l ↦ partialRound P (S l) c)
        (partialModel16 c W i.toNat) := by
      rw [partialModel16_eq]
      refine ⟨by rw [size_spliceRows coords16_spec _ _ _ hW, h.1], fun l hl ↦ ?_, fun k hk ↦ by
        rw [getD_spliceRows_outside coords16_spec _ _ _ hW k hk, h.2.2 k hk]⟩
      rw [← partialModel16_eq, lane_partial16 P hd hD c W i.toNat hW l hl, h.2.1 l hl]
    obtain ⟨W', e, h'⟩ := ih _ _ hp
    refine ⟨W', ?_, h'⟩
    rw [List.map_cons, List.foldl_cons, dite_eq_left_of_eq_true (eq_true ⟨hg, hdf⟩),
      partial16_encode, e]

/-- **The packed permutation is correct.** On a group of eight states at word `i` of a packed
buffer, `permute16` applies the Poseidon2 permutation to every state, and leaves the rest of the
buffer unchanged. This covers Plonky3's default width-16 instance, `KoalaBear.width16`. -/
theorem permute16_spec (P : Params F 16) (hd : P.degree = 3)
    (hD : P.diagonal = KoalaBear.diagonal16 F) (hi : P.initial.length = 4)
    (ht : P.terminal.length = 4) (W : Array F) (i : USize) (hfit : GroupFits (encode W) i) :
    ∃ W', permute16 (Packed16.ofParams P) (encode W) i = encode W' ∧ W'.size = W.size ∧
      (∀ l < 8, lane 16 W' i.toNat l = permute P (lane 16 W i.toNat l)) ∧
      ∀ k, (k < i.toNat ∨ i.toNat + 8 * 16 ≤ k) → W'.getD k 0 = W.getD k 0 := by
  have hsize (rows : List (Vector F 16)) (hr : rows.length = 4) :
      (rows.foldl (fun acc c ↦ acc ++ c.toArray) #[]).size = 64 := by
    rw [(concat_rows rows #[]).1, hr]; rfl
  have hu : 4 * 64 < USize.size := by have := USize.le_size; omega
  have h0 : Holds 16 W i.toNat (fun l ↦ lane 16 W i.toNat l) W :=
    ⟨rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  obtain ⟨W1, e1, h1⟩ := external16_holds W W i _ h0 hfit
  obtain ⟨W2, e2, h2⟩ := fullRounds_holds P hd _ W i hfit (by rw [hsize _ hi]; exact hu) 4
    (by rw [hsize _ hi]) W1 _ h1
  obtain ⟨W3, e3, h3⟩ := partialRounds_holds P hd hD W i hfit P.internal W2 _ h2
  obtain ⟨W4, e4, h4⟩ := fullRounds_holds P hd _ W i hfit (by rw [hsize _ ht]; exact hu) 4
    (by rw [hsize _ ht]) W3 _ h3
  refine ⟨W4, ?_, h4.1, fun l hl ↦ ?_, h4.2.2⟩
  · simp only [permute16, Packed16.ofParams, partialRounds, Native.encodeFields_eq, e1, e2,
      List.foldl_toArray', e3, e4]
  · rw [h4.2.1 l hl]
    beta_reduce
    rw [fullRounds_spec P _ hi, fullRounds_spec P _ ht]
    rfl

/-- Plonky3's width-16 Poseidon2 on packed Montgomery words: every lane of the group at `i`,
read in the spec field `KoalaBear.Field`, goes through the specification permutation. -/
theorem permute16_width16 (W : Array F) (i : USize) (hfit : GroupFits (encode W) i) :
    ∃ W', permute16 (Packed16.ofParams (KoalaBear.width16 F)) (encode W) i = encode W' ∧
      W'.size = W.size ∧
      (∀ l < 8, (lane 16 W' i.toNat l).map KoalaBear.Fast.ringEquiv =
        permute (KoalaBear.width16 _root_.KoalaBear.Field)
          ((lane 16 W i.toNat l).map KoalaBear.Fast.ringEquiv)) ∧
      ∀ k, (k < i.toNat ∨ i.toNat + 8 * 16 ≤ k) → W'.getD k 0 = W.getD k 0 := by
  obtain ⟨W', e, hs, hl, ho⟩ := permute16_spec (KoalaBear.width16 F) rfl rfl rfl rfl W i hfit
  exact ⟨W', e, hs, fun l hl' ↦ by rw [hl l hl', KoalaBear.fast_width16], ho⟩

end CompStark.Poseidon2.Packed
