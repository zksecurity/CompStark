/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Poseidon2.PackedCorrectness
import all CompStark.Poseidon2.Packed
import all CompStark.Poseidon2.PackedLanes
import all CompPoly.Univariate.NTTFast.Packed.Native

/-! # Correctness of the packed width-24 Poseidon2

Each kernel of `permute24` refines a model of `PackedLanes` (`PackedKernels`), whose lanes are the
rounds of the specification; the round loops thread `Holds` through them (`permute24_spec`).
-/

@[expose] public section
namespace CompStark.Poseidon2.Packed
open Montgomery.Native32.Words (Fits Fits.mono Fits.of_size inBounds)
open CompPoly.PackedRepr (encode size_encode_uint32)
open CompPoly.CPolynomial.NTTFast.Packed (size_encode_fields add_val sub_val
  Native.encodeFields_eq)
open CompPoly.CPolynomial.NTTFast.Packed.Native (readUOffset_encode readUOffset_encodeWords
  usize_numeral)
open CompPoly.CPolynomial.NTTFast.Packed (ofWord ofWord_val reduceOnce encode_eq_map_val
  getD_map_val)

variable {p : ℕ} [Montgomery.Native32.Mont32Field p] [K : PackedKernels p]

local notation "F" => Montgomery.Native32.FastField p


/-- `mat4` on the S-box words is `mat4` on the S-box model. -/
theorem encode_mat4Words_sbox24 (rc W : Array F) (r i : Nat) (hW : i + 8 * 24 ≤ W.size) :
    encode (mat4Words p coords24 (sboxWords K.lazyPow coords24 rc W r i) i) =
      encode (mat4Model coords24 (sboxModel K.degree coords24 rc W r i) i) := by
  have hc := coords24_spec
  have hW' : i + 8 * 24 ≤ (W.map Subtype.val).size := by rw [Array.size_map]; exact hW
  have hs1 : (sboxWords K.lazyPow coords24 rc W r i).size =
      (sboxModel K.degree coords24 rc W r i).size := by
    rw [sboxWords, size_spliceRows hc _ _ _ hW', sboxModel, size_spliceRows hc _ _ _ hW,
      Array.size_map]
  have hs2 : i + 8 * 24 ≤ (sboxModel K.degree coords24 rc W r i).size := by
    rw [sboxModel, size_spliceRows hc _ _ _ hW]; exact hW
  rw [mat4Words, mat4Model, encode_spliceRows_val hc _ _ _ _ hs1 hs2 fun k hk ↦ by
    rw [sboxWords, getD_spliceRows_outside hc _ _ _ hW' k hk, getD_map_val, sboxModel,
      getD_spliceRows_outside hc _ _ _ hW k hk]]
  exact congrArg encode (spliceRows_congr hc _ _ _ _ fun j hj l hl ↦ by
    rw [red_word_sboxWords hc rc W r i hW _ (by omega) l hl,
      red_word_sboxWords hc rc W r i hW _ (by omega) l hl,
      red_word_sboxWords hc rc W r i hW _ (by omega) l hl,
      red_word_sboxWords hc rc W r i hW _ (by omega) l hl])

omit K in
/-- `mat4` on the words of a packed field array is `mat4` on the array. -/
theorem encode_mat4Words_map24 (W : Array F) (i : Nat) (hW : i + 8 * 24 ≤ W.size) :
    encode (mat4Words p coords24 (W.map Subtype.val) i) = encode (mat4Model coords24 W i) := by
  have hc := coords24_spec
  rw [mat4Words, mat4Model, encode_spliceRows_val hc _ _ _ _ (Array.size_map ..) hW
    fun k _ ↦ getD_map_val W k]
  exact congrArg encode (spliceRows_congr hc _ _ _ _ fun j _ l _ ↦ by
    rw [red_word_map, red_word_map, red_word_map, red_word_map])

/-! ### Lanes -/

omit K in
theorem sum_blocks6 (f : Nat → F) :
    ∑ b : Fin (24 / 4), f b.val = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  rw [show 24 / 4 = 6 from rfl, Fin.sum_univ_eq_sum_range f 6]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

omit K in
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

omit K in
/-- The S-box kernel then the external matrix is a full round, lane by lane. -/
theorem lane_full24 (P : Params F 24) (rc W : Array F) (r i : Nat)
    (hW : i + 8 * 24 ≤ W.size) (l : Nat) (hl : l < 8) :
    lane 24 (mixModel coords24 [4, 8, 12, 16, 20]
      (mat4Model coords24 (sboxModel P.degree coords24 rc W r i) i) i) i l =
        fullRound P (lane 24 W i l) (row 24 rc r) := by
  have hW' : i + 8 * 24 ≤ (sboxModel P.degree coords24 rc W r i).size := by
    rw [sboxModel, size_spliceRows coords24_spec _ _ _ hW]; exact hW
  rw [lane_mix_mat4_24 _ i hW' l hl, lane_sbox P.degree coords24_spec rc W r i hW l hl, fullRound]


/-! ### The round loops -/

omit K in
theorem le_of_room24 {n : Nat} (W : Array F) (i : USize) (hn : (encode W).size = n)
    (h : Room24 n i) : i.toNat + 8 * 24 ≤ W.size := by
  rw [size_encode_fields] at hn
  omega

omit K in
/-- `mat4` then the block-sum mixing on a group that holds `S` holds the external matrix of it. -/
theorem holds_external24 (W0 X : Array F) (i : Nat) (S : Nat → Vector F 24)
    (h : Holds 24 W0 i S X) (hX : i + 8 * 24 ≤ X.size) :
    Holds 24 W0 i (fun l ↦ externalLinear (S l))
      (mixModel coords24 [4, 8, 12, 16, 20] (mat4Model coords24 X i) i) := by
  have hs1 : (mat4Model coords24 X i).size = X.size := by
    rw [mat4Model, size_spliceRows coords24_spec _ _ _ hX]
  have hX1 : i + 8 * 24 ≤ (mat4Model coords24 X i).size := by rw [hs1]; exact hX
  refine ⟨?_, fun l hl ↦ by rw [lane_mix_mat4_24 X i hX l hl, h.2.1 l hl], fun k hk ↦ ?_⟩
  · rw [mixModel, size_spliceRows coords24_spec _ _ _ hX1, hs1, h.1]
  · rw [mixModel, getD_spliceRows_outside coords24_spec _ _ _ hX1 k hk, mat4Model,
      getD_spliceRows_outside coords24_spec _ _ _ hX k hk, h.2.2 k hk]

/-- The external matrix on words below `2 p` whose `mat4` is `mat4` on `X`. -/
theorem external24_words {n : Nat} (U : Array UInt32) (X : Array F) (i : USize)
    (hr : Room24 n i) (hU : ∀ k, (U.getD k 0).toNat < 2 * p)
    (hM : encode (mat4Words p coords24 U i.toNat) = encode (mat4Model coords24 X i.toNat))
    (s : Buf n) (hs : s.1 = encode U) :
    (external24 p s i hr).1 =
      encode (mixModel coords24 [4, 8, 12, 16, 20] (mat4Model coords24 X i.toNat) i.toNat) := by
  obtain ⟨b, hb⟩ := s
  dsimp only at hs
  subst hs
  obtain ⟨hb1, e⟩ := Buf.val_eq (s := Buf.of ⟨encode U, hb⟩
      (K.mat4x24 (encode U) i (hr.fits ⟨encode U, hb⟩)))
      ((Buf.of_val _ _).trans ((K.mat4x24_encodeWords U i _ hU).trans hM))
  unfold external24
  dsimp only
  rw [e, Buf.of_val]
  exact K.mix24_encode _ i _

/-- The external matrix on a group that holds `S`. -/
theorem external24_holds {n : Nat} (W0 W : Array F) (i : USize) (S : Nat → Vector F 24)
    (h : Holds 24 W0 i.toNat S W) (hr : Room24 n i) (s : Buf n) (hs : s.1 = encode W) :
    ∃ W', (external24 p s i hr).1 = encode W' ∧
      Holds 24 W0 i.toNat (fun l ↦ externalLinear (S l)) W' := by
  have hW := le_of_room24 W i (hs ▸ s.2) hr
  exact ⟨_, external24_words (W.map Subtype.val) W i hr (map_val_lt W)
    (encode_mat4Words_map24 W i.toNat hW) s (hs.trans (encode_eq_map_val W)),
    holds_external24 W0 W i.toNat S h hW⟩

omit K in
theorem toNat_twentyfour_mul (k : USize) (hk : k < 4) : (24 * k).toNat = 24 * k.toNat := by
  have hk' := lt_four_toNat hk
  have := USize.le_size
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  rw [USize.toNat_mul, usize_numeral 24 (by decide), hsize]
  exact Nat.mod_eq_of_lt (by omega)

/-- Full rounds `k, …, 3` with the constant rows of `rcW`. -/
theorem fullRounds24Go_holds {n : Nat} (P : Params F 24) (hd : P.degree = K.degree)
    (rcW W0 : Array F)
    (hrc : Rows24 (encode rcW)) (i : USize) (hr : Room24 n i) :
    ∀ (m : Nat) (k : USize), 4 - k.toNat = m → ∀ (W : Array F) (S : Nat → Vector F 24),
      Holds 24 W0 i.toNat S W → ∀ s : Buf n, s.1 = encode W →
      ∃ W', (fullRounds24Go p (encode rcW) hrc i hr k s).1 = encode W' ∧
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
    have hsz : (sboxModel K.degree coords24 rcW W (24 * k.toNat) i.toNat).size = W.size := by
      rw [sboxModel, size_spliceRows coords24_spec _ _ _ hW]
    have hsb : Holds 24 W0 i.toNat (fun l ↦ Vector.ofFn fun j : Fin 24 ↦
        ((S l)[j] + (row 24 rcW (24 * k.toNat))[j]) ^ K.degree)
        (sboxModel K.degree coords24 rcW W (24 * k.toNat) i.toNat) :=
      ⟨by rw [hsz, h.1], fun l hl ↦ by
        rw [lane_sbox K.degree coords24_spec _ _ _ _ hW l hl, h.2.1 l hl],
        fun k' hk' ↦ by
          rw [sboxModel, getD_spliceRows_outside coords24_spec _ _ _ hW k' hk', h.2.2 k' hk']⟩
    have hsz' : i.toNat + 8 * 24 ≤
        (sboxModel K.degree coords24 rcW W (24 * k.toNat) i.toNat).size := by
      rw [hsz]; exact hW
    have e2 := external24_words (sboxWords K.lazyPow coords24 rcW W (24 * k.toNat) i.toNat)
      (sboxModel K.degree coords24 rcW W (24 * k.toNat) i.toNat) i hr
      (sboxWords_lt coords24_spec rcW W _ _ hW)
      (encode_mat4Words_sbox24 rcW W _ _ hW)
      (Buf.of ⟨encode W, hb⟩ (K.sbox24 (encode rcW) (24 * k) (encode W) i
        (hr.fits ⟨encode W, hb⟩) (hrc.fits k hk))) (by rw [Buf.of_val, K.sbox24_encode, e24])
    have h2 := holds_external24 W0 _ i.toNat _ hsb hsz'
    obtain ⟨W3, e3, h3⟩ := ih (k + 1) (by rw [toNat_succ_of_lt_four k hk]; omega) _ _ h2 _ e2
    refine ⟨W3, ?_, ?_⟩
    · rw [fullRounds24Go, dite_eq_left hk]
      exact e3
    · refine ⟨h3.1, fun l hl ↦ ?_, h3.2.2⟩
      rw [h3.2.1 l hl, toNat_succ_of_lt_four k hk,
        show 4 - k.toNat = (4 - (k.toNat + 1)) + 1 by omega, List.range'_succ]
      simp only [List.foldl_cons, fullRound, hd]

/-- The partial rounds with the constants `k, …` of `Packed24.ofParams P`. -/
theorem partialRounds24Go_holds {n : Nat} (P : Params F 24) (hd : P.degree = K.degree)
    (hD : P.diagonal = K.diagonal24) (W0 : Array F) (i : USize) (hr : Room24 n i) :
    ∀ (m k : Nat), P.internal.length - k = m → ∀ (W : Array F) (S : Nat → Vector F 24),
      Holds 24 W0 i.toNat S W → ∀ s : Buf n, s.1 = encode W →
      ∃ W', (partialRounds24Go p (Packed24.ofParams P) i hr k s).1 = encode W' ∧
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
    have hkc : (Packed24.ofParams P).internal[k] = c.val := by
      simp only [Packed24.ofParams, List.getElem_toArray, List.getElem_map, hc]
    obtain ⟨W1, e1, hs1, hl1, ho1⟩ := K.partial24_spec P hd hD c W i
      (hr.fits ⟨encode W, hb⟩) hW
    have hp : Holds 24 W0 i.toNat (fun l ↦ partialRound P (S l) c) W1 :=
      ⟨by rw [hs1, h.1], fun l hl ↦ by rw [hl1 l hl, h.2.1 l hl], fun k hk ↦ by
        rw [ho1 k hk, h.2.2 k hk]⟩
    have hs2 : (Buf.of ⟨encode W, hb⟩ (K.partial24 (Packed24.ofParams P).internal[k]
        (encode W) i (hr.fits ⟨encode W, hb⟩))).1 = encode W1 := by
      rw [Buf.of_val, hkc]
      exact e1
    obtain ⟨W', e, h'⟩ := ih (k + 1) (by omega) _ _ hp _ hs2
    refine ⟨W', ?_, ?_⟩
    · rw [partialRounds24Go, dite_eq_left hk]
      exact e
    · refine ⟨h'.1, fun l hl ↦ ?_, h'.2.2⟩
      rw [h'.2.1 l hl, List.drop_eq_getElem_cons hk']
      simp only [List.foldl_cons, hc]

/-- **The packed permutation is correct.** On a group of eight states at word `i` of a packed
buffer, `permute24` applies the Poseidon2 permutation to every state, and leaves the rest of the
buffer unchanged, for every instance of the kernels' S-box degree and internal diagonal with four
initial and four terminal full rounds. -/
theorem permute24_spec (P : Params F 24) (hd : P.degree = K.degree)
    (hD : P.diagonal = K.diagonal24) (hi : P.initial.length = 4)
    (ht : P.terminal.length = 4) (W : Array F) (i : USize) (hfit : GroupFits24 (encode W) i) :
    ∃ W', permute24 p (Packed24.ofParams P) (encode W) i = encode W' ∧ W'.size = W.size ∧
      (∀ l < 8, lane 24 W' i.toNat l = permute P (lane 24 W i.toNat l)) ∧
      ∀ k, (k < i.toNat ∨ i.toNat + 8 * 24 ≤ k) → W'.getD k 0 = W.getD k 0 := by
  have hsize (rows : List (Vector F 24)) (hr : rows.length = 4) :
      (rows.foldl (fun acc c ↦ acc ++ c.toArray) #[]).size = 96 := by
    rw [(concat_rows rows #[]).1, hr]; rfl
  have hu : 4 * 96 < USize.size := by have := USize.le_size; omega
  have hK : (Packed24.ofParams P).Fits := by
    simp only [Packed24.Fits, Rows24, Packed24.ofParams, Native.encodeFields_eq,
      size_encode_fields, hsize _ hi, hsize _ ht]
    omega
  have h0 : Holds 24 W i.toNat (fun l ↦ lane 24 W i.toNat l) W :=
    ⟨rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  have hr : Room24 (encode W).size i := hfit
  obtain ⟨W1, e1, h1⟩ := external24_holds W W i _ h0 hr ⟨encode W, rfl⟩ rfl
  obtain ⟨W2, e2, h2⟩ := fullRounds24Go_holds P hd _ W (by
      simpa only [Packed24.ofParams, Native.encodeFields_eq] using hK.1) i hr 4 0 rfl W1 _ h1 _ e1
  obtain ⟨W3, e3, h3⟩ := partialRounds24Go_holds P hd hD W i hr _ 0 rfl W2 _ h2 _ e2
  obtain ⟨W4, e4, h4⟩ := fullRounds24Go_holds P hd _ W (by
      simpa only [Packed24.ofParams, Native.encodeFields_eq] using hK.2) i hr 4 0 rfl W3 _ h3
      _ e3
  refine ⟨W4, ?_, h4.1, fun l hl ↦ ?_, h4.2.2⟩
  · rw [permute24, dite_eq_left ⟨hfit, hK⟩]
    simpa only [Packed24.ofParams, Native.encodeFields_eq] using e4
  · rw [h4.2.1 l hl]
    simp only [USize.toNat_zero, Nat.sub_zero, List.drop_zero, ← List.range_eq_range']
    rw [fullRounds_spec P _ hi, fullRounds_spec P _ ht]
    rfl

end CompStark.Poseidon2.Packed
