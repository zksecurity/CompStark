/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Poseidon2.PackedKernels
import all CompStark.Poseidon2.Packed
import all CompStark.Poseidon2.PackedLanes
import all CompPoly.Univariate.NTTFast.Packed.Native

/-! # Correctness of the packed width-16 Poseidon2

Each kernel of `permute16` refines a model of `PackedLanes` (`PackedKernels`), whose lanes are the
rounds of the specification; the round loops thread `Holds` through them (`permute16_spec`). The
tactics at the end prove a field's generated kernels equal to their models.
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

section Words
variable {t : Nat} {cs : List Nat} (hc : Coords t cs)
include hc

/-- The S-box words are below `2 p`. -/
theorem sboxWords_lt (rc W : Array F) (r i : Nat) (hW : i + 8 * t ≤ W.size) (k : Nat) :
    ((sboxWords K.lazyPow cs rc W r i).getD k 0).toNat < 2 * p := by
  have hW' : i + 8 * t ≤ (W.map Subtype.val).size := by rw [Array.size_map]; exact hW
  by_cases hk : k < i ∨ i + 8 * t ≤ k
  · rw [sboxWords, getD_spliceRows_outside hc _ _ _ hW' k hk]
    exact map_val_lt W k
  · obtain ⟨j, l, hj, hl, rfl⟩ : ∃ j l, j < t ∧ l < 8 ∧ k = i + (8 * j + l) :=
      ⟨(k - i) / 8, (k - i) % 8, by omega, by omega, by omega⟩
    have e := word_spliceRows hc (W.map Subtype.val) i
      (fun j l ↦ K.lazyPow (word W i j l + rc.getD (r + j) 0).val) hW' j hj l hl
    simp only [word] at e
    rw [sboxWords, e]
    exact K.lazyPow_lt _

/-- The S-box words reduced are the S-box model. -/
theorem red_word_sboxWords (rc W : Array F) (r i : Nat) (hW : i + 8 * t ≤ W.size) (j : Nat)
    (hj : j < t) (l : Nat) (hl : l < 8) :
    red p (word (sboxWords K.lazyPow cs rc W r i) i j l) =
      word (sboxModel K.degree cs rc W r i) i j l := by
  have hW' : i + 8 * t ≤ (W.map Subtype.val).size := by rw [Array.size_map]; exact hW
  rw [sboxWords, word_spliceRows hc _ _ _ hW' j hj l hl, sboxModel,
    word_spliceRows hc _ _ _ hW j hj l hl, red, K.reduceOnce_lazyPow, ofWord_val]

end Words

/-- `mat4` on the S-box words is `mat4` on the S-box model. -/
theorem encode_mat4Words_sbox16 (rc W : Array F) (r i : Nat) (hW : i + 8 * 16 ≤ W.size) :
    encode (mat4Words p coords16 (sboxWords K.lazyPow coords16 rc W r i) i) =
      encode (mat4Model coords16 (sboxModel K.degree coords16 rc W r i) i) := by
  have hc := coords16_spec
  have hW' : i + 8 * 16 ≤ (W.map Subtype.val).size := by rw [Array.size_map]; exact hW
  have hs1 : (sboxWords K.lazyPow coords16 rc W r i).size =
      (sboxModel K.degree coords16 rc W r i).size := by
    rw [sboxWords, size_spliceRows hc _ _ _ hW', sboxModel, size_spliceRows hc _ _ _ hW,
      Array.size_map]
  have hs2 : i + 8 * 16 ≤ (sboxModel K.degree coords16 rc W r i).size := by
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
theorem encode_mat4Words_map16 (W : Array F) (i : Nat) (hW : i + 8 * 16 ≤ W.size) :
    encode (mat4Words p coords16 (W.map Subtype.val) i) = encode (mat4Model coords16 W i) := by
  have hc := coords16_spec
  rw [mat4Words, mat4Model, encode_spliceRows_val hc _ _ _ _ (Array.size_map ..) hW
    fun k _ ↦ getD_map_val W k]
  exact congrArg encode (spliceRows_congr hc _ _ _ _ fun j _ l _ ↦ by
    rw [red_word_map, red_word_map, red_word_map, red_word_map])

/-! ### Lanes -/

omit K in
theorem sum_blocks4 (f : Nat → F) : ∑ b : Fin (16 / 4), f b.val = f 0 + f 1 + f 2 + f 3 := by
  rw [show 16 / 4 = 4 from rfl, Fin.sum_univ_four]
  rfl

omit K in
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

omit K in
/-- The S-box kernel then the external matrix is a full round, lane by lane. -/
theorem lane_full16 (P : Params F 16) (rc W : Array F) (r i : Nat)
    (hW : i + 8 * 16 ≤ W.size) (l : Nat) (hl : l < 8) :
    lane 16 (mixModel coords16 [4, 8, 12]
      (mat4Model coords16 (sboxModel P.degree coords16 rc W r i) i) i) i l =
        fullRound P (lane 16 W i l) (row 16 rc r) := by
  have hW' : i + 8 * 16 ≤ (sboxModel P.degree coords16 rc W r i).size := by
    rw [sboxModel, size_spliceRows coords16_spec _ _ _ hW]; exact hW
  rw [lane_mix_mat4_16 _ i hW' l hl, lane_sbox P.degree coords16_spec rc W r i hW l hl, fullRound]

/-! ### The round loops -/

omit K in
theorem Buf.val_eq {n : Nat} {s : Buf n} {b : ByteArray} (h : s.1 = b) : ∃ hb, s = ⟨b, hb⟩ :=
  ⟨h ▸ s.2, Subtype.ext h⟩

omit K in
theorem Buf.of_val {n : Nat} (b : Buf n) (x : { y : ByteArray // y.size = b.1.size }) :
    (Buf.of b x).1 = x.1 := rfl

omit K in
theorem le_of_room16 {n : Nat} (W : Array F) (i : USize) (hn : (encode W).size = n)
    (h : Room16 n i) : i.toNat + 8 * 16 ≤ W.size := by
  rw [size_encode_fields] at hn
  omega

omit K in
/-- `mat4` then the block-sum mixing on a group that holds `S` holds the external matrix of it. -/
theorem holds_external16 (W0 X : Array F) (i : Nat) (S : Nat → Vector F 16)
    (h : Holds 16 W0 i S X) (hX : i + 8 * 16 ≤ X.size) :
    Holds 16 W0 i (fun l ↦ externalLinear (S l))
      (mixModel coords16 [4, 8, 12] (mat4Model coords16 X i) i) := by
  have hs1 : (mat4Model coords16 X i).size = X.size := by
    rw [mat4Model, size_spliceRows coords16_spec _ _ _ hX]
  have hX1 : i + 8 * 16 ≤ (mat4Model coords16 X i).size := by rw [hs1]; exact hX
  refine ⟨?_, fun l hl ↦ by rw [lane_mix_mat4_16 X i hX l hl, h.2.1 l hl], fun k hk ↦ ?_⟩
  · rw [mixModel, size_spliceRows coords16_spec _ _ _ hX1, hs1, h.1]
  · rw [mixModel, getD_spliceRows_outside coords16_spec _ _ _ hX1 k hk, mat4Model,
      getD_spliceRows_outside coords16_spec _ _ _ hX k hk, h.2.2 k hk]

/-- The external matrix on words below `2 p` whose `mat4` is `mat4` on `X`. -/
theorem external16_words {n : Nat} (U : Array UInt32) (X : Array F) (i : USize)
    (hr : Room16 n i) (hU : ∀ k, (U.getD k 0).toNat < 2 * p)
    (hM : encode (mat4Words p coords16 U i.toNat) = encode (mat4Model coords16 X i.toNat))
    (s : Buf n) (hs : s.1 = encode U) :
    (external16 p s i hr).1 =
      encode (mixModel coords16 [4, 8, 12] (mat4Model coords16 X i.toNat) i.toNat) := by
  obtain ⟨b, hb⟩ := s
  dsimp only at hs
  subst hs
  obtain ⟨hb1, e⟩ := Buf.val_eq (s := Buf.of ⟨encode U, hb⟩
      (K.mat4x16 (encode U) i (hr.fits ⟨encode U, hb⟩)))
      ((Buf.of_val _ _).trans ((K.mat4x16_encodeWords U i _ hU).trans hM))
  unfold external16
  dsimp only
  rw [e, Buf.of_val]
  exact K.mix16_encode _ i _

/-- The external matrix on a group that holds `S`. -/
theorem external16_holds {n : Nat} (W0 W : Array F) (i : USize) (S : Nat → Vector F 16)
    (h : Holds 16 W0 i.toNat S W) (hr : Room16 n i) (s : Buf n) (hs : s.1 = encode W) :
    ∃ W', (external16 p s i hr).1 = encode W' ∧
      Holds 16 W0 i.toNat (fun l ↦ externalLinear (S l)) W' := by
  have hW := le_of_room16 W i (hs ▸ s.2) hr
  exact ⟨_, external16_words (W.map Subtype.val) W i hr (map_val_lt W)
    (encode_mat4Words_map16 W i.toNat hW) s (hs.trans (encode_eq_map_val W)),
    holds_external16 W0 W i.toNat S h hW⟩

omit K in
theorem toNat_sixteen_mul (k : USize) (hk : k < 4) : (16 * k).toNat = 16 * k.toNat := by
  have hk' := lt_four_toNat hk
  have := USize.le_size
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  rw [USize.toNat_mul, usize_numeral 16 (by decide), hsize]
  exact Nat.mod_eq_of_lt (by omega)

omit K in
theorem toNat_succ_of_lt_four (k : USize) (hk : k < 4) : (k + 1).toNat = k.toNat + 1 := by
  have hk' := lt_four_toNat hk
  have := USize.le_size
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  rw [USize.toNat_add, USize.toNat_one, hsize, Nat.mod_eq_of_lt (by omega)]

/-- Full rounds `k, …, 3` with the constant rows of `rcW`. -/
theorem fullRoundsGo_holds {n : Nat} (P : Params F 16) (hd : P.degree = K.degree)
    (rcW W0 : Array F)
    (hrc : Rows16 (encode rcW)) (i : USize) (hr : Room16 n i) :
    ∀ (m : Nat) (k : USize), 4 - k.toNat = m → ∀ (W : Array F) (S : Nat → Vector F 16),
      Holds 16 W0 i.toNat S W → ∀ s : Buf n, s.1 = encode W →
      ∃ W', (fullRoundsGo p (encode rcW) hrc i hr k s).1 = encode W' ∧
        Holds 16 W0 i.toNat (fun l ↦ (List.range' k.toNat (4 - k.toNat)).foldl
          (fun s r ↦ fullRound P s (row 16 rcW (16 * r))) (S l)) W' := by
  intro m
  induction m with
  | zero =>
    intro k hm W S h s hs
    have hk : ¬ k < 4 := fun hk ↦ by have := lt_four_toNat hk; omega
    refine ⟨W, ?_, by rw [show 4 - k.toNat = 0 by omega]; exact h⟩
    rw [fullRoundsGo, dite_eq_right hk, hs]
  | succ m ih =>
    intro k hm W S h s hs
    have hk : k < 4 := by
      rw [USize.lt_iff_toNat_lt, usize_numeral 4 (by decide)]; omega
    obtain ⟨b, hb⟩ := s
    dsimp only at hs
    subst hs
    have hW := le_of_room16 W i hb hr
    have e16 : (16 * k).toNat = 16 * k.toNat := toNat_sixteen_mul k hk
    have hsz : (sboxModel K.degree coords16 rcW W (16 * k.toNat) i.toNat).size = W.size := by
      rw [sboxModel, size_spliceRows coords16_spec _ _ _ hW]
    have hsb : Holds 16 W0 i.toNat (fun l ↦ Vector.ofFn fun j : Fin 16 ↦
        ((S l)[j] + (row 16 rcW (16 * k.toNat))[j]) ^ K.degree)
        (sboxModel K.degree coords16 rcW W (16 * k.toNat) i.toNat) :=
      ⟨by rw [hsz, h.1], fun l hl ↦ by
        rw [lane_sbox K.degree coords16_spec _ _ _ _ hW l hl, h.2.1 l hl],
        fun k' hk' ↦ by
          rw [sboxModel, getD_spliceRows_outside coords16_spec _ _ _ hW k' hk', h.2.2 k' hk']⟩
    have hsz' : i.toNat + 8 * 16 ≤
        (sboxModel K.degree coords16 rcW W (16 * k.toNat) i.toNat).size := by
      rw [hsz]; exact hW
    have e2 := external16_words (sboxWords K.lazyPow coords16 rcW W (16 * k.toNat) i.toNat)
      (sboxModel K.degree coords16 rcW W (16 * k.toNat) i.toNat) i hr
      (sboxWords_lt coords16_spec rcW W _ _ hW)
      (encode_mat4Words_sbox16 rcW W _ _ hW)
      (Buf.of ⟨encode W, hb⟩ (K.sbox16 (encode rcW) (16 * k) (encode W) i
        (hr.fits ⟨encode W, hb⟩) (hrc.fits k hk))) (by rw [Buf.of_val, K.sbox16_encode, e16])
    have h2 := holds_external16 W0 _ i.toNat _ hsb hsz'
    obtain ⟨W3, e3, h3⟩ := ih (k + 1) (by rw [toNat_succ_of_lt_four k hk]; omega) _ _ h2 _ e2
    refine ⟨W3, ?_, ?_⟩
    · rw [fullRoundsGo, dite_eq_left hk]
      exact e3
    · refine ⟨h3.1, fun l hl ↦ ?_, h3.2.2⟩
      rw [h3.2.1 l hl, toNat_succ_of_lt_four k hk,
        show 4 - k.toNat = (4 - (k.toNat + 1)) + 1 by omega, List.range'_succ]
      simp only [List.foldl_cons, fullRound, hd]

/-- The partial rounds with the constants `k, …` of `Packed16.ofParams P`. -/
theorem partialRoundsGo_holds {n : Nat} (P : Params F 16) (hd : P.degree = K.degree)
    (hD : P.diagonal = K.diagonal16) (W0 : Array F) (i : USize) (hr : Room16 n i) :
    ∀ (m k : Nat), P.internal.length - k = m → ∀ (W : Array F) (S : Nat → Vector F 16),
      Holds 16 W0 i.toNat S W → ∀ s : Buf n, s.1 = encode W →
      ∃ W', (partialRoundsGo p (Packed16.ofParams P) i hr k s).1 = encode W' ∧
        Holds 16 W0 i.toNat (fun l ↦ (P.internal.drop k).foldl (partialRound P) (S l)) W' := by
  intro m
  induction m with
  | zero =>
    intro k hm W S h s hs
    have hk : ¬ k < (Packed16.ofParams P).internal.size := by
      simp only [Packed16.ofParams, List.size_toArray, List.length_map]; omega
    refine ⟨W, ?_, by rw [List.drop_eq_nil_of_le (by omega)]; exact h⟩
    rw [partialRoundsGo, dite_eq_right hk, hs]
  | succ m ih =>
    intro k hm W S h s hs
    have hk : k < (Packed16.ofParams P).internal.size := by
      simp only [Packed16.ofParams, List.size_toArray, List.length_map]; omega
    have hk' : k < P.internal.length := by omega
    obtain ⟨b, hb⟩ := s
    dsimp only at hs
    subst hs
    have hW := le_of_room16 W i hb hr
    set c := P.internal[k] with hc
    have hkc : (Packed16.ofParams P).internal[k] = c.val := by
      simp only [Packed16.ofParams, List.getElem_toArray, List.getElem_map, hc]
    obtain ⟨W1, e1, hs1, hl1, ho1⟩ := K.partial16_spec P hd hD c W i
      (hr.fits ⟨encode W, hb⟩) hW
    have hp : Holds 16 W0 i.toNat (fun l ↦ partialRound P (S l) c) W1 :=
      ⟨by rw [hs1, h.1], fun l hl ↦ by rw [hl1 l hl, h.2.1 l hl], fun k hk ↦ by
        rw [ho1 k hk, h.2.2 k hk]⟩
    have hs2 : (Buf.of ⟨encode W, hb⟩ (K.partial16 (Packed16.ofParams P).internal[k]
        (encode W) i (hr.fits ⟨encode W, hb⟩))).1 = encode W1 := by
      rw [Buf.of_val, hkc]
      exact e1
    obtain ⟨W', e, h'⟩ := ih (k + 1) (by omega) _ _ hp _ hs2
    refine ⟨W', ?_, ?_⟩
    · rw [partialRoundsGo, dite_eq_left hk]
      exact e
    · refine ⟨h'.1, fun l hl ↦ ?_, h'.2.2⟩
      rw [h'.2.1 l hl, List.drop_eq_getElem_cons hk']
      simp only [List.foldl_cons, hc]

/-- **The packed permutation is correct.** On a group of eight states at word `i` of a packed
buffer, `permute16` applies the Poseidon2 permutation to every state, and leaves the rest of the
buffer unchanged, for every instance of the kernels' S-box degree and internal diagonal with four
initial and four terminal full rounds. -/
theorem permute16_spec (P : Params F 16) (hd : P.degree = K.degree)
    (hD : P.diagonal = K.diagonal16) (hi : P.initial.length = 4)
    (ht : P.terminal.length = 4) (W : Array F) (i : USize) (hfit : GroupFits (encode W) i) :
    ∃ W', permute16 p (Packed16.ofParams P) (encode W) i = encode W' ∧ W'.size = W.size ∧
      (∀ l < 8, lane 16 W' i.toNat l = permute P (lane 16 W i.toNat l)) ∧
      ∀ k, (k < i.toNat ∨ i.toNat + 8 * 16 ≤ k) → W'.getD k 0 = W.getD k 0 := by
  have hsize (rows : List (Vector F 16)) (hr : rows.length = 4) :
      (rows.foldl (fun acc c ↦ acc ++ c.toArray) #[]).size = 64 := by
    rw [(concat_rows rows #[]).1, hr]; rfl
  have hu : 4 * 64 < USize.size := by have := USize.le_size; omega
  have hK : (Packed16.ofParams P).Fits := by
    simp only [Packed16.Fits, Rows16, Packed16.ofParams, Native.encodeFields_eq,
      size_encode_fields, hsize _ hi, hsize _ ht]
    omega
  have h0 : Holds 16 W i.toNat (fun l ↦ lane 16 W i.toNat l) W :=
    ⟨rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  have hr : Room16 (encode W).size i := hfit
  obtain ⟨W1, e1, h1⟩ := external16_holds W W i _ h0 hr ⟨encode W, rfl⟩ rfl
  obtain ⟨W2, e2, h2⟩ := fullRoundsGo_holds P hd _ W (by
      simpa only [Packed16.ofParams, Native.encodeFields_eq] using hK.1) i hr 4 0 rfl W1 _ h1 _ e1
  obtain ⟨W3, e3, h3⟩ := partialRoundsGo_holds P hd hD W i hr _ 0 rfl W2 _ h2 _ e2
  obtain ⟨W4, e4, h4⟩ := fullRoundsGo_holds P hd _ W (by
      simpa only [Packed16.ofParams, Native.encodeFields_eq] using hK.2) i hr 4 0 rfl W3 _ h3
      _ e3
  refine ⟨W4, ?_, h4.1, fun l hl ↦ ?_, h4.2.2⟩
  · rw [permute16, dite_eq_left ⟨hfit, hK⟩]
    simpa only [Packed16.ofParams, Native.encodeFields_eq] using e4
  · rw [h4.2.1 l hl]
    simp only [USize.toNat_zero, Nat.sub_zero, List.drop_zero, ← List.range_eq_range']
    rw [fullRounds_spec P _ hi, fullRounds_spec P _ ht]
    rfl

/-! ### The kernels of a field

A field's generated kernels equal their models by unfolding: the tactics below rewrite a kernel's
reads, word arithmetic and stores into field operations and row splices (`p2_sbox_encode`,
`p2_mat4_encode`, `p2_mix_encode`, `p2_partial_encode`, for a kernel `k` with the bounds `hb`),
put the partial-round model in row-splice form (`p2_partialModel_eq`) and close the lanes of a
partial round against the specification (`p2_lane_partial`, after `lane_spliceRows`, with the
hypotheses `hd` on the degree and `hD` on the diagonal), with the field's diagonal tails and
diagonals `ds` unfolded. -/

omit K in
/-- A partial-round kernel whose output is a row splice with the lanes of a partial round meets
`PackedKernels.partial16_spec` and `partial24_spec`. -/
theorem partial_spec_of {t : Nat} {cs : List Nat} (hc : Coords t cs) (P : Params F t) (c : F)
    (W : Array F) (i : Nat) (g : Nat → Nat → F) (hW : i + 8 * t ≤ W.size)
    (hl : ∀ l < 8, lane t (spliceRows cs W i g) i l = partialRound P (lane t W i l) c)
    (b : ByteArray) (hb : b = encode (spliceRows cs W i g)) :
    ∃ W', b = encode W' ∧ W'.size = W.size ∧
      (∀ l < 8, lane t W' i l = partialRound P (lane t W i l) c) ∧
      ∀ k, (k < i ∨ i + 8 * t ≤ k) → W'.getD k 0 = W.getD k 0 :=
  ⟨_, hb, size_spliceRows hc _ _ _ hW, hl, fun k hk ↦ getD_spliceRows_outside hc _ _ _ hW k hk⟩

set_option hygiene false in
macro "p2_sbox_encode" k:ident : tactic => `(tactic| (
  have hs := hb
  simp only [GroupFits, GroupFits24, Fits, CompPoly.CPolynomial.NTTFast.Packed.size_encode_fields]
    at hs
  unfold $k:ident
  simp only [touch8_encode_words,
    CompPoly.CPolynomial.NTTFast.Packed.Native.readUOffset_encodeWords,
    CompPoly.CPolynomial.NTTFast.Packed.getD_map_val,
    CompPoly.CPolynomial.NTTFast.Packed.Native.readUOffset_encode,
    CompPoly.CPolynomial.NTTFast.Packed.add_val, USize.reduceToNat]
  simp (disch := (simp only [USize.reduceToNat, CompPoly.PackedRepr.size_encode_uint32,
    Array.size_map]; omega)) only [store8_encodeWords]
  simp only [USize.reduceToNat, sboxWords, spliceRows, word, coords16, coords24, lit8,
    List.foldl_cons, List.foldl_nil, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]))

set_option hygiene false in
macro "p2_mat4_encode" k:ident : tactic => `(tactic| (
  have hs := hb
  simp only [GroupFits, GroupFits24, Fits, CompPoly.PackedRepr.size_encode_uint32] at hs
  unfold $k:ident
  simp only [touch8_encodeWords, CompPoly.CPolynomial.NTTFast.Packed.Native.readUOffset_encodeWords,
    USize.reduceToNat]
  simp (disch := exact hU _) only [reduceOnce_eq_red]
  simp only [CompPoly.CPolynomial.NTTFast.Packed.add_val]
  simp (disch := (simp only [USize.reduceToNat, CompPoly.PackedRepr.size_encode_uint32]; omega))
    only [store8_encodeWords]
  simp only [USize.reduceToNat, mat4Words, spliceRows, word, coords16, coords24, lit8,
    List.foldl_cons, List.foldl_nil, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
    Nat.add_zero, mat4Word]))

set_option hygiene false in
macro "p2_mix_encode" k:ident : tactic => `(tactic| (
  have hs := hb
  simp only [GroupFits, GroupFits24, Fits, CompPoly.CPolynomial.NTTFast.Packed.size_encode_fields]
    at hs
  unfold $k:ident
  simp only [touch8_encode, CompPoly.CPolynomial.NTTFast.Packed.Native.readUOffset_encode,
    CompPoly.CPolynomial.NTTFast.Packed.add_val, USize.reduceToNat]
  simp (disch := (simp only [USize.reduceToNat,
    CompPoly.CPolynomial.NTTFast.Packed.size_encode_fields]; omega)) only [store8_encode']
  simp only [USize.reduceToNat, mixModel, blockSum, spliceRows, word, coords16, coords24, lit8,
    List.foldl_cons, List.foldl_nil, Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.add_zero]))

set_option hygiene false in
macro "p2_partial_encode" k:ident "[" ds:ident,* "]" : tactic => `(tactic| (
  have hs := hb
  simp only [GroupFits, GroupFits24, Fits, CompPoly.CPolynomial.NTTFast.Packed.size_encode_fields]
    at hs
  unfold $k:ident
  simp (disch := decide) only [touch8_encode,
    CompPoly.CPolynomial.NTTFast.Packed.Native.readUOffset_encode,
    CompPoly.CPolynomial.NTTFast.Packed.add_val, CompPoly.CPolynomial.NTTFast.Packed.sub_val,
    cubeSign_val, pow7Sign_val, halve_val, mulInvPow2_val, USize.reduceToNat, UInt32.reduceToNat]
  simp (disch := (simp only [USize.reduceToNat,
    CompPoly.CPolynomial.NTTFast.Packed.size_encode_fields]; omega)) only [store8_encode']
  simp only [USize.reduceToNat, partialModel, partialRows, tailRows, spliceList, rowSum, restSum,
    treeSum, pairSums, List.map_cons, List.map_nil, List.headD_cons, powAdd, word, coords16,
    coords24, List.tail_cons, List.cons_append, List.nil_append, lit8, List.zip_cons_cons,
    List.zip_nil_right, List.foldl_cons, List.foldl_nil, Nat.reduceMul, Nat.reduceAdd,
    Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, $[$ds:ident],*]))

macro "p2_partialModel_eq" "[" ds:ident,* "]" : tactic => `(tactic| (
  simp only [partialModel, spliceList, spliceRows, partialRows, tailRows, coords16, coords24,
    List.tail_cons, List.cons_append, List.nil_append, List.zip_cons_cons, List.zip_nil_right,
    List.foldl_cons, List.foldl_nil, List.getD_cons_zero, List.getD_cons_succ, $[$ds:ident],*]))

set_option hygiene false in
macro "p2_lane_partial" "[" ds:ident,* "]" : tactic => `(tactic| (
  ext j hj
  simp only [Vector.getElem_ofFn, Fin.getElem_fin, partialRound, internalLinear, hd, hD, lane,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, ↓reduceIte,
    Nat.add_one_ne_zero, add_zero]
  interval_cases j <;>
    simp only [partialRows, tailRows, coords16, coords24, List.tail_cons, List.cons_append,
      List.nil_append, List.getD_cons_zero,
      List.getD_cons_succ, rowSum, restSum, powAdd, treeSum, pairSums, List.map_cons,
      List.map_nil, List.headD_cons, half, invPow2, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, Bool.false_eq_true, ↓reduceIte,
      Nat.reduceEqDiff, $[$ds:ident],*] <;> ring))

end CompStark.Poseidon2.Packed
