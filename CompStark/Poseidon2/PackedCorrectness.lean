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
open CompPoly.PackedRepr (encode size_encode_uint32)
open CompPoly.CPolynomial.NTTFast.Packed (size_encode_fields add_val sub_val
  Native.encodeFields_eq)
open CompPoly.CPolynomial.NTTFast.Packed.Native (readUOffset_encode readUOffset_encodeWords
  usize_numeral)
open CompPoly.CPolynomial.NTTFast.Packed (ofWord ofWord_val reduceOnce encode_eq_map_val
  getD_map_val)

local notation "F" => KoalaBear.Fast.Field

/-- The rows of a width-16 partial round: `V_j · x + sum` for the width-16 diagonal `V`, as
`partial16` computes them, coordinate `0` as `rest - y = -2 y + (y + rest)`. -/
def partialRows16 (c : F) (W : Array F) (i : Nat) : List (Nat → F) :=
  let x (j l : Nat) := word W i j l
  let r (l : Nat) := restSum [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] W i l
  let s (l : Nat) := rowSum [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] c W i l
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
   fun l ↦ s l + x 10 l * invPow2 3,
   fun l ↦ s l + x 11 l * invPow2 24,
   fun l ↦ s l - x 12 l * invPow2 8,
   fun l ↦ s l - x 13 l * invPow2 3,
   fun l ↦ s l - x 14 l * invPow2 4,
   fun l ↦ s l - x 15 l * invPow2 24]

/-- The model of `partial16`. -/
def partialModel16 (c : F) (W : Array F) (i : Nat) : Array F :=
  spliceList coords16 W i (partialRows16 c W i)

/-- A word below `2 p` reduced once, as a field element. -/
def red (u : UInt32) : F := ofWord _ (reduceOnce KoalaBear.fieldSize u)

theorem reduceOnce_eq_red (u : UInt32) (h : u.toNat < 2 * 2130706433) :
    reduceOnce KoalaBear.fieldSize u = (red u).val := by
  have hp : (reduceOnce KoalaBear.fieldSize u).toNat < KoalaBear.fieldSize := by
    rw [CompPoly.CPolynomial.NTTFast.Packed.reduceOnce_eq]
    split <;> rename_i hu
    · exact hu
    · simp only [UInt32.lt_iff_toNat_lt] at hu
      have : (Montgomery.Native32.Mont32Field.modulus32
        (modulus := KoalaBear.fieldSize)).toNat = 2130706433 := rfl
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)]
      change _ < 2130706433
      omega
  simp only [red, ofWord, hp, ↓reduceDIte]

/-- The words of the S-box kernel: the cubes of the group, below `2 p`, and the other words. -/
def sboxWords (cs : List Nat) (rc W : Array F) (r i : Nat) : Array UInt32 :=
  spliceRows cs (W.map Subtype.val) i fun j l ↦ cubeLazy (word W i j l + rc.getD (r + j) 0).val

/-- A packed field array, as the words of its encoding. -/
theorem touch8_encode_words (W : Array F) (i : USize) (h) :
    touch8 (encode W) i h = ⟨encode (W.map Subtype.val), by rw [← encode_eq_map_val]⟩ := by
  rw [touch8_encode]
  apply Subtype.ext
  exact encode_eq_map_val W

/-! ### Kernels -/

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem sbox16_encode (rc W : Array F) (r i : USize) (hb) (hr) :
    (sbox16 (encode rc) r (encode W) i hb hr).1 =
      encode (sboxWords coords16 rc W r.toNat i.toNat) := by
  have hs := hb
  simp only [GroupFits, Fits, size_encode_fields] at hs
  unfold sbox16
  simp only [touch8_encode_words, readUOffset_encodeWords, getD_map_val, readUOffset_encode,
    add_val, USize.reduceToNat]
  simp (disch := (simp only [USize.reduceToNat, size_encode_uint32, Array.size_map]; omega)) only
    [store8_encodeWords]
  simp only [USize.reduceToNat, sboxWords, spliceRows, word, coords16, lit8, List.foldl_cons,
    List.foldl_nil, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]

/-- The words `mat4` writes on a group of words below `2 p`. -/
def mat4Words (cs : List Nat) (U : Array UInt32) (i : Nat) : Array UInt32 :=
  spliceRows cs U i fun j l ↦
    (mat4Word (red (word U i (4 * (j / 4)) l)) (red (word U i (4 * (j / 4) + 1) l))
      (red (word U i (4 * (j / 4) + 2) l)) (red (word U i (4 * (j / 4) + 3) l)) (j % 4)).val

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem mat4x16_encodeWords (U : Array UInt32) (i : USize) (hb)
    (hU : ∀ k, (U.getD k 0).toNat < 2 * 2130706433) :
    (mat4x16 (encode U) i hb).1 = encode (mat4Words coords16 U i.toNat) := by
  have hs := hb
  simp only [GroupFits, Fits, size_encode_uint32] at hs
  unfold mat4x16
  simp only [touch8_encodeWords, readUOffset_encodeWords, USize.reduceToNat]
  simp (disch := exact hU _) only [reduceOnce_eq_red]
  simp only [add_val]
  simp (disch := (simp only [USize.reduceToNat, size_encode_uint32]; omega)) only
    [store8_encodeWords]
  simp only [USize.reduceToNat, mat4Words, spliceRows, word, coords16, lit8, List.foldl_cons,
    List.foldl_nil, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.add_zero,
    mat4Word]

/-- A canonical word reduced once is its field element. -/
theorem red_val (x : F) : red x.val = x := by
  rw [red, reduceOnce_val, ofWord_val]

/-- The words of a packed field array are below `2 p`. -/
theorem map_val_lt (W : Array F) (k : Nat) :
    ((W.map Subtype.val).getD k 0).toNat < 2 * 2130706433 := by
  rw [getD_map_val]
  have := (W.getD k 0).property
  change _ < 2130706433 at this
  omega

/-- The words of a packed field array reduced are its elements. -/
theorem red_word_map (W : Array F) (i j l : Nat) :
    red (word (W.map Subtype.val) i j l) = word W i j l := by
  rw [word, getD_map_val, red_val]

section Words
variable {t : Nat} {cs : List Nat} (hc : Coords t cs)
include hc

/-- The S-box words are below `2 p`. -/
theorem sboxWords_lt (rc W : Array F) (r i : Nat) (hW : i + 8 * t ≤ W.size) (k : Nat) :
    ((sboxWords cs rc W r i).getD k 0).toNat < 2 * 2130706433 := by
  have hW' : i + 8 * t ≤ (W.map Subtype.val).size := by rw [Array.size_map]; exact hW
  by_cases hk : k < i ∨ i + 8 * t ≤ k
  · rw [sboxWords, getD_spliceRows_outside hc _ _ _ hW' k hk]
    exact map_val_lt W k
  · obtain ⟨j, l, hj, hl, rfl⟩ : ∃ j l, j < t ∧ l < 8 ∧ k = i + (8 * j + l) :=
      ⟨(k - i) / 8, (k - i) % 8, by omega, by omega, by omega⟩
    have e := word_spliceRows hc (W.map Subtype.val) i
      (fun j l ↦ cubeLazy (word W i j l + rc.getD (r + j) 0).val) hW' j hj l hl
    simp only [word] at e
    rw [sboxWords, e]
    exact cubeLazy_lt _

/-- The S-box words reduced are the S-box model. -/
theorem red_word_sboxWords (rc W : Array F) (r i : Nat) (hW : i + 8 * t ≤ W.size) (j : Nat)
    (hj : j < t) (l : Nat) (hl : l < 8) :
    red (word (sboxWords cs rc W r i) i j l) = word (sboxModel cs rc W r i) i j l := by
  have hW' : i + 8 * t ≤ (W.map Subtype.val).size := by rw [Array.size_map]; exact hW
  rw [sboxWords, word_spliceRows hc _ _ _ hW' j hj l hl, sboxModel,
    word_spliceRows hc _ _ _ hW j hj l hl, red, reduceOnce_cubeLazy, ofWord_val]

end Words

/-- `mat4` on the S-box words is `mat4` on the S-box model. -/
theorem encode_mat4Words_sbox16 (rc W : Array F) (r i : Nat) (hW : i + 8 * 16 ≤ W.size) :
    encode (mat4Words coords16 (sboxWords coords16 rc W r i) i) =
      encode (mat4Model coords16 (sboxModel coords16 rc W r i) i) := by
  have hc := coords16_spec
  have hW' : i + 8 * 16 ≤ (W.map Subtype.val).size := by rw [Array.size_map]; exact hW
  have hs1 : (sboxWords coords16 rc W r i).size = (sboxModel coords16 rc W r i).size := by
    rw [sboxWords, size_spliceRows hc _ _ _ hW', sboxModel, size_spliceRows hc _ _ _ hW,
      Array.size_map]
  have hs2 : i + 8 * 16 ≤ (sboxModel coords16 rc W r i).size := by
    rw [sboxModel, size_spliceRows hc _ _ _ hW]; exact hW
  rw [mat4Words, mat4Model, encode_spliceRows_val hc _ _ _ _ hs1 hs2 fun k hk ↦ by
    rw [sboxWords, getD_spliceRows_outside hc _ _ _ hW' k hk, getD_map_val, sboxModel,
      getD_spliceRows_outside hc _ _ _ hW k hk]]
  exact congrArg encode (spliceRows_congr hc _ _ _ _ fun j hj l hl ↦ by
    rw [red_word_sboxWords hc rc W r i hW _ (by omega) l hl,
      red_word_sboxWords hc rc W r i hW _ (by omega) l hl,
      red_word_sboxWords hc rc W r i hW _ (by omega) l hl,
      red_word_sboxWords hc rc W r i hW _ (by omega) l hl])

/-- `mat4` on the words of a packed field array is `mat4` on the array. -/
theorem encode_mat4Words_map16 (W : Array F) (i : Nat) (hW : i + 8 * 16 ≤ W.size) :
    encode (mat4Words coords16 (W.map Subtype.val) i) = encode (mat4Model coords16 W i) := by
  have hc := coords16_spec
  rw [mat4Words, mat4Model, encode_spliceRows_val hc _ _ _ _ (Array.size_map ..) hW
    fun k _ ↦ getD_map_val W k]
  exact congrArg encode (spliceRows_congr hc _ _ _ _ fun j _ l _ ↦ by
    rw [red_word_map, red_word_map, red_word_map, red_word_map])

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem mix16_encode (W : Array F) (i : USize) (hb) :
    (mix16 (encode W) i hb).1 = encode (mixModel coords16 [4, 8, 12] W i.toNat) := by
  have hs := hb
  simp only [GroupFits, Fits, size_encode_fields] at hs
  unfold mix16
  simp only [touch8_encode, readUOffset_encode, add_val, USize.reduceToNat]
  simp (disch := (simp only [USize.reduceToNat, size_encode_fields]; omega)) only [store8_encode']
  simp only [USize.reduceToNat, mixModel, blockSum, spliceRows, word, coords16, lit8,
    List.foldl_cons, List.foldl_nil, Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.add_zero]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem partial16_encode (c : F) (d : ByteArray) (W : Array F) (i : USize) (hb) (hd) :
    (partial16 c.val d (encode W) i hb hd).1 = encode (partialModel16 c W i.toNat) := by
  have hs := hb
  simp only [GroupFits, Fits, size_encode_fields] at hs
  unfold partial16
  simp (disch := decide) only [touch8_encode, readUOffset_encode, add_val, sub_val, cube_val,
    halve_val,
    mulInvPow2_val, USize.reduceToNat, UInt32.reduceToNat]
  simp (disch := (simp only [USize.reduceToNat, size_encode_fields]; omega)) only [store8_encode']
  simp only [USize.reduceToNat, partialModel16, partialRows16, spliceList, rowSum, restSum,
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
    simp only [partialRows16, List.getD_cons_zero, List.getD_cons_succ, rowSum, restSum, cubeAdd,
      treeSum, pairSums, List.map_cons, List.map_nil, List.headD_cons, half, invPow2,
      KoalaBear.diagonal16, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, ↓reduceIte,
      Nat.reduceEqDiff] <;> ring

/-! ### The round loops -/

theorem Buf.val_eq {n : Nat} {s : Buf n} {b : ByteArray} (h : s.1 = b) : ∃ hb, s = ⟨b, hb⟩ :=
  ⟨h ▸ s.2, Subtype.ext h⟩

theorem Buf.of_val {n : Nat} (b : Buf n) (x : { y : ByteArray // y.size = b.1.size }) :
    (Buf.of b x).1 = x.1 := rfl

theorem le_of_room16 {n : Nat} (W : Array F) (i : USize) (hn : (encode W).size = n)
    (h : Room16 n i) : i.toNat + 8 * 16 ≤ W.size := by
  rw [size_encode_fields] at hn
  omega

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
    (hr : Room16 n i) (hU : ∀ k, (U.getD k 0).toNat < 2 * 2130706433)
    (hM : encode (mat4Words coords16 U i.toNat) = encode (mat4Model coords16 X i.toNat))
    (s : Buf n) (hs : s.1 = encode U) :
    (external16 s i hr).1 =
      encode (mixModel coords16 [4, 8, 12] (mat4Model coords16 X i.toNat) i.toNat) := by
  obtain ⟨b, hb⟩ := s
  dsimp only at hs
  subst hs
  obtain ⟨hb1, e⟩ := Buf.val_eq (s := Buf.of ⟨encode U, hb⟩
      (mat4x16 (encode U) i (hr.fits ⟨encode U, hb⟩)))
      ((Buf.of_val _ _).trans ((mat4x16_encodeWords U i _ hU).trans hM))
  unfold external16
  dsimp only
  rw [e, Buf.of_val]
  exact mix16_encode _ i _

/-- The external matrix on a group that holds `S`. -/
theorem external16_holds {n : Nat} (W0 W : Array F) (i : USize) (S : Nat → Vector F 16)
    (h : Holds 16 W0 i.toNat S W) (hr : Room16 n i) (s : Buf n) (hs : s.1 = encode W) :
    ∃ W', (external16 s i hr).1 = encode W' ∧
      Holds 16 W0 i.toNat (fun l ↦ externalLinear (S l)) W' := by
  have hW := le_of_room16 W i (hs ▸ s.2) hr
  exact ⟨_, external16_words (W.map Subtype.val) W i hr (map_val_lt W)
    (encode_mat4Words_map16 W i.toNat hW) s (hs.trans (encode_eq_map_val W)),
    holds_external16 W0 W i.toNat S h hW⟩

theorem toNat_sixteen_mul (k : USize) (hk : k < 4) : (16 * k).toNat = 16 * k.toNat := by
  have hk' := lt_four_toNat hk
  have := USize.le_size
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  rw [USize.toNat_mul, usize_numeral 16 (by decide), hsize]
  exact Nat.mod_eq_of_lt (by omega)

theorem toNat_succ_of_lt_four (k : USize) (hk : k < 4) : (k + 1).toNat = k.toNat + 1 := by
  have hk' := lt_four_toNat hk
  have := USize.le_size
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  rw [USize.toNat_add, USize.toNat_one, hsize, Nat.mod_eq_of_lt (by omega)]

/-- Full rounds `k, …, 3` with the constant rows of `rcW`. -/
theorem fullRoundsGo_holds {n : Nat} (P : Params F 16) (hd : P.degree = 3) (rcW W0 : Array F)
    (hrc : Rows16 (encode rcW)) (i : USize) (hr : Room16 n i) :
    ∀ (m : Nat) (k : USize), 4 - k.toNat = m → ∀ (W : Array F) (S : Nat → Vector F 16),
      Holds 16 W0 i.toNat S W → ∀ s : Buf n, s.1 = encode W →
      ∃ W', (fullRoundsGo (encode rcW) hrc i hr k s).1 = encode W' ∧
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
    have hsz : (sboxModel coords16 rcW W (16 * k.toNat) i.toNat).size = W.size := by
      rw [sboxModel, size_spliceRows coords16_spec _ _ _ hW]
    have hsb : Holds 16 W0 i.toNat (fun l ↦ Vector.ofFn fun j : Fin 16 ↦
        ((S l)[j] + (row 16 rcW (16 * k.toNat))[j]) ^ 3)
        (sboxModel coords16 rcW W (16 * k.toNat) i.toNat) :=
      ⟨by rw [hsz, h.1], fun l hl ↦ by rw [lane_sbox coords16_spec _ _ _ _ hW l hl, h.2.1 l hl],
        fun k' hk' ↦ by
          rw [sboxModel, getD_spliceRows_outside coords16_spec _ _ _ hW k' hk', h.2.2 k' hk']⟩
    have hsz' : i.toNat + 8 * 16 ≤ (sboxModel coords16 rcW W (16 * k.toNat) i.toNat).size := by
      rw [hsz]; exact hW
    have e2 := external16_words (sboxWords coords16 rcW W (16 * k.toNat) i.toNat)
      (sboxModel coords16 rcW W (16 * k.toNat) i.toNat) i hr
      (sboxWords_lt coords16_spec rcW W _ _ hW)
      (encode_mat4Words_sbox16 rcW W _ _ hW)
      (Buf.of ⟨encode W, hb⟩ (sbox16 (encode rcW) (16 * k) (encode W) i (hr.fits ⟨encode W, hb⟩)
        (hrc.fits k hk))) (by rw [Buf.of_val, sbox16_encode, e16])
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
theorem partialRoundsGo_holds {n : Nat} (P : Params F 16) (hd : P.degree = 3)
    (hD : P.diagonal = KoalaBear.diagonal16 F) (W0 : Array F) (i : USize) (hr : Room16 n i)
    (hdf : Fits (Packed16.ofParams P).diagonal 0 15) :
    ∀ (m k : Nat), P.internal.length - k = m → ∀ (W : Array F) (S : Nat → Vector F 16),
      Holds 16 W0 i.toNat S W → ∀ s : Buf n, s.1 = encode W →
      ∃ W', (partialRoundsGo (Packed16.ofParams P) hdf i hr k s).1 = encode W' ∧
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
    have hp : Holds 16 W0 i.toNat (fun l ↦ partialRound P (S l) c)
        (partialModel16 c W i.toNat) := by
      rw [partialModel16_eq]
      refine ⟨by rw [size_spliceRows coords16_spec _ _ _ hW, h.1], fun l hl ↦ ?_, fun k hk ↦ by
        rw [getD_spliceRows_outside coords16_spec _ _ _ hW k hk, h.2.2 k hk]⟩
      rw [← partialModel16_eq, lane_partial16 P hd hD c W i.toNat hW l hl, h.2.1 l hl]
    have hkc : (Packed16.ofParams P).internal[k] = c.val := by
      simp only [Packed16.ofParams, List.getElem_toArray, List.getElem_map, hc]
    have hs1 : (Buf.of ⟨encode W, hb⟩ (partial16 (Packed16.ofParams P).internal[k]
        (Packed16.ofParams P).diagonal (encode W) i (hr.fits ⟨encode W, hb⟩) hdf)).1 =
          encode (partialModel16 c W i.toNat) := by
      rw [Buf.of_val, hkc]
      exact partial16_encode c _ W i _ hdf
    obtain ⟨W', e, h'⟩ := ih (k + 1) (by omega) _ _ hp _ hs1
    refine ⟨W', ?_, ?_⟩
    · rw [partialRoundsGo, dite_eq_left hk]
      exact e
    · refine ⟨h'.1, fun l hl ↦ ?_, h'.2.2⟩
      rw [h'.2.1 l hl, List.drop_eq_getElem_cons hk']
      simp only [List.foldl_cons, hc]

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
  have hK : (Packed16.ofParams P).Fits := by
    simp only [Packed16.Fits, Rows16, Packed16.ofParams, Native.encodeFields_eq,
      size_encode_fields, hsize _ hi, hsize _ ht, Fits, Vector.size_toArray, USize.reduceToNat]
    omega
  have h0 : Holds 16 W i.toNat (fun l ↦ lane 16 W i.toNat l) W :=
    ⟨rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  have hr : Room16 (encode W).size i := hfit
  obtain ⟨W1, e1, h1⟩ := external16_holds W W i _ h0 hr ⟨encode W, rfl⟩ rfl
  obtain ⟨W2, e2, h2⟩ := fullRoundsGo_holds P hd _ W (by
      simpa only [Packed16.ofParams, Native.encodeFields_eq] using hK.1) i hr 4 0 rfl W1 _ h1 _ e1
  obtain ⟨W3, e3, h3⟩ := partialRoundsGo_holds P hd hD W i hr hK.2.2 _ 0 rfl W2 _ h2 _ e2
  obtain ⟨W4, e4, h4⟩ := fullRoundsGo_holds P hd _ W (by
      simpa only [Packed16.ofParams, Native.encodeFields_eq] using hK.2.1) i hr 4 0 rfl W3 _ h3
      _ e3
  refine ⟨W4, ?_, h4.1, fun l hl ↦ ?_, h4.2.2⟩
  · rw [permute16, dite_eq_left ⟨hfit, hK⟩]
    simpa only [Packed16.ofParams, Native.encodeFields_eq] using e4
  · rw [h4.2.1 l hl]
    simp only [USize.toNat_zero, Nat.sub_zero, List.drop_zero, ← List.range_eq_range']
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
