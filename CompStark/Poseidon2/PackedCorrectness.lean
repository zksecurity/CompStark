/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Poseidon2.Packed
public import CompPoly.Univariate.NTTFast.Packed.FieldStorage
import all CompStark.Poseidon2.Packed
import all CompPoly.Univariate.NTTFast.Packed.Native
import CompPoly.Univariate.NTTFast.Packed.StorageLemmas
public import CompStark.Poseidon2.ArithmeticLemmas
public import CompStark.Poseidon2.Map

/-! # Correctness of the packed Poseidon2 rounds -/

@[expose] public section
namespace CompStark.Poseidon2.Packed
open CompPoly.PackedRepr (encode size_encode_uint32)
open CompPoly.CPolynomial.NTTFast.Packed (splice encode_eq_map_val size_encode_fields
  map_val_extract add_val sub_val mul_val)
open CompPoly.CPolynomial.NTTFast.Packed.Native (putWords size_putWords putWords_eq readUOffset
  readUOffset_encode wordOffset_toNat)
open CompPoly.CPolynomial.NTTFast.Packed (Native.encodeFields_eq)

local notation "F" => KoalaBear.Fast.Field

/-- Eight field coordinates stored at word `idx` splice them in. -/
theorem store8_encode {n : Nat} (W : Array F) (hW : (encode W).size = n) (off : USize)
    (idx : Nat) (ho : off.toNat = 4 * idx) (hi : idx + 8 ≤ W.size)
    (x0 x1 x2 x3 x4 x5 x6 x7 : F) (h) :
    (⟨putWords ⟨encode W, hW⟩ off 8 x0.val x1.val x2.val x3.val x4.val x5.val x6.val x7.val
        0 0 0 0 0 0 0 0 h, size_putWords ..⟩ : { x : ByteArray // x.size = n }) =
      ⟨encode (splice W idx #[x0, x1, x2, x3, x4, x5, x6, x7]), by
        rw [← hW, size_encode_fields, size_encode_fields,
          CompPoly.CPolynomial.NTTFast.Packed.size_splice _ _ _ (by exact hi)]⟩ := by
  apply Subtype.ext
  subst hW
  dsimp only
  rw [putWords_eq _ _ 8 (by decide), ho, encode_eq_map_val,
    CompPoly.PackedRepr.replaceAt_encode_uint32,
    encode_eq_map_val]
  congr 1
  have hb : (CompPoly.CPolynomial.NTTFast.Packed.Native.batch x0.val x1.val x2.val x3.val x4.val
      x5.val x6.val x7.val 0 0 0 0 0 0 0 0).extract 0 8 =
      (#[x0, x1, x2, x3, x4, x5, x6, x7] : Array F).map Subtype.val := by
    apply Array.toList_inj.mp
    simp only [Array.toList_extract, Array.toList_map, List.extract_eq_take_drop, List.drop_zero]
    rfl
  simp only [splice, Array.map_append, map_val_extract, Array.size_map, hb]

/-- `store8` on a packed field array splices the eight coordinates in. -/
theorem store8_encode' {n : Nat} (W : Array F) (hW : (encode W).size = n) (i k : USize)
    (hk : 4 * (i.toNat + k.toNat) + 3 < USize.size) (hi : 4 * (i.toNat + k.toNat + 8) ≤ n)
    (x0 x1 x2 x3 x4 x5 x6 x7 : F) (h) :
    store8 ⟨encode W, hW⟩ i k x0.val x1.val x2.val x3.val x4.val x5.val x6.val x7.val h =
      ⟨encode (splice W (i.toNat + k.toNat) #[x0, x1, x2, x3, x4, x5, x6, x7]), by
        rw [← hW, size_encode_fields, size_encode_fields,
          CompPoly.CPolynomial.NTTFast.Packed.size_splice _ _ _ (by
            rw [← hW, size_encode_fields] at hi
            simp only [List.size_toArray, List.length_cons, List.length_nil]
            omega)]⟩ :=
  store8_encode W hW _ _ (wordOffset_toNat i k hk) (by rw [← hW, size_encode_fields] at hi; omega)
    x0 x1 x2 x3 x4 x5 x6 x7 h

/-- Eight values of a function, as an array literal. -/
def lit8 {α : Type} (f : Nat → α) : Array α := #[f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7]

/-- The coordinates of a width-16 state. -/
def coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- Row `j` of the eight states at `i` replaced by `g j 0, …, g j 7`, for every coordinate `j`.
Every kernel computes such a replacement, with `g` reading only the input. -/
def spliceRows (W : Array F) (i : Nat) (g : Nat → Nat → F) : Array F :=
  coords.foldl (fun A j ↦ splice A (i + 8 * j) (lit8 (g j))) W

/-- Coordinate `j` of lane `l` of the eight states at `i`. -/
abbrev word (W : Array F) (i j l : Nat) : F := W.getD (i + (8 * j + l)) 0

/-- The field-array model of `sbox16`: coordinate `j` becomes `(x + c_j) ^ 3`. -/
def sboxModel (rc W : Array F) (r i : Nat) : Array F :=
  spliceRows W i fun j l ↦
    let a := word W i j l + rc.getD (r + j) 0
    a * a * a

/-- `mat4` on coordinates `x0, …, x3` with Plonky3's addition chain; `k` selects the row. -/
def mat4Word (x0 x1 x2 x3 : F) (k : Nat) : F :=
  let t01 := x0 + x1
  let t23 := x2 + x3
  let t0123 := t01 + t23
  let t01123 := t0123 + x1
  let t01233 := t0123 + x3
  match k with
  | 0 => t01123 + t01
  | 1 => t01123 + (x2 + x2)
  | 2 => t01233 + t23
  | _ => t01233 + (x0 + x0)

/-- The field-array model of `mat4x16`. -/
def mat4Model (W : Array F) (i : Nat) : Array F :=
  spliceRows W i fun j l ↦
    mat4Word (word W i (4 * (j / 4)) l) (word W i (4 * (j / 4) + 1) l)
      (word W i (4 * (j / 4) + 2) l) (word W i (4 * (j / 4) + 3) l) (j % 4)

/-- The field-array model of `mix16`: every coordinate plus the sum of its row over the blocks. -/
def mixModel (W : Array F) (i : Nat) : Array F :=
  spliceRows W i fun j l ↦
    word W i j l + (word W i (j % 4) l + word W i (4 + j % 4) l + word W i (8 + j % 4) l +
      word W i (12 + j % 4) l)

/-- Row `j` of the eight states at `i` replaced by `g_j 0, …, g_j 7`, for the row functions
`rows = [g_0, …, g_15]`. -/
def spliceList (W : Array F) (i : Nat) (rows : List (Nat → F)) : Array F :=
  (coords.zip rows).foldl (fun A jg ↦ splice A (i + 8 * jg.1) (lit8 jg.2)) W

/-- `(x + c) ^ 3` as two products. -/
def cubeAdd (c x : F) : F := (x + c) * (x + c) * (x + c)

/-- The sum of lane `l` after the S-box of a partial round. -/
def rowSum (c : F) (W : Array F) (i l : Nat) : F :=
  cubeAdd c (word W i 0 l) + word W i 1 l + word W i 2 l + word W i 3 l + word W i 4 l +
    word W i 5 l + word W i 6 l + word W i 7 l + word W i 8 l + word W i 9 l + word W i 10 l +
    word W i 11 l + word W i 12 l + word W i 13 l + word W i 14 l + word W i 15 l

/-- The rows of a partial round: `V_j · x + sum` for the width-16 diagonal `V`, as `partial16`
computes them. -/
def partialRows (c : F) (W : Array F) (i : Nat) : List (Nat → F) :=
  let x (j l : Nat) := word W i j l
  let s (l : Nat) := rowSum c W i l
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

/-- The field-array model of `partial16`. -/
def partialModel (c : F) (W : Array F) (i : Nat) : Array F :=
  spliceList W i (partialRows c W i)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem sbox16_encode (rc W : Array F) (r i : USize) (hb) (hr) :
    sbox16 (encode rc) r (encode W) i hb hr = encode (sboxModel rc W r.toNat i.toNat) := by
  have hs := hb
  simp only [GroupFits, Fits, size_encode_fields] at hs
  unfold sbox16
  simp only [readUOffset_encode, add_val, mul_val, USize.reduceToNat]
  simp (disch := (simp only [USize.reduceToNat, size_encode_fields]; omega)) only [store8_encode']
  simp only [USize.reduceToNat, sboxModel, spliceRows, word, coords, lit8, List.foldl_cons,
    List.foldl_nil, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem mat4x16_encode (W : Array F) (i : USize) (hb) :
    mat4x16 (encode W) i hb = encode (mat4Model W i.toNat) := by
  have hs := hb
  simp only [GroupFits, Fits, size_encode_fields] at hs
  unfold mat4x16
  simp only [readUOffset_encode, add_val, USize.reduceToNat]
  simp (disch := (simp only [USize.reduceToNat, size_encode_fields]; omega)) only [store8_encode']
  simp only [USize.reduceToNat, mat4Model, spliceRows, word, coords, lit8, List.foldl_cons,
    List.foldl_nil, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.add_zero,
    mat4Word]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem mix16_encode (W : Array F) (i : USize) (hb) :
    mix16 (encode W) i hb = encode (mixModel W i.toNat) := by
  have hs := hb
  simp only [GroupFits, Fits, size_encode_fields] at hs
  unfold mix16
  simp only [readUOffset_encode, add_val, USize.reduceToNat]
  simp (disch := (simp only [USize.reduceToNat, size_encode_fields]; omega)) only [store8_encode']
  simp only [USize.reduceToNat, mixModel, spliceRows, word, coords, lit8, List.foldl_cons,
    List.foldl_nil, Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.add_zero]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem partial16_encode (c : F) (D W : Array F) (i : USize) (hb) (hd) :
    partial16 c.val (encode D) (encode W) i hb hd = encode (partialModel c W i.toNat) := by
  have hs := hb
  simp only [GroupFits, Fits, size_encode_fields] at hs
  unfold partial16
  simp (disch := decide) only [readUOffset_encode, add_val, sub_val, mul_val, halve_val,
    mulInvPow2_val, USize.reduceToNat, UInt32.reduceToNat]
  simp (disch := (simp only [USize.reduceToNat, size_encode_fields]; omega)) only [store8_encode']
  simp only [USize.reduceToNat, partialModel, partialRows, spliceList, rowSum, cubeAdd, word,
    coords, lit8, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil,
    Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, Nat.zero_add]

/-! ### Lanes -/

/-- A fold of row splices: word `(j, l)` holds `g j l` once row `j` is spliced, and the words
outside the group are unchanged. -/
theorem foldl_splice_rows (g : Nat → Nat → F) (i : Nat) (L : List Nat) (hL : ∀ j ∈ L, j < 16) :
    ∀ W : Array F, i + 128 ≤ W.size →
      (L.foldl (fun A j ↦ splice A (i + 8 * j) (lit8 (g j))) W).size = W.size ∧
      (∀ j < 16, ∀ l < 8, (L.foldl (fun A j ↦ splice A (i + 8 * j) (lit8 (g j))) W).getD
        (i + (8 * j + l)) 0 = if j ∈ L then g j l else W.getD (i + (8 * j + l)) 0) ∧
      ∀ k, (k < i ∨ i + 128 ≤ k) →
        (L.foldl (fun A j ↦ splice A (i + 8 * j) (lit8 (g j))) W).getD k 0 = W.getD k 0 := by
  induction L with
  | nil => intro W _; exact ⟨rfl, fun j _ l _ ↦ by simp, fun _ _ ↦ rfl⟩
  | cons a L ih =>
    intro W hW
    have ha := hL a List.mem_cons_self
    have hsz : (lit8 (g a)).size = 8 := rfl
    have hfit : i + 8 * a + (lit8 (g a)).size ≤ W.size := by rw [hsz]; omega
    have hS := CompPoly.CPolynomial.NTTFast.Packed.size_splice W _ _ hfit
    obtain ⟨h1, h2, h3⟩ := ih (fun j hj ↦ hL j (List.mem_cons_of_mem a hj))
      (splice W (i + 8 * a) (lit8 (g a))) (by rw [hS]; exact hW)
    simp only [List.foldl_cons]
    refine ⟨by rw [h1, hS], fun j hj l hl ↦ ?_, fun k hk ↦ ?_⟩
    · rw [h2 j hj l hl, CompPoly.CPolynomial.NTTFast.Packed.getD_splice _ _ _ hfit, hsz]
      by_cases hjL : j ∈ L
      · simp only [hjL, ↓reduceIte, List.mem_cons, or_true]
      · simp only [hjL, ↓reduceIte, List.mem_cons, or_false]
        by_cases hja : j = a
        · subst hja
          have hl' : i + (8 * j + l) - (i + 8 * j) = l := by omega
          simp only [show ¬i + (8 * j + l) < i + 8 * j by omega,
            show i + (8 * j + l) < i + 8 * j + 8 by omega, ↓reduceIte, hl']
          interval_cases l <;> rfl
        · simp only [hja, ↓reduceIte]
          split_ifs <;> first | rfl | omega
    · rw [h3 k hk, CompPoly.CPolynomial.NTTFast.Packed.getD_splice _ _ _ hfit, hsz]
      split_ifs <;> first | rfl | omega

/-- Lane `l` of the eight states at `i`: coordinate `j` is word `i + 8 j + l`. -/
def lane (W : Array F) (i l : Nat) : Vector F 16 := Vector.ofFn fun j ↦ word W i j.val l

theorem coords_lt : ∀ j ∈ coords, j < 16 := by decide

theorem mem_coords (j : Nat) (hj : j < 16) : j ∈ coords := by
  interval_cases j <;> decide

/-- A row splice keeps the size. -/
theorem size_spliceRows (W : Array F) (i : Nat) (g : Nat → Nat → F) (hW : i + 128 ≤ W.size) :
    (spliceRows W i g).size = W.size :=
  (foldl_splice_rows g i coords coords_lt W hW).1

/-- After a row splice, lane `l` is `g · l`. -/
theorem lane_spliceRows (W : Array F) (i : Nat) (g : Nat → Nat → F) (hW : i + 128 ≤ W.size)
    (l : Nat) (hl : l < 8) : lane (spliceRows W i g) i l = Vector.ofFn fun j ↦ g j.val l := by
  ext j hj
  simp only [lane, Vector.getElem_ofFn, word]
  rw [spliceRows, (foldl_splice_rows g i coords coords_lt W hW).2.1 j hj l hl,
    ite_eq_left_of_eq_true _ _ (eq_true (mem_coords j hj))]

/-- A row splice leaves the words outside the group unchanged. -/
theorem getD_spliceRows_outside (W : Array F) (i : Nat) (g : Nat → Nat → F)
    (hW : i + 128 ≤ W.size) (k : Nat) (hk : k < i ∨ i + 128 ≤ k) :
    (spliceRows W i g).getD k 0 = W.getD k 0 :=
  (foldl_splice_rows g i coords coords_lt W hW).2.2 k hk

/-- The partial-round model is a row splice of its rows. -/
theorem partialModel_eq (c : F) (W : Array F) (i : Nat) :
    partialModel c W i = spliceRows W i fun j ↦ (partialRows c W i).getD j fun _ ↦ 0 := by
  simp only [partialModel, spliceList, spliceRows, partialRows, coords, List.zip_cons_cons,
    List.zip_nil_right, List.foldl_cons, List.foldl_nil, List.getD_cons_zero,
    List.getD_cons_succ]

/-- After a row splice, word `(j, l)` is `g j l`. -/
theorem word_spliceRows (W : Array F) (i : Nat) (g : Nat → Nat → F) (hW : i + 128 ≤ W.size)
    (j : Nat) (hj : j < 16) (l : Nat) (hl : l < 8) : word (spliceRows W i g) i j l = g j l := by
  rw [word, spliceRows, (foldl_splice_rows g i coords coords_lt W hW).2.1 j hj l hl,
    ite_eq_left_of_eq_true _ _ (eq_true (mem_coords j hj))]

theorem getElem?_lane (W : Array F) (i l k : Nat) (hk : k < 16) :
    (lane W i l)[k]? = some (word W i k l) := by
  simp only [lane, Vector.getElem?_ofFn, hk, ↓reduceDIte]

theorem sum_blocks (f : Nat → F) : ∑ b : Fin (16 / 4), f b.val = f 0 + f 1 + f 2 + f 3 := by
  rw [show 16 / 4 = 4 from rfl, Fin.sum_univ_four]
  rfl

/-- `mat4` then the block-sum mixing is the external matrix, lane by lane. -/
theorem lane_mix_mat4 (W : Array F) (i : Nat) (hW : i + 128 ≤ W.size) (l : Nat) (hl : l < 8) :
    lane (mixModel (mat4Model W i) i) i l = externalLinear (lane W i l) := by
  have hW' : i + 128 ≤ (mat4Model W i).size := by
    rw [mat4Model, size_spliceRows _ _ _ hW]; exact hW
  ext j hj
  simp only [lane, Vector.getElem_ofFn]
  rw [mixModel, word_spliceRows _ _ _ hW' j hj l hl]
  simp only [mat4Model, word_spliceRows _ _ _ hW _ (show j % 4 < 16 by omega) l hl,
    word_spliceRows _ _ _ hW _ (show 4 + j % 4 < 16 by omega) l hl,
    word_spliceRows _ _ _ hW _ (show 8 + j % 4 < 16 by omega) l hl,
    word_spliceRows _ _ _ hW _ (show 12 + j % 4 < 16 by omega) l hl,
    word_spliceRows _ _ _ hW _ hj l hl]
  simp only [externalLinear, Vector.getElem_ofFn]
  rw [sum_blocks fun b ↦ mat4 (Vector.ofFn fun j : Fin 16 ↦ word W i j.val l) b (j % 4)]
  simp only [mat4]
  interval_cases j <;>
    simp (disch := omega) only [Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd,
      Nat.zero_mod, mat4Word, Vector.getElem?_ofFn, Nat.reduceLT, ↓reduceDIte,
      Option.getD_some] <;> ring

/-- The constants `r, …, r + 15` of a table. -/
def row (rc : Array F) (r : Nat) : Vector F 16 := Vector.ofFn fun j ↦ rc.getD (r + j.val) 0

/-- The S-box kernel's lanes. -/
theorem lane_sbox (rc W : Array F) (r i : Nat) (hW : i + 128 ≤ W.size) (l : Nat) (hl : l < 8) :
    lane (sboxModel rc W r i) i l =
      Vector.ofFn fun j : Fin 16 ↦ ((lane W i l)[j] + (row rc r)[j]) ^ 3 := by
  rw [sboxModel, lane_spliceRows _ _ _ hW l hl]
  ext j hj
  simp only [Vector.getElem_ofFn, Fin.getElem_fin, lane, row]
  ring

/-- The S-box kernel then the external matrix is a full round, lane by lane. -/
theorem lane_full (P : Params F 16) (hd : P.degree = 3) (rc W : Array F) (r i : Nat)
    (hW : i + 128 ≤ W.size) (l : Nat) (hl : l < 8) :
    lane (mixModel (mat4Model (sboxModel rc W r i) i) i) i l =
      fullRound P (lane W i l) (row rc r) := by
  have hW' : i + 128 ≤ (sboxModel rc W r i).size := by
    rw [sboxModel, size_spliceRows _ _ _ hW]; exact hW
  rw [lane_mix_mat4 _ i hW' l hl, lane_sbox rc W r i hW l hl, fullRound, hd]

/-- A sum over sixteen coordinates, written out. -/
theorem sum16 (g : Nat → F) : ∑ j : Fin 16, g j.val = g 0 + g 1 + g 2 + g 3 + g 4 + g 5 +
    g 6 + g 7 + g 8 + g 9 + g 10 + g 11 + g 12 + g 13 + g 14 + g 15 := by
  rw [Fin.sum_univ_eq_sum_range g 16]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

/-- The partial-round kernel is a partial round, lane by lane, for the width-16 diagonal. -/
theorem lane_partial (P : Params F 16) (hd : P.degree = 3)
    (hD : P.diagonal = KoalaBear.diagonal16 F) (c : F) (W : Array F) (i : Nat)
    (hW : i + 128 ≤ W.size) (l : Nat) (hl : l < 8) :
    lane (partialModel c W i) i l = partialRound P (lane W i l) c := by
  rw [partialModel_eq, lane_spliceRows _ _ _ hW l hl]
  ext j hj
  simp only [Vector.getElem_ofFn, Fin.getElem_fin, partialRound, internalLinear, hd, hD, lane,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, ↓reduceIte,
    Nat.add_one_ne_zero, add_zero]
  interval_cases j <;>
    simp only [partialRows, List.getD_cons_zero, List.getD_cons_succ, rowSum, cubeAdd, half, invPow2,
      KoalaBear.diagonal16, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, Array.getD_eq_getD_getElem?, ↓reduceIte, Nat.reduceEqDiff] <;> ring

/-! ### The round loops -/

/-- `W` holds the states `S l` in the lanes of the group at `i`, has the size of `W0`, and agrees
with `W0` outside the group. -/
def Holds (W0 : Array F) (i : Nat) (S : Nat → Vector F 16) (W : Array F) : Prop :=
  W.size = W0.size ∧ (∀ l < 8, lane W i l = S l) ∧
    ∀ k, (k < i ∨ i + 128 ≤ k) → W.getD k 0 = W0.getD k 0

theorem groupFits_of_size (W W0 : Array F) (i : USize) (hs : W.size = W0.size)
    (h : GroupFits (encode W0) i) : GroupFits (encode W) i := by
  simp only [GroupFits, Fits, size_encode_fields, hs] at h ⊢
  exact h

theorem le_of_groupFits (W : Array F) (i : USize) (h : GroupFits (encode W) i) :
    i.toNat + 128 ≤ W.size := by
  simp only [GroupFits, Fits, size_encode_fields] at h
  omega

/-- A row splice that computes new lanes keeps `Holds`. -/
theorem holds_spliceRows (W0 W : Array F) (i : Nat) (S S' : Nat → Vector F 16)
    (g : Nat → Nat → F) (h : Holds W0 i S W) (hW : i + 128 ≤ W.size)
    (hl : ∀ l < 8, lane (spliceRows W i g) i l = S' l) : Holds W0 i S' (spliceRows W i g) :=
  ⟨by rw [size_spliceRows _ _ _ hW, h.1], hl, fun k hk ↦ by
    rw [getD_spliceRows_outside _ _ _ hW k hk, h.2.2 k hk]⟩

/-- The external matrix on a group that holds `S`. -/
theorem external16_holds (W0 W : Array F) (i : USize) (S : Nat → Vector F 16)
    (h : Holds W0 i.toNat S W) (hfit : GroupFits (encode W0) i) :
    ∃ W', external16 (encode W) i = encode W' ∧
      Holds W0 i.toNat (fun l ↦ externalLinear (S l)) W' := by
  have hg := groupFits_of_size W W0 i h.1 hfit
  have hW := le_of_groupFits W i hg
  have hs1 : (mat4Model W i.toNat).size = W.size := by rw [mat4Model, size_spliceRows _ _ _ hW]
  have hg1 : GroupFits (encode (mat4Model W i.toNat)) i := groupFits_of_size _ W i hs1 hg
  refine ⟨mixModel (mat4Model W i.toNat) i.toNat, ?_, ?_⟩
  · unfold external16
    rw [dite_eq_left_of_eq_true (eq_true hg), mat4x16_encode,
      dite_eq_left_of_eq_true (eq_true hg1), mix16_encode]
  · have hW1 : i.toNat + 128 ≤ (mat4Model W i.toNat).size := by rw [hs1]; exact hW
    refine ⟨?_, fun l hl ↦ by rw [lane_mix_mat4 W i.toNat hW l hl, h.2.1 l hl], fun k hk ↦ ?_⟩
    · rw [mixModel, size_spliceRows _ _ _ hW1, hs1, h.1]
    · rw [mixModel, getD_spliceRows_outside _ _ _ hW1 k hk, mat4Model,
        getD_spliceRows_outside _ _ _ hW k hk, h.2.2 k hk]

/-- The first `n` full rounds with the constant rows of `rcW`. -/
theorem fullRounds_holds (P : Params F 16) (hd : P.degree = 3) (rcW W0 : Array F) (i : USize)
    (hfit : GroupFits (encode W0) i) (hrc : 4 * rcW.size < USize.size) (n : Nat)
    (hn : 16 * n ≤ rcW.size) (W : Array F) (S : Nat → Vector F 16)
    (h : Holds W0 i.toNat S W) :
    ∃ W', fullRounds (encode rcW) n (encode W) i = encode W' ∧
      Holds W0 i.toNat (fun l ↦ (List.range n).foldl (fun s r ↦ fullRound P s (row rcW (16 * r)))
        (S l)) W' := by
  induction n with
  | zero => exact ⟨W, rfl, h⟩
  | succ n ih =>
    obtain ⟨W1, e1, h1⟩ := ih (by omega)
    have hg := groupFits_of_size W1 W0 i h1.1 hfit
    have hW := le_of_groupFits W1 i hg
    have hr : 4 * (16 * n + 15) + 3 < (encode rcW).size ∧ (encode rcW).size < USize.size := by
      simp only [size_encode_fields]; omega
    have hs : (sboxModel rcW W1 (16 * n) i.toNat).size = W0.size := by
      rw [sboxModel, size_spliceRows _ _ _ hW, h1.1]
    have hsb : Holds W0 i.toNat (fun l ↦ Vector.ofFn fun j : Fin 16 ↦
        (((List.range n).foldl (fun s r ↦ fullRound P s (row rcW (16 * r))) (S l))[j] +
          (row rcW (16 * n))[j]) ^ 3) (sboxModel rcW W1 (16 * n) i.toNat) :=
      ⟨hs, fun l hl ↦ by rw [lane_sbox _ _ _ _ hW l hl, h1.2.1 l hl], fun k hk ↦ by
        rw [sboxModel, getD_spliceRows_outside _ _ _ hW k hk, h1.2.2 k hk]⟩
    obtain ⟨W2, e2, h2⟩ := external16_holds W0 _ i _ hsb hfit
    refine ⟨W2, ?_, ?_⟩
    · unfold fullRounds at e1 ⊢
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
    (h : Holds W0 i.toNat S W) :
    ∃ W', (L.map Subtype.val).foldl (fun b c ↦
        if h : GroupFits b i ∧ Fits (encode P.diagonal.toArray) 0 15 then
          partial16 c (encode P.diagonal.toArray) b i h.1 h.2
        else b) (encode W) = encode W' ∧
      Holds W0 i.toNat (fun l ↦ L.foldl (partialRound P) (S l)) W' := by
  induction L generalizing W S with
  | nil => exact ⟨W, rfl, h⟩
  | cons c L ih =>
    have hg := groupFits_of_size W W0 i h.1 hfit
    have hW := le_of_groupFits W i hg
    have hdf : Fits (encode P.diagonal.toArray) 0 15 := by
      simp only [Fits, size_encode_fields, Vector.size_toArray, USize.reduceToNat]
      have := USize.le_size
      omega
    have hp : Holds W0 i.toNat (fun l ↦ partialRound P (S l) c)
        (partialModel c W i.toNat) := by
      rw [partialModel_eq]
      refine ⟨by rw [size_spliceRows _ _ _ hW, h.1], fun l hl ↦ ?_, fun k hk ↦ by
        rw [getD_spliceRows_outside _ _ _ hW k hk, h.2.2 k hk]⟩
      rw [← partialModel_eq, lane_partial P hd hD c W i.toNat hW l hl, h.2.1 l hl]
    obtain ⟨W', e, h'⟩ := ih _ _ hp
    refine ⟨W', ?_, h'⟩
    rw [List.map_cons, List.foldl_cons, dite_eq_left_of_eq_true (eq_true ⟨hg, hdf⟩),
      partial16_encode, e]

/-- Concatenated rows of sixteen constants. -/
theorem concat_rows (rows : List (Vector F 16)) : ∀ acc : Array F,
    (rows.foldl (fun acc c ↦ acc ++ c.toArray) acc).size = acc.size + 16 * rows.length ∧
      (∀ k < acc.size, (rows.foldl (fun acc c ↦ acc ++ c.toArray) acc).getD k 0 = acc.getD k 0) ∧
      ∀ r < rows.length, ∀ j < 16,
        (rows.foldl (fun acc c ↦ acc ++ c.toArray) acc).getD (acc.size + (16 * r + j)) 0 =
          (rows.getD r 0)[j]?.getD 0 := by
  induction rows with
  | nil =>
    intro acc
    simp only [List.foldl_nil, List.length_nil, mul_zero, add_zero, Array.getD_eq_getD_getElem?,
      implies_true, not_lt_zero, add_lt_iff_neg_left, not_false_eq_true, getElem?_neg,
      Option.getD_none, List.getD_eq_getElem?_getD, IsEmpty.forall_iff, and_self]
  | cons c rows ih =>
    intro acc
    obtain ⟨h1, h2, h3⟩ := ih (acc ++ c.toArray)
    have hs : (acc ++ c.toArray).size = acc.size + 16 := by
      simp only [Array.size_append, Vector.size_toArray]
    simp only [List.foldl_cons, List.length_cons]
    refine ⟨by rw [h1, hs]; ring, fun k hk ↦ ?_, fun r hr j hj ↦ ?_⟩
    · rw [h2 k (by rw [hs]; omega), Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
        Array.getElem?_append_left hk]
    · rcases r with _ | r
      · rw [h2 _ (by rw [hs]; omega), Array.getD_eq_getD_getElem?,
          Array.getElem?_append_right (by omega)]
        simp only [mul_zero, zero_add, add_tsub_cancel_left, Vector.getElem?_toArray,
          List.getD_eq_getElem?_getD, List.length_cons, lt_add_iff_pos_left, Order.lt_add_one_iff,
          zero_le, getElem?_pos, List.getElem_cons_zero, Option.getD_some]
      · rw [show acc.size + (16 * (r + 1) + j) = (acc ++ c.toArray).size + (16 * r + j) by
          rw [hs]; ring, h3 r (by omega) j hj]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ]

/-- Row `r` of concatenated constant rows is constant vector `r`. -/
theorem row_concat (rows : List (Vector F 16)) (r : Nat) (hr : r < rows.length) :
    row (rows.foldl (fun acc c ↦ acc ++ c.toArray) #[]) (16 * r) = rows.getD r 0 := by
  ext j hj
  have h := (concat_rows rows #[]).2.2 r hr j hj
  simp only [Array.size_empty, Nat.zero_add] at h
  simp only [row, Vector.getElem_ofFn, h, Vector.getElem?_eq_getElem hj, Option.getD_some]

/-- Folding over the indices of a list is folding over the list. -/
theorem foldl_range_getD {α β : Type*} (g : α → β → α) (d : β) :
    ∀ (L : List β) (a : α), (List.range L.length).foldl (fun s r ↦ g s (L.getD r d)) a =
      L.foldl g a
  | [], _ => rfl
  | x :: L, a => by
    rw [List.length_cons, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    exact foldl_range_getD g d L (g a x)

/-- Folds over `range n` agree when their steps agree on `0, …, n - 1`. -/
theorem foldl_range_congr {α : Type*} (f g : α → Nat → α) (n : Nat)
    (h : ∀ r < n, ∀ s, f s r = g s r) (a : α) :
    (List.range n).foldl f a = (List.range n).foldl g a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, ih (fun r hr ↦ h r (by omega)),
      List.foldl_cons, List.foldl_cons, List.foldl_nil, List.foldl_nil, h n (by omega)]

/-- The full rounds of the packed loop are the full rounds of the specification. -/
theorem fullRounds_spec (P : Params F 16) (rows : List (Vector F 16)) (hr : rows.length = 4)
    (s : Vector F 16) :
    (List.range 4).foldl (fun s r ↦
        fullRound P s (row (rows.foldl (fun acc c ↦ acc ++ c.toArray) #[]) (16 * r))) s =
      rows.foldl (fullRound P) s := by
  rw [foldl_range_congr _ (fun s r ↦ fullRound P s (rows.getD r 0)) 4
    (fun r hr' s ↦ by rw [row_concat rows r (by omega)]), ← hr]
  exact foldl_range_getD (fullRound P) 0 rows s

/-- **The packed permutation is correct.** On a group of eight states at word `i` of a packed
buffer, `permute16` applies the Poseidon2 permutation to every state, and leaves the rest of the
buffer unchanged. This covers Plonky3's default width-16 instance, `KoalaBear.width16`. -/
theorem permute16_spec (P : Params F 16) (hd : P.degree = 3)
    (hD : P.diagonal = KoalaBear.diagonal16 F) (hi : P.initial.length = 4)
    (ht : P.terminal.length = 4) (W : Array F) (i : USize) (hfit : GroupFits (encode W) i) :
    ∃ W', permute16 (Packed16.ofParams P) (encode W) i = encode W' ∧ W'.size = W.size ∧
      (∀ l < 8, lane W' i.toNat l = permute P (lane W i.toNat l)) ∧
      ∀ k, (k < i.toNat ∨ i.toNat + 128 ≤ k) → W'.getD k 0 = W.getD k 0 := by
  have hsize (rows : List (Vector F 16)) (hr : rows.length = 4) :
      (rows.foldl (fun acc c ↦ acc ++ c.toArray) #[]).size = 64 := by
    rw [(concat_rows rows #[]).1, hr]; rfl
  have hu : 4 * 64 < USize.size := by have := USize.le_size; omega
  have h0 : Holds W i.toNat (fun l ↦ lane W i.toNat l) W := ⟨rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
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
      (∀ l < 8, (lane W' i.toNat l).map KoalaBear.Fast.ringEquiv =
        permute (KoalaBear.width16 _root_.KoalaBear.Field)
          ((lane W i.toNat l).map KoalaBear.Fast.ringEquiv)) ∧
      ∀ k, (k < i.toNat ∨ i.toNat + 128 ≤ k) → W'.getD k 0 = W.getD k 0 := by
  obtain ⟨W', e, hs, hl, ho⟩ := permute16_spec (KoalaBear.width16 F) rfl rfl rfl rfl W i hfit
  exact ⟨W', e, hs, fun l hl' ↦ by rw [hl l hl', fast_width16], ho⟩

end CompStark.Poseidon2.Packed
