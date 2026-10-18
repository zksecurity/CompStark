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

/-! # Lanes of packed Poseidon2 groups

The width-generic part of the correctness of the packed rounds. A group of eight states of
width `t` at word `i` holds coordinate `j` of lane `l` at word `i + 8 j + l` (`word`). Every
round kernel replaces the rows of its group by values that read only its input (`spliceRows`),
so a single lemma gives each kernel's lanes (`lane_spliceRows`) and leaves the words outside the
group unchanged. `Holds` threads lanes through the round loops.
-/

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

/-- Coordinate `j` of lane `l` of the eight states at `i`. -/
abbrev word (W : Array F) (i j l : Nat) : F := W.getD (i + (8 * j + l)) 0

/-- Row `j` of the eight states at `i` replaced by `g j 0, …, g j 7`, for every coordinate `j` of
`cs`. Every kernel computes such a replacement, with `g` reading only the input. -/
def spliceRows (cs : List Nat) (W : Array F) (i : Nat) (g : Nat → Nat → F) : Array F :=
  cs.foldl (fun A j ↦ splice A (i + 8 * j) (lit8 (g j))) W

/-- Lane `l` of the eight states of width `t` at `i`: coordinate `j` is word `i + 8 j + l`. -/
def lane (t : Nat) (W : Array F) (i l : Nat) : Vector F t := Vector.ofFn fun j ↦ word W i j.val l

/-- `cs` lists the coordinates `0, …, t - 1`. -/
structure Coords (t : Nat) (cs : List Nat) : Prop where
  lt : ∀ j ∈ cs, j < t
  mem : ∀ j < t, j ∈ cs

/-- A fold of row splices: word `(j, l)` holds `g j l` once row `j` is spliced, and the words
outside the group are unchanged. -/
theorem foldl_splice_rows (t : Nat) (g : Nat → Nat → F) (i : Nat) (L : List Nat)
    (hL : ∀ j ∈ L, j < t) : ∀ W : Array F, i + 8 * t ≤ W.size →
      (L.foldl (fun A j ↦ splice A (i + 8 * j) (lit8 (g j))) W).size = W.size ∧
      (∀ j < t, ∀ l < 8, (L.foldl (fun A j ↦ splice A (i + 8 * j) (lit8 (g j))) W).getD
        (i + (8 * j + l)) 0 = if j ∈ L then g j l else W.getD (i + (8 * j + l)) 0) ∧
      ∀ k, (k < i ∨ i + 8 * t ≤ k) →
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

section Rows
variable {t : Nat} {cs : List Nat} (hc : Coords t cs)
include hc

/-- A row splice keeps the size. -/
theorem size_spliceRows (W : Array F) (i : Nat) (g : Nat → Nat → F) (hW : i + 8 * t ≤ W.size) :
    (spliceRows cs W i g).size = W.size :=
  (foldl_splice_rows t g i cs hc.lt W hW).1

/-- After a row splice, word `(j, l)` is `g j l`. -/
theorem word_spliceRows (W : Array F) (i : Nat) (g : Nat → Nat → F) (hW : i + 8 * t ≤ W.size)
    (j : Nat) (hj : j < t) (l : Nat) (hl : l < 8) : word (spliceRows cs W i g) i j l = g j l := by
  rw [word, spliceRows, (foldl_splice_rows t g i cs hc.lt W hW).2.1 j hj l hl,
    ite_eq_left_of_eq_true _ _ (eq_true (hc.mem j hj))]

/-- After a row splice, lane `l` is `g · l`. -/
theorem lane_spliceRows (W : Array F) (i : Nat) (g : Nat → Nat → F) (hW : i + 8 * t ≤ W.size)
    (l : Nat) (hl : l < 8) :
    lane t (spliceRows cs W i g) i l = Vector.ofFn fun j ↦ g j.val l := by
  ext j hj
  simp only [lane, Vector.getElem_ofFn]
  exact word_spliceRows hc W i g hW j hj l hl

/-- A row splice leaves the words outside the group unchanged. -/
theorem getD_spliceRows_outside (W : Array F) (i : Nat) (g : Nat → Nat → F)
    (hW : i + 8 * t ≤ W.size) (k : Nat) (hk : k < i ∨ i + 8 * t ≤ k) :
    (spliceRows cs W i g).getD k 0 = W.getD k 0 :=
  (foldl_splice_rows t g i cs hc.lt W hW).2.2 k hk

end Rows

/-! ### Kernel models -/

/-- The model of the S-box kernel: coordinate `j` becomes `(x + c_j) ^ 3`. -/
def sboxModel (cs : List Nat) (rc W : Array F) (r i : Nat) : Array F :=
  spliceRows cs W i fun j l ↦
    let a := word W i j l + rc.getD (r + j) 0
    a * a * a

/-- `mat4` on coordinates `x0, …, x3` with Plonky3's addition chain, except row 2 as
`(t0123 + x2) + 2 x3`; `k` selects the row. -/
def mat4Word (x0 x1 x2 x3 : F) (k : Nat) : F :=
  let t01 := x0 + x1
  let t23 := x2 + x3
  let t0123 := t01 + t23
  let t01123 := t0123 + x1
  let t01233 := t0123 + x3
  match k with
  | 0 => t01123 + t01
  | 1 => t01123 + (x2 + x2)
  | 2 => t0123 + x2 + (x3 + x3)
  | _ => t01233 + (x0 + x0)

/-- The model of the `mat4` kernel. -/
def mat4Model (cs : List Nat) (W : Array F) (i : Nat) : Array F :=
  spliceRows cs W i fun j l ↦
    mat4Word (word W i (4 * (j / 4)) l) (word W i (4 * (j / 4) + 1) l)
      (word W i (4 * (j / 4) + 2) l) (word W i (4 * (j / 4) + 3) l) (j % 4)

/-- The sum of row `k` of lane `l` over the blocks at the offsets `0 :: bs`. -/
def blockSum (bs : List Nat) (W : Array F) (i k l : Nat) : F :=
  bs.foldl (fun acc b ↦ acc + word W i (b + k) l) (word W i k l)

/-- The model of the block-sum mixing kernel, with the block offsets `0 :: bs`. -/
def mixModel (cs bs : List Nat) (W : Array F) (i : Nat) : Array F :=
  spliceRows cs W i fun j l ↦ word W i j l + blockSum bs W i (j % 4) l

/-- Row `j` of the eight states at `i` replaced by `g_j 0, …, g_j 7`, for the coordinates `cs`
and the row functions `rows`. -/
def spliceList (cs : List Nat) (W : Array F) (i : Nat) (rows : List (Nat → F)) : Array F :=
  (cs.zip rows).foldl (fun A jg ↦ splice A (i + 8 * jg.1) (lit8 jg.2)) W

/-- `(x + c) ^ 3` as two products. -/
def cubeAdd (c x : F) : F := (x + c) * (x + c) * (x + c)

/-- Neighbours added pairwise, an odd last term carried. -/
def pairSums : List F → List F
  | a :: b :: rest => (a + b) :: pairSums rest
  | xs => xs

/-- The sum of a list of at most `2 ^ n` terms as a tree of pairwise additions, `n` levels deep. -/
def treeSum : Nat → List F → F
  | 0, xs => xs.headD 0
  | n + 1, xs => treeSum n (pairSums xs)

/-- The sum of lane `l` after the S-box of a partial round: the S-box output plus the tree sum of
the coordinates `ks`. -/
def rowSum (ks : List Nat) (c : F) (W : Array F) (i l : Nat) : F :=
  cubeAdd c (word W i 0 l) + treeSum 5 (ks.map fun j ↦ word W i j l)

/-! ### The round loops -/

/-- `W` holds the states `S l` in the lanes of the width-`t` group at `i`, has the size of `W0`,
and agrees with `W0` outside the group. -/
def Holds (t : Nat) (W0 : Array F) (i : Nat) (S : Nat → Vector F t) (W : Array F) : Prop :=
  W.size = W0.size ∧ (∀ l < 8, lane t W i l = S l) ∧
    ∀ k, (k < i ∨ i + 8 * t ≤ k) → W.getD k 0 = W0.getD k 0

/-- A row splice that computes new lanes keeps `Holds`. -/
theorem holds_spliceRows {t : Nat} {cs : List Nat} (hc : Coords t cs) (W0 W : Array F) (i : Nat)
    (S S' : Nat → Vector F t) (g : Nat → Nat → F) (h : Holds t W0 i S W)
    (hW : i + 8 * t ≤ W.size) (hl : ∀ l < 8, lane t (spliceRows cs W i g) i l = S' l) :
    Holds t W0 i S' (spliceRows cs W i g) :=
  ⟨by rw [size_spliceRows hc _ _ _ hW, h.1], hl, fun k hk ↦ by
    rw [getD_spliceRows_outside hc _ _ _ hW k hk, h.2.2 k hk]⟩

/-- The constants `r, …, r + t - 1` of a table. -/
def row (t : Nat) (rc : Array F) (r : Nat) : Vector F t :=
  Vector.ofFn fun j ↦ rc.getD (r + j.val) 0

/-- Concatenated rows of `t` constants. -/
theorem concat_rows {t : Nat} (rows : List (Vector F t)) : ∀ acc : Array F,
    (rows.foldl (fun acc c ↦ acc ++ c.toArray) acc).size = acc.size + t * rows.length ∧
      (∀ k < acc.size, (rows.foldl (fun acc c ↦ acc ++ c.toArray) acc).getD k 0 = acc.getD k 0) ∧
      ∀ r < rows.length, ∀ j < t,
        (rows.foldl (fun acc c ↦ acc ++ c.toArray) acc).getD (acc.size + (t * r + j)) 0 =
          (rows.getD r 0)[j]?.getD 0 := by
  induction rows with
  | nil =>
    intro acc
    simp only [List.foldl_nil, List.length_nil, mul_zero, add_zero, Array.getD_eq_getD_getElem?,
      implies_true, not_lt_zero, IsEmpty.forall_iff, and_self]
  | cons c rows ih =>
    intro acc
    obtain ⟨h1, h2, h3⟩ := ih (acc ++ c.toArray)
    have hs : (acc ++ c.toArray).size = acc.size + t := by
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
      · rw [show acc.size + (t * (r + 1) + j) = (acc ++ c.toArray).size + (t * r + j) by
          rw [hs]; ring, h3 r (by omega) j hj]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ]

/-- Row `r` of concatenated constant rows is constant vector `r`. -/
theorem row_concat {t : Nat} (rows : List (Vector F t)) (r : Nat) (hr : r < rows.length) :
    row t (rows.foldl (fun acc c ↦ acc ++ c.toArray) #[]) (t * r) = rows.getD r 0 := by
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

/-- The full rounds of a packed loop over concatenated constant rows are the full rounds of the
specification. -/
theorem fullRounds_spec {t : Nat} (P : Params F t) (rows : List (Vector F t))
    (hr : rows.length = 4) (s : Vector F t) :
    (List.range 4).foldl (fun s r ↦
        fullRound P s (row t (rows.foldl (fun acc c ↦ acc ++ c.toArray) #[]) (t * r))) s =
      rows.foldl (fullRound P) s := by
  rw [foldl_range_congr _ (fun s r ↦ fullRound P s (rows.getD r 0)) 4
    (fun r hr' s ↦ by rw [row_concat rows r (by omega)]), ← hr]
  exact foldl_range_getD (fullRound P) 0 rows s

/-- The S-box kernel's lanes. -/
theorem lane_sbox {t : Nat} {cs : List Nat} (hc : Coords t cs) (rc W : Array F) (r i : Nat)
    (hW : i + 8 * t ≤ W.size) (l : Nat) (hl : l < 8) :
    lane t (sboxModel cs rc W r i) i l =
      Vector.ofFn fun j : Fin t ↦ ((lane t W i l)[j] + (row t rc r)[j]) ^ 3 := by
  rw [sboxModel, lane_spliceRows hc _ _ _ hW l hl]
  ext j hj
  simp only [Vector.getElem_ofFn, Fin.getElem_fin, lane, row]
  ring

end CompStark.Poseidon2.Packed
