/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Merkle.Packed
public import CompStark.Merkle.Tree
public import CompStark.Plonky3.Hash
public import CompStark.Poseidon2.PackedCorrectness
import all CompStark.Merkle.Packed
import all CompPoly.Univariate.NTTFast.Packed.Native
import CompPoly.Univariate.NTTFast.Packed.ArrayLemmas

/-! # Correctness of the packed Merkle commitment -/

@[expose] public section
namespace CompStark.Merkle.Packed
open CompStark.Poseidon2 CompStark.Poseidon2.Packed Montgomery.Native32
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTTFast.Packed (size_encode_fields array_eq_of_getD getD_ofFn_bounded)
open CompPoly.CPolynomial.NTTFast.Packed.Native (readUOffset_encode)

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p

/-- Lines `q 0, …, q 7` of sixteen coordinates of `M` as rows `0, …, 15` of the group at `i`. -/
def loadModel (M W : Array F) (q : Nat → Nat) (i : Nat) : Array F :=
  spliceRows coords16 W i fun j l ↦ M.getD (q l + j) 0

/-- The digests in coordinates `0, …, 7` of the lanes of the group at `i` of `S`, as digests at
words `dst 0, …, dst 7` of `O`. -/
def storeModel (S O : Array F) (i : Nat) (dst : Nat → Nat) : Array F :=
  [0, 1, 2, 3, 4, 5, 6, 7].foldl (fun A l ↦ CompPoly.CPolynomial.NTTFast.Packed.splice A (dst l)
    (lit8 fun j ↦ word S i j l)) O

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem load16x24_encode (M W : Array F) (q : Nat → Nat) (hq : ∀ l < 8, q l < USize.size)
    (i : USize) (h0 h1 h2 h3 h4 h5 h6 h7 hb) :
    load16x24 (encode M) (q 0).toUSize (q 1).toUSize (q 2).toUSize (q 3).toUSize (q 4).toUSize
      (q 5).toUSize (q 6).toUSize (q 7).toUSize (encode W) i h0 h1 h2 h3 h4 h5 h6 h7 hb =
      encode (loadModel M W q i.toNat) := by
  have hs := hb
  simp only [GroupFits24, Fits, size_encode_fields] at hs
  have hu (l : Nat) (hl : l < 8) : (q l).toUSize.toNat = q l := USize.toNat_ofNat_of_lt' (hq l hl)
  unfold load16x24
  simp only [readUOffset_encode, USize.reduceToNat, hu 0 (by decide), hu 1 (by decide),
    hu 2 (by decide), hu 3 (by decide), hu 4 (by decide), hu 5 (by decide), hu 6 (by decide),
    hu 7 (by decide)]
  simp (disch := (simp only [USize.reduceToNat, size_encode_fields]; omega)) only [store8_encode']
  simp only [USize.reduceToNat, loadModel, spliceRows, coords16, lit8, List.foldl_cons,
    List.foldl_nil, Nat.reduceMul, Nat.add_zero]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem load16x16_encode (M W : Array F) (q : Nat → Nat) (hq : ∀ l < 8, q l < USize.size)
    (i : USize) (h0 h1 h2 h3 h4 h5 h6 h7 hb) :
    load16x16 (encode M) (q 0).toUSize (q 1).toUSize (q 2).toUSize (q 3).toUSize (q 4).toUSize
      (q 5).toUSize (q 6).toUSize (q 7).toUSize (encode W) i h0 h1 h2 h3 h4 h5 h6 h7 hb =
      encode (loadModel M W q i.toNat) := by
  have hs := hb
  simp only [GroupFits, Fits, size_encode_fields] at hs
  have hu (l : Nat) (hl : l < 8) : (q l).toUSize.toNat = q l := USize.toNat_ofNat_of_lt' (hq l hl)
  unfold load16x16
  simp only [readUOffset_encode, USize.reduceToNat, hu 0 (by decide), hu 1 (by decide),
    hu 2 (by decide), hu 3 (by decide), hu 4 (by decide), hu 5 (by decide), hu 6 (by decide),
    hu 7 (by decide)]
  simp (disch := (simp only [USize.reduceToNat, size_encode_fields]; omega)) only [store8_encode']
  simp only [USize.reduceToNat, loadModel, spliceRows, coords16, lit8, List.foldl_cons,
    List.foldl_nil, Nat.reduceMul, Nat.add_zero]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem store8x8_encode (S O : Array F) (i : USize) (dst : Nat → Nat)
    (hdst : ∀ l < 8, dst l < USize.size) (hb g0 g1 g2 g3 g4 g5 g6 g7) :
    store8x8 (encode S) i (encode O) (dst 0).toUSize (dst 1).toUSize (dst 2).toUSize (dst 3).toUSize
      (dst 4).toUSize (dst 5).toUSize (dst 6).toUSize (dst 7).toUSize hb g0 g1 g2 g3 g4 g5 g6 g7 =
      encode (storeModel S O i.toNat dst) := by
  have hu (l : Nat) (hl : l < 8) : (dst l).toUSize.toNat = dst l := USize.toNat_ofNat_of_lt' (hdst
      l hl)
  have f0 := g0; have f1 := g1; have f2 := g2; have f3 := g3
  have f4 := g4; have f5 := g5; have f6 := g6; have f7 := g7
  simp only [Fits, size_encode_fields, hu 0 (by decide), hu 1 (by decide), hu 2 (by decide),
    hu 3 (by decide), hu 4 (by decide), hu 5 (by decide), hu 6 (by decide),
    hu 7 (by decide)] at f0 f1 f2 f3 f4 f5 f6 f7
  unfold store8x8
  simp only [readUOffset_encode, USize.reduceToNat]
  simp (disch := (simp only [USize.reduceToNat, size_encode_fields, hu 0 (by decide),
    hu 1 (by decide), hu 2 (by decide), hu 3 (by decide), hu 4 (by decide), hu 5 (by decide),
    hu 6 (by decide), hu 7 (by decide)]; omega)) only [store8_encode']
  simp only [USize.reduceToNat, storeModel, lit8, word, List.foldl_cons, List.foldl_nil,
    Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, hu 0 (by decide), hu 1 (by decide),
    hu 2 (by decide), hu 3 (by decide), hu 4 (by decide), hu 5 (by decide), hu 6 (by decide),
    hu 7 (by decide)]

/-- `X` with words `8 j + l` replaced by `v j` for `j < J`. -/
def setColumn (X : Array F) (l J : Nat) (v : Nat → F) : Array F :=
  Array.ofFn (n := X.size) fun k ↦
    if k.val % 8 = l ∧ k.val / 8 < J then v (k.val / 8) else X.getD k.val 0

theorem getD_setColumn (X : Array F) (l J : Nat) (v : Nat → F) (k : Nat) :
    (setColumn X l J v).getD k 0 =
      if k < X.size ∧ k % 8 = l ∧ k / 8 < J then v (k / 8) else X.getD k 0 := by
  by_cases hk : k < X.size
  · simp only [setColumn, getD_ofFn_bounded _ _ hk, hk, true_and]
  · simp only [hk, false_and, ↓reduceIte, Array.getD_eq_getD_getElem?]
    rw [Array.getElem?_eq_none (by simp only [setColumn, Array.size_ofFn]; omega),
      Array.getElem?_eq_none (by omega)]

theorem writes_column (l J : Nat) (v : Nat → F) (hl : l < 8) :
    ∀ X : Array F, 8 * J ≤ X.size → 4 * X.size < USize.size →
      (List.range J).foldl (fun st j ↦
        CompPoly.CPolynomial.NTTFast.Packed.Native.write st (8 * j + l) (v j).val) (encode X) =
        encode (setColumn X l J v) := by
  induction J with
  | zero =>
    intro X _ _
    rw [List.range_zero, List.foldl_nil]
    congr 1
    apply array_eq_of_getD _ _ 0 (by simp only [setColumn, Array.size_ofFn])
    intro k
    rw [getD_setColumn]
    simp only [Nat.not_lt_zero, and_false, ↓reduceIte]
  | succ J ih =>
    intro X hX hu
    have hs : (setColumn X l J v).size = X.size := by simp only [setColumn, Array.size_ofFn]
    rw [List.range_succ, List.foldl_append, ih X (by omega) hu, List.foldl_cons, List.foldl_nil,
      CompPoly.CPolynomial.NTTFast.Packed.Native.write_encode _ _
        (by rw [size_encode_fields, hs]; exact hu) (by rw [hs]; omega)]
    congr 1
    apply array_eq_of_getD _ _ 0 (by simp only [setColumn, Array.size_ofFn,
      Array.size_setIfInBounds])
    intro k
    rw [CompPoly.CPolynomial.NTTFast.Packed.getD_setIfInBounds _ _ _ _ _ (by rw [hs]; omega),
      getD_setColumn, getD_setColumn]
    by_cases hkJ : k = 8 * J + l
    · subst hkJ
      have h1 : (8 * J + l) % 8 = l := by omega
      have h2 : (8 * J + l) / 8 = J := by omega
      simp only [↓reduceIte, h1, h2, Nat.lt_succ_self, and_true,
        show 8 * J + l < X.size by omega]
    · simp only [hkJ, ↓reduceIte]
      by_cases hc : k < X.size ∧ k % 8 = l ∧ k / 8 < J
      · simp only [hc, and_self, ↓reduceIte, show k / 8 < J + 1 by omega]
      · have : ¬(k < X.size ∧ k % 8 = l ∧ k / 8 < J + 1) := by omega
        simp only [hc, this, ↓reduceIte]

theorem ite_pure_yield {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then pure (ForInStep.yield a) else pure (ForInStep.yield b) : Id (ForInStep β)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

theorem foldl_congr_mem {α β : Type*} (L : List β) (f g : α → β → α)
    (h : ∀ x ∈ L, ∀ a, f a x = g a x) (a : α) : L.foldl f a = L.foldl g a := by
  induction L generalizing a with
  | nil => rfl
  | cons x L ih =>
    rw [List.foldl_cons, List.foldl_cons, h x List.mem_cons_self,
      ih fun y hy ↦ h y (List.mem_cons_of_mem x hy)]

/-- The lanes of a column update. -/
theorem word_setColumn (X : Array F) (l J : Nat) (v : Nat → F) (j l' : Nat) (hl' : l' < 8)
    (hX : 8 * j + l' < X.size) :
    word (setColumn X l J v) 0 j l' = if l' = l ∧ j < J then v j else word X 0 j l' := by
  rw [word, word, Nat.zero_add, getD_setColumn]
  have h1 : (8 * j + l') % 8 = l' := by omega
  have h2 : (8 * j + l') / 8 = j := by omega
  simp only [h1, h2, hX, true_and]

/-- Block `blk` of row `r` of a row-major matrix of width `w`, as a list. -/
def block (M : Array F) (w r blk : Nat) : List F :=
  (List.range (min 16 (w - 16 * blk))).map fun j ↦ M.getD (r * w + 16 * blk + j) 0

theorem getD_block (M : Array F) (w r blk j : Nat) (d : F) :
    (block M w r blk).getD j d =
      if j < min 16 (w - 16 * blk) then M.getD (r * w + 16 * blk + j) 0 else d := by
  simp only [block, List.getD_eq_getElem?_getD, List.getElem?_map]
  split
  · rw [List.getElem?_range (by assumption)]; rfl
  · rw [List.getElem?_eq_none (by simp only [List.length_range]; omega)]; rfl

theorem scatterRows_encode (M A : Array F) (w rows r0 blk : Nat) (hM : rows * w ≤ M.size)
    (hA : 128 ≤ A.size) (hu : 4 * M.size < USize.size) (hu' : 4 * A.size < USize.size) :
    ∃ A', scatterRows (encode M) w rows r0 blk (encode A) = encode A' ∧ A'.size = A.size ∧
      ∀ l < 8, ∀ j, 8 * j + l < A.size → word A' 0 j l =
        if r0 + l < rows ∧ j < min 16 (w - 16 * blk) then M.getD ((r0 + l) * w + 16 * blk + j) 0
        else word A 0 j l := by
  unfold scatterRows
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    bind_pure, pure_bind, ite_pure_yield, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  have key : ∀ L ≤ 8, ∃ A', (List.range L).foldl (fun b a ↦
      if r0 + a < rows then (List.range (min 16 (w - 16 * blk))).foldl (fun b a_1 ↦
        CompPoly.CPolynomial.NTTFast.Packed.Native.write b (8 * a_1 + a)
          (CompPoly.CPolynomial.NTTFast.Packed.Native.read (encode M)
            ((r0 + a) * w + 16 * blk + a_1))) b
      else b) (encode A) = encode A' ∧ A'.size = A.size ∧
      ∀ l < 8, ∀ j, 8 * j + l < A.size → word A' 0 j l =
        if l < L ∧ r0 + l < rows ∧ j < min 16 (w - 16 * blk)
        then M.getD ((r0 + l) * w + 16 * blk + j) 0 else word A 0 j l := by
    intro L hL
    induction L with
    | zero =>
      refine ⟨A, rfl, rfl, fun l _ j _ ↦ ?_⟩
      simp only [Nat.not_lt_zero, false_and, ↓reduceIte]
    | succ L ih =>
      obtain ⟨A1, e1, s1, w1⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, e1, List.foldl_cons, List.foldl_nil]
      by_cases hrow : r0 + L < rows
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hrow)]
        let v (j : Nat) : F := M.getD ((r0 + L) * w + 16 * blk + j) 0
        have hsz : (r0 + L + 1) * w ≤ M.size :=
          Nat.le_trans (Nat.mul_le_mul_right w (by omega)) hM
        rw [Nat.add_mul, Nat.one_mul] at hsz
        have hc : ∀ j ∈ List.range (min 16 (w - 16 * blk)), ∀ b,
            CompPoly.CPolynomial.NTTFast.Packed.Native.write b (8 * j + L)
              (CompPoly.CPolynomial.NTTFast.Packed.Native.read (encode M)
                ((r0 + L) * w + 16 * blk + j)) =
            CompPoly.CPolynomial.NTTFast.Packed.Native.write b (8 * j + L) (v j).val := by
          intro j hj b
          have hj : j < min 16 (w - 16 * blk) := List.mem_range.mp hj
          have hj' : 16 * blk + j < w := by omega
          rw [CompPoly.CPolynomial.NTTFast.Packed.Native.read_encode _ _
            (by rw [size_encode_fields]; exact hu) (by omega)]
        rw [foldl_congr_mem _ _ _ hc]
        rw [writes_column L _ v (by omega) A1 (by omega) (by rw [s1]; exact hu')]
        refine ⟨_, rfl, by rw [setColumn, Array.size_ofFn, s1], fun l hl j hj ↦ ?_⟩
        rw [word_setColumn A1 L _ v j l hl (by omega), w1 l hl j hj]
        by_cases hlL : l = L
        · subst hlL
          simp only [true_and, Nat.lt_succ_self, hrow, v]
          split_ifs <;> first | rfl | omega
        · simp only [hlL, false_and, ↓reduceIte]
          split_ifs <;> first | rfl | omega
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hrow)]
        refine ⟨A1, rfl, s1, fun l hl j hj ↦ ?_⟩
        rw [w1 l hl j hj]
        split_ifs <;> first | rfl | omega
  obtain ⟨A', e, s, wl⟩ := key 8 le_rfl
  refine ⟨A', e, s, fun l hl j hj ↦ ?_⟩
  rw [wl l hl j hj]
  split_ifs <;> first | rfl | omega

theorem absorbBlock_encode (M A : Array F) (w rows r0 blk : Nat) (hM : M.size = rows * w)
    (hA : A.size = 192) (hu : 4 * M.size < USize.size) :
    ∃ A', absorbBlock (encode M) w rows r0 blk (encode A) = encode A' ∧ A'.size = 192 ∧
      ∀ l < 8, lane 24 A' 0 l = if r0 + l < rows then
        CompStark.Hash.overwrite (lane 24 A 0 l) (block M w (r0 + l) blk) else lane 24 A 0 l := by
  unfold absorbBlock
  split
  · rename_i hfull
    obtain ⟨hr, hcnt⟩ := hfull
    have hw : 16 * blk + 16 ≤ w := by omega
    have hq : ∀ l < 8, (r0 + l) * w + 16 * blk + 16 ≤ M.size := fun l hl ↦ by
      have := Nat.mul_le_mul_right w (show r0 + l + 1 ≤ rows by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    have hqu : ∀ l < 8, (r0 + l) * w + 16 * blk < USize.size := fun l hl ↦ by
      have := hq l hl; omega
    have hfit : ∀ l < 8, Fits (encode M) ((r0 + l) * w + 16 * blk).toUSize 15 := fun l hl ↦ by
      have := hq l hl
      simp only [Fits, size_encode_fields, USize.toNat_ofNat_of_lt' (hqu l hl)]
      omega
    have hg : GroupFits24 (encode A) 0 := by
      simp only [GroupFits24, Fits, size_encode_fields, hA, USize.reduceToNat]
      have := USize.le_size; omega
    unfold loadLines24
    rw [dite_eq_left_of_eq_true (eq_true ⟨hfit 0 (by decide), hfit 1 (by decide),
      hfit 2 (by decide), hfit 3 (by decide), hfit 4 (by decide), hfit 5 (by decide),
      hfit 6 (by decide), hfit 7 (by decide), hg⟩)]
    refine ⟨loadModel M A (fun l ↦ (r0 + l) * w + 16 * blk) 0,
      load16x24_encode M A (fun l ↦ (r0 + l) * w + 16 * blk) hqu 0 _ _ _ _ _ _ _ _ _, ?_, ?_⟩
    · have hL : ∀ j ∈ coords16, j < 24 := fun j hj ↦ by have := coords16_spec.lt j hj; omega
      rw [loadModel, spliceRows, (foldl_splice_rows 24 _ 0 coords16 hL A (by rw [hA])).1, hA]
    · intro l hl
      have hL : ∀ j ∈ coords16, j < 24 := fun j hj ↦ by have := coords16_spec.lt j hj; omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      ext j hj
      simp only [lane, Vector.getElem_ofFn, CompStark.Hash.overwrite, Fin.getElem_fin, getD_block,
        hcnt]
      rw [word, loadModel, spliceRows,
        (foldl_splice_rows 24 _ 0 coords16 hL A (by rw [hA])).2.1 j hj l hl]
      by_cases hj16 : j < 16
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (coords16_spec.mem j hj16)),
          ite_eq_left_of_eq_true _ _ (eq_true hj16)]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hj16 (coords16_spec.lt j h)),
          ite_eq_right_of_eq_false _ _ (eq_false hj16)]
  · obtain ⟨A', e, s, wl⟩ := scatterRows_encode M A w rows r0 blk (by rw [hM]) (by omega) hu
      (by rw [hA]; have := USize.le_size; omega)
    refine ⟨A', e, by rw [s, hA], fun l hl ↦ ?_⟩
    ext j hj
    simp only [lane, Vector.getElem_ofFn]
    rw [wl l hl j (by omega)]
    split_ifs with h1 h2
    · simp only [CompStark.Hash.overwrite, Vector.getElem_ofFn, getD_block, h1.2, ↓reduceIte]
    · omega
    · have hn : ¬j < min 16 (w - 16 * blk) := by omega
      simp only [CompStark.Hash.overwrite, Vector.getElem_ofFn, getD_block, hn, ↓reduceIte,
        Fin.getElem_fin]
    · simp only [Vector.getElem_ofFn]

theorem absorb_eq_foldl {α : Type*} {t : Nat} (perm : Vector α t → Vector α t) (r : Nat)
    (hr : 0 < r) :
    ∀ (xs : List α) (s : Vector α t), CompStark.Hash.absorb perm r hr s xs =
      (List.range ((xs.length + r - 1) / r)).foldl
        (fun s b ↦ perm (CompStark.Hash.overwrite s ((xs.drop (r * b)).take r))) s
  | [], s => by
    rw [CompStark.Hash.absorb, List.length_nil, Nat.zero_add,
      Nat.div_eq_of_lt (by omega), List.range_zero, List.foldl_nil]
  | x :: xs, s => by
    rw [CompStark.Hash.absorb, absorb_eq_foldl perm r hr ((x :: xs).drop r)]
    have hn : ((x :: xs).length + r - 1) / r = (((x :: xs).drop r).length + r - 1) / r + 1 := by
      rw [List.length_drop, List.length_cons]
      by_cases h : xs.length + 1 ≤ r
      · rw [Nat.sub_eq_zero_of_le h, Nat.zero_add,
          Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega),
          Nat.div_eq_of_lt (show r - 1 < r by omega)]
      · rw [show xs.length + 1 + r - 1 = (xs.length + 1 - r + r - 1) + 1 * r by omega,
          Nat.add_mul_div_right _ _ hr]
    rw [hn, List.range_succ_eq_map, List.foldl_cons, List.foldl_map, Nat.mul_zero, List.drop_zero]
    congr 1
    funext s b
    rw [List.drop_drop, Nat.mul_succ, Nat.add_comm]
termination_by xs => xs.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

theorem block_eq (M : Array F) (w h r blk : Nat) :
    block M w r blk =
      ((((⟨w, h, M⟩ : CompStark.Merkle.Matrix F).row r).drop (16 * blk)).take 16) := by
  apply List.ext_getElem
  · simp only [block, CompStark.Merkle.Matrix.row, List.length_map, List.length_range,
      List.length_take, List.length_drop]
  · intro j h1 h2
    simp only [block, CompStark.Merkle.Matrix.row, List.getElem_map, List.getElem_range,
      List.getElem_take, List.getElem_drop, Nat.add_assoc]

theorem zeroWords_fields (n : Nat) :
    CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords n =
      encode (Array.replicate n (0 : F)) := by
  rw [CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords_eq,
    CompPoly.CPolynomial.NTTFast.Packed.encode_eq_map_val, Array.map_replicate]
  rfl

theorem groupFits24_zero (A : Array F) (hA : A.size = 192) : GroupFits24 (encode A) 0 := by
  simp only [GroupFits24, Fits, size_encode_fields, hA, USize.reduceToNat]
  have := USize.le_size; omega

theorem lane_zero (t : Nat) (W : Array F) (l : Nat) : lane t W 0 l = Group.lane t W l := by
  simp only [lane, Group.lane, word, Nat.zero_add]


/-- The packed width-24 permutation of a group of eight states, state by state. -/
theorem permute24_lanes [Poseidon2Field (FastField p)] [PackedPoseidon2 p] (A : Array F) (hA :
    A.size = 192) :
    ∃ A', PackedPoseidon2.permute24 p (encode A) = encode A' ∧ A'.size = 192 ∧
      ∀ l < 8, lane 24 A' 0 l = permute ((Poseidon2Field.params24 : Params (FastField p) 24)) (lane
          24 A 0 l) :=
  ⟨_, PackedPoseidon2.permute24_encode A hA, Group.size_map .., fun l hl ↦ by
    rw [lane_zero, lane_zero, Group.lane_map _ _ _ _ hl]⟩

/-- The packed width-16 permutation of a group of eight states, state by state. -/
theorem permute16_lanes [Poseidon2Field (FastField p)] [PackedPoseidon2 p] (A : Array F) (hA :
    A.size = 128) :
    ∃ A', PackedPoseidon2.permute16 p (encode A) = encode A' ∧ A'.size = 128 ∧
      ∀ l < 8, lane 16 A' 0 l = permute ((Poseidon2Field.params16 : Params (FastField p) 16)) (lane
          16 A 0 l) :=
  ⟨_, PackedPoseidon2.permute16_encode A hA, Group.size_map .., fun l hl ↦ by
    rw [lane_zero, lane_zero, Group.lane_map _ _ _ _ hl]⟩

theorem absorbRows_encode [Poseidon2Field (FastField p)] [PackedPoseidon2 p] (M : Array F) (w rows
    r0 : Nat) (hM : M.size = rows * w)
    (hu : 4 * M.size < USize.size) :
    ∃ A, absorbRows p (encode M) w rows r0 = encode A ∧
      A.size = 192 ∧ ∀ l < 8, r0 + l < rows → lane 24 A 0 l =
        CompStark.Hash.absorb (permute ((Poseidon2Field.params24 : Params (FastField p) 24))) 16
            (by decide)
          (Vector.replicate 24 0) ((⟨w, rows, M⟩ : CompStark.Merkle.Matrix F).row (r0 + l)) := by
  have key : ∀ b, ∃ A, (List.range b).foldl (fun st blk ↦
      PackedPoseidon2.permute24 p (absorbBlock (encode M) w rows r0 blk st))
      (encode (Array.replicate 192 (0 : F))) = encode A ∧ A.size = 192 ∧
      ∀ l < 8, r0 + l < rows → lane 24 A 0 l = (List.range b).foldl (fun s blk ↦
        permute ((Poseidon2Field.params24 : Params (FastField p) 24)) (CompStark.Hash.overwrite s
          ((((⟨w, rows, M⟩ : CompStark.Merkle.Matrix F).row (r0 + l)).drop (16 * blk)).take 16)))
        (Vector.replicate 24 0) := by
    intro b
    induction b with
    | zero =>
      refine ⟨_, rfl, Array.size_replicate, fun l hl _ ↦ ?_⟩
      ext j hj
      simp only [List.range_zero, List.foldl_nil, lane, Vector.getElem_ofFn, word,
        Vector.getElem_replicate, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split_ifs <;> rfl
    | succ b ih =>
      obtain ⟨A, e, hs, hprev⟩ := ih
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [e]
      obtain ⟨A1, e1, s1, l1⟩ := absorbBlock_encode M A w rows r0 b hM hs hu
      rw [e1]
      obtain ⟨A2, e2, s2, l2⟩ := permute24_lanes A1 s1
      refine ⟨A2, e2, s2, fun l hl hr ↦ ?_⟩
      rw [l2 l hl, l1 l hl, ite_eq_left_of_eq_true _ _ (eq_true hr), hprev l hl hr,
        block_eq _ _ rows]
  obtain ⟨A, e, hs, hl⟩ := key ((w + 15) / 16)
  refine ⟨A, by rw [absorbRows, zeroWords_fields (p := p), e], hs, fun l h8 hr ↦ ?_⟩
  rw [hl l h8 hr, absorb_eq_foldl]
  simp only [CompStark.Merkle.Matrix.row, List.length_map, List.length_range,
    show w + 16 - 1 = w + 15 by omega]

open CompPoly.CPolynomial.NTTFast.Packed (getD_splice getD_setIfInBounds) in
theorem storeModel_spec (S O : Array F) (r0 : Nat) (hO : 8 * r0 + 64 ≤ O.size) :
    (storeModel S O 0 fun l ↦ 8 * (r0 + l)).size = O.size ∧ ∀ k,
    (storeModel S O 0 fun l ↦ 8 * (r0 + l)).getD k 0 =
      if 8 * r0 ≤ k ∧ k < 8 * r0 + 64 then word S 0 (k % 8) (k / 8 - r0) else O.getD k 0 := by
  have key : ∀ L ≤ 8, ((List.range L).foldl (fun A l ↦ CompPoly.CPolynomial.NTTFast.Packed.splice
      A (8 * (r0 + l)) (lit8 fun j ↦ word S 0 j l)) O).size = O.size ∧
      ∀ k, ((List.range L).foldl (fun A l ↦ CompPoly.CPolynomial.NTTFast.Packed.splice
        A (8 * (r0 + l)) (lit8 fun j ↦ word S 0 j l)) O).getD k 0 =
        if 8 * r0 ≤ k ∧ k < 8 * r0 + 8 * L then word S 0 (k % 8) (k / 8 - r0) else O.getD k 0 := by
    intro L hL
    induction L with
    | zero =>
      refine ⟨rfl, fun k ↦ ?_⟩
      simp only [Nat.mul_zero, Nat.add_zero]
      split_ifs <;> first | rfl | omega
    | succ L ih =>
      obtain ⟨hs, hg⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hv : (lit8 fun j ↦ word S 0 j L).size = 8 := rfl
      have hb : 8 * (r0 + L) + (lit8 fun j ↦ word S 0 j L).size ≤
          ((List.range L).foldl (fun A l ↦ CompPoly.CPolynomial.NTTFast.Packed.splice
            A (8 * (r0 + l)) (lit8 fun j ↦ word S 0 j l)) O).size := by
        rw [hs, hv]; omega
      refine ⟨by rw [CompPoly.CPolynomial.NTTFast.Packed.size_splice _ _ _ hb, hs], fun k ↦ ?_⟩
      rw [getD_splice _ _ _ hb, hg, hv]
      by_cases hk : 8 * (r0 + L) ≤ k ∧ k < 8 * (r0 + L) + 8
      · have hj : k - 8 * (r0 + L) < 8 := by omega
        rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
        have hl : k / 8 - r0 = L := by omega
        have hm : k % 8 = k - 8 * (r0 + L) := by omega
        rw [hl, hm]
        generalize k - 8 * (r0 + L) = j at hj
        interval_cases j <;> rfl
      · by_cases h1 : k < 8 * (r0 + L)
        · rw [ite_eq_left h1]
          split_ifs <;> first | rfl | omega
        · rw [ite_eq_right h1, ite_eq_right (by omega)]
          split_ifs <;> first | rfl | omega
  rw [storeModel, show [0, 1, 2, 3, 4, 5, 6, 7] = List.range 8 by rfl]
  exact key 8 le_rfl

theorem writes_digest (S X : Array F) (hS : 64 ≤ S.size) (hSu : 4 * S.size < USize.size)
    (l d : Nat) (hl : l < 8)
    (hX : 8 * d + 8 ≤ X.size) (hu : 4 * X.size < USize.size) : ∀ J ≤ 8,
    ∃ X', (List.range J).foldl (fun b j ↦ CompPoly.CPolynomial.NTTFast.Packed.Native.write b
        (8 * d + j) (CompPoly.CPolynomial.NTTFast.Packed.Native.read (encode S) (8 * j + l)))
        (encode X) = encode X' ∧ X'.size = X.size ∧
      ∀ k, X'.getD k 0 = if 8 * d ≤ k ∧ k < 8 * d + J then word S 0 (k % 8) l else X.getD k 0 := by
  intro J hJ
  induction J with
  | zero => exact ⟨X, rfl, rfl, fun k ↦ by rw [ite_eq_right (by omega)]⟩
  | succ J ih =>
    obtain ⟨X1, e1, s1, g1⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, e1, List.foldl_cons, List.foldl_nil,
      CompPoly.CPolynomial.NTTFast.Packed.Native.read_encode _ _
        (by rw [size_encode_fields]; exact hSu) (by omega),
      CompPoly.CPolynomial.NTTFast.Packed.Native.write_encode _ _
        (by rw [size_encode_fields, s1]; exact hu) (by omega)]
    refine ⟨_, rfl, by rw [Array.size_setIfInBounds, s1], fun k ↦ ?_⟩
    rw [CompPoly.CPolynomial.NTTFast.Packed.getD_setIfInBounds _ _ _ _ _ (by omega), g1]
    by_cases hk : k = 8 * d + J
    · subst hk
      rw [ite_eq_left rfl, ite_eq_left (by omega),
        show (8 * d + J) % 8 = J by omega, word, Nat.zero_add]
    · rw [ite_eq_right hk]
      split_ifs <;> first | rfl | omega

theorem storeRows_encode (S O : Array F) (rows r0 : Nat) (hS : 64 ≤ S.size)
    (hSu : 4 * S.size < USize.size)
    (hO : O.size = 8 * rows) (hu : 4 * O.size < USize.size) :
    ∃ O', storeRows (encode S) rows r0 (encode O) = encode O' ∧ O'.size = 8 * rows ∧
      ∀ k, O'.getD k 0 = if 8 * r0 ≤ k ∧ k < 8 * rows ∧ k < 8 * r0 + 64 then
        word S 0 (k % 8) (k / 8 - r0) else O.getD k 0 := by
  unfold storeRows
  dsimp only
  split
  · rename_i hfull
    unfold storeDigests
    have hp : ∀ l < 8, 8 * (r0 + l) < USize.size := fun l hl ↦ by omega
    have hfit : ∀ l < 8, Fits (encode O) (8 * (r0 + l)).toUSize 7 := fun l hl ↦ by
      simp only [Fits, size_encode_fields, USize.toNat_ofNat_of_lt' (hp l hl)]
      omega
    have hs : Fits (encode S) 0 63 := by
      simp only [Fits, size_encode_fields, USize.reduceToNat]
      omega
    simp only [Id.run, pure]
    rw [dite_eq_left_of_eq_true (eq_true ⟨hs, hfit 0 (by decide), hfit 1 (by decide),
      hfit 2 (by decide), hfit 3 (by decide), hfit 4 (by decide), hfit 5 (by decide),
      hfit 6 (by decide), hfit 7 (by decide)⟩)]
    refine ⟨_, store8x8_encode S O 0 (fun l ↦ 8 * (r0 + l)) hp _ _ _ _ _ _ _ _ _, ?_, ?_⟩
    · rw [USize.toNat_zero, (storeModel_spec S O r0 (by omega)).1, hO]
    · intro k
      rw [USize.toNat_zero, (storeModel_spec S O r0 (by omega)).2]
      split_ifs <;> first | rfl | omega
  · simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
      bind_pure, pure_bind, ite_pure_yield, List.forIn_pure_yield_eq_foldl,
      Id.run_pure]
    have key : ∀ L ≤ 8, ∃ O', (List.range L).foldl (fun b a ↦ if r0 + a < rows then
        (List.range 8).foldl (fun b a_1 ↦ CompPoly.CPolynomial.NTTFast.Packed.Native.write b
          (8 * (r0 + a) + a_1) (CompPoly.CPolynomial.NTTFast.Packed.Native.read (encode S)
            (8 * a_1 + a))) b else b) (encode O) = encode O' ∧
        O'.size = 8 * rows ∧ ∀ k, O'.getD k 0 = if 8 * r0 ≤ k ∧ k < 8 * rows ∧ k < 8 * r0 + 8 * L
          then word S 0 (k % 8) (k / 8 - r0) else O.getD k 0 := by
      intro L hL
      induction L with
      | zero => exact ⟨O, rfl, hO, fun k ↦ by rw [ite_eq_right (by omega)]⟩
      | succ L ih =>
        obtain ⟨O1, e1, s1, g1⟩ := ih (by omega)
        rw [List.range_succ (n := L), List.foldl_append, e1, List.foldl_cons, List.foldl_nil]
        by_cases hr : r0 + L < rows
        · rw [ite_eq_left hr]
          obtain ⟨O2, e2, s2, g2⟩ := writes_digest S O1 hS hSu L (r0 + L) (by omega) (by omega)
            (by rw [s1, ← hO]; exact hu) 8 le_rfl
          refine ⟨O2, e2, by rw [s2, s1], fun k ↦ ?_⟩
          rw [g2, g1]
          by_cases hk : 8 * (r0 + L) ≤ k ∧ k < 8 * (r0 + L) + 8
          · rw [ite_eq_left hk, ite_eq_left (by omega), show k / 8 - r0 = L by omega]
          · rw [ite_eq_right hk]
            split_ifs <;> first | rfl | omega
        · rw [ite_eq_right hr]
          refine ⟨O1, rfl, s1, fun k ↦ ?_⟩
          rw [g1]
          split_ifs <;> first | rfl | omega
    obtain ⟨O', e, s, g⟩ := key 8 le_rfl
    exact ⟨O', e, s, g⟩

theorem getElem_hash [Poseidon2Field (FastField p)] [PackedPoseidon2 p] (xs : List F) (j : Nat) (hj
    : j < 8) :
    (Hash.Poseidon2.hash (FastField p) xs)[j] =
      (CompStark.Hash.absorb (permute ((Poseidon2Field.params24 : Params (FastField p) 24))) 16 (by
          decide)
        (Vector.replicate 24 0) xs)[j] := by
  simp only [Hash.Poseidon2.hash_eq, CompStark.Hash.sponge, Vector.getElem_cast,
    Vector.getElem_take]

theorem hashChunk_encode [Poseidon2Field (FastField p)] [PackedPoseidon2 p] (M : Array F) (w rows :
    Nat) (hM : M.size = rows * w)
    (hu : 4 * M.size < USize.size) (ho : 4 * (8 * rows) < USize.size) :
    ∃ D, hashChunk p (encode M) w rows = encode D ∧
      D.size = 8 * rows ∧ ∀ r < rows, ∀ j (hj : j < 8), D.getD (8 * r + j) 0 =
        (Hash.Poseidon2.hash (FastField p)
          ((⟨w, rows, M⟩ : CompStark.Merkle.Matrix F).row r))[j]'hj := by
  have key : ∀ G, ∃ D, (List.range G).foldl (fun out g ↦
      hashRows8 p (encode M) w rows (8 * g) out)
      (encode (Array.replicate (8 * rows) (0 : F))) = encode D ∧ D.size = 8 * rows ∧
      ∀ r < rows, ∀ j (hj : j < 8), D.getD (8 * r + j) 0 = if r < 8 * G then
        (Hash.Poseidon2.hash (FastField p) ((⟨w, rows, M⟩ : CompStark.Merkle.Matrix F).row r))[j]'hj
        else 0 := by
    intro G
    induction G with
    | zero =>
      refine ⟨_, rfl, Array.size_replicate, fun r hr j hj ↦ ?_⟩
      rw [ite_eq_right (by omega), Array.getD_eq_getD_getElem?, Array.getElem?_replicate,
        ite_eq_left (by omega)]
      rfl
    | succ G ih =>
      obtain ⟨D, e, s, g⟩ := ih
      rw [List.range_succ, List.foldl_append, e, List.foldl_cons, List.foldl_nil, hashRows8]
      obtain ⟨A, eA, sA, lA⟩ := absorbRows_encode M w rows (8 * G) hM hu
      rw [eA]
      obtain ⟨D', e', s', g'⟩ := storeRows_encode A D rows (8 * G) (by omega)
        (by rw [sA]; have := USize.le_size; omega) s (by rw [s]; exact ho)
      refine ⟨D', e', s', fun r hr j hj ↦ ?_⟩
      rw [g']
      by_cases hG : 8 * G ≤ r ∧ r < 8 * G + 8
      · have hl := lA (r - 8 * G) (by omega) (by omega)
        rw [show 8 * G + (r - 8 * G) = r by omega] at hl
        rw [ite_eq_left (by omega), ite_eq_left (by omega), getElem_hash _ _ hj, ← hl,
          show (8 * r + j) % 8 = j by omega, show (8 * r + j) / 8 - 8 * G = r - 8 * G by omega]
        simp only [lane, Vector.getElem_ofFn]
      · rw [ite_eq_right (by omega), g r hr j hj]
        split_ifs <;> first | rfl | omega
  obtain ⟨D, e, s, g⟩ := key ((rows + 7) / 8)
  refine ⟨D, by rw [hashChunk, zeroWords_fields (p := p), e], s, fun r hr j hj ↦ ?_⟩
  rw [g r hr j hj, ite_eq_left (by omega)]

/-- Digest `k` of a layer stored as consecutive words. -/
def dig (P : Array F) (k : Nat) : Vector F 8 := Vector.ofFn fun j ↦ P.getD (8 * k + j) 0

theorem loadPairs_encode (P : Array F) (n o : Nat) (hP : P.size = 8 * n)
    (hu : 4 * P.size < USize.size) :
    ∃ S, loadPairs (encode P) n o = encode S ∧ S.size = 128 ∧ ∀ l < 8, o + l < n / 2 →
      lane 16 S 0 l = Vector.ofFn fun j ↦ P.getD (16 * (o + l) + j) 0 := by
  have h128 : 4 * 128 < USize.size := by have := USize.le_size; omega
  unfold loadPairs
  rw [zeroWords_fields (p := p)]
  split
  · rename_i hfull
    have hq : ∀ l < 8, (o + l) * 16 + 16 * 0 + 16 ≤ P.size := fun l hl ↦ by omega
    have hqu : ∀ l < 8, (o + l) * 16 + 16 * 0 < USize.size := fun l hl ↦ by
      have := hq l hl; omega
    have hfit : ∀ l < 8, Fits (encode P) ((o + l) * 16 + 16 * 0).toUSize 15 := fun l hl ↦ by
      have := hq l hl
      simp only [Fits, size_encode_fields, USize.toNat_ofNat_of_lt' (hqu l hl)]
      omega
    have hg : GroupFits (encode (Array.replicate 128 (0 : F))) 0 := by
      simp only [GroupFits, Fits, size_encode_fields, Array.size_replicate, USize.reduceToNat]
      omega
    unfold loadLines16
    rw [dite_eq_left_of_eq_true (eq_true ⟨hfit 0 (by decide), hfit 1 (by decide),
      hfit 2 (by decide), hfit 3 (by decide), hfit 4 (by decide), hfit 5 (by decide),
      hfit 6 (by decide), hfit 7 (by decide), hg⟩)]
    have hL : ∀ j ∈ coords16, j < 16 := coords16_spec.lt
    have hW : 0 + 8 * 16 ≤ (Array.replicate 128 (0 : F)).size := by
      rw [Array.size_replicate]
    refine ⟨_, load16x16_encode P _ (fun l ↦ (o + l) * 16 + 16 * 0) hqu 0 _ _ _ _ _ _ _ _ _,
      ?_, fun l hl _ ↦ ?_⟩
    · rw [USize.toNat_zero, loadModel, spliceRows, (foldl_splice_rows 16 _ 0 coords16 hL _ hW).1,
        Array.size_replicate]
    · ext j hj
      simp only [lane, Vector.getElem_ofFn, USize.toNat_zero]
      rw [word, loadModel, spliceRows, (foldl_splice_rows 16 _ 0 coords16 hL _ hW).2.1 j hj l hl,
        ite_eq_left_of_eq_true _ _ (eq_true (coords16_spec.mem j hj))]
      congr 1
      omega
  · obtain ⟨S, e, s, wl⟩ := scatterRows_encode P (Array.replicate 128 0) 16 (n / 2) o 0
      (by omega) (by rw [Array.size_replicate]) hu (by rw [Array.size_replicate]; exact h128)
    refine ⟨S, e, by rw [s, Array.size_replicate], fun l hl hr ↦ ?_⟩
    ext j hj
    simp only [lane, Vector.getElem_ofFn]
    rw [wl l hl j (by rw [Array.size_replicate]; omega),
      ite_eq_left_of_eq_true _ _ (eq_true ⟨hr, by omega⟩)]
    congr 1
    omega

theorem overwrite_pair (P : Array F) (i : Nat) :
    CompStark.Hash.overwrite (Vector.replicate 16 0)
        ((dig P (2 * i)).toList ++ (dig P (2 * i + 1)).toList) =
      Vector.ofFn fun j ↦ P.getD (16 * i + j) 0 := by
  ext j hj
  simp only [CompStark.Hash.overwrite, Vector.getElem_ofFn, List.getD_eq_getElem?_getD,
    List.getElem?_append, Vector.length_toList, Vector.getElem?_toList, dig]
  by_cases h : j < 8
  · simp only [h, ↓reduceIte, Vector.getElem?_ofFn, dite_true, Option.getD_some]
    congr 1; omega
  · simp only [h, ↓reduceIte, Vector.getElem?_ofFn, show j - 8 < 8 by omega, dite_true,
      Option.getD_some]
    congr 1; omega

theorem compress8_encode [Poseidon2Field (FastField p)] [PackedPoseidon2 p] (P O : Array F) (n o o0
    count : Nat) (hP : P.size = 8 * n)
    (hu : 4 * P.size < USize.size) (hO : O.size = 8 * count) (huO : 4 * O.size < USize.size)
    (ho : o0 ≤ o) (hc : o0 + count ≤ n / 2) :
    ∃ O', compress8 p (encode P) n o o0 count (encode O) =
      encode O' ∧ O'.size = 8 * count ∧ ∀ k, O'.getD k 0 =
        if 8 * (o - o0) ≤ k ∧ k < 8 * count ∧ k < 8 * (o - o0) + 64 then
          (Hash.Poseidon2.compress (FastField p) (dig P (2 * (o0 + k / 8)))
            (dig P (2 * (o0 + k / 8) + 1)))[k % 8]'(Nat.mod_lt _ (by decide))
        else O.getD k 0 := by
  obtain ⟨S, e, s, ls⟩ := loadPairs_encode P n o hP hu
  obtain ⟨S2, e2, s2, l2⟩ := permute16_lanes S s
  obtain ⟨O', e3, s3, g3⟩ := storeRows_encode S2 O count (o - o0) (by omega)
    (by rw [s2]; have := USize.le_size; omega) hO huO
  refine ⟨O', by rw [compress8, e, e2, e3], s3, fun k ↦ ?_⟩
  rw [g3]
  split_ifs with hk
  · have hl : k / 8 - (o - o0) < 8 := by omega
    have hpl := l2 _ hl
    rw [ls _ hl (by omega), show o + (k / 8 - (o - o0)) = o0 + k / 8 by omega] at hpl
    simp only [Hash.Poseidon2.compress_eq, CompStark.Hash.compress, overwrite_pair,
      ← hpl, Vector.getElem_cast, Vector.getElem_take, lane, Vector.getElem_ofFn]
  · rfl

end CompStark.Merkle.Packed
