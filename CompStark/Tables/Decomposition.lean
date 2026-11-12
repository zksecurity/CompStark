/-
Copyright (c) 2026 zkSecurity.
Adapted from Verified-zkEVM/leanerVM (Apache-2.0), revision a9d42bfdae8081a4e16aef1cd8526cdaa2a8f4d6:
LeanerVM.Protocol.Bus and ToCompPoly.Stacking.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.BusSound
public import CompStark.Multilinear.Algebra.AmbientStacking

/-! The multilinear extension of a side's stacked leaves as a sum over its blocks: each block's
extension at the point's low coordinates, weighted by the public selector of its aligned offset in
the high coordinates, plus the ambient one-padding (`leaves_blocks`). -/

@[expose] public section

namespace CompStark.Tables.System

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear

variable (S : System K) (L : Layout S.tables.length)

/-- The selector of the aligned block of height `κ` at `offset` among `2 ^ μ` leaves. -/
def selectorWeight (μ κ offset : ℕ) (ζ : List E) : E :=
  ∏ j : Fin (μ - κ), eqFactor (ζ.getD (κ + j.val) 0) (bit (offset / 2 ^ κ) j.val)

/-- Sum a block expression with its aligned selector weight. -/
def sumBlocks (μ : ℕ) (ζ : List E) (value : Block S.tables.length → E) :
    List (Block S.tables.length) → ℕ → E
  | [], _ => 0
  | b :: rest, offset =>
      selectorWeight μ (Block.height S L b) offset ζ * value b +
        sumBlocks μ ζ value rest (offset + 2 ^ Block.height S L b)

/-- Sorted blocks have decreasing heights. -/
theorem sortedBlocks_antitone (side : Fin 3) :
    Antitone fun b : Fin (S.sortedBlocks L side).length ↦
      Block.height S L (S.sortedBlocks L side)[b] := by
  intro a b hab
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · have hp := List.pairwise_mergeSort
      (le := fun a b : Block S.tables.length ↦ decide (Block.height S L b ≤ Block.height S L a))
      (fun a b c hab hbc ↦ by simp only [decide_eq_true_eq] at *; omega)
      (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (S.blocks side)
    exact of_decide_eq_true (List.pairwise_iff_getElem.mp hp a.val b.val a.isLt b.isLt h)

/-- The aligned power-of-two block layout of a side. -/
@[reducible] def blockLayout (side : Fin 3) : Algebra.Blocks where
  n := (S.sortedBlocks L side).length
  size b := Block.height S L (S.sortedBlocks L side)[b]
  descending := S.sortedBlocks_antitone L side

/-- The layout's total is the side's number of block leaves. -/
theorem blockLayout_total (side : Fin 3) :
    (S.blockLayout L side).total = ((S.blocks side).map fun b ↦ 2 ^ Block.height S L b).sum := by
  rw [Algebra.Blocks.total_eq_sum]
  change (∑ b : Fin (S.sortedBlocks L side).length,
    2 ^ Block.height S L (S.sortedBlocks L side)[b.val]) = _
  rw [Fin.sum_univ_fun_getElem (S.sortedBlocks L side) (fun b ↦ 2 ^ Block.height S L b)]
  exact ((List.mergeSort_perm _ _).map _).sum_eq

/-- Start of a block in a concatenated block list. -/
def blockOffset (bs : List (Block S.tables.length)) (b : ℕ) : ℕ :=
  ((bs.take b).map fun x ↦ 2 ^ Block.height S L x).sum

variable (k : ℕ) (w : Witness K S.tables.length) (α : Fin k → E) (β : E)

/-- A block is read at its prefix offset. -/
theorem stackLeaves_block (bs : List (Block S.tables.length)) (b : Fin bs.length) (i : ℕ)
    (hi : i < 2 ^ Block.height S L bs[b]) :
    S.stackLeaves L k w α β bs (S.blockOffset L bs b.val + i) = S.blockLeaf L k w α β bs[b] i := by
  induction bs with
  | nil => exact Fin.elim0 b
  | cons x bs ih =>
    cases b using Fin.cases with
    | zero =>
      change i < 2 ^ Block.height S L x at hi
      change S.stackLeaves L k w α β (x :: bs) (S.blockOffset L (x :: bs) 0 + i) =
        S.blockLeaf L k w α β x i
      simp only [blockOffset, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add,
        stackLeaves, hi, ↓reduceIte]
    | succ b =>
      have ho : S.blockOffset L (x :: bs) b.succ.val =
          2 ^ Block.height S L x + S.blockOffset L bs b.val := by
        simp only [blockOffset, Fin.val_succ, List.take_succ_cons, List.map_cons, List.sum_cons]
      rw [ho, stackLeaves, ite_eq_right (by omega),
        show 2 ^ Block.height S L x + S.blockOffset L bs b.val + i - 2 ^ Block.height S L x =
          S.blockOffset L bs b.val + i by omega]
      exact ih b hi

/-- Past its last block a stack is one. -/
theorem stackLeaves_pad (bs : List (Block S.tables.length)) (i : ℕ)
    (hi : (bs.map fun x ↦ 2 ^ Block.height S L x).sum ≤ i) : S.stackLeaves L k w α β bs i = 1 := by
  induction bs generalizing i with
  | nil => rfl
  | cons x bs ih =>
    simp only [List.map_cons, List.sum_cons] at hi
    rw [stackLeaves, ite_eq_right (by omega)]
    exact ih _ (by omega)

/-- Prefix offsets are the aligned layout's offsets. -/
theorem blockLayout_offset (side : Fin 3) (b : Fin (S.blockLayout L side).n) :
    (S.blockLayout L side).offset b = S.blockOffset L (S.sortedBlocks L side) b.val := by
  have h (j : ℕ) (hj : j ≤ (S.sortedBlocks L side).length) :
      (S.blockLayout L side).offsetNat j = S.blockOffset L (S.sortedBlocks L side) j := by
    induction j with
    | zero => simp only [Algebra.Blocks.offsetNat, Finset.range_zero, Finset.sum_empty,
        blockOffset, List.take_zero, List.map_nil, List.sum_nil]
    | succ j ih =>
      have hlt : j < (S.sortedBlocks L side).length := by omega
      rw [Algebra.Blocks.offsetNat_succ _ j hlt, ih (by omega)]
      simp only [blockOffset, List.take_succ_eq_append_getElem hlt, List.map_append,
        List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      rfl
  exact h b.val (Nat.le_of_lt b.isLt)

/-- The recursive stack is the aligned block stack with one-padding. -/
theorem blockLayout_stack (μ : ℕ) (side : Fin 3) (i : Fin (2 ^ μ)) :
    ((S.blockLayout L side).stackAt (fun b ↦ Vector.ofFn (fun j ↦
      S.blockLeaf L k w α β (S.sortedBlocks L side)[b] j.val)) μ 1)[i] =
      S.leaves L k w α β side i.val := by
  let B := S.blockLayout L side
  let T : B.Tables E := fun b ↦ Vector.ofFn (fun j ↦
    S.blockLeaf L k w α β (S.sortedBlocks L side)[b] j.val)
  change (B.stackAt T μ 1)[i.val] = _
  have htotal : B.total = ((S.sortedBlocks L side).map fun x ↦ 2 ^ Block.height S L x).sum := by
    rw [Algebra.Blocks.total_eq_sum]
    exact Fin.sum_univ_fun_getElem (S.sortedBlocks L side) (fun x ↦ 2 ^ Block.height S L x)
  by_cases hi : B.total ≤ i.val
  · rw [Algebra.Blocks.stackAt_getElem_of_total_le _ _ _ i.isLt hi]
    apply Eq.symm
    apply stackLeaves_pad
    rw [← htotal]
    exact hi
  · obtain ⟨b, hb⟩ := B.exists_inWindow (Nat.lt_of_not_ge hi)
    rw [Algebra.Blocks.stackAt_getElem_of_inWindow _ _ _ i.isLt hb, Vector.getElem_ofFn]
    have hlt : i.val - B.offset b < 2 ^ B.size b := by obtain ⟨h1, h2⟩ := hb; omega
    have h := S.stackLeaves_block L k w α β (S.sortedBlocks L side) b (i.val - B.offset b) hlt
    rw [← blockLayout_offset, Nat.add_sub_of_le hb.1] at h
    exact h.symm

/-- Enumerating blocks recovers the recursive selector-weighted sum. -/
theorem sumBlocks_eq_sum (μ : ℕ) (z : List E) (value : Block S.tables.length → E)
    (bs : List (Block S.tables.length)) (offset : ℕ) :
    S.sumBlocks L μ z value bs offset = ∑ b : Fin bs.length,
      selectorWeight μ (Block.height S L bs[b]) (offset + S.blockOffset L bs b.val) z *
        value bs[b] := by
  induction bs generalizing offset with
  | nil => simp only [sumBlocks, List.length_nil, Fin.sum_univ_zero]
  | cons x bs ih =>
    simp only [List.length_cons]
    rw [sumBlocks, ih, Fin.sum_univ_succ]
    simp only [Fin.getElem_fin, List.getElem_cons_zero, List.getElem_cons_succ, Fin.val_zero,
      Fin.val_succ, blockOffset, List.take_zero, List.take_succ_cons, List.map_cons, List.map_nil,
      List.sum_nil, List.sum_cons, Nat.add_zero]
    apply congrArg (fun x' : E ↦ selectorWeight μ (Block.height S L x) offset z * value x + x')
    apply Finset.sum_congr rfl
    intro b _
    rw [Nat.add_assoc]

/-- The aligned block selector is the public high-coordinate product. -/
theorem blockLayout_selector (μ : ℕ) (fits : S.Fits L μ) (side : Fin 3)
    (b : Fin (S.blockLayout L side).n) (z : Vector E μ) :
    (S.blockLayout L side).selectorWeight (by rw [blockLayout_total]; exact fits side) b z =
      selectorWeight μ (Block.height S L (S.sortedBlocks L side)[b])
        (S.blockOffset L (S.sortedBlocks L side) b.val) z.toList := by
  rw [Algebra.Blocks.selectorWeight]
  simp only [Fin.getElem_fin]
  rw [Algebra.lagrangeBasis_getElem_nat]
  unfold selectorWeight
  apply Finset.prod_congr rfl
  intro j _
  simp only [Algebra.Blocks.highPoint, Algebra.highVec, Vector.getElem_ofFn, Vector.getElem_cast,
    Fin.getElem_fin, Algebra.Blocks.selector_val, blockLayout_offset]
  rw [List.getD_eq_getElem z.toList 0 (by have := j.isLt; simp only [Vector.length_toList]; omega),
    Vector.getElem_toList]
  dsimp only [eqFactor, bit]
  split <;> simp only [sub_zero, sub_self, mul_one, mul_zero, zero_add, add_zero]

/-- Low block coordinates are the point's prefix. -/
theorem blockLayout_lowPoint (μ : ℕ) (fits : S.Fits L μ) (side : Fin 3)
    (b : Fin (S.blockLayout L side).n) (z : Vector E μ) :
    ((S.blockLayout L side).lowPoint (by rw [blockLayout_total]; exact fits side) b z).toList =
      z.toList.take (Block.height S L (S.sortedBlocks L side)[b]) := by
  apply List.ext_getElem
  · simp only [Vector.length_toList, List.length_take]
    exact (Nat.min_eq_left ((S.blockLayout L side).size_le
      (by rw [blockLayout_total]; exact fits side) b)).symm
  · intro i hi hj
    simp only [Algebra.Blocks.lowPoint, Algebra.lowVec, Vector.getElem_toList,
      Vector.getElem_ofFn, Vector.getElem_cast, List.getElem_take]

/-- Aligned blocks decompose the extension of a side's leaves. -/
theorem leaves_blocks (μ : ℕ) (fits : S.Fits L μ) (side : Fin 3) (z : Vector E μ) :
    mle μ (S.leaves L k w α β side) z.toList =
      S.sumBlocks L μ z.toList (fun b ↦ mle (Block.height S L b)
        (S.blockLeaf L k w α β b) (z.toList.take (Block.height S L b))) (S.sortedBlocks L side) 0 +
      (1 - S.sumBlocks L μ z.toList (fun _ ↦ 1) (S.sortedBlocks L side) 0) := by
  let B := S.blockLayout L side
  let T : B.Tables E := fun b ↦ Vector.ofFn fun j ↦
    S.blockLeaf L k w α β (S.sortedBlocks L side)[b] j.val
  have hT : Vector.ofFn (fun i : Fin (2 ^ μ) ↦ S.leaves L k w α β side i.val) = B.stackAt T μ 1 := by
    apply Vector.ext
    intro i hi
    simpa only [B, T, Vector.getElem_ofFn, Fin.getElem_fin] using
      (S.blockLayout_stack L k w α β μ side ⟨i, hi⟩).symm
  rw [mle_toList, hT, Algebra.Blocks.stack_eval_ambient _ _ (by rw [blockLayout_total]; exact fits side)]
  simp only [one_mul, sumBlocks_eq_sum, Nat.zero_add, mul_one]
  apply congrArg₂ (fun x y : E ↦ x + (1 - y))
  · apply Finset.sum_congr rfl
    intro b _
    rw [blockLayout_selector S L μ fits]
    apply congrArg (fun x : E ↦ selectorWeight μ (Block.height S L (S.sortedBlocks L side)[b])
      (S.blockOffset L (S.sortedBlocks L side) b.val) z.toList * x)
    rw [← mle_toList, blockLayout_lowPoint S L μ fits]
  · exact Finset.sum_congr rfl fun b _ ↦ blockLayout_selector S L μ fits side b z

end CompStark.Tables.System
