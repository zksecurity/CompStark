/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Bus
public import CompStark.Multilinear.GrandProduct

/-! The leaves of the bus's three product trees.

A push or pull block is one interaction of one table: on its executed rows its leaf is `β` minus
the fingerprint of the row's encoded tuple, on its padding rows `1`. A nonzero block is one
nonzero column of one table: its value on executed rows, `1` on padding. The blocks of a side are
stacked in decreasing height and padded with ones to the common depth `μ`; the root of the
pushed and pulled trees is the grand product of the encoded multisets (`root_eq_sideProduct`),
and the root of the nonzero tree vanishes exactly when a nonzero column does
(`nonzeroRoot_ne_zero_iff`). -/

@[expose] public section

namespace CompStark.Tables

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear

/-- A block of a product tree. -/
inductive Block (n : ℕ) where
  /-- One interaction of a table. -/
  | interaction (t : Fin n) (I : Interaction K)
  /-- One nonzero column of a table. -/
  | nonzero (t : Fin n) (c : ℕ)

namespace System

variable (S : System K) (L : Layout S.tables.length)

/-- The blocks of side `0` (push), `1` (pull) and `2` (nonzero), in table order. -/
def blocks (side : Fin 3) : List (Block S.tables.length) :=
  (List.finRange S.tables.length).flatMap fun t ↦
    if side.val = 2 then (S.table t).nonzero.map (.nonzero t)
    else ((S.table t).interactions.filter (·.push == (side.val = 0))).map (.interaction t)

/-- A block's log-height: its table's. -/
def Block.height : Block S.tables.length → ℕ
  | .interaction t _ | .nonzero t _ => L.logHeight t

/-- A block's table. -/
def Block.table : Block S.tables.length → Fin S.tables.length
  | .interaction t _ | .nonzero t _ => t

/-- The blocks of a side in decreasing height. -/
def sortedBlocks (side : Fin 3) : List (Block S.tables.length) :=
  (S.blocks side).mergeSort fun a b ↦ decide (Block.height S L b ≤ Block.height S L a)

variable (k : ℕ) (w : Witness K S.tables.length) (α : Fin k → E) (β : E)

/-- A block's form on a row: `β` minus the fingerprint of the encoded tuple, or the column's
value. -/
noncomputable def blockForm (b : Block S.tables.length) (env : Expr.Env K K) (row : ℕ → K) : E :=
  match b with
  | .interaction _ I => β - fingerprint k α (encode k (S.busIndex I.bus) (I.tuple.map (Expr.eval env)))
  | .nonzero _ c => ofK (row c)

/-- The leaf of row `i` of a block: its form, corrected on padding rows by the form of the public
padding row. -/
noncomputable def blockLeaf (b : Block S.tables.length) (i : ℕ) : E :=
  let t := Block.table S b
  S.blockForm k α β b (S.env L w t i) (fun c ↦ ((w t).getD i #[]).getD c 0) +
    if L.executed t ≤ i then
      1 - S.blockForm k α β b (S.paddingEnv L t i) (fun c ↦ (S.table t).padding.getD c 0)
    else 0

/-- Every padding row is the table's public padding row. -/
def Padded : Prop :=
  ∀ t, ∀ i, L.executed t ≤ i → i < 2 ^ L.logHeight t → (w t).getD i #[] = (S.table t).padding.toArray

/-- A padding row that is the public padding row has leaf one. -/
theorem blockLeaf_padding (padded : S.Padded L w) (b : Block S.tables.length) (i : ℕ)
    (hi : L.executed (Block.table S b) ≤ i) (hh : i < 2 ^ L.logHeight (Block.table S b)) :
    S.blockLeaf L k w α β b i = 1 := by
  have row := padded _ i hi hh
  have env : S.env L w (Block.table S b) i = S.paddingEnv L (Block.table S b) i := by
    simp only [paddingEnv, env, row, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getD_eq_getElem?_getD]
  simp only [blockLeaf, hi, ↓reduceIte, env, row, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]
  ring

/-- An executed row's leaf is its form. -/
theorem blockLeaf_executed (b : Block S.tables.length) (i : ℕ) (hi : i < L.executed (Block.table S b)) :
    S.blockLeaf L k w α β b i =
      S.blockForm k α β b (S.env L w (Block.table S b) i)
        (fun c ↦ ((w (Block.table S b)).getD i #[]).getD c 0) := by
  simp only [blockLeaf, show ¬ L.executed (Block.table S b) ≤ i by omega, ↓reduceIte, add_zero]

/-- Stacked blocks, then ones. -/
noncomputable def stackLeaves : List (Block S.tables.length) → ℕ → E
  | [], _ => 1
  | b :: rest, i => if i < 2 ^ Block.height S L b then S.blockLeaf L k w α β b i
      else stackLeaves rest (i - 2 ^ Block.height S L b)

/-- The three sides' leaves, as the grand-product GKR reads them. -/
noncomputable def leaves (side : Fin 3) (i : ℕ) : E :=
  S.stackLeaves L k w α β (S.sortedBlocks L side) i

/-- A block's padding leaves are one. -/
theorem prod_blockLeaf (padded : S.Padded L w) (b : Block S.tables.length)
    (hexec : L.executed (Block.table S b) ≤ 2 ^ Block.height S L b) :
    ∏ i ∈ Finset.range (2 ^ Block.height S L b), S.blockLeaf L k w α β b i =
      ∏ i ∈ Finset.range (L.executed (Block.table S b)), S.blockLeaf L k w α β b i := by
  rw [← Nat.add_sub_cancel' hexec, Finset.prod_range_add]
  conv_rhs => rw [← mul_one (∏ i ∈ Finset.range _, _)]
  congr 1
  apply Finset.prod_eq_one
  intro i hi
  have hh : Block.height S L b = L.logHeight (Block.table S b) := by cases b <;> rfl
  apply blockLeaf_padding S L k w α β padded b _ (Nat.le_add_right _ _)
  have := Finset.mem_range.mp hi
  rw [hh] at this
  omega

/-- Stacked leaves multiply to the product of their blocks when they fit `N` leaves. -/
theorem prod_stackLeaves (bs : List (Block S.tables.length)) (N : ℕ)
    (hfit : (bs.map fun b ↦ 2 ^ Block.height S L b).sum ≤ N) :
    ∏ j ∈ Finset.range N, S.stackLeaves L k w α β bs j =
      (bs.map fun b ↦ ∏ i ∈ Finset.range (2 ^ Block.height S L b),
        S.blockLeaf L k w α β b i).prod := by
  induction bs generalizing N with
  | nil => simp only [stackLeaves, Finset.prod_const_one, List.map_nil, List.prod_nil]
  | cons b rest ih =>
    simp only [List.map_cons, List.sum_cons] at hfit
    rw [← Nat.add_sub_cancel' (le_trans (Nat.le_add_right _ _) hfit), Finset.prod_range_add,
      List.map_cons, List.prod_cons]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      simp only [stackLeaves, Finset.mem_range.mp hi, ↓reduceIte]
    · rw [← ih (N - 2 ^ Block.height S L b) (by omega)]
      apply Finset.prod_congr rfl
      intro i _
      simp only [stackLeaves, show ¬ 2 ^ Block.height S L b + i < 2 ^ Block.height S L b by omega,
        ↓reduceIte, Nat.add_sub_cancel_left]

/-- A list product of products swaps its order. -/
theorem list_prod_comm {α β : Type} (l : List α) (m : List β) (f : α → β → E) :
    (l.map fun a ↦ (m.map fun b ↦ f a b).prod).prod =
      (m.map fun b ↦ (l.map fun a ↦ f a b).prod).prod := by
  have := Multiset.prod_map_prod_map (l : Multiset α) (m : Multiset β) (f := f)
  simpa only [Multiset.map_coe, Multiset.prod_coe] using this

/-- The product over a `flatMap` is the product of the products. -/
theorem prod_flatMap {α : Type} (l : List α) (f : α → List E) :
    (l.flatMap f).prod = (l.map fun a ↦ (f a).prod).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.prod_append, ih, List.map_cons, List.prod_cons]

/-- A product over a range is the product of the mapped list. -/
theorem prod_range_list (n : ℕ) (f : ℕ → E) :
    ∏ i ∈ Finset.range n, f i = ((List.range n).map f).prod := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Finset.prod_range_succ, ih, List.range_succ, List.map_append, List.prod_append,
      List.map_singleton, List.prod_singleton]

/-- The pushed or pulled blocks multiply to the grand product of the encoded multiset. -/
theorem blocks_prod {width : String → ℕ} (h : S.BusShape k width) (push : Bool) (side : Fin 3)
    (hside : side.val = if push then 0 else 1) :
    ((S.blocks side).map fun b ↦ ∏ i ∈ Finset.range (L.executed (Block.table S b)),
        S.blockLeaf L k w α β b i).prod =
      sideProduct k α β (S.encoded k L w push) := by
  have h2 : side.val ≠ 2 := by split at hside <;> omega
  have hdir : decide (side.val = 0) = push := by cases push <;> simp only [hside, ↓reduceIte] <;> decide
  rw [sideProduct, encoded_eq_emitted S h, Multiset.map_map]
  simp only [blocks, h2, ↓reduceIte, hdir, emitted, Multiset.map_coe, Multiset.prod_coe,
    List.map_flatMap, prod_flatMap, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro t _
  rw [list_prod_comm]
  congr 1
  apply List.map_congr_left
  intro i hi
  change ((List.range (L.executed t)).map (S.blockLeaf L k w α β (.interaction t i))).prod = _
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [blockLeaf_executed S L k w α β (.interaction t i) j (List.mem_range.mp hj)]
  rfl

/-- The blocks fit `2 ^ μ` leaves on every side. -/
def Fits (μ : ℕ) : Prop :=
  ∀ side, ((S.blocks side).map fun b ↦ 2 ^ Block.height S L b).sum ≤ 2 ^ μ

/-- The root of a side's tree is the product of its blocks' executed leaves. -/
theorem root_eq_blocks (μ : ℕ) (fits : S.Fits L μ) (padded : S.Padded L w)
    (hexec : ∀ t, L.executed t ≤ 2 ^ L.logHeight t) (side : Fin 3) :
    GrandProduct.level μ 0 (S.leaves L k w α β) side 0 =
      ((S.blocks side).map fun b ↦ ∏ i ∈ Finset.range (L.executed (Block.table S b)),
        S.blockLeaf L k w α β b i).prod := by
  have perm := List.mergeSort_perm (S.blocks side)
    (fun a b ↦ decide (Block.height S L b ≤ Block.height S L a))
  have fitSorted : ((S.sortedBlocks L side).map fun b ↦ 2 ^ Block.height S L b).sum ≤ 2 ^ μ :=
    (perm.map fun b ↦ 2 ^ Block.height S L b).sum_eq ▸ fits side
  simp only [GrandProduct.level, Nat.sub_zero, Nat.zero_mul, Nat.zero_add, leaves]
  rw [Fin.prod_univ_eq_prod_range (fun j ↦ S.stackLeaves L k w α β (S.sortedBlocks L side) j),
    prod_stackLeaves S L k w α β _ _ fitSorted]
  rw [← (perm.map _).prod_eq]
  congr 1
  apply List.map_congr_left
  intro b _
  apply prod_blockLeaf S L k w α β padded
  cases b <;> exact hexec _

/-- The pushed and pulled roots are the grand products of the encoded multisets. -/
theorem root_eq_sideProduct {width : String → ℕ} (h : S.BusShape k width) (μ : ℕ)
    (fits : S.Fits L μ) (padded : S.Padded L w) (hexec : ∀ t, L.executed t ≤ 2 ^ L.logHeight t)
    (push : Bool) :
    GrandProduct.level μ 0 (S.leaves L k w α β) (if push then 0 else 1) 0 =
      sideProduct k α β (S.encoded k L w push) := by
  rw [root_eq_blocks S L k w α β μ fits padded hexec]
  exact blocks_prod S L k w α β h push _ (by cases push <;> rfl)

/-- The nonzero root vanishes exactly when a nonzero column vanishes on an executed row. -/
theorem nonzeroRoot_ne_zero_iff (μ : ℕ) (fits : S.Fits L μ) (padded : S.Padded L w)
    (hexec : ∀ t, L.executed t ≤ 2 ^ L.logHeight t) :
    GrandProduct.level μ 0 (S.leaves L k w α β) 2 0 ≠ 0 ↔
      ∀ t, ∀ i < L.executed t, ∀ c ∈ (S.table t).nonzero, ((w t).getD i #[]).getD c 0 ≠ 0 := by
  have zero (x : K) : ofK x = 0 ↔ x = 0 :=
    ⟨fun h ↦ ofK_injective (h.trans (map_zero (algebraMap K E)).symm), fun h ↦ by
      rw [h]; exact map_zero (algebraMap K E)⟩
  have mem (b : Block S.tables.length) : b ∈ S.blocks 2 ↔
      ∃ t c, c ∈ (S.table t).nonzero ∧ b = .nonzero t c := by
    simp only [blocks, show (2 : Fin 3).val = 2 from rfl, ↓reduceIte, List.mem_flatMap,
      List.mem_finRange, true_and, List.mem_map]
    exact ⟨fun ⟨t, c, hc, he⟩ ↦ ⟨t, c, hc, he.symm⟩, fun ⟨t, c, hc, he⟩ ↦ ⟨t, c, hc, he.symm⟩⟩
  rw [root_eq_blocks S L k w α β μ fits padded hexec, Ne, List.prod_eq_zero_iff, List.mem_map]
  constructor
  · intro h t i hi c hc hz
    apply h
    refine ⟨.nonzero t c, (mem _).mpr ⟨t, c, hc, rfl⟩, Finset.prod_eq_zero (Finset.mem_range.mpr hi) ?_⟩
    rw [blockLeaf_executed S L k w α β (.nonzero t c) i hi]
    simp only [blockForm, Block.table, hz]
    exact (zero 0).mpr rfl
  · rintro h ⟨b, hb, hprod⟩
    obtain ⟨t, c, hc, rfl⟩ := (mem b).mp hb
    obtain ⟨i, hi, hz⟩ := Finset.prod_eq_zero_iff.mp hprod
    have hi' : i < L.executed t := Finset.mem_range.mp hi
    rw [blockLeaf_executed S L k w α β (.nonzero t c) i hi'] at hz
    exact h t i hi' c hc ((zero _).mp hz)

end System

end CompStark.Tables
