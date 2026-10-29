/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Counts

/-! # A range check by lookup inclusion

A batch of range tables (`rangeTable`), each providing the values `0, …, 2 ^ logN - 1` with
unconstrained multiplicities, and range queries (`rangeQuery`), each querying a value `v` with a
boolean multiplicity `s`, all on the bus `range` (`Setup.IsRangeBatch`). Both AIRs pass the count
check (`Air.countsChecked`), and lookup inclusion makes every real query a value of a table
(`rangeChecked_of_satisfiedWithInclusion`): its key is not provided by a query, whose tuples have
weight `1`, and the queries' multiplicities at its key are `0` or `1` with one of them `1`, so
they do not sum to zero; a table row provides it, and the table's tuple is its row index.
-/

@[expose] public section
namespace CompStark.Iop.Batch
open CompStark.Stark

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- A batch of range tables and range queries: every instance is `rangeTable` of its height or
`rangeQuery`. -/
def Setup.IsRangeBatch (S : Setup EF) : Prop :=
  ∀ i, S.air i = rangeTable (S.logN i) ∨ S.air i = rangeQuery

/-- A batch statement of range tables and range queries: every instance is `rangeTable` of its
keygen height or `rangeQuery`. -/
def Statement.IsRangeBatch (C : Statement F) : Prop :=
  ∀ i, C.air i = rangeTable (C.keyLogN i) ∨ C.air i = rangeQuery

/-- A range table has preprocessed columns, so at every admitted vector of lengths it has its
keygen height: the statement is a range batch there. -/
theorem Statement.isRangeBatch_setupAt (C : Statement F) (hC : C.IsRangeBatch)
    (n : Fin C.k → ℕ) (h : C.Admits n) : (C.setupAt EF n h).IsRangeBatch := fun i ↦ by
  rcases hC i with ht | hq
  · refine Or.inl ?_
    have hn := h.keyed i (by rw [ht]; exact Nat.one_pos)
    show C.air i = rangeTable (n i)
    rw [hn, ht]
  · exact Or.inr hq

/-- Every real query is in range: on every row of every `rangeQuery` instance whose `s` is `1`,
the value `v` is the index of a row of some `rangeTable` instance. -/
def Setup.RangeChecked (S : Setup EF) (traces : Fin S.k → Array F) : Prop :=
  ∀ i, S.air i = rangeQuery → ∀ r < 2 ^ S.logN i, (traces i).getD (r * 2 + 1) 0 = 1 →
    ∃ j, S.air j = rangeTable (S.logN j) ∧
      ∃ m : Nat, m < 2 ^ S.logN j ∧ (traces i).getD (r * 2) 0 = (m : F)

end CompStark.Iop.Batch

namespace CompStark.Sound.Batch
open CompStark.Stark CompStark.Lookup

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

theorem rangeQuery_countsChecked : (rangeQuery : Air F).countsChecked = true := by
  have h : (Expr.cur 1 * (Expr.cur 1 - Expr.const 1) : Expr F).isBoolCheck 1 = true := by
    show (1 == 1 && 1 == 1 && decide ((1 : F) = 1)) = true
    simp only [beq_self_eq_true, decide_true, Bool.and_self]
  simp only [Air.countsChecked, rangeQuery, List.all_cons, List.all_nil, Air.queryBound,
    Expr.countBound, Air.isBoolean, List.any_cons, List.any_nil, h, Bool.true_or, ↓reduceIte,
    Option.bind_some, Option.map_some, Stark.Lookup.countWeight, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Bool.and_true]
  rfl

theorem rangeTable_countsChecked (logN : Nat) : (rangeTable logN : Air F).countsChecked = true :=
  rfl

/-- The AIRs of a range batch bound their queries' multiplicities. -/
theorem countsBounded_of_isRangeBatch (S : Iop.Batch.Setup EF) (hS : S.IsRangeBatch)
    (i : Fin S.k) : (S.air i).CountsBounded (S.logN i) :=
  S.countsBounded_of_countsChecked (fun i ↦ by
    rcases hS i with h | h <;> rw [h]
    exacts [rangeTable_countsChecked _, rangeQuery_countsChecked]) i

theorem lookups_of_rangeQuery {S : Iop.Batch.Setup EF} {i : Fin S.k}
    (h : S.air i = rangeQuery) : S.lookups i = (rangeQuery : Air F).lookups := by
  show Iop.Batch.instanceLookups true (S.air i) (S.keyLogN i) = _
  rw [h]
  rfl

theorem lookups_of_rangeTable {S : Iop.Batch.Setup EF} {i : Fin S.k}
    (h : S.air i = rangeTable (S.logN i)) :
    S.lookups i = (rangeTable (S.logN i) : Air F).lookups := by
  show Iop.Batch.instanceLookups true (S.air i) (S.keyLogN i) = _
  rw [h]
  rfl

theorem getD_ofFn_index (n m : Nat) (h : m < n) :
    (Array.ofFn (n := n) fun i ↦ (i.val : F)).getD m 0 = (m : F) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, h, ↓reduceDIte,
    Option.getD_some]

/-- **A range check by lookup inclusion.** In a range batch satisfied with lookup inclusion, every
real query is in range. -/
theorem rangeChecked_of_satisfiedWithInclusion (S : Iop.Batch.Setup EF) (hS : S.IsRangeBatch)
    (traces : Fin S.k → Array F) (publicValues : Fin S.k → List F)
    (h : S.SatisfiedWithInclusion traces publicValues) : S.RangeChecked traces := by
  intro i hi r hr hs
  have hli := lookups_of_rangeQuery hi
  obtain ⟨b, hb⟩ : ∃ b, busNumbers S i = [b] := by
    have hlen := length_busNumbers S i
    rw [hli] at hlen
    match busNumbers S i, hlen with
    | [b], _ => exact ⟨b, rfl⟩
  set v := (traces i).getD (r * 2) 0
  rcases h.included (b, [v]) with ⟨j, r', hr', lb, hlb, -, t, ht, hw, hvals, -⟩ | hsum
  · have hl1 := (List.of_mem_zip hlb).1
    rcases hS j with hj | hj
    · rw [lookups_of_rangeTable hj] at hl1
      simp only [rangeTable, List.mem_singleton] at hl1
      rw [hl1, List.mem_singleton] at ht
      subst ht
      refine ⟨j, hj, r', hr', ?_⟩
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, Expr.eval,
        generationRow] at hvals
      rw [← hvals, hj]
      show (Array.ofFn (n := 2 ^ S.logN j) fun i ↦ (i.val : F)).getD (r' * 1 + 0) 0 = _
      rw [Nat.mul_one, Nat.add_zero, getD_ofFn_index _ _ hr']
    · rw [lookups_of_rangeQuery hj] at hl1
      simp only [rangeQuery, List.mem_singleton] at hl1
      rw [hl1, List.mem_singleton] at ht
      subst ht
      exact absurd hw Nat.one_ne_zero
  · exfalso
    have hx0 : ((b, [v]), (1 : F)) ∈ S.queries traces publicValues := by
      refine (mem_queries S traces publicValues).mpr ⟨i, r, hr, (rangeQuery.lookups.head
        (List.cons_ne_nil _ _), b), ?_, ([.cur 0], .bounded (.cur 1) 1), List.mem_singleton_self _,
        Nat.one_pos, ?_⟩
      · rw [hli, hb]
        exact List.mem_singleton_self _
      · simp only [List.map_cons, List.map_nil, Expr.eval, generationRow, hi]
        rw [← hs]
        rfl
    have hnonneg : ∀ x ∈ ((S.queries traces publicValues).filter (·.1 = (b, [v]))).map
        (intValue ·.2), 0 ≤ x := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨j, r', hr', lb, hlb, t, ht, hw, rfl⟩ :=
        (mem_queries S traces publicValues).mp (List.mem_filter.mp hy).1
      have hl1 := (List.of_mem_zip hlb).1
      rcases hS j with hj | hj
      · rw [lookups_of_rangeTable hj] at hl1
        simp only [rangeTable, List.mem_singleton] at hl1
        rw [hl1, List.mem_singleton] at ht
        subst ht
        exact absurd hw (Nat.lt_irrefl 0)
      · rw [lookups_of_rangeQuery hj] at hl1
        simp only [rangeQuery, List.mem_singleton] at hl1
        rw [hl1, List.mem_singleton] at ht
        subst ht
        have hc := h.air j |>.vanish _ (by rw [hj]; exact List.mem_singleton_self _) r' hr'
        simp only [Expr.eval, Air.traceRow] at hc
        rcases eq_zero_or_one hc with h0 | h1
        · simp only [Expr.eval, generationRow, h0, intValue_zero, le_refl]
        · simp only [Expr.eval, generationRow, h1, intValue_one, zero_le_one]
    have hle := List.single_le_sum hnonneg (intValue (1 : F))
      (List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hx0, decide_eq_true rfl⟩, rfl⟩)
    rw [hsum, intValue_one] at hle
    omega

end CompStark.Sound.Batch
