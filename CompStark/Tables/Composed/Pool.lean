/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Composed.External

/-! The claim pool of the bus and the table sumcheck: the boundary values at the bus point and the
transmitted committed values at the table point, each a weighted claim on the stack
(`pool_holds_iff`). The transmitted virtual values go to the argument that opens them. -/

@[expose] public section

namespace CompStark.Tables.Composed

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System

variable (S : System K) (L : Layout S.tables.length) (k M : ℕ)

/-- A claim on column `c` of table `t` at a point, as a weighted stack claim if the column is
stacked. -/
def columnClaim (t : Fin S.tables.length) (c : ℕ) (z : List E) (value : E) :
    Option (Whir.Claim E M) :=
  ((S.stackColumns L).finIdxOf? (t, c)).map fun b ↦ S.stackClaim L M b z value

/-- The boundary values as stack claims at the bus point. -/
def boundaryClaims (o : Bus.Output S L k) : List (Whir.Claim E M) :=
  (List.finRange (S.boundaryColumns L).length).filterMap fun j ↦
    columnClaim S L M (S.boundaryColumns L)[j].1 (S.boundaryColumns L)[j].2
      (o.point.take (L.logHeight (S.boundaryColumns L)[j].1)) (o.boundary j)

/-- The transmitted committed values as stack claims at the table point. -/
def valueClaims (o : TableSumcheck.Output S L k) : List (Whir.Claim E M) :=
  (List.finRange S.tables.length).flatMap fun t ↦
    if h : S.Direct L t = false then
      (List.finRange (TableSumcheck.transmitted S t).length).filterMap fun i ↦
        if TableSumcheck.virtualAt S t (TableSumcheck.transmitted S t)[i] then none
        else columnClaim S L M t (TableSumcheck.transmitted S t)[i]
          (o.point.take (L.logHeight t)) (o.values ⟨t, h⟩ i)
    else []

/-- The pool of the bus and the table sumcheck. -/
def pool (o : TableSumcheck.Output S L k) : List (Whir.Claim E M) :=
  boundaryClaims S L k M o.bus ++ valueClaims S L k M o

/-- The table sumcheck's transmitted committed values are their columns' extensions. -/
def CommittedHold (o : TableSumcheck.Output S L k) (w : Witness K S.tables.length) : Prop :=
  ∀ t (i : Fin (TableSumcheck.transmitted S t.1).length),
    TableSumcheck.virtualAt S t.1 (TableSumcheck.transmitted S t.1)[i] = false →
      o.values t i = S.column L w t.1 (TableSumcheck.transmitted S t.1)[i]
        (o.point.take (L.logHeight t.1))

/-- The boundary values are their columns' extensions. -/
def BoundaryHold (o : Bus.Output S L k) (w : Witness K S.tables.length) : Prop :=
  ∀ p ∈ S.boundaryColumns L, S.boundaryValue L o.boundary p.1 p.2 =
    S.column L w p.1 p.2 (o.point.take (L.logHeight p.1))

/-- A transmitted column that is not virtual is committed. -/
theorem committed_of_transmitted (t : Fin S.tables.length) (c : ℕ)
    (hc : c ∈ TableSumcheck.transmitted S t) (hv : TableSumcheck.virtualAt S t c = false) :
    c ∈ S.committedColumns t := by
  refine List.mem_filter.mpr ⟨List.mem_range.mpr (TableSumcheck.lt_of_mem_transmitted S t c hc), ?_⟩
  simpa only [TableSumcheck.virtualAt, Bool.not_eq_true'] using hv

/-- A witness and a stack agree on a committed column's extension. -/
structure Agrees (w : Witness K S.tables.length) (q : Whir.Table K M) : Prop where
  /-- Committed cells are the stack's. -/
  cells : ∀ t i c, c ∈ S.committedColumns t → i < 2 ^ L.logHeight t →
    ((w t).getD i #[]).getD c 0 = ((S.read L M q t).getD i #[]).getD c 0

/-- On a committed column, a column claim holds exactly when its value is the column's extension. -/
theorem columnClaim_holds_iff (hM : (S.stackBlocks L).total ≤ 2 ^ M) (w : Witness K S.tables.length)
    (q : Whir.Table K M) (agree : Agrees S L M w q) (t : Fin S.tables.length) (c : ℕ)
    (hc : c ∈ S.committedColumns t) (z : List E) (value : E) :
    ∃ claim, columnClaim S L M t c z value = some claim ∧
      (claim.Holds (fun u ↦ ofK (q u)) ↔ value = S.column L w t c z) := by
  have mem := (S.mem_stackColumns L t c).mpr hc
  obtain ⟨b, hb⟩ : ∃ b, (S.stackColumns L).finIdxOf? (t, c) = some b := by
    cases h : (S.stackColumns L).finIdxOf? (t, c) with
    | none => exact absurd mem (List.finIdxOf?_eq_none_iff.mp h)
    | some b => exact ⟨b, rfl⟩
  have hget := (List.finIdxOf?_eq_some_iff.mp hb).1
  refine ⟨S.stackClaim L M b z value, by simp only [columnClaim, hb, Option.map_some], ?_⟩
  rw [stackClaim_read_iff S L M hM q b z value, hget]
  have he : S.column L (S.read L M q) t c z = S.column L w t c z := by
    unfold column
    apply mle_congr_values
    intro i hi
    rw [agree.cells t i c hc hi]
  rw [he]

/-- Boundary columns are distinct. -/
theorem boundaryColumns_nodup : (S.boundaryColumns L).Nodup := by
  unfold boundaryColumns
  apply List.nodup_flatMap.mpr
  refine ⟨fun t _ ↦ ?_, ?_⟩
  · split
    · exact (List.nodup_range.filter _).map fun _ _ h ↦ (Prod.mk.inj h).2
    · exact List.nodup_nil
  · apply (List.nodup_finRange S.tables.length).pairwise_of_forall_ne
    intro a _ b _ hab
    simp only [Function.onFun, List.disjoint_left]
    intro x hx hy
    split at hx
    · split at hy
      · obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
        obtain ⟨c', -, h⟩ := List.mem_map.mp hy
        exact hab (Prod.mk.inj h).1.symm
      · exact List.not_mem_nil hy
    · exact List.not_mem_nil hx

/-- The boundary value of the `j`-th boundary column is the `j`-th value. -/
theorem boundaryValue_get (vals : S.BoundaryValues L) (j : Fin (S.boundaryColumns L).length) :
    S.boundaryValue L vals (S.boundaryColumns L)[j].1 (S.boundaryColumns L)[j].2 = vals j := by
  have hidx : (S.boundaryColumns L).finIdxOf? ((S.boundaryColumns L)[j].1, (S.boundaryColumns L)[j].2) =
      some j := by
    apply List.finIdxOf?_eq_some_iff.mpr
    refine ⟨rfl, fun j' hj heq ↦ ?_⟩
    have := (List.Nodup.getElem_inj_iff (boundaryColumns_nodup S L)).mp heq
    exact absurd this (by omega)
  unfold boundaryValue
  rw [hidx]
  rfl

variable {S L k M}

/-- The boundary claims hold on a stack exactly when the boundary values are true of an agreeing
witness, the boundary columns being committed. -/
theorem boundaryClaims_holds_iff (hM : (S.stackBlocks L).total ≤ 2 ^ M)
    (hbd : ∀ p ∈ S.boundaryColumns L, p.2 ∈ S.committedColumns p.1)
    (w : Witness K S.tables.length) (q : Whir.Table K M) (agree : Agrees S L M w q)
    (o : Bus.Output S L k) :
    (∀ c ∈ boundaryClaims S L k M o, c.Holds (fun u ↦ ofK (q u))) ↔ BoundaryHold S L k o w := by
  constructor
  · intro h p hp
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨claim, hsome, hiff⟩ := columnClaim_holds_iff S L M hM w q agree _ _
      (hbd _ (List.getElem_mem hj)) (o.point.take (L.logHeight (S.boundaryColumns L)[j].1)) (o.boundary ⟨j, hj⟩)
    have hmem : claim ∈ boundaryClaims S L k M o :=
      List.mem_filterMap.mpr ⟨⟨j, hj⟩, List.mem_finRange _, hsome⟩
    have := hiff.mp (h claim hmem)
    rw [show (S.boundaryColumns L)[j] = (S.boundaryColumns L)[(⟨j, hj⟩ : Fin _)] from rfl,
      boundaryValue_get S L o.boundary ⟨j, hj⟩]
    exact this
  · intro h c hc
    obtain ⟨j, -, hsome⟩ := List.mem_filterMap.mp hc
    obtain ⟨claim, hsome', hiff⟩ := columnClaim_holds_iff S L M hM w q agree _ _
      (hbd _ (List.getElem_mem j.isLt)) (o.point.take (L.logHeight (S.boundaryColumns L)[j].1)) (o.boundary j)
    obtain rfl : c = claim := Option.some.inj (hsome.symm.trans hsome')
    apply hiff.mpr
    have := h _ (List.getElem_mem j.isLt)
    exact (boundaryValue_get S L o.boundary j).symm.trans this

/-- The value claims hold on a stack exactly when the transmitted committed values are true of an
agreeing witness. -/
theorem valueClaims_holds_iff (hM : (S.stackBlocks L).total ≤ 2 ^ M)
    (w : Witness K S.tables.length) (q : Whir.Table K M) (agree : Agrees S L M w q)
    (o : TableSumcheck.Output S L k) :
    (∀ c ∈ valueClaims S L k M o, c.Holds (fun u ↦ ofK (q u))) ↔ CommittedHold S L k o w := by
  constructor
  · intro h t i hv
    obtain ⟨claim, hsome, hiff⟩ := columnClaim_holds_iff S L M hM w q agree t.1 _
      (committed_of_transmitted S t.1 _ (List.getElem_mem i.isLt) hv)
      (o.point.take (L.logHeight t.1)) (o.values t i)
    apply hiff.mp
    apply h
    apply List.mem_flatMap.mpr
    refine ⟨t.1, List.mem_finRange _, ?_⟩
    rw [dif_pos t.2]
    apply List.mem_filterMap.mpr
    refine ⟨i, List.mem_finRange _, ?_⟩
    rw [if_neg (by simp only [hv, Bool.false_eq_true, not_false_eq_true])]
    exact hsome
  · intro h c hc
    obtain ⟨t, -, ht⟩ := List.mem_flatMap.mp hc
    split at ht
    · rename_i hd
      obtain ⟨i, -, hsome⟩ := List.mem_filterMap.mp ht
      split at hsome
      · cases hsome
      · rename_i hv
        have hv' : TableSumcheck.virtualAt S t (TableSumcheck.transmitted S t)[i] = false := by
          simpa only [Bool.not_eq_true] using hv
        obtain ⟨claim, hsome', hiff⟩ := columnClaim_holds_iff S L M hM w q agree t _
          (committed_of_transmitted S t _ (List.getElem_mem i.isLt) hv')
          (o.point.take (L.logHeight t)) (o.values ⟨t, hd⟩ i)
        obtain rfl : c = claim := Option.some.inj (hsome.symm.trans hsome')
        exact hiff.mpr (h ⟨t, hd⟩ i hv')
    · exact absurd ht List.not_mem_nil

/-- The pool holds on a stack exactly when the boundary and transmitted committed values are true of
an agreeing witness. -/
theorem pool_holds_iff (hM : (S.stackBlocks L).total ≤ 2 ^ M)
    (hbd : ∀ p ∈ S.boundaryColumns L, p.2 ∈ S.committedColumns p.1)
    (w : Witness K S.tables.length) (q : Whir.Table K M) (agree : Agrees S L M w q)
    (o : TableSumcheck.Output S L k) :
    (∀ c ∈ pool S L k M o, c.Holds (fun u ↦ ofK (q u))) ↔
      BoundaryHold S L k o.bus w ∧ CommittedHold S L k o w := by
  rw [← boundaryClaims_holds_iff hM hbd w q agree, ← valueClaims_holds_iff hM w q agree]
  simp only [pool, List.mem_append]
  exact ⟨fun h ↦ ⟨fun c hc ↦ h c (Or.inl hc), fun c hc ↦ h c (Or.inr hc)⟩,
    fun h c hc ↦ hc.elim (h.1 c) (h.2 c)⟩

end CompStark.Tables.Composed
