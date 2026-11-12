/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Basic
public import CompStark.Tables.BusOutput
public import CompStark.Multilinear.Algebra.Stacking
public import CompStark.Pcs.BinaryDomain

/-! The stacked commitment of a system: every committed column of every table, tallest table first,
in one aligned base-field table. A claim on a committed column at a point is the stack's extension
at the point lifted by the column's selector bits, a weighted claim of the polynomial commitment
(`stackClaim_holds_iff`). Virtual columns are not stacked; another argument opens them. -/

@[expose] public section

namespace CompStark.Tables.System

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear

variable (S : System K) (L : Layout S.tables.length)

/-- The committed columns of a table: those that are not virtual. -/
def committedColumns (t : Fin S.tables.length) : List ℕ :=
  (List.range (S.table t).air.width).filter fun c ↦ !(S.table t).virtual.contains c

/-- Every committed column, tallest table first. -/
def stackColumns : List (Fin S.tables.length × ℕ) :=
  ((List.finRange S.tables.length).flatMap fun t ↦ (S.committedColumns t).map (t, ·)).insertionSort
    fun a b ↦ L.logHeight b.1 ≤ L.logHeight a.1

/-- Stacked columns have decreasing heights. -/
theorem stackColumns_antitone :
    Antitone fun b : Fin (S.stackColumns L).length ↦ L.logHeight (S.stackColumns L)[b].1 := by
  intro a b hab
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · let r := fun a b : Fin S.tables.length × ℕ ↦ L.logHeight b.1 ≤ L.logHeight a.1
    have : Std.Total r := ⟨fun a b ↦ le_total _ _⟩
    have : IsTrans (Fin S.tables.length × ℕ) r := ⟨fun a b c h1 h2 ↦ le_trans h2 h1⟩
    have hp := List.pairwise_insertionSort r
      ((List.finRange S.tables.length).flatMap fun t ↦ (S.committedColumns t).map (t, ·))
    exact List.pairwise_iff_getElem.mp hp a.val b.val a.isLt b.isLt h

/-- The stack's aligned blocks: one per committed column, on its table's variables. -/
@[reducible] def stackBlocks : Algebra.Blocks where
  n := (S.stackColumns L).length
  size b := L.logHeight (S.stackColumns L)[b].1
  descending := S.stackColumns_antitone L

/-- A stacked column is a committed column of its table. -/
theorem mem_stackColumns (t : Fin S.tables.length) (c : ℕ) :
    (t, c) ∈ S.stackColumns L ↔ c ∈ S.committedColumns t := by
  rw [stackColumns, (List.perm_insertionSort _ _).mem_iff]
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨t', c', hc, rfl, rfl⟩
    exact hc
  · intro hc
    exact ⟨t, c, hc, rfl, rfl⟩

/-- The stack's size: one window of its table's height per committed column. -/
theorem stackBlocks_total : (S.stackBlocks L).total =
    (((List.finRange S.tables.length).flatMap fun t ↦ (S.committedColumns t).map (t, ·)).map
      fun p ↦ 2 ^ L.logHeight p.1).sum := by
  rw [Algebra.Blocks.total_eq_sum]
  rw [← ((List.perm_insertionSort (fun a b : Fin S.tables.length × ℕ ↦ L.logHeight b.1 ≤ L.logHeight a.1)
    ((List.finRange S.tables.length).flatMap fun t ↦ (S.committedColumns t).map (t, ·))).map
      (fun p : Fin S.tables.length × ℕ ↦ 2 ^ L.logHeight p.1)).sum_eq]
  change _ = ((S.stackColumns L).map fun p ↦ 2 ^ L.logHeight p.1).sum
  rw [← List.sum_ofFn]
  congr 1
  exact List.ofFn_getElem_eq_map (S.stackColumns L) (fun p ↦ 2 ^ L.logHeight p.1)

/-- The number of variables the stack needs. -/
def stackVars : ℕ := Nat.clog 2 (S.stackBlocks L).total

/-- The stack fits its variables. -/
theorem total_le_stackVars : (S.stackBlocks L).total ≤ 2 ^ S.stackVars L :=
  Nat.le_pow_clog (by decide) _

/-- The values of a stacked column, row by row. -/
def columnValues (w : Witness K S.tables.length) (b : Fin (S.stackColumns L).length) :
    CompPoly.CMlPolynomialEval K ((S.stackBlocks L).size b) :=
  Vector.ofFn fun i ↦ (((w (S.stackColumns L)[b].1).getD i.val #[]).getD (S.stackColumns L)[b].2 0)

/-- The stack of a witness as a table on `M` variables; cells no column covers are zero. -/
def stack (M : ℕ) (w : Witness K S.tables.length) : Whir.Table K M :=
  let values := (S.stackBlocks L).stackAt (S.columnValues L w) M 0
  fun u ↦ values[Pcs.cubeIndex M u]

/-- A point of a stacked column lifted to the stack: the point below the column's height, the bits
of its offset above. -/
def liftPoint (M : ℕ) (b : Fin (S.stackColumns L).length) (z : List E) : Fin M → E :=
  fun k ↦ if k.val < L.logHeight (S.stackColumns L)[b].1 then z.getD k.val 0
    else bit ((S.stackBlocks L).offset b) k.val

/-- A claim on a stacked column at a point, as a weighted claim on the stack. -/
def stackClaim (M : ℕ) (b : Fin (S.stackColumns L).length) (z : List E) (value : E) :
    Whir.Claim E M :=
  ⟨Whir.eqWeight (S.liftPoint L M b z), value⟩

/-- A Boolean table's extension is the low-bit-first extension of its numeric values. -/
theorem whirMle_eq_mle (n : ℕ) (f : Whir.Table E n) (p : Fin n → E) :
    Whir.mle f p = mle n (fun x ↦ if h : x < 2 ^ n then f (Pcs.mask n ⟨x, h⟩) else 0) (List.ofFn p) := by
  unfold Whir.mle mle
  rw [← (Pcs.cubeEquiv n).sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Pcs.cubeEquiv_apply, Fin.is_lt, ↓reduceDIte, Fin.eta]
  rw [mul_comm]
  apply congrArg (_ * ·)
  unfold Whir.eqWeight
  apply Finset.prod_congr rfl
  intro k _
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn, k.isLt]), List.getElem_ofFn]
  simp only [Pcs.mask, eqFactor, bit]
  by_cases hb : (x.val).testBit k.val = true <;> simp only [hb, Fin.eta, Bool.false_eq_true, ↓reduceIte] <;> ring

/-- At a point whose high coordinates are the bits of an aligned offset, an extension is the
extension of the window at that offset. -/
theorem mle_window (h M : ℕ) (hh : h ≤ M) (values : ℕ → E) (off : ℕ) (hdvd : 2 ^ h ∣ off)
    (hoff : off + 2 ^ h ≤ 2 ^ M) (z : List E) :
    mle M values (List.ofFn fun k : Fin M ↦ if k.val < h then z.getD k.val 0 else bit off k.val) =
      mle h (fun i ↦ values (off + i)) z := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hh
  obtain ⟨j0, rfl⟩ := hdvd
  have hj0 : j0 < 2 ^ m := by
    rw [pow_add] at hoff
    by_contra hc
    have : 2 ^ h * 2 ^ m ≤ 2 ^ h * j0 := Nat.mul_le_mul_left _ (by omega)
    have := Nat.two_pow_pos h
    nlinarith
  unfold mle
  rw [Algebra.sum_cube_split]
  rw [Finset.sum_eq_single (⟨j0, hj0⟩ : Fin (2 ^ m))]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [Algebra.cubeIndex_val]
    rw [show i.val + 2 ^ h * j0 = 2 ^ h * j0 + i.val by ring]
    apply congrArg (_ * ·)
    rw [Fin.prod_univ_add]
    have hhi : (∏ k : Fin m, eqFactor
        ((List.ofFn fun k : Fin (h + m) ↦ if k.val < h then z.getD k.val 0 else bit (2 ^ h * j0) k.val).getD
          (Fin.natAdd h k).val 0) (bit (2 ^ h * j0 + i.val) (Fin.natAdd h k).val)) = 1 := by
      apply Finset.prod_eq_one
      intro k _
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn, Fin.is_lt]), List.getElem_ofFn]
      simp only [Fin.natAdd, show ¬ h + k.val < h by omega, ↓reduceIte]
      have t1 := Algebra.testBit_cubeIndex (k := h) (m := m) i ⟨j0, hj0⟩ (h + k.val)
      simp only [Algebra.cubeIndex_val, show ¬ h + k.val < h by omega, ↓reduceIte,
        Nat.add_sub_cancel_left] at t1
      rw [Nat.add_comm] at t1
      have t2 : (2 ^ h * j0).testBit (h + k.val) = j0.testBit k.val := by
        rw [Nat.mul_comm, Nat.testBit_mul_two_pow]
        simp only [show h ≤ h + k.val by omega, decide_true, Bool.true_and, Nat.add_sub_cancel_left]
      have e1 : bit (2 ^ h * j0) (h + k.val) = bit (2 ^ h * j0 + i.val) (h + k.val) := by
        simp only [bit, t1, t2]
      rw [e1]
      simp only [eqFactor, bit]
      split <;> ring
    rw [hhi, mul_one]
    apply Finset.prod_congr rfl
    intro k _
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn, Fin.is_lt]), List.getElem_ofFn]
    simp only [Fin.castAdd, k.isLt, ↓reduceIte, Fin.val_castLE]
    have t := Algebra.testBit_cubeIndex (k := h) (m := m) i ⟨j0, hj0⟩ k.val
    simp only [Algebra.cubeIndex_val, k.isLt, ↓reduceIte] at t
    rw [Nat.add_comm] at t
    have e : bit (2 ^ h * j0 + i.val) k.val = bit i.val k.val := by simp only [bit, t]
    rw [e]
  · intro j _ hj
    apply Finset.sum_eq_zero
    intro i _
    obtain ⟨a, ha⟩ : ∃ a : Fin m, j.val.testBit a.val ≠ j0.testBit a.val := by
      by_contra hall
      push Not at hall
      apply hj
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro a
      by_cases ha : a < m
      · exact hall ⟨a, ha⟩
      · rw [Nat.testBit_eq_false_of_lt (j.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (hj0.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (i := Fin.natAdd h a) (Finset.mem_univ _)
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn, Fin.is_lt]), List.getElem_ofFn]
    simp only [Fin.natAdd, show ¬ h + a.val < h by omega, ↓reduceIte]
    have t1 := Algebra.testBit_cubeIndex (k := h) (m := m) i j (h + a.val)
    simp only [Algebra.cubeIndex_val, show ¬ h + a.val < h by omega, ↓reduceIte,
      Nat.add_sub_cancel_left] at t1
    have t2 : (2 ^ h * j0).testBit (h + a.val) = j0.testBit a.val := by
      rw [mul_comm, Nat.testBit_mul_two_pow]
      simp only [show h ≤ h + a.val by omega, decide_true, Bool.true_and, Nat.add_sub_cancel_left]
    simp only [eqFactor, bit, Algebra.cubeIndex_val, t1, t2]
    cases hj1 : j.val.testBit a.val <;> cases hj2 : j0.testBit a.val <;> simp_all
  · intro hn
    exact absurd (Finset.mem_univ _) hn

variable (M : ℕ)

/-- A weighted stack claim holds exactly when its value is the extension of the stack's window. -/
theorem stackClaim_holds_iff (hM : (S.stackBlocks L).total ≤ 2 ^ M) (q : Whir.Table K M)
    (b : Fin (S.stackColumns L).length) (z : List E) (value : E) :
    (S.stackClaim L M b z value).Holds (fun u ↦ ofK (q u)) ↔
      value = mle (L.logHeight (S.stackColumns L)[b].1)
        (fun i ↦ if h : (S.stackBlocks L).offset b + i < 2 ^ M then
          ofK (q (Pcs.mask M ⟨(S.stackBlocks L).offset b + i, h⟩)) else 0) z := by
  have hle := (S.stackBlocks L).size_le hM b
  have hdvd := (S.stackBlocks L).pow_size_dvd_offset b
  have hoff := ((S.stackBlocks L).offset_add_pow_le_total b).trans hM
  unfold stackClaim Whir.Claim.Holds
  change Whir.mle (fun u ↦ ofK (q u)) (S.liftPoint L M b z) = value ↔ _
  rw [whirMle_eq_mle, eq_comm]
  unfold liftPoint
  rw [mle_window _ M hle _ _ hdvd hoff z]

/-- On the stack of a witness, a stacked column's window holds the column. -/
theorem stack_window (hM : (S.stackBlocks L).total ≤ 2 ^ M) (w : Witness K S.tables.length)
    (b : Fin (S.stackColumns L).length) (i : ℕ) (hi : i < 2 ^ L.logHeight (S.stackColumns L)[b].1)
    (h : (S.stackBlocks L).offset b + i < 2 ^ M) :
    S.stack L M w (Pcs.mask M ⟨(S.stackBlocks L).offset b + i, h⟩) =
      ((w (S.stackColumns L)[b].1).getD i #[]).getD (S.stackColumns L)[b].2 0 := by
  unfold stack
  have hcube : Pcs.cubeIndex M (Pcs.mask M ⟨(S.stackBlocks L).offset b + i, h⟩) =
      ⟨(S.stackBlocks L).offset b + i, h⟩ :=
    (Pcs.cubeEquiv M).left_inv _
  simp only [hcube, Fin.getElem_fin]
  rw [(S.stackBlocks L).stackAt_getElem_of_inWindow (b := b) _ _ h ⟨by omega, by simpa using hi⟩]
  simp only [columnValues, Vector.getElem_ofFn, Nat.add_sub_cancel_left, Fin.getElem_fin]

/-- A weighted stack claim on the stack of a witness holds exactly when it is the column's
extension. -/
theorem stackClaim_stack_iff (hM : (S.stackBlocks L).total ≤ 2 ^ M) (w : Witness K S.tables.length)
    (b : Fin (S.stackColumns L).length) (z : List E) (value : E) :
    (S.stackClaim L M b z value).Holds (fun u ↦ ofK (S.stack L M w u)) ↔
      value = S.column L w (S.stackColumns L)[b].1 (S.stackColumns L)[b].2 z := by
  rw [stackClaim_holds_iff S L M hM]
  have hoff := ((S.stackBlocks L).offset_add_pow_le_total b).trans hM
  have he : mle (L.logHeight (S.stackColumns L)[b].1)
      (fun i ↦ if h : (S.stackBlocks L).offset b + i < 2 ^ M then
        ofK (S.stack L M w (Pcs.mask M ⟨(S.stackBlocks L).offset b + i, h⟩)) else 0) z =
      S.column L w (S.stackColumns L)[b].1 (S.stackColumns L)[b].2 z := by
    apply mle_congr_values
    intro i hi
    have hi' : (S.stackBlocks L).offset b + i < 2 ^ M := by
      have : 2 ^ (S.stackBlocks L).size b = 2 ^ L.logHeight (S.stackColumns L)[b].1 := rfl
      omega
    rw [dite_eq_left hi', stack_window S L M hM w b i hi]
  rw [he]

/-- Stacked columns are distinct. -/
theorem stackColumns_nodup : (S.stackColumns L).Nodup := by
  rw [stackColumns, (List.perm_insertionSort _ _).nodup_iff]
  apply List.nodup_flatMap.mpr
  refine ⟨fun t _ ↦ (List.nodup_range.filter _).map fun _ _ h ↦ (Prod.mk.inj h).2, ?_⟩
  apply (List.nodup_finRange S.tables.length).pairwise_of_forall_ne
  intro a _ b _ hab
  simp only [Function.onFun, List.disjoint_left, List.mem_map]
  rintro x ⟨c, -, rfl⟩ ⟨c', -, h⟩
  exact hab (Prod.mk.inj h).1.symm

/-- Cell `c` of row `i` of table `t` read off a table on `M` variables: its stacked column's
window, zero for a column that is not stacked. -/
def readCell (q : Whir.Table K M) (t : Fin S.tables.length) (i c : ℕ) : K :=
  match (S.stackColumns L).finIdxOf? (t, c) with
  | some b => if h : (S.stackBlocks L).offset b + i < 2 ^ M then
      q (Pcs.mask M ⟨(S.stackBlocks L).offset b + i, h⟩) else 0
  | none => 0

/-- The witness read off a table on `M` variables, of the system's shape; virtual columns are zero. -/
def read (q : Whir.Table K M) : Witness K S.tables.length := fun t ↦
  List.ofFn fun i : Fin (2 ^ L.logHeight t) ↦
    Array.ofFn fun c : Fin (S.table t).air.width ↦ S.readCell L M q t i.val c.val

/-- A read witness has the system's shape. -/
theorem read_shaped (q : Whir.Table K M) : S.Shaped L (S.read L M q) := by
  intro t
  refine ⟨by simp only [read, List.length_ofFn], ?_⟩
  intro row hrow
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
  simp only [Array.size_ofFn]

/-- A read cell inside the table is its stacked column's window. -/
theorem read_cell (q : Whir.Table K M) (t : Fin S.tables.length) (i c : ℕ)
    (hi : i < 2 ^ L.logHeight t) (hc : c < (S.table t).air.width) :
    ((S.read L M q t).getD i #[]).getD c 0 = S.readCell L M q t i c := by
  simp only [read]
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn, hi]), List.getElem_ofFn,
    Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hc, ↓reduceDIte, Option.getD_some]

/-- The read cell of a stacked column is its window. -/
theorem readCell_stacked (q : Whir.Table K M) (b : Fin (S.stackColumns L).length) (i : ℕ) :
    S.readCell L M q (S.stackColumns L)[b].1 i (S.stackColumns L)[b].2 =
      if h : (S.stackBlocks L).offset b + i < 2 ^ M then
        q (Pcs.mask M ⟨(S.stackBlocks L).offset b + i, h⟩) else 0 := by
  have hidx : (S.stackColumns L).finIdxOf? ((S.stackColumns L)[b].1, (S.stackColumns L)[b].2) = some b := by
    apply List.finIdxOf?_eq_some_iff.mpr
    refine ⟨rfl, fun j hj heq ↦ ?_⟩
    have := (List.Nodup.getElem_inj_iff (S.stackColumns_nodup L)).mp heq
    exact absurd this (by omega)
  unfold readCell
  rw [hidx]

/-- A weighted stack claim holds exactly when its value is the read column's extension. -/
theorem stackClaim_read_iff (hM : (S.stackBlocks L).total ≤ 2 ^ M) (q : Whir.Table K M)
    (b : Fin (S.stackColumns L).length) (z : List E) (value : E) :
    (S.stackClaim L M b z value).Holds (fun u ↦ ofK (q u)) ↔
      value = S.column L (S.read L M q) (S.stackColumns L)[b].1 (S.stackColumns L)[b].2 z := by
  rw [stackClaim_holds_iff S L M hM]
  have hc : (S.stackColumns L)[b].2 < (S.table (S.stackColumns L)[b].1).air.width := by
    have hm := (S.mem_stackColumns L _ _).mp (List.getElem_mem (l := S.stackColumns L) b.isLt)
    exact List.mem_range.mp (List.mem_filter.mp hm).1
  have he : mle (L.logHeight (S.stackColumns L)[b].1)
      (fun i ↦ if h : (S.stackBlocks L).offset b + i < 2 ^ M then
        ofK (q (Pcs.mask M ⟨(S.stackBlocks L).offset b + i, h⟩)) else 0) z =
      S.column L (S.read L M q) (S.stackColumns L)[b].1 (S.stackColumns L)[b].2 z := by
    apply mle_congr_values
    intro i hi
    rw [read_cell S L M q _ i _ hi hc, readCell_stacked]
    split_ifs
    · rfl
    · exact (map_zero (algebraMap K E)).symm
  rw [he]

/-- Reading a committed cell off the stack of a witness gives the witness's cell. -/
theorem readCell_stack (hM : (S.stackBlocks L).total ≤ 2 ^ M) (w : Witness K S.tables.length)
    (t : Fin S.tables.length) (i c : ℕ) (hi : i < 2 ^ L.logHeight t) (hc : c ∈ S.committedColumns t) :
    S.readCell L M (S.stack L M w) t i c = ((w t).getD i #[]).getD c 0 := by
  have mem := (S.mem_stackColumns L t c).mpr hc
  obtain ⟨b, hb⟩ : ∃ b, (S.stackColumns L).finIdxOf? (t, c) = some b := by
    cases h : (S.stackColumns L).finIdxOf? (t, c) with
    | none => exact absurd mem (List.finIdxOf?_eq_none_iff.mp h)
    | some b => exact ⟨b, rfl⟩
  have hget := (List.finIdxOf?_eq_some_iff.mp hb).1
  have hsizeb : L.logHeight (S.stackColumns L)[b].1 = L.logHeight t := by rw [hget]
  have hbound : (S.stackBlocks L).offset b + i < 2 ^ M := by
    have := ((S.stackBlocks L).offset_add_pow_le_total b).trans hM
    have h2 : 2 ^ (S.stackBlocks L).size b = 2 ^ L.logHeight t := by
      change 2 ^ L.logHeight (S.stackColumns L)[b].1 = _
      rw [hsizeb]
    omega
  unfold readCell
  rw [hb]
  simp only [hbound, ↓reduceDIte]
  rw [stack_window S L M hM w b i (by rw [hsizeb]; exact hi) hbound, hget]

/-- With no virtual columns, reading the stack of a witness of the system's shape returns the
witness. -/
theorem read_stack (hM : (S.stackBlocks L).total ≤ 2 ^ M) (w : Witness K S.tables.length)
    (shaped : S.Shaped L w) (novirtual : ∀ t, (S.table t).virtual = []) :
    S.read L M (S.stack L M w) = w := by
  funext t
  obtain ⟨hlen, hsize⟩ := shaped t
  apply List.ext_getElem (by simp only [read, List.length_ofFn, hlen])
  intro i h1 h2
  simp only [read, List.getElem_ofFn]
  have hrow := hsize _ (List.getElem_mem h2)
  apply Array.ext (by simp only [Array.size_ofFn, hrow])
  intro c hc1 hc2
  simp only [Array.getElem_ofFn]
  have hi : i < 2 ^ L.logHeight t := by simpa only [read, List.length_ofFn] using h1
  have hc : c < (S.table t).air.width := by simpa only [Array.size_ofFn] using hc1
  have hcomm : c ∈ S.committedColumns t := by
    simp only [committedColumns, novirtual, List.contains_nil, Bool.not_false, List.filter_true,
      List.mem_range, hc]
  rw [readCell_stack S L M hM w t i c hi hcomm]
  simp only [List.getD_eq_getElem _ _ h2, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hc2,
    Option.getD_some]

end CompStark.Tables.System
