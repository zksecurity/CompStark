/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.Rounds
public import CompStark.Ni.BatchRun
public import CompStark.Merkle.ExtractMixed

/-! # Binding commitments of mixed heights

The batch STARK commits to matrices of several heights under one root, Plonky3's trees with
injected matrices. `BindingM`: every accepted opening against a root opens the rows extracted from
a cache (`Merkle.extractGroup`), group by group of matrices of one height; `CapBindingM` the same
for every entry of a cap.

`Merkle.matColumn`: the extracted column `j` of matrix `t` of a commitment, read off its group's
rows at the matrix's offset among the matrices of its height; an accepted opening that binds opens
it (`matColumn_eq`, and `matColumnCap_eq` against a cap).
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Iop CompStark.RandomOracle OracleSpec OracleComp

variable {F : Type} [BaseField F]

/-! ### Binding -/

/-- Accepted openings against `root` of matrices of heights `hs`, at most `2 ^ K`, open the rows
extracted from `cache`, height by height. -/
def BindingM (cache : Merkle.Cache F (Digest F)) (H : Primitives F Id) (root : Digest F) (K : ℕ)
    (hs : List ℕ) : Prop :=
  ∀ (i : ℕ) (values : List (List F)) (path : List (Digest F)),
    verifyBatchH H root hs i values path = true →
    ∀ g ∈ Merkle.heightGroups hs, ∀ l, g.1 = 2 ^ l →
      Merkle.extractGroup cache (Merkle.injLevels K hs) K l (i >>> (K - l)) root =
        some (g.2.flatMap fun m ↦ values.getD m [])

/-- Accepted openings against every entry of the cap `cap` of height `capHeight` (capped at `K`,
`c` levels), of matrices of heights `hs` at most `2 ^ K`, open the rows extracted from `cache` in
the entry's subtree, whose matrices have the heights divided by `2 ^ c`. -/
def CapBindingM (cache : Merkle.Cache F (Digest F)) (H : Primitives F Id) (cap : Cap F)
    (capHeight K : ℕ) (hs : List ℕ) : Prop :=
  ∀ e, BindingM cache H (cap.toList.getD e 0) (K - min capHeight K)
    (hs.map (· / 2 ^ min capHeight K))

variable {K : Nat}

/-! ### Matrix columns -/

/-- Reading an entry past the rows of the earlier matrices of a concatenation, in increasing
order. -/
theorem getD_flatMap_offset (f : ℕ → List F) (w : ℕ → ℕ) :
    ∀ (L : List ℕ), L.Pairwise (· < ·) → (∀ t ∈ L, (f t).length = w t) → ∀ t ∈ L,
      ∀ j < w t, (L.flatMap f).getD (((L.filter (· < t)).map w).sum + j) 0 = (f t).getD j 0
  | [], _, _, t, ht, _, _ => absurd ht List.not_mem_nil
  | a :: L, hs, hw, t, ht, j, hj => by
    rw [List.flatMap_cons]
    rcases List.mem_cons.mp ht with rfl | ht
    · have hfilt : (t :: L).filter (· < t) = [] := List.filter_eq_nil_iff.mpr fun x hx h ↦ by
        rcases List.mem_cons.mp hx with rfl | hx
        · simp only [Nat.lt_irrefl, decide_false, Bool.false_eq_true] at h
        · have := List.rel_of_pairwise_cons hs hx
          simp only [decide_eq_true_eq] at h
          omega
      rw [hfilt, List.map_nil, List.sum_nil, Nat.zero_add, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [hw t List.mem_cons_self]; exact hj),
        ← List.getD_eq_getElem?_getD]
    · have hat : a < t := List.rel_of_pairwise_cons hs ht
      have hfilt : (a :: L).filter (· < t) = a :: L.filter (· < t) :=
        List.filter_cons_of_pos (by simp only [decide_eq_true_eq]; exact hat)
      have hfa := hw a List.mem_cons_self
      rw [hfilt, List.map_cons, List.sum_cons, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by rw [hfa]; omega), hfa,
        show w a + ((L.filter (· < t)).map w).sum + j - w a =
          ((L.filter (· < t)).map w).sum + j by omega, ← List.getD_eq_getElem?_getD]
      exact getD_flatMap_offset f w L hs.of_cons (fun t' ht' ↦ hw t' (List.mem_cons_of_mem _ ht'))
        t ht j hj

theorem range_filter_lt : ∀ (n t : ℕ), t ≤ n → (List.range n).filter (· < t) = List.range t
  | 0, t, h => by rw [Nat.le_zero.mp h]; rfl
  | n + 1, t, h => by
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · rw [List.range_succ, List.filter_append, range_filter_lt n t (by omega),
        List.filter_singleton, decide_eq_false (by omega)]
      simp only [Bool.cond_false, List.append_nil]
    · exact List.filter_eq_self.mpr fun x hx ↦ decide_eq_true (List.mem_range.mp hx)

/-- **An opening that binds opens the extracted columns.** -/
theorem matColumn_eq (cache : Merkle.Cache F (Digest F)) (H : Primitives F Id) (root : Digest F)
    (K : ℕ) (hs ws : List ℕ) (hb : BindingM cache H root K hs) (i : ℕ) (values : List (List F))
    (path : List (Digest F)) (hv : verifyBatchH H root hs i values path = true)
    (hw : ∀ t < hs.length, (values.getD t []).length = ws.getD t 0)
    (t m : ℕ) (ht : t < hs.length) (htm : hs.getD t 0 = 2 ^ m) (j : ℕ) (hj : j < ws.getD t 0) :
    Merkle.matColumn cache root K hs ws t j m (i >>> (K - m)) = (values.getD t []).getD j 0 := by
  obtain ⟨keys, hk, hmem, hG⟩ := Merkle.heightGroups_eq hs
  have hkey : 2 ^ m ∈ keys := (hmem _).mpr (by
    rw [← htm, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
    exact List.getElem_mem ht)
  set idx := (List.range hs.length).filter (hs.getD · 0 == 2 ^ m) with hidx
  have hg : (2 ^ m, idx) ∈ Merkle.heightGroups hs := by
    rw [hG]
    exact List.mem_map.mpr ⟨_, hkey, rfl⟩
  have hext := hb i values path hv _ hg m rfl
  unfold Merkle.matColumn
  rw [hext, Option.getD_some]
  have hoff : Merkle.matOffset hs ws t = ((idx.filter (· < t)).map (ws.getD · 0)).sum := by
    unfold Merkle.matOffset
    congr 2
    rw [hidx, List.filter_filter, ← range_filter_lt hs.length t ht.le, List.filter_filter]
    refine List.filter_congr fun x _ ↦ ?_
    rw [htm, beq_eq_decide, Bool.and_comm]
  rw [hoff]
  refine getD_flatMap_offset (values.getD · []) (ws.getD · 0) idx ?_ ?_ t ?_ j hj
  · exact (List.pairwise_lt_range.sublist List.filter_sublist)
  · intro t' ht'
    obtain ⟨h1, -⟩ := List.mem_filter.mp ht'
    exact hw t' (List.mem_range.mp h1)
  · exact List.mem_filter.mpr ⟨List.mem_range.mpr ht, by rw [htm]; exact beq_self_eq_true _⟩

theorem shiftRight_mod_two_pow (a s n : ℕ) (h : s ≤ n) :
    (a % 2 ^ n) >>> s = (a >>> s) % 2 ^ (n - s) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    show 2 ^ n = 2 ^ s * 2 ^ (n - s) by rw [← Nat.pow_add, Nat.add_sub_cancel' h],
    Nat.mod_mul_right_div_self]

/-- **An opening against a cap that binds opens the extracted columns.** -/
theorem matColumnCap_eq (cache : Merkle.Cache F (Digest F)) (H : Primitives F Id) (cap : Cap F)
    (capHeight K : ℕ) (hs ws : List ℕ) (hb : CapBindingM cache H cap capHeight K hs) (idx : ℕ)
    (values : List (List F)) (path : List (Digest F))
    (hv : verifyCapMixedH H cap capHeight hs K idx values path = true)
    (hw : ∀ t < hs.length, (values.getD t []).length = ws.getD t 0)
    (t m : ℕ) (ht : t < hs.length) (htm : hs.getD t 0 = 2 ^ m) (hcm : min capHeight K ≤ m)
    (hmK : m ≤ K) (j : ℕ) (hj : j < ws.getD t 0) :
    Merkle.matColumnCap cache cap.toList capHeight K hs ws t j m (idx >>> (K - m)) =
      (values.getD t []).getD j 0 := by
  set c := min capHeight K with hc
  unfold Merkle.matColumnCap
  have hmod : idx >>> (K - m) % 2 ^ (m - c) = (idx % 2 ^ (K - c)) >>> (K - c - (m - c)) := by
    rw [shiftRight_mod_two_pow _ _ _ (by omega), show K - c - (m - c) = K - m by omega,
      show K - c - (K - m) = m - c by omega]
  rw [← hc, ← Nat.shiftRight_add, show K - m + (m - c) = K - c by omega, hmod]
  refine matColumn_eq cache H _ (K - c) _ ws (hb _) _ values path hv
    (fun t' ht' ↦ hw t' (by rwa [List.length_map] at ht')) t (m - c)
    (by rw [List.length_map]; exact ht) ?_ j hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem ht,
    Option.map_some, Option.getD_some, ← List.getD_eq_getElem _ 0 ht, htm,
    Nat.pow_div hcm (by decide)]

end CompStark.Ni
