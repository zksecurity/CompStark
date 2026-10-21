/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.Binding
public import CompStark.Ni.BatchRun
public import CompStark.Merkle.ExtractMixed

/-! # Binding commitments of mixed heights

The batch STARK commits to matrices of several heights under one root, Plonky3's trees with
injected matrices. `BindingM`: every accepted opening against a root opens the rows extracted from
a cache (`Merkle.extractGroup`), group by group of matrices of one height. As for one height
(`binding_fresh`), the primitives on the answers of a log without digest clashes, and a digest
outside it elsewhere, bind every digest of the log (`bindingM_fresh`): an accepted climb only makes
queries of the log (`Merkle.climbCached_of_fresh`).

`Merkle.matColumn`: the extracted column `j` of matrix `t` of a commitment, read off its group's
rows at the matrix's offset among the matrices of its height; an accepted opening that binds opens
it (`matColumn_eq`).
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

/-- An accepted opening climbs from the hash of its tallest rows to the commitment. -/
theorem climb_of_verifyBatchM {d : Nat} (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d) (root : Vector F d) (hs : List ℕ)
    (i : ℕ) (values : List (List F)) (path : List (Vector F d))
    (hv : Merkle.verifyBatch hash compress root hs i values path = true) :
    ∃ maxH tallest rest, Merkle.heightGroups hs = (maxH, tallest) :: rest ∧
      Merkle.climb hash compress values path rest i maxH.nextPowerOfTwo
        (Merkle.hashRows hash values tallest) = root := by
  unfold Merkle.verifyBatch at hv
  split at hv
  · exact absurd hv Bool.false_ne_true
  · rename_i maxH tallest rest hG
    simp only [Bool.and_eq_true, beq_iff_eq] at hv
    exact ⟨maxH, tallest, rest, hG, hv.2⟩

variable {K : Nat}

/-- **Binding from a log, at mixed heights.** With no digest clashes in `log`, answered by
`answer`, the primitives on `fresh log answer dstar` bind every digest of `log`, for matrices of
heights `2 ^ j ≤ 2 ^ K`, some of height `2 ^ K`. -/
theorem bindingM_fresh {bd : Digest F → List F → Digest F} (answer : (q : Query F) → Answer K q)
    (log : QueryLog (spec F K)) (hcons : Consistent answer log) (hclash : NoClash bd log)
    (dstar : Digest F) (hdstar : dstar ∉ logDigests bd log) (root : Digest F)
    (hroot : root ∈ logDigests bd log) (L : ℕ) (hs : List ℕ)
    (hpow : ∀ h ∈ hs, ∃ j ≤ L, h = 2 ^ j) (htop : 2 ^ L ∈ hs) :
    BindingM (logCache log) (idealOf (fresh log answer dstar)) root L hs := by
  intro i values path hv
  set g' := fresh log answer dstar
  set hash : List F → Digest F := fun row ↦ g' (.leaf row)
  set compress : Digest F → Digest F → Digest F := fun a b ↦ g' (.node a b)
  have hv' : Merkle.verifyBatch hash compress root hs i values path = true := hv
  have hmem_digests : ∀ e ∈ log, ∀ x ∈ keyDigests bd e.1, x ∈ logDigests bd log :=
    fun e he x hx ↦ List.mem_flatMap.mpr ⟨e, he, List.mem_cons_of_mem _ hx⟩
  have hnode : ∀ a b, compress a b ≠ dstar → (logCache log).node a b (compress a b) := by
    intro a b h
    have hm : Query.node a b ∈ log.map Sigma.fst := by
      by_contra hm
      exact h (by simp only [compress, g', fresh, hm, ↓reduceIte])
    show (⟨.node a b, g' (.node a b)⟩ : (q : Query F) × Answer K q) ∈ log
    rw [show g' (.node a b) = answer (.node a b) from fresh_of_mem log answer dstar _ hm]
    exact mk_mem_of_consistent hcons hm
  have hleaf : ∀ row, hash row ≠ dstar → (logCache log).leaf row (hash row) := by
    intro row h
    have hm : Query.leaf row ∈ log.map Sigma.fst := by
      by_contra hm
      exact h (by simp only [hash, g', fresh, hm, ↓reduceIte])
    show (⟨.leaf row, g' (.leaf row)⟩ : (q : Query F) × Answer K q) ∈ log
    rw [show g' (.leaf row) = answer (.leaf row) from fresh_of_mem log answer dstar _ hm]
    exact mk_mem_of_consistent hcons hm
  have hstuck : ∀ a b, (a = dstar ∨ b = dstar) → compress a b = dstar := by
    intro a b hab
    have hm : Query.node a b ∉ log.map Sigma.fst := by
      intro hmem
      obtain ⟨e, he, hek⟩ := List.mem_map.mp hmem
      refine hdstar ?_
      rcases hab with rfl | rfl
      · exact hmem_digests e he _ (by rw [hek]; simp only [keyDigests, List.mem_cons, true_or])
      · exact hmem_digests e he _ (by rw [hek]; simp only [keyDigests, List.mem_cons,
          List.not_mem_nil, or_false, or_true])
    simp only [compress, g', fresh, hm, ↓reduceIte]
  obtain ⟨maxH, tallest, rest, hG, hclimb⟩ := climb_of_verifyBatchM hash compress root hs i values
    path hv'
  obtain ⟨keys, hk, hmem, hG'⟩ := Merkle.heightGroups_eq hs
  have hmax : maxH = 2 ^ L := by
    rw [hG'] at hG
    rcases keys with _ | ⟨a, ks⟩
    · exact absurd hG (by simp only [List.map_nil, reduceCtorEq, not_false_eq_true])
    · simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hG
      rw [← hG.1.1]
      obtain ⟨j, hj, rfl⟩ := hpow a ((hmem a).mp List.mem_cons_self)
      rcases List.mem_cons.mp ((hmem _).mpr htop) with h | h
      · exact h.symm
      · have := List.rel_of_pairwise_cons hk h
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) hj
        omega
  rw [hmax, Merkle.nextPowerOfTwo_two_pow] at hclimb
  have hne : root ≠ dstar := fun h ↦ hdstar (h ▸ hroot)
  obtain ⟨hx, hcc⟩ := Merkle.climbCached_of_fresh (logCache log) hash compress values dstar hnode
    hleaf hstuck path rest i _ _ (by rw [hclimb]; exact hne)
  refine Merkle.extractGroup_of_verifyBatch (logCache log) hash compress values
    (logCache_injective hcons hclash) root L hs hpow htop i path hv' ?_ ?_
  · rw [hG]
    intro g hg
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hg
    subst hg
    exact hleaf _ hx
  · rw [hG]
    intro g hg
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hg
    subst hg
    exact hcc

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

end CompStark.Ni
