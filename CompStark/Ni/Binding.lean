/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.FirstQueries

/-! # Binding commitments from a log

BCS consistency (`Ni/Bcs.lean`) asks that every accepted opening against the proof's commitments
open the rows extracted from a cache (`Binding`), for every opening, not only those the verifier
checked. The verifier's run on an answer table only depends on the answers to the keys it
queries, so the table can be changed elsewhere (`evalWithAnswerFn_congr`): `fresh log answer
dstar` keeps the answers to the keys of `log` and answers every other hash query `dstar`, a digest
that no query of `log` answers or holds in its key. With no digest clashes in `log`, an opening
accepted against a digest of `log` then uses only hash queries of `log` (`climb_cached`: once a
climb leaves the log it is stuck at `dstar`), so it opens the extracted rows (D's
`extractRow_eq_of_verifyBatch`; `binding_fresh`).
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Iop CompStark.RandomOracle OracleSpec OracleComp

variable {F : Type} [BaseField F]

variable {K : Nat}

/-! ### Changing the answers outside a run -/

omit [BaseField F] in
/-- A computation's result on an answer table depends only on the answers to the keys it
queries. -/
theorem evalWithAnswerFn_congr {α : Type} (answer answer' : (q : Query F) → Answer K q) :
    ∀ (oa : OracleComp (spec F K) α), (∀ e ∈ tableQueryLog oa answer, answer' e.1 = answer e.1) →
      evalWithAnswerFn (QueryImpl.ofFn answer') oa = evalWithAnswerFn (QueryImpl.ofFn answer) oa
  := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => intro _; rfl
  | query_bind t k ih =>
    intro h
    rw [tableQueryLog_query_bind] at h
    have ht : answer' t = answer t := h _ List.mem_cons_self
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply, ht]
    exact ih _ fun e he ↦ h e (List.mem_cons_of_mem _ he)

/-- The digests of a log: its answers' and its keys'. -/
def logDigests (log : QueryLog (spec F K)) : List (Digest F) :=
  log.flatMap fun e ↦ digestOf e.1 e.2 :: keyDigests e.1

theorem length_logDigests_le (log : QueryLog (spec F K)) :
    (logDigests log).length ≤ 3 * log.length := by
  induction log with
  | nil => simp only [logDigests, List.flatMap_nil, List.length_nil, Nat.zero_le]
  | cons e log ih =>
    simp only [logDigests, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have := length_keyDigests_le e.1
    omega

/-- A digest outside a list shorter than the digests. -/
theorem exists_not_mem (l : List (Digest F)) (h : l.length < Fintype.card (Digest F)) :
    ∃ d, d ∉ l := by
  classical
  by_contra hall
  simp only [not_exists, not_not] at hall
  have hsub : (Finset.univ : Finset (Digest F)) ⊆ l.toFinset := fun d _ ↦ List.mem_toFinset.mpr
      (hall d)
  have := (Finset.card_le_card hsub).trans (List.toFinset_card_le l)
  rw [Finset.card_univ] at this
  omega

/-- The answers of `log`, and `dstar` to every other hash query. -/
def fresh (log : QueryLog (spec F K)) (answer : (q : Query F) → Answer K q) (dstar : Digest F) :
    (q : Query F) → Answer K q
  | .duplex cap input => answer (.duplex cap input)
  | .leaf row => if Query.leaf row ∈ log.map Sigma.fst then answer (.leaf row) else dstar
  | .node left right =>
    if Query.node left right ∈ log.map Sigma.fst then answer (.node left right) else dstar

theorem fresh_of_mem (log : QueryLog (spec F K)) (answer : (q : Query F) → Answer K q)
    (dstar : Digest F) (t : Query F) (ht : t ∈ log.map Sigma.fst) :
    fresh log answer dstar t = answer t := by
  cases t <;> simp only [fresh, ht, ↓reduceIte]

/-! ### Climbing out of the log -/

section Climb
variable {d : Nat} (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d)
  (values : List (List F)) (dstar : Vector F d) (cached : Vector F d → Vector F d → Prop)

omit [BaseField F] in
/-- A climb that does not end at `dstar` compresses only cached pairs, if compressing an uncached
pair or a pair with `dstar` gives `dstar`. -/
theorem climb_cached (hfresh : ∀ a b, ¬ cached a b → compress a b = dstar)
    (hstuck : ∀ a b, (a = dstar ∨ b = dstar) → ¬ cached a b) :
    ∀ (path : List (Vector F d)) (leaf : Vector F d) (i padded : Nat),
      Merkle.climb hash compress values path [] i padded leaf ≠ dstar →
        leaf ≠ dstar ∧ ∀ pair ∈ Merkle.climbPairs compress leaf i path, cached pair.1 pair.2
  | [], leaf, _, _, h => ⟨h, fun _ hp ↦ absurd hp (List.not_mem_nil)⟩
  | sib :: sibs, leaf, i, padded, h => by
    set pair := if i % 2 = 0 then (leaf, sib) else (sib, leaf) with hpair
    have hclimb : Merkle.climb hash compress values (sib :: sibs) [] i padded leaf =
        Merkle.climb hash compress values sibs [] (i / 2) (padded / 2)
          (compress pair.1 pair.2) := by
      by_cases hi : i % 2 = 0 <;> simp only [Merkle.climb, hpair, hi, ↓reduceIte]
    rw [hclimb] at h
    obtain ⟨hnext, hrest⟩ := climb_cached hfresh hstuck sibs _ (i / 2) (padded / 2) h
    have hc : cached pair.1 pair.2 := by
      by_contra hc
      exact hnext (hfresh _ _ hc)
    refine ⟨fun hl ↦ hstuck pair.1 pair.2 ?_ hc, fun p hp ↦ ?_⟩
    · by_cases hi : i % 2 = 0 <;> simp only [hpair, hi, ↓reduceIte, hl, true_or, or_true]
    · simp only [Merkle.climbPairs, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hc
      · exact hrest p hp

end Climb

/-- An accepted single-height opening climbs from the hash of the opened rows to the
commitment. -/
theorem climb_of_verifyBatch {d : Nat} (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d) (root : Vector F d) (n k i : Nat)
    (hn : 0 < n) (values : List (List F)) (path : List (Vector F d))
    (hv : Merkle.verifyBatch hash compress root (List.replicate n (2 ^ k)) i values path = true) :
    Merkle.climb hash compress values path [] i (2 ^ k) (hash values.flatten) = root := by
  have hlog : Nat.log2 (2 ^ k).nextPowerOfTwo = k := Merkle.log2Ceil_two_pow k
  have hlen : path.length = k := by
    simp only [Merkle.verifyBatch, Merkle.heightGroups_replicate n _ hn, Bool.and_eq_true,
      beq_iff_eq, hlog] at hv
    exact hv.1.1.2
  have hdepth : path.reverse.length = (BinaryTree.SkeletonLeafIndex.ofNat k i).depth := by
    rw [List.length_reverse, hlen, BinaryTree.SkeletonLeafIndex.depth_ofNat]
  have hroot := ((Merkle.verifyBatch_iff hash compress root n k i hn values path ⟨_, hdepth⟩
    rfl).mp hv).2.2
  rwa [← Merkle.climb_eq_getPutativeRootWithHash hash compress values i (2 ^ k) _ k path _
    ⟨path.reverse, hdepth⟩ rfl rfl] at hroot

/-! ### Binding -/

/-- **Binding from a log.** With no digest clashes in `log`, answered by `answer`, the primitives
on `fresh log answer dstar` bind every digest of `log` to the rows extracted from it. -/
theorem binding_fresh (answer : (q : Query F) → Answer K q) (log : QueryLog (spec F K))
    (hcons : Consistent answer log) (hclash : NoClash log) (dstar : Digest F)
    (hdstar : dstar ∉ logDigests log) (root : Digest F) (hroot : root ∈ logDigests log) :
    Binding (logCache log) (idealOf (fresh log answer dstar)) root := by
  intro n k i values path hn hv
  set g' := fresh log answer dstar
  set hash : List F → Digest F := fun row ↦ g' (.leaf row)
  set compress : Digest F → Digest F → Digest F := fun a b ↦ g' (.node a b)
  have hv' : Merkle.verifyBatch hash compress root (List.replicate n (2 ^ k)) i values path =
      true := hv
  have hclimb := climb_of_verifyBatch hash compress root n k i hn values path hv'
  have hmem_digests : ∀ e ∈ log, ∀ x ∈ keyDigests e.1, x ∈ logDigests log := fun e he x hx ↦
    List.mem_flatMap.mpr ⟨e, he, List.mem_cons_of_mem _ hx⟩
  have hfresh_node : ∀ a b, ¬ Query.node a b ∈ log.map Sigma.fst → compress a b = dstar :=
    fun a b h ↦ by simp only [compress, g', fresh, h, ↓reduceIte]
  have hstuck : ∀ a b, (a = dstar ∨ b = dstar) → ¬ Query.node a b ∈ log.map Sigma.fst := by
    intro a b hab hmem
    obtain ⟨e, he, hek⟩ := List.mem_map.mp hmem
    refine hdstar ?_
    rcases hab with rfl | rfl
    · exact hmem_digests e he _ (by rw [hek]; simp only [keyDigests, List.mem_cons, true_or])
    · exact hmem_digests e he _ (by rw [hek]; simp only [keyDigests, List.mem_cons,
        List.not_mem_nil, or_false, or_true])
  obtain ⟨hleaf, hnodes⟩ := climb_cached hash compress values dstar
    (fun a b ↦ Query.node a b ∈ log.map Sigma.fst) hfresh_node hstuck path _ i (2 ^ k)
    (by rw [hclimb]; rintro rfl; exact hdstar hroot)
  have hleaf_mem : Query.leaf values.flatten ∈ log.map Sigma.fst := by
    by_contra h
    exact hleaf (by simp only [hash, g', fresh, h, ↓reduceIte])
  refine Merkle.extractRow_eq_of_verifyBatch (logCache log) (logCache_injective hcons hclash)
    hash compress root n k i hn values path hv' ?_ fun pair hp ↦ ?_
  · show (⟨.leaf values.flatten, g' (.leaf values.flatten)⟩ : (q : Query F) × Answer K q) ∈ log
    rw [show g' (.leaf values.flatten) = answer (.leaf values.flatten) from
      fresh_of_mem log answer dstar _ hleaf_mem]
    exact mk_mem_of_consistent hcons hleaf_mem
  · have hm := hnodes pair hp
    show (⟨.node pair.1 pair.2, g' (.node pair.1 pair.2)⟩ : (q : Query F) × Answer K q) ∈ log
    rw [show g' (.node pair.1 pair.2) = answer (.node pair.1 pair.2) from
      fresh_of_mem log answer dstar _ hm]
    exact mk_mem_of_consistent hcons hm

end CompStark.Ni
