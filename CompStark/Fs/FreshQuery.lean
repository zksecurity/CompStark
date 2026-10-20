/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery

/-! # Fresh bad queries that see the query log

VCVio's `prEvent_randomOracle_le_of_bad_queries` bounds an event of a lazy random-oracle run by
`n · ε` when every bad key has resampling probability at most `ε`, but its bad predicate sees
only the key and the full answer table, not the order of the queries. Collisions, predictions and
extraction from the queries made so far need that order. Here the bad predicate takes the log
of the queries before the tested one:

* `prEvent_exists_fresh_bad_le`: if the event forces some query whose key was not queried
  before it to get an answer that is `bad` for the log before it, and a uniform answer is bad
  with probability at most `ε` after every log shorter than `n`, then an adaptive computation
  making at most `n` queries triggers the event with probability at most `n · ε`.

The proof follows VCVio's `prEvent_freshBadQuery_le`: run against a uniform complete answer
table, expose the answer to the next fresh query, and recurse with that query appended to the
log. The key domain may be infinite, by VCVio's restriction to the finitely many reachable keys.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace OracleComp

variable {D α : Type} {R : D → Type}

/-- Some query of `log`, made after the queries `pre`, has a key queried neither in `pre` nor
earlier in `log`, and an answer that is `bad` for the log before it. -/
def FreshBadAfter (bad : QueryLog (ofFn R) → (t : D) → R t → Prop)
    (pre log : QueryLog (ofFn R)) : Prop :=
  ∃ mid q post, log = mid ++ q :: post ∧ q.1 ∉ (pre ++ mid).map Sigma.fst ∧
    bad (pre ++ mid) q.1 q.2

/-- No queries, no fresh bad query. -/
theorem freshBadAfter_nil (bad : QueryLog (ofFn R) → (t : D) → R t → Prop)
    (pre : QueryLog (ofFn R)) : ¬ FreshBadAfter bad pre [] := by
  rintro ⟨mid, q, post, h, -⟩
  simp only [List.nil_eq, List.append_eq_nil_iff, reduceCtorEq, and_false] at h

/-- The first query is fresh and bad, or a later one is, after it. -/
theorem freshBadAfter_cons (bad : QueryLog (ofFn R) → (t : D) → R t → Prop)
    (pre : QueryLog (ofFn R)) (q : (t : D) × R t) (rest : QueryLog (ofFn R)) :
    FreshBadAfter bad pre (q :: rest) ↔
      (q.1 ∉ pre.map Sigma.fst ∧ bad pre q.1 q.2) ∨ FreshBadAfter bad (pre ++ [q]) rest := by
  constructor
  · rintro ⟨mid, q', post, h, hfresh, hbad⟩
    cases mid with
    | nil =>
        obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp h
        exact Or.inl ⟨by simpa only [List.append_nil] using hfresh,
          by simpa only [List.append_nil] using hbad⟩
    | cons a mid =>
        obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp h
        refine Or.inr ⟨mid, q', post, rfl, ?_, ?_⟩
        · simpa only [List.append_assoc, List.singleton_append] using hfresh
        · simpa only [List.append_assoc, List.singleton_append] using hbad
  · rintro (⟨hfresh, hbad⟩ | ⟨mid, q', post, rfl, hfresh, hbad⟩)
    · exact ⟨[], q, rest, rfl, by simpa only [List.append_nil] using hfresh,
        by simpa only [List.append_nil] using hbad⟩
    · refine ⟨q :: mid, q', post, rfl, ?_, ?_⟩
      · simpa only [List.append_assoc, List.singleton_append] using hfresh
      · simpa only [List.append_assoc, List.singleton_append] using hbad

/-- Restricting the keys keeps a query bound. -/
theorem isTotalQueryBound_restrictQueries (S : Finset D) (oa : OracleComp (ofFn R) α)
    (h : AllQueriesSatisfy oa (· ∈ S)) (n : ℕ) (hn : IsTotalQueryBound oa n) :
    IsTotalQueryBound (restrictQueries S oa h) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
      exact ⟨hn.1, fun u => ih u
        (((allQueriesSatisfy_query_bind_iff _ _ _).mp h).2 u) _ (hn.2 u)⟩

variable [DecidableEq D]

/-- The finite-domain core: started from the log `pre` and a cache with exactly `pre`'s keys,
an `n`-query computation adds a fresh bad query with probability at most `n · ε`. -/
private theorem prEvent_freshBadAfter_le [Finite D] [∀ d, SampleableType (R d)]
    [SampleableType (∀ d, R d)] (bad : QueryLog (ofFn R) → (t : D) → R t → Prop) (ε : ℝ≥0∞)
    (N : ℕ) (hε : ∀ pre t, pre.length < N → t ∉ pre.map Sigma.fst →
      Pr{let u ← $ᵗ R t}[bad pre t u] ≤ ε)
    (oa : OracleComp (ofFn R) α) (n : ℕ) (hn : IsTotalQueryBound oa n)
    (pre : QueryLog (ofFn R)) (c : (ofFn R).QueryCache)
    (hc : ∀ t, c t = none ↔ t ∉ pre.map Sigma.fst) (hlen : pre.length + n ≤ N) :
    Pr{let g ← $ᵗ (∀ d, R d)}[FreshBadAfter bad pre (tableQueryLog oa (completeTable c g))] ≤
      n * ε := by
  induction oa using OracleComp.inductionOn generalizing n pre c with
  | pure a =>
      simp only [tableQueryLog_pure, freshBadAfter_nil, prEvent_false, zero_le]
  | query_bind t k ih =>
      obtain ⟨hn0, hk⟩ := isTotalQueryBound_query_bind_iff.mp hn
      simp_rw [tableQueryLog_query_bind, freshBadAfter_cons]
      have hlen' (u : R t) : (pre ++ [⟨t, u⟩] : QueryLog (ofFn R)).length + (n - 1) ≤ N := by
        simp only [List.length_append, List.length_singleton]
        omega
      have hcache (c' : (ofFn R).QueryCache) (u : R t)
          (hc' : c' t ≠ none) (heq : ∀ t', t' ≠ t → c' t' = c t') :
          ∀ t', c' t' = none ↔ t' ∉ (pre ++ [⟨t, u⟩] : QueryLog (ofFn R)).map Sigma.fst := by
        intro t'
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
          List.mem_singleton, not_or]
        by_cases ht : t' = t
        · rw [ht]
          simp only [hc', not_true_eq_false, and_false]
        · simp only [heq t' ht, hc, ht, not_false_eq_true, and_true]
      cases hct : c t with
      | some u =>
          have hold : t ∈ pre.map Sigma.fst := by
            by_contra h
            simp only [(hc t).mpr h, reduceCtorEq] at hct
          have hval (g : ∀ d, R d) : completeTable c g t = u := by
            simp only [completeTable, hct, Option.getD_some]
          simp_rw [hval, hold, not_true_eq_false, false_and, false_or]
          refine (ih u (n - 1) (hk u) (pre ++ [⟨t, u⟩]) c
            (hcache c u (by simp only [hct, ne_eq, reduceCtorEq, not_false_eq_true])
              fun _ _ => rfl) (hlen' u)).trans ?_
          gcongr
          omega
      | none =>
          have hfresh : t ∉ pre.map Sigma.fst := (hc t).mp hct
          apply (prEvent_or_le _ _ _).trans
          have hfirst : Pr{let g ← $ᵗ (∀ d, R d)}[t ∉ pre.map Sigma.fst ∧
              bad pre t (completeTable c g t)] ≤ ε := by
            refine (prEvent_mono _ _ _ fun g h => h.2).trans ?_
            refine prEvent_completeTable_cell_le c t hct (fun t' f => bad pre t' (f t')) ε
              fun g => ?_
            simpa only [Function.update_self] using hε pre t (by omega) hfresh
          have hupd (g : ∀ d, R d) (u : R t) :
              completeTable c (Function.update g t u) = completeTable (c.cacheQuery t u) g := by
            rw [completeTable_cacheQuery, completeTable_update_of_none c g hct]
          have hrest : Pr{let g ← $ᵗ (∀ d, R d)}[FreshBadAfter bad
              (pre ++ [⟨t, completeTable c g t⟩])
              (tableQueryLog (k (completeTable c g t)) (completeTable c g))] ≤
              ((n - 1 : ℕ) : ℝ≥0∞) * ε := by
            rw [prEvent_uniformTable_update t]
            have hval (g : ∀ d, R d) (u : R t) : completeTable (c.cacheQuery t u) g t = u := by
              rw [completeTable_cacheQuery, Function.update_self]
            simp_rw [hupd, hval]
            refine wp_le_of_forall_le _ fun u => ?_
            have hcu : (c.cacheQuery t u) t ≠ none := by
              simp only [QueryCache.cacheQuery_self, ne_eq, reduceCtorEq, not_false_eq_true]
            exact ih u (n - 1) (hk u) (pre ++ [⟨t, u⟩]) (c.cacheQuery t u)
              (hcache _ u hcu fun t' ht' => QueryCache.cacheQuery_of_ne c u ht') (hlen' u)
          calc
            _ ≤ ε + ((n - 1 : ℕ) : ℝ≥0∞) * ε := add_le_add hfirst hrest
            _ = n * ε := by
              conv_lhs => lhs; rw [← one_mul ε]
              rw [← add_mul, ← Nat.cast_one, ← Nat.cast_add]
              congr 2
              omega

/-- The finite-domain case of `prEvent_exists_fresh_bad_le`. -/
private theorem prEvent_exists_fresh_bad_le_finite [Finite D] [∀ d, SampleableType (R d)]
    [SampleableType (∀ d, R d)] (oa : OracleComp (ofFn R) α) (n : ℕ)
    (hn : IsTotalQueryBound oa n) (event : α → Prop)
    (bad : QueryLog (ofFn R) → (t : D) → R t → Prop) (ε : ℝ≥0∞)
    (hε : ∀ pre t, pre.length < n → t ∉ pre.map Sigma.fst →
      Pr{let u ← $ᵗ R t}[bad pre t u] ≤ ε)
    (htrace : ∀ g, event (evalWithAnswerFn (QueryImpl.ofFn g) oa) →
      FreshBadAfter bad [] (tableQueryLog oa g)) :
    Pr{let result ← (simulateQ randomOracle oa).run' ∅}[event result] ≤ n * ε := by
  let : MeasurableSpace α := ⊤
  have heager := evalDist_simulateQ_randomOracle_run'_eq_completeTable oa ∅
  simp only [completeTable_empty] at heager
  rw [(EvalDistEq.of_evalDist_eq heager).prEvent_eq event]
  simp only [expect_norm]
  refine (prEvent_mono ($ᵗ (∀ d, R d)) _ _ htrace).trans ?_
  have h := prEvent_freshBadAfter_le bad ε n hε oa n hn [] ∅
    (fun t => by simp only [QueryCache.empty_apply, List.map_nil, List.not_mem_nil,
      not_false_eq_true]) (by simp only [List.length_nil, zero_add, le_refl])
  simpa only [completeTable_empty] using h

/-- **Fresh bad queries against a lazy random oracle.** Let `bad pre t u` say that the answer
`u` to the key `t` is bad after the queries `pre`. If whenever the event holds of a run against
an answer table some query is fresh (its key was not queried before) and bad for the queries
before it, and a uniform answer to a fresh key is bad with probability at most `ε` after every
`pre` of fewer than `n` queries, then an adaptive computation making at most `n` queries
triggers the event against a lazy random oracle with probability at most `n · ε`. -/
theorem prEvent_exists_fresh_bad_le [∀ d, SampleableType (R d)]
    (oa : OracleComp (ofFn R) α) (n : ℕ) (hn : IsTotalQueryBound oa n) (event : α → Prop)
    (bad : QueryLog (ofFn R) → (t : D) → R t → Prop) (ε : ℝ≥0∞)
    (hε : ∀ pre t, pre.length < n → t ∉ pre.map Sigma.fst →
      Pr{let u ← $ᵗ R t}[bad pre t u] ≤ ε)
    (htrace : ∀ g, event (evalWithAnswerFn (QueryImpl.ofFn g) oa) →
      ∃ pre q post, tableQueryLog oa g = pre ++ q :: post ∧ q.1 ∉ pre.map Sigma.fst ∧
        bad pre q.1 q.2) :
    Pr{let result ← (simulateQ randomOracle oa).run' ∅}[event result] ≤ n * ε := by
  classical
  let S := possibleQueryKeys oa
  have hS : AllQueriesSatisfy oa (· ∈ S) := allQueriesSatisfy_possibleQueryKeys oa
  let small := restrictQueries S oa hS
  let : ∀ d : S, Fintype (R d.val) := fun d => Fintype.ofFinite (R d.val)
  let : Nonempty ((d : S) → R d.val) := ⟨fun d => Classical.arbitrary (R d.val)⟩
  let : SampleableType ((d : S) → R d.val) := SampleableType.ofFintype _
  let embed : ((t : S) × R t.val) → ((t : D) × R t) := fun q => ⟨q.1.val, q.2⟩
  have hfresh (pre : QueryLog (ofFn fun d : S => R d.val)) (t : S)
      (h : t ∉ pre.map Sigma.fst) : t.val ∉ (pre.map embed).map Sigma.fst := by
    simp only [List.map_map, List.mem_map, Function.comp_apply, not_exists, not_and] at h ⊢
    exact fun q hq heq => h q hq (Subtype.ext heq)
  have hfresh' (pre : QueryLog (ofFn fun d : S => R d.val)) (t : S)
      (h : t.val ∉ (pre.map embed).map Sigma.fst) : t ∉ pre.map Sigma.fst := by
    simp only [List.map_map, List.mem_map, Function.comp_apply, not_exists, not_and] at h ⊢
    exact fun q hq heq => h q hq (congrArg Subtype.val heq)
  rw [← randomOracle_restrictQueries S oa hS ∅]
  refine prEvent_exists_fresh_bad_le_finite small n
    (isTotalQueryBound_restrictQueries S oa hS n hn) event
    (fun pre t u => bad (pre.map embed) t.val u) ε
    (fun pre t hlen ht => hε _ _ (by simpa only [List.length_map] using hlen) (hfresh pre t ht))
    fun g hevent => ?_
  have hrestrict : (fun d : S => extendTable S g d.val) = g := by
    funext d
    exact extendTable_subtype S g d
  have heval := evalWithAnswerFn_restrictQueries S oa hS (extendTable S g)
  rw [hrestrict] at heval
  obtain ⟨pre, q, post, hlog, hq, hbad⟩ := htrace (extendTable S g) (heval ▸ hevent)
  have hmap := tableQueryLog_restrictQueries S oa hS (extendTable S g)
  rw [hrestrict, hlog] at hmap
  obtain ⟨pre', rest', hsplit, rfl, hrest⟩ := List.map_eq_append_iff.mp hmap
  obtain ⟨q', post', rfl, rfl, -⟩ := List.map_eq_cons_iff.mp hrest
  refine ⟨pre', q', post', hsplit, ?_, ?_⟩
  · simpa only [List.nil_append] using hfresh' pre' q'.1 hq
  · simpa only [List.nil_append] using hbad

end OracleComp
