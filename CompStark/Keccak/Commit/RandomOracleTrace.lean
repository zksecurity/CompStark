/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ArkLib.Interaction.Oracle.Security.BcsSimulation
public import VCVio.OracleComp.QueryTracking.QueryBound.Hazard

/-! Chronological collision and late-preimage accounting for a commitment oracle beside
typed challenge queries. The trace contains fresh queries only, newest first. -/

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStark.Keccak.Commit.RandomOracleTrace

open OracleComp OracleSpec Interaction.Oracle.Security
open scoped ENNReal

variable {Input Key Digest : Type} {Response : Key → Type}

/-- Commitment queries return digests; challenge queries retain their own answer types. -/
abbrev spec (Input Digest : Type) (Response : Key → Type) : OracleSpec (Input ⊕ Key) :=
  ofFn (Sum.elim (fun _ : Input => Digest) Response)

/-- A query's digest references are interpreted before its answer is sampled. -/
abbrev References (Input Key Digest : Type) := Input ⊕ Key → List Digest

/-- Commitment answers themselves become protected against later hash collisions. -/
def returnedDigest : (entry : (t : Input ⊕ Key) × (spec Input Digest Response).Range t) → List Digest
  | ⟨.inl _, value⟩ => [value]
  | ⟨.inr _, _⟩ => []

/-- All digests mentioned as roots or children, together with all prior commitment answers. -/
def targets (refs : References Input Key Digest)
    (log : QueryLog (spec Input Digest Response)) : List Digest :=
  log.flatMap fun entry => refs entry.1 ++ returnedDigest entry

/-- A fresh commitment answer hits a digest fixed before that answer, including its own children. -/
def Hit (refs : References Input Key Digest)
    (entry : (t : Input ⊕ Key) × (spec Input Digest Response).Range t)
    (log : QueryLog (spec Input Digest Response)) : Prop :=
  match entry with
  | ⟨.inl input, value⟩ => value ∈ refs (.inl input) ++ targets refs log
  | ⟨.inr _, _⟩ => False

/-- A fresh-query trace contains a chronological collision or late-preimage hit. -/
def Bad (refs : References Input Key Digest) : QueryLog (spec Input Digest Response) → Prop
  | [] => False
  | entry :: log => Bad refs log ∨ Hit refs entry log

/-- Concatenating traces concatenates their protected digests. -/
theorem targets_append (refs : References Input Key Digest)
    (left right : QueryLog (spec Input Digest Response)) :
    targets refs (left ++ right) = targets refs left ++ targets refs right :=
  by unfold targets; exact List.flatMap_append

/-- Every cached commitment answer is included in the trace's protected digests. -/
theorem answer_mem_targets [DecidableEq Input] [DecidableEq Key]
    (refs : References Input Key Digest) (log : QueryLog (spec Input Digest Response))
    (input : Input) (value : Digest) (known : Bcs.cacheOf log (.inl input) = some value) :
    value ∈ targets refs log := by
  induction log with
  | nil => cases known
  | cons entry log ih =>
      rcases entry with ⟨query, answer⟩
      by_cases same : query = .inl input
      · subst query
        have equal : answer = value := Option.some.inj (by simpa only [List.cons_append, Bcs.cacheOf_cons, QueryCache.cacheQuery_self] using known)
        subst value
        exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
      · have older : Bcs.cacheOf log (.inl input) = some value := by
          simpa only [Bcs.cacheOf_cons, QueryCache.cacheQuery_of_ne _ _ (Ne.symm same)] using known
        exact List.mem_append_right _ (ih older)

/-- A protected digest has no newly discovered preimage after a good snapshot. -/
theorem no_late_preimage [DecidableEq Input] [DecidableEq Key]
    (refs : References Input Key Digest)
    (before later : QueryLog (spec Input Digest Response)) (value : Digest)
    (retained : value ∈ targets refs before) (good : ¬ Bad refs (later ++ before))
    (input : Input) (absent : Bcs.cacheOf before (.inl input) = none) :
    Bcs.cacheOf (later ++ before) (.inl input) ≠ some value := by
  induction later with
  | nil => simp only [List.nil_append, absent, ne_eq, reduceCtorEq, not_false_eq_true]
  | cons entry later ih =>
      have tailGood : ¬ Bad refs (later ++ before) := fun bad => good (Or.inl bad)
      rcases entry with ⟨query, answer⟩
      by_cases same : query = .inl input
      · subst query
        intro known
        have equal : answer = value := Option.some.inj (by simpa only [List.cons_append, Bcs.cacheOf_cons, QueryCache.cacheQuery_self] using known)
        apply good
        right
        change answer ∈ refs (.inl input) ++ targets refs (later ++ before)
        rw [equal, targets_append]
        exact List.mem_append_right _ (List.mem_append_right _ retained)
      · simpa only [List.cons_append, Bcs.cacheOf_cons,
          QueryCache.cacheQuery_of_ne _ _ (Ne.symm same)] using ih tailGood

/-- A good trace's commitment cache is injective on its answered inputs. -/
theorem hash_cache_injective [DecidableEq Input] [DecidableEq Key]
    (refs : References Input Key Digest) (log : QueryLog (spec Input Digest Response))
    (good : ¬ Bad refs log) (a b : Input) (value : Digest)
    (ha : Bcs.cacheOf log (.inl a) = some value)
    (hb : Bcs.cacheOf log (.inl b) = some value) : a = b := by
  induction log with
  | nil => cases ha
  | cons entry log ih =>
      have tailGood : ¬ Bad refs log := fun bad => good (Or.inl bad)
      rcases entry with ⟨query, answer⟩
      by_cases qa : query = .inl a
      · subst query
        by_cases ab : a = b
        · exact ab
        · have older : Bcs.cacheOf log (.inl b) = some value := by
            simpa only [Bcs.cacheOf_cons, QueryCache.cacheQuery_of_ne _ _
              (show Sum.inl b ≠ (.inl a : Input ⊕ Key) from fun h => ab (Sum.inl.inj h).symm)] using hb
          have equal : answer = value := Option.some.inj (by simpa only [Bcs.cacheOf_cons, QueryCache.cacheQuery_self] using ha)
          exact (good (Or.inr (by
            change answer ∈ refs (.inl a) ++ targets refs log
            rw [equal]
            exact List.mem_append_right _ (answer_mem_targets refs log b value older)))).elim
      · have olderA : Bcs.cacheOf log (.inl a) = some value := by
          simpa only [Bcs.cacheOf_cons, QueryCache.cacheQuery_of_ne _ _ (Ne.symm qa)] using ha
        by_cases qb : query = .inl b
        · subst query
          have equal : answer = value := Option.some.inj (by simpa only [Bcs.cacheOf_cons, QueryCache.cacheQuery_self] using hb)
          exact (good (Or.inr (by
            change answer ∈ refs (.inl b) ++ targets refs log
            rw [equal]
            exact List.mem_append_right _ (answer_mem_targets refs log a value olderA)))).elim
        · apply ih tailGood olderA
          simpa only [Bcs.cacheOf_cons, QueryCache.cacheQuery_of_ne _ _ (Ne.symm qb)] using hb

/-- A trace records answers from one fixed oracle table. -/
def Agrees (table : (query : Input ⊕ Key) → (spec Input Digest Response).Range query)
    (log : QueryLog (spec Input Digest Response)) : Prop :=
  ∀ entry ∈ log, table entry.1 = entry.2

/-- Any answer in a coherent trace's cache is the answer of its common table. -/
theorem cache_eq_table [DecidableEq Input] [DecidableEq Key]
    (table : (query : Input ⊕ Key) → (spec Input Digest Response).Range query)
    (log : QueryLog (spec Input Digest Response)) (coherent : Agrees table log)
    (query : Input ⊕ Key) (value : (spec Input Digest Response).Range query)
    (known : Bcs.cacheOf log query = some value) : table query = value := by
  induction log with
  | nil => cases known
  | cons entry log ih =>
      rcases entry with ⟨key, answer⟩
      by_cases same : key = query
      · subst key
        have equal : answer = value := Option.some.inj (by
          simpa only [Bcs.cacheOf_cons, QueryCache.cacheQuery_self] using known)
        exact (coherent _ List.mem_cons_self).trans equal
      · exact ih (fun e he => coherent e (List.mem_cons_of_mem _ he)) (by
          simpa only [Bcs.cacheOf_cons, QueryCache.cacheQuery_of_ne _ _ (Ne.symm same)] using known)

/-- Every digest referenced by a cached input is protected by the same trace. -/
theorem references_mem_targets [DecidableEq Input] [DecidableEq Key]
    (refs : References Input Key Digest) (log : QueryLog (spec Input Digest Response))
    (input : Input) (value child : Digest) (known : Bcs.cacheOf log (.inl input) = some value)
    (referenced : child ∈ refs (.inl input)) : child ∈ targets refs log := by
  induction log with
  | nil => cases known
  | cons entry log ih =>
      rcases entry with ⟨query, answer⟩
      by_cases same : query = .inl input
      · subst query
        exact List.mem_append_left _ (List.mem_append_left _ referenced)
      · apply List.mem_append_right _
        apply ih
        simpa only [Bcs.cacheOf_cons, QueryCache.cacheQuery_of_ne _ _ (Ne.symm same)] using known

/-- Every later preimage of a protected digest already has its identical answer in the snapshot. -/
theorem hash_known_before [DecidableEq Input] [DecidableEq Key]
    (refs : References Input Key Digest)
    (table : (query : Input ⊕ Key) → (spec Input Digest Response).Range query)
    (before later : QueryLog (spec Input Digest Response))
    (coherent : Agrees table (later ++ before)) (good : ¬ Bad refs (later ++ before))
    (input : Input) (value : Digest) (retained : value ∈ targets refs before)
    (known : Bcs.cacheOf (later ++ before) (.inl input) = some value) :
    Bcs.cacheOf before (.inl input) = some value := by
  cases old : Bcs.cacheOf before (.inl input) with
  | none => exact (no_late_preimage refs before later value retained good input old known).elim
  | some answer =>
      have oldValue := cache_eq_table table before
        (fun e he => coherent e (List.mem_append_right _ he)) (.inl input) answer old
      have newValue := cache_eq_table table (later ++ before) coherent (.inl input) value known
      exact congrArg some (oldValue.symm.trans newValue)

/-- Digests reachable from selected roots by following referenced children of cached hash inputs. -/
inductive Reachable [DecidableEq Input] [DecidableEq Key]
    (refs : References Input Key Digest) (log : QueryLog (spec Input Digest Response))
    (roots : List Digest) : Digest → Prop
  /-- Each selected root starts a path. -/
  | root (value : Digest) (member : value ∈ roots) : Reachable refs log roots value
  /-- A known preimage exposes every digest parsed as one of its children. -/
  | child (value child : Digest) (input : Input) (parent : Reachable refs log roots value)
      (known : Bcs.cacheOf log (.inl input) = some value)
      (referenced : child ∈ refs (.inl input)) : Reachable refs log roots child

/-- Good chronological traces cannot reveal new nodes beneath roots frozen in an earlier snapshot. -/
theorem reachable_mem_snapshot [DecidableEq Input] [DecidableEq Key]
    (refs : References Input Key Digest)
    (table : (query : Input ⊕ Key) → (spec Input Digest Response).Range query)
    (before later : QueryLog (spec Input Digest Response))
    (coherent : Agrees table (later ++ before)) (good : ¬ Bad refs (later ++ before))
    (roots : List Digest) (retained : ∀ value ∈ roots, value ∈ targets refs before)
    (value : Digest) (reachable : Reachable refs (later ++ before) roots value) :
    value ∈ targets refs before := by
  induction reachable with
  | root value member => exact retained value member
  | child value child input parent known referenced ih =>
      exact references_mem_targets refs before input value child
        (hash_known_before refs table before later coherent good input value ih known) referenced

/-- Every queried operation beneath a frozen root is recoverable from that snapshot. -/
theorem reachable_hash_known_before [DecidableEq Input] [DecidableEq Key]
    (refs : References Input Key Digest)
    (table : (query : Input ⊕ Key) → (spec Input Digest Response).Range query)
    (before later : QueryLog (spec Input Digest Response))
    (coherent : Agrees table (later ++ before)) (good : ¬ Bad refs (later ++ before))
    (roots : List Digest) (retained : ∀ value ∈ roots, value ∈ targets refs before)
    (value : Digest) (reachable : Reachable refs (later ++ before) roots value)
    (input : Input) (known : Bcs.cacheOf (later ++ before) (.inl input) = some value) :
    Bcs.cacheOf before (.inl input) = some value :=
  hash_known_before refs table before later coherent good input value
    (reachable_mem_snapshot refs table before later coherent good roots retained value reachable) known

/-- Look up a queried raw preimage by digest, using only the finite recorded trace. -/
def lookup [DecidableEq Digest] (log : QueryLog (spec Input Digest Response))
    (value : Digest) : Option Input :=
  match log with
  | [] => none
  | ⟨.inl input, answer⟩ :: tail => if answer = value then some input else lookup tail value
  | ⟨.inr _, _⟩ :: tail => lookup tail value

/-- On a good trace, reverse lookup recovers every answered input uniquely. -/
theorem lookup_eq_of_known [DecidableEq Input] [DecidableEq Key] [DecidableEq Digest]
    (refs : References Input Key Digest) (log : QueryLog (spec Input Digest Response))
    (good : ¬ Bad refs log) (input : Input) (value : Digest)
    (known : Bcs.cacheOf log (.inl input) = some value) : lookup log value = some input := by
  induction log with
  | nil => cases known
  | cons entry log ih =>
      have tailGood : ¬ Bad refs log := fun bad => good (Or.inl bad)
      rcases entry with ⟨query, answer⟩
      cases query with
      | inr key =>
          exact ih tailGood (by simpa only [Bcs.cacheOf_cons,
            QueryCache.cacheQuery_of_ne _ _ (Sum.inl_ne_inr)] using known)
      | inl other =>
          by_cases same : answer = value
          · subst answer
            have equal := hash_cache_injective refs (⟨.inl other, value⟩ :: log) good
              other input value (by simp only [Bcs.cacheOf_cons, QueryCache.cacheQuery_self]) known
            simp only [lookup, ↓reduceIte, equal]
          · rw [lookup, ite_eq_right same]
            apply ih tailGood
            have different : Sum.inl input ≠ (.inl other : Input ⊕ Key) := by
              intro equal
              cases Sum.inl.inj equal
              exact same (Option.some.inj (by
                simpa only [Bcs.cacheOf_cons, QueryCache.cacheQuery_self] using known))
            simpa only [Bcs.cacheOf_cons, QueryCache.cacheQuery_of_ne _ _ different] using known

/-- Every suffix of a good newest-first trace is itself good. -/
theorem good_suffix (refs : References Input Key Digest)
    (before later : QueryLog (spec Input Digest Response)) (good : ¬ Bad refs (later ++ before)) :
    ¬ Bad refs before := by
  induction later with
  | nil => exact good
  | cons entry later ih => exact ih (fun bad => good (Or.inl bad))

/-- Finite reverse lookup recovers all later openings below the roots of a good snapshot. -/
theorem reachable_lookup_before [DecidableEq Input] [DecidableEq Key] [DecidableEq Digest]
    (refs : References Input Key Digest)
    (table : (query : Input ⊕ Key) → (spec Input Digest Response).Range query)
    (before later : QueryLog (spec Input Digest Response))
    (coherent : Agrees table (later ++ before)) (good : ¬ Bad refs (later ++ before))
    (roots : List Digest) (retained : ∀ value ∈ roots, value ∈ targets refs before)
    (value : Digest) (reachable : Reachable refs (later ++ before) roots value)
    (input : Input) (known : Bcs.cacheOf (later ++ before) (.inl input) = some value) :
    lookup before value = some input :=
  lookup_eq_of_known refs before (good_suffix refs before later good) input value
    (reachable_hash_known_before refs table before later coherent good roots retained value reachable input known)

/-- A newest-first log records each key only when it was absent from the older cache. -/
def Fresh [DecidableEq Input] [DecidableEq Key] : QueryLog (spec Input Digest Response) → Prop
  | [] => True
  | entry :: log => Fresh log ∧ Bcs.cacheOf log entry.1 = none

/-- Every fresh logged answer survives in the final cache. -/
theorem fresh_cache_member [DecidableEq Input] [DecidableEq Key]
    (log : QueryLog (spec Input Digest Response)) (fresh : Fresh log)
    (entry : (query : Input ⊕ Key) × (spec Input Digest Response).Range query) (member : entry ∈ log) :
    Bcs.cacheOf log entry.1 = some entry.2 := by
  induction log with
  | nil => cases member
  | cons head log ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp only [Bcs.cacheOf_cons, QueryCache.cacheQuery_self]
      · have different : entry.1 ≠ head.1 := by
          intro same
          exact Bcs.cacheOf_ne_none_of_mem member (same.symm ▸ fresh.2)
        simpa only [Bcs.cacheOf_cons, QueryCache.cacheQuery_of_ne _ _ different] using ih fresh.1 member

/-- Completing a fresh finite cache supplies a table coherent with every logged answer. -/
theorem fresh_agrees [DecidableEq Input] [DecidableEq Key]
    (fallback : (query : Input ⊕ Key) → (spec Input Digest Response).Range query)
    (log : QueryLog (spec Input Digest Response)) (fresh : Fresh log) :
    Agrees (fun query => (Bcs.cacheOf log query).getD (fallback query)) log := by
  intro entry member
  simp only [fresh_cache_member log fresh entry member, Option.getD_some]

section Probability

variable [DecidableEq Input] [DecidableEq Key] [SampleableType Digest]
    [∀ key, SampleableType (Response key)]

/-- Both kinds of query have uniform response samplers. -/
instance responseSampleable (query : Input ⊕ Key) : SampleableType ((spec Input Digest Response).Range query) :=
  match query with
  | .inl _ => inferInstanceAs (SampleableType Digest)
  | .inr key => inferInstanceAs (SampleableType (Response key))

/-- A lazy oracle records each fresh query once and retains repeated-query answers. -/
def handler : QueryImpl (spec Input Digest Response)
    (StateT (QueryLog (spec Input Digest Response)) ProbComp) := fun query => StateT.mk fun log =>
  match Bcs.cacheOf log query with
  | some value => pure (value, log)
  | none => do
      let value ← $ᵗ (spec Input Digest Response).Range query
      return (value, ⟨query, value⟩ :: log)

/-- Lazy sampling preserves the invariant that each recorded key is fresh. -/
theorem handler_fresh : QueryImpl.PreservesInv
    (handler (Input := Input) (Digest := Digest) (Response := Response)) Fresh := by
  intro query log fresh result supported
  simp only [handler, StateT.run_mk] at supported
  cases known : Bcs.cacheOf log query with
  | some value =>
      rw [known, mem_support_pure_iff] at supported
      exact supported ▸ fresh
  | none =>
      rw [known, mem_support_bind_iff] at supported
      obtain ⟨value, _, supported⟩ := supported
      rw [mem_support_pure_iff] at supported
      subst result
      exact ⟨fresh, known⟩

/-- Every supported oracle execution produces a fresh, and therefore coherent, query log. -/
theorem run_fresh {α : Type} (program : OracleComp (spec Input Digest Response) α)
    (result : α × QueryLog (spec Input Digest Response))
    (supported : result ∈ support ((simulateQ handler program).run [])) : Fresh result.2 :=
  simulateQ_run_preservesInv handler Fresh handler_fresh program [] trivial result supported

/-- Forgetting the fresh log gives precisely the shared lazy random oracle. -/
theorem handler_projects {α : Type} (program : OracleComp (spec Input Digest Response) α)
    (log : QueryLog (spec Input Digest Response)) :
    Prod.map id Bcs.cacheOf <$> (simulateQ handler program).run log =
      (simulateQ randomOracle program).run (Bcs.cacheOf log) := by
  apply map_run_simulateQ_eq_of_query_map_eq
  intro query log
  simp only [handler, StateT.run_mk, randomOracle.run_eq]
  cases known : Bcs.cacheOf log query with
  | some value => simp only [map_pure, Prod.map_apply, id_eq]
  | none => simp only [map_bind, map_pure, Prod.map_apply, id_eq, Bcs.cacheOf_cons]

omit [DecidableEq Input] [DecidableEq Key] [SampleableType Digest]
    [∀ key, SampleableType (Response key)] in
/-- Each trace entry adds its references and at most one commitment answer to the protected set. -/
theorem targets_length_le (refs : References Input Key Digest) (width : ℕ)
    (bounded : ∀ query, (refs query).length ≤ width)
    (log : QueryLog (spec Input Digest Response)) :
    (targets refs log).length ≤ (width + 1) * log.length := by
  induction log with
  | nil => simp only [targets, List.flatMap_nil, List.length_nil, Nat.mul_zero, le_refl]
  | cons entry log ih =>
      have size := bounded entry.1
      have answer : (returnedDigest entry).length ≤ 1 := by cases entry with
        | mk query value => cases query <;> simp only [returnedDigest, List.length_cons, List.length_nil] <;> omega
      simp only [targets, List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_add, Nat.mul_one] at *
      omega

/-- A uniform digest hits a fixed list with probability at most its length over the digest space. -/
theorem uniform_mem_le (values : List Digest) :
    Pr{let value ← ($ᵗ Digest : ProbComp Digest)}[value ∈ values] ≤
      (values.length : ℝ≥0∞) / Nat.card Digest := by
  classical
  let : Fintype Digest := Fintype.ofFinite _
  have same : ∀ value, value ∈ values ↔ ∃ i : Fin values.length, values[i] = value := by
    intro value
    constructor
    · intro member
      obtain ⟨i, hi, equal⟩ := List.mem_iff_getElem.mp member
      exact ⟨⟨i, hi⟩, equal⟩
    · rintro ⟨i, equal⟩
      exact List.mem_iff_getElem.mpr ⟨i.val, i.isLt, equal⟩
  rw [prEvent_congr _ _ _ same, Nat.card_eq_fintype_card]
  exact SampleableType.prEvent_uniformSample_exists_eq_le (fun i : Fin values.length => values[i])

omit [DecidableEq Input] [DecidableEq Key] in
/-- One fresh response hits at most the currently protected digests and the query's own references. -/
theorem hit_probability_le (refs : References Input Key Digest) (width : ℕ)
    (bounded : ∀ query, (refs query).length ≤ width)
    (query : Input ⊕ Key) (log : QueryLog (spec Input Digest Response)) :
    Pr{let value ← ($ᵗ (spec Input Digest Response).Range query :
      ProbComp ((spec Input Digest Response).Range query))}[Hit refs ⟨query, value⟩ log] ≤
      ((width + 1) * (log.length + 1) : ℕ) / (Nat.card Digest : ℝ≥0∞) := by
  cases query with
  | inr key => exact (prEvent_eq_zero_of_forall_not _ _ (fun _ => id)).trans_le zero_le
  | inl input =>
      refine (uniform_mem_le (refs (.inl input) ++ targets refs log)).trans ?_
      apply ENNReal.div_le_div_right
      apply Nat.cast_le.mpr
      have own := bounded (.inl input)
      have previous := targets_length_le refs width bounded log
      rw [List.length_append]
      nlinarith

/-- A query records at most one fresh entry, including on repeated-query branches. -/
theorem handler_length_le (query : Input ⊕ Key) (log : QueryLog (spec Input Digest Response))
    (result : (spec Input Digest Response).Range query × QueryLog (spec Input Digest Response))
    (supported : result ∈ support ((handler query).run log)) :
    result.2.length ≤ log.length + 1 := by
  simp only [handler, StateT.run_mk] at supported
  cases known : Bcs.cacheOf log query with
  | some value =>
      rw [known, mem_support_pure_iff] at supported
      subst result
      exact Nat.le_succ _
  | none =>
      rw [known, mem_support_bind_iff] at supported
      obtain ⟨value, _, supported⟩ := supported
      rw [mem_support_pure_iff] at supported
      subst result
      exact le_rfl

/-- From a good trace, one oracle call incurs only the fresh commitment-response hazard. -/
theorem handler_bad_le (refs : References Input Key Digest) (width : ℕ)
    (bounded : ∀ query, (refs query).length ≤ width)
    (query : Input ⊕ Key) (log : QueryLog (spec Input Digest Response)) (good : ¬ Bad refs log) :
    Pr{let result ← (handler query).run log}[Bad refs result.2] ≤
      ((width + 1) * (log.length + 1) : ℕ) / (Nat.card Digest : ℝ≥0∞) := by
  simp only [handler, StateT.run_mk]
  cases known : Bcs.cacheOf log query with
  | some value =>
      exact (prEvent_eq_zero_of_forall_mem_support _ _ (fun result supported => by
        rw [mem_support_pure_iff] at supported
        exact supported ▸ good)).trans_le zero_le
  | none =>
      simpa only [prEvent_norm, Bad, good, false_or] using
        hit_probability_le refs width bounded query log

/-- Adaptive collision and late-preimage risk is the sum of the per-query chronological hazards. -/
theorem bad_probability_le_sum {α : Type} (refs : References Input Key Digest) (width : ℕ)
    (bounded : ∀ query, (refs query).length ≤ width)
    (program : OracleComp (spec Input Digest Response) α) (queries : ℕ)
    (budget : IsTotalQueryBound program queries) :
    Pr{let result ← (simulateQ handler program).run []}[Bad refs result.2] ≤
      ∑ i ∈ Finset.range queries,
        ((width + 1) * (i + 1) : ℕ) / (Nat.card Digest : ℝ≥0∞) := by
  have charged : program.IsQueryBoundP (fun _ => True) queries := by
    simpa only [IsQueryBoundP, not_true_eq_false, false_or, ↓reduceIte, IsTotalQueryBound] using budget
  simpa only [List.length_nil, Nat.zero_add] using
    (prEvent_simulateQ_run_le_sum_of_isQueryBoundP handler (fun _ => True) List.length
      (fun _ => True) (Bad refs)
      (fun n => ((width + 1) * (n + 1) : ℕ) / (Nat.card Digest : ℝ≥0∞))
      (by intro a b hab; dsimp only; gcongr)
      (fun _ _ _ _ _ => trivial)
      (fun _ _ impossible => (impossible trivial).elim)
      (fun query log _ _ _ result supported => handler_length_le query log result supported)
      (fun query log _ _ good => handler_bad_le refs width bounded query log good)
      program charged [] trivial (fun bad => bad))

/-- A quadratic bound covers all adaptive commitment and challenge queries, including verification. -/
theorem bad_probability_le {α : Type} (refs : References Input Key Digest) (width : ℕ)
    (bounded : ∀ query, (refs query).length ≤ width)
    (program : OracleComp (spec Input Digest Response) α) (queries : ℕ)
    (budget : IsTotalQueryBound program queries) :
    Pr{let result ← (simulateQ handler program).run []}[Bad refs result.2] ≤
      ((width + 1) * queries * queries : ℕ) / (Nat.card Digest : ℝ≥0∞) := by
  refine (bad_probability_le_sum refs width bounded program queries budget).trans ?_
  calc
    _ ≤ (∑ _i ∈ Finset.range queries,
        ((width + 1) * queries : ℕ) / (Nat.card Digest : ℝ≥0∞)) := by
      apply Finset.sum_le_sum
      intro i hi
      have bound : i + 1 ≤ queries := Finset.mem_range.mp hi
      gcongr
    _ = _ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_div_assoc]
      push_cast
      congr 1
      ring

end Probability

end CompStark.Keccak.Commit.RandomOracleTrace
