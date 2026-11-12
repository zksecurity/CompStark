/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ArkLib.Interaction.Oracle.Security.StandardBcs
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery

/-! Cached random-oracle execution of the authenticated witness checker. The density
bridge explicitly requires a dominating prefix independent of the target answer. -/

set_option backward.isDefEq.respectTransparency false

@[expose] public section

namespace CompStark.Compiled.WitnessRandomOracle

open Interaction Interaction.Oracle Interaction.Oracle.Security
open StandardBcs StateRestoration OracleComp OracleSpec
open scoped ENNReal

/-- Earlier-challenge consistency reads only strict ancestor keys. -/
theorem prefixConsistent_congr {Com : Type} [DecidableEq Com] {protocol : Protocol}
    (coin : PublicCoin protocol) (pre : Prefix PUnit (compiledCoin Com coin))
    (words : PrefixMessages coin pre) (h g : PrefixTable PUnit (compiledCoin Com coin))
    (equality : (p : Prefix PUnit (compiledCoin Com coin)) → DecidableEq p.Challenge)
    (agree : ∀ p ∈ CorrelationIntractable.strictAncestors (compiledCoin Com coin) pre,
      h p = g p) :
    prefixConsistent coin pre words h equality = prefixConsistent coin pre words g equality := by
  induction coin with
  | done => exact nomatch pre
  | sender next ih =>
      exact ih pre.1 pre.2 words _ _ _ (fun p hp =>
        agree ⟨pre.1, p⟩ (List.mem_map.mpr ⟨p, hp, rfl⟩))
  | oracle next ih =>
      exact ih pre.2 words.2 _ _ _ (fun p hp =>
        agree ⟨pre.1, p⟩ (List.mem_map.mpr ⟨p, hp, rfl⟩))
  | challenge next ih =>
      cases pre with
      | inl _ => rfl
      | inr pair =>
          obtain ⟨salt, pre⟩ := pair
          have head := agree (.inl salt) List.mem_cons_self
          have tail := ih pre words.2 (fun p => h (.inr ⟨salt, p⟩)) (fun p => g (.inr ⟨salt, p⟩))
            (fun p => equality (.inr ⟨salt, p⟩)) (fun p hp =>
            agree (.inr ⟨salt, p⟩)
              (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p, hp, rfl⟩)))
          exact congrArg₂ Bool.and (congrArg (fun value => @decide (words.1 = value) (equality (.inl salt) words.1 value)) head) tail

section Read

variable {D : Type} {R : D → Type} [DecidableEq D]

/-- Query a finite list of coordinates and retain the answers in a completed table.
The fallback is never used at a queried coordinate. -/
def readTable (fallback : ∀ d, R d) : List D → OracleComp (ofFn R) (∀ d, R d)
  | [] => pure fallback
  | d :: ds => do
      let value ← liftM ((ofFn R).query d)
      readTable (Function.update fallback d value) ds

/-- Replaying the reads against a table recovers that table on every requested key. -/
theorem readTable_agrees (fallback g : ∀ d, R d) (ds : List D) :
    ∀ d ∈ ds, evalWithAnswerFn (QueryImpl.ofFn g) (readTable fallback ds) d = g d := by
  have aux : ∀ (ds : List D) (fallback : ∀ d, R d),
      (∀ d ∈ ds, evalWithAnswerFn (QueryImpl.ofFn g) (readTable fallback ds) d = g d) ∧
      (∀ d ∉ ds, evalWithAnswerFn (QueryImpl.ofFn g) (readTable fallback ds) d = fallback d) := by
    intro ds
    induction ds with
    | nil => exact fun _ => ⟨by simp only [List.not_mem_nil, false_implies, implies_true],
        fun _ _ => rfl⟩
    | cons d ds ih =>
        intro fallback
        simp only [readTable, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
          QueryImpl.ofFn_apply]
        obtain ⟨inside, outside⟩ := ih (Function.update fallback d (g d))
        constructor
        · intro e he
          rcases List.mem_cons.mp he with he | he
          · subst e
            by_cases hd : d ∈ ds
            · exact inside d hd
            · rw [outside d hd, Function.update_self]
          · exact inside e he
        · intro e he
          rw [outside e (fun h => he (List.mem_cons_of_mem d h)),
            Function.update_of_ne (fun h => he (by simp only [h, List.mem_cons_self]))]
  exact (aux ds fallback).1

/-- Reading a coordinate list issues exactly those queries, including repetitions. -/
theorem readTable_log (fallback g : ∀ d, R d) (ds : List D) :
    tableQueryLog (readTable fallback ds) g = ds.map (fun d => ⟨d, g d⟩) := by
  induction ds generalizing fallback with
  | nil => rfl
  | cons d ds ih => simp only [readTable, tableQueryLog_query_bind, ih, List.map_cons]

/-- The number of oracle calls made by a table read is bounded by its list length. -/
theorem readTable_queryBound (fallback : ∀ d, R d) (ds : List D) :
    IsTotalQueryBound (readTable fallback ds) ds.length := by
  induction ds generalizing fallback with
  | nil => trivial
  | cons d ds ih =>
      exact (isTotalQueryBound_query_bind_iff).mpr ⟨by simp, fun _ => by
        simpa only [List.length_cons, Nat.add_sub_cancel] using ih _⟩

end Read

variable {Statement Com : Type} [DecidableEq Com] {protocol : Statement → Protocol}
    {coin : (s : Statement) → PublicCoin (protocol s)}

/-- The typed keys of the existing commitment-compiled protocol. -/
abbrev ChallengeKey (coin : (s : Statement) → PublicCoin (protocol s)) :=
  Key Statement PUnit (fun s => compiledCoin Com (coin s))

/-- Challenge queries retain the original dependent response types. -/
abbrev challengeSpec (coin : (s : Statement) → PublicCoin (protocol s)) :=
  ofFn (fun k : ChallengeKey (Com := Com) coin => k.Challenge)

/-- The exact challenge coordinates used by the witness checker. -/
def verificationKeys (key : ChallengeKey (Com := Com) coin) : List (ChallengeKey (Com := Com) coin) :=
  (CorrelationIntractable.strictAncestors (compiledCoin Com (coin key.1)) key.2).map
    (fun pre => ⟨key.1, pre⟩) ++ [key]

/-- The selected challenge is always queried, including when the adversary did not query it. -/
theorem target_mem_verificationKeys (key : ChallengeKey (Com := Com) coin) :
    key ∈ verificationKeys key := List.mem_append_right _ (List.mem_cons_self)

variable (relation : WitnessCIRelation (Com := Com) coin)

/-- Exact witness verification using a shared cached oracle for the challenges. -/
noncomputable def check (output : Option (WitnessCIOutput relation)) :
    OracleComp (challengeSpec (Com := Com) coin) Bool := by
  classical
  exact match output with
  | none => pure false
  | some output => do
      let table ← readTable (fun k => Classical.arbitrary k.Challenge) (verificationKeys output.1)
      return witnessCheck relation table (some output)

/-- Deterministic replay of the oracle checker is the existing authenticated witness check. -/
theorem check_eq (h : Table Statement PUnit (fun s => compiledCoin Com (coin s)))
    (output : Option (WitnessCIOutput relation)) :
    evalWithAnswerFn (QueryImpl.ofFn h) (check relation output) = witnessCheck relation h output := by
  classical
  cases output with
  | none => rfl
  | some output =>
      simp only [check, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      have agrees := readTable_agrees (R := fun k : ChallengeKey (Com := Com) coin => k.Challenge)
        (fun k => Classical.arbitrary k.Challenge) h
        (verificationKeys output.1)
      rcases output with ⟨key, words, auth⟩
      simp only [witnessCheck]
      apply congrArg₂ Bool.and
      · apply congrArg (fun b => ((!relation.isQuery key || relation.complete key words) && b) &&
          relation.authenticate key words auth)
        apply prefixConsistent_congr
        intro p hp
        exact agrees ⟨key.1, p⟩ (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
      · exact congrArg (relation.check key words) (agrees key (target_mem_verificationKeys key))

/-- A successful check has queried its selected key in the actual deterministic log. -/
theorem check_target_queried (h : Table Statement PUnit (fun s => compiledCoin Com (coin s)))
    (output : WitnessCIOutput relation) :
    ⟨output.1, h output.1⟩ ∈ tableQueryLog (check relation (some output)) h := by
  classical
  simp only [check, tableQueryLog_bind, tableQueryLog_pure, List.append_nil, readTable_log]
  exact List.mem_map.mpr ⟨output.1, target_mem_verificationKeys output.1, rfl⟩

/-- The exact post-adversary checker runs on the adversary's challenge oracle. -/
noncomputable def experiment (A : OracleComp (challengeSpec (Com := Com) coin)
    (Option (WitnessCIOutput relation))) : OracleComp (challengeSpec (Com := Com) coin) Bool :=
  A >>= check relation

/-- Verification charges one call for every earlier challenge and one for the selected challenge. -/
theorem check_queryBound (output : WitnessCIOutput relation) :
    IsTotalQueryBound (check relation (some output)) (verificationKeys output.1).length := by
  classical
  simpa only [check, Nat.add_zero] using
    (isTotalQueryBound_bind (readTable_queryBound
      (fun k : ChallengeKey (Com := Com) coin => Classical.arbitrary k.Challenge)
      (verificationKeys output.1)) (n₂ := 0) (fun _ => by trivial))

/-- An adversary's query budget and a uniform verification budget add, including rejected outputs. -/
theorem experiment_queryBound
    (A : OracleComp (challengeSpec (Com := Com) coin) (Option (WitnessCIOutput relation)))
    (adversaryQueries verificationQueries : ℕ) (bounded : IsTotalQueryBound A adversaryQueries)
    (cap : ∀ key : ChallengeKey (Com := Com) coin, (verificationKeys key).length ≤ verificationQueries) :
    IsTotalQueryBound (experiment relation A) (adversaryQueries + verificationQueries) := by
  apply isTotalQueryBound_bind bounded
  intro output
  cases output with
  | none => trivial
  | some output => exact (check_queryBound relation output).mono (cap output.1)

/-- All authenticated, consistent witnesses that can win at one key, allowing adaptive selection. -/
def AuthenticatedBad (key : ChallengeKey (Com := Com) coin)
    (h : Table Statement PUnit (fun s => compiledCoin Com (coin s))) : Prop :=
  ∃ words auth, witnessCheck relation h (some ⟨key, words, auth⟩) = true

variable [DecidableEq (ChallengeKey (Com := Com) coin)]

/-- A bridge from authenticated witnesses to a common prefix whose bad set is sparse.
Independence of the target cell is separate from domination of authenticated prefixes. -/
structure Envelope where
  /-- A dominating prefix may use other oracle coordinates but not the target answer. -/
  words : (key : ChallengeKey (Com := Com) coin) →
    Table Statement PUnit (fun s => compiledCoin Com (coin s)) → PrefixMessages (coin key.1) key.2
  /-- Resampling the selected challenge cannot change the chosen prefix. -/
  independent : ∀ key h value,
    words key (Function.update h key value) = words key h
  /-- Every authenticated prefix consistent with earlier answers is below the chosen prefix. -/
  dominates : ∀ key h masked auth,
    prefixConsistent (coin key.1) key.2 masked (Table.fibre h key.1)
      (fun pre => relation.challengeEq ⟨key.1, pre⟩) = true →
    relation.authenticate key masked auth = true → relation.MaskLE key masked (words key h)

/-- A target-independent authenticated envelope converts per-prefix density into cell density. -/
theorem authenticatedBad_density (envelope : Envelope relation)
    (key : ChallengeKey (Com := Com) coin)
    (h : Table Statement PUnit (fun s => compiledCoin Com (coin s))) :
    Pr{let value ← ($ᵗ key.Challenge : ProbComp key.Challenge)}[
      AuthenticatedBad relation key (Function.update h key value)] ≤ (relation.error key).out := by
  classical
  refine (prEvent_mono _ _ _ (fun value won => ?_)).trans (relation.bad_bound key (envelope.words key h))
  obtain ⟨masked, auth, won⟩ := won
  simp only [witnessCheck, Bool.and_eq_true] at won
  have dominated := envelope.dominates key (Function.update h key value) masked auth won.1.1.2 won.1.2
  rw [envelope.independent] at dominated
  exact relation.monotone key masked (envelope.words key h) dominated
    (fun query => by simpa only [query, Bool.not_true, Bool.false_or] using won.1.1.1) value
    ((relation.check_iff _ _ _).mp (by simpa only [Function.update_self] using won.2))

/-- Adaptive success is bounded by the total queried-cell budget, including verification.
The envelope hypothesis is the authentication bridge, not a consequence of per-prefix density. -/
theorem experiment_le
    (envelope : Envelope relation)
    (A : OracleComp (challengeSpec (Com := Com) coin) (Option (WitnessCIOutput relation)))
    (queries : ℕ) (bounded : IsTotalQueryBound (experiment relation A) queries)
    (error : ℝ≥0∞) (errors : ∀ key, (relation.error key).out ≤ error) :
    Pr{let won ← (simulateQ randomOracle (experiment relation A)).run' ∅}[won = true] ≤
      queries * error := by
  apply prEvent_randomOracle_le_of_bad_queries (experiment relation A) queries bounded
    (fun won => won = true) (AuthenticatedBad relation) error
  · exact fun key h => (authenticatedBad_density relation envelope key h).trans (errors key)
  · intro h won
    simp only [experiment, evalWithAnswerFn_bind, check_eq] at won
    cases result : evalWithAnswerFn (QueryImpl.ofFn h) A with
    | none => simp only [result, witnessCheck, Bool.false_eq_true] at won
    | some output =>
        rw [result] at won
        refine ⟨⟨output.1, h output.1⟩, ?_, output.2.1, output.2.2, won⟩
        rw [experiment, tableQueryLog_bind, result]
        exact List.mem_append_right _ (check_target_queried relation h output)

/-- Key-dependent errors can be charged directly instead of taking the largest protocol error. -/
theorem experiment_le_weighted
    (envelope : Envelope relation)
    (A : OracleComp (challengeSpec (Com := Com) coin) (Option (WitnessCIOutput relation)))
    (error : ChallengeKey (Com := Com) coin → ℝ≥0∞) (budget : ℝ≥0∞)
    (bounded : WorstCaseCostBound (experiment relation A) ⟨error⟩ budget)
    (errors : ∀ key, (relation.error key).out ≤ error key) :
    Pr{let won ← (simulateQ randomOracle (experiment relation A)).run' ∅}[won = true] ≤ budget := by
  apply prEvent_randomOracle_le_of_bad_queries_weighted (experiment relation A) error budget bounded
    (fun won => won = true) (AuthenticatedBad relation)
  · exact fun key h => (authenticatedBad_density relation envelope key h).trans (errors key)
  · intro h won
    simp only [experiment, evalWithAnswerFn_bind, check_eq] at won
    cases result : evalWithAnswerFn (QueryImpl.ofFn h) A with
    | none => simp only [result, witnessCheck, Bool.false_eq_true] at won
    | some output =>
        rw [result] at won
        refine ⟨⟨output.1, h output.1⟩, ?_, output.2.1, output.2.2, won⟩
        rw [experiment, tableQueryLog_bind, result]
        exact List.mem_append_right _ (check_target_queried relation h output)

/-- Private random tapes are averaged outside the adaptive oracle run; the bound is uniform in them. -/
theorem randomized_experiment_le {Coins : Type} [SampleableType Coins]
    (envelope : Envelope relation)
    (A : Coins → OracleComp (challengeSpec (Com := Com) coin) (Option (WitnessCIOutput relation)))
    (queries : ℕ) (bounded : ∀ c, IsTotalQueryBound (experiment relation (A c)) queries)
    (error : ℝ≥0∞) (errors : ∀ key, (relation.error key).out ≤ error) :
    Pr{let c ← ($ᵗ Coins : ProbComp Coins);
       let won ← (simulateQ randomOracle (experiment relation (A c))).run' ∅}[won = true] ≤
      queries * error := by
  simpa only [prEvent_norm] using
    (prEvent_bind_le_of_forall_le ($ᵗ Coins : ProbComp Coins)
      (fun c => (simulateQ randomOracle (experiment relation (A c))).run' ∅)
      (fun won => won = true) (fun c => experiment_le relation envelope (A c) queries
        (bounded c) error errors))

end CompStark.Compiled.WitnessRandomOracle
