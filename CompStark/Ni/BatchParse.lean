/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.Parse
public import CompStark.Ni.BatchNatural
public import CompStark.Ni.BatchQueryBound

/-! # The batch verifier's rounds

As for the STARK (`Ni/Parse.lean`), every challenge round of the batch verifier is one duplex
call, and an accepting run queries all of them in order.

* `inputsB`: the batch's transcript schedule, the elements the verifier observes before each
  squeeze: the batch's domain separator, every instance's degree bits, the main commitment, the
  public values and the preprocessed commitment (`headB`), then with lookups the lookup grinding
  witness, before the lookup round, and the permutation commitment and the terminals, before the
  round of `α`; the quotient commitment and the out-of-domain grinding witness; the PCS's domain
  separator, the opened values and the batching grinding witness; each commit-phase commitment with
  its grinding witness, the first after FRI's domain separator; the final polynomial and the query
  grinding witness. The PCS's observations do not depend on the opening points
  (`claimCounts_batchRounds`, `roundValues_batchRounds`).
* `hasRounds_verifyBatchWith`: if the batch verifier accepts a proof on fixed answers, its log
  holds the call of every round of the proof's schedule.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.RandomOracle OracleSpec OracleComp

variable {F : Type}

/-- A passed `unless` check on logged answers: its condition holds, and the rest runs with the
same log. -/
theorem unless_logged {K : Nat} {α : Type} (b : Bool) (e : String)
    (k : PUnit → ExceptT String (WriterT (QueryLog (spec F K)) Id) α) (r : α)
    (h : ((have jp := k
      if b = true then jp PUnit.unit else (throw e >>= fun r ↦ jp r) :
        ExceptT String (WriterT (QueryLog (spec F K)) Id) α).run.run).1 = .ok r) :
    b = true ∧ ((have jp := k
      if b = true then jp PUnit.unit else (throw e >>= fun r ↦ jp r) :
        ExceptT String (WriterT (QueryLog (spec F K)) Id) α).run.run) = (k PUnit.unit).run.run := by
  cases b
  · exact absurd h (by intro h'; cases h')
  · exact ⟨rfl, rfl⟩

variable [BaseField F] {EF : Type} [Challenge F EF]

/-! ### The schedule -/

section Schedule
variable (instances : List (CompStark.Batch.Instance F)) (common : CompStark.Batch.Common F)
  (proof : CompStark.Batch.BatchProof F EF)

theorem claimCounts_batchRounds (z z' : EF) :
    claimCounts (CompStark.Batch.batchRounds instances common proof z) =
      claimCounts (CompStark.Batch.batchRounds instances common proof z') := by
  unfold claimCounts CompStark.Batch.batchRounds traceOpenings
  cases common.preprocessed <;> cases proof.permutationCommit <;>
    simp only [List.map_cons, List.map_map, List.map_nil, List.map_flatMap,
      Function.comp_def, apply_ite, List.cons_append, List.nil_append, List.append_nil]

theorem roundValues_batchRounds (z z' : EF) :
    roundValues (CompStark.Batch.batchRounds instances common proof z) =
      roundValues (CompStark.Batch.batchRounds instances common proof z') := by
  unfold roundValues CompStark.Batch.batchRounds traceOpenings
  cases common.preprocessed <;> cases proof.permutationCommit <;>
    simp only [List.flatMap_cons, List.flatMap_map, List.flatMap_nil, apply_ite, List.cons_append,
      List.nil_append, List.append_nil, List.flatMap_assoc]

end Schedule

/-- The preprocessed commitment's elements, none without one. -/
def prepDigest (common : CompStark.Batch.Common F) : List F :=
  (common.preprocessed.map (·.toList)).getD []

/-- The permutation commitment's elements, none without one. -/
def permDigest (proof : CompStark.Batch.BatchProof F EF) : List F :=
  (proof.permutationCommit.map (·.toList)).getD []

/-- FRI's domain separator on a batch proof for `S`. -/
noncomputable def friSeedB (S : Iop.Batch.Setup EF) : List F :=
  DomainSeparator.friSeed F EF (friAritiesB S) (2 ^ S.params.logFinalPolyLen)
    S.params.commitPowBits S.params.queryPowBits S.params.numQueries S.logTop S.params.logBlowup
    S.params.maxLogArity

/-- The rounds before the round of `α`: the lookup round, with lookups. -/
def lookupRounds (S : Iop.Batch.Setup EF) : ℕ := if S.hasLookups then 1 else 0

/-- The elements the batch verifier observes before the lookup phase: the batch's domain
separator, every instance's degree bits, the main commitment, the public values and the
preprocessed commitment. -/
noncomputable def headB (S : Iop.Batch.Setup EF) (common : CompStark.Batch.Common F)
    (pis : List (List F)) (proof : CompStark.Batch.BatchProof F EF) : List F :=
  CompStark.Batch.batchSeedOf EF S.params S.instances common ++
    coeffs (S.instances.map fun I ↦ (Ext.ofBase (I.logN : F) : EF)) ++ proof.mainCommit.toList ++
    pis.flatten ++ prepDigest common

/-- The elements the batch verifier observes on `proof` before each squeeze from the round of `α`
on, round by round: before `α`, without lookups the head, and the permutation commitment and the
terminals. -/
noncomputable def roundsB (S : Iop.Batch.Setup EF) (common : CompStark.Batch.Common F)
    (pis : List (List F)) (proof : CompStark.Batch.BatchProof F EF) : List (List F) :=
  ((if S.hasLookups then [] else headB S common pis proof) ++ permDigest proof ++
    coeffs (proof.lookupTerminals.toList.filterMap id)) ::
  (proof.quotientCommit.toList ++ witnessInput S.params.oodPowBits proof.oodWitness) ::
  (DomainSeparator.pcsSeed F EF
      (claimCounts (CompStark.Batch.batchRounds S.instances common proof 0))
      S.params.batchPowBits ++
    coeffs (roundValues (CompStark.Batch.batchRounds S.instances common proof 0)) ++
    witnessInput S.params.batchPowBits proof.fri.batchWitness) ::
  prependSeed (friSeedB S)
    (((proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).map fun cw ↦
      cw.1.toList ++ witnessInput S.params.commitPowBits cw.2) ++
    [coeffs proof.fri.finalPoly.toList ++
      witnessInput S.params.queryPowBits proof.fri.queryWitness])

/-- The elements the batch verifier observes on `proof` before each squeeze, round by round: with
lookups, the head and the lookup grinding witness before the lookup round, then `roundsB`. -/
noncomputable def inputsB (S : Iop.Batch.Setup EF) (common : CompStark.Batch.Common F)
    (pis : List (List F)) (proof : CompStark.Batch.BatchProof F EF) : List (List F) :=
  (if S.hasLookups then
    [headB S common pis proof ++ witnessInput S.params.lookupPowBits (proof.lookupWitness.getD 0)]
  else []) ++ roundsB S common pis proof

section Getters
variable (S : Iop.Batch.Setup EF) (common : CompStark.Batch.Common F) (pis : List (List F))
  (proof : CompStark.Batch.BatchProof F EF)

theorem length_lookupPrefix :
    (if S.hasLookups then
      [headB S common pis proof ++ witnessInput S.params.lookupPowBits (proof.lookupWitness.getD 0)]
    else []).length = lookupRounds S := by
  unfold lookupRounds
  split <;> rfl

/-- From the round of `α` on, the schedule is `roundsB`. -/
theorem inputsB_getD_add (j : Nat) :
    (inputsB S common pis proof).getD (lookupRounds S + j) [] =
      (roundsB S common pis proof).getD j [] := by
  rw [inputsB, ← length_lookupPrefix S common pis proof, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]

/-- With lookups, the lookup round observes the head and the lookup grinding witness. -/
theorem inputsB_getD_zero (h : S.hasLookups = true) :
    (inputsB S common pis proof).getD 0 [] =
      headB S common pis proof ++
        witnessInput S.params.lookupPowBits (proof.lookupWitness.getD 0) := by
  simp only [inputsB, h, ↓reduceIte, List.singleton_append, List.getD_cons_zero]

theorem inputsB_getD_alpha :
    (inputsB S common pis proof).getD (lookupRounds S) [] =
      (if S.hasLookups then [] else headB S common pis proof) ++ permDigest proof ++
        coeffs (proof.lookupTerminals.toList.filterMap id) := by
  rw [← Nat.add_zero (lookupRounds S), inputsB_getD_add]
  rfl

theorem inputsB_getD_ood :
    (inputsB S common pis proof).getD (lookupRounds S + 1) [] =
      proof.quotientCommit.toList ++ witnessInput S.params.oodPowBits proof.oodWitness := by
  rw [inputsB_getD_add]
  rfl

theorem inputsB_getD_pcs :
    (inputsB S common pis proof).getD (lookupRounds S + 2) [] =
      DomainSeparator.pcsSeed F EF
        (claimCounts (CompStark.Batch.batchRounds S.instances common proof 0))
        S.params.batchPowBits ++
      coeffs (roundValues (CompStark.Batch.batchRounds S.instances common proof 0)) ++
      witnessInput S.params.batchPowBits proof.fri.batchWitness := by
  rw [inputsB_getD_add]
  rfl

theorem inputsB_getD_fri (k : Nat) : (inputsB S common pis proof).getD (lookupRounds S + 3 + k) [] =
    seedAt (friSeedB S) k ++
      ((((proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).map fun cw ↦
        cw.1.toList ++ witnessInput S.params.commitPowBits cw.2) ++
      [coeffs proof.fri.finalPoly.toList ++
        witnessInput S.params.queryPowBits proof.fri.queryWitness]).getD k []) := by
  rw [Nat.add_assoc, inputsB_getD_add, roundsB, show 3 + k = k + 1 + 1 + 1 by omega,
    List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
  rcases h : ((proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).map fun cw ↦
      cw.1.toList ++ witnessInput S.params.commitPowBits cw.2) ++
      [coeffs proof.fri.finalPoly.toList ++
        witnessInput S.params.queryPowBits proof.fri.queryWitness]
    with _ | ⟨b, bs⟩
  · simp only [List.append_eq_nil_iff, List.cons_ne_nil, and_false] at h
  · exact getD_prependSeed _ _ _ _

theorem inputsB_getD_fold (j : Nat)
    (hj : j < (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length) :
    (inputsB S common pis proof).getD (lookupRounds S + 3 + j) [] = seedAt (friSeedB S) j ++
      (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)[j].1.toList ++
        witnessInput S.params.commitPowBits
          (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)[j].2 := by
  rw [inputsB_getD_fri, List.append_assoc, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp only [List.length_map]; exact hj)]
  simp only [List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]

theorem inputsB_getD_last :
    (inputsB S common pis proof).getD
      (lookupRounds S + 3 + (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length)
        [] =
      seedAt (friSeedB S)
        (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length ++
      coeffs proof.fri.finalPoly.toList ++
        witnessInput S.params.queryPowBits proof.fri.queryWitness := by
  rw [inputsB_getD_fri, List.append_assoc, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp only [List.length_map]; omega)]
  simp only [List.length_map, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

theorem length_inputsB :
    (inputsB S common pis proof).length = lookupRounds S + 2 + 2 +
      (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length := by
  rw [inputsB, List.length_append, length_lookupPrefix, roundsB]
  rcases h : ((proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).map fun cw ↦
      cw.1.toList ++ witnessInput S.params.commitPowBits cw.2) ++
      [coeffs proof.fri.finalPoly.toList ++
        witnessInput S.params.queryPowBits proof.fri.queryWitness]
    with _ | ⟨b, bs⟩
  · simp only [List.append_eq_nil_iff, List.cons_ne_nil, and_false] at h
  · have := congrArg List.length h
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at this
    simp only [prependSeed, List.length_cons]
    omega

end Getters

/-! ### The batch verifier's run on logged answers -/

section Run
variable {K : Nat} (answer : (q : Query F) → Answer K q)

theorem out_observeExts_nil (xs : List EF) (cap : Digest F) (input : List F) :
    out answer (observeExts (idealLogged answer) xs) ⟨cap, input, []⟩ =
      (.ok ((), ⟨cap, input ++ coeffs xs, []⟩), []) := by
  rw [out_observeExts]
  split
  · rename_i h
    rw [h, List.append_nil]
  · rfl

/-- **The lookup phase on logged answers.** From the head, an accepted lookup phase queries the
lookup round, with lookups, and leaves the challenger at the round of `α` with its input. -/
theorem out_lookupPhase_logs (S : Iop.Batch.Setup EF) (hK : 2 * Challenge.d EF + 1 ≤ K)
    (common : CompStark.Batch.Common F) (proof : CompStark.Batch.BatchProof F EF)
    (pis : List (List F)) (hperm : proof.permutationCommit.isSome = S.hasLookups)
    {r : (EF × EF) × Sponge F}
    (h : (out answer (CompStark.Batch.lookupPhase (H := idealLogged answer) S.params S.instances
      proof : M _ (EF × EF)) ⟨initCap, headB S common pis proof, []⟩).1 = .ok r) :
    r.2 = ⟨capAt answer (inputsB S common pis proof) (lookupRounds S),
      (inputsB S common pis proof).getD (lookupRounds S) [], []⟩ ∧
    ∃ rest, (out answer (CompStark.Batch.lookupPhase (H := idealLogged answer) S.params
      S.instances proof : M _ (EF × EF)) ⟨initCap, headB S common pis proof, []⟩).2 =
      if S.hasLookups then ⟨keyAt answer (inputsB S common pis proof) 0,
        answer (keyAt answer (inputsB S common pis proof) 0)⟩ :: rest else [] := by
  set blocks := inputsB S common pis proof
  have hpd : ∀ cap samples, S.hasLookups = true →
      out answer (observeList (idealLogged answer)
        ((proof.permutationCommit.map (·.toList)).getD [])) ⟨cap, [], samples⟩ =
      (.ok ((), ⟨cap, permDigest proof, []⟩), []) := by
    intro cap samples hl
    obtain ⟨root, hroot⟩ := Option.isSome_iff_exists.mp (hperm.trans hl)
    have hne : (root.toList : List F) ≠ [] :=
      List.ne_nil_of_length_pos (by simp only [Vector.length_toList]; omega)
    simp only [hroot, Option.map_some, Option.getD_some, out_observeList,
      ite_eq_right_of_eq_false _ _ (eq_false hne), permDigest, List.nil_append]
  unfold CompStark.Batch.lookupPhase at h ⊢
  have hhas : CompStark.Batch.hasLookups S.instances = S.hasLookups := rfl
  rw [hhas] at h ⊢
  cases hl : S.hasLookups with
  | false =>
    simp only [hl, Bool.false_eq_true, ↓reduceIte] at h ⊢
    simp only [out_bind, out_pure, out_observeList_nil, out_observeExts_nil,
      List.append_nil] at h ⊢
    obtain ⟨-, h2⟩ := Prod.mk.inj (Except.ok.inj h)
    refine ⟨?_, [], trivial⟩
    have h0 : lookupRounds S = 0 := by simp only [lookupRounds, hl]; rfl
    have ha := inputsB_getD_alpha S common pis proof
    rw [h0, hl] at ha
    rw [← h2, h0]
    change _ = (⟨_, (inputsB S common pis proof).getD 0 [], []⟩ : Sponge F)
    rw [ha]
    simp only [Bool.false_eq_true, ↓reduceIte, permDigest]
    rfl
  | true =>
    simp only [hl, ↓reduceIte] at h ⊢
    have h1 : lookupRounds S = 1 := by simp only [lookupRounds, hl]; rfl
    have hin₀ : blocks.getD 0 [] = headB S common pis proof ++
        witnessInput S.params.lookupPowBits (proof.lookupWitness.getD 0) :=
      inputsB_getD_zero S common pis proof hl
    have hin₁ : blocks.getD 1 [] = permDigest proof ++
        coeffs (proof.lookupTerminals.toList.filterMap id) := by
      rw [← h1, inputsB_getD_alpha, hl]
      rfl
    rw [h1]
    by_cases hbits : S.params.lookupPowBits = 0
    · rw [hbits] at h ⊢
      simp only [witnessInput, hbits, ↓reduceIte, List.append_nil] at hin₀
      rw [← hin₀, show initCap = capAt answer blocks 0 from rfl] at h ⊢
      simp only [out_bind, out_checkWitness_zero] at h ⊢
      have hv₀ := out_sampleExt_nil (EF := EF) answer (by omega) (capAt answer blocks 0)
        (blocks.getD 0 [])
      simp only [ensure, ↓reduceIte, out_pure, hv₀] at h ⊢
      rw [out_sampleExt_pop answer _ _ _ (by rw [List.length_drop, Vector.length_toList]; omega)]
        at h ⊢
      dsimp only at h ⊢
      rw [hpd _ _ hl] at h ⊢
      dsimp only at h ⊢
      rw [out_observeExts_nil] at h ⊢
      dsimp only at h ⊢
      obtain ⟨-, h2⟩ := Prod.mk.inj (Except.ok.inj h)
      refine ⟨?_, _, rfl⟩
      rw [← h2, hin₁]
      rfl
    · obtain ⟨v, hv⟩ := out_checkWitness_pos answer _ hbits (proof.lookupWitness.getD 0) initCap
        (headB S common pis proof) []
      simp only [witnessInput, hbits, ↓reduceIte] at hin₀
      rw [out_bind, hv] at h ⊢
      dsimp only at h ⊢
      rw [← hin₀, show initCap = capAt answer blocks 0 from rfl] at h ⊢
      rw [out_bind] at h ⊢
      cases v with
      | false =>
        simp only [ensure, Bool.false_eq_true, ↓reduceIte, out_throw] at h
        exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
      | true =>
        simp only [ensure, ↓reduceIte, out_pure, out_bind] at h ⊢
        rw [out_sampleExt_pop answer _ _ _ (by rw [List.length_tail, Vector.length_toList]; omega)]
          at h ⊢
        dsimp only at h ⊢
        rw [out_sampleExt_pop answer _ _ _ (by
          rw [List.length_drop, List.length_tail, Vector.length_toList]; omega)] at h ⊢
        dsimp only at h ⊢
        rw [hpd _ _ hl] at h ⊢
        dsimp only at h ⊢
        rw [out_observeExts_nil] at h ⊢
        dsimp only at h ⊢
        obtain ⟨-, h2⟩ := Prod.mk.inj (Except.ok.inj h)
        refine ⟨?_, _, rfl⟩
        rw [← h2, hin₁]
        rfl

/-- The batch verifier on logged answers, if it accepts, queries every round of the schedule. -/
theorem verifyBatchWith_logs (S : Iop.Batch.Setup EF)
    (hK : S.params.numQueries + 2 * Challenge.d EF + 1 ≤ K)
    (common : CompStark.Batch.Common F) (proof : CompStark.Batch.BatchProof F EF)
    (pis : List (List F))
    (hok : (CompStark.Batch.verifyBatchWith (idealLogged answer) S.params S.instances common
      proof pis).run.1 = .ok ()) :
    LogsRounds answer (inputsB S common pis proof) 0 (inputsB S common pis proof).length
      (CompStark.Batch.verifyBatchWith (idealLogged answer) S.params S.instances common proof
        pis).run.2 := by
  unfold CompStark.Batch.verifyBatchWith at hok ⊢
  obtain ⟨hcount, hrw⟩ := unless_logged _ _ _ _ hok
  rw [hrw] at hok ⊢
  obtain ⟨-, hrw⟩ := unless_logged _ _ _ _ hok
  rw [hrw] at hok ⊢
  obtain ⟨-, hrw⟩ := unless_logged _ _ _ _ hok
  rw [hrw] at hok ⊢
  obtain ⟨-, hrw⟩ := unless_logged _ _ _ _ hok
  rw [hrw] at hok ⊢
  obtain ⟨-, hrw⟩ := unless_logged _ _ _ _ hok
  rw [hrw] at hok ⊢
  obtain ⟨-, hrw⟩ := unless_logged _ _ _ _ hok
  rw [hrw] at hok ⊢
  obtain ⟨-, hrw⟩ := unless_logged _ _ _ _ hok
  rw [hrw] at hok ⊢
  obtain ⟨hlk, hrw⟩ := unless_logged _ _ _ _ hok
  rw [hrw] at hok ⊢
  obtain ⟨-, hrw⟩ := unless_logged _ _ _ _ hok
  rw [hrw] at hok ⊢
  clear hrw
  have hperm := (lookupShapeOk_spec S.params S.instances proof hlk).2
  dsimp only at hok ⊢
  rw [run_stateT_bind _ _ _ (fun a ↦ by
    rcases a with ⟨⟨_, _, _, _⟩, _⟩
    dsimp only
    split
    · split <;> rfl
    · rfl)] at hok ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at hcount
  have hsize : proof.opened.size = S.k := by rw [hcount.1.1.1.1, length_instances]
  rcases hrun : out answer _ { cap := initCap, input := [], samples := [] } with ⟨_ | a, w⟩
  · rw [hrun] at hok
    cases hok
  rw [hrun] at hok
  dsimp only
  have hrun1 := congrArg Prod.fst hrun
  have hrun2 := congrArg Prod.snd hrun
  dsimp only at hrun1 hrun2
  rw [← hrun2]
  clear hrun hrun2 hok
  set blocks := inputsB S common pis proof with hblocks
  -- the observations of the head
  obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
  rw [out_observeList_nil] at h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, out_observeList_nil, List.nil_append]
  obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
  rw [out_observeExts_nil] at h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, out_observeExts_nil, List.nil_append]
  obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
  rw [out_observeList_nil] at h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, out_observeList_nil, List.nil_append]
  obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
  rw [out_observeList_nil] at h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, out_observeList_nil, List.nil_append]
  obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
  rw [out_observeList_nil] at h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, out_observeList_nil, List.nil_append]
  have hhead : [] ++ CompStark.Batch.batchSeedOf EF S.params S.instances common ++
      coeffs (S.instances.map fun I ↦ (Ext.ofBase (I.logN : F) : EF)) ++ proof.mainCommit.toList ++
      pis.flatten ++ ((common.preprocessed.map (·.toList)).getD []) =
        headB S common pis proof := by
    simp only [headB, prepDigest, List.nil_append]
  rw [hhead] at hrun1 ⊢
  -- the lookup phase
  obtain ⟨⟨la, lb⟩, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
  obtain ⟨hs₁, lrest, hlrest⟩ := out_lookupPhase_logs answer S (by omega) common proof pis hperm h₁
  dsimp only at hs₁
  subst hs₁
  rw [hlog, hlrest]
  dsimp only at hrun1 ⊢
  set L := lookupRounds S with hL
  have hlookup : LogsRounds answer blocks 0 L
      (if S.hasLookups then ⟨keyAt answer blocks 0, answer (keyAt answer blocks 0)⟩ :: lrest
        else []) := by
    intro j hj hj'
    rw [hL, lookupRounds] at hj'
    split at hj'
    · rename_i hl
      obtain rfl : j = 0 := by omega
      simp only [hl, ↓reduceIte, List.map_cons, List.mem_cons, true_or]
    · omega
  refine logsRounds_append hlookup ?_
  -- the round of `α`
  have hv₀ := out_sampleExt_nil (EF := EF) answer (by omega) (capAt answer blocks L)
    (blocks.getD L [])
  obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
  rw [hv₀] at h₁
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, hv₀]
  refine logsRounds_cons (by simp only [keyAt, List.map_cons, List.map_nil,
    List.mem_singleton]) ?_
  rw [show (answer (.duplex (capAt answer blocks L) (blocks.getD L []))).1 =
    capAt answer blocks (L + 1) from rfl] at hrun1 ⊢
  -- the round of `ζ`
  have hqc : proof.quotientCommit.toList ≠ [] :=
    List.ne_nil_of_length_pos (by simp only [Vector.length_toList]; omega)
  obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
  rw [out_observeList, ite_eq_right_of_eq_false _ _ (eq_false hqc)] at h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, out_observeList, ite_eq_right_of_eq_false _ _ (eq_false hqc), List.nil_append]
  dsimp only at hrun1 ⊢
  rw [List.nil_append] at hrun1 ⊢
  have hin₁ : blocks.getD (L + 1) [] =
      proof.quotientCommit.toList ++ witnessInput S.params.oodPowBits proof.oodWitness :=
    inputsB_getD_ood S common pis proof
  have hzeta : ∀ (la lb alpha zeta : EF) (smp : List F) {res : (EF × EF × EF × EF) × Sponge F},
      (out answer (do
        ensure (S.instances.all fun I ↦ Ext.powTwo zeta I.logN - 1 != 0)
          "out-of-domain point in a trace domain"
        verifyPcs (idealLogged answer) S.params
          (CompStark.Batch.batchRounds S.instances common proof zeta) proof.fri
        pure (la, lb, alpha, zeta)) ⟨capAt answer blocks (L + 2), [], smp⟩).1 = .ok res →
      LogsRounds answer blocks (L + 2) blocks.length
        (out answer (do
          ensure (S.instances.all fun I ↦ Ext.powTwo zeta I.logN - 1 != 0)
            "out-of-domain point in a trace domain"
          verifyPcs (idealLogged answer) S.params
            (CompStark.Batch.batchRounds S.instances common proof zeta) proof.fri
          pure (la, lb, alpha, zeta)) ⟨capAt answer blocks (L + 2), [], smp⟩).2 := by
    intro la lb alpha zeta smp res h
    obtain ⟨-, h, hlog⟩ := out_ensure_bind_ok answer h
    rw [hlog]
    obtain ⟨_, _, h₂, -, hlog⟩ := out_bind_ok answer h
    rw [hlog]
    refine logsRounds_left ?_
    rw [hblocks, length_inputsB]
    refine verifyPcs_logs (by omega) _ (L + 2) proof.fri _ (S.logTop :: S.friHeights)
      (descHeights_batchRounds S common proof zeta hsize) ?_
      (fun j hj ↦ by
        rw [show L + 2 + 1 + j = lookupRounds S + 3 + j by omega]
        exact inputsB_getD_fold S common pis proof j hj)
      (by
        rw [show L + 2 + 1 = lookupRounds S + 3 by omega]
        exact inputsB_getD_last S common pis proof)
      _ h₂
    rw [inputsB_getD_pcs, claimCounts_batchRounds _ _ _ zeta 0,
      roundValues_batchRounds _ _ _ zeta 0]
  by_cases hbits : S.params.oodPowBits = 0
  · simp only [witnessInput, hbits, ↓reduceIte, List.append_nil] at hin₁
    obtain ⟨_, s₂, h₂, hrun1, hlog⟩ := out_bind_ok answer hrun1
    rw [hbits, out_checkWitness_zero] at h₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₂)
    rw [hlog, hbits, out_checkWitness_zero]
    refine logsRounds_right ?_
    obtain ⟨-, hrun1, hlog⟩ := out_ensure_bind_ok answer hrun1
    rw [hlog]
    rw [← hin₁] at hrun1 ⊢
    have hv₁ := out_sampleExt_nil (EF := EF) answer (by omega) (capAt answer blocks (L + 1))
      (blocks.getD (L + 1) [])
    obtain ⟨_, s₃, h₃, hrun1, hlog⟩ := out_bind_ok answer hrun1
    rw [hv₁] at h₃
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₃)
    rw [hlog, hv₁]
    refine logsRounds_cons (by simp only [keyAt, List.map_cons, List.map_nil,
      List.mem_singleton]) ?_
    exact hzeta _ _ _ _ _ hrun1
  · simp only [witnessInput, hbits, ↓reduceIte] at hin₁
    obtain ⟨v, hv⟩ := out_checkWitness_pos answer _ hbits proof.oodWitness
      (capAt answer blocks (L + 1)) proof.quotientCommit.toList []
    obtain ⟨_, s₂, h₂, hrun1, hlog⟩ := out_bind_ok answer hrun1
    rw [hv] at h₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₂)
    rw [hlog, hv, ← hin₁]
    rw [← hin₁] at hrun1
    refine logsRounds_cons (by simp only [keyAt, List.map_cons, List.map_nil,
      List.mem_singleton]) ?_
    obtain ⟨-, hrun1, hlog⟩ := out_ensure_bind_ok answer hrun1
    rw [hlog]
    have hv₁ := out_sampleExt_pop (EF := EF) answer
      (answer (.duplex (capAt answer blocks (L + 1)) (blocks.getD (L + 1) []))).1 []
      (answer (.duplex (capAt answer blocks (L + 1)) (blocks.getD (L + 1) []))).2.toList.tail
      (by rw [List.length_tail, Vector.length_toList]; omega)
    obtain ⟨_, s₃, h₃, hrun1, hlog⟩ := out_bind_ok answer hrun1
    rw [hv₁] at h₃
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₃)
    rw [hlog, hv₁, List.nil_append]
    exact hzeta _ _ _ _ _ hrun1

/-- **The first call.** If the batch verifier on logged answers accepts, its log starts with
the duplex call of the first round. -/
theorem verifyBatchWith_log_head (S : Iop.Batch.Setup EF)
    (hK : S.params.numQueries + 2 * Challenge.d EF + 1 ≤ K)
    (common : CompStark.Batch.Common F) (proof : CompStark.Batch.BatchProof F EF)
    (pis : List (List F))
    (hok : (CompStark.Batch.verifyBatchWith (idealLogged answer) S.params S.instances common
      proof pis).run.1 = .ok ()) :
    ∃ rest, (CompStark.Batch.verifyBatchWith (idealLogged answer) S.params S.instances common
      proof pis).run.2 = ⟨keyAt answer (inputsB S common pis proof) 0,
        answer (keyAt answer (inputsB S common pis proof) 0)⟩ :: rest := by
  unfold CompStark.Batch.verifyBatchWith at hok ⊢
  obtain ⟨hcount, hrw⟩ := unless_logged _ _ _ _ hok
  rw [hrw] at hok ⊢
  obtain ⟨-, hrw⟩ := unless_logged _ _ _ _ hok
  rw [hrw] at hok ⊢
  obtain ⟨-, hrw⟩ := unless_logged _ _ _ _ hok
  rw [hrw] at hok ⊢
  obtain ⟨-, hrw⟩ := unless_logged _ _ _ _ hok
  rw [hrw] at hok ⊢
  obtain ⟨-, hrw⟩ := unless_logged _ _ _ _ hok
  rw [hrw] at hok ⊢
  obtain ⟨-, hrw⟩ := unless_logged _ _ _ _ hok
  rw [hrw] at hok ⊢
  obtain ⟨-, hrw⟩ := unless_logged _ _ _ _ hok
  rw [hrw] at hok ⊢
  obtain ⟨hlk, hrw⟩ := unless_logged _ _ _ _ hok
  rw [hrw] at hok ⊢
  obtain ⟨-, hrw⟩ := unless_logged _ _ _ _ hok
  rw [hrw] at hok ⊢
  clear hrw
  have hperm := (lookupShapeOk_spec S.params S.instances proof hlk).2
  dsimp only at hok ⊢
  rw [run_stateT_bind _ _ _ (fun a ↦ by
    rcases a with ⟨⟨_, _, _, _⟩, _⟩
    dsimp only
    split
    · split <;> rfl
    · rfl)] at hok ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at hcount
  have hsize : proof.opened.size = S.k := by rw [hcount.1.1.1.1, length_instances]
  rcases hrun : out answer _ { cap := initCap, input := [], samples := [] } with ⟨_ | a, w⟩
  · rw [hrun] at hok
    cases hok
  rw [hrun] at hok
  dsimp only
  have hrun1 := congrArg Prod.fst hrun
  have hrun2 := congrArg Prod.snd hrun
  dsimp only at hrun1 hrun2
  rw [← hrun2]
  clear hrun hrun2 hok
  set blocks := inputsB S common pis proof with hblocks
  -- the observations of the head
  obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
  rw [out_observeList_nil] at h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, out_observeList_nil, List.nil_append]
  obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
  rw [out_observeExts_nil] at h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, out_observeExts_nil, List.nil_append]
  obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
  rw [out_observeList_nil] at h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, out_observeList_nil, List.nil_append]
  obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
  rw [out_observeList_nil] at h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, out_observeList_nil, List.nil_append]
  obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
  rw [out_observeList_nil] at h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, out_observeList_nil, List.nil_append]
  have hhead : [] ++ CompStark.Batch.batchSeedOf EF S.params S.instances common ++
      coeffs (S.instances.map fun I ↦ (Ext.ofBase (I.logN : F) : EF)) ++ proof.mainCommit.toList ++
      pis.flatten ++ ((common.preprocessed.map (·.toList)).getD []) =
        headB S common pis proof := by
    simp only [headB, prepDigest, List.nil_append]
  rw [hhead] at hrun1 ⊢
  -- the lookup phase
  obtain ⟨⟨la, lb⟩, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
  obtain ⟨hs₁, lrest, hlrest⟩ := out_lookupPhase_logs answer S (by omega) common proof pis hperm h₁
  dsimp only at hs₁
  subst hs₁
  rw [hlog, hlrest]
  dsimp only at hrun1 ⊢
  cases hl : S.hasLookups
  · -- the round of `α` is the first
    have h0 : lookupRounds S = 0 := by simp only [lookupRounds, hl]; rfl
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
    rw [h0] at hrun1 ⊢
    have hv₀ := out_sampleExt_nil (EF := EF) answer (by omega) (capAt answer blocks 0)
      (blocks.getD 0 [])
    obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
    rw [hv₀] at h₁
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
    rw [hlog, hv₀]
    exact ⟨_, rfl⟩
  · simp only [↓reduceIte, List.cons_append]
    exact ⟨_, rfl⟩

end Run

/-- The batch verifier on logged answers gives the batch verifier on the answers, and its log. -/
theorem run_idealLoggedB {K : Nat} {answer : (q : Query F) → Answer K q} (P : Fri.Params)
    (instances : List (CompStark.Batch.Instance F)) (common : CompStark.Batch.Common F)
    (proof : CompStark.Batch.BatchProof F EF) (pis : List (List F)) :
    (CompStark.Batch.verifyBatchWith (idealLogged answer) P instances common proof pis).run =
      (CompStark.Batch.verifyBatchWith (idealOf answer) P instances common proof pis,
        tableQueryLog (CompStark.Batch.verifyBatchWith (ideal F K) P instances common proof pis)
          answer) := by
  have h := QueryImpl.fst_map_run_withLogging (QueryImpl.ofFn answer)
    (CompStark.Batch.verifyBatchWith (ideal F K) P instances common proof pis)
  rw [simulateQ_verifyBatchWith, simulateQ_verifyBatchWith] at h
  exact Prod.ext h (tableQueryLog_verifyBatchWith answer P instances common proof pis).symm

/-- **The batch verifier queries every round.** If the batch verifier accepts a proof on the
answers `answer`, the duplex call of every round of the proof's schedule is in its log. -/
theorem hasRounds_verifyBatchWith (S : Iop.Batch.Setup EF)
    (answer : (q : Query F) → Answer S.streamLen q) (common : CompStark.Batch.Common F)
    (proof : CompStark.Batch.BatchProof F EF) (pis : List (List F))
    (hok : CompStark.Batch.verifyBatchWith (idealOf answer) S.params S.instances common proof pis =
      .ok ()) :
    HasRounds answer (tableQueryLog (CompStark.Batch.verifyBatchWith (ideal F S.streamLen)
      S.params S.instances common proof pis) answer) (inputsB S common pis proof)
      (inputsB S common pis proof).length := by
  have h := verifyBatchWith_logs answer S (le_refl _) common proof pis
    (by rw [run_idealLoggedB]; exact hok)
  rw [run_idealLoggedB] at h
  exact fun j hj ↦ h j (Nat.zero_le j) hj

end CompStark.Ni
