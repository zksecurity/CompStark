/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.QueryBound
public import CompStark.Ni.BatchBcs

/-! # The batch verifier's oracle calls

FRI on rounds of mixed heights makes at most `n (1 + L + 2 G)` calls per query and round
(`Fri.costs_verifyPcs`, `Ni/QueryBound.lean`), so the batch verifier makes at most
`Setup.verifierCalls` (`isTotalQueryBound_verifyBatchWith`), the lookup round's included. The
batch setup makes at most four calls per leaf of its tree (`isTotalQueryBound_setupRo`).
-/

@[expose] public section
namespace CompStark.Iop.Batch.Setup
open CompStark.Stark CompStark.Fri CompStark.RandomOracle CompStark.Ni OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] (S : Setup EF)

/-- A failed `unless` check makes no calls; a passed one costs what the rest costs. -/
theorem bound_unless {ι : Type} {spec : OracleSpec ι} {α : Type} (b : Bool) (e : String)
    (k : PUnit → ExceptT String (OracleComp spec) α) (n : Nat)
    (h : b = true → IsTotalQueryBound (k PUnit.unit).run n) :
    IsTotalQueryBound (have jp := k
      if b = true then jp PUnit.unit else (throw e >>= fun r ↦ jp r) :
        ExceptT String (OracleComp spec) α).run n := by
  cases b
  · show IsTotalQueryBound (pure (Except.error e) : OracleComp spec _) n
    trivial
  · exact h rfl

theorem isTotalQueryBound_verifyBatchWith (common : CompStark.Batch.Common F)
    (proof : CompStark.Batch.BatchProof F EF) (pis : List (List F)) :
    IsTotalQueryBound (CompStark.Batch.verifyBatchWith (ideal F S.streamLen) S.params S.instances
      common proof pis) S.verifierCalls := by
  unfold CompStark.Batch.verifyBatchWith
  refine bound_unless _ _ _ _ fun hcount ↦ ?_
  refine bound_unless _ _ _ _ fun hdb ↦ ?_
  refine bound_unless _ _ _ _ fun hq ↦ ?_
  refine bound_unless _ _ _ _ fun _ ↦ ?_
  refine bound_unless _ _ _ _ fun _ ↦ ?_
  refine bound_unless _ _ _ _ fun _ ↦ ?_
  refine bound_unless _ _ _ _ fun hprep ↦ ?_
  refine bound_unless _ _ _ _ fun hlk ↦ ?_
  refine bound_unless _ _ _ _ fun _ ↦ ?_
  have hperm := (lookupShapeOk_spec S.params S.instances proof hlk).2
  simp only [Bool.and_eq_true, beq_iff_eq] at hcount hprep
  have hsize : proof.opened.size = S.k := by rw [hcount.1.1.1.1, length_instances]
  have hlp : Costs (H := ideal F S.streamLen)
      (CompStark.Batch.lookupPhase S.params S.instances proof : M _ (EF × EF)) S.lookupCalls
      fun _ ↦ True := by
    unfold CompStark.Batch.lookupPhase lookupCalls
    rw [← hasLookups]
    cases S.hasLookups
    · exact costs_free_bind (costs_pure _ (fun _ ↦ True) trivial) fun _ _ ↦
        costs_free_bind (costs_observeList _) fun _ _ ↦
        costs_free_bind (costs_observeExts _) fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial
    · simp only [↓reduceIte]
      exact costs_bind_le (costs_checkWitness _ _) (b := 2 * Challenge.d EF)
        (fun _ _ ↦ costs_ensure_bind fun _ ↦ costs_bind_le (b := Challenge.d EF)
          (costs_sampleExt (EF := EF)) (fun _ _ ↦
          costs_bind_le (b := 0) (costs_sampleExt (EF := EF)) (fun _ _ ↦
            costs_free_bind (costs_pure _ (fun _ ↦ True) trivial) fun _ _ ↦
            costs_free_bind (costs_observeList _) fun _ _ ↦
            costs_free_bind (costs_observeExts _) fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial)
            (by omega)) (by omega)) (by omega)
  dsimp only
  rw [ExceptT.run_bind]
  refine (isTotalQueryBound_bind (n₂ := 0) ((?_ : Costs (H := ideal F S.streamLen) _
    S.verifierCalls fun _ ↦ True) _).1 fun r ↦ ?_).mono (by omega)
  swap
  · rcases r with _ | ⟨⟨la, lb, alpha, zeta⟩, s⟩
    · trivial
    · dsimp only
      split
      · split
        · trivial
        · trivial
      · trivial
  set G := S.friHeights.length
  set c := 1 + S.logTop + 2 * G
  set V := Challenge.d EF + 2 + (Challenge.d EF + 1) * S.friArities.length +
    S.params.numQueries * (1 + (S.inputRounds + S.friArities.length) * c)
  have hpcs : ∀ zeta : EF, Costs (H := ideal F S.streamLen) (verifyPcs (ideal F S.streamLen)
      S.params (CompStark.Batch.batchRounds S.instances common proof zeta) proof.fri) V
      fun _ ↦ True := by
    intro zeta
    have hD := descHeights_batchRounds S common proof zeta hsize
    have hmem := mem_matHeights S common proof zeta hsize
    refine costs_mono (costs_verifyPcs S.params _ proof.fri S.logTop G
      (fun h hh ↦ ?_) (S.logTop :: S.friHeights) (fun h hh ↦ ?_) le_rfl) ?_ fun _ h ↦ h
    · obtain ⟨i, rfl⟩ := (hmem h).mp hh
      exact logTop_ge S i
    · obtain ⟨i, rfl⟩ := (hmem h).mp hh
      rw [← hD, mem_descHeights]
      exact (hmem _).mpr ⟨i, rfl⟩
    · rw [hD, List.headD_cons]
      have hA : (foldSchedule S.params.maxLogArity (S.params.logBlowup + S.params.logFinalPolyLen)
          S.logTop (S.logTop :: S.friHeights)).length = S.friArities.length := rfl
      have hlen : (CompStark.Batch.batchRounds S.instances common proof zeta).length ≤
          S.inputRounds := by
        have hpl : (prepRounds S proof zeta common).length ≤
            if S.hasPreprocessed then 1 else 0 := by
          rw [prepRounds]
          cases hc : common.preprocessed with
          | none => exact Nat.zero_le _
          | some root =>
            have hhas : S.hasPreprocessed = true := by
              rw [hc] at hprep
              rw [hasPreprocessed, List.ofFn_eq_map, List.any_map]
              rw [Iop.Batch.Setup.instances, List.ofFn_eq_map, List.any_map] at hprep
              exact hprep.symm
            simp only [hhas, ↓reduceIte, List.length_cons, List.length_nil, le_refl]
        have hrl : (permRounds S proof zeta).length ≤ if S.hasLookups then 1 else 0 := by
          rw [permRounds, hasLookups, ← hperm]
          cases proof.permutationCommit <;> rfl
        rw [batchRounds_cases, inputRounds]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [hA]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_left
        (Nat.mul_le_mul_right _ (Nat.add_le_add_right hlen _)) 1)) _
  refine costs_free_bind (costs_observeList _) fun _ _ ↦ costs_free_bind (costs_observeExts _)
    fun _ _ ↦ costs_free_bind (costs_observeList _) fun _ _ ↦
    costs_free_bind (costs_observeList _) fun _ _ ↦ costs_free_bind (costs_observeList _)
    fun _ _ ↦ costs_bind_le (b := Challenge.d EF + 1 + Challenge.d EF + V) hlp (fun _ _ ↦
    costs_bind_le (b := 1 + Challenge.d EF + V) costs_sampleExt (fun alpha _ ↦
      costs_free_bind (costs_observeList _) fun _ _ ↦ costs_bind_le (b := Challenge.d EF + V)
      (costs_checkWitness _ _) (fun _ _ ↦ costs_ensure_bind fun _ ↦ costs_bind_le (b := V)
        costs_sampleExt (fun zeta _ ↦ costs_ensure_bind fun _ ↦ costs_bind_le (a := V) (b := 0)
          (hpcs zeta) (fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial) le_rfl) le_rfl)
      (by omega)) (by omega)) ?_
  simp only [V, c, G, verifierCalls, openingQueries]
  exact le_of_eq (by ring)

/-- A node of the batch setup's tree at level `l` costs at most `4 · 2 ^ l - 3` calls: a hash per
leaf, a compression per node, and a hash and a compression where a node injects. -/
theorem isTotalQueryBound_injNodeWith {K : Nat} (ms : List (Merkle.Matrix F)) (k : Nat) :
    ∀ l i, IsTotalQueryBound (CompStark.Batch.injNodeWith (ideal F K) ms k l i) (4 * 2 ^ l - 3)
  | 0, i => isTotalQueryBound_query _
  | l + 1, i => by
    have ih := isTotalQueryBound_injNodeWith (K := K) ms k l
    have hp := Nat.one_le_two_pow (n := l)
    rw [CompStark.Batch.injNodeWith]
    refine (isTotalQueryBound_bind (ih _) fun _ ↦ isTotalQueryBound_bind (ih _) fun _ ↦
      isTotalQueryBound_bind (n₂ := 2) (isTotalQueryBound_query _) fun _ ↦ ?_).mono ?_
    · split
      · refine isTotalQueryBound_bind (n₁ := 1) (n₂ := 1) ?_ fun _ ↦ ?_
        · exact isTotalQueryBound_query _
        · exact isTotalQueryBound_query _
      · trivial
    · rw [Nat.pow_succ]
      omega

/-- **The batch setup's oracle calls.** -/
theorem isTotalQueryBound_setupRo : IsTotalQueryBound S.setupRo S.setupQueries := by
  unfold setupRo CompStark.Batch.commonWith setupQueries
  split
  · trivial
  · rename_i hne
    have hhas : S.hasPreprocessed = true := by
      rw [List.isEmpty_iff] at hne
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
      obtain ⟨I, hI, hf⟩ := List.mem_filterMap.mp hx
      split at hf
      · simp only [reduceCtorEq] at hf
      · rename_i hpw
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (show _ ∈ List.ofFn _ from hI)
        exact List.any_eq_true.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩,
          decide_eq_true (Nat.pos_of_ne_zero hpw)⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true hhas)]
    refine (isTotalQueryBound_bind (isTotalQueryBound_injNodeWith _ _ _ 0)
      fun _ ↦ Merkle.isTotalQueryBound_pure _).mono (by omega)

end CompStark.Iop.Batch.Setup
