/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BatchParse
public import CompStark.Ni.BcsChallenges

/-! # The batch run's challenges are the oracle's answers

As for the STARK (`Ni/BcsChallenges.lean`): on the ideal primitives of an answer table, the
challenges of the batch verifier's run (`alphaOfB`, `zetaOfB`, `batchOfB`, `commitReplayB`,
`powSampleOfB`, `querySampleOfB`) are read off the answers to the duplex calls of the proof's
schedule `inputsB` (`challengesB_idealOf`).
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.RandomOracle OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {K : Nat}
  (answer : (q : Query F) → Answer K q)

section Rounds
variable (S : Iop.Batch.Setup EF) (common : CompStark.Batch.Common F)
  (proof : CompStark.Batch.BatchProof F EF) (pis : List (List F))

theorem stateAlphaB_idealOf :
    stateAlphaB (idealOf answer) S.params S.instances common proof pis =
      ⟨capAt answer (inputsB S common pis proof) 0, (inputsB S common pis proof).getD 0 [],
        []⟩ := by
  unfold stateAlphaB
  rw [show (idealOf answer).init = ⟨initCap, [], []⟩ from rfl, obsExts_eq]
  simp only [obsList_idealOf_mk, List.nil_append]
  simp only [inputsB, prepDigest, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    Option.getD_some]
  rfl

theorem alphaB_idealOf (hK : Challenge.d EF ≤ K) :
    Challenge.toSpec (alphaOfB (idealOf answer) S.params S.instances common proof pis) =
      extAt (answer (keyAt answer (inputsB S common pis proof) 0)).2 0 ∧
    (smpExt (EF := EF) (idealOf answer)
      (stateAlphaB (idealOf answer) S.params S.instances common proof pis)).2 =
      ⟨capAt answer (inputsB S common pis proof) 1, [],
        (answer (keyAt answer (inputsB S common pis proof) 0)).2.toList.drop
          (Challenge.d EF)⟩ := by
  rw [alphaOfB, stateAlphaB_idealOf answer S]
  exact smpExt_idealOf_nil answer hK _ _

theorem zetaB_idealOf (hK : Challenge.d EF + 1 ≤ K) :
    Challenge.toSpec (zetaOfB (idealOf answer) S.params S.instances common proof pis) =
      extAt (answer (keyAt answer (inputsB S common pis proof) 1)).2
        (challengeOffset S.params.oodPowBits) ∧
    ∃ l, (smpExt (EF := EF) (idealOf answer) (oodCheckB (EF := EF) (idealOf answer) S.params
      S.instances common proof pis).2).2 =
        ⟨capAt answer (inputsB S common pis proof) 2, [], l⟩ := by
  have hst : obsList (idealOf answer) (smpExt (EF := EF) (idealOf answer)
      (stateAlphaB (idealOf answer) S.params S.instances common proof pis)).2
        proof.quotientCommit.toList =
      ⟨capAt answer (inputsB S common pis proof) 1, proof.quotientCommit.toList, []⟩ := by
    rw [(alphaB_idealOf answer S common proof pis (by omega)).2,
      obsList_idealOf_ne answer _ _ (digest_toList_ne_nil _)]
    rfl
  have h := grindRound_idealOf (EF := EF) answer hK (inputsB S common pis proof) 1
    proof.quotientCommit.toList S.params.oodPowBits proof.oodWitness (by
      simp only [inputsB, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.getD_some])
  rw [← hst] at h
  exact h

theorem batchB_idealOf (hK : Challenge.d EF + 1 ≤ K) :
    Challenge.toSpec (batchOfB (idealOf answer) S.params S.instances common proof pis) =
      extAt (answer (keyAt answer (inputsB S common pis proof) 2)).2
        (challengeOffset S.params.batchPowBits) ∧
    ∃ l, stateFriB (idealOf answer) S.params S.instances common proof pis =
      ⟨capAt answer (inputsB S common pis proof) 3, [], l⟩ := by
  obtain ⟨-, l, hl⟩ := zetaB_idealOf answer S common proof pis hK
  set zeta := zetaOfB (idealOf answer) S.params S.instances common proof pis
  have hst : pcsState (idealOf answer) S.params
      (CompStark.Batch.batchRounds S.instances common proof zeta)
      (smpExt (EF := EF) (idealOf answer) (oodCheckB (EF := EF) (idealOf answer) S.params
        S.instances common proof pis).2).2 =
      ⟨capAt answer (inputsB S common pis proof) 2, DomainSeparator.pcsSeed F EF
        (claimCounts (CompStark.Batch.batchRounds S.instances common proof 0))
        S.params.batchPowBits ++
        coeffs (roundValues (CompStark.Batch.batchRounds S.instances common proof 0)), []⟩ := by
    rw [hl, pcsState, obsOpened_eq, claimCounts_batchRounds _ _ _ zeta 0,
      roundValues_batchRounds _ _ _ zeta 0,
      obsList_idealOf_ne answer _ _ (pcsSeed_ne_nil _ _), obsList_idealOf answer _ rfl]
    rfl
  have h := grindRound_idealOf (EF := EF) answer hK (inputsB S common pis proof) 2
    (DomainSeparator.pcsSeed F EF
      (claimCounts (CompStark.Batch.batchRounds S.instances common proof 0))
      S.params.batchPowBits ++
      coeffs (roundValues (CompStark.Batch.batchRounds S.instances common proof 0)))
    S.params.batchPowBits proof.fri.batchWitness (by
      simp only [inputsB, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.getD_some])
  rw [← hst] at h
  exact h

/-- **The batch run's challenges are the oracle's answers.** On the ideal primitives of an answer
table, with streams long enough for the query round, on a proof with a final polynomial: `α` is
the first `d` samples of round `0`; `ζ`, the batching challenge and `β_i` are read at the grinding
offsets of rounds `1`, `2` and `3 + i`; and the query round's grinding sample and query samples
are its samples from `0` and from the grinding offset. -/
theorem challengesB_idealOf (hK : S.params.numQueries + Challenge.d EF + 1 ≤ K)
    (hfp : proof.fri.finalPoly.toList ≠ []) :
    let u := fun j ↦ (answer (keyAt answer (inputsB S common pis proof) j)).2
    let n := (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length
    Challenge.toSpec (alphaOfB (idealOf answer) S.params S.instances common proof pis) =
        extAt (u 0) 0 ∧
      Challenge.toSpec (zetaOfB (idealOf answer) S.params S.instances common proof pis) =
        extAt (u 1) (challengeOffset S.params.oodPowBits) ∧
      Challenge.toSpec (batchOfB (idealOf answer) S.params S.instances common proof pis) =
        extAt (u 2) (challengeOffset S.params.batchPowBits) ∧
      (commitReplayB (idealOf answer) S common proof pis).1.length = n ∧
      (∀ i < n, Challenge.toSpec ((commitReplayB (idealOf answer) S common proof pis).1.getD i 0) =
        extAt (u (3 + i)) (challengeOffset S.params.commitPowBits)) ∧
      (S.params.queryPowBits ≠ 0 → powSampleOfB (idealOf answer) S common proof pis =
        ((u (3 + n)).toList.getD 0 0)) ∧
      ∀ j < S.params.numQueries, querySampleOfB (idealOf answer) S common proof pis j =
        ((u (3 + n)).toList.getD (challengeOffset S.params.queryPowBits + j) 0) := by
  intro u n
  obtain ⟨hb1, l₀, hl₀⟩ := batchB_idealOf answer S common proof pis (by omega)
  have hstart : friStartB (idealOf answer) S common proof pis =
      ⟨capAt answer (inputsB S common pis proof) 3, friSeedB S, []⟩ := by
    rw [friStartB, hl₀, obsList_idealOf_ne answer _ _ (friSeed_ne_nil _ _ _ _ _ _ _ _)]
    rfl
  obtain ⟨hc1, hc2, l, hl⟩ := commitReplay_idealOf (EF := EF) answer S.params (by omega)
    (inputsB S common pis proof) (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)
    3 (friSeedB S) [] (fun i hi ↦ inputsB_getD_fold S common pis proof i hi)
  rw [← hstart] at hc1 hc2 hl
  obtain ⟨hq1, hq2⟩ := queryRound_idealOf answer S.params proof.fri (by omega)
    (inputsB S common pis proof) (3 + n) _ l hfp (inputsB_getD_last S common pis proof)
  have hqs : queryStateB (idealOf answer) S common proof pis =
      obsExts (idealOf answer) ⟨capAt answer (inputsB S common pis proof) (3 + n),
        seedAt (friSeedB S) n, l⟩ proof.fri.finalPoly.toList := by
    rw [queryStateB, commitReplayB, hl]
  refine ⟨(alphaB_idealOf answer S common proof pis (by omega)).1,
    (zetaB_idealOf answer S common proof pis (by omega)).1, hb1, hc1, hc2, fun hb ↦ ?_,
    fun j hj ↦ ?_⟩
  · rw [powSampleOfB, ite_eq_right hb, hqs, hq1 hb]
  · rw [querySampleOfB, hqs, hq2 j hj]

end Rounds

end CompStark.Ni
