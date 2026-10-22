/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BatchParse
public import CompStark.Ni.BcsChallenges

/-! # The batch run's challenges are the oracle's answers

As for the STARK (`Ni/BcsChallenges.lean`): on the ideal primitives of an answer table, the
challenges of the batch verifier's run (`lookupRunB`, `alphaOfB`, `zetaOfB`, `batchOfB`,
`commitReplayB`, `powSampleOfB`, `querySampleOfB`) are read off the answers to the duplex calls of
the proof's schedule `inputsB` (`challengesB_idealOf`).
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.RandomOracle OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {K : Nat}
  (answer : (q : Query F) → Answer K q)

/-- A round with grinding and two extension samples: after observing `input`, check the grinding
witness and sample two extension elements, the round's answer at the grinding offset and `d`
samples further. -/
theorem grindPair_idealOf (hK : 2 * Challenge.d EF + 1 ≤ K) (blocks : List (List F)) (r : Nat)
    (input : List F) (bits : Nat) (w : F)
    (hr : blocks.getD r [] = input ++ witnessInput bits w) :
    let a := smpExt (EF := EF) (idealOf answer)
      (chkWit (idealOf answer) bits w ⟨capAt answer blocks r, input, []⟩).2
    let b := smpExt (EF := EF) (idealOf answer) a.2
    Challenge.toSpec a.1 = extAt (answer (keyAt answer blocks r)).2 (challengeOffset bits) ∧
      Challenge.toSpec b.1 =
        extAt (answer (keyAt answer blocks r)).2 (challengeOffset bits + Challenge.d EF) ∧
      ∃ l, b.2 = ⟨capAt answer blocks (r + 1), [], l⟩ := by
  intro a b
  set u := (answer (keyAt answer blocks r)).2
  have ha : Challenge.toSpec a.1 = extAt u (challengeOffset bits) ∧
      a.2 = ⟨capAt answer blocks (r + 1), [],
        u.toList.drop (challengeOffset bits + Challenge.d EF)⟩ := by
    by_cases hb : bits = 0
    · simp only [witnessInput, hb, ↓reduceIte, List.append_nil] at hr
      have h := smpExt_idealOf_nil (EF := EF) answer (by omega) (capAt answer blocks r)
        (blocks.getD r [])
      simp only [a, chkWit, hb, ↓reduceIte, challengeOffset, Nat.zero_add]
      rw [← hr]
      exact h
    · simp only [witnessInput, hb, ↓reduceIte] at hr
      have hst : (chkWit (idealOf answer) bits w ⟨capAt answer blocks r, input, []⟩).2 =
          ⟨capAt answer blocks (r + 1), [], u.toList.drop 1⟩ := by
        rw [chkWit, ite_eq_right hb, List.drop_one]
        show ((idealOf answer).sample ⟨capAt answer blocks r, input ++ [w], []⟩).2 = _
        rw [sample_idealOf_nil, ← hr]
        rfl
      rw [show challengeOffset bits = 1 by simp only [challengeOffset, hb, ↓reduceIte]]
      rw [show a = smpExt (idealOf answer) _ from rfl, hst,
        smpExt_idealOf_pop answer _ _ _ (by rw [List.length_drop, Vector.length_toList]; omega),
        List.drop_drop]
      exact ⟨toSpec_ofCoeffs_drop _ _, rfl⟩
  have hb : b = ((Challenge.ofCoeffs ((u.toList.drop (challengeOffset bits + Challenge.d EF)).take
      (Challenge.d EF)) : EF), ⟨capAt answer blocks (r + 1), [],
        u.toList.drop (challengeOffset bits + Challenge.d EF + Challenge.d EF)⟩) := by
    rw [show b = smpExt (idealOf answer) a.2 from rfl, ha.2]
    rw [smpExt_idealOf_pop answer _ _ _ (by
      rw [List.length_drop, Vector.length_toList]
      unfold challengeOffset; split <;> omega), List.drop_drop]
  rw [hb]
  exact ⟨ha.1, toSpec_ofCoeffs_drop _ _, _, rfl⟩

section Rounds
variable (S : Iop.Batch.Setup EF) (common : CompStark.Batch.Common F)
  (proof : CompStark.Batch.BatchProof F EF) (pis : List (List F))

theorem stateLookupB_idealOf :
    stateLookupB (idealOf answer) S.params S.instances common proof pis =
      ⟨initCap, headB S common pis proof, []⟩ := by
  unfold stateLookupB
  rw [show (idealOf answer).init = ⟨initCap, [], []⟩ from rfl]
  simp only [obsExts_eq, obsList_idealOf_mk, List.nil_append, headB, prepDigest]

/-- With lookups, the lookup challenges are read off the lookup round's answer: `α_L` at the
grinding offset and `β_L` `d` samples further. -/
theorem lookupB_idealOf (hK : 2 * Challenge.d EF + 1 ≤ K) (hl : S.hasLookups = true) :
    Challenge.toSpec (lookupRunB (idealOf answer) S.params S.instances common proof pis).1 =
      extAt (answer (keyAt answer (inputsB S common pis proof) 0)).2
        (challengeOffset S.params.lookupPowBits) ∧
    Challenge.toSpec (lookupRunB (idealOf answer) S.params S.instances common proof pis).2 =
      extAt (answer (keyAt answer (inputsB S common pis proof) 0)).2
        (challengeOffset S.params.lookupPowBits + Challenge.d EF) ∧
    ∃ l, (lookupRun (idealOf answer) S.params S.instances proof
      (stateLookupB (idealOf answer) S.params S.instances common proof pis)).2 =
        ⟨capAt answer (inputsB S common pis proof) 1, [], l⟩ := by
  have h := grindPair_idealOf (EF := EF) answer hK (inputsB S common pis proof) 0
    (headB S common pis proof) S.params.lookupPowBits (proof.lookupWitness.getD 0)
    (inputsB_getD_zero S common pis proof hl)
  have hl' : CompStark.Batch.hasLookups S.instances = true := hl
  rw [lookupRunB, lookupRun, stateLookupB_idealOf, ite_eq_left_of_eq_true _ _ (eq_true hl')]
  exact h

theorem stateAlphaB_idealOf (hK : 2 * Challenge.d EF + 1 ≤ K)
    (hperm : proof.permutationCommit.isSome = S.hasLookups) :
    stateAlphaB (idealOf answer) S.params S.instances common proof pis =
      ⟨capAt answer (inputsB S common pis proof) (lookupRounds S),
        (inputsB S common pis proof).getD (lookupRounds S) [], []⟩ := by
  unfold stateAlphaB
  rw [inputsB_getD_alpha]
  cases hl : S.hasLookups with
  | false =>
    have hl' : CompStark.Batch.hasLookups S.instances = false := hl
    rw [lookupRun, ite_eq_right_of_eq_false _ _ (eq_false (by rw [hl']; decide)),
      stateLookupB_idealOf]
    simp only [obsExts_eq, obsList_idealOf_mk, Bool.false_eq_true, ↓reduceIte, permDigest,
      lookupRounds, hl]
    rfl
  | true =>
    obtain ⟨-, -, l, hst⟩ := lookupB_idealOf answer S common proof pis hK hl
    obtain ⟨root, hroot⟩ := Option.isSome_iff_exists.mp (hperm.trans hl)
    rw [hst]
    simp only [permDigest, hroot, Option.map_some, Option.getD_some, obsExts_eq, ↓reduceIte,
      lookupRounds, hl]
    rw [obsList_idealOf_ne answer _ _ (digest_toList_ne_nil _), obsList_idealOf_mk]

theorem alphaB_idealOf (hK : 2 * Challenge.d EF + 1 ≤ K)
    (hperm : proof.permutationCommit.isSome = S.hasLookups) :
    Challenge.toSpec (alphaOfB (idealOf answer) S.params S.instances common proof pis) =
      extAt (answer (keyAt answer (inputsB S common pis proof) (lookupRounds S))).2 0 ∧
    (smpExt (EF := EF) (idealOf answer)
      (stateAlphaB (idealOf answer) S.params S.instances common proof pis)).2 =
      ⟨capAt answer (inputsB S common pis proof) (lookupRounds S + 1), [],
        (answer (keyAt answer (inputsB S common pis proof) (lookupRounds S))).2.toList.drop
          (Challenge.d EF)⟩ := by
  rw [alphaOfB, stateAlphaB_idealOf answer S common proof pis hK hperm]
  exact smpExt_idealOf_nil answer (by omega) _ _

theorem zetaB_idealOf (hK : 2 * Challenge.d EF + 1 ≤ K)
    (hperm : proof.permutationCommit.isSome = S.hasLookups) :
    Challenge.toSpec (zetaOfB (idealOf answer) S.params S.instances common proof pis) =
      extAt (answer (keyAt answer (inputsB S common pis proof) (lookupRounds S + 1))).2
        (challengeOffset S.params.oodPowBits) ∧
    ∃ l, (smpExt (EF := EF) (idealOf answer) (oodCheckB (EF := EF) (idealOf answer) S.params
      S.instances common proof pis).2).2 =
        ⟨capAt answer (inputsB S common pis proof) (lookupRounds S + 2), [], l⟩ := by
  have hst : obsList (idealOf answer) (smpExt (EF := EF) (idealOf answer)
      (stateAlphaB (idealOf answer) S.params S.instances common proof pis)).2
        proof.quotientCommit.toList =
      ⟨capAt answer (inputsB S common pis proof) (lookupRounds S + 1),
        proof.quotientCommit.toList, []⟩ := by
    rw [(alphaB_idealOf answer S common proof pis hK hperm).2,
      obsList_idealOf_ne answer _ _ (digest_toList_ne_nil _)]
    rfl
  have h := grindRound_idealOf (EF := EF) answer (by omega) (inputsB S common pis proof)
    (lookupRounds S + 1) proof.quotientCommit.toList S.params.oodPowBits proof.oodWitness
    (inputsB_getD_ood S common pis proof)
  rw [← hst] at h
  exact h

theorem batchB_idealOf (hK : 2 * Challenge.d EF + 1 ≤ K)
    (hperm : proof.permutationCommit.isSome = S.hasLookups) :
    Challenge.toSpec (batchOfB (idealOf answer) S.params S.instances common proof pis) =
      extAt (answer (keyAt answer (inputsB S common pis proof) (lookupRounds S + 2))).2
        (challengeOffset S.params.batchPowBits) ∧
    ∃ l, stateFriB (idealOf answer) S.params S.instances common proof pis =
      ⟨capAt answer (inputsB S common pis proof) (lookupRounds S + 3), [], l⟩ := by
  obtain ⟨-, l, hl⟩ := zetaB_idealOf answer S common proof pis hK hperm
  set zeta := zetaOfB (idealOf answer) S.params S.instances common proof pis
  have hst : pcsState (idealOf answer) S.params
      (CompStark.Batch.batchRounds S.instances common proof zeta)
      (smpExt (EF := EF) (idealOf answer) (oodCheckB (EF := EF) (idealOf answer) S.params
        S.instances common proof pis).2).2 =
      ⟨capAt answer (inputsB S common pis proof) (lookupRounds S + 2), DomainSeparator.pcsSeed F EF
        (claimCounts (CompStark.Batch.batchRounds S.instances common proof 0))
        S.params.batchPowBits ++
        coeffs (roundValues (CompStark.Batch.batchRounds S.instances common proof 0)), []⟩ := by
    rw [hl, pcsState, obsOpened_eq, claimCounts_batchRounds _ _ _ zeta 0,
      roundValues_batchRounds _ _ _ zeta 0,
      obsList_idealOf_ne answer _ _ (pcsSeed_ne_nil _ _), obsList_idealOf answer _ rfl]
    rfl
  have h := grindRound_idealOf (EF := EF) answer (by omega) (inputsB S common pis proof)
    (lookupRounds S + 2)
    (DomainSeparator.pcsSeed F EF
      (claimCounts (CompStark.Batch.batchRounds S.instances common proof 0))
      S.params.batchPowBits ++
      coeffs (roundValues (CompStark.Batch.batchRounds S.instances common proof 0)))
    S.params.batchPowBits proof.fri.batchWitness (by rw [inputsB_getD_pcs, List.append_assoc])
  rw [← hst] at h
  exact h

/-- **The batch run's challenges are the oracle's answers.** On the ideal primitives of an answer
table, with streams long enough for every round, on a proof with a final polynomial and a
permutation commitment exactly with lookups, after the `L` lookup rounds (`lookupRounds`): with
lookups `(α_L, β_L)` are read at the grinding offset of round `0`; `α` is the first `d` samples of
round `L`; `ζ`, the batching challenge and `β_i` are read at the grinding offsets of rounds
`L + 1`, `L + 2` and `L + 3 + i`; and the query round's grinding sample and query samples are its
samples from `0` and from the grinding offset. -/
theorem challengesB_idealOf (hK : S.params.numQueries + 2 * Challenge.d EF + 1 ≤ K)
    (hfp : proof.fri.finalPoly.toList ≠ [])
    (hperm : proof.permutationCommit.isSome = S.hasLookups) :
    let u := fun j ↦ (answer (keyAt answer (inputsB S common pis proof) j)).2
    let n := (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length
    let L := lookupRounds S
    (S.hasLookups = true →
      Challenge.toSpec (lookupRunB (idealOf answer) S.params S.instances common proof pis).1 =
        extAt (u 0) (challengeOffset S.params.lookupPowBits) ∧
      Challenge.toSpec (lookupRunB (idealOf answer) S.params S.instances common proof pis).2 =
        extAt (u 0) (challengeOffset S.params.lookupPowBits + Challenge.d EF)) ∧
    Challenge.toSpec (alphaOfB (idealOf answer) S.params S.instances common proof pis) =
        extAt (u L) 0 ∧
      Challenge.toSpec (zetaOfB (idealOf answer) S.params S.instances common proof pis) =
        extAt (u (L + 1)) (challengeOffset S.params.oodPowBits) ∧
      Challenge.toSpec (batchOfB (idealOf answer) S.params S.instances common proof pis) =
        extAt (u (L + 2)) (challengeOffset S.params.batchPowBits) ∧
      (commitReplayB (idealOf answer) S common proof pis).1.length = n ∧
      (∀ i < n, Challenge.toSpec ((commitReplayB (idealOf answer) S common proof pis).1.getD i 0) =
        extAt (u (L + 3 + i)) (challengeOffset S.params.commitPowBits)) ∧
      (S.params.queryPowBits ≠ 0 → powSampleOfB (idealOf answer) S common proof pis =
        ((u (L + 3 + n)).toList.getD 0 0)) ∧
      ∀ j < S.params.numQueries, querySampleOfB (idealOf answer) S common proof pis j =
        ((u (L + 3 + n)).toList.getD (challengeOffset S.params.queryPowBits + j) 0) := by
  intro u n L
  obtain ⟨hb1, l₀, hl₀⟩ := batchB_idealOf answer S common proof pis (by omega) hperm
  have hstart : friStartB (idealOf answer) S common proof pis =
      ⟨capAt answer (inputsB S common pis proof) (L + 3), friSeedB S, []⟩ := by
    rw [friStartB, hl₀, obsList_idealOf_ne answer _ _ (friSeed_ne_nil _ _ _ _ _ _ _ _)]
    rfl
  obtain ⟨hc1, hc2, l, hl⟩ := commitReplay_idealOf (EF := EF) answer S.params (by omega)
    (inputsB S common pis proof) (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)
    (L + 3) (friSeedB S) [] (fun i hi ↦ inputsB_getD_fold S common pis proof i hi)
  rw [← hstart] at hc1 hc2 hl
  obtain ⟨hq1, hq2⟩ := queryRound_idealOf answer S.params proof.fri (by omega)
    (inputsB S common pis proof) (L + 3 + n) _ l hfp (inputsB_getD_last S common pis proof)
  have hqs : queryStateB (idealOf answer) S common proof pis =
      obsExts (idealOf answer) ⟨capAt answer (inputsB S common pis proof) (L + 3 + n),
        seedAt (friSeedB S) n, l⟩ proof.fri.finalPoly.toList := by
    rw [queryStateB, commitReplayB, hl]
  refine ⟨fun hl ↦ ?_, (alphaB_idealOf answer S common proof pis (by omega) hperm).1,
    (zetaB_idealOf answer S common proof pis (by omega) hperm).1, hb1, hc1, hc2, fun hb ↦ ?_,
    fun j hj ↦ ?_⟩
  · obtain ⟨h1, h2, -⟩ := lookupB_idealOf answer S common proof pis (by omega) hl
    exact ⟨h1, h2⟩
  · rw [powSampleOfB, ite_eq_right hb, hqs, hq1 hb]
  · rw [querySampleOfB, hqs, hq2 j hj]

end Rounds

end CompStark.Ni
