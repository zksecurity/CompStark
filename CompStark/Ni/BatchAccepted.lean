/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BatchChallenges
public import CompStark.Ni.Accepted

/-! # The grinding of accepted batch runs

As for the STARK (`Ni/Accepted.lean`): every grinding check of an accepted batch run passes, so
on an answer table the first sample of the out-of-domain, batching and fold rounds' answers has
its grinding bits vanishing (`oodWitnessB_idealOf`, `batchWitnessB_idealOf`,
`commitWitnessB_idealOf`).
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.RandomOracle OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {K : Nat}
  (answer : (q : Query F) → Answer K q)

section Rounds
variable (S : Iop.Batch.Setup EF) (common : CompStark.Batch.Common F)
  (proof : CompStark.Batch.BatchProof F EF) (pis : List (List F))

/-- **The out-of-domain round's grinding.** -/
theorem oodWitnessB_idealOf (hK : Challenge.d EF ≤ K)
    (hood : (oodCheckB (EF := EF) (idealOf answer) S.params S.instances common proof pis).1 =
      true)
    (hbits : S.params.oodPowBits ≠ 0) :
    CompPoly.CanonicalNat.toNat ((answer (keyAt answer (inputsB S common pis proof)
      1)).2.toList.getD 0 0) % 2 ^ S.params.oodPowBits = 0 := by
  have hst : obsList (idealOf answer) (smpExt (EF := EF) (idealOf answer)
      (stateAlphaB (idealOf answer) S.params S.instances common proof pis)).2
        proof.quotientCommit.toList =
      ⟨capAt answer (inputsB S common pis proof) 1, proof.quotientCommit.toList, []⟩ := by
    rw [(alphaB_idealOf answer S common proof pis hK).2,
      obsList_idealOf_ne answer _ _ (digest_toList_ne_nil _)]
    rfl
  rw [oodCheckB, hst] at hood
  exact grindWitness_idealOf answer _ 1 _ _ _ (by
    simp only [inputsB, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]) hbits hood

/-- **The batching round's grinding.** -/
theorem batchWitnessB_idealOf (hK : Challenge.d EF + 1 ≤ K)
    (hbc : (batchCheckB (idealOf answer) S.params S.instances common proof pis).1 = true)
    (hbits : S.params.batchPowBits ≠ 0) :
    CompPoly.CanonicalNat.toNat ((answer (keyAt answer (inputsB S common pis proof)
      2)).2.toList.getD 0 0) % 2 ^ S.params.batchPowBits = 0 := by
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
  rw [batchCheckB, hst] at hbc
  exact grindWitness_idealOf answer _ 2 _ _ _ (by
    simp only [inputsB, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]) hbits hbc

/-- **The fold rounds' grinding.** If FRI accepts after the batching challenge on the ideal
primitives of an answer table, on rounds of the batch's heights, then with grinding every fold
round's answer has a first sample with `commitPowBits` vanishing low bits. -/
theorem commitWitnessB_idealOf (hK : S.params.numQueries + Challenge.d EF + 1 ≤ K)
    (rounds : List (Round F EF))
    (hheights : descHeights (matHeights S.params rounds) = S.logTop :: S.friHeights)
    (st : Sponge F)
    (hfri : verifyFri (idealOf answer) S.params proof.fri rounds
      (batchOfB (idealOf answer) S.params S.instances common proof pis)
      (stateFriB (idealOf answer) S.params S.instances common proof pis) = .ok ((), st))
    (i : Nat) (hi : i < (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length)
    (hbits : S.params.commitPowBits ≠ 0) :
    CompPoly.CanonicalNat.toNat ((answer (keyAt answer (inputsB S common pis proof)
      (3 + i))).2.toList.getD 0 0) % 2 ^ S.params.commitPowBits = 0 := by
  set H := idealOf answer
  set cws := proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList
  set blocks := inputsB S common pis proof
  unfold verifyFri at hfri
  obtain ⟨-, hfri⟩ := ensure_bind_eq_ok H hfri
  obtain ⟨-, hfri⟩ := ensure_bind_eq_ok H hfri
  change (ensure ((descHeights (matHeights S.params rounds)).headD 0 ≤ twoAdicity F) _ >>= _)
    _ = _ at hfri
  simp only [hheights, List.headD_cons] at hfri
  obtain ⟨-, hfri⟩ := ensure_bind_eq_ok H hfri
  obtain ⟨-, hfri⟩ := ensure_bind_eq_ok H hfri
  obtain ⟨-, hfri⟩ := ensure_bind_eq_ok H hfri
  obtain ⟨-, hfri⟩ := ensure_bind_eq_ok H hfri
  obtain ⟨-, hfri⟩ := ensure_bind_eq_ok H hfri
  obtain ⟨-, hfri⟩ := ensure_bind_eq_ok H hfri
  rw [bind_ok_of H (observeList_eq H _ _)] at hfri
  obtain ⟨-, hfri⟩ := ensure_bind_eq_ok H hfri
  obtain ⟨betas, st1, hloop, -⟩ := bind_eq_ok H hfri
  have hwit := commitLoop_wit H S.params _ (fun _ _ ↦ rfl) cws #[] _ _ hloop i hi
  have hstart : obsList H (stateFriB H S.params S.instances common proof pis)
      (DomainSeparator.friSeed F EF (foldSchedule S.params.maxLogArity
        (S.params.logBlowup + S.params.logFinalPolyLen) S.logTop (S.logTop :: S.friHeights))
        (2 ^ S.params.logFinalPolyLen) S.params.commitPowBits S.params.queryPowBits
        S.params.numQueries S.logTop S.params.logBlowup S.params.maxLogArity) =
      ⟨capAt answer blocks 3, friSeedB S, []⟩ := by
    obtain ⟨-, l₀, hl₀⟩ := batchB_idealOf answer S common proof pis (by omega)
    rw [hl₀]
    exact obsList_idealOf_ne answer _ (friSeedB S) (friSeed_ne_nil _ _ _ _ _ _ _ _)
  have hh' : ((List.map (fun x : Domain F × List (EF × List EF) ↦ x.1.logSize + S.params.logBlowup)
      (List.flatMap (fun x ↦ x.2) rounds)).mergeSort fun a b ↦ decide (b ≤ a)).dedup =
      S.logTop :: S.friHeights := hheights
  simp only [hh', List.headD_cons] at hwit
  rw [hstart] at hwit
  have htake : ∀ j (hj : j < (cws.take i).length), blocks.getD (3 + j) [] =
      seedAt (friSeedB S) j ++ (cws.take i)[j].1.toList ++
        witnessInput S.params.commitPowBits (cws.take i)[j].2 := by
    intro j hj
    rw [List.length_take] at hj
    rw [List.getElem_take]
    exact inputsB_getD_fold S common pis proof j (Nat.lt_of_lt_of_le hj (Nat.min_le_right _ _))
  obtain ⟨-, -, l, hl⟩ :=
    commitReplay_idealOf (EF := EF) answer S.params (by omega) blocks (cws.take i) 3 _ [] htake
  rw [hl, List.length_take, Nat.min_eq_left hi.le] at hwit
  have hblock : blocks.getD (3 + i) [] = seedAt (friSeedB S) i ++ cws[i].1.toList ++
      [cws[i].2] := by
    rw [inputsB_getD_fold S common pis proof i hi]
    simp only [witnessInput, hbits, ↓reduceIte]
    rfl
  rw [obsList_idealOf_ne answer _ _ (digest_toList_ne_nil _)] at hwit
  simp only [chkWit, hbits, ↓reduceIte, smpBits, beq_iff_eq] at hwit
  change CompPoly.CanonicalNat.toNat (H.sample ⟨capAt answer blocks (3 + i),
    seedAt (friSeedB S) i ++ cws[i].1.toList ++ [cws[i].2], []⟩).1 %
      2 ^ S.params.commitPowBits = 0 at hwit
  rw [sample_idealOf_nil, ← hblock] at hwit
  rw [← List.headD_eq_getD]
  exact hwit

end Rounds

end CompStark.Ni
