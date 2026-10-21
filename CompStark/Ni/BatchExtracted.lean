/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BatchRounds
public import CompStark.Ni.Extracted

/-! # The extracted batch transcript is the prefix transcript of the schedule

* Congruences: the prefix transcript's fields depend only on the inputs and answers of their
  rounds and on what the cache extracts under the observed digests (`SameUnder`, `SameUnderM`
  for the trees of mixed heights).
* `extractB_eq_prefixTranscriptB`: on an accepted batch proof, the transcript `bcsB` extracts from
  a run on an answer table is the prefix transcript of the proof's schedule (`inputsB`) with the
  answers to its duplex calls.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop CompStark.RandomOracle
open Polynomial OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- `cache` and `cache'` extract the same rows of every height under `root`. -/
def SameUnderM (cache cache' : Merkle.Cache F (Digest F)) (root : Digest F) : Prop :=
  ∀ inj K t i, Merkle.extractGroup cache inj K t i root = Merkle.extractGroup cache' inj K t i root

theorem matColumn_congr {cache cache' : Merkle.Cache F (Digest F)} {root : Digest F}
    (h : SameUnderM cache cache' root) :
    Merkle.matColumn cache root = Merkle.matColumn cache' root := by
  funext K hs ws t j m r
  simp only [Merkle.matColumn]
  rw [h]

/-! ### Accepted proofs -/

section Accepted
variable (S : Iop.Batch.Setup EF) (H : Primitives F Id) (common : CompStark.Batch.Common F)
  (proof : CompStark.Batch.BatchProof F EF) (pis : List (List F))

/-- **The shape of an accepted batch proof.** One opened value set per instance, each in its
AIR's shape, the preprocessed commitment exactly when some instance has preprocessed columns, a
commitment and grinding witness per fold, and a final polynomial of its length. -/
theorem shape_of_verifyBatchWith
    (h : CompStark.Batch.verifyBatchWith H S.params S.instances common proof pis = .ok ()) :
    proof.opened.size = S.k ∧
      (∀ i : Fin S.k, CompStark.Batch.openedShapeOk (S.air i)
        (proof.opened.toList.getD i noOpenings) (S.logN i) = true) ∧
      common.preprocessed.isSome = S.instances.any (0 < ·.air.preprocessedWidth) ∧
      proof.fri.commits.size = (friAritiesB S).length ∧
      proof.fri.commitWitnesses.size = (friAritiesB S).length ∧
      proof.fri.finalPoly.size = 2 ^ S.params.logFinalPolyLen := by
  obtain ⟨hsize, -, -, -, -, hshapeZ, hprepS, -, -, -, ⟨st, hfriOk⟩, -⟩ :=
    verifyBatchWith_ok H S.params S.instances common proof pis h
  rw [length_instances] at hsize
  have hos : proof.opened.toList.length = S.k := by rw [Array.length_toList, hsize]
  have hD := descHeights_batchRounds S common proof
    (zetaOfB H S.params S.instances common proof pis) hsize
  have hok := verifyFri_okR H S.params proof.fri _ _ _ _ hfriOk
  dsimp only at hok
  rw [hD, List.headD_cons] at hok
  obtain ⟨-, -, -, -, -, hcs, hcw, hfp, -⟩ := hok
  exact ⟨hsize, fun i ↦ hshapeZ _ (zip_instances S _ hos ▸
    List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩), hprepS, hcs, hcw, hfp⟩

theorem length_zip_commitsB
    (h : CompStark.Batch.verifyBatchWith H S.params S.instances common proof pis = .ok ()) :
    (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length =
      (friAritiesB S).length := by
  obtain ⟨-, -, -, hcs, hcw, -⟩ := shape_of_verifyBatchWith S H common proof pis h
  rw [List.length_zip, Array.length_toList, Array.length_toList, hcs, hcw, Nat.min_self]

end Accepted

/-! ### Congruences -/

section Congr
variable (S : Iop.Batch.Setup EF) {cache cache' : Merkle.Cache F (Digest F)}
  {block block' : ℕ → List F} {sample sample' : ℕ → Vector F S.streamLen}

theorem prefixTranscriptB_trace (hb : block 0 = block' 0)
    (h : SameUnderM cache cache' (digestAt (block' 0) (mainOffsetB S))) :
    (prefixTranscriptB S cache block sample).trace =
      (prefixTranscriptB S cache' block' sample').trace := by
  funext i c x
  show Merkle.matColumn cache (digestAt (block 0) (mainOffsetB S)) _ _ _ _ _ _ _ =
    Merkle.matColumn cache' (digestAt (block' 0) (mainOffsetB S)) _ _ _ _ _ _ _
  rw [hb, matColumn_congr h]

theorem prefixTranscriptB_quotient (hb : block 1 = block' 1)
    (h : SameUnderM cache cache' (digestAt (block' 1) 0)) :
    (prefixTranscriptB S cache block sample).quotient =
      (prefixTranscriptB S cache' block' sample').quotient := by
  funext i c e x
  show Merkle.matColumn cache (digestAt (block 1) 0) _ _ _ _ _ _ _ =
    Merkle.matColumn cache' (digestAt (block' 1) 0) _ _ _ _ _ _ _
  rw [hb, matColumn_congr h]

theorem prefixTranscriptB_words (f : ℕ) (hb : block (3 + f) = block' (3 + f))
    (h : SameUnder cache cache' (digestAt (block' (3 + f)) (friOffsetB S f))) :
    (prefixTranscriptB S cache block sample).words f =
      (prefixTranscriptB S cache' block' sample').words f := by
  funext m z
  show (if f < (friAritiesB S).length then friWordAt (EF := EF) cache
      (digestAt (block (3 + f)) (friOffsetB S f)) m ((friAritiesB S).getD f 0) z.val else 0) =
    (if f < (friAritiesB S).length then friWordAt (EF := EF) cache'
      (digestAt (block' (3 + f)) (friOffsetB S f)) m ((friAritiesB S).getD f 0) z.val else 0)
  rw [hb, friWordAt_congr h]

end Congr

/-! ### The schedule of an accepted proof -/

section Schedule
variable (S : Iop.Batch.Setup EF) (common : CompStark.Batch.Common F)
  (proof : CompStark.Batch.BatchProof F EF) (pis : List (List F))

theorem inputsB_getD_zero : (inputsB S common pis proof).getD 0 [] =
    CompStark.Batch.batchSeedOf EF S.params S.instances common ++
      coeffs (S.instances.map fun I ↦ (Ext.ofBase (I.logN : F) : EF)) ++ proof.mainCommit.toList ++
      pis.flatten ++ prepDigest common := by
  simp only [inputsB, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some]

theorem inputsB_getD_one : (inputsB S common pis proof).getD 1 [] =
    proof.quotientCommit.toList ++ witnessInput S.params.oodPowBits proof.oodWitness := by
  simp only [inputsB, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some]

theorem inputsB_getD_two : (inputsB S common pis proof).getD 2 [] =
    DomainSeparator.pcsSeed F EF
      (claimCounts (CompStark.Batch.batchRounds S.instances common proof 0))
      S.params.batchPowBits ++
    coeffs (roundValues (CompStark.Batch.batchRounds S.instances common proof 0)) ++
    witnessInput S.params.batchPowBits proof.fri.batchWitness := by
  simp only [inputsB, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some]

theorem length_coeffs_map {α : Type} (l : List α) (f : α → EF) :
    (coeffs (l.map f)).length = Challenge.d EF * l.length := by
  rw [coeffs, List.length_flatMap, List.map_map, List.sum_eq_length_nsmul _ (Challenge.d EF)
    (by
      intro n hn
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hn
      exact Challenge.length_coeffs _), List.length_map, smul_eq_mul, Nat.mul_comm]

/-- The batch's domain separator on a proof with the setup's preprocessed commitment is `S`'s. -/
theorem batchSeedOf_eq
    (hprep : common.preprocessed.isSome = S.instances.any (0 < ·.air.preprocessedWidth)) :
    CompStark.Batch.batchSeedOf EF S.params S.instances common = batchSeedS S := by
  rw [CompStark.Batch.batchSeedOf, batchSeedS, hprep, hasPreprocessed_eq]

theorem mainRoot_eq
    (hprep : common.preprocessed.isSome = S.instances.any (0 < ·.air.preprocessedWidth)) :
    digestAt ((inputsB S common pis proof).getD 0 []) (mainOffsetB S) = proof.mainCommit := by
  rw [inputsB_getD_zero, List.append_assoc _ pis.flatten, batchSeedOf_eq S common hprep]
  have hlen : mainOffsetB S = (batchSeedS S ++
      coeffs (S.instances.map fun I ↦ (Ext.ofBase (I.logN : F) : EF))).length := by
    rw [List.length_append, length_coeffs_map, length_instances, mainOffsetB]
  rw [hlen]
  exact digestAt_append _ _ _

theorem quotientRoot_eqB :
    digestAt ((inputsB S common pis proof).getD 1 []) 0 = proof.quotientCommit := by
  rw [inputsB_getD_one, digestAt_append_zero]

/-- On a proof in the instances' shapes, the decoded openings are the opened values. -/
theorem openings_eqB (hsize : proof.opened.size = S.k)
    (hshape : ∀ i : Fin S.k, CompStark.Batch.openedShapeOk (S.air i)
      (proof.opened.toList.getD i noOpenings) (S.logN i) = true)
    (hprep : common.preprocessed.isSome = S.instances.any (0 < ·.air.preprocessedWidth)) :
    openingsAtB S (((inputsB S common pis proof).getD 2 []).drop (pcsSeedB S).length) =
      fun i ↦ openingsOf (S.instanceSetup i) (proof.opened.toList.getD i noOpenings) := by
  rw [inputsB_getD_two, claimCounts_batchRounds_eq S common proof hsize hshape hprep, ← pcsSeedB,
    List.append_assoc, List.drop_left]
  funext i
  exact openingsAtB_coeffs S common proof hsize hshape hprep 0 _ i

theorem friAritiesB_ne_nil : friAritiesB S ≠ [] := by
  have hf := S.folds S.top
  have hb := (S.valid S.top).blowup
  unfold friAritiesB Iop.Batch.Setup.logTop
  obtain ⟨n, hn⟩ : ∃ n, S.logN S.top + S.params.logBlowup = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
    (by omega)).symm⟩
  rw [hn, foldSchedule, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  exact List.cons_ne_nil _ _

variable (answer : (q : Query F) → Answer S.streamLen q)
variable {common proof pis}

theorem foldRoot_eqB
    (hok : CompStark.Batch.verifyBatchWith (idealOf answer) S.params S.instances common proof pis =
      .ok ()) (i : ℕ) (hi : i < (friAritiesB S).length) :
    digestAt ((inputsB S common pis proof).getD (3 + i) []) (friOffsetB S i) =
      proof.fri.commits.toList.getD i 0 := by
  have hz := length_zip_commitsB S (idealOf answer) common proof pis hok
  rw [inputsB_getD_fold _ _ _ _ i (by omega)]
  have hpre : friOffsetB S i = (seedAt (friSeedB S) i).length := by
    simp only [friOffsetB, seedAt]
    split <;> rfl
  have hc : i < proof.fri.commits.toList.length := by
    obtain ⟨-, -, -, hcs, -⟩ := shape_of_verifyBatchWith S (idealOf answer) common proof pis hok
    rw [Array.length_toList, hcs]
    exact hi
  rw [hpre, digestAt_append, List.getElem_zip, List.getD_eq_getElem _ _ hc]

theorem finalPoly_eqB
    (hok : CompStark.Batch.verifyBatchWith (idealOf answer) S.params S.instances common proof pis =
      .ok ()) :
    finalPolyAt S.domainSetup ((inputsB S common pis proof).getD (3 + (friAritiesB S).length) []) =
      proof.fri.finalPoly := by
  have hz := length_zip_commitsB S (idealOf answer) common proof pis hok
  obtain ⟨-, -, -, -, -, hfp⟩ := shape_of_verifyBatchWith S (idealOf answer) common proof pis hok
  have hlast := inputsB_getD_last S common pis proof
  rw [hz] at hlast
  have hseed : seedAt (friSeedB S) (friAritiesB S).length = [] := by
    have := List.length_pos_of_ne_nil (friAritiesB_ne_nil S)
    simp only [seedAt, Nat.pos_iff_ne_zero.mp this, ↓reduceIte]
  rw [hlast, hseed, List.nil_append]
  exact finalPolyAt_coeffs S.domainSetup _ _ hfp

/-- Batch transcripts with the same fields are equal. -/
theorem transcript_ext {t t' : Sound.Batch.Transcript S} (h1 : t.trace = t'.trace)
    (h2 : t.alpha = t'.alpha) (h3 : t.quotient = t'.quotient) (h4 : t.zeta = t'.zeta)
    (h5 : t.openings = t'.openings) (h6 : t.batch = t'.batch) (h7 : t.words = t'.words)
    (h8 : t.finalPoly = t'.finalPoly) (h9 : t.betas = t'.betas) : t = t' := by
  cases t
  cases t'
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9
  rfl

/-- **The extracted batch transcript.** On an accepted batch proof, the transcript extracted
from a run on the answers `answer` is the prefix transcript of the proof's schedule with the
answers to its duplex calls. -/
theorem extractB_eq_prefixTranscriptB (cache : Merkle.Cache F (Digest F))
    (hok : CompStark.Batch.verifyBatchWith (idealOf answer) S.params S.instances common proof pis =
      .ok ()) :
    extractB S cache (idealOf answer) common proof pis =
      prefixTranscriptB S cache (fun k ↦ (inputsB S common pis proof).getD k [])
        (fun k ↦ (answer (keyAt answer (inputsB S common pis proof) k)).2) := by
  obtain ⟨hsize, hshape, hprep, hcs, -, hfp⟩ :=
    shape_of_verifyBatchWith S (idealOf answer) common proof pis hok
  have hfpne : proof.fri.finalPoly.toList ≠ [] := by
    refine List.ne_nil_of_length_pos ?_
    rw [Array.length_toList, hfp]
    exact Nat.two_pow_pos _
  have hz := length_zip_commitsB S (idealOf answer) common proof pis hok
  obtain ⟨hα, hζ, hbatch, hlenβ, hβ, -, -⟩ :=
    challengesB_idealOf answer S common proof pis (le_refl _) hfpne
  refine transcript_ext S ?_ hα ?_ hζ ?_ hbatch ?_ ?_ ?_
  · funext i c x
    show Merkle.matColumn cache proof.mainCommit _ _ _ _ _ _ _ =
      Merkle.matColumn cache (digestAt ((inputsB S common pis proof).getD 0 []) (mainOffsetB S))
        _ _ _ _ _ _ _
    rw [mainRoot_eq S common proof pis hprep]
  · funext i c e x
    show Merkle.matColumn cache proof.quotientCommit _ _ _ _ _ _ _ =
      Merkle.matColumn cache (digestAt ((inputsB S common pis proof).getD 1 []) 0) _ _ _ _ _ _ _
    rw [quotientRoot_eqB]
  · exact (openings_eqB S common proof pis hsize hshape hprep).symm
  · funext j m z
    show (if j < (friAritiesB S).length then friWordAt (EF := EF) cache
        (proof.fri.commits.toList.getD j 0) m ((friAritiesB S).getD j 0) z.val else 0) =
      (if j < (friAritiesB S).length then friWordAt (EF := EF) cache
        (digestAt ((inputsB S common pis proof).getD (3 + j) []) (friOffsetB S j)) m
          ((friAritiesB S).getD j 0) z.val else 0)
    split
    · rename_i hj
      rw [foldRoot_eqB S answer hok j hj]
    · rfl
  · show finalPoly S.domainSetup proof.fri.finalPoly = finalPoly S.domainSetup
      (finalPolyAt S.domainSetup
        ((inputsB S common pis proof).getD (3 + (friAritiesB S).length) []))
    rw [finalPoly_eqB S answer hok]
  · funext j
    show (lift gen : Challenge.Spec EF) ^ 2 ^ ((friAritiesB S).take j).sum *
      Challenge.toSpec ((commitReplayB (idealOf answer) S common proof pis).1.getD j 0) =
        betasAtB S (fun k ↦ (answer (keyAt answer (inputsB S common pis proof) k)).2) j
    unfold betasAtB
    split
    · rename_i hj
      rw [hβ j (by rw [hz]; exact hj)]
    · rename_i hj
      rw [List.getD_eq_default _ _ (by rw [hlenβ, hz]; omega), Challenge.toSpec_zero, mul_zero]

end Schedule

end CompStark.Ni
