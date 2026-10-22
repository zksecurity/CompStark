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
AIR's shape, the preprocessed commitment exactly when some instance has preprocessed columns,
permutation openings in their shapes and a terminal exactly for the instances with lookups, the
permutation commitment exactly with lookups, a commitment and grinding witness per fold, and a
final polynomial of its length. -/
theorem shape_of_verifyBatchWith
    (h : CompStark.Batch.verifyBatchWith H S.params S.instances common proof pis = .ok ()) :
    proof.opened.size = S.k ∧
      (∀ i : Fin S.k, CompStark.Batch.openedShapeOk ⟨S.air i, S.logN i⟩
        (proof.opened.toList.getD i noOpenings) = true) ∧
      common.preprocessed.isSome = S.instances.any (0 < ·.air.preprocessedWidth) ∧
      proof.fri.commits.size = S.friArities.length ∧
      proof.fri.commitWitnesses.size = S.friArities.length ∧
      proof.fri.finalPoly.size = 2 ^ S.params.logFinalPolyLen ∧
      proof.permutationLocal.size = S.k ∧ proof.permutationNext.size = S.k ∧
      proof.lookupTerminals.size = S.k ∧
      (∀ i : Fin S.k,
        (proof.permutationLocal.getD i #[]).size = Challenge.d EF * (S.instanceSetup i).permWidth ∧
        (proof.permutationNext.getD i #[]).size = Challenge.d EF * (S.instanceSetup i).permWidth ∧
        (proof.lookupTerminals.getD i none).isSome = !(S.lookups i).isEmpty) ∧
      proof.permutationCommit.isSome = S.hasLookups := by
  obtain ⟨hsize, -, hlsize, hnsize, htsize, -, -, -, hshapeZ, hprepS, hlk, -, -, -, -,
    ⟨st, hfriOk⟩, -⟩ := verifyBatchWith_ok H S.params S.instances common proof pis h
  obtain ⟨hpshapes, hperm⟩ := lookupShapeOk_spec S.params S.instances proof hlk
  rw [length_instances] at hsize hlsize hnsize htsize
  have hos : proof.opened.toList.length = S.k := by rw [Array.length_toList, hsize]
  have hD := descHeights_batchRounds S common proof
    (zetaOfB H S.params S.instances common proof pis) hsize
  have hok := verifyFri_okR H S.params proof.fri _ _ _ _ hfriOk
  dsimp only at hok
  rw [hD, List.headD_cons] at hok
  obtain ⟨-, -, -, -, -, hcs, hcw, hfp, -⟩ := hok
  exact ⟨hsize, fun i ↦ hshapeZ _ (zip_instances S _ hos ▸
    List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩), hprepS, hcs, hcw, hfp, hlsize, hnsize,
    htsize, permShapes S proof hlsize hnsize htsize hpshapes, hperm⟩

theorem length_zip_commitsB
    (h : CompStark.Batch.verifyBatchWith H S.params S.instances common proof pis = .ok ()) :
    (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length =
      S.friArities.length := by
  obtain ⟨-, -, -, hcs, hcw, -⟩ := shape_of_verifyBatchWith S H common proof pis h
  rw [List.length_zip, Array.length_toList, Array.length_toList, hcs, hcw, Nat.min_self]

end Accepted

/-! ### Congruences -/

section Congr
variable (S : Iop.Batch.Setup EF) {cache cache' : Merkle.Cache F (Digest F)}
  {block block' : ℕ → List F} {sample sample' : ℕ → Vector F S.streamLen}

/-- Without lookups, no instance has lookups. -/
theorem lookups_eq_nil_of (hl : S.hasLookups = false) (i : Fin S.k) : S.lookups i = [] := by
  by_contra hne
  have : S.hasLookups = true :=
    List.any_eq_true.mpr ⟨⟨S.air i, S.logN i⟩, List.mem_ofFn.mpr ⟨i, rfl⟩, by
      rw [show (⟨S.air i, S.logN i⟩ : CompStark.Batch.Instance F).lookups = S.lookups i from rfl]
      simpa only [Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff] using hne⟩
  rw [hl] at this
  exact Bool.false_ne_true this

theorem prefixTranscriptB_trace (hb : block 0 = block' 0)
    (h : SameUnderM cache cache' (digestAt (block' 0) (mainOffsetB S))) :
    (prefixTranscriptB S cache block sample).trace =
      (prefixTranscriptB S cache' block' sample').trace := by
  funext i c x
  show Merkle.matColumn cache (digestAt (block 0) (mainOffsetB S)) _ _ _ _ _ _ _ =
    Merkle.matColumn cache' (digestAt (block' 0) (mainOffsetB S)) _ _ _ _ _ _ _
  rw [hb, matColumn_congr h]

/-- The permutation traces read under the permutation commitment; without lookups, there are
none. -/
theorem prefixTranscriptB_perm (hb : block (lookupRounds S) = block' (lookupRounds S))
    (h : S.hasLookups = true → SameUnderM cache cache' (digestAt (block' (lookupRounds S)) 0)) :
    (prefixTranscriptB S cache block sample).perm =
      (prefixTranscriptB S cache' block' sample').perm := by
  funext i c e x
  cases hl : S.hasLookups
  · have h0 : ∀ (ls : List (Lookup F)) (T : Iop.Setup EF ls), ls = [] → T.permWidth = 0 := by
      rintro ls T rfl; rfl
    have hc := c.isLt
    generalize (c : ℕ) = n at hc
    rw [h0 _ _ (lookups_eq_nil_of S hl i)] at hc
    exact absurd hc (Nat.not_lt_zero _)
  replace h := h hl
  show Merkle.matColumn cache (digestAt (block (lookupRounds S)) 0) _ _ _ _ _ _ _ =
    Merkle.matColumn cache' (digestAt (block' (lookupRounds S)) 0) _ _ _ _ _ _ _
  rw [hb, matColumn_congr h]

theorem prefixTranscriptB_quotient (hb : block (lookupRounds S + 1) = block' (lookupRounds S + 1))
    (h : SameUnderM cache cache' (digestAt (block' (lookupRounds S + 1)) 0)) :
    (prefixTranscriptB S cache block sample).quotient =
      (prefixTranscriptB S cache' block' sample').quotient := by
  funext i c e x
  show Merkle.matColumn cache (digestAt (block (lookupRounds S + 1)) 0) _ _ _ _ _ _ _ =
    Merkle.matColumn cache' (digestAt (block' (lookupRounds S + 1)) 0) _ _ _ _ _ _ _
  rw [hb, matColumn_congr h]

theorem prefixTranscriptB_words (f : ℕ)
    (hb : block (lookupRounds S + 3 + f) = block' (lookupRounds S + 3 + f))
    (h : SameUnder cache cache' (digestAt (block' (lookupRounds S + 3 + f)) (friOffsetB S f))) :
    (prefixTranscriptB S cache block sample).words f =
      (prefixTranscriptB S cache' block' sample').words f := by
  funext m z
  show (if f < S.friArities.length then friWordAt (EF := EF) cache
      (digestAt (block (lookupRounds S + 3 + f)) (friOffsetB S f)) m (S.friArities.getD f 0)
        z.val else 0) =
    (if f < S.friArities.length then friWordAt (EF := EF) cache'
      (digestAt (block' (lookupRounds S + 3 + f)) (friOffsetB S f)) m (S.friArities.getD f 0)
        z.val else 0)
  rw [hb, friWordAt_congr h]

end Congr

/-! ### The schedule of an accepted proof -/

section Schedule
variable (S : Iop.Batch.Setup EF) (common : CompStark.Batch.Common F)
  (proof : CompStark.Batch.BatchProof F EF) (pis : List (List F))

/-- The first round observes the head first. -/
theorem inputsB_getD_head : ∃ rest, (inputsB S common pis proof).getD 0 [] =
    headB S common pis proof ++ rest := by
  cases hl : S.hasLookups
  · have h0 : lookupRounds S = 0 := by simp only [lookupRounds, hl]; rfl
    have h := inputsB_getD_alpha S common pis proof
    rw [h0, hl] at h
    rw [h]
    exact ⟨permDigest proof ++ coeffs (proof.lookupTerminals.toList.filterMap id), by
      simp only [Bool.false_eq_true, ↓reduceIte, List.append_assoc]⟩
  · exact ⟨_, inputsB_getD_zero S common pis proof hl⟩

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
  obtain ⟨rest, hr⟩ := inputsB_getD_head S common proof pis
  rw [hr, headB, batchSeedOf_eq S common hprep]
  simp only [List.append_assoc]
  rw [← List.append_assoc (batchSeedS S), ← List.append_assoc (batchSeedS S ++ _)]
  have hlen : mainOffsetB S = (batchSeedS S ++
      coeffs (S.instances.map fun I ↦ (Ext.ofBase (I.logN : F) : EF))).length := by
    rw [List.length_append, length_coeffs_map, length_instances, mainOffsetB]
  rw [hlen]
  exact digestAt_append _ _ _

theorem permRoot_eqB (hl : S.hasLookups = true) {root : Digest F}
    (hroot : proof.permutationCommit = some root) :
    digestAt ((inputsB S common pis proof).getD (lookupRounds S) []) 0 = root := by
  rw [inputsB_getD_alpha, hl, permDigest, hroot]
  simp only [↓reduceIte, List.nil_append, Option.map_some, Option.getD_some]
  exact digestAt_append_zero _ _

theorem quotientRoot_eqB :
    digestAt ((inputsB S common pis proof).getD (lookupRounds S + 1) []) 0 =
      proof.quotientCommit := by
  rw [inputsB_getD_ood, digestAt_append_zero]

/-- The observed terminals, read back. -/
theorem filterMap_id_eq {k : ℕ} (ts : List (Option EF)) (hlen : ts.length = k) :
    ts.filterMap id = (List.finRange k).flatMap fun j : Fin k ↦ (ts.getD j.val none).toList := by
  subst hlen
  rw [List.filterMap_eq_flatMap_toList]
  conv_lhs => rw [← List.ofFn_getElem (xs := ts)]
  rw [List.ofFn_eq_map, List.flatMap_map]
  refine List.flatMap_congr fun j _ ↦ ?_
  rw [List.getD_eq_getElem _ _ j.isLt]
  rfl

theorem terminal_eqB (hl : S.hasLookups = true)
    (hperm : proof.permutationCommit.isSome = S.hasLookups)
    (htsize : proof.lookupTerminals.size = S.k)
    (hsome : ∀ i : Fin S.k, (proof.lookupTerminals.getD i none).isSome = !(S.lookups i).isEmpty)
    (i : Fin S.k) (hi : (S.lookups i).isEmpty = false) :
    Challenge.toSpec (extFrom (EF := EF)
      (((inputsB S common pis proof).getD (lookupRounds S) []).drop 8) (terminalIndex S i)) =
      Challenge.toSpec ((proof.lookupTerminals.getD i none).getD 0) := by
  obtain ⟨root, hroot⟩ := Option.isSome_iff_exists.mp (hperm.trans hl)
  rw [inputsB_getD_alpha, hl, permDigest, hroot]
  simp only [↓reduceIte, List.nil_append, Option.map_some, Option.getD_some]
  rw [List.drop_left' Vector.length_toList]
  have htl : proof.lookupTerminals.toList.length = S.k := by rw [Array.length_toList, htsize]
  have hlenT : ∀ j : Fin S.k, ((proof.lookupTerminals.toList.getD j none).toList).length =
      (fun j : Fin S.k ↦ if (S.lookups j).isEmpty then 0 else 1) j := by
    intro j
    have h := hsome j
    rw [show proof.lookupTerminals.toList.getD j none = proof.lookupTerminals.getD j none by
      rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]]
    rcases hx : proof.lookupTerminals.getD j none with _ | y <;> rw [hx] at h <;>
      cases hj : (S.lookups j).isEmpty <;> simp_all
  have hfm := filterMap_id_eq proof.lookupTerminals.toList htl
  have hlt : terminalIndex S i < (proof.lookupTerminals.toList.filterMap id).length := by
    rw [hfm, length_flatMap_finRange _ _ hlenT]
    have := blockOff_add_le (fun j : Fin S.k ↦ if (S.lookups j).isEmpty then 0 else 1) i
    simp only [hi, Bool.false_eq_true, ↓reduceIte] at this
    unfold terminalIndex
    omega
  rw [← List.append_nil (coeffs _), extFrom_coeffs [] _ _ hlt]
  have hpos : 0 < (fun j : Fin S.k ↦ if (S.lookups j).isEmpty then 0 else 1) i := by
    show 0 < (if (S.lookups i).isEmpty then 0 else 1)
    rw [hi]
    decide
  have hg := getD_flatMap_finRange
    (fun j : Fin S.k ↦ (proof.lookupTerminals.toList.getD j none).toList) _ hlenT 0 i 0 hpos
  rw [Nat.add_zero, ← hfm] at hg
  rw [← List.getD_eq_getElem _ 0 hlt]
  unfold terminalIndex
  rw [hg, show proof.lookupTerminals.toList.getD i none = proof.lookupTerminals.getD i none by
    rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]]
  have h := hsome i
  rw [hi, Bool.not_false] at h
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp h
  rw [hy]
  rfl

/-- On a proof in the instances' shapes, the decoded openings are the opened values. -/
theorem openings_eqB (hsize : proof.opened.size = S.k)
    (hlsize : proof.permutationLocal.size = S.k) (hnsize : proof.permutationNext.size = S.k)
    (hshape : ∀ i : Fin S.k, CompStark.Batch.openedShapeOk ⟨S.air i, S.logN i⟩
      (proof.opened.toList.getD i noOpenings) = true)
    (hprep : common.preprocessed.isSome = S.instances.any (0 < ·.air.preprocessedWidth))
    (hpw : ∀ i : Fin S.k,
      (proof.permutationLocal.getD i #[]).size = Challenge.d EF * (S.instanceSetup i).permWidth ∧
      (proof.permutationNext.getD i #[]).size = Challenge.d EF * (S.instanceSetup i).permWidth)
    (hperm : proof.permutationCommit.isSome = S.hasLookups) :
    openingsAtB S (((inputsB S common pis proof).getD (lookupRounds S + 2) []).drop
      (pcsSeedB S).length) = fun i ↦ openingsOf (S.instanceSetup i)
        (proof.opened.toList.getD i noOpenings) (proof.permutationLocal.getD i #[])
        (proof.permutationNext.getD i #[]) := by
  rw [inputsB_getD_pcs, claimCounts_batchRounds_eq S common proof hsize hlsize hnsize hshape
    hprep hpw hperm, ← pcsSeedB, List.append_assoc, List.drop_left]
  funext i
  exact openingsAtB_coeffs S common proof hsize hlsize hnsize hshape hprep hpw hperm 0 _ i

theorem friArities_ne_nil : S.friArities ≠ [] := by
  have hf := S.folds S.top
  have hb := (S.valid S.top).blowup
  unfold Iop.Batch.Setup.friArities Iop.Batch.Setup.logTop
  obtain ⟨n, hn⟩ : ∃ n, S.logN S.top + S.params.logBlowup = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
    (by omega)).symm⟩
  rw [hn, foldSchedule, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  exact List.cons_ne_nil _ _

variable (answer : (q : Query F) → Answer S.streamLen q)
variable {common proof pis}

theorem foldRoot_eqB
    (hok : CompStark.Batch.verifyBatchWith (idealOf answer) S.params S.instances common proof pis =
      .ok ()) (i : ℕ) (hi : i < S.friArities.length) :
    digestAt ((inputsB S common pis proof).getD (lookupRounds S + 3 + i) []) (friOffsetB S i) =
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
    finalPolyAt S.domainSetup
      ((inputsB S common pis proof).getD (lookupRounds S + 3 + S.friArities.length) []) =
      proof.fri.finalPoly := by
  have hz := length_zip_commitsB S (idealOf answer) common proof pis hok
  obtain ⟨-, -, -, -, -, hfp, -⟩ := shape_of_verifyBatchWith S (idealOf answer) common proof pis hok
  have hlast := inputsB_getD_last S common pis proof
  rw [hz] at hlast
  have hseed : seedAt (friSeedB S) S.friArities.length = [] := by
    have := List.length_pos_of_ne_nil (friArities_ne_nil S)
    simp only [seedAt, Nat.pos_iff_ne_zero.mp this, ↓reduceIte]
  rw [hlast, hseed, List.nil_append]
  exact finalPolyAt_coeffs S.domainSetup _ _ hfp

/-- Batch transcripts with the same fields are equal. -/
theorem transcript_ext {t t' : Sound.Batch.Transcript S} (h1 : t.trace = t'.trace)
    (h2 : t.lookupAlpha = t'.lookupAlpha) (h3 : t.lookupBeta = t'.lookupBeta)
    (h4 : t.perm = t'.perm) (h5 : t.terminal = t'.terminal) (h6 : t.alpha = t'.alpha)
    (h7 : t.quotient = t'.quotient) (h8 : t.zeta = t'.zeta) (h9 : t.openings = t'.openings)
    (h10 : t.batch = t'.batch) (h11 : t.words = t'.words) (h12 : t.finalPoly = t'.finalPoly)
    (h13 : t.betas = t'.betas) : t = t' := by
  cases t
  cases t'
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  rfl

/-- Without lookups the lookup challenges are `0`. -/
theorem lookupRunB_eq_zero (hl : S.hasLookups = false) :
    lookupRunB (idealOf answer) S.params S.instances common proof pis = (0, 0) := by
  have hl' : CompStark.Batch.hasLookups S.instances = false := hl
  rw [lookupRunB, lookupRun, ite_eq_right_of_eq_false _ _ (eq_false (by rw [hl']; decide))]

/-- **The extracted batch transcript.** On an accepted batch proof, the transcript extracted
from a run on the answers `answer` is the prefix transcript of the proof's schedule with the
answers to its duplex calls. -/
theorem extractB_eq_prefixTranscriptB (cache : Merkle.Cache F (Digest F))
    (hok : CompStark.Batch.verifyBatchWith (idealOf answer) S.params S.instances common proof pis =
      .ok ()) :
    extractB S cache (idealOf answer) common proof pis =
      prefixTranscriptB S cache (fun k ↦ (inputsB S common pis proof).getD k [])
        (fun k ↦ (answer (keyAt answer (inputsB S common pis proof) k)).2) := by
  obtain ⟨hsize, hshape, hprep, hcs, -, hfp, hlsize, hnsize, htsize, hpw, hperm⟩ :=
    shape_of_verifyBatchWith S (idealOf answer) common proof pis hok
  have hfpne : proof.fri.finalPoly.toList ≠ [] := by
    refine List.ne_nil_of_length_pos ?_
    rw [Array.length_toList, hfp]
    exact Nat.two_pow_pos _
  have hz := length_zip_commitsB S (idealOf answer) common proof pis hok
  obtain ⟨hlk, hα, hζ, hbatch, hlenβ, hβ, -, -⟩ :=
    challengesB_idealOf answer S common proof pis (le_refl _) hfpne hperm
  refine transcript_ext S ?_ ?_ ?_ ?_ ?_ hα ?_ hζ ?_ hbatch ?_ ?_ ?_
  · funext i c x
    show Merkle.matColumn cache proof.mainCommit _ _ _ _ _ _ _ =
      Merkle.matColumn cache (digestAt ((inputsB S common pis proof).getD 0 []) (mainOffsetB S))
        _ _ _ _ _ _ _
    rw [mainRoot_eq S common proof pis hprep]
  · show Challenge.toSpec (lookupRunB (idealOf answer) S.params S.instances common proof pis).1 =
      if S.hasLookups then _ else 0
    cases hl : S.hasLookups
    · rw [lookupRunB_eq_zero S answer hl, Challenge.toSpec_zero]
      rfl
    · exact (hlk hl).1
  · show Challenge.toSpec (lookupRunB (idealOf answer) S.params S.instances common proof pis).2 =
      if S.hasLookups then _ else 0
    cases hl : S.hasLookups
    · rw [lookupRunB_eq_zero S answer hl, Challenge.toSpec_zero]
      rfl
    · exact (hlk hl).2
  · funext i c e x
    cases hl : S.hasLookups
    · have h0 : (S.instanceSetup i).permWidth = 0 := by
        have hi : (S.lookups i).isEmpty = true := by
          by_contra hne
          have : S.hasLookups = true :=
            List.any_eq_true.mpr ⟨⟨S.air i, S.logN i⟩, List.mem_ofFn.mpr ⟨i, rfl⟩, by
              rw [← lookups_eq]
              simpa only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_true] using hne⟩
          rw [hl] at this
          exact Bool.false_ne_true this
        simp only [permWidth_eq, hi, ↓reduceIte]
      exact absurd c.isLt (by omega)
    · obtain ⟨root, hroot⟩ := Option.isSome_iff_exists.mp (hperm.trans hl)
      show Merkle.matColumn cache (permRoot proof) _ _ _ _ _ _ _ =
        Merkle.matColumn cache (digestAt ((inputsB S common pis proof).getD (lookupRounds S) [])
          0) _ _ _ _ _ _ _
      rw [permRoot_eqB S common proof pis hl hroot, permRoot, hroot, Option.getD_some]
  · funext i
    show Challenge.toSpec ((proof.lookupTerminals.getD i none).getD 0) =
      if (S.lookups i).isEmpty then 0 else _
    cases hi : (S.lookups i).isEmpty
    · have hl : S.hasLookups = true :=
        List.any_eq_true.mpr ⟨⟨S.air i, S.logN i⟩, List.mem_ofFn.mpr ⟨i, rfl⟩, by
          rw [← lookups_eq, hi]; rfl⟩
      exact (terminal_eqB S common proof pis hl hperm htsize (fun j ↦ (hpw j).2.2) i hi).symm
    · have h := (hpw i).2.2
      rw [hi, Bool.not_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
      rw [h, Option.getD_none, Challenge.toSpec_zero]
      rfl
  · funext i c e x
    show Merkle.matColumn cache proof.quotientCommit _ _ _ _ _ _ _ =
      Merkle.matColumn cache (digestAt ((inputsB S common pis proof).getD (lookupRounds S + 1) [])
        0) _ _ _ _ _ _ _
    rw [quotientRoot_eqB]
  · exact (openings_eqB S common proof pis hsize hlsize hnsize hshape hprep
      (fun i ↦ ⟨(hpw i).1, (hpw i).2.1⟩) hperm).symm
  · funext j m z
    show (if j < S.friArities.length then friWordAt (EF := EF) cache
        (proof.fri.commits.toList.getD j 0) m (S.friArities.getD j 0) z.val else 0) =
      (if j < S.friArities.length then friWordAt (EF := EF) cache
        (digestAt ((inputsB S common pis proof).getD (lookupRounds S + 3 + j) [])
          (friOffsetB S j)) m (S.friArities.getD j 0) z.val else 0)
    split
    · rename_i hj
      rw [foldRoot_eqB S answer hok j hj]
    · rfl
  · show finalPoly S.domainSetup proof.fri.finalPoly = finalPoly S.domainSetup
      (finalPolyAt S.domainSetup
        ((inputsB S common pis proof).getD (lookupRounds S + 3 + S.friArities.length) []))
    rw [finalPoly_eqB S answer hok]
  · funext j
    show (lift gen : Challenge.Spec EF) ^ 2 ^ (S.friArities.take j).sum *
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
