/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.ZeroRounds

/-! # FRI without folds: BCS consistency

On a proof of `2 ^ logN` rows with `logFinalPolyLen = logN`, Plonky3's fold schedule is empty
(`friHyps0`): the proof has no commit-phase commitments, FRI's domain separator is `S`'s for zero
arities (`friSeedOf_eq0`), and every query only compares its batched quotient with the final
polynomial at its point.

`bcs0`: if the verifier accepts such a proof whose commitments bind the rows extracted from a
cache, the transcript extracted from the proof and the cache (`extract0`) passes the constraint
check at `ζ`, its query grinding sample has its vanishing bits, and every query sample selects a
point where the DEEP word agrees with the final polynomial. On an answer table, the extracted
transcript is the prefix transcript of the proof's four rounds
(`extract0_eq_prefixTranscript0`).
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop CompStark.RandomOracle
open Polynomial OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

variable (S : Iop.Setup EF)

/-! ### The empty fold schedule -/

/-- Without folds, `S` has no fold arities. -/
theorem foldArities_eq_nil (h0 : S.params.logFinalPolyLen = S.logN) : S.foldArities = [] := by
  rw [Iop.Setup.foldArities, h0, Nat.sub_self, Sound.folds]

/-- The verifier's FRI rounds on a proof of `2 ^ logN` rows without folds: the largest query
domain is `L`, every opened matrix has its height, and the fold schedule is empty. -/
theorem friHyps0 (h0 : S.params.logFinalPolyLen = S.logN) (vk : Option (PreprocessedKey F))
    (proof : Proof F EF) (zeta : EF) (hdb : proof.degreeBits = S.logN) :
    friLogMax S.params proof = S.logSize ∧
      (∀ x ∈ openingRounds S.air vk proof zeta, ∀ dp ∈ x.2,
        dp.1.logSize + S.params.logBlowup = S.logSize) ∧
      friSchedule S.params proof = [] := by
  have hL : friLogMax S.params proof = S.logSize := by
    simp only [friLogMax, hdb, Iop.Setup.logSize]
  refine ⟨hL, fun x hx dp hdp ↦ ?_, ?_⟩
  · rw [logSize_openingRounds S.air vk proof zeta x hx dp hdp, hdb]
  · rw [friSchedule, hL]
    cases hm : S.logSize with
    | zero => rfl
    | succ m =>
      have hle : m + 1 ≤ S.params.logBlowup + S.params.logFinalPolyLen := by
        unfold Iop.Setup.logSize at hm
        omega
      simp only [foldSchedule, hle, ↓reduceIte]

/-- On a proof for `2 ^ logN` rows without folds, FRI's domain separator is `S`'s. -/
theorem friSeedOf_eq0 (h0 : S.params.logFinalPolyLen = S.logN) (proof : Proof F EF)
    (hdb : proof.degreeBits = S.logN) : friSeedOf S.params proof = friSeedS S := by
  obtain ⟨hL, -, hsched⟩ := friHyps0 S h0 none proof 0 hdb
  rw [friSeedOf, hsched, hL, friSeedS, foldArities_eq_nil S h0]
  rfl

/-- An accepted proof for `2 ^ logN` rows without folds has no commit-phase commitments, a final
polynomial of `2 ^ logFinalPolyLen` coefficients, and trace and quotient caps of the size of
`S`'s trees. -/
theorem fri0_ok (h0 : S.params.logFinalPolyLen = S.logN) (H : Primitives F Id)
    (vk : Option (PreprocessedKey F)) (proof : Proof F EF) (pis : List F)
    (hdb : proof.degreeBits = S.logN) (h : verifyWith H S.params S.air vk proof pis = .ok ()) :
    proof.fri.commits.size = 0 ∧ proof.fri.commitWitnesses.size = 0 ∧
      proof.fri.finalPoly.size = 2 ^ S.params.logFinalPolyLen ∧
      proof.traceCommit.size = capSize S S.logSize ∧
      proof.quotientCommit.size = capSize S S.logSize := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨st, hfriOk⟩, -⟩ :=
    verifyWith_ok H S.params S.air vk proof pis h
  obtain ⟨hL, hh, hsched⟩ := friHyps0 S h0 vk proof (zetaOf H S.params S.air vk proof pis) hdb
  obtain ⟨-, hfolds, hcs, hcw, hfp, -, hcrlen, hq⟩ :=
    verifyFri_ok H S.params proof.fri _ _ _ hh _ _ hfriOk
  have har : foldSchedule S.params.maxLogArity (S.params.logBlowup + S.params.logFinalPolyLen)
      S.logSize [S.logSize] = [] := by
    rwa [friSchedule, hL] at hsched
  obtain ⟨hround, -⟩ := size_caps_of_queryOk _ _ _ _ _ _ _ _ _ _ _ _ _
    hcrlen (by rw [Array.length_toList]; exact hfolds) (hq 0 S.valid.queries)
  rw [har] at hcs hcw
  exact ⟨hcs, hcw, hfp,
    hround 0 (by simp only [openingRounds, List.cons_append, List.length_cons]; omega),
    hround 1 (by simp only [openingRounds, List.cons_append, List.length_cons]; omega)⟩

/-! ### The final polynomial -/

/-- The extracted final polynomial at the point `s x`, `s` the final domain's shift, is Plonky3's
final polynomial at `x`. -/
theorem eval_finalPoly_mul (coeffs : Array EF) (x : F) :
    (finalPoly S coeffs).eval (S.finalShift * lift x) =
      Challenge.toSpec (coeffs.foldr (fun c acc ↦ acc * Ext.ofBase x + c) 0) := by
  have hpt : Challenge.toSpec (Ext.ofBase x : EF) = lift x := by
    rw [Challenge.toSpec_ofBase']
  rw [← Array.foldr_toList, toSpec_horner_list, Array.length_toList, hpt, finalPoly,
    eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, Array.getD_eq_getD_getElem?,
    List.getD_eq_getElem?_getD, Array.getElem?_toList, mul_assoc, ← mul_pow, ← mul_assoc,
    inv_mul_cancel₀ (show S.finalShift ≠ 0 from pow_ne_zero _ lift_gen_ne_zero), one_mul]

/-- Without folds, the extracted final polynomial at the point of `L` of index `rev I` is
Plonky3's final polynomial at the subgroup's point. -/
theorem eval_finalPoly0 (h0 : S.params.logFinalPolyLen = S.logN) (coeffs : Array EF) (I : Nat) :
    (finalPoly S coeffs).eval (S.domain (finMod S.logSize (reverseBits I S.logSize))) =
      Challenge.toSpec (coeffs.foldr (fun c acc ↦
        acc * Ext.ofBase (powF (twoAdicGen S.logSize) (reverseBits I S.logSize)) + c) 0) := by
  have hs : S.finalShift = lift gen := by
    rw [Iop.Setup.finalShift, h0, Nat.sub_self, pow_zero, pow_one]
  rw [domain_finMod, lift_mul, ← hs]
  exact eval_finalPoly_mul S coeffs _

/-! ### The extracted transcript -/

/-- The interactive oracle proof's transcript without folds extracted from an accepted proof: the
words from `cache`, the opened values and final polynomial from the proof, and the challenges of
the run on `H`. -/
noncomputable def extract0 (cache : Merkle.Cache F (Digest F)) (H : Primitives F Id)
    (vk : Option (PreprocessedKey F)) (proof : Proof F EF) (pis : List F) : Transcript0 S where
  trace := traceWords S cache proof
  alpha := Challenge.toSpec (alphaOf H S.params S.air vk proof pis)
  quotient := quotientWords S cache proof
  zeta := Challenge.toSpec (zetaOf H S.params S.air vk proof pis)
  openings := openingsOf S proof.opened
  batch := Challenge.toSpec (batchOf H S.params S.air vk proof pis)
  finalCoeffs := proof.fri.finalPoly

/-- **BCS consistency without folds.** If the verifier on pure primitives `H` accepts a proof of
`2 ^ logN` rows, `logN = logFinalPolyLen`, whose commitments bind the rows extracted from
`cache`, and under whose preprocessed commitment `cache` holds the preprocessed trace's extension,
the extracted transcript passes the check at `ζ`, the query grinding sample has its vanishing
bits, and every query sample selects a point where the DEEP word agrees with the final
polynomial. -/
theorem bcs0 (h0 : S.params.logFinalPolyLen = S.logN) (cache : Merkle.Cache F (Digest F))
    (H : Primitives F Id) (vk : Option (PreprocessedKey F)) (proof : Proof F EF) (pis : List F)
    (hdb : proof.degreeBits = S.logN)
    (htrace : CapBinding cache H proof.traceCommit)
    (hquot : CapBinding cache H proof.quotientCommit)
    (hprepBind : ∀ k ∈ vk, CapBinding cache H k.commit)
    (hprep : ∀ k ∈ vk, ∀ j < S.air.preprocessedWidth,
      committedColumn S cache k.commit j = S.preprocessedWord j)
    (h : verifyWith H S.params S.air vk proof pis = .ok ()) :
    let t := extract0 S cache H vk proof pis
    ConstraintsHoldAt S pis t.alpha t.zeta t.openings ∧
      CompPoly.CanonicalNat.toNat (powSampleOf H S.params S.air vk proof pis) %
        2 ^ S.params.queryPowBits = 0 ∧
      ∀ j : Fin S.params.numQueries,
        queryPoint S (querySampleOf H S.params S.air vk proof pis j) ∈ t.agreement := by
  intro t
  obtain ⟨htl, htn, hqc, hq4, hshape, -, -, -, -, -, ⟨st, hfriOk⟩, hcheck⟩ :=
    verifyWith_ok H S.params S.air vk proof pis h
  rw [hdb] at hcheck hshape hqc
  obtain ⟨hL, hh, hsched⟩ := friHyps0 S h0 vk proof (zetaOf H S.params S.air vk proof pis) hdb
  have hok := verifyFri_ok H S.params proof.fri _ _ _ hh _ _ hfriOk
  have hstart : friStart H S.params S.air vk proof pis =
      obsList H (stateFri H S.params S.air vk proof pis)
      (DomainSeparator.friSeed F EF (foldSchedule S.params.maxLogArity
        (S.params.logBlowup + S.params.logFinalPolyLen) S.logSize [S.logSize])
        (2 ^ S.params.logFinalPolyLen) S.params.commitPowBits S.params.queryPowBits
        S.params.numQueries S.logSize S.params.logBlowup S.params.maxLogArity) := by
    rw [friStart, friSeedOf, friSchedule, hL]
  dsimp only at hok
  rw [← hstart] at hok
  obtain ⟨-, -, -, -, -, hw, hcrlen, hq⟩ := hok
  have har : foldSchedule S.params.maxLogArity (S.params.logBlowup + S.params.logFinalPolyLen)
      S.logSize [S.logSize] = [] := by
    rwa [friSchedule, hL] at hsched
  rw [har, List.length_nil] at hcrlen
  have hcr := List.eq_nil_of_length_eq_zero hcrlen
  refine ⟨constraintsHoldAt_of_check S pis proof.opened _ _ hqc hcheck, ?_, fun j ↦ ?_⟩
  · unfold powSampleOf
    split
    · rename_i hb; rw [hb, pow_zero, Nat.mod_one]
    · rename_i hb
      simp only [chkWit, hb, ↓reduceIte, beq_iff_eq] at hw
      exact hw
  · have hqj := hq j.val j.isLt
    rw [har, hcr] at hqj
    obtain ⟨hlen, hbatch, -, -, hfinal⟩ := hqj
    simp only [querySteps, List.zip_nil_left, List.map_nil, List.length_nil,
      foldState_zero] at hfinal
    set index := (smpBits H S.logSize (sampleStates H (chkWit H S.params.queryPowBits
      proof.fri.queryWitness (obsExts H (commitReplay (EF := EF) H S.params
        (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)
        (friStart H S.params S.air vk proof pis)).2 proof.fri.finalPoly.toList)).2 j.val)).1
      with hindex
    have hidx : index < 2 ^ S.logSize := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hpt : queryPoint S (querySampleOf H S.params S.air vk proof pis j) =
        finMod S.logSize (reverseBits index S.logSize) := by
      apply Fin.ext
      simp only [queryPoint, finMod, Nat.mod_eq_of_lt (reverseBits_lt _ _), hindex,
        smpBits, querySampleOf, queryState]
    have hdeep := deepWord_eq S cache H vk proof (zetaOf H S.params S.air vk proof pis)
      (batchOf H S.params S.air vk proof pis)
      (Challenge.toSpec (alphaOf H S.params S.air vk proof pis)) hdb htl htn hqc
      (fun ch hc ↦ hq4 ch hc) hshape htrace hquot hprepBind hprep _ index hidx hlen hbatch
    rw [hpt, Transcript0.mem_agreement, eval_finalPoly0 S h0]
    refine hdeep.trans (congrArg Challenge.toSpec ?_)
    exact hfinal.symm

/-! ### The extracted transcript is the prefix transcript -/

section Schedule
variable (answer : (q : Query F) → Answer S.streamLen q) {vk : Option (PreprocessedKey F)}
  {proof : Proof F EF} {pis : List F}

theorem traceRoot_eq0 (h0 : S.params.logFinalPolyLen = S.logN) (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air vk proof pis = .ok ()) :
    capFrom ((inputs S.params S.air vk pis proof).getD 0 []) (starkSeedS S).length
      (capSize S S.logSize) = proof.traceCommit := by
  rw [inputs_getD_zero, starkSeedS, hdb, List.append_assoc,
    ← (fri0_ok S h0 _ vk proof pis hdb hok).2.2.2.1]
  exact capFrom_append _ _ _

theorem quotientRoot_eq0 (h0 : S.params.logFinalPolyLen = S.logN)
    (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air vk proof pis = .ok ()) :
    capFrom ((inputs S.params S.air vk pis proof).getD 1 []) 0 (capSize S S.logSize) =
      proof.quotientCommit := by
  rw [inputs_getD_one, ← (fri0_ok S h0 _ vk proof pis hdb hok).2.2.2.2]
  exact capFrom_append _ [] _

/-- Without folds, the proof has no commit-phase rounds. -/
theorem length_zip_commits0 (h0 : S.params.logFinalPolyLen = S.logN)
    (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air vk proof pis = .ok ()) :
    (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length = 0 := by
  rw [List.length_zip, Array.length_toList, (fri0_ok S h0 _ vk proof pis hdb hok).1,
    Nat.zero_min]

/-- Without folds, the query round's input is FRI's domain separator, the final polynomial's
coefficients and the query grinding witness. -/
theorem inputs_getD_three0 (h0 : S.params.logFinalPolyLen = S.logN)
    (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air vk proof pis = .ok ()) :
    (inputs S.params S.air vk pis proof).getD 3 [] = friSeedS S ++
      coeffs proof.fri.finalPoly.toList ++
        witnessInput S.params.queryPowBits proof.fri.queryWitness := by
  have hlast := inputs_getD_last S.params S.air vk pis proof
  rw [length_zip_commits0 S answer h0 hdb hok] at hlast
  rw [hlast, show seedAt (friSeedOf S.params proof) 0 = friSeedOf S.params proof from rfl,
    friSeedOf_eq0 S h0 proof hdb]

theorem finalPoly_eq0 (h0 : S.params.logFinalPolyLen = S.logN) (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air vk proof pis = .ok ()) :
    finalPolyAt S (((inputs S.params S.air vk pis proof).getD 3 []).drop (friSeedS S).length) =
      proof.fri.finalPoly := by
  rw [inputs_getD_three0 S answer h0 hdb hok, List.append_assoc, List.drop_left]
  exact finalPolyAt_coeffs S _ _ (fri0_ok S h0 _ vk proof pis hdb hok).2.2.1

/-- **The extracted transcript without folds.** On an accepted proof for `2 ^ logN` rows,
`logN = logFinalPolyLen`, the transcript extracted from a run on the answers `answer` is the
prefix transcript of the proof's four rounds with the answers to their duplex calls. -/
theorem extract0_eq_prefixTranscript0 (h0 : S.params.logFinalPolyLen = S.logN)
    (cache : Merkle.Cache F (Digest F)) (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air vk proof pis = .ok ()) :
    extract0 S cache (idealOf answer) vk proof pis =
      prefixTranscript0 S cache (fun k ↦ (inputs S.params S.air vk pis proof).getD k [])
        (fun k ↦ (answer (keyAt answer (inputs S.params S.air vk pis proof) k)).2) := by
  obtain ⟨htl, htn, hqc, hq4, hshape, -, -, -, -, -, ⟨st, hfriOk⟩, -⟩ :=
    verifyWith_ok (idealOf answer) S.params S.air vk proof pis hok
  have hfp : proof.fri.finalPoly.toList ≠ [] := by
    rw [ne_eq, Array.toList_eq_nil_iff, ← Array.size_eq_zero_iff,
      (fri0_ok S h0 _ vk proof pis hdb hok).2.2.1]
    exact (Nat.two_pow_pos _).ne'
  obtain ⟨hα, hζ, hbatch, -⟩ := challenges_idealOf answer S.params S.air vk proof pis
    (le_refl _) htn hshape hfp (size_quotientCommit_ne _ _ _ _ _ _ hok)
    (size_commits_ne _ _ _ _ _ _ _ hfriOk)
  simp only [extract0, prefixTranscript0, traceRoot_eq0 S answer h0 hdb hok,
    quotientRoot_eq0 S answer h0 hdb hok,
    openings_eq S vk proof pis htl htn (by rw [hqc, hdb]) hq4 (hdb ▸ hshape), hα, hζ, hbatch,
    finalPoly_eq0 S answer h0 hdb hok]
  rfl

end Schedule

/-! ### Congruences -/

section Congr
variable {cache cache' : Merkle.Cache F (Digest F)} {block block' : Nat → List F}
  {sample sample' : Nat → Vector F S.streamLen}

theorem prefixTranscript0_trace (hb : block 0 = block' 0)
    (h : CapSameUnder cache cache'
      (capFrom (block' 0) (starkSeedS S).length (capSize S S.logSize))) :
    (prefixTranscript0 S cache block sample).trace =
      (prefixTranscript0 S cache' block' sample').trace := by
  simp only [prefixTranscript0, hb, committedColumn_congr S h]

theorem prefixTranscript0_quotient (hb : block 1 = block' 1)
    (h : CapSameUnder cache cache' (capFrom (block' 1) 0 (capSize S S.logSize))) :
    (prefixTranscript0 S cache block sample).quotient =
      (prefixTranscript0 S cache' block' sample').quotient := by
  simp only [prefixTranscript0, hb, committedColumn_congr S h]

/-- The prefix transcript of the four rounds depends on their inputs and the answers before the
query round, and on the rows extracted under the observed digests. -/
theorem prefixTranscript0_congr (hb : ∀ k ≤ 3, block k = block' k)
    (hs : ∀ k ≤ 2, sample k = sample' k)
    (htrace : CapSameUnder cache cache'
      (capFrom (block' 0) (starkSeedS S).length (capSize S S.logSize)))
    (hquot : CapSameUnder cache cache' (capFrom (block' 1) 0 (capSize S S.logSize))) :
    prefixTranscript0 S cache block sample = prefixTranscript0 S cache' block' sample' := by
  rw [prefixTranscript0_sample_congr S cache block hs]
  simp only [prefixTranscript0, hb 0 (by omega), hb 1 (by omega), hb 2 (by omega),
    hb 3 (le_refl _), committedColumn_congr S htrace, committedColumn_congr S hquot]

end Congr

end CompStark.Ni
