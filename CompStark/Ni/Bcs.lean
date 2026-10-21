/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BcsDeep

/-! # BCS consistency: an accepted proof's extracted transcript

The verifier runs on pure primitives `H`, whose challenger answers are the Fiat–Shamir challenges
and whose Merkle hashes are answered from a cache of hash queries. The interactive oracle proof's
transcript is read off the proof and the cache (`extract`): the trace and quotient words and the
FRI oracles extracted from the cache under the proof's commitments, the proof's opened values and
final polynomial, and the challenges the challenger returns.

`bcs`: if the verifier accepts a proof of `2 ^ logN` rows, and every accepted opening against the
proof's commitments opens the rows extracted from the cache (`Binding`), the extracted transcript
passes the deterministic checks of the round-by-round terminal lemma
(`Sound.exists_satisfied_of_safe`): the constraints hold at `ζ`, the final polynomial has low
degree, the query grinding sample has its vanishing bits, and every query sample selects a point
where the FRI checks pass and the recommitted word agrees with the DEEP word.

The challenges are those of the run (`alphaOf`, `zetaOf`, `batchOf`, `betasOf`, `powSampleOf`,
`querySampleOf`). ArkLib folds a word on the coset `s · ⟨ω⟩` at `s β` where Plonky3 folds the same
values at `β` (`foldChallenges`), and its final polynomial is Plonky3's in the coset coordinate
(`finalPoly`).
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop Polynomial
open Fri.Spec

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### The run's challenges -/

section Challenges
variable (H : Primitives F Id) (P : Params) (A : Air F) (proof : Proof F EF) (pis : List F)

/-- The challenger when FRI's commit loop starts, after FRI's domain separator. -/
def friStart : H.State := obsList H (stateFri H P A proof pis) (friSeedOf P proof)

/-- The commit loop's folding challenges. -/
def betasOf : List EF :=
  (commitReplay H P (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)
    (friStart H P A proof pis)).1

/-- The challenger before the query grinding check: after the commit loop and the final
polynomial. -/
def queryState : H.State :=
  obsExts H (commitReplay (EF := EF) H P
    (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)
    (friStart H P A proof pis)).2 proof.fri.finalPoly.toList

/-- The query grinding sample, after the witness; `0` without query grinding. -/
def powSampleOf : F :=
  if P.queryPowBits = 0 then 0
  else (H.sample (H.observe (queryState H P A proof pis) proof.fri.queryWitness)).1

/-- Query `j`'s sample, whose low bits are its index. -/
def querySampleOf (j : Nat) : F :=
  (H.sample (sampleStates H
    (chkWit H P.queryPowBits proof.fri.queryWitness (queryState H P A proof pis)).2 j)).1

end Challenges

/-! ### The extracted transcript -/

/-- The interactive oracle proof's transcript extracted from an accepted proof: the words and FRI
oracles from `cache`, the opened values and final polynomial from the proof, and the challenges
of the run on `H`. -/
noncomputable def extract (S : Iop.Setup EF) (cache : Merkle.Cache F (Digest F))
    (H : Primitives F Id)
    (proof : Proof F EF) (pis : List F) : Sound.Transcript S where
  trace := traceWords S cache proof
  alpha := Challenge.toSpec (alphaOf H S.params S.air proof pis)
  quotient := quotientWords S cache proof
  zeta := Challenge.toSpec (zetaOf H S.params S.air proof pis)
  openings := openingsOf S proof.opened
  batch := Challenge.toSpec (batchOf H S.params S.air proof pis)
  fri := friOracles S cache proof.fri.commits.toList proof.fri.finalPoly
  betas := foldChallenges S (betasOf H S.params S.air proof pis)

/-! ### Arities -/

theorem foldArities_eq (m : Nat) : ∀ r, foldArities m r = (folds m r).map PNat.val
  | 0 => by rw [foldArities, folds]; rfl
  | r + 1 => by
    rw [foldArities, folds]
    exact congrArg (List.cons _) (foldArities_eq m _)
  decreasing_by omega

theorem natDegree_finalPoly (S : Iop.Setup EF) (cache : Merkle.Cache F (Digest F))
    (commits : List (Digest F)) (coeffs : Array EF)
    (h : coeffs.size = 2 ^ S.params.logFinalPolyLen) :
    (finalPolynomial S.schedule (friOracles S cache commits coeffs)).natDegree <
      (finalDegreeOf S).val := by
  rw [finalPolynomial_friOracles, CompPoly.CPolynomial.natDegree_toPoly,
    ← CompPoly.CPolynomial.ringEquiv_apply, RingEquiv.apply_symm_apply, finalPoly]
  rw [finalDegreeOf, finalDegree, PNat.mk_coe]
  refine natDegree_lt_of_degree ?_ (Nat.two_pow_pos _)
  rw [← h]
  exact degree_sum_C_mul_X_pow_lt _ _

/-! ### BCS consistency -/

/-- The verifier's FRI rounds on a proof of `2 ^ logN` rows: the largest query domain is `L`,
above the blowup, every opened matrix has its height, and FRI folds by `S`'s schedule. -/
theorem friHyps (S : Iop.Setup EF) (proof : Proof F EF) (zeta : EF)
    (hdb : proof.degreeBits = S.logN) :
    friLogMax S.params proof = S.logSize ∧ S.logSize ≠ S.params.logBlowup ∧
      (∀ x ∈ vRounds proof zeta, ∀ dp ∈ x.2, dp.1.logSize + S.params.logBlowup = S.logSize) ∧
      friSchedule S.params proof = S.foldArities.map PNat.val := by
  have hfolds := S.folds
  have hL : friLogMax S.params proof = S.logSize := by
    simp only [friLogMax, hdb, Iop.Setup.logSize]
  refine ⟨hL, by unfold Iop.Setup.logSize; omega, fun x hx dp hdp ↦ ?_, ?_⟩
  · rw [← hL]
    simp only [vRounds, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hdp
      rw [hdp]
    · obtain ⟨ch, -, rfl⟩ := List.mem_map.mp hdp
      rfl
  · have hsub : proof.degreeBits + S.params.logBlowup -
        (S.params.logBlowup + S.params.logFinalPolyLen) = S.logN - S.params.logFinalPolyLen := by
      omega
    rw [friSchedule, foldSchedule_single _ _ S.valid.folds _ _ (Nat.sub_le _ _), foldArities_eq,
      friLogMax, hsub]
    rfl

/-- **BCS consistency.** If the verifier on pure primitives `H` accepts a proof of `2 ^ logN`
rows whose commitments bind the rows extracted from `cache`, the extracted transcript passes the
deterministic checks of `Sound.exists_satisfied_of_safe`, with the run's grinding and query
samples. -/
theorem bcs (S : Iop.Setup EF) (cache : Merkle.Cache F (Digest F)) (H : Primitives F Id)
    (proof : Proof F EF)
    (pis : List F) (hdb : proof.degreeBits = S.logN)
    (htrace : Binding cache H proof.traceCommit) (hquot : Binding cache H proof.quotientCommit)
    (hfri : ∀ c ∈ proof.fri.commits, Binding cache H c)
    (h : verifyWith H S.params S.air proof pis = .ok ()) :
    let t := extract S cache H proof pis
    ConstraintsHoldAt S pis t.alpha t.zeta t.openings ∧
      (finalPolynomial S.schedule t.fri).natDegree < (finalDegreeOf S).val ∧
      CompPoly.CanonicalNat.toNat (powSampleOf H S.params S.air proof pis) %
        2 ^ S.params.queryPowBits = 0 ∧
      ∀ j : Fin S.params.numQueries,
        queryPoint S (querySampleOf H S.params S.air proof pis j) ∈ t.consistentQueries := by
  intro t
  obtain ⟨htl, htn, hqc, hq4, -, -, -, -, -, ⟨st, hfriOk⟩, hcheck⟩ :=
    verifyWith_ok H S.params S.air proof pis h
  rw [hdb] at hcheck
  obtain ⟨hL, hb, hh, hsched⟩ := friHyps S proof (zetaOf H S.params S.air proof pis) hdb
  have hok := verifyFri_ok H S.params proof.fri _ _ _ hb hh _ _ hfriOk
  have hstart : friStart H S.params S.air proof pis =
      obsList H (stateFri H S.params S.air proof pis)
      (DomainSeparator.friSeed F EF (foldSchedule S.params.maxLogArity
        (S.params.logBlowup + S.params.logFinalPolyLen) S.logSize [S.logSize])
        (2 ^ S.params.logFinalPolyLen) S.params.commitPowBits S.params.queryPowBits
        S.params.numQueries S.logSize S.params.logBlowup S.params.maxLogArity) := by
    rw [friStart, friSeedOf, friSchedule, hL]
  dsimp only at hok
  rw [← hstart] at hok
  obtain ⟨-, hfolds, hcs, -, hfp, hw, hcrlen, hq⟩ := hok
  set ar := foldSchedule S.params.maxLogArity (S.params.logBlowup + S.params.logFinalPolyLen)
    S.logSize [S.logSize]
  have hsched' : ar = S.foldArities.map PNat.val := by rw [← hsched, friSchedule, hL]
  refine ⟨constraintsHoldAt_of_check S pis proof.opened _ _ hqc hcheck,
    natDegree_finalPoly S cache _ _ hfp, ?_, fun j ↦ ?_⟩
  · unfold powSampleOf
    split
    · rename_i h0; rw [h0, pow_zero, Nat.mod_one]
    · rename_i h0
      simp only [chkWit, h0, ↓reduceIte, beq_iff_eq] at hw
      exact hw
  · obtain ⟨hlen, hbatch, hsteps, -, hfinal⟩ := hq j.val j.isLt
    set index := (smpBits H S.logSize (sampleStates H (chkWit H S.params.queryPowBits
      proof.fri.queryWitness (obsExts H (commitReplay (EF := EF) H S.params
        (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)
        (friStart H S.params S.air proof pis)).2 proof.fri.finalPoly.toList)).2 j.val)).1
      with hindex
    have hidx : index < 2 ^ S.logSize := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hpt : queryPoint S (querySampleOf H S.params S.air proof pis j) =
        finMod S.logSize (reverseBits index S.logSize) := by
      apply Fin.ext
      simp only [queryPoint, finMod, Nat.mod_eq_of_lt (reverseBits_lt _ _), hindex,
        smpBits, querySampleOf, queryState]
    have hflen : proof.fri.folds.toList.length = ar.length := by
      rw [Array.length_toList, hfolds]
    have hsl : (querySteps j.val ar proof.fri.folds.toList).map (·.logArity) =
        S.foldArities.map PNat.val := by
      rw [map_logArity_querySteps _ _ _ hflen, hsched']
    have hslen := length_querySteps j.val _ _ hflen
    rw [List.length_zip, hslen, Nat.min_eq_right hcrlen.ge, ← hslen] at hfinal
    obtain ⟨hacc, hinit⟩ := query_checks S cache H _ proof.fri.commits.toList _
      proof.fri.finalPoly hsl
      (by rw [hslen]; exact hcrlen)
      (by rw [hslen, Array.length_toList]; exact hcs)
      (fun c hc ↦ hfri c (Array.mem_toList_iff.mp hc))
      index hidx (queryValue S.logSize (batchOf H S.params S.air proof pis)
        (vRounds proof (zetaOf H S.params S.air proof pis)) proof.fri.inputs.toList j.val index)
      hsteps hfinal
    have hdeep := deepWord_eq S cache H proof (zetaOf H S.params S.air proof pis)
      (batchOf H S.params S.air proof pis) (Challenge.toSpec (alphaOf H S.params S.air proof pis))
      hdb htl htn hqc (fun ch hc ↦ hq4 ch hc) htrace hquot _ index hidx hlen hbatch
    rw [hpt]
    simp only [Transcript.consistentQueries, Fri.Spec.consistentQueries, Finset.mem_filter]
    exact ⟨hacc, hinit.trans hdeep.symm⟩

end CompStark.Ni
