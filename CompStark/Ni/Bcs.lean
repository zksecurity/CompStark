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
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop Polynomial Montgomery.Native32
open Fri.Spec
open KoalaBear.Fast (Ext4)

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4
local notation "𝔽" => KoalaBear.Field
local notation "𝕂" => Challenge.Spec KoalaBear.Fast.Ext4

/-! ### The run's challenges -/

section Challenges
variable (H : Primitives Id) (P : Params) (proof : Proof EF) (pis : List F)

/-- FRI's batching challenge. -/
def batchOf : EF := (smpExt H (stateFri H proof pis)).1

/-- The commit loop's folding challenges. -/
def betasOf : List EF :=
  (commitReplay H P (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)
    (smpExt H (stateFri H proof pis)).2).1

/-- The challenger before the query grinding check: after the commit loop, the final polynomial
and the fold arities. -/
def queryState : H.State :=
  (arities proof.fri).foldl (fun s (a : Nat) ↦ H.observe s (a : F))
    (obsExts H (commitReplay H P (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)
      (smpExt H (stateFri H proof pis)).2).2 proof.fri.finalPoly.toList)

/-- The query grinding sample, after the witness; `0` without query grinding. -/
def powSampleOf : 𝔽 :=
  if P.queryPowBits = 0 then 0
  else FastField.toField (H.sample (H.observe (queryState H P proof pis) proof.fri.queryWitness)).1

/-- Query `j`'s sample, whose low bits are its index. -/
def querySampleOf (j : Nat) : 𝔽 :=
  FastField.toField (H.sample (sampleStates H
    (chkWit H P.queryPowBits proof.fri.queryWitness (queryState H P proof pis)).2 j)).1

end Challenges

/-! ### The extracted transcript -/

/-- The interactive oracle proof's transcript extracted from an accepted proof: the words and FRI
oracles from `cache`, the opened values and final polynomial from the proof, and the challenges
of the run on `H`. -/
noncomputable def extract (S : Iop.Setup KoalaBear.Fast.Ext4) (cache : Merkle.Cache F Digest)
    (H : Primitives Id)
    (proof : Proof EF) (pis : List F) : Sound.Transcript S where
  trace := traceWords S cache proof
  alpha := Ext4.toSpec (alphaOf H proof pis)
  quotient := quotientWords S cache proof
  zeta := Ext4.toSpec (zetaOf H proof pis)
  openings := openingsOf S proof.opened
  batch := Ext4.toSpec (batchOf H proof pis)
  fri := friOracles S cache proof.fri.commits.toList proof.fri.finalPoly
  betas := foldChallenges S (betasOf H S.params proof pis)

/-! ### Arities -/

theorem foldArities_eq (m : Nat) : ∀ r, foldArities m r = (folds m r).map PNat.val
  | 0 => by rw [foldArities, folds]; rfl
  | r + 1 => by
    rw [foldArities, folds]
    exact congrArg (List.cons _) (foldArities_eq m _)
  decreasing_by omega

theorem natDegree_finalPoly (S : Iop.Setup KoalaBear.Fast.Ext4) (cache : Merkle.Cache F Digest)
    (commits : List Digest) (coeffs : Array EF)
    (h : coeffs.size = 2 ^ S.params.logFinalPolyLen) :
    (finalPolynomial S.schedule (friOracles S cache commits coeffs)).natDegree <
      (finalDegreeOf S).val := by
  rw [finalPolynomial_friOracles, CompPoly.CPolynomial.natDegree_toPoly,
    ← CompPoly.CPolynomial.ringEquiv_apply, RingEquiv.apply_symm_apply, finalPoly]
  rw [finalDegreeOf, finalDegree, PNat.mk_coe]
  refine Complete.natDegree_lt_of_degree ?_ (Nat.two_pow_pos _)
  rw [← h]
  exact Complete.degree_sum_C_mul_X_pow_lt _ _

/-! ### BCS consistency -/

/-- The verifier's FRI rounds on an accepted proof of `2 ^ logN` rows: the largest query domain
is `L`, above the blowup, and every opened matrix has its height. -/
theorem friHyps (S : Iop.Setup KoalaBear.Fast.Ext4) (H : Primitives Id) (proof : Proof EF)
    (pis : List F)
    (hdb : proof.degreeBits = S.logN)
    (harity : arities proof.fri = foldArities S.params.maxLogArity
      (S.logN - S.params.logFinalPolyLen)) :
    (arities proof.fri).sum + S.params.logBlowup + S.params.logFinalPolyLen = S.logSize ∧
      (arities proof.fri).sum + S.params.logBlowup + S.params.logFinalPolyLen ≠
        S.params.logBlowup ∧
      vRounds proof (zetaOf H proof pis) ≠ [] ∧
      ∀ x ∈ vRounds proof (zetaOf H proof pis), ∀ dp ∈ x.2,
        dp.1.logSize + S.params.logBlowup =
          (arities proof.fri).sum + S.params.logBlowup + S.params.logFinalPolyLen := by
  have hfolds := S.folds
  have harr : arities proof.fri = S.foldArities.map PNat.val := by
    rw [harity, foldArities_eq]; rfl
  have hsum : (arities proof.fri).sum = S.logN - S.params.logFinalPolyLen := by
    rw [harr]; exact sum_folds _ _
  have hlogMax : (arities proof.fri).sum + S.params.logBlowup + S.params.logFinalPolyLen =
      S.logSize := by
    rw [hsum]; unfold Iop.Setup.logSize; omega
  have hh : ∀ x ∈ vRounds proof (zetaOf H proof pis), ∀ dp ∈ x.2,
      dp.1.logSize + S.params.logBlowup =
      (arities proof.fri).sum + S.params.logBlowup + S.params.logFinalPolyLen := by
    intro x hx dp hdp
    rw [hlogMax]
    simp only [vRounds, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hdp
      rw [hdp, hdb]
    · obtain ⟨ch, -, rfl⟩ := List.mem_map.mp hdp
      dsimp only
      rw [hdb]
  have hb : (arities proof.fri).sum + S.params.logBlowup + S.params.logFinalPolyLen ≠
      S.params.logBlowup := by
    rw [hlogMax]; unfold Iop.Setup.logSize; omega
  have hne : vRounds proof (zetaOf H proof pis) ≠ [] := List.cons_ne_nil _ _
  exact ⟨hlogMax, hb, hne, hh⟩

/-- **BCS consistency.** If the verifier on pure primitives `H` accepts a proof of `2 ^ logN`
rows whose commitments bind the rows extracted from `cache`, the extracted transcript passes the
deterministic checks of `Sound.exists_satisfied_of_safe`, with the run's grinding and query
samples. -/
theorem bcs (S : Iop.Setup KoalaBear.Fast.Ext4) (cache : Merkle.Cache F Digest) (H : Primitives Id)
    (proof : Proof EF)
    (pis : List F) (hdb : proof.degreeBits = S.logN)
    (htrace : Binding cache H proof.traceCommit) (hquot : Binding cache H proof.quotientCommit)
    (hfri : ∀ c ∈ proof.fri.commits, Binding cache H c)
    (h : verifyWith H S.params S.air proof pis = .ok ()) :
    let t := extract S cache H proof pis
    ConstraintsHoldAt S pis t.alpha t.zeta t.openings ∧
      (finalPolynomial S.schedule t.fri).natDegree < (finalDegreeOf S).val ∧
      (powSampleOf H S.params proof pis).val % 2 ^ S.params.queryPowBits = 0 ∧
      ∀ j : Fin S.params.numQueries,
        queryPoint S (querySampleOf H S.params proof pis j) ∈ t.consistentQueries := by
  intro t
  obtain ⟨htl, htn, hqc, hq4, harity, ⟨st, hfriOk⟩, hcheck⟩ :=
    verifyWith_ok H S.params S.air proof pis h
  rw [hdb] at hcheck harity
  have harr : arities proof.fri = S.foldArities.map PNat.val := by
    rw [harity, foldArities_eq]; rfl
  obtain ⟨hlogMax, hb, hne, hh⟩ := friHyps S H proof pis hdb harity
  obtain ⟨hqa, hwit, hfp, hqs, hw, hq⟩ := verifyFri_ok H S.params proof.fri _ hb hne hh _ _
    hfriOk
  rw [hlogMax] at hq
  refine ⟨constraintsHoldAt_of_check S pis proof.opened _ _ hqc hcheck,
    natDegree_finalPoly S cache _ _ hfp, ?_, fun j ↦ ?_⟩
  · unfold powSampleOf
    split
    · rename_i h0; rw [h0, pow_zero, Nat.mod_one]
    · rename_i h0
      simp only [chkWit, h0, ↓reduceIte, beq_iff_eq] at hw
      rw [← FastField.toNat_eq_val_toField]
      exact hw
  · have hj : j.val < proof.fri.queries.size := by rw [hqs]; exact j.isLt
    obtain ⟨hlen, hbatch, hbl, hcl, hsteps, -, hfinal⟩ := hq j.val hj
    set index := (smpBits H S.logSize (sampleStates H (chkWit H S.params.queryPowBits
      proof.fri.queryWitness (queryState H S.params proof pis)).2 j.val)).1 with hindex
    have hidx : index < 2 ^ S.logSize := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hpt : queryPoint S (querySampleOf H S.params proof pis j) =
        finMod S.logSize (reverseBits index S.logSize) := by
      apply Fin.ext
      simp only [queryPoint, finMod, Nat.mod_eq_of_lt (Complete.reverseBits_lt _ _), hindex,
        smpBits, querySampleOf, FastField.toNat_eq_val_toField]
    have hsl : (proof.fri.queries[j.val].steps.toList).map (·.logArity) =
        S.foldArities.map PNat.val := by
      rw [← harr]; exact (hqa _ (Array.getElem_mem_toList hj)).2
    obtain ⟨hacc, hinit⟩ := query_checks S cache H _ _ _ proof.fri.finalPoly hsl hbl hcl
      (fun c hc ↦ hfri c (Array.mem_toList_iff.mp hc)) index hidx _ hsteps
      (by rw [List.length_zip, List.length_zip, hbl, hcl, Nat.min_self, Nat.min_self] at hfinal
          exact hfinal)
    have hdeep := deepWord_eq S cache H proof (zetaOf H proof pis) (batchOf H proof pis)
      (Ext4.toSpec (alphaOf H proof pis)) hdb htl htn hqc (fun ch hc ↦ hq4 ch hc) htrace hquot
      _ index hidx hlen hbatch
    rw [hpt]
    simp only [Transcript.consistentQueries, Fri.Spec.consistentQueries, Finset.mem_filter]
    exact ⟨hacc, hinit.trans hdeep.symm⟩

end CompStark.Ni
