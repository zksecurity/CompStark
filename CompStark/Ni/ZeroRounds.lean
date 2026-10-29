/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.Lengths

/-! # FRI without folds: the rounds' bad events

When the trace is as short as FRI's final polynomial (`logFinalPolyLen = logN`), FRI has no
commit-phase rounds: each query only checks that the batched DEEP value at its point equals the
final polynomial there. The Fiat–Shamir transcript has four rounds: `α`, `ζ`, the batching
challenge, and the query round, whose input is FRI's domain separator, the final polynomial's
coefficients and the query grinding witness.

A fresh duplex call is bad (`RoundBad0`) when the queries before it parse it as round `i` and its
answer makes round `i` bad (`roundBad0At`) for the transcript read off the parsed prefix
(`prefixTranscript0`): the rounds `α`, `ζ` and `a` as with folds (`roundBadAt`), and the query
round (`QueryBad0`) when the DEEP word is `δ`-far from the code, the grinding sample passes, and
every query selects a point where the DEEP word agrees with the final polynomial. The final
polynomial has degree below `n`, so it agrees with a far word on fewer than `(1 - δ) N` points
(`card_agreement_lt`), and the queries all land there with probability at most
`powFraction queryPowBits · friQueryError0` (`prob_queryBad0_le`).
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop CompStark.RandomOracle
open Polynomial OracleSpec OracleComp
open scoped ENNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### The transcript -/

/-- The transcript of the interactive oracle proof when FRI does not fold: the prover's words and
messages, the challenges, and the final polynomial's coefficients. -/
structure Transcript0 (S : Iop.Setup EF) where
  trace : Fin S.air.width → S.Point → F
  alpha : 𝕂
  quotient : Fin S.chunks → Fin (Challenge.d EF) → S.Point → F
  zeta : 𝕂
  openings : Openings S
  batch : 𝕂
  /-- The final polynomial's coefficients, in the coordinate of the subgroup (`finalPoly`). -/
  finalCoeffs : Array EF

namespace Transcript0
variable {S : Iop.Setup EF} (t : Transcript0 S)

/-- The batched DEEP word of the transcript. -/
noncomputable def deepWord : S.Point → 𝕂 :=
  Iop.deepWord (fixedProver t.trace t.quotient t.openings) t.alpha t.zeta t.batch

open Classical in
/-- The points of `L` where the DEEP word agrees with the final polynomial. -/
noncomputable def agreement : Finset S.Point :=
  Finset.univ.filter fun z ↦ t.deepWord z = (finalPoly S t.finalCoeffs).eval (S.domain z)

theorem mem_agreement (z : S.Point) :
    z ∈ t.agreement ↔ t.deepWord z = (finalPoly S t.finalCoeffs).eval (S.domain z) := by
  classical
  unfold agreement
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ z)

end Transcript0

section Query
variable (S : Iop.Setup EF)

/-- The query round without folds: the DEEP word is `δ`-far, the grinding sample `pow` has
`queryPowBits` vanishing low bits, and every query sample selects a point where the DEEP word
agrees with the final polynomial. -/
def QueryBad0 (δ : NNReal) (t : Transcript0 S) (pow : F)
    (queries : Fin S.params.numQueries → F) : Prop :=
  ¬ Near S δ t.deepWord ∧ CompPoly.CanonicalNat.toNat pow % 2 ^ S.params.queryPowBits = 0 ∧
    ∀ j, queryPoint S (queries j) ∈ t.agreement

/-- A final polynomial of at most `n` coefficients agrees with a `δ`-far word on fewer than
`(1 - δ) N` points. -/
theorem card_agreement_lt (δ : NNReal) (t : Transcript0 S) (hsize : t.finalCoeffs.size ≤ S.n)
    (hfar : ¬ Near S δ t.deepWord) :
    (t.agreement.card : ℝ) < 2 ^ (S.logN + S.params.logBlowup) * (1 - δ) := by
  refine lt_of_not_ge fun hge ↦ hfar ⟨t.agreement, ?_,
    fun z ↦ (finalPoly S t.finalCoeffs).eval (S.domain z), ?_,
    fun z hz ↦ (t.mem_agreement z).mp hz⟩
  · rw [ge_iff_le, Setup.size, Nat.cast_pow, Nat.cast_ofNat]
    exact hge
  · have hdeg : (finalPoly S t.finalCoeffs).natDegree < S.n := by
      refine natDegree_lt_of_degree ?_ (Nat.two_pow_pos _)
      exact (degree_sum_C_mul_X_pow_lt _ _).trans_le (by exact_mod_cast hsize)
    exact ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval _ hdeg fun _ ↦ rfl

open Classical in
/-- The query round without folds: at most `powFraction queryPowBits · friQueryError0`. -/
theorem prob_queryBad0_le (δ : NNReal) (t : Transcript0 S) (hsize : t.finalCoeffs.size ≤ S.n) :
    Pr{let z ← $ᵗ (F × (Fin S.params.numQueries → F))}[QueryBad0 S δ t z.1 z.2] ≤
      powFraction F S.params.queryPowBits * friQueryError0 S δ := by
  by_cases hfar : ¬ Near S δ t.deepWord
  · set m := S.logN + S.params.logBlowup
    set G := t.agreement.image fun z ↦ reverseBits z.val m
    have hG : (G.card : ℝ) ≤ 2 ^ m * (1 - δ) := by
      have hcard : (G.card : ℝ) ≤ t.agreement.card := by exact_mod_cast Finset.card_image_le
      exact hcard.trans (card_agreement_lt S δ t hsize hfar).le
    have h := prob_queryRound_le S.params.queryPowBits m S.params.numQueries
      (BaseField.two_pow_dvd_card_sub_one_of_le S.valid.twoAdic) G _ hG
    refine le_trans (le_of_eq ?_) h
    congr 2
    funext z
    simp only [QueryBad0, hfar, not_false_eq_true, true_and, queryPoint_mem_iff, G, m]
  · rw [SampleableType.prEvent_uniformSample]
    have h : (Finset.univ.filter fun z : F × (Fin S.params.numQueries → F) ↦
        QueryBad0 S δ t z.1 z.2) = ∅ :=
      Finset.filter_false_of_mem fun z _ hz ↦ hfar hz.1
    rw [h, Finset.card_empty, Nat.cast_zero, ENNReal.zero_div]
    exact bot_le

end Query

/-! ### The transcript of a prefix -/

section Prefix
variable (S : Iop.Setup EF)

/-- The transcript read off the inputs `block j` and answers `sample j` of the rounds `j` and the
hash queries `cache`: the words extracted under the observed digests, the observed openings and
final polynomial, the latter after FRI's domain separator, and the challenges of the answers. -/
noncomputable def prefixTranscript0 (cache : Merkle.Cache F (Digest F)) (block : Nat → List F)
    (sample : Nat → Vector F S.streamLen) : Transcript0 S where
  trace j := committedColumn S cache
    (capFrom (block 0) (starkSeedS S).length (capSize S S.logSize)) j
  alpha := extAt (sample 0) 0
  quotient c e := committedColumn S cache (capFrom (block 1) 0 (capSize S S.logSize))
    (Challenge.d EF * c.val + e.val)
  zeta := extAt (sample 1) (challengeOffset S.params.oodPowBits)
  openings := openingsAt S ((block 2).drop (pcsSeedS S).length)
  batch := extAt (sample 2) (challengeOffset S.params.batchPowBits)
  finalCoeffs := finalPolyAt S ((block 3).drop (friSeedS S).length)

/-- The prefix transcript reads the answers of the rounds before the query round only. -/
theorem prefixTranscript0_sample_congr (cache : Merkle.Cache F (Digest F)) (block : Nat → List F)
    {sample sample' : Nat → Vector F S.streamLen} (h : ∀ j, j ≤ 2 → sample j = sample' j) :
    prefixTranscript0 S cache block sample = prefixTranscript0 S cache block sample' := by
  simp only [prefixTranscript0, h 0 (by omega), h 1 (by omega), h 2 (by omega)]

/-- The prefix transcript's final polynomial has the `n` coefficients the verifier checks, at
most `n`. -/
theorem size_prefixTranscript0 (cache : Merkle.Cache F (Digest F)) (block : Nat → List F)
    (sample : Nat → Vector F S.streamLen) :
    (prefixTranscript0 S cache block sample).finalCoeffs.size ≤ S.n := by
  simp only [prefixTranscript0, finalPolyAt, Array.size_ofFn]
  exact Nat.pow_le_pow_right (by decide) S.valid.finalPolyFits

variable (publicValues : List F) (δ δ' : NNReal)

/-- Round `i`'s bad event without folds on the transcript `t`, whose round `i` was answered `u`:
`α`; `ζ` and batching, each with its grinding sample, the answer's first; and the queries. -/
def roundBad0At (i : Nat) (t : Transcript0 S) (u : Vector F S.streamLen) : Prop :=
  if i = 0 then AlphaBad S publicValues δ' t.trace t.alpha
  else if i = 1 then
    (S.params.oodPowBits ≠ 0 →
      CompPoly.CanonicalNat.toNat ((u.toList.getD 0 0)) % 2 ^ S.params.oodPowBits = 0) ∧
      ZetaBad S publicValues δ' t.trace t.alpha t.quotient t.zeta
  else if i = 2 then
    (S.params.batchPowBits ≠ 0 →
      CompPoly.CanonicalNat.toNat ((u.toList.getD 0 0)) % 2 ^ S.params.batchPowBits = 0) ∧
      BatchBad S δ δ' t.trace t.alpha t.quotient t.zeta t.openings t.batch
  else if i = 3 then QueryBad0 S δ t (powAt S u) (queriesAt S u)
  else False

/-- A duplex call is bad after the queries `pre` when FRI does not fold if `pre` parses it as
round `i` of a transcript whose first round observes `S`'s domain separator first, and its answer
makes round `i` bad for the prefix transcript on `pre`'s hash queries. -/
def RoundBad0 (pre : QueryLog (spec F S.streamLen)) :
    (t : Query F) → Answer S.streamLen t → Prop
  | .duplex cap input, u => match parse pre (.duplex cap input) with
    | some (steps, _) =>
      starkSeedS S <+: (steps.map Prod.fst ++ [input]).getD 0 [] ∧
      roundBad0At S publicValues δ δ' steps.length
        (prefixTranscript0 S (logCache pre) (fun j ↦ (steps.map Prod.fst ++ [input]).getD j [])
          fun j ↦ (steps.map Prod.snd ++ [u.2]).getD j (Vector.replicate _ 0)) u.2
    | none => False
  | .leaf _, _ => False
  | .node .., _ => False

/-- A bad duplex call's first round observes the setup's domain separator first. -/
theorem prefix_firstBlock0 (pre : QueryLog (spec F S.streamLen)) (t : Query F)
    (u : Answer S.streamLen t) (h : RoundBad0 S publicValues δ δ' pre t u) :
    starkSeedS S <+: firstBlock pre t := by
  cases t with
  | duplex cap input =>
    unfold RoundBad0 at h
    unfold firstBlock
    dsimp only at h ⊢
    cases hp : parse pre (.duplex cap input) with
    | none => rw [hp] at h; exact absurd h id
    | some r =>
      obtain ⟨steps, rest⟩ := r
      rw [hp] at h
      exact h.1
  | leaf => exact absurd h id
  | node => exact absurd h id

/-! ### The rounds' errors -/

/-- **One fresh answer without folds.** The bad event of round `i` on the prefix transcript of
`i` earlier rounds, the answer to round `i` uniform, has probability at most `roundError0`. -/
theorem prob_roundBad0At_le (cache : Merkle.Cache F (Digest F)) (block : Nat → List F)
    (samples : List (Vector F S.streamLen)) :
    Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[roundBad0At S publicValues δ δ'
      samples.length (prefixTranscript0 S cache block
        fun j ↦ (samples ++ [u.2]).getD j (Vector.replicate _ 0)) u.2] ≤
      roundError0 S δ δ' := by
  set d := Vector.replicate S.streamLen (0 : F)
  set i := samples.length with hi
  have hK : S.streamLen = S.params.numQueries + Challenge.d EF + 1 := rfl
  unfold roundBad0At
  split_ifs with h0 h1 h2 hq
  · -- `α`
    set tr := (prefixTranscript0 S cache block fun j ↦ samples.getD j d).trace
    calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(fun x ↦
          AlphaBad S publicValues δ' tr (extEquiv x)) fun j ↦ u.2.toList.getD j.val 0] :=
          prEvent_congr_iff _ fun u ↦ by
            simp only [prefixTranscript0, tr, getD_append_singleton samples u.2 d 0 h0.symm,
              extAt_eq, Nat.zero_add]
      _ = Pr{let a ← $ᵗ 𝕂}[AlphaBad S publicValues δ' tr a] := by
          refine (prob_answer_prefix S.streamLen (Challenge.d EF) (by omega)
            (fun x ↦ AlphaBad S publicValues δ' tr (extEquiv x))).trans ?_
          exact SampleableType.prEvent_uniformSample_equiv (extEquiv (EF := EF))
            (fun a ↦ AlphaBad S publicValues δ' tr a)
      _ ≤ foldingError S δ' := prob_alphaBad_le S publicValues [] 0 δ' tr
      _ ≤ _ := le_max_left _ _
  · -- `ζ`
    set T := prefixTranscript0 S cache block fun j ↦ samples.getD j d
    calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(S.params.oodPowBits ≠ 0 →
          CompPoly.CanonicalNat.toNat (u.2.toList.getD 0 0) % 2 ^ S.params.oodPowBits = 0) ∧
          ZetaBad S publicValues δ' T.trace T.alpha T.quotient
            (extAt u.2 (challengeOffset S.params.oodPowBits))] :=
          prEvent_congr_iff _ fun u ↦ by
            simp only [prefixTranscript0, T, getD_append_singleton samples u.2 d 1 h1.symm,
              getD_append_singleton_lt samples u.2 d 0 (by omega)]
      _ ≤ powFraction F S.params.oodPowBits * outOfDomainError S δ' :=
          (prob_grindExt_le S.streamLen _ (by omega) _).trans
            (mul_le_mul_right (prob_zetaBad_le S publicValues [] 0 δ' _ _ _) _)
      _ ≤ _ := (le_max_left _ _).trans (le_max_right _ _)
  · -- batching
    set T := prefixTranscript0 S cache block fun j ↦ samples.getD j d
    calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(S.params.batchPowBits ≠ 0 →
          CompPoly.CanonicalNat.toNat (u.2.toList.getD 0 0) % 2 ^ S.params.batchPowBits = 0) ∧
          BatchBad S δ δ' T.trace T.alpha T.quotient T.zeta T.openings
            (extAt u.2 (challengeOffset S.params.batchPowBits))] :=
          prEvent_congr_iff _ fun u ↦ by
            simp only [prefixTranscript0, T, getD_append_singleton samples u.2 d 2 h2.symm,
              getD_append_singleton_lt samples u.2 d 0 (by omega),
              getD_append_singleton_lt samples u.2 d 1 (by omega)]
      _ ≤ powFraction F S.params.batchPowBits * batchingError S δ δ' :=
          (prob_grindExt_le S.streamLen _ (by omega) _).trans
            (mul_le_mul_right (prob_batchBad_le S δ δ' _ _ _ _ _) _)
      _ ≤ _ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · -- the queries
    set T := prefixTranscript0 S cache block fun j ↦ samples.getD j d
    have hT (v : Vector F S.streamLen) :
        (prefixTranscript0 S cache block fun j ↦ (samples ++ [v]).getD j d) = T :=
      prefixTranscript0_sample_congr S cache block fun j hj ↦
        getD_append_singleton_lt samples v d j (by omega)
    have hle : powFraction F S.params.queryPowBits * friQueryError0 S δ ≤ roundError0 S δ δ' :=
      (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    refine le_trans ?_ hle
    refine le_trans (le_of_eq ?_)
      (prob_queryBad0_le S δ T (size_prefixTranscript0 S cache block _))
    by_cases hb : S.params.queryPowBits = 0
    · have hpow (a : F) (q : Fin S.params.numQueries → F) :
          QueryBad0 S δ T a q ↔ QueryBad0 S δ T 0 q := by
        simp only [QueryBad0, hb, pow_zero, Nat.mod_one]
      calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(fun x ↦
            QueryBad0 S δ T 0 (fieldsEquiv _ x)) fun j ↦ u.2.toList.getD j.val 0] :=
            prEvent_congr_iff _ fun u ↦ by
              have hp : powAt S u.2 = 0 := by simp only [powAt, hb, ↓reduceIte]
              have hqs : queriesAt S u.2 =
                  fieldsEquiv _ (fun j : Fin S.params.numQueries ↦ u.2.toList.getD j.val 0) := by
                funext j
                simp only [queriesAt, challengeOffset, hb, ↓reduceIte, Nat.zero_add]
                rfl
              rw [hT, hp, hqs]
        _ = Pr{let q ← $ᵗ (Fin S.params.numQueries → F)}[QueryBad0 S δ T 0 q] := by
            refine (prob_answer_prefix S.streamLen S.params.numQueries (by omega)
              (fun x ↦ QueryBad0 S δ T 0 (fieldsEquiv _ x))).trans ?_
            exact SampleableType.prEvent_uniformSample_equiv (fieldsEquiv _) _
        _ = _ := by
            refine Eq.trans ?_ (prEvent_congr_iff ($ᵗ (F × (Fin S.params.numQueries → F)))
              fun z ↦ hpow z.1 z.2).symm
            have h := SampleableType.prEvent_uniformSample_equiv
              (Equiv.prodComm F (Fin S.params.numQueries → F))
              (fun z ↦ QueryBad0 S δ T 0 z.1)
            simp only [Equiv.prodComm_apply, Prod.fst_swap] at h
            rw [h, SampleableType.prEvent_uniformSample_fst
              (p := fun q ↦ QueryBad0 S δ T 0 q)]
    · calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(fun x ↦
            QueryBad0 S δ T (powFieldsEquiv _ x).1 (powFieldsEquiv _ x).2)
              fun j ↦ u.2.toList.getD j.val 0] :=
            prEvent_congr_iff _ fun u ↦ by
              have hp : powAt S u.2 = (powFieldsEquiv _
                  (fun j : Fin (S.params.numQueries + 1) ↦ u.2.toList.getD j.val 0)).1 := by
                simp only [powAt, hb, ↓reduceIte]
                rfl
              have hqs : queriesAt S u.2 = (powFieldsEquiv _
                  (fun j : Fin (S.params.numQueries + 1) ↦ u.2.toList.getD j.val 0)).2 := by
                funext j
                simp only [queriesAt, challengeOffset, hb, ↓reduceIte]
                show _ = (u.2.toList.getD (j.val + 1) 0)
                rw [Nat.add_comm]
              rw [hT, hp, hqs]
        _ = _ := by
            refine (prob_answer_prefix S.streamLen (S.params.numQueries + 1) (by omega)
              (fun x ↦ QueryBad0 S δ T (powFieldsEquiv _ x).1 (powFieldsEquiv _ x).2)).trans ?_
            exact SampleableType.prEvent_uniformSample_equiv (powFieldsEquiv _)
              (fun z ↦ QueryBad0 S δ T z.1 z.2)
  · simp only [prEvent_false, zero_le]

/-- **A fresh duplex answer without folds.** After any queries `pre`, a uniform answer to any
call is round-bad with probability at most `roundError0`. -/
theorem prob_roundBad0_le (pre : QueryLog (spec F S.streamLen)) (t : Query F) :
    Pr{let u ← $ᵗ (Answer S.streamLen t)}[RoundBad0 S publicValues δ δ' pre t u] ≤
      roundError0 S δ δ' := by
  cases t with
  | duplex cap input =>
    cases hparse : parse pre (.duplex cap input) with
    | none =>
      refine le_of_eq_of_le (prEvent_congr_iff _ fun u ↦ (?_ : _ ↔ False)) ?_
      · unfold RoundBad0
        dsimp only
        rw [hparse]
      · simp only [prEvent_false, zero_le]
    | some r =>
      obtain ⟨steps, rest⟩ := r
      have h := prob_roundBad0At_le S publicValues δ δ' (logCache pre)
        (fun j ↦ (steps.map Prod.fst ++ [input]).getD j []) (steps.map Prod.snd)
      rw [List.length_map] at h
      refine le_trans (prEvent_mono _ _ _ fun u hu ↦ ?_) h
      unfold RoundBad0 at hu
      dsimp only at hu
      rw [hparse] at hu
      exact hu.2
  | leaf row =>
    refine le_of_eq_of_le (prEvent_congr_iff _ fun u ↦ (Iff.rfl : _ ↔ False)) ?_
    simp only [prEvent_false, zero_le]
  | node left right =>
    refine le_of_eq_of_le (prEvent_congr_iff _ fun u ↦ (Iff.rfl : _ ↔ False)) ?_
    simp only [prEvent_false, zero_le]

end Prefix

end CompStark.Ni
