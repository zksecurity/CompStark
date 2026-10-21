/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BatchRounds
public import CompStark.Ni.RoundBounds

/-! # The bad events of one fresh answer to the batch verifier

As for the STARK (`Ni/RoundBounds.lean`): a fresh answer to a duplex call is a uniform capacity
and `K` uniform samples, and a batch round reads its challenges off the first samples, so the bad
event of round `i` on the prefix parsed before the call has probability at most round `i`'s
error (`prob_roundBadB_le`): the prefix transcript is fixed by the earlier queries, and the
samples are carried to the challenges by bijections. A fold's challenge is Plonky3's, scaled by a
nonzero shift to ArkLib's coordinate.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop CompStark.RandomOracle
open Polynomial OracleSpec OracleComp
open scoped ENNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

section Bounds
variable (S : Iop.Batch.Setup EF) (publicValues : Fin S.k → List F) (δ δ' loss : NNReal)

/-- The largest batch round error at proximity loss `loss`; `roundError` is its infimum. -/
noncomputable def roundBoundB : ENNReal :=
  max (⨆ i, foldingError (S.instanceSetup i) δ') <|
    max (powFraction F S.params.oodPowBits * ⨆ i, outOfDomainError (S.instanceSetup i) δ') <|
    max (powFraction F S.params.batchPowBits * ⨆ i, batchingErrorOf (S.instanceSetup i)
      (S.groupNumOpened (S.logN i + S.params.logBlowup)) δ
      ((δ' : ℝ) - 2 / (S.instanceSetup i).size)) <|
    max (powFraction F S.params.commitPowBits * ⨆ j, Iop.Batch.friFoldError S δ loss j)
      (powFraction F S.params.queryPowBits * Iop.Batch.friQueryError S δ loss)

theorem roundError_eqB : Iop.Batch.roundError S δ δ' = ⨅ loss, roundBoundB S δ δ' loss := rfl

theorem streamLen_eqB : S.streamLen = S.params.numQueries + Challenge.d EF + 1 := rfl

theorem prefixTranscriptB_betas (cache : Merkle.Cache F (Digest F)) (block : ℕ → List F)
    (sample : ℕ → Vector F S.streamLen) :
    (prefixTranscriptB S cache block sample).betas = betasAtB S sample := rfl

/-- FRI's rounds read the answers of the first three rounds only. -/
theorem prefixTranscriptB_rounds_congr (cache : Merkle.Cache F (Digest F)) (block : ℕ → List F)
    {sample sample' : ℕ → Vector F S.streamLen} (h0 : sample 0 = sample' 0)
    (h1 : sample 1 = sample' 1) (h2 : sample 2 = sample' 2) :
    (prefixTranscriptB S cache block sample).rounds =
      (prefixTranscriptB S cache block sample').rounds := by
  unfold Sound.Batch.Transcript.rounds Sound.Batch.Transcript.deepWords
    Sound.Batch.Transcript.prover
  have ha : (prefixTranscriptB S cache block sample).alpha =
      (prefixTranscriptB S cache block sample').alpha := congrArg (extAt · 0) h0
  have hz : (prefixTranscriptB S cache block sample).zeta =
      (prefixTranscriptB S cache block sample').zeta :=
    congrArg (extAt · (challengeOffset S.params.oodPowBits)) h1
  have hb : (prefixTranscriptB S cache block sample).batch =
      (prefixTranscriptB S cache block sample').batch :=
    congrArg (extAt · (challengeOffset S.params.batchPowBits)) h2
  rw [ha, hz, hb]
  rfl

/-- The prefix transcript reads the answers of the rounds before the query round only. -/
theorem prefixTranscriptB_sample_congr (cache : Merkle.Cache F (Digest F)) (block : ℕ → List F)
    {sample sample' : ℕ → Vector F S.streamLen}
    (h : ∀ j, j < 3 + (friAritiesB S).length → sample j = sample' j) :
    prefixTranscriptB S cache block sample = prefixTranscriptB S cache block sample' := by
  have hβ : betasAtB S sample = betasAtB S sample' := by
    funext j
    unfold betasAtB
    split
    · rename_i hj
      rw [h (3 + j) (by omega)]
    · rfl
  simp only [prefixTranscriptB, h 0 (by omega), h 1 (by omega), h 2 (by omega), hβ]

/-- **One fresh answer.** The bad event of batch round `i` on the prefix transcript of `i`
earlier rounds, the answer to round `i` uniform, has probability at most the round's error. -/
theorem prob_roundBadAtB_le (cache : Merkle.Cache F (Digest F)) (block : ℕ → List F)
    (samples : List (Vector F S.streamLen)) :
    Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[roundBadAtB S publicValues δ δ' loss
      samples.length (prefixTranscriptB S cache block
        fun j ↦ (samples ++ [u.2]).getD j (Vector.replicate _ 0)) u.2] ≤
      roundBoundB S δ δ' loss := by
  set d := Vector.replicate S.streamLen (0 : F)
  set i := samples.length with hi
  have hK := streamLen_eqB S
  unfold roundBadAtB
  split_ifs with h0 h1 h2 hf hq
  · -- `α`
    set tr := (prefixTranscriptB S cache block fun j ↦ samples.getD j d).trace
    calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(fun x ↦
          Sound.Batch.AlphaBad S publicValues δ' tr (extEquiv x))
            fun j ↦ u.2.toList.getD j.val 0] :=
          prEvent_congr_iff _ fun u ↦ by
            simp only [prefixTranscriptB, tr, getD_append_singleton samples u.2 d 0 h0.symm,
              extAt_eq, Nat.zero_add]
      _ = Pr{let a ← $ᵗ 𝕂}[Sound.Batch.AlphaBad S publicValues δ' tr a] := by
          refine (prob_answer_prefix S.streamLen (Challenge.d EF) (by omega)
            (fun x ↦ Sound.Batch.AlphaBad S publicValues δ' tr (extEquiv x))).trans ?_
          exact SampleableType.prEvent_uniformSample_equiv extEquiv _
      _ ≤ ⨆ i, foldingError (S.instanceSetup i) δ' :=
          Sound.Batch.prob_alphaBad_le S publicValues δ' tr
      _ ≤ _ := le_max_left _ _
  · -- `ζ`
    set T := prefixTranscriptB S cache block fun j ↦ samples.getD j d
    calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(S.params.oodPowBits ≠ 0 →
          CompPoly.CanonicalNat.toNat (u.2.toList.getD 0 0) % 2 ^ S.params.oodPowBits = 0) ∧
          Sound.Batch.ZetaBad S publicValues δ' T.trace T.alpha T.quotient
            (extAt u.2 (challengeOffset S.params.oodPowBits))] :=
          prEvent_congr_iff _ fun u ↦ by
            simp only [prefixTranscriptB, T, getD_append_singleton samples u.2 d 1 h1.symm,
              getD_append_singleton_lt samples u.2 d 0 (by omega)]
      _ ≤ powFraction F S.params.oodPowBits * ⨆ i, outOfDomainError (S.instanceSetup i) δ' :=
          (prob_grindExt_le S.streamLen _ (by omega) _).trans
            (mul_le_mul_right (Sound.Batch.prob_zetaBad_le S publicValues δ' _ _ _) _)
      _ ≤ _ := (le_max_left _ _).trans (le_max_right _ _)
  · -- batching
    set T := prefixTranscriptB S cache block fun j ↦ samples.getD j d
    calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(S.params.batchPowBits ≠ 0 →
          CompPoly.CanonicalNat.toNat (u.2.toList.getD 0 0) % 2 ^ S.params.batchPowBits = 0) ∧
          Sound.Batch.BatchBad S publicValues δ δ' T.trace T.alpha T.quotient T.zeta T.openings
            (extAt u.2 (challengeOffset S.params.batchPowBits))] :=
          prEvent_congr_iff _ fun u ↦ by
            simp only [prefixTranscriptB, T, getD_append_singleton samples u.2 d 2 h2.symm,
              getD_append_singleton_lt samples u.2 d 0 (by omega),
              getD_append_singleton_lt samples u.2 d 1 (by omega)]
      _ ≤ powFraction F S.params.batchPowBits * ⨆ i, batchingErrorOf (S.instanceSetup i)
            (S.groupNumOpened (S.logN i + S.params.logBlowup)) δ
            ((δ' : ℝ) - 2 / (S.instanceSetup i).size) :=
          (prob_grindExt_le S.streamLen _ (by omega) _).trans
            (mul_le_mul_right (Sound.Batch.prob_batchBad_le S publicValues δ δ' _ _ _ _ _) _)
      _ ≤ _ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · -- fold `i - 3`
    set f := i - 3 with hfdef
    have hi3 : 3 + f = samples.length := by omega
    set T0 := prefixTranscriptB S cache block fun j ↦ samples.getD j d with hT0
    obtain ⟨c, hc_def⟩ : ∃ c : 𝕂, c = lift gen ^ 2 ^ ((friAritiesB S).take f).sum := ⟨_, rfl⟩
    have hc : c ≠ 0 := by rw [hc_def]; exact pow_ne_zero _ lift_gen_ne_zero
    have hβ (v : Vector F S.streamLen) :
        (prefixTranscriptB S cache block fun j ↦ (samples ++ [v]).getD j d).betas f =
          c * extAt v (challengeOffset S.params.commitPowBits) := by
      rw [prefixTranscriptB_betas, betasAtB, ite_eq_left_of_eq_true _ _ (eq_true hf),
        getD_append_singleton samples v d _ hi3, hc_def]
    have hR (v : Vector F S.streamLen) :
        (prefixTranscriptB S cache block fun j ↦ (samples ++ [v]).getD j d).rounds = T0.rounds :=
      prefixTranscriptB_rounds_congr S cache block
        (getD_append_singleton_lt samples v d 0 (by omega))
        (getD_append_singleton_lt samples v d 1 (by omega))
        (getD_append_singleton_lt samples v d 2 (by omega))
    have hW (v : Vector F S.streamLen) :
        (prefixTranscriptB S cache block fun j ↦ (samples ++ [v]).getD j d).words = T0.words :=
      rfl
    have hle : powFraction F S.params.commitPowBits * Iop.Batch.friFoldError S δ loss f ≤
        roundBoundB S δ δ' loss :=
      (mul_le_mul_right (le_iSup (Iop.Batch.friFoldError S δ loss) f) _).trans
        ((le_max_left _ _).trans ((le_max_right _ _).trans
          ((le_max_right _ _).trans (le_max_right _ _))))
    refine le_trans ?_ hle
    simp only [hβ, hR, hW]
    set inj := Sound.Batch.injected S T0.deepWords
    have hTR : T0.rounds = S.domainSetup.friRounds inj S.friHeights := rfl
    rw [hTR]
    by_cases hb : S.params.commitPowBits = 0
    · calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(fun x ↦
            Sound.Batch.FoldBad S δ loss (S.domainSetup.friRounds inj S.friHeights) T0.words f
              (c * extEquiv x)) fun j ↦ u.2.toList.getD j.val 0] :=
            prEvent_congr_iff _ fun u ↦ by
              simp only [hb, ne_eq, not_true_eq_false, IsEmpty.forall_iff, true_and,
                challengeOffset, ↓reduceIte, extAt_eq, Nat.zero_add]
        _ = Pr{let a ← $ᵗ 𝕂}[Sound.Batch.FoldBad S δ loss
              (S.domainSetup.friRounds inj S.friHeights) T0.words f a] := by
            refine (prob_answer_prefix S.streamLen (Challenge.d EF) (by omega)
              (fun x ↦ Sound.Batch.FoldBad S δ loss (S.domainSetup.friRounds inj S.friHeights)
                T0.words f (c * extEquiv x))).trans ?_
            refine (SampleableType.prEvent_uniformSample_equiv extEquiv
              (fun a ↦ Sound.Batch.FoldBad S δ loss (S.domainSetup.friRounds inj S.friHeights)
                T0.words f (c * a))).trans ?_
            exact SampleableType.prEvent_uniformSample_equiv (Equiv.mulLeft₀ c hc) _
        _ ≤ Iop.Batch.friFoldError S δ loss f := Sound.Batch.prob_foldBad_le S δ loss _ inj f
        _ = _ := by rw [hb, powFraction_zero, one_mul]
    · calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(fun x ↦
            CompPoly.CanonicalNat.toNat (powExtEquiv x).1 % 2 ^ S.params.commitPowBits = 0 ∧
              Sound.Batch.FoldBad S δ loss (S.domainSetup.friRounds inj S.friHeights) T0.words f
                (c * (powExtEquiv x).2))
              fun j ↦ u.2.toList.getD j.val 0] :=
            prEvent_congr_iff _ fun u ↦ by
              simp only [hb, ne_eq, not_false_eq_true, forall_const, challengeOffset,
                ↓reduceIte, extAt_eq, powExtEquiv_apply, Fin.val_zero, Fin.val_succ]
              simp only [Nat.add_comm 1]
        _ = Pr{let z ← $ᵗ (F × 𝕂)}[
              CompPoly.CanonicalNat.toNat z.1 % 2 ^ S.params.commitPowBits = 0 ∧
              Sound.Batch.FoldBad S δ loss (S.domainSetup.friRounds inj S.friHeights) T0.words f
                z.2] := by
            refine (prob_answer_prefix S.streamLen (Challenge.d EF + 1) (by omega) (fun x ↦
              CompPoly.CanonicalNat.toNat (powExtEquiv x).1 % 2 ^ S.params.commitPowBits = 0 ∧
                Sound.Batch.FoldBad S δ loss (S.domainSetup.friRounds inj S.friHeights)
                  T0.words f (c * (powExtEquiv x).2))).trans ?_
            refine (SampleableType.prEvent_uniformSample_equiv powExtEquiv
              (fun z ↦ CompPoly.CanonicalNat.toNat z.1 % 2 ^ S.params.commitPowBits = 0 ∧
                Sound.Batch.FoldBad S δ loss (S.domainSetup.friRounds inj S.friHeights)
                  T0.words f (c * z.2))).trans ?_
            exact SampleableType.prEvent_uniformSample_equiv
              (Equiv.prodCongr (Equiv.refl F) (Equiv.mulLeft₀ c hc))
              (fun z ↦ CompPoly.CanonicalNat.toNat z.1 % 2 ^ S.params.commitPowBits = 0 ∧
                Sound.Batch.FoldBad S δ loss (S.domainSetup.friRounds inj S.friHeights)
                  T0.words f z.2)
        _ ≤ _ := Sound.Batch.prob_foldRound_le S δ loss _ inj f
  · -- the queries
    set T := prefixTranscriptB S cache block fun j ↦ samples.getD j d
    have hT (v : Vector F S.streamLen) :
        (prefixTranscriptB S cache block fun j ↦ (samples ++ [v]).getD j d) = T :=
      prefixTranscriptB_sample_congr S cache block fun j hj ↦
        getD_append_singleton_lt samples v d j (by omega)
    have hle : powFraction F S.params.queryPowBits * Iop.Batch.friQueryError S δ loss ≤
        roundBoundB S δ δ' loss :=
      (le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))
    refine le_trans ?_ hle
    refine le_trans (le_of_eq ?_) (Sound.Batch.prob_queryBad_le S δ loss T)
    by_cases hb : S.params.queryPowBits = 0
    · have hpow (a : F) (q : Fin S.params.numQueries → F) :
          Sound.Batch.QueryBad S δ loss T a q ↔ Sound.Batch.QueryBad S δ loss T 0 q := by
        simp only [Sound.Batch.QueryBad, hb, pow_zero, Nat.mod_one]
      calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(fun x ↦
            Sound.Batch.QueryBad S δ loss T 0 (fieldsEquiv _ x))
              fun j ↦ u.2.toList.getD j.val 0] :=
            prEvent_congr_iff _ fun u ↦ by
              have hp : powAtB S u.2 = 0 := by simp only [powAtB, hb, ↓reduceIte]
              have hqs : queriesAtB S u.2 =
                  fieldsEquiv _ (fun j : Fin S.params.numQueries ↦ u.2.toList.getD j.val 0) := by
                funext j
                simp only [queriesAtB, challengeOffset, hb, ↓reduceIte, Nat.zero_add]
                rfl
              rw [hT, hp, hqs]
        _ = Pr{let q ← $ᵗ (Fin S.params.numQueries → F)}[
              Sound.Batch.QueryBad S δ loss T 0 q] := by
            refine (prob_answer_prefix S.streamLen S.params.numQueries (by omega)
              (fun x ↦ Sound.Batch.QueryBad S δ loss T 0 (fieldsEquiv _ x))).trans ?_
            exact SampleableType.prEvent_uniformSample_equiv (fieldsEquiv _) _
        _ = _ := by
            refine Eq.trans ?_ (prEvent_congr_iff ($ᵗ (F × (Fin S.params.numQueries → F)))
              fun z ↦ hpow z.1 z.2).symm
            have h := SampleableType.prEvent_uniformSample_equiv
              (Equiv.prodComm F (Fin S.params.numQueries → F))
              (fun z ↦ Sound.Batch.QueryBad S δ loss T 0 z.1)
            simp only [Equiv.prodComm_apply, Prod.fst_swap] at h
            rw [h, SampleableType.prEvent_uniformSample_fst
              (p := fun q ↦ Sound.Batch.QueryBad S δ loss T 0 q)]
    · calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(fun x ↦
            Sound.Batch.QueryBad S δ loss T (powFieldsEquiv _ x).1 (powFieldsEquiv _ x).2)
              fun j ↦ u.2.toList.getD j.val 0] :=
            prEvent_congr_iff _ fun u ↦ by
              have hp : powAtB S u.2 = (powFieldsEquiv _
                  (fun j : Fin (S.params.numQueries + 1) ↦ u.2.toList.getD j.val 0)).1 := by
                simp only [powAtB, hb, ↓reduceIte]
                rfl
              have hqs : queriesAtB S u.2 = (powFieldsEquiv _
                  (fun j : Fin (S.params.numQueries + 1) ↦ u.2.toList.getD j.val 0)).2 := by
                funext j
                simp only [queriesAtB, challengeOffset, hb, ↓reduceIte]
                show _ = (u.2.toList.getD (j.val + 1) 0)
                rw [Nat.add_comm]
              rw [hT, hp, hqs]
        _ = _ := by
            refine (prob_answer_prefix S.streamLen (S.params.numQueries + 1) (by omega)
              (fun x ↦ Sound.Batch.QueryBad S δ loss T (powFieldsEquiv _ x).1
                (powFieldsEquiv _ x).2)).trans ?_
            exact SampleableType.prEvent_uniformSample_equiv (powFieldsEquiv _)
              (fun z ↦ Sound.Batch.QueryBad S δ loss T z.1 z.2)
  · simp only [prEvent_false, zero_le]

/-- **A fresh duplex answer.** After any queries `pre`, a uniform answer to any call is
round-bad with probability at most the largest batch round error. -/
theorem prob_roundBadB_le (pre : QueryLog (spec F S.streamLen)) (t : Query F) :
    Pr{let u ← $ᵗ (Answer S.streamLen t)}[RoundBadB S publicValues δ δ' loss pre t u] ≤
      roundBoundB S δ δ' loss := by
  cases t with
  | duplex cap input =>
    cases hparse : parse pre (.duplex cap input) with
    | none =>
      refine le_of_eq_of_le (prEvent_congr_iff _ fun u ↦ (?_ : _ ↔ False)) ?_
      · unfold RoundBadB
        dsimp only
        rw [hparse]
      · simp only [prEvent_false, zero_le]
    | some r =>
      obtain ⟨steps, rest⟩ := r
      have h := prob_roundBadAtB_le S publicValues δ δ' loss (logCache pre)
        (fun j ↦ (steps.map Prod.fst ++ [input]).getD j []) (steps.map Prod.snd)
      rw [List.length_map] at h
      refine le_of_eq_of_le (prEvent_congr_iff _ fun u ↦ ?_) h
      unfold RoundBadB
      dsimp only
      rw [hparse]
  | leaf row =>
    refine le_of_eq_of_le (prEvent_congr_iff _ fun u ↦ (Iff.rfl : _ ↔ False)) ?_
    simp only [prEvent_false, zero_le]
  | node left right =>
    refine le_of_eq_of_le (prEvent_congr_iff _ fun u ↦ (Iff.rfl : _ ↔ False)) ?_
    simp only [prEvent_false, zero_le]

end Bounds

end CompStark.Ni
