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
samples are carried to the challenges by bijections. The lookup round reads two challenges off
consecutive samples (`prob_grindPair_le`). A fold's challenge is Plonky3's, scaled by a nonzero
shift to ArkLib's coordinate.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop CompStark.RandomOracle
open Polynomial OracleSpec OracleComp
open scoped ENNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### Two challenges in one answer -/

section Pair

/-- `d + d` samples as a pair of elements of `𝕂`. -/
noncomputable def pairEquiv : (Fin (Challenge.d EF + Challenge.d EF) → F) ≃ 𝕂 × 𝕂 :=
  ((Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl F)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)).trans (Equiv.prodCongr extEquiv extEquiv)

theorem pairEquiv_apply (x : Fin (Challenge.d EF + Challenge.d EF) → F) :
    pairEquiv x = (extEquiv fun j ↦ x (Fin.castAdd _ j), extEquiv fun j ↦ x (Fin.natAdd _ j)) :=
  rfl

/-- Two extension elements read off consecutive samples of a uniform answer from `o`, after the
first `o`, are a uniform pair. -/
theorem prob_pair_at (K o : Nat) (ho : o + (Challenge.d EF + Challenge.d EF) ≤ K)
    (P : 𝕂 × 𝕂 → Prop) :
    Pr{let u ← $ᵗ (Digest F × Vector F K)}[P (extAt u.2 o, extAt u.2 (o + Challenge.d EF))] =
      Pr{let z ← $ᵗ (𝕂 × 𝕂)}[P z] := by
  let e : (Fin (o + (Challenge.d EF + Challenge.d EF)) → F) ≃
      (Fin o → F) × (Fin (Challenge.d EF + Challenge.d EF) → F) :=
    (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl F)).trans
      (Equiv.sumArrowEquivProdArrow _ _ _)
  have he : ∀ x : Fin (o + (Challenge.d EF + Challenge.d EF)) → F,
      (e x).2 = fun j ↦ x (Fin.natAdd o j) := by
    intro x
    funext j
    simp only [e, Equiv.trans_apply, Equiv.sumArrowEquivProdArrow_apply_snd, Function.comp_apply,
      Equiv.arrowCongr_apply, Equiv.symm_symm, finSumFinEquiv_apply_right, Equiv.refl_apply]
  calc _ = Pr{let u ← $ᵗ (Digest F × Vector F K)}[(fun x ↦ P (pairEquiv (e x).2))
        fun j ↦ u.2.toList.getD j.val 0] :=
        prEvent_congr_iff _ fun u ↦ by
          dsimp only
          rw [he, pairEquiv_apply, extAt_eq, extAt_eq]
          simp only [Fin.natAdd, Fin.castAdd, Fin.val_castLE, Nat.add_assoc]
    _ = Pr{let x ← $ᵗ (Fin (o + (Challenge.d EF + Challenge.d EF)) → F)}[
          P (pairEquiv (e x).2)] :=
        prob_answer_prefix (F := F) K _ ho (fun x ↦ P (pairEquiv (e x).2))
    _ = Pr{let y ← $ᵗ ((Fin o → F) × (Fin (Challenge.d EF + Challenge.d EF) → F))}[
          P (pairEquiv y.2)] :=
        SampleableType.prEvent_uniformSample_equiv e (fun y ↦ P (pairEquiv y.2))
    _ = Pr{let z ← $ᵗ (Fin (Challenge.d EF + Challenge.d EF) → F)}[P (pairEquiv z)] := by
        have h := SampleableType.prEvent_uniformSample_equiv
          (Equiv.prodComm (Fin o → F) (Fin (Challenge.d EF + Challenge.d EF) → F))
          (fun z ↦ P (pairEquiv z.1))
        simp only [Equiv.prodComm_apply, Prod.fst_swap] at h
        rw [h]
        exact SampleableType.prEvent_uniformSample_fst (fun z ↦ P (pairEquiv z))
    _ = _ := SampleableType.prEvent_uniformSample_equiv pairEquiv P

/-- A grinding sample, an answer's first sample, with `bits` vanishing low bits, and an event on
the two extension elements read after it: at most `powFraction bits` times the event's
probability. -/
theorem prob_grindPair_le (K bits : Nat) (hK : 2 * Challenge.d EF + 1 ≤ K) (P : 𝕂 × 𝕂 → Prop) :
    Pr{let u ← $ᵗ (Digest F × Vector F K)}[(bits ≠ 0 →
      CompPoly.CanonicalNat.toNat (u.2.toList.getD 0 0) % 2 ^ bits = 0) ∧
        P (extAt u.2 (challengeOffset bits),
          extAt u.2 (challengeOffset bits + Challenge.d EF))] ≤
      powFraction F bits * Pr{let z ← $ᵗ (𝕂 × 𝕂)}[P z] := by
  classical
  by_cases hb : bits = 0
  · calc _ = Pr{let u ← $ᵗ (Digest F × Vector F K)}[
            P (extAt u.2 0, extAt u.2 (0 + Challenge.d EF))] :=
          prEvent_congr_iff _ fun u ↦ by
            simp only [hb, ne_eq, not_true_eq_false, IsEmpty.forall_iff, true_and,
              challengeOffset, ↓reduceIte]
      _ = Pr{let z ← $ᵗ (𝕂 × 𝕂)}[P z] := prob_pair_at K 0 (by omega) P
      _ ≤ _ := by rw [hb, powFraction_zero, one_mul]
  · let e : (Fin (Challenge.d EF + Challenge.d EF + 1) → F) ≃ F × (𝕂 × 𝕂) :=
      (Fin.consEquiv fun _ ↦ F).symm.trans (Equiv.prodCongr (Equiv.refl F) pairEquiv)
    have happ : ∀ x, e x = (x 0, pairEquiv fun j ↦ x j.succ) := fun _ ↦ rfl
    calc _ = Pr{let u ← $ᵗ (Digest F × Vector F K)}[(fun x ↦
          CompPoly.CanonicalNat.toNat (e x).1 % 2 ^ bits = 0 ∧ P (e x).2)
            fun j ↦ u.2.toList.getD j.val 0] :=
          prEvent_congr_iff _ fun u ↦ by
            have h1 : (fun j : Fin (Challenge.d EF) ↦ u.2.toList.getD (1 + j.val) 0) =
                fun j ↦ u.2.toList.getD (Fin.castAdd (Challenge.d EF) j).succ 0 :=
              funext fun j ↦ by rw [Fin.val_succ, Fin.val_castAdd, Nat.add_comm]
            have h2 : (fun j : Fin (Challenge.d EF) ↦
                u.2.toList.getD (1 + Challenge.d EF + j.val) 0) =
                fun j ↦ u.2.toList.getD (Fin.natAdd (Challenge.d EF) j).succ 0 :=
              funext fun j ↦ by rw [Fin.val_succ, Fin.val_natAdd]; congr 1; omega
            rw [show challengeOffset bits = 1 by simp only [challengeOffset, hb, ↓reduceIte],
              extAt_eq, extAt_eq, h1, h2]
            exact ⟨fun ⟨h, hp⟩ ↦ ⟨h hb, hp⟩, fun ⟨h, hp⟩ ↦ ⟨fun _ ↦ h, hp⟩⟩
      _ = Pr{let z ← $ᵗ (F × (𝕂 × 𝕂))}[CompPoly.CanonicalNat.toNat z.1 % 2 ^ bits = 0 ∧
            P z.2] :=
          (prob_answer_prefix K (Challenge.d EF + Challenge.d EF + 1) (by omega) (fun x ↦
            CompPoly.CanonicalNat.toNat (e x).1 % 2 ^ bits = 0 ∧ P (e x).2)).trans
            (SampleableType.prEvent_uniformSample_equiv e
              (fun z ↦ CompPoly.CanonicalNat.toNat z.1 % 2 ^ bits = 0 ∧ P z.2))
      _ ≤ _ := prob_pow_and_le bits P

end Pair

section Bounds
variable (S : Iop.Batch.Setup EF) [S.CapFits] (publicValues : Fin S.k → List F) (δ δ' loss : NNReal)

/-- The largest batch round error at proximity loss `loss`; `roundError` is its infimum. -/
noncomputable def roundBoundB : ENNReal :=
  max (powFraction F S.params.lookupPowBits * S.lookupError δ') <|
  max (⨆ i, foldingError (S.instanceSetup i) δ') <|
    max (powFraction F S.params.oodPowBits * ⨆ i, outOfDomainError (S.instanceSetup i) δ') <|
    max (powFraction F S.params.batchPowBits * ⨆ i, batchingErrorOf (S.instanceSetup i)
      (S.groupNumOpened (S.logN i + S.params.logBlowup)) δ
      δ') <|
    max (powFraction F S.params.commitPowBits * ⨆ j, Iop.Batch.friFoldError S δ loss j)
      (powFraction F S.params.queryPowBits * Iop.Batch.friQueryError S δ loss)

theorem roundError_eqB : Iop.Batch.roundError S δ δ' = ⨅ loss, roundBoundB S δ δ' loss := rfl

theorem streamLen_eqB : S.streamLen = S.params.numQueries + 2 * Challenge.d EF + 1 := rfl

theorem prefixTranscriptB_betas (cache : Merkle.Cache F (Digest F)) (block : ℕ → List F)
    (sample : ℕ → Vector F S.streamLen) :
    (prefixTranscriptB S cache block sample).betas = betasAtB S sample := rfl

/-- The lookup challenges read the lookup round's answer only. -/
theorem prefixTranscriptB_lookup_congr (cache : Merkle.Cache F (Digest F)) (block : ℕ → List F)
    {sample sample' : ℕ → Vector F S.streamLen} (h : S.hasLookups = true → sample 0 = sample' 0) :
    (prefixTranscriptB S cache block sample).lookupAlpha =
        (prefixTranscriptB S cache block sample').lookupAlpha ∧
      (prefixTranscriptB S cache block sample).lookupBeta =
        (prefixTranscriptB S cache block sample').lookupBeta := by
  simp only [prefixTranscriptB]
  by_cases hl : S.hasLookups = true
  · rw [h hl]
    exact ⟨rfl, rfl⟩
  · simp only [hl, Bool.false_eq_true, ↓reduceIte, and_self]

/-- FRI's rounds read the answers of the lookup rounds and the next three rounds only. -/
theorem prefixTranscriptB_rounds_congr (cache : Merkle.Cache F (Digest F)) (block : ℕ → List F)
    {sample sample' : ℕ → Vector F S.streamLen}
    (h : ∀ j < lookupRounds S + 3, sample j = sample' j) :
    (prefixTranscriptB S cache block sample).rounds =
      (prefixTranscriptB S cache block sample').rounds := by
  unfold Sound.Batch.Transcript.rounds Sound.Batch.Transcript.deepWords
    Sound.Batch.Transcript.prover
  obtain ⟨hla, hlb⟩ := prefixTranscriptB_lookup_congr S cache block (sample := sample)
    (sample' := sample') fun hl ↦ h 0 (by omega)
  have ha : (prefixTranscriptB S cache block sample).alpha =
      (prefixTranscriptB S cache block sample').alpha := congrArg (extAt · 0) (h _ (by omega))
  have hz : (prefixTranscriptB S cache block sample).zeta =
      (prefixTranscriptB S cache block sample').zeta :=
    congrArg (extAt · (challengeOffset S.params.oodPowBits)) (h _ (by omega))
  have hb : (prefixTranscriptB S cache block sample).batch =
      (prefixTranscriptB S cache block sample').batch :=
    congrArg (extAt · (challengeOffset S.params.batchPowBits)) (h _ (by omega))
  rw [hla, hlb, ha, hz, hb]
  rfl

/-- The prefix transcript reads the answers of the rounds before the query round only. -/
theorem prefixTranscriptB_sample_congr (cache : Merkle.Cache F (Digest F)) (block : ℕ → List F)
    {sample sample' : ℕ → Vector F S.streamLen}
    (h : ∀ j, j < lookupRounds S + 3 + S.friArities.length → sample j = sample' j) :
    prefixTranscriptB S cache block sample = prefixTranscriptB S cache block sample' := by
  have hβ : betasAtB S sample = betasAtB S sample' := by
    funext j
    unfold betasAtB
    split
    · rename_i hj
      rw [h (lookupRounds S + 3 + j) (by omega)]
    · rfl
  simp only [prefixTranscriptB, h 0 (by omega), h (lookupRounds S) (by omega),
    h (lookupRounds S + 1) (by omega), h (lookupRounds S + 2) (by omega), hβ]

/-- **One fresh answer.** The bad event of batch round `i` on the prefix transcript of `i`
earlier rounds, the answer to round `i` uniform, has probability at most the round's error. -/
theorem prob_roundBadAtB_le (cache : Merkle.Cache F (Digest F)) (block : ℕ → List F)
    (samples : List (Vector F S.streamLen)) :
    Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[roundBadAtB S publicValues δ δ' loss
      samples.length (prefixTranscriptB S cache block
        fun j ↦ (samples ++ [u.2]).getD j (Vector.replicate _ 0)) u.2] ≤
      roundBoundB S δ δ' loss := by
  set i := samples.length with hi
  have hK := streamLen_eqB S
  set T0 := prefixTranscriptB S cache block fun j ↦ samples.getD j (Vector.replicate S.streamLen 0)
    with hT0
  have hL1 : lookupRounds S ≤ 1 := by rw [lookupRounds]; split <;> omega
  have hpre : ∀ v : Vector F S.streamLen, ∀ j < i,
      (samples ++ [v]).getD j (Vector.replicate S.streamLen 0) =
        samples.getD j (Vector.replicate S.streamLen 0) :=
    fun v j hj ↦ getD_append_singleton_lt samples v (Vector.replicate S.streamLen 0) j hj
  have hcur : ∀ v : Vector F S.streamLen,
      (samples ++ [v]).getD i (Vector.replicate S.streamLen 0) = v :=
    fun v ↦ getD_append_singleton samples v (Vector.replicate S.streamLen 0) i rfl
  -- after the lookup rounds, the lookup challenges are the prefix's
  have hlk : ∀ v : Vector F S.streamLen, lookupRounds S ≤ i →
      (prefixTranscriptB S cache block
        fun j ↦ (samples ++ [v]).getD j (Vector.replicate S.streamLen 0)).lookupAlpha =
        T0.lookupAlpha ∧
      (prefixTranscriptB S cache block
        fun j ↦ (samples ++ [v]).getD j (Vector.replicate S.streamLen 0)).lookupBeta =
        T0.lookupBeta := fun v hLi ↦
    prefixTranscriptB_lookup_congr S cache block fun hl ↦ hpre v 0 (by
      have : lookupRounds S = 1 := by simp only [lookupRounds, hl, ↓reduceIte]
      omega)
  unfold roundBadAtB
  split_ifs with hlr h0 h1 h2 hf hq
  · -- the lookup challenges
    have hl : S.hasLookups = true := by
      by_contra hl
      rw [lookupRounds, ite_eq_right_of_eq_false _ _ (eq_false hl)] at hlr
      omega
    have hi0 : i = 0 := by omega
    calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(S.params.lookupPowBits ≠ 0 →
          CompPoly.CanonicalNat.toNat (u.2.toList.getD 0 0) % 2 ^ S.params.lookupPowBits = 0) ∧
          Sound.Batch.LookupBad S publicValues δ' T0.trace
            (extAt u.2 (challengeOffset S.params.lookupPowBits))
            (extAt u.2 (challengeOffset S.params.lookupPowBits + Challenge.d EF))] :=
          prEvent_congr_iff _ fun u ↦ by
            have h0' : (samples ++ [u.2]).getD 0 (Vector.replicate S.streamLen 0) = u.2 := by
              rw [← hi0]; exact hcur u.2
            simp only [prefixTranscriptB, hl, ↓reduceIte, h0', T0]
      _ ≤ powFraction F S.params.lookupPowBits *
            Pr{let z ← $ᵗ (𝕂 × 𝕂)}[Sound.Batch.LookupBad S publicValues δ' T0.trace z.1 z.2] :=
          prob_grindPair_le S.streamLen S.params.lookupPowBits (by omega)
            fun z ↦ Sound.Batch.LookupBad S publicValues δ' T0.trace z.1 z.2
      _ ≤ powFraction F S.params.lookupPowBits * S.lookupError δ' :=
          mul_le_mul_right (Sound.Batch.prob_lookupBad_le S publicValues δ' T0.trace) _
      _ ≤ _ := le_max_left _ _
  · -- `α`
    have hLi : lookupRounds S ≤ i := by omega
    have hiL : i = lookupRounds S := by omega
    calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(fun x ↦
          Sound.Batch.AlphaBad S publicValues δ' T0.trace T0.perm T0.terminal T0.lookupAlpha
            T0.lookupBeta (extEquiv x)) fun j ↦ u.2.toList.getD j.val 0] :=
          prEvent_congr_iff _ fun u ↦ by
            rw [(hlk u.2 hLi).1, (hlk u.2 hLi).2]
            have hs : (samples ++ [u.2]).getD (lookupRounds S)
                (Vector.replicate S.streamLen 0) = u.2 := by
              rw [← hiL]; exact hcur u.2
            simp only [prefixTranscriptB, T0, hs, extAt_eq, Nat.zero_add]
      _ = Pr{let a ← $ᵗ 𝕂}[Sound.Batch.AlphaBad S publicValues δ' T0.trace T0.perm T0.terminal
            T0.lookupAlpha T0.lookupBeta a] := by
          refine (prob_answer_prefix S.streamLen (Challenge.d EF) (by omega)
            (fun x ↦ Sound.Batch.AlphaBad S publicValues δ' T0.trace T0.perm T0.terminal
              T0.lookupAlpha T0.lookupBeta (extEquiv x))).trans ?_
          exact SampleableType.prEvent_uniformSample_equiv extEquiv _
      _ ≤ ⨆ i, foldingError (S.instanceSetup i) δ' :=
          Sound.Batch.prob_alphaBad_le S publicValues δ' _ _ _ _ _
      _ ≤ _ := (le_max_left _ _).trans (le_max_right _ _)
  · -- `ζ`
    have hLi : lookupRounds S ≤ i := by omega
    have hiL : i = lookupRounds S + 1 := by omega
    calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(S.params.oodPowBits ≠ 0 →
          CompPoly.CanonicalNat.toNat (u.2.toList.getD 0 0) % 2 ^ S.params.oodPowBits = 0) ∧
          Sound.Batch.ZetaBad S publicValues δ' T0.trace T0.perm T0.terminal T0.lookupAlpha
            T0.lookupBeta T0.alpha T0.quotient
            (extAt u.2 (challengeOffset S.params.oodPowBits))] :=
          prEvent_congr_iff _ fun u ↦ by
            rw [(hlk u.2 hLi).1, (hlk u.2 hLi).2]
            have hs : (samples ++ [u.2]).getD (lookupRounds S + 1)
                (Vector.replicate S.streamLen 0) = u.2 := by
              rw [← hiL]; exact hcur u.2
            simp only [prefixTranscriptB, T0, hs, hpre u.2 (lookupRounds S) (by omega)]
      _ ≤ powFraction F S.params.oodPowBits * ⨆ i, outOfDomainError (S.instanceSetup i) δ' :=
          (prob_grindExt_le S.streamLen _ (by omega) _).trans
            (mul_le_mul_right (Sound.Batch.prob_zetaBad_le S publicValues δ' _ _ _ _ _ _ _) _)
      _ ≤ _ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · -- batching
    have hLi : lookupRounds S ≤ i := by omega
    have hiL : i = lookupRounds S + 2 := by omega
    calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(S.params.batchPowBits ≠ 0 →
          CompPoly.CanonicalNat.toNat (u.2.toList.getD 0 0) % 2 ^ S.params.batchPowBits = 0) ∧
          Sound.Batch.BatchBad S publicValues δ δ' T0.trace T0.perm T0.terminal T0.lookupAlpha
            T0.lookupBeta T0.alpha T0.quotient T0.zeta T0.openings
            (extAt u.2 (challengeOffset S.params.batchPowBits))] :=
          prEvent_congr_iff _ fun u ↦ by
            rw [(hlk u.2 hLi).1, (hlk u.2 hLi).2]
            have hs : (samples ++ [u.2]).getD (lookupRounds S + 2)
                (Vector.replicate S.streamLen 0) = u.2 := by
              rw [← hiL]; exact hcur u.2
            simp only [prefixTranscriptB, T0, hs, hpre u.2 (lookupRounds S) (by omega),
              hpre u.2 (lookupRounds S + 1) (by omega)]
      _ ≤ powFraction F S.params.batchPowBits * ⨆ i, batchingErrorOf (S.instanceSetup i)
            (S.groupNumOpened (S.logN i + S.params.logBlowup)) δ
            δ' :=
          (prob_grindExt_le S.streamLen _ (by omega) _).trans
            (mul_le_mul_right (Sound.Batch.prob_batchBad_le S publicValues δ δ' _ _ _ _ _ _ _ _
              _) _)
      _ ≤ _ := (le_max_left _ _).trans ((le_max_right _ _).trans
          ((le_max_right _ _).trans (le_max_right _ _)))
  · -- fold `i - lookupRounds S - 3`
    set f := i - lookupRounds S - 3 with hfdef
    have hi3 : lookupRounds S + 3 + f = samples.length := by omega
    obtain ⟨c, hc_def⟩ : ∃ c : 𝕂, c = lift gen ^ 2 ^ (S.friArities.take f).sum := ⟨_, rfl⟩
    have hc : c ≠ 0 := by rw [hc_def]; exact pow_ne_zero _ lift_gen_ne_zero
    have hβ (v : Vector F S.streamLen) :
        (prefixTranscriptB S cache block
        fun j ↦ (samples ++ [v]).getD j (Vector.replicate S.streamLen 0)).betas f =
          c * extAt v (challengeOffset S.params.commitPowBits) := by
      rw [prefixTranscriptB_betas, betasAtB, ite_eq_left_of_eq_true _ _ (eq_true hf),
        getD_append_singleton samples v (Vector.replicate S.streamLen 0) _ hi3, hc_def]
    have hR (v : Vector F S.streamLen) :
        (prefixTranscriptB S cache block
        fun j ↦ (samples ++ [v]).getD j (Vector.replicate S.streamLen 0)).rounds = T0.rounds :=
      prefixTranscriptB_rounds_congr S cache block fun j hj ↦ hpre v j (by omega)
    have hW (v : Vector F S.streamLen) :
        (prefixTranscriptB S cache block
        fun j ↦ (samples ++ [v]).getD j (Vector.replicate S.streamLen 0)).words = T0.words :=
      rfl
    have hle : powFraction F S.params.commitPowBits * Iop.Batch.friFoldError S δ loss f ≤
        roundBoundB S δ δ' loss :=
      (mul_le_mul_right (le_iSup (Iop.Batch.friFoldError S δ loss) f) _).trans
        ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
          ((le_max_right _ _).trans (le_max_right _ _)))))
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
    have hT (v : Vector F S.streamLen) :
        (prefixTranscriptB S cache block
        fun j ↦ (samples ++ [v]).getD j (Vector.replicate S.streamLen 0)) = T0 :=
      prefixTranscriptB_sample_congr S cache block fun j hj ↦ hpre v j (by omega)
    have hle : powFraction F S.params.queryPowBits * Iop.Batch.friQueryError S δ loss ≤
        roundBoundB S δ δ' loss :=
      (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _))))
    refine le_trans ?_ hle
    refine le_trans (le_of_eq ?_) (Sound.Batch.prob_queryBad_le S δ loss T0)
    by_cases hb : S.params.queryPowBits = 0
    · have hpow (a : F) (q : Fin S.params.numQueries → F) :
          Sound.Batch.QueryBad S δ loss T0 a q ↔ Sound.Batch.QueryBad S δ loss T0 0 q := by
        simp only [Sound.Batch.QueryBad, hb, pow_zero, Nat.mod_one]
      calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(fun x ↦
            Sound.Batch.QueryBad S δ loss T0 0 (fieldsEquiv _ x))
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
              Sound.Batch.QueryBad S δ loss T0 0 q] := by
            refine (prob_answer_prefix S.streamLen S.params.numQueries (by omega)
              (fun x ↦ Sound.Batch.QueryBad S δ loss T0 0 (fieldsEquiv _ x))).trans ?_
            exact SampleableType.prEvent_uniformSample_equiv (fieldsEquiv _) _
        _ = _ := by
            refine Eq.trans ?_ (prEvent_congr_iff ($ᵗ (F × (Fin S.params.numQueries → F)))
              fun z ↦ hpow z.1 z.2).symm
            have h := SampleableType.prEvent_uniformSample_equiv
              (Equiv.prodComm F (Fin S.params.numQueries → F))
              (fun z ↦ Sound.Batch.QueryBad S δ loss T0 0 z.1)
            simp only [Equiv.prodComm_apply, Prod.fst_swap] at h
            rw [h, SampleableType.prEvent_uniformSample_fst
              (p := fun q ↦ Sound.Batch.QueryBad S δ loss T0 0 q)]
    · calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(fun x ↦
            Sound.Batch.QueryBad S δ loss T0 (powFieldsEquiv _ x).1 (powFieldsEquiv _ x).2)
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
              (fun x ↦ Sound.Batch.QueryBad S δ loss T0 (powFieldsEquiv _ x).1
                (powFieldsEquiv _ x).2)).trans ?_
            exact SampleableType.prEvent_uniformSample_equiv (powFieldsEquiv _)
              (fun z ↦ Sound.Batch.QueryBad S δ loss T0 z.1 z.2)
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
