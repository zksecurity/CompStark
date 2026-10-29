/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.Rounds
public import CompStark.Ni.FirstQueries

/-! # The bad events of one fresh answer

A fresh answer to a duplex call is a uniform capacity and `K` uniform samples, and a round reads
its challenges off the first samples. So the bad event of round `i` on the prefix parsed before
the call has probability at most round `i`'s error (`prob_roundBad_le`), whatever the earlier
queries: the prefix transcript is fixed by them, and the samples are carried to the challenges by
bijections (`prob_answer_prefix`, `extEquiv`). The fold rounds' challenges are Plonky3's, scaled by
a nonzero shift to ArkLib's coordinate, another bijection.

The answer's digest (a hash, or the duplex's new capacity) clashes with the known digests with
probability at most `3 q / |F|^8` after fewer than `q` queries (`prob_digestClash_le`), for the
digests of the keys: a compression's two children, a duplex call's capacity and the digest a
commitment round observes (`keyDigests`).
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop CompStark.RandomOracle
open Polynomial Fri.Spec OracleSpec OracleComp
open scoped ENNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### Uniform samples -/

/-- The first `m` samples of a uniform stream are uniform. -/
theorem prob_vector_prefix (K m : Nat) (hm : m ≤ K) (P : (Fin m → F) → Prop) :
    Pr{let v ← $ᵗ (Vector F K)}[P fun j ↦ v.toList.getD j.val 0] =
      Pr{let x ← $ᵗ (Fin m → F)}[P x] := by
  let e : Vector F K ≃ (Fin m → F) × (Fin (K - m) → F) :=
    (arrayVectorEquivFin F K).trans ((Equiv.arrowCongr (finCongr (by omega : K = m + (K - m)))
      (Equiv.refl F)).trans ((Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl F)).trans
        (Equiv.sumArrowEquivProdArrow _ _ _)))
  have he : ∀ v, (e v).1 = fun j ↦ v.toList.getD j.val 0 := by
    intro v
    funext j
    have hj : j.val < K := by omega
    simp only [e, Equiv.trans_apply, Equiv.sumArrowEquivProdArrow_apply_fst, Function.comp_apply,
      Equiv.arrowCongr_apply, Equiv.symm_symm, finSumFinEquiv_apply_left, Equiv.refl_apply,
      arrayVectorEquivFin, Equiv.coe_fn_mk, finCongr_symm, finCongr_apply, Fin.val_cast,
      Fin.val_castAdd, List.getD_eq_getElem?_getD, Vector.getElem?_toList,
      Vector.getElem?_eq_getElem hj, Option.getD_some]
  have h := SampleableType.prEvent_uniformSample_equiv e (fun z ↦ P z.1)
  simp only [he] at h
  rw [h, SampleableType.prEvent_uniformSample_fst]

/-- The first `m` samples of a uniform answer to a duplex call are uniform. -/
theorem prob_answer_prefix (K m : Nat) (hm : m ≤ K) (P : (Fin m → F) → Prop) :
    Pr{let u ← $ᵗ (Digest F × Vector F K)}[P fun j ↦ u.2.toList.getD j.val 0] =
      Pr{let x ← $ᵗ (Fin m → F)}[P x] := by
  have h := SampleableType.prEvent_uniformSample_equiv (Equiv.prodComm (Digest F) (Vector F K))
    (fun z ↦ P fun j ↦ z.1.toList.getD j.val 0)
  simp only [Equiv.prodComm_apply, Prod.fst_swap] at h
  rw [h, SampleableType.prEvent_uniformSample_fst
    (p := fun v : Vector F K ↦ P fun j ↦ v.toList.getD j.val 0), prob_vector_prefix K m hm]

/-- `d` samples as an element of `𝕂`, lowest coefficient first. -/
noncomputable def extEquiv : (Fin (Challenge.d EF) → F) ≃ 𝕂 :=
  (Equiv.arrowCongr (Equiv.refl _) (Equiv.refl F)).trans
    (CompPoly.Extension.Ext.equivFn (Challenge.params EF)).symm

theorem extAt_eq (K : Nat) (v : Vector F K) (offset : Nat) :
    (extAt v offset : 𝕂) = extEquiv fun j ↦ v.toList.getD (offset + j.val) 0 := rfl

/-- A grinding sample and `d` samples as a pair in `F × 𝕂`. -/
noncomputable def powExtEquiv : (Fin (Challenge.d EF + 1) → F) ≃ F × 𝕂 :=
  (Fin.consEquiv fun _ ↦ F).symm.trans
    (Equiv.prodCongr (Equiv.refl F) extEquiv)

theorem powExtEquiv_apply (x : Fin (Challenge.d EF + 1) → F) :
    powExtEquiv x = ((x 0), extEquiv fun j ↦ x j.succ) := rfl

/-- Samples as elements of `F`. -/
noncomputable def fieldsEquiv (n : Nat) : (Fin n → F) ≃ (Fin n → F) :=
  Equiv.arrowCongr (Equiv.refl _) (Equiv.refl F)

/-- A grinding sample and `n` samples, in `F`. -/
noncomputable def powFieldsEquiv (n : Nat) : (Fin (n + 1) → F) ≃ F × (Fin n → F) :=
  (Fin.consEquiv fun _ ↦ F).symm.trans
    (Equiv.prodCongr (Equiv.refl F) (fieldsEquiv n))

theorem prEvent_congr_iff {α : Type} (mx : ProbComp α) {p q : α → Prop} (h : ∀ x, p x ↔ q x) :
    Pr{let x ← mx}[p x] = Pr{let x ← mx}[q x] := by
  have : p = q := funext fun x ↦ propext (h x)
  rw [this]

/-- An extension element read at any offset of a uniform answer is uniform. -/
theorem prob_extAt (K o : Nat) (ho : o + Challenge.d EF ≤ K) (P : 𝕂 → Prop) :
    Pr{let u ← $ᵗ (Digest F × Vector F K)}[P (extAt u.2 o)] = Pr{let a ← $ᵗ 𝕂}[P a] := by
  let e : (Fin (o + Challenge.d EF) → F) ≃ (Fin o → F) × (Fin (Challenge.d EF) → F) :=
    (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl F)).trans
      (Equiv.sumArrowEquivProdArrow _ _ _)
  have he : ∀ x : Fin (o + Challenge.d EF) → F, (e x).2 = fun j ↦ x (Fin.natAdd o j) := by
    intro x
    funext j
    simp only [e, Equiv.trans_apply, Equiv.sumArrowEquivProdArrow_apply_snd, Function.comp_apply,
      Equiv.arrowCongr_apply, Equiv.symm_symm, finSumFinEquiv_apply_right, Equiv.refl_apply]
  calc _ = Pr{let u ← $ᵗ (Digest F × Vector F K)}[(fun x ↦ P (extEquiv (e x).2))
        fun j ↦ u.2.toList.getD j.val 0] :=
        prEvent_congr_iff _ fun u ↦ by
          dsimp only
          rw [he, extAt_eq]
          rfl
    _ = Pr{let x ← $ᵗ (Fin (o + Challenge.d EF) → F)}[P (extEquiv (e x).2)] :=
        prob_answer_prefix (F := F) K _ ho (fun x ↦ P (extEquiv (e x).2))
    _ = Pr{let y ← $ᵗ ((Fin o → F) × (Fin (Challenge.d EF) → F))}[P (extEquiv y.2)] :=
        SampleableType.prEvent_uniformSample_equiv e (fun y ↦ P (extEquiv y.2))
    _ = Pr{let z ← $ᵗ (Fin (Challenge.d EF) → F)}[P (extEquiv z)] := by
        have h := SampleableType.prEvent_uniformSample_equiv
          (Equiv.prodComm (Fin o → F) (Fin (Challenge.d EF) → F)) (fun z ↦ P (extEquiv z.1))
        simp only [Equiv.prodComm_apply, Prod.fst_swap] at h
        rw [h]
        exact SampleableType.prEvent_uniformSample_fst (fun z ↦ P (extEquiv z))
    _ = _ := SampleableType.prEvent_uniformSample_equiv extEquiv P

/-- A grinding sample, an answer's first sample, with `bits` vanishing low bits, and an event on
the extension element read after it: at most `powFraction bits` times the event's probability. -/
theorem prob_grindExt_le (K bits : Nat) (hK : Challenge.d EF + 1 ≤ K) (P : 𝕂 → Prop) :
    Pr{let u ← $ᵗ (Digest F × Vector F K)}[(bits ≠ 0 →
      CompPoly.CanonicalNat.toNat (u.2.toList.getD 0 0) % 2 ^ bits = 0) ∧
        P (extAt u.2 (challengeOffset bits))] ≤ powFraction F bits * Pr{let a ← $ᵗ 𝕂}[P a] := by
  classical
  by_cases hb : bits = 0
  · calc _ = Pr{let u ← $ᵗ (Digest F × Vector F K)}[P (extAt u.2 0)] :=
          prEvent_congr_iff _ fun u ↦ by
            simp only [hb, ne_eq, not_true_eq_false, IsEmpty.forall_iff, true_and,
              challengeOffset, ↓reduceIte]
      _ = Pr{let a ← $ᵗ 𝕂}[P a] := prob_extAt K 0 (by omega) P
      _ ≤ _ := by rw [hb, powFraction_zero, one_mul]
  · calc _ = Pr{let u ← $ᵗ (Digest F × Vector F K)}[(fun x ↦
          CompPoly.CanonicalNat.toNat (powExtEquiv x).1 % 2 ^ bits = 0 ∧ P (powExtEquiv x).2)
            fun j ↦ u.2.toList.getD j.val 0] :=
          prEvent_congr_iff _ fun u ↦ by
            simp only [hb, ne_eq, not_false_eq_true, forall_const, challengeOffset,
              ↓reduceIte, extAt_eq, powExtEquiv_apply, Fin.val_zero, Fin.val_succ]
            simp only [Nat.add_comm 1]
      _ = Pr{let z ← $ᵗ (F × 𝕂)}[CompPoly.CanonicalNat.toNat z.1 % 2 ^ bits = 0 ∧ P z.2] :=
          (prob_answer_prefix K (Challenge.d EF + 1) hK (fun x ↦
            CompPoly.CanonicalNat.toNat (powExtEquiv x).1 % 2 ^ bits = 0 ∧
              P (powExtEquiv x).2)).trans
            (SampleableType.prEvent_uniformSample_equiv powExtEquiv
              (fun z ↦ CompPoly.CanonicalNat.toNat z.1 % 2 ^ bits = 0 ∧ P z.2))
      _ ≤ _ := prob_pow_and_le bits P

theorem challengeOffset_le_one (bits : Nat) : challengeOffset bits ≤ 1 := by
  unfold challengeOffset; split <;> omega

theorem getD_append_singleton {α : Type} (l : List α) (x d : α) (j : Nat) (hj : j = l.length) :
    (l ++ [x]).getD j d = x := by
  subst hj
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
    List.getElem?_cons_zero, Option.getD_some]

theorem getD_append_singleton_lt {α : Type} (l : List α) (x d : α) (j : Nat) (hj : j < l.length) :
    (l ++ [x]).getD j d = l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem prefixTranscript_betas_eq (S : Iop.Setup EF)
    (cache : Merkle.Cache F (Digest F))
    (block : Nat → List F) (sample : Nat → Vector F S.streamLen) :
    (prefixTranscript S cache block sample).betas = betasAt S sample := rfl

theorem prefixTranscript_fri_eq (S : Iop.Setup EF) (cache : Merkle.Cache F (Digest F))
    (block : Nat → List F) (sample sample' : Nat → Vector F S.streamLen) :
    (prefixTranscript S cache block sample).fri = (prefixTranscript S cache block sample').fri :=
  rfl

/-! ### The rounds' errors -/

section Bounds
variable (S : Iop.Setup EF) (publicValues : List F) (δ δ' loss : NNReal)

/-- The largest round error at proximity loss `loss`; `roundError` is its infimum. -/
noncomputable def roundBound : ENNReal :=
  max (foldingError S δ') <| max (powFraction F S.params.oodPowBits * outOfDomainError S δ') <|
    max (powFraction F S.params.batchPowBits * batchingError S δ δ') <|
    max (powFraction F S.params.commitPowBits * ⨆ i, friFoldError S δ loss i)
      (powFraction F S.params.queryPowBits * friQueryError S δ loss)

theorem roundError_eq : roundError S δ δ' = ⨅ loss, roundBound S δ δ' loss := rfl

theorem streamLen_eq : S.streamLen = S.params.numQueries + Challenge.d EF + 1 := rfl

/-- **One fresh answer.** The bad event of round `i` on the prefix transcript of `i` earlier
rounds, the answer to round `i` uniform, has probability at most the round's error. -/
theorem prob_roundBadAt_le (cache : Merkle.Cache F (Digest F)) (block : Nat → List F)
    (samples : List (Vector F S.streamLen)) :
    Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[roundBadAt S publicValues δ δ' loss
      samples.length (prefixTranscript S cache block
        fun j ↦ (samples ++ [u.2]).getD j (Vector.replicate _ 0)) u.2] ≤
      roundBound S δ δ' loss := by
  set d := Vector.replicate S.streamLen (0 : F)
  set i := samples.length with hi
  have hK := streamLen_eq S
  unfold roundBadAt
  split_ifs with h0 h1 h2 hf hq
  · -- `α`
    set tr := (prefixTranscript S cache block fun j ↦ samples.getD j d).trace
    calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(fun x ↦
          AlphaBad S publicValues δ' tr (extEquiv x)) fun j ↦ u.2.toList.getD j.val 0] :=
          prEvent_congr_iff _ fun u ↦ by
            simp only [prefixTranscript, tr, getD_append_singleton samples u.2 d 0 h0.symm,
              extAt_eq, Nat.zero_add]
      _ = Pr{let a ← $ᵗ 𝕂}[AlphaBad S publicValues δ' tr a] := by
          refine (prob_answer_prefix S.streamLen (Challenge.d EF) (by omega)
            (fun x ↦ AlphaBad S publicValues δ' tr (extEquiv x))).trans ?_
          exact SampleableType.prEvent_uniformSample_equiv (extEquiv (EF := EF))
            (fun a ↦ AlphaBad S publicValues δ' tr a)
      _ ≤ foldingError S δ' := prob_alphaBad_le S publicValues [] 0 δ' tr
      _ ≤ _ := le_max_left _ _
  · -- `ζ`
    set T := prefixTranscript S cache block fun j ↦ samples.getD j d
    calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(S.params.oodPowBits ≠ 0 →
          CompPoly.CanonicalNat.toNat (u.2.toList.getD 0 0) % 2 ^ S.params.oodPowBits = 0) ∧
          ZetaBad S publicValues δ' T.trace T.alpha T.quotient
            (extAt u.2 (challengeOffset S.params.oodPowBits))] :=
          prEvent_congr_iff _ fun u ↦ by
            simp only [prefixTranscript, T, getD_append_singleton samples u.2 d 1 h1.symm,
              getD_append_singleton_lt samples u.2 d 0 (by omega)]
      _ ≤ powFraction F S.params.oodPowBits * outOfDomainError S δ' :=
          (prob_grindExt_le S.streamLen _ (by omega) _).trans
            (mul_le_mul_right (prob_zetaBad_le S publicValues [] 0 δ' _ _ _) _)
      _ ≤ _ := (le_max_left _ _).trans (le_max_right _ _)
  · -- batching
    set T := prefixTranscript S cache block fun j ↦ samples.getD j d
    calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(S.params.batchPowBits ≠ 0 →
          CompPoly.CanonicalNat.toNat (u.2.toList.getD 0 0) % 2 ^ S.params.batchPowBits = 0) ∧
          BatchBad S δ δ' T.trace T.alpha T.quotient T.zeta T.openings
            (extAt u.2 (challengeOffset S.params.batchPowBits))] :=
          prEvent_congr_iff _ fun u ↦ by
            simp only [prefixTranscript, T, getD_append_singleton samples u.2 d 2 h2.symm,
              getD_append_singleton_lt samples u.2 d 0 (by omega),
              getD_append_singleton_lt samples u.2 d 1 (by omega)]
      _ ≤ powFraction F S.params.batchPowBits * batchingError S δ δ' :=
          (prob_grindExt_le S.streamLen _ (by omega) _).trans
            (mul_le_mul_right (prob_batchBad_le S δ δ' _ _ _ _ _) _)
      _ ≤ _ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · -- fold `i - 3`
    obtain ⟨f, hfeq⟩ : ∃ f : Fin (S.lastFold + 1), f = ⟨i - 3, hf⟩ := ⟨_, rfl⟩
    rw [← hfeq]
    have hi3 : 3 + f.val = samples.length := by
      have : f.val = i - 3 := by rw [hfeq]
      omega
    obtain ⟨c, hc_def⟩ : ∃ c : 𝕂, c = lift gen ^ 2 ^ foldingPrefix S.schedule f.castSucc :=
      ⟨_, rfl⟩
    have hc : c ≠ 0 := by rw [hc_def]; exact pow_ne_zero _ lift_gen_ne_zero
    have hβ (v : Vector F S.streamLen) :
        (prefixTranscript S cache block fun j ↦ (samples ++ [v]).getD j d).betas f =
          c * extAt v (challengeOffset S.params.commitPowBits) := by
      rw [prefixTranscript_betas_eq, betasAt, getD_append_singleton samples v d _ hi3, hc_def]
    obtain ⟨fri, hfri_def⟩ :
        ∃ fri, fri = (prefixTranscript S cache block fun j ↦ samples.getD j d).fri :=
      ⟨_, rfl⟩
    have hfri (v : Vector F S.streamLen) :
        (prefixTranscript S cache block fun j ↦ (samples ++ [v]).getD j d).fri = fri := by
      rw [hfri_def, prefixTranscript_fri_eq]
    have hle : powFraction F S.params.commitPowBits * friFoldError S δ loss f ≤
        roundBound S δ δ' loss :=
      (mul_le_mul_right (le_iSup (friFoldError S δ loss) f) _).trans
        ((le_max_left _ _).trans ((le_max_right _ _).trans
          ((le_max_right _ _).trans (le_max_right _ _))))
    refine le_trans ?_ hle
    simp only [hβ, hfri]
    by_cases hb : S.params.commitPowBits = 0
    · calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(fun x ↦
            FoldBad S δ loss f fri (c * extEquiv x)) fun j ↦ u.2.toList.getD j.val 0] :=
            prEvent_congr_iff _ fun u ↦ by
              simp only [hb, ne_eq, not_true_eq_false, IsEmpty.forall_iff, true_and,
                challengeOffset, ↓reduceIte, extAt_eq, Nat.zero_add]
        _ = Pr{let a ← $ᵗ 𝕂}[FoldBad S δ loss f fri a] := by
            refine (prob_answer_prefix S.streamLen (Challenge.d EF) (by omega)
              (fun x ↦ FoldBad S δ loss f fri (c * extEquiv x))).trans ?_
            refine (SampleableType.prEvent_uniformSample_equiv extEquiv
              (fun a ↦ FoldBad S δ loss f fri (c * a))).trans ?_
            exact SampleableType.prEvent_uniformSample_equiv (Equiv.mulLeft₀ c hc) _
        _ ≤ friFoldError S δ loss f := prob_foldBad_le S δ loss f fri
        _ = _ := by rw [hb, powFraction_zero, one_mul]
    · calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(fun x ↦
            CompPoly.CanonicalNat.toNat (powExtEquiv x).1 % 2 ^ S.params.commitPowBits = 0 ∧
              FoldBad S δ loss f fri (c * (powExtEquiv x).2))
              fun j ↦ u.2.toList.getD j.val 0] :=
            prEvent_congr_iff _ fun u ↦ by
              simp only [hb, ne_eq, not_false_eq_true, forall_const, challengeOffset,
                ↓reduceIte, extAt_eq, powExtEquiv_apply, Fin.val_zero, Fin.val_succ]
              simp only [Nat.add_comm 1]
        _ = Pr{let z ← $ᵗ (F × 𝕂)}[
              CompPoly.CanonicalNat.toNat z.1 % 2 ^ S.params.commitPowBits = 0 ∧
              FoldBad S δ loss f fri z.2] := by
            refine (prob_answer_prefix S.streamLen (Challenge.d EF + 1) (by omega) (fun x ↦
              CompPoly.CanonicalNat.toNat (powExtEquiv x).1 % 2 ^ S.params.commitPowBits = 0 ∧
                FoldBad S δ loss f fri (c * (powExtEquiv x).2))).trans ?_
            refine (SampleableType.prEvent_uniformSample_equiv powExtEquiv
              (fun z ↦ CompPoly.CanonicalNat.toNat z.1 % 2 ^ S.params.commitPowBits = 0 ∧
                FoldBad S δ loss f fri (c * z.2))).trans ?_
            exact SampleableType.prEvent_uniformSample_equiv
              (Equiv.prodCongr (Equiv.refl F) (Equiv.mulLeft₀ c hc))
              (fun z ↦ CompPoly.CanonicalNat.toNat z.1 % 2 ^ S.params.commitPowBits = 0 ∧
                FoldBad S δ loss f fri z.2)
        _ ≤ _ := prob_foldRound_le S δ loss f fri
  · -- the queries
    set T := prefixTranscript S cache block fun j ↦ samples.getD j d
    have hT (v : Vector F S.streamLen) :
        (prefixTranscript S cache block fun j ↦ (samples ++ [v]).getD j d) = T :=
      prefixTranscript_sample_congr S cache block fun j hj ↦
        getD_append_singleton_lt samples v d j (by omega)
    have hle : powFraction F S.params.queryPowBits * friQueryError S δ loss ≤
        roundBound S δ δ' loss :=
      (le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))
    refine le_trans ?_ hle
    refine le_trans (le_of_eq ?_) (prob_queryBad_le S δ loss T)
    by_cases hb : S.params.queryPowBits = 0
    · have hpow (a : F) (q : Fin S.params.numQueries → F) :
          QueryBad S δ loss T a q ↔ QueryBad S δ loss T 0 q := by
        simp only [QueryBad, hb, pow_zero, Nat.mod_one]
      calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(fun x ↦
            QueryBad S δ loss T 0 (fieldsEquiv _ x)) fun j ↦ u.2.toList.getD j.val 0] :=
            prEvent_congr_iff _ fun u ↦ by
              have hp : powAt S u.2 = 0 := by simp only [powAt, hb, ↓reduceIte]
              have hqs : queriesAt S u.2 =
                  fieldsEquiv _ (fun j : Fin S.params.numQueries ↦ u.2.toList.getD j.val 0) := by
                funext j
                simp only [queriesAt, challengeOffset, hb, ↓reduceIte, Nat.zero_add]
                rfl
              rw [hT, hp, hqs]
        _ = Pr{let q ← $ᵗ (Fin S.params.numQueries → F)}[QueryBad S δ loss T 0 q] := by
            refine (prob_answer_prefix S.streamLen S.params.numQueries (by omega)
              (fun x ↦ QueryBad S δ loss T 0 (fieldsEquiv _ x))).trans ?_
            exact SampleableType.prEvent_uniformSample_equiv (fieldsEquiv _) _
        _ = _ := by
            refine Eq.trans ?_ (prEvent_congr_iff ($ᵗ (F × (Fin S.params.numQueries → F)))
              fun z ↦ hpow z.1 z.2).symm
            have h := SampleableType.prEvent_uniformSample_equiv
              (Equiv.prodComm F (Fin S.params.numQueries → F))
              (fun z ↦ QueryBad S δ loss T 0 z.1)
            simp only [Equiv.prodComm_apply, Prod.fst_swap] at h
            rw [h, SampleableType.prEvent_uniformSample_fst
              (p := fun q ↦ QueryBad S δ loss T 0 q)]
    · calc _ = Pr{let u ← $ᵗ (Digest F × Vector F S.streamLen)}[(fun x ↦
            QueryBad S δ loss T (powFieldsEquiv _ x).1 (powFieldsEquiv _ x).2)
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
              (fun x ↦ QueryBad S δ loss T (powFieldsEquiv _ x).1 (powFieldsEquiv _ x).2)).trans ?_
            exact SampleableType.prEvent_uniformSample_equiv (powFieldsEquiv _)
              (fun z ↦ QueryBad S δ loss T z.1 z.2)
  · simp only [prEvent_false, zero_le]

/-- **A fresh duplex answer.** After any queries `pre`, a uniform answer to any call is
round-bad with probability at most the largest round error. -/
theorem prob_roundBad_le (pre : QueryLog (spec F S.streamLen)) (t : Query F) :
    Pr{let u ← $ᵗ (Answer S.streamLen t)}[RoundBad S publicValues δ δ' loss pre t u] ≤
      roundBound S δ δ' loss := by
  cases t with
  | duplex cap input =>
    cases hparse : parse pre (.duplex cap input) with
    | none =>
      refine le_of_eq_of_le (prEvent_congr_iff _ fun u ↦ (?_ : _ ↔ False)) ?_
      · unfold RoundBad
        dsimp only
        rw [hparse]
      · simp only [prEvent_false, zero_le]
    | some r =>
      obtain ⟨steps, rest⟩ := r
      have h := prob_roundBadAt_le S publicValues δ δ' loss (logCache pre)
        (fun j ↦ (steps.map Prod.fst ++ [input]).getD j []) (steps.map Prod.snd)
      rw [List.length_map] at h
      refine le_trans (prEvent_mono _ _ _ fun u hu ↦ ?_) h
      unfold RoundBad at hu
      dsimp only at hu
      rw [hparse] at hu
      exact hu.2
  | leaf row =>
    refine le_of_eq_of_le (prEvent_congr_iff _ fun u ↦ (Iff.rfl : _ ↔ False)) ?_
    simp only [prEvent_false, zero_le]
  | node left right =>
    refine le_of_eq_of_le (prEvent_congr_iff _ fun u ↦ (Iff.rfl : _ ↔ False)) ?_
    simp only [prEvent_false, zero_le]

end Bounds

/-! ### Digest clashes -/

/-- `|Digest| = |F| ^ 8`. -/
theorem card_digest : Fintype.card (Digest F) = Nat.card F ^ 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (arrayVectorEquivFin F 8), Fintype.card_fun,
    Fintype.card_fin]

/-- An answer's digest is uniform. -/
theorem prob_digestOf_eq_le (K : Nat) (t : Query F) (x : Digest F) :
    Pr{let u ← $ᵗ (Answer K t)}[digestOf t u = x] ≤ (Fintype.card (Digest F) : ℝ≥0∞)⁻¹ := by
  cases t with
  | duplex cap input => exact (prEvent_uniformSample_fst_eq (β := Vector F K) x).le
  | leaf row => exact (SampleableType.prEvent_uniformSample_eq_singleton x).le
  | node left right => exact (SampleableType.prEvent_uniformSample_eq_singleton x).le

/-- A fresh answer after fewer than `n` queries clashes with probability at most
`(m + 2) n / |Digest|`, if an input binds at most `m ≥ 1` digests. -/
theorem prob_clash_le (bd : Digest F → List F → List (Digest F)) (m : Nat) (hm : 1 ≤ m)
    (hbd : ∀ c i, (bd c i).length ≤ m) (K n : Nat)
    (pre : QueryLog (spec F K)) (hpre : pre.length < n) (t : Query F) :
    Pr{let u ← $ᵗ (Answer K t)}[Clash bd pre t u] ≤
      ((m + 2) * n : ℕ) * (Fintype.card (Digest F) : ℝ≥0∞)⁻¹ := by
  refine (prEvent_digestClash_le digestOf (prob_digestOf_eq_le K) (keyDigests bd) (m + 1)
    (length_keyDigests_le bd m hm hbd) [initCap] pre t).trans ?_
  gcongr
  simp only [List.length_cons, List.length_nil]
  calc 0 + 1 + (m + 1 + 1) * pre.length + (m + 1) = (m + 2) * (pre.length + 1) := by ring
    _ ≤ (m + 2) * n := Nat.mul_le_mul_left _ hpre

end CompStark.Ni
