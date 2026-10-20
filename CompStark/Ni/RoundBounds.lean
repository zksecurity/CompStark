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
probability at most `3 q / |𝔽|^8` after fewer than `q` queries (`prob_digestClash_le`), for the
digests of the keys: a compression's two children, a duplex call's capacity and the digest a
commitment round observes (`keyDigests`).
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop CompStark.RandomOracle
open Polynomial Montgomery.Native32 Fri.Spec OracleSpec OracleComp
open KoalaBear.Fast (Ext4)
open scoped ENNReal

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4
local notation "𝔽" => KoalaBear.Field
local notation "𝕂" => KoalaBear.Ext4

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
    Pr{let u ← $ᵗ (Digest × Vector F K)}[P fun j ↦ u.2.toList.getD j.val 0] =
      Pr{let x ← $ᵗ (Fin m → F)}[P x] := by
  have h := SampleableType.prEvent_uniformSample_equiv (Equiv.prodComm Digest (Vector F K))
    (fun z ↦ P fun j ↦ z.1.toList.getD j.val 0)
  simp only [Equiv.prodComm_apply, Prod.fst_swap] at h
  rw [h, SampleableType.prEvent_uniformSample_fst
    (p := fun v : Vector F K ↦ P fun j ↦ v.toList.getD j.val 0), prob_vector_prefix K m hm]

/-- Four samples as an element of `𝕂`, lowest coefficient first. -/
noncomputable def extEquiv : (Fin 4 → F) ≃ 𝕂 where
  toFun x := Ext4.specEquiv ⟨x 0, x 1, x 2, x 3⟩
  invFun a := ![(Ext4.specEquiv.symm a).c0, (Ext4.specEquiv.symm a).c1,
    (Ext4.specEquiv.symm a).c2, (Ext4.specEquiv.symm a).c3]
  left_inv x := by
    funext j
    fin_cases j <;> simp only [RingEquiv.symm_apply_apply] <;> rfl
  right_inv a := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]
    exact Ext4.specEquiv.apply_symm_apply a

theorem extAt_eq (K : Nat) (v : Vector F K) (offset : Nat) :
    extAt v offset = extEquiv fun j ↦ v.toList.getD (offset + j.val) 0 := rfl

/-- A grinding sample and four samples as a pair in `𝔽 × 𝕂`. -/
noncomputable def powExtEquiv : (Fin 5 → F) ≃ 𝔽 × 𝕂 :=
  (Fin.consEquiv fun _ ↦ F).symm.trans
    (Equiv.prodCongr KoalaBear.Fast.ringEquiv.toEquiv extEquiv)

theorem powExtEquiv_apply (x : Fin 5 → F) :
    powExtEquiv x = (FastField.toField (x 0), extEquiv fun j ↦ x j.succ) := rfl

/-- Samples as elements of `𝔽`. -/
noncomputable def fieldsEquiv (n : Nat) : (Fin n → F) ≃ (Fin n → 𝔽) :=
  Equiv.arrowCongr (Equiv.refl _) KoalaBear.Fast.ringEquiv.toEquiv

/-- A grinding sample and `n` samples, in `𝔽`. -/
noncomputable def powFieldsEquiv (n : Nat) : (Fin (n + 1) → F) ≃ 𝔽 × (Fin n → 𝔽) :=
  (Fin.consEquiv fun _ ↦ F).symm.trans
    (Equiv.prodCongr KoalaBear.Fast.ringEquiv.toEquiv (fieldsEquiv n))

theorem powFraction_zero : powFraction 0 = 1 := by
  rw [powFraction, Nat.sub_zero, ← card_field, ENNReal.div_self
    (by simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true])
    (ENNReal.natCast_ne_top _)]

theorem prEvent_congr_iff {α : Type} (mx : ProbComp α) {p q : α → Prop} (h : ∀ x, p x ↔ q x) :
    Pr{let x ← mx}[p x] = Pr{let x ← mx}[q x] := by
  have : p = q := funext fun x ↦ propext (h x)
  rw [this]

theorem getD_append_singleton {α : Type} (l : List α) (x d : α) (j : Nat) (hj : j = l.length) :
    (l ++ [x]).getD j d = x := by
  subst hj
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
    List.getElem?_cons_zero, Option.getD_some]

theorem getD_append_singleton_lt {α : Type} (l : List α) (x d : α) (j : Nat) (hj : j < l.length) :
    (l ++ [x]).getD j d = l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

/-! ### The rounds' errors -/

section Bounds
variable (S : Iop.Setup) (publicValues : List F) (δ δ' loss : NNReal)

/-- The largest round error at proximity loss `loss`; `roundError` is its infimum. -/
noncomputable def roundBound : ENNReal :=
  max (foldingError S δ') <| max (outOfDomainError S δ') <|
    max (batchingError S δ ((δ' : ℝ) - 2 / S.size)) <|
    max (powFraction S.params.commitPowBits * ⨆ i, friFoldError S δ loss i)
      (powFraction S.params.queryPowBits * friQueryError S δ loss)

theorem roundError_eq : roundError S δ δ' = ⨅ loss, roundBound S δ δ' loss := rfl

theorem streamLen_eq : S.streamLen = S.params.numQueries + 5 := rfl

/-- **One fresh answer.** The bad event of round `i` on the prefix transcript of `i` earlier
rounds, the answer to round `i` uniform, has probability at most the round's error. -/
theorem prob_roundBadAt_le (cache : Merkle.Cache F Digest) (block : Nat → List F)
    (samples : List (Vector F S.streamLen)) :
    Pr{let u ← $ᵗ (Digest × Vector F S.streamLen)}[roundBadAt S publicValues δ δ' loss
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
    calc _ = Pr{let u ← $ᵗ (Digest × Vector F S.streamLen)}[(fun x ↦
          AlphaBad S publicValues δ' tr (extEquiv x)) fun j ↦ u.2.toList.getD j.val 0] :=
          prEvent_congr_iff _ fun u ↦ by
            simp only [prefixTranscript, tr, getD_append_singleton samples u.2 d 0 h0.symm,
              extAt_eq, Nat.zero_add]
      _ = Pr{let a ← $ᵗ 𝕂}[AlphaBad S publicValues δ' tr a] := by
          rw [prob_answer_prefix _ 4 (by omega)]
          exact SampleableType.prEvent_uniformSample_equiv extEquiv _
      _ ≤ foldingError S δ' := prob_alphaBad_le S publicValues δ' tr
      _ ≤ _ := le_max_left _ _
  · -- `ζ`
    set T := prefixTranscript S cache block fun j ↦ samples.getD j d
    calc _ = Pr{let u ← $ᵗ (Digest × Vector F S.streamLen)}[(fun x ↦
          ZetaBad S publicValues δ' T.trace T.alpha T.quotient (extEquiv x))
            fun j ↦ u.2.toList.getD j.val 0] :=
          prEvent_congr_iff _ fun u ↦ by
            simp only [prefixTranscript, T, getD_append_singleton samples u.2 d 1 h1.symm,
              getD_append_singleton_lt samples u.2 d 0 (by omega), extAt_eq, Nat.zero_add]
      _ = Pr{let a ← $ᵗ 𝕂}[ZetaBad S publicValues δ' T.trace T.alpha T.quotient a] := by
          rw [prob_answer_prefix _ 4 (by omega)]
          exact SampleableType.prEvent_uniformSample_equiv extEquiv _
      _ ≤ outOfDomainError S δ' := prob_zetaBad_le S publicValues δ' _ _ _
      _ ≤ _ := (le_max_left _ _).trans (le_max_right _ _)
  · -- batching
    set T := prefixTranscript S cache block fun j ↦ samples.getD j d
    calc _ = Pr{let u ← $ᵗ (Digest × Vector F S.streamLen)}[(fun x ↦
          BatchBad S δ δ' T.trace T.alpha T.quotient T.zeta T.openings (extEquiv x))
            fun j ↦ u.2.toList.getD j.val 0] :=
          prEvent_congr_iff _ fun u ↦ by
            simp only [prefixTranscript, T, getD_append_singleton samples u.2 d 2 h2.symm,
              getD_append_singleton_lt samples u.2 d 0 (by omega),
              getD_append_singleton_lt samples u.2 d 1 (by omega), extAt_eq, Nat.zero_add]
      _ = Pr{let a ← $ᵗ 𝕂}[BatchBad S δ δ' T.trace T.alpha T.quotient T.zeta T.openings a] := by
          rw [prob_answer_prefix _ 4 (by omega)]
          exact SampleableType.prEvent_uniformSample_equiv extEquiv _
      _ ≤ batchingError S δ ((δ' : ℝ) - 2 / S.size) := prob_batchBad_le S δ δ' _ _ _ _ _
      _ ≤ _ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · -- fold `i - 3`
    set f : Fin (S.lastFold + 1) := ⟨i - 3, hf⟩
    set T := prefixTranscript S cache block fun j ↦ samples.getD j d
    set c := lift gen ^ 2 ^ foldingPrefix S.schedule f.castSucc
    have hc : c ≠ 0 := pow_ne_zero _ lift_gen_ne_zero
    have hβ (v : Vector F S.streamLen) :
        (prefixTranscript S cache block fun j ↦ (samples ++ [v]).getD j d).betas f =
          c * extAt v (challengeOffset S.params.commitPowBits) := by
      simp only [prefixTranscript, betasAt, c, f]
      rw [getD_append_singleton samples v d _ (by simp only [f]; omega)]
    have hfri (v : Vector F S.streamLen) :
        (prefixTranscript S cache block fun j ↦ (samples ++ [v]).getD j d).fri = T.fri := rfl
    have hle : powFraction S.params.commitPowBits * friFoldError S δ loss f ≤
        roundBound S δ δ' loss :=
      (mul_le_mul_right (le_iSup (friFoldError S δ loss) f) _).trans
        ((le_max_left _ _).trans ((le_max_right _ _).trans
          ((le_max_right _ _).trans (le_max_right _ _))))
    refine le_trans ?_ hle
    by_cases hb : S.params.commitPowBits = 0
    · calc _ = Pr{let u ← $ᵗ (Digest × Vector F S.streamLen)}[(fun x ↦
            FoldBad S δ loss f T.fri (c * extEquiv x)) fun j ↦ u.2.toList.getD j.val 0] :=
            prEvent_congr_iff _ fun u ↦ by
              rw [hβ, hfri]
              simp only [hb, ne_eq, not_true_eq_false, IsEmpty.forall_iff, true_and,
                challengeOffset, ↓reduceIte, extAt_eq, Nat.zero_add, f]
        _ = Pr{let a ← $ᵗ 𝕂}[FoldBad S δ loss f T.fri a] := by
            rw [prob_answer_prefix _ 4 (by omega)]
            rw [SampleableType.prEvent_uniformSample_equiv extEquiv
              (fun a ↦ FoldBad S δ loss f T.fri (c * a))]
            exact SampleableType.prEvent_uniformSample_equiv (Equiv.mulLeft₀ c hc) _
        _ ≤ friFoldError S δ loss f := prob_foldBad_le S δ loss f T.fri
        _ = _ := by rw [hb, powFraction_zero, one_mul]
    · calc _ = Pr{let u ← $ᵗ (Digest × Vector F S.streamLen)}[(fun x ↦
            (powExtEquiv x).1.val % 2 ^ S.params.commitPowBits = 0 ∧
              FoldBad S δ loss f T.fri (c * (powExtEquiv x).2))
              fun j ↦ u.2.toList.getD j.val 0] :=
            prEvent_congr_iff _ fun u ↦ by
              rw [hβ, hfri]
              simp only [hb, ne_eq, not_false_eq_true, forall_const, challengeOffset,
                ↓reduceIte, extAt_eq, powExtEquiv_apply, Fin.val_zero, Fin.val_succ, f]
              simp only [Nat.add_comm 1]
        _ = Pr{let z ← $ᵗ (𝔽 × 𝕂)}[z.1.val % 2 ^ S.params.commitPowBits = 0 ∧
              FoldBad S δ loss f T.fri z.2] := by
            rw [prob_answer_prefix _ 5 (by omega)]
            rw [SampleableType.prEvent_uniformSample_equiv powExtEquiv
              (fun z ↦ z.1.val % 2 ^ S.params.commitPowBits = 0 ∧
                FoldBad S δ loss f T.fri (c * z.2))]
            exact SampleableType.prEvent_uniformSample_equiv
              (Equiv.prodCongr (Equiv.refl 𝔽) (Equiv.mulLeft₀ c hc))
              (fun z ↦ z.1.val % 2 ^ S.params.commitPowBits = 0 ∧ FoldBad S δ loss f T.fri z.2)
        _ ≤ _ := prob_foldRound_le S δ loss f T.fri
  · -- the queries
    set T := prefixTranscript S cache block fun j ↦ samples.getD j d
    have hT (v : Vector F S.streamLen) :
        (prefixTranscript S cache block fun j ↦ (samples ++ [v]).getD j d) = T :=
      prefixTranscript_sample_congr S cache block fun j hj ↦
        getD_append_singleton_lt samples v d j (by omega)
    have hle : powFraction S.params.queryPowBits * friQueryError S δ loss ≤
        roundBound S δ δ' loss :=
      (le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))
    refine le_trans ?_ hle
    refine le_trans (le_of_eq ?_) (prob_queryBad_le S δ loss T)
    by_cases hb : S.params.queryPowBits = 0
    · have hpow (a : 𝔽) (q : Fin S.params.numQueries → 𝔽) :
          QueryBad S δ loss T a q ↔ QueryBad S δ loss T 0 q := by
        simp only [QueryBad, hb, pow_zero, Nat.mod_one]
      calc _ = Pr{let u ← $ᵗ (Digest × Vector F S.streamLen)}[(fun x ↦
            QueryBad S δ loss T 0 (fieldsEquiv _ x)) fun j ↦ u.2.toList.getD j.val 0] :=
            prEvent_congr_iff _ fun u ↦ by
              rw [hT]
              simp only [powAt, queriesAt, hb, challengeOffset, ↓reduceIte, Nat.zero_add]
              rfl
        _ = Pr{let q ← $ᵗ (Fin S.params.numQueries → 𝔽)}[QueryBad S δ loss T 0 q] := by
            rw [prob_answer_prefix _ _ (by omega)]
            exact SampleableType.prEvent_uniformSample_equiv (fieldsEquiv _) _
        _ = _ := by
            rw [prEvent_congr_iff _ fun z ↦ hpow z.1 z.2]
            have h := SampleableType.prEvent_uniformSample_equiv
              (Equiv.prodComm 𝔽 (Fin S.params.numQueries → 𝔽))
              (fun z ↦ QueryBad S δ loss T 0 z.1)
            simp only [Equiv.prodComm_apply, Prod.fst_swap] at h
            rw [h, SampleableType.prEvent_uniformSample_fst
              (p := fun q ↦ QueryBad S δ loss T 0 q)]
    · calc _ = Pr{let u ← $ᵗ (Digest × Vector F S.streamLen)}[(fun x ↦
            QueryBad S δ loss T (powFieldsEquiv _ x).1 (powFieldsEquiv _ x).2)
              fun j ↦ u.2.toList.getD j.val 0] :=
            prEvent_congr_iff _ fun u ↦ by
              rw [hT]
              simp only [powAt, queriesAt, hb, challengeOffset, ↓reduceIte]
              simp only [Nat.add_comm 1]
              rfl
        _ = _ := by
            rw [prob_answer_prefix _ _ (by omega)]
            exact SampleableType.prEvent_uniformSample_equiv (powFieldsEquiv _)
              (fun z ↦ QueryBad S δ loss T z.1 z.2)
  · simp only [prEvent_false, zero_le]

/-- **A fresh duplex answer.** After any queries `pre`, a uniform answer to any call is
round-bad with probability at most the largest round error. -/
theorem prob_roundBad_le (pre : QueryLog (spec S.streamLen)) (t : Query) :
    Pr{let u ← $ᵗ (Answer S.streamLen t)}[RoundBad S publicValues δ δ' loss pre t u] ≤
      roundBound S δ δ' loss := by
  cases t with
  | duplex cap input =>
    cases hparse : parse pre (.duplex cap input) with
    | none => simp only [RoundBad, hparse, prEvent_false, zero_le]
    | some r =>
      obtain ⟨steps, rest⟩ := r
      simp only [RoundBad, hparse]
      have h := prob_roundBadAt_le S publicValues δ δ' loss (logCache pre)
        (fun j ↦ (steps.map Prod.fst ++ [input]).getD j []) (steps.map Prod.snd)
      rw [List.length_map] at h
      exact h
  | leaf row => simp only [RoundBad, prEvent_false, zero_le]
  | node left right => simp only [RoundBad, prEvent_false, zero_le]

end Bounds

/-! ### Digest clashes -/

/-- `|Digest| = |𝔽| ^ 8`. -/
theorem card_digest : Fintype.card Digest = Fintype.card 𝔽 ^ 8 := by
  rw [Fintype.card_congr (arrayVectorEquivFin F 8), Fintype.card_fun, Fintype.card_fin,
    Fintype.card_congr KoalaBear.Fast.ringEquiv.toEquiv]

/-- An answer's digest is uniform. -/
theorem prob_digestOf_eq_le (K : Nat) (t : Query) (x : Digest) :
    Pr{let u ← $ᵗ (Answer K t)}[digestOf t u = x] ≤ (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  cases t with
  | duplex cap input => exact (prEvent_uniformSample_fst_eq (β := Vector F K) x).le
  | leaf row => exact (SampleableType.prEvent_uniformSample_eq_singleton x).le
  | node left right => exact (SampleableType.prEvent_uniformSample_eq_singleton x).le

/-- A fresh answer after fewer than `n` queries clashes with probability at most
`3 n / |Digest|`. -/
theorem prob_clash_le (K n : Nat) (pre : QueryLog (spec K)) (hpre : pre.length < n)
    (t : Query) :
    Pr{let u ← $ᵗ (Answer K t)}[Clash pre t u] ≤
      (3 * n : ℕ) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  refine (prEvent_digestClash_le digestOf (prob_digestOf_eq_le K) keyDigests 2
    length_keyDigests_le [initCap] pre t).trans ?_
  gcongr
  simp only [List.length_cons, List.length_nil]
  omega

end CompStark.Ni
