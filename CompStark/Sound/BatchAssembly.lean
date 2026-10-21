/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.BatchSoundnessError
public import CompStark.Sound.Assembly

/-! # Knowledge soundness of the batch STARK from its steps

If no tuple of close traces satisfies every AIR, some instance `i₀` has no close trace that
satisfies its AIR (`exists_failing_instance`). The acceptance probability averages, over `α`, `ζ`
and `a`, the constraint checks at `ζ` times FRI's acceptance of the batched DEEP word. For each
`(α, ζ)`:

* if the DEEP components of all opened words are not `(δ' - 2/N)`-near the code on a common set,
  the batched word is `δ`-near for few `a` (`batchingStep`), and FRI rejects `δ`-far words
  (`friStep`): `batchingErrorOf + friError`;
* otherwise the components of instance `i₀`'s opened words, among them, are near on the same set
  (`nearTogether_instance`), and instance `i₀`'s check passes for few `ζ` unless `α` is one of few
  bad values (`exists_bad_alphas`): `foldingError + outOfDomainError` of instance `i₀`.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop Polynomial

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### The opened words -/

/-- A STARK's opened words are its main, quotient and preprocessed ones. -/
theorem openedWords_eq_append {S : Iop.Setup EF} (p : Iop.Prover S) (α ζ : 𝕂) :
    Iop.openedWords p α ζ =
      Batch.mainOpened p α ζ ++ Batch.quotientOpened p α ζ ++ Batch.preprocessedOpened p α ζ := by
  simp only [Iop.openedWords, Batch.mainOpened, Batch.quotientOpened, Batch.preprocessedOpened,
    List.append_assoc]

theorem length_batchOpenedWords {S : Batch.Setup EF} (p : Batch.Prover S) (α ζ : 𝕂) :
    (Batch.openedWords p α ζ).length = S.numOpened := by
  have h (i : Fin S.k) : (Batch.mainOpened (p.instanceProver i) α ζ).length +
      (Batch.quotientOpened (p.instanceProver i) α ζ).length +
      (Batch.preprocessedOpened (p.instanceProver i) α ζ).length =
        (S.instanceSetup i).numOpened := by
    rw [← List.length_append, ← List.length_append, ← openedWords_eq_append, length_openedWords]
  rw [Batch.openedWords, List.length_append, List.length_append, List.length_flatMap,
    List.length_flatMap, List.length_flatMap, ← Fin.sum_univ_def, ← Fin.sum_univ_def,
    ← Fin.sum_univ_def, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ h i

/-- Every instance's opened word is an opened word of the batch. -/
theorem mem_batchOpenedWords {S : Batch.Setup EF} (p : Batch.Prover S) (α ζ : 𝕂) (i : Fin S.k)
    {w : (S.Point → F) × 𝕂 × 𝕂} (hw : w ∈ Iop.openedWords (p.instanceProver i) α ζ) :
    w ∈ Batch.openedWords p α ζ := by
  rw [openedWords_eq_append] at hw
  have hi := List.mem_finRange i
  rcases List.mem_append.mp hw with h | h
  · rcases List.mem_append.mp h with h | h
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨i, hi, h⟩))
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, hi, h⟩))
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, hi, h⟩)

/-- The DEEP components of the batch's opened words, by position. -/
noncomputable def batchComponents {S : Batch.Setup EF} (p : Batch.Prover S) (α ζ : 𝕂) :
    Fin S.numOpened → S.Point → 𝕂 := fun k ↦
  let w := (Batch.openedWords p α ζ)[k.val]'(by
    rw [length_batchOpenedWords]; exact k.isLt)
  deepComponent S.domainSetup w.1 w.2.1 w.2.2

/-- The batched DEEP word is the combination of the components by the powers of `a`. -/
theorem batchDeepWord_eq {S : Batch.Setup EF} (p : Batch.Prover S) (α ζ a : 𝕂) :
    Batch.deepWord p α ζ a =
      fun i ↦ ∑ k : Fin S.numOpened, a ^ (k : Nat) * batchComponents p α ζ k i :=
  funext fun i ↦ sum_zipIdx_deep S.domainSetup _ (length_batchOpenedWords p α ζ) a i

/-- If the batch's DEEP components are near on a common set, so are every instance's. -/
theorem nearTogether_instance {S : Batch.Setup EF} (p : Batch.Prover S) (α ζ : 𝕂) (i : Fin S.k)
    (δ : ℝ) (h : NearTogether S.domainSetup δ (batchComponents p α ζ)) :
    NearTogether (S.instanceSetup i) δ (components (p.instanceProver i) α ζ) := by
  obtain ⟨T, hT, hnear⟩ := h
  refine ⟨T, hT, fun k ↦ ?_⟩
  have hk : k.val < (Iop.openedWords (p.instanceProver i) α ζ).length := by
    rw [length_openedWords]; exact k.isLt
  obtain ⟨k', hk', hw⟩ := List.mem_iff_getElem.mp
    (mem_batchOpenedWords p α ζ i (List.getElem_mem hk))
  obtain ⟨u, hu, hTu⟩ := hnear ⟨k', by rw [← length_batchOpenedWords p α ζ]; exact hk'⟩
  refine ⟨u, hu, fun x hx ↦ ?_⟩
  rw [← hTu x hx]
  simp only [components, batchComponents, hw]
  rfl

/-! ### The failing instance -/

/-- If no tuple of close traces satisfies every AIR, some instance has no close trace that
satisfies its AIR. -/
theorem exists_failing_instance {S : Batch.Setup EF} (publicValues : Fin S.k → List F)
    (p : Batch.Prover S) (δ : ℝ)
    (hfail : ∀ traces ∈ Batch.closeTraces S δ p.trace,
      ¬ ∀ i, (S.air i).Satisfied S.logN (traces i) (publicValues i)) :
    ∃ i, ∀ P ∈ candidates (S.instanceSetup i) δ (p.trace i),
      ¬ (S.air i).Satisfied S.logN (traceOf (S.instanceSetup i) P) (publicValues i) := by
  by_contra h
  simp only [not_exists, not_forall, not_not] at h
  choose P hP hsat using h
  exact hfail (fun i ↦ traceOf (S.instanceSetup i) (P i))
    (fun i ↦ ⟨P i, (hP i).1, (hP i).2, rfl⟩) hsat

/-! ### Summing over the challenges -/

section Sums
variable {S : Batch.Setup EF} (publicValues : Fin S.k → List F) (p : Batch.Prover S)

open Classical

/-- For one `(α, ζ)`: `|𝕂| (batchingError + friError)` if a component is far, and `|𝕂|` if
instance `i₀`'s check passes with near components. -/
theorem batch_sum_a_le (δ : NNReal) (δ' : ℝ) (α ζ : 𝕂) (i₀ : Fin S.k) :
    ∑ a : 𝕂, (if ∀ i, ConstraintsHoldAt (S.instanceSetup i) (publicValues i) α ζ
        (p.openings α ζ i) then friAcceptance S.domainSetup (Batch.deepWord p α ζ a) else 0) ≤
      card𝕂 EF * (batchingErrorOf S.domainSetup S.numOpened δ δ' + friError S.domainSetup δ) +
        if NearTogether S.domainSetup δ' (batchComponents p α ζ) ∧
          ConstraintsHoldAt (S.instanceSetup i₀) (publicValues i₀) α ζ (p.openings α ζ i₀)
        then card𝕂 EF else 0 := by
  by_cases hH : ∀ i, ConstraintsHoldAt (S.instanceSetup i) (publicValues i) α ζ
    (p.openings α ζ i)
  · rw [Finset.sum_congr rfl fun a _ ↦ ite_eq_left hH]
    by_cases hG : NearTogether S.domainSetup δ' (batchComponents p α ζ)
    · rw [ite_eq_left ⟨hG, hH i₀⟩]
      refine le_add_left ((Finset.sum_le_sum fun a _ ↦ friAtMostOne S.domainSetup _).trans ?_)
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    · rw [ite_eq_right fun h ↦ hG h.1, add_zero]
      have hb := batchingStep S.domainSetup S.numOpened δ δ' (batchComponents p α ζ) hG
      set P : 𝕂 → Prop := fun a ↦ Near S.domainSetup δ
        fun i ↦ ∑ k : Fin S.numOpened, a ^ (k : Nat) * batchComponents p α ζ k i
      have hnear : ((Finset.univ.filter P).card : ENNReal) ≤
          card𝕂 EF * batchingErrorOf S.domainSetup S.numOpened δ δ' := by
        have h := (ENNReal.div_le_iff_le_mul (Or.inl (card𝕂_ne_zero (EF := EF)))
          (Or.inl (card𝕂_ne_top (EF := EF)))).mp hb
        rwa [mul_comm] at h
      calc ∑ a : 𝕂, friAcceptance S.domainSetup (Batch.deepWord p α ζ a)
          ≤ ∑ a : 𝕂, ((if P a then 1 else 0) + friError S.domainSetup δ) := by
            refine Finset.sum_le_sum fun a _ ↦ ?_
            split_ifs with ha
            · exact (friAtMostOne S.domainSetup _).trans le_self_add
            · rw [zero_add, batchDeepWord_eq]
              exact friStep S.domainSetup δ _ ha
        _ = (Finset.univ.filter P).card + card𝕂 EF * friError S.domainSetup δ := by
            rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const, Finset.card_univ,
              nsmul_eq_mul]
        _ ≤ card𝕂 EF * (batchingErrorOf S.domainSetup S.numOpened δ δ' +
            friError S.domainSetup δ) := by
            rw [mul_add]; gcongr
  · rw [Finset.sum_congr rfl fun a _ ↦ ite_eq_right hH, Finset.sum_const_zero]
    exact bot_le

end Sums

open Classical in
/-- Knowledge soundness of the batch STARK, from the steps. -/
theorem batchAcceptance_le (S : Batch.Setup EF) (publicValues : Fin S.k → List F)
    (p : Batch.Prover S) (δ δ' : NNReal) (hδ' : (δ' : ℝ) < 1 - S.rate)
    (hfail : ∀ traces ∈ Batch.closeTraces S δ' p.trace,
      ¬ ∀ i, (S.air i).Satisfied S.logN (traces i) (publicValues i)) :
    Batch.acceptance publicValues p ≤ Batch.knowledgeError S δ δ' := by
  obtain ⟨i₀, hfail₀⟩ := exists_failing_instance publicValues p δ' hfail
  set I := S.instanceSetup i₀
  obtain ⟨bad, hbad, hgood⟩ := exists_bad_alphas (publicValues i₀) (p.instanceProver i₀) δ' hδ'
    hfail₀
  set ℓT := I.listSize (Fin I.air.width) δ'
  set ℓQ := I.listSize (Fin I.chunks × Fin (Challenge.d EF)) δ'
  set E := batchingErrorOf S.domainSetup S.numOpened δ ((δ' : ℝ) - 2 / S.size) +
    friError S.domainSetup δ
  set D := I.identityDegree
  -- The `ζ` with near components and instance `i₀`'s check passing, for one `α`.
  have hcount : ∀ α : 𝕂, ((Finset.univ.filter fun ζ : 𝕂 ↦
      NearTogether S.domainSetup ((δ' : ℝ) - 2 / S.size) (batchComponents p α ζ) ∧
        ConstraintsHoldAt I (publicValues i₀) α ζ (p.openings α ζ i₀)).card : ENNReal) ≤
      I.n + ((if α ∈ bad then card𝕂 EF else 0) + (ℓT * ℓQ * D : Nat)) := by
    intro α
    by_cases hα : α ∈ bad
    · simp only [hα, ↓reduceIte]
      refine le_trans ?_ (le_add_left le_self_add)
      exact Nat.cast_le.mpr (Finset.card_le_univ _)
    simp only [hα, ↓reduceIte, zero_add]
    rw [← Nat.cast_add]
    refine Nat.cast_le.mpr ((Finset.card_le_card fun ζ hζ ↦ ?_).trans (hgood α hα))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ ⊢
    exact ⟨nearTogether_instance p α ζ i₀ _ hζ.1, hζ.2⟩
  -- Summing over `a` and `ζ`, for one `α`.
  have hα : ∀ α : 𝕂, ∑ ζ : 𝕂, ∑ a : 𝕂,
      (if ∀ i, ConstraintsHoldAt (S.instanceSetup i) (publicValues i) α ζ (p.openings α ζ i)
        then friAcceptance S.domainSetup (Batch.deepWord p α ζ a) else 0) ≤
      card𝕂 EF ^ 2 * E + card𝕂 EF * (I.n + ((if α ∈ bad then card𝕂 EF else 0) +
        (ℓT * ℓQ * D : Nat))) := by
    intro α
    refine (Finset.sum_le_sum fun ζ _ ↦
      batch_sum_a_le publicValues p δ ((δ' : ℝ) - 2 / S.size) α ζ i₀).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      ← mul_assoc, ← pow_two, mul_comm _ (card𝕂 EF)]
    exact add_le_add le_rfl (mul_le_mul_right (hcount α) _)
  -- Summing over `α`.
  have hsum : ∑ α : 𝕂, ∑ ζ : 𝕂, ∑ a : 𝕂,
      (if ∀ i, ConstraintsHoldAt (S.instanceSetup i) (publicValues i) α ζ (p.openings α ζ i)
        then friAcceptance S.domainSetup (Batch.deepWord p α ζ a) else 0) ≤
      card𝕂 EF ^ 3 * E + card𝕂 EF ^ 2 * (I.n + bad.card + (ℓT * ℓQ * D : Nat)) := by
    refine (Finset.sum_le_sum fun α _ ↦ hα α).trans_eq ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.sum_const, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
    ring
  -- The error of instance `i₀`'s challenges `α` and `ζ`.
  have hI : ((I.n + bad.card + (ℓT * ℓQ * D : Nat) : ENNReal)) / card𝕂 EF ≤
      ⨆ i, foldingError (S.instanceSetup i) δ' + outOfDomainError (S.instanceSetup i) δ' := by
    refine le_iSup_of_le i₀ ?_
    have key : (I.n + bad.card + (ℓT * ℓQ * D : Nat) : ENNReal) ≤
        ((ℓT * (I.air.constraints.length - 1) : Nat) : ENNReal) + ((ℓT * ℓQ * D + I.n : Nat) :
          ENNReal) := by
      have hbad' : bad.card ≤ ℓT * (I.air.constraints.length - 1) := hbad
      have hk : I.n + bad.card + ℓT * ℓQ * D ≤
          ℓT * (I.air.constraints.length - 1) + (ℓT * ℓQ * D + I.n) := by omega
      exact_mod_cast hk
    refine (ENNReal.div_le_div_right key (card𝕂 EF)).trans_eq ?_
    rw [← ENNReal.div_add_div_same, foldingError, outOfDomainError]
  calc Batch.acceptance publicValues p
      ≤ (card𝕂 EF)⁻¹ ^ 3 * (card𝕂 EF ^ 3 * E +
          card𝕂 EF ^ 2 * (I.n + bad.card + (ℓT * ℓQ * D : Nat))) :=
        mul_le_mul_right hsum _
    _ = E + (I.n + bad.card + (ℓT * ℓQ * D : Nat)) / card𝕂 EF := inv_cube_mul _ _
    _ ≤ E + ⨆ i, foldingError (S.instanceSetup i) δ' + outOfDomainError (S.instanceSetup i) δ' :=
        add_le_add le_rfl hI
    _ = Batch.knowledgeError S δ δ' := by
        rw [Batch.knowledgeError]
        ring

end CompStark.Sound
