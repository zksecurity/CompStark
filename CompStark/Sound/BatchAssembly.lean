/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.BatchSoundnessError
public import CompStark.Sound.Assembly
public import Mathlib.Data.Finset.Sort

/-! # Knowledge soundness of the batch STARK from its steps

If no tuple of close traces satisfies every AIR, some instance `i₀` has no close trace that
satisfies its AIR (`exists_failing_instance`). The acceptance probability averages, over `α`, `ζ`
and `a`, the constraint checks at `ζ` times FRI's acceptance of the batched DEEP words. For each
`(α, ζ)`, with `m₀` the log size of `i₀`'s domain:

* if the DEEP components of the opened words of the instances of size `m₀` are not
  `(δ' - 2/N)`-near the code on a common set, their batched word is `δ`-near for few `a`
  (`batchingStep`), and FRI rejects when it is `δ`-far, be it FRI's word or an injected one
  (`batchFriStep`): `batchingErrorOf + friErrorWith`;
* otherwise the components of instance `i₀`'s opened words, among them, are near on the same set
  (`nearTogether_instance`), and instance `i₀`'s check passes for few `ζ` unless `α` is one of few
  bad values (`exists_bad_alphas`): `foldingError + outOfDomainError` of instance `i₀`.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop Polynomial FriGame FriInject

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### The opened words -/

/-- A STARK's opened words are its main, quotient and preprocessed ones. -/
theorem openedWords_eq_append {S : Iop.Setup EF} (p : Iop.Prover S) (α ζ : 𝕂) :
    Iop.openedWords p α ζ =
      Batch.mainOpened p α ζ ++ Batch.quotientOpened p α ζ ++ Batch.preprocessedOpened p α ζ := by
  simp only [Iop.openedWords, Batch.mainOpened, Batch.quotientOpened, Batch.preprocessedOpened,
    List.append_assoc]

section Groups
variable {S : Batch.Setup EF}

/-- An instance's words, read on its own domain's size, are its words. -/
theorem onSize_self (i : Fin S.k) (words : List (((S.instanceSetup i).Point → F) × 𝕂 × 𝕂)) :
    Batch.onSize i (S.logN i + S.params.logBlowup) words = words := by
  rw [Batch.onSize, dite_eq_left rfl]
  conv_rhs => rw [← List.map_id words]
  rfl

theorem length_onSize (i : Fin S.k) (m : ℕ)
    (words : List (((S.instanceSetup i).Point → F) × 𝕂 × 𝕂)) :
    (Batch.onSize i m words).length =
      if S.logN i + S.params.logBlowup = m then words.length else 0 := by
  unfold Batch.onSize
  split_ifs <;> simp only [List.length_map, List.length_nil]

/-- The opened words of the instances of a domain size number `groupNumOpened`. -/
theorem length_groupOpened (p : Batch.Prover S) (α ζ : 𝕂) (m : ℕ) :
    (Batch.groupOpened p α ζ m).length = S.groupNumOpened m := by
  have h (i : Fin S.k) : (Batch.mainOpened (p.instanceProver i) α ζ).length +
      (Batch.quotientOpened (p.instanceProver i) α ζ).length +
      (Batch.preprocessedOpened (p.instanceProver i) α ζ).length =
        (S.instanceSetup i).numOpened := by
    rw [← List.length_append, ← List.length_append, ← openedWords_eq_append, length_openedWords]
  rw [Batch.groupOpened, List.length_append, List.length_append, List.length_flatMap,
    List.length_flatMap, List.length_flatMap, ← Fin.sum_univ_def, ← Fin.sum_univ_def,
    ← Fin.sum_univ_def, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Batch.Setup.groupNumOpened, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [length_onSize]
  split_ifs
  · exact h i
  · rfl

/-- Every instance's opened word is an opened word of its domain's size. -/
theorem mem_groupOpened (p : Batch.Prover S) (α ζ : 𝕂) (i : Fin S.k)
    {w : ((S.instanceSetup i).Point → F) × 𝕂 × 𝕂}
    (hw : w ∈ Iop.openedWords (p.instanceProver i) α ζ) :
    w ∈ Batch.groupOpened p α ζ (S.logN i + S.params.logBlowup) := by
  rw [openedWords_eq_append] at hw
  have hi := List.mem_finRange i
  rcases List.mem_append.mp hw with h | h
  · rcases List.mem_append.mp h with h | h
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr
        ⟨i, hi, (onSize_self i _).symm ▸ h⟩))
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨i, hi, (onSize_self i _).symm ▸ h⟩))
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, hi, (onSize_self i _).symm ▸ h⟩)

/-- The DEEP components of the opened words of instance `i`'s domain size, by position. -/
noncomputable def groupComponents (p : Batch.Prover S) (α ζ : 𝕂) (i : Fin S.k) :
    Fin (S.groupNumOpened (S.logN i + S.params.logBlowup)) → (S.instanceSetup i).Point → 𝕂 :=
  fun k ↦
    let w := (Batch.groupOpened p α ζ (S.logN i + S.params.logBlowup))[k.val]'(by
      rw [length_groupOpened]; exact k.isLt)
    deepComponent (S.instanceSetup i) w.1 w.2.1 w.2.2

/-- The batched DEEP word of instance `i`'s domain size is the combination of the components by
the powers of `a`. -/
theorem groupDeepWord_eq (p : Batch.Prover S) (α ζ a : 𝕂) (i : Fin S.k) :
    Batch.groupDeepWord p α ζ a (S.logN i + S.params.logBlowup) =
      fun x ↦ ∑ k : Fin (S.groupNumOpened (S.logN i + S.params.logBlowup)),
        a ^ (k : Nat) * groupComponents p α ζ i k x := by
  funext x
  refine Eq.trans ?_ (sum_zipIdx_deep (S.instanceSetup i) _ (length_groupOpened p α ζ _) a x)
  unfold Batch.groupDeepWord
  congr 1
  refine List.map_congr_left fun w _ ↦ ?_
  obtain ⟨⟨f, z, y⟩, k⟩ := w
  rw [domain_eq]

/-- If the components of instance `i`'s domain size are near on a common set, so are instance
`i`'s. -/
theorem nearTogether_instance (p : Batch.Prover S) (α ζ : 𝕂) (i : Fin S.k) (δ : ℝ)
    (h : NearTogether (S.instanceSetup i) δ (groupComponents p α ζ i)) :
    NearTogether (S.instanceSetup i) δ (components (p.instanceProver i) α ζ) := by
  obtain ⟨T, hT, hnear⟩ := h
  refine ⟨T, hT, fun k ↦ ?_⟩
  have hk : k.val < (Iop.openedWords (p.instanceProver i) α ζ).length := by
    rw [length_openedWords]; exact k.isLt
  obtain ⟨k', hk', hw⟩ := List.mem_iff_getElem.mp
    (mem_groupOpened p α ζ i (List.getElem_mem hk))
  obtain ⟨u, hu, hTu⟩ := hnear ⟨k', by rw [← length_groupOpened p α ζ]; exact hk'⟩
  refine ⟨u, hu, fun x hx ↦ ?_⟩
  rw [← hTu x hx]
  simp only [components, groupComponents, hw]

end Groups

/-! ### FRI on the batched words -/

section Fri
variable (S : Batch.Setup EF)

/-- The log sizes where FRI injects are those of the shorter instances' domains. -/
theorem mem_friHeights (m : ℕ) :
    m ∈ S.friHeights ↔ ∃ i, S.logN i + S.params.logBlowup = m ∧
      m ≠ S.logN S.top + S.params.logBlowup := by
  simp only [Batch.Setup.friHeights, Finset.mem_sort, Finset.mem_erase, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, i, hi⟩
    exact ⟨i, hi, hne⟩
  · rintro ⟨i, hi, hne⟩
    exact ⟨hne, i, hi⟩

/-- The sizes where FRI injects fit below the tallest domain and above the final one. -/
theorem fits_friHeights :
    Rounds.Fits (S.params.logFinalPolyLen + S.params.logBlowup)
      (S.logN S.top + S.params.logBlowup) S.friHeights := by
  refine ⟨?_, fun m hm ↦ ?_⟩
  · refine ((Finset.pairwise_sort _ _).and (Finset.sort_nodup _ _)).imp fun h ↦ ?_
    exact lt_of_le_of_ne h.1 (Ne.symm h.2)
  · obtain ⟨i, rfl, hne⟩ := (mem_friHeights S m).mp hm
    have := S.logN_le_top i
    have := S.folds i
    omega

/-- A word near the code agrees with it on `(1 - δ) N` points. -/
theorem agrees_of_near (T : Iop.Setup EF) (δ : ℝ) (w : T.Point → 𝕂) (h : Near T δ w) :
    Agrees T.domain T.n (1 - δ) w := by
  obtain ⟨A, hA, v, hv, hvA⟩ := h
  refine ⟨A, ?_, v, hv, fun x hx ↦ (hvA x hx).symm⟩
  rw [ge_iff_le, Iop.Setup.size, Nat.cast_pow, Nat.cast_ofNat, mul_comm] at hA
  exact hA

/-- **FRI rejects a far batched word.** If the batched DEEP word of instance `i`'s domain size is
not `δ`-near its code, FRI accepts with probability at most `friErrorWith`: it is FRI's word or an
injected one. -/
theorem batchFriStep (p : Batch.Prover S) (α ζ a : 𝕂) (δ : NNReal) (i : Fin S.k)
    (hfar : ¬ Near (S.instanceSetup i) δ
      (Batch.groupDeepWord p α ζ a (S.logN i + S.params.logBlowup))) :
    friAcceptanceWith S.domainSetup (Batch.groupDeepWord p α ζ a) S.friHeights
        (Batch.groupDeepWord p α ζ a _) ≤
      friErrorWith S.domainSetup S.friHeights δ := by
  have hfar' : ∀ hm, ¬ Agrees (cosetDomain (EF := EF) (S.logN i + S.params.logBlowup) hm)
      (2 ^ (S.logN i + S.params.logBlowup - S.params.logBlowup)) (1 - δ)
      (Batch.groupDeepWord p α ζ a (S.logN i + S.params.logBlowup)) := by
    intro hm hA
    rw [Nat.add_sub_cancel] at hA
    exact hfar (near_of_agrees (S.instanceSetup i) δ _ hA)
  refine friAcceptanceWith_le S.domainSetup _ _ (fits_friHeights S) _ δ ?_
  by_cases htop : S.logN i = S.logN S.top
  · left
    intro hnear
    rw [htop] at hfar'
    have hA := agrees_of_near S.domainSetup δ _ hnear
    refine hfar' S.domainSetup.valid.twoAdic ?_
    rw [Nat.add_sub_cancel]
    exact hA
  · right
    exact ⟨_, (mem_friHeights S _).mpr ⟨i, rfl, by omega⟩, hfar'⟩

end Fri

/-! ### The failing instance -/

/-- If no tuple of close traces satisfies every AIR, some instance has no close trace that
satisfies its AIR. -/
theorem exists_failing_instance {S : Batch.Setup EF} (publicValues : Fin S.k → List F)
    (p : Batch.Prover S) (δ : ℝ)
    (hfail : ∀ traces ∈ Batch.closeTraces S δ p.trace,
      ¬ ∀ i, (S.air i).Satisfied (S.logN i) (traces i) (publicValues i)) :
    ∃ i, ∀ P ∈ candidates (S.instanceSetup i) δ (p.trace i),
      ¬ (S.air i).Satisfied (S.logN i) (traceOf (S.instanceSetup i) P) (publicValues i) := by
  by_contra h
  simp only [not_exists, not_forall, not_not] at h
  choose P hP hsat using h
  exact hfail (fun i ↦ traceOf (S.instanceSetup i) (P i))
    (fun i ↦ ⟨P i, (hP i).1, (hP i).2, rfl⟩) hsat

/-! ### Summing over the challenges -/

section Sums
variable {S : Batch.Setup EF} (publicValues : Fin S.k → List F) (p : Batch.Prover S)

open Classical

/-- For one `(α, ζ)`: `|𝕂| (batchingError + friError)` if a component of instance `i₀`'s domain
size is far, and `|𝕂|` if instance `i₀`'s check passes with near components. -/
theorem batch_sum_a_le (δ : NNReal) (δ' : ℝ) (α ζ : 𝕂) (i₀ : Fin S.k) :
    ∑ a : 𝕂, (if ∀ i, ConstraintsHoldAt (S.instanceSetup i) (publicValues i) α ζ
        (p.openings α ζ i) then friAcceptanceWith S.domainSetup (Batch.groupDeepWord p α ζ a)
          S.friHeights (Batch.groupDeepWord p α ζ a _) else 0) ≤
      card𝕂 EF * (batchingErrorOf (S.instanceSetup i₀)
          (S.groupNumOpened (S.logN i₀ + S.params.logBlowup)) δ δ' +
        friErrorWith S.domainSetup S.friHeights δ) +
        if NearTogether (S.instanceSetup i₀) δ' (groupComponents p α ζ i₀) ∧
          ConstraintsHoldAt (S.instanceSetup i₀) (publicValues i₀) α ζ (p.openings α ζ i₀)
        then card𝕂 EF else 0 := by
  set m := S.groupNumOpened (S.logN i₀ + S.params.logBlowup)
  have hle1 (a : 𝕂) : friAcceptanceWith S.domainSetup (Batch.groupDeepWord p α ζ a)
      S.friHeights (Batch.groupDeepWord p α ζ a _) ≤ 1 := acceptance_le_one _ _ _ _ _ _
  by_cases hH : ∀ i, ConstraintsHoldAt (S.instanceSetup i) (publicValues i) α ζ
    (p.openings α ζ i)
  · rw [Finset.sum_congr rfl fun a _ ↦ ite_eq_left hH]
    by_cases hG : NearTogether (S.instanceSetup i₀) δ' (groupComponents p α ζ i₀)
    · rw [ite_eq_left ⟨hG, hH i₀⟩]
      refine le_add_left ((Finset.sum_le_sum fun a _ ↦ hle1 a).trans ?_)
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    · rw [ite_eq_right fun h ↦ hG h.1, add_zero]
      have hb := batchingStep (S.instanceSetup i₀) m δ δ' (groupComponents p α ζ i₀) hG
      set P : 𝕂 → Prop := fun a ↦ Near (S.instanceSetup i₀) δ
        fun x ↦ ∑ k : Fin m, a ^ (k : Nat) * groupComponents p α ζ i₀ k x
      have hnear : ((Finset.univ.filter P).card : ENNReal) ≤
          card𝕂 EF * batchingErrorOf (S.instanceSetup i₀) m δ δ' := by
        have h := (ENNReal.div_le_iff_le_mul (Or.inl (card𝕂_ne_zero (EF := EF)))
          (Or.inl (card𝕂_ne_top (EF := EF)))).mp hb
        rwa [mul_comm] at h
      calc ∑ a : 𝕂, friAcceptanceWith S.domainSetup (Batch.groupDeepWord p α ζ a)
            S.friHeights (Batch.groupDeepWord p α ζ a _)
          ≤ ∑ a : 𝕂, ((if P a then 1 else 0) + friErrorWith S.domainSetup S.friHeights δ) := by
            refine Finset.sum_le_sum fun a _ ↦ ?_
            split_ifs with ha
            · exact (hle1 a).trans le_self_add
            · rw [zero_add]
              refine batchFriStep S p α ζ a δ i₀ ?_
              rw [groupDeepWord_eq]
              exact ha
        _ = (Finset.univ.filter P).card + card𝕂 EF * friErrorWith S.domainSetup S.friHeights δ := by
            rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const, Finset.card_univ,
              nsmul_eq_mul]
        _ ≤ card𝕂 EF * (batchingErrorOf (S.instanceSetup i₀) m δ δ' +
            friErrorWith S.domainSetup S.friHeights δ) := by
            rw [mul_add]; gcongr
  · rw [Finset.sum_congr rfl fun a _ ↦ ite_eq_right hH, Finset.sum_const_zero]
    exact bot_le

end Sums

open Classical in
/-- Knowledge soundness of the batch STARK, from the steps. -/
theorem batchAcceptance_le (S : Batch.Setup EF) (publicValues : Fin S.k → List F)
    (p : Batch.Prover S) (δ δ' : NNReal) (hδ' : (δ' : ℝ) < 1 - S.rate)
    (hfail : ∀ traces ∈ Batch.closeTraces S δ' p.trace,
      ¬ ∀ i, (S.air i).Satisfied (S.logN i) (traces i) (publicValues i)) :
    Batch.acceptance publicValues p ≤ Batch.knowledgeError S δ δ' := by
  obtain ⟨i₀, hfail₀⟩ := exists_failing_instance publicValues p δ' hfail
  set I := S.instanceSetup i₀
  have hrate : I.rate = S.rate := by
    rw [Iop.Setup.rate, Batch.Setup.rate, Iop.Setup.n, Iop.Setup.size, pow_add, Nat.cast_mul]
    have : ((2 ^ S.logN i₀ : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  obtain ⟨bad, hbad, hgood⟩ := exists_bad_alphas (publicValues i₀) (p.instanceProver i₀) δ'
    (hrate ▸ hδ') hfail₀
  set ℓT := I.listSize (Fin I.air.width) δ'
  set ℓQ := I.listSize (Fin I.chunks × Fin (Challenge.d EF)) δ'
  set E := batchingErrorOf I (S.groupNumOpened (S.logN i₀ + S.params.logBlowup)) δ
      ((δ' : ℝ) - 2 / I.size) + friErrorWith S.domainSetup S.friHeights δ
  set D := I.identityDegree
  -- The `ζ` with near components and instance `i₀`'s check passing, for one `α`.
  have hcount : ∀ α : 𝕂, ((Finset.univ.filter fun ζ : 𝕂 ↦
      NearTogether I ((δ' : ℝ) - 2 / I.size) (groupComponents p α ζ i₀) ∧
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
        then friAcceptanceWith S.domainSetup (Batch.groupDeepWord p α ζ a) S.friHeights
          (Batch.groupDeepWord p α ζ a _) else 0) ≤
      card𝕂 EF ^ 2 * E + card𝕂 EF * (I.n + ((if α ∈ bad then card𝕂 EF else 0) +
        (ℓT * ℓQ * D : Nat))) := by
    intro α
    refine (Finset.sum_le_sum fun ζ _ ↦
      batch_sum_a_le publicValues p δ ((δ' : ℝ) - 2 / I.size) α ζ i₀).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      ← mul_assoc, ← pow_two, mul_comm _ (card𝕂 EF)]
    exact add_le_add le_rfl (mul_le_mul_right (hcount α) _)
  -- Summing over `α`.
  have hsum : ∑ α : 𝕂, ∑ ζ : 𝕂, ∑ a : 𝕂,
      (if ∀ i, ConstraintsHoldAt (S.instanceSetup i) (publicValues i) α ζ (p.openings α ζ i)
        then friAcceptanceWith S.domainSetup (Batch.groupDeepWord p α ζ a) S.friHeights
          (Batch.groupDeepWord p α ζ a _) else 0) ≤
      card𝕂 EF ^ 3 * E + card𝕂 EF ^ 2 * (I.n + bad.card + (ℓT * ℓQ * D : Nat)) := by
    refine (Finset.sum_le_sum fun α _ ↦ hα α).trans_eq ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.sum_const, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
    ring
  -- The error of instance `i₀`'s challenges `α` and `ζ`.
  have hI : ((I.n + bad.card + (ℓT * ℓQ * D : Nat) : ENNReal)) / card𝕂 EF ≤
      foldingError I δ' + outOfDomainError I δ' := by
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
    _ ≤ E + (foldingError I δ' + outOfDomainError I δ') := add_le_add le_rfl hI
    _ = S.instanceError δ δ' i₀ + friErrorWith S.domainSetup S.friHeights δ := by
        rw [Batch.Setup.instanceError]
        ring
    _ ≤ Batch.knowledgeError S δ δ' :=
        add_le_add (le_iSup (fun i ↦ S.instanceError δ δ' i) i₀) le_rfl

end CompStark.Sound
