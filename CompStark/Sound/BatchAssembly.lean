/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.BatchLogUp
public import Mathlib.Data.Finset.Sort

/-! # Knowledge soundness of the batch STARK from its steps

The acceptance probability averages, over the lookup challenges `(α_L, β_L)`, the acceptance at
them (`acceptanceAt`). If no tuple of close traces satisfies the batch, the pair is bad
(`LookupBad`) for few pairs (`card_lookupBad_le`). At any other pair at which the terminals sum
to zero, some instance `i₀` has no close trace and close permutation trace that satisfy all its
constraints (`exists_failing_instance`): otherwise the close traces satisfy every AIR, so their
buses do not balance, and the terminals sum to the messages' nonzero sum of fractions
(`sum_terminals_eq`). The acceptance at the pair averages, over `α`, `ζ` and `a`, the constraint
checks at `ζ` times FRI's acceptance of the batched DEEP words. For each `(α, ζ)`, with `m₀` the
log size of `i₀`'s domain:

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

/-- A STARK's opened words are its main, quotient, preprocessed and permutation ones. -/
theorem openedWords_eq_append {lookups : List (Lookup F)} {S : Iop.Setup EF lookups}
    (p : Iop.Prover S) (α ζ : 𝕂) :
    Iop.openedWords p α ζ = Batch.mainOpened p α ζ ++ Batch.quotientOpened p α ζ ++
      Batch.preprocessedOpened p α ζ ++ Batch.permOpened p α ζ := by
  simp only [Iop.openedWords, Batch.mainOpened, Batch.quotientOpened, Batch.preprocessedOpened,
    Batch.permOpened, List.append_assoc]

section Groups
variable {withLookups : Bool} {S : Batch.Setup EF withLookups}

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
theorem length_groupOpened (p : Batch.Prover S) (lα lβ α ζ : 𝕂) (m : ℕ) :
    (Batch.groupOpened p lα lβ α ζ m).length = S.groupNumOpened m := by
  have h (i : Fin S.k) : (Batch.mainOpened (p.instanceProver lα lβ i) α ζ).length +
      (Batch.quotientOpened (p.instanceProver lα lβ i) α ζ).length +
      (Batch.preprocessedOpened (p.instanceProver lα lβ i) α ζ).length +
      (Batch.permOpened (p.instanceProver lα lβ i) α ζ).length =
        (S.instanceSetup i).numOpened := by
    rw [← List.length_append, ← List.length_append, ← List.length_append,
      ← openedWords_eq_append, length_openedWords]
  rw [Batch.groupOpened, List.length_append, List.length_append, List.length_append,
    List.length_flatMap, List.length_flatMap, List.length_flatMap, List.length_flatMap,
    ← Fin.sum_univ_def, ← Fin.sum_univ_def, ← Fin.sum_univ_def, ← Fin.sum_univ_def,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Batch.Setup.groupNumOpened, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [length_onSize]
  split_ifs
  · exact h i
  · rfl

/-- Every instance's opened word is an opened word of its domain's size. -/
theorem mem_groupOpened (p : Batch.Prover S) (lα lβ α ζ : 𝕂) (i : Fin S.k)
    {w : ((S.instanceSetup i).Point → F) × 𝕂 × 𝕂}
    (hw : w ∈ Iop.openedWords (p.instanceProver lα lβ i) α ζ) :
    w ∈ Batch.groupOpened p lα lβ α ζ (S.logN i + S.params.logBlowup) := by
  rw [openedWords_eq_append] at hw
  have hi := List.mem_finRange i
  rw [Batch.groupOpened]
  simp only [List.mem_append] at hw ⊢
  rcases hw with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (List.mem_flatMap.mpr ⟨i, hi, (onSize_self i _).symm ▸ h⟩)))
  · exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨i, hi, (onSize_self i _).symm ▸ h⟩)))
  · exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨i, hi, (onSize_self i _).symm ▸ h⟩))
  · exact Or.inr (List.mem_flatMap.mpr ⟨i, hi, (onSize_self i _).symm ▸ h⟩)

/-- The DEEP components of the opened words of instance `i`'s domain size, by position. -/
noncomputable def groupComponents (p : Batch.Prover S) (lα lβ α ζ : 𝕂) (i : Fin S.k) :
    Fin (S.groupNumOpened (S.logN i + S.params.logBlowup)) → (S.instanceSetup i).Point → 𝕂 :=
  fun k ↦
    let w := (Batch.groupOpened p lα lβ α ζ (S.logN i + S.params.logBlowup))[k.val]'(by
      rw [length_groupOpened]; exact k.isLt)
    deepComponent (S.instanceSetup i) w.1 w.2.1 w.2.2

/-- The batched DEEP word of instance `i`'s domain size is the combination of the components by
the powers of `a`. -/
theorem groupDeepWord_eq (p : Batch.Prover S) (lα lβ α ζ a : 𝕂) (i : Fin S.k) :
    Batch.groupDeepWord p lα lβ α ζ a (S.logN i + S.params.logBlowup) =
      fun x ↦ ∑ k : Fin (S.groupNumOpened (S.logN i + S.params.logBlowup)),
        a ^ (k : Nat) * groupComponents p lα lβ α ζ i k x := by
  funext x
  refine Eq.trans ?_ (sum_zipIdx_deep (S.instanceSetup i) _
    (length_groupOpened p lα lβ α ζ _) a x)
  unfold Batch.groupDeepWord
  congr 1
  refine List.map_congr_left fun w _ ↦ ?_
  obtain ⟨⟨f, z, y⟩, k⟩ := w
  rw [domain_eq]

/-- If the components of instance `i`'s domain size are near on a common set, so are instance
`i`'s. -/
theorem nearTogether_instance (p : Batch.Prover S) (lα lβ α ζ : 𝕂) (i : Fin S.k) (δ : ℝ)
    (h : NearTogether (S.instanceSetup i) δ (groupComponents p lα lβ α ζ i)) :
    NearTogether (S.instanceSetup i) δ (components (p.instanceProver lα lβ i) α ζ) := by
  obtain ⟨T, hT, hnear⟩ := h
  refine ⟨T, hT, fun k ↦ ?_⟩
  have hk : k.val < (Iop.openedWords (p.instanceProver lα lβ i) α ζ).length := by
    rw [length_openedWords]; exact k.isLt
  obtain ⟨k', hk', hw⟩ := List.mem_iff_getElem.mp
    (mem_groupOpened p lα lβ α ζ i (List.getElem_mem hk))
  obtain ⟨u, hu, hTu⟩ := hnear ⟨k', by rw [← length_groupOpened p lα lβ α ζ]; exact hk'⟩
  refine ⟨u, hu, fun x hx ↦ ?_⟩
  rw [← hTu x hx]
  simp only [components, groupComponents, hw]

end Groups

/-! ### FRI on the batched words -/

section Fri
variable {withLookups : Bool} (S : Batch.Setup EF withLookups)

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
theorem agrees_of_near {lookups : List (Lookup F)} (T : Iop.Setup EF lookups) (δ : ℝ)
    (w : T.Point → 𝕂) (h : Near T δ w) : Agrees T.domain T.n (1 - δ) w := by
  obtain ⟨A, hA, v, hv, hvA⟩ := h
  refine ⟨A, ?_, v, hv, fun x hx ↦ (hvA x hx).symm⟩
  rw [ge_iff_le, Iop.Setup.size, Nat.cast_pow, Nat.cast_ofNat, mul_comm] at hA
  exact hA

/-- **FRI rejects a far batched word.** If the batched DEEP word of instance `i`'s domain size is
not `δ`-near its code, FRI accepts with probability at most `friErrorWith`: it is FRI's word or an
injected one. -/
theorem batchFriStep (p : Batch.Prover S) (lα lβ α ζ a : 𝕂) (δ : NNReal) (i : Fin S.k)
    (hfar : ¬ Near (S.instanceSetup i) δ
      (Batch.groupDeepWord p lα lβ α ζ a (S.logN i + S.params.logBlowup))) :
    friAcceptanceWith S.domainSetup (Batch.groupDeepWord p lα lβ α ζ a) S.friHeights
        (Batch.groupDeepWord p lα lβ α ζ a _) ≤
      friErrorWith S.domainSetup S.friHeights δ := by
  have hfar' : ∀ hm, ¬ Agrees (cosetDomain (EF := EF) (S.logN i + S.params.logBlowup) hm)
      (2 ^ (S.logN i + S.params.logBlowup - S.params.logBlowup)) (1 - δ)
      (Batch.groupDeepWord p lα lβ α ζ a (S.logN i + S.params.logBlowup)) := by
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

/-- Instance `i` fails at the lookup challenges `(α_L, β_L)`: none of its candidate traces and
candidate permutation traces satisfies all its constraints. -/
def Failing {withLookups : Bool} (S : Batch.Setup EF withLookups) (publicValues : Fin S.k → List F)
    (δ : ℝ) (traces : (i : Fin S.k) → Fin (S.air i).width → (S.instanceSetup i).Point → F)
    (perms : (i : Fin S.k) → Fin (S.instanceSetup i).permWidth → Fin (Challenge.d EF) →
      (S.instanceSetup i).Point → F)
    (terminals : Fin S.k → 𝕂) (lα lβ : 𝕂) (i : Fin S.k) : Prop :=
  ∀ P ∈ candidates (S.instanceSetup i) δ (traces i), ∀ R ∈ candidates (S.instanceSetup i) δ
    (fun ce : Fin (S.instanceSetup i).permWidth × Fin (Challenge.d EF) ↦ perms i ce.1 ce.2),
    ¬ Holds (S.instanceSetup i) (publicValues i) (S.challenges lα lβ i) (terminals i)
      (traceOf (S.instanceSetup i) P) fun c e ↦ R (c, e)

/-- If no tuple of close traces satisfies the batch, the lookup challenges are not bad and the
terminals of the instances with lookups sum to zero, some instance fails. -/
theorem exists_failing_instance {withLookups : Bool} {S : Batch.Setup EF withLookups}
    (publicValues : Fin S.k → List F) (δ : ℝ)
    (traces : (i : Fin S.k) → Fin (S.air i).width → (S.instanceSetup i).Point → F)
    (perms : (i : Fin S.k) → Fin (S.instanceSetup i).permWidth → Fin (Challenge.d EF) →
      (S.instanceSetup i).Point → F)
    (terminals : Fin S.k → 𝕂) (lα lβ : 𝕂)
    (hfail : ∀ ts ∈ Batch.closeTraces S δ traces, ¬ S.Satisfied ts publicValues)
    (hlookup : ¬ Batch.LookupBad S publicValues δ traces lα lβ)
    (hsum : (∑ i with S.lookups i ≠ [], terminals i) = 0) :
    ∃ i, Failing S publicValues δ traces perms terminals lα lβ i := by
  by_contra h
  simp only [Failing, not_exists, not_forall, not_not] at h
  choose P hP R hR hholds using h
  set ts := fun i ↦ traceOf (S.instanceSetup i) (P i)
  have hair : ∀ i, (S.air i).Satisfied (S.logN i) (ts i) (publicValues i) :=
    fun i ↦ (hholds i).air
  have hbal : ¬ S.Balanced ts publicValues := fun hb ↦
    hfail ts (fun i ↦ ⟨P i, (hP i).1, (hP i).2, rfl⟩) ⟨hair, hb⟩
  have hgood : ¬ LogUp.PairBad S.lookupWidth (S.messages ts publicValues) lα lβ :=
    fun hbad ↦ hlookup ⟨P, hP, hair, hbal, hbad⟩
  simp only [LogUp.PairBad, not_or, not_exists, not_and] at hgood
  have heq := Batch.sum_terminals_eq S publicValues lα lβ ts (fun i c e ↦ R i (c, e)) terminals
    hholds hgood.1
  exact hgood.2 (heq ▸ hsum)

/-! ### Summing over the challenges -/

section Sums
variable {withLookups : Bool} {S : Batch.Setup EF withLookups} (publicValues : Fin S.k → List F)
  (p : Batch.Prover S)

open Classical

/-- For one `(α, ζ)`: `|𝕂| (batchingError + friError)` if a component of instance `i₀`'s domain
size is far, and `|𝕂|` if instance `i₀`'s check passes with near components. -/
theorem batch_sum_a_le (δ : NNReal) (δ' : ℝ) (lα lβ α ζ : 𝕂) (i₀ : Fin S.k) :
    ∑ a : 𝕂, (if (∑ i with S.lookups i ≠ [], p.terminal lα lβ i) = 0 ∧
        ∀ i, ConstraintsHoldAt (S.instanceSetup i) (publicValues i) α ζ
          (p.openings lα lβ α ζ i) (S.challenges lα lβ i) (p.terminal lα lβ i)
        then friAcceptanceWith S.domainSetup (Batch.groupDeepWord p lα lβ α ζ a)
          S.friHeights (Batch.groupDeepWord p lα lβ α ζ a _) else 0) ≤
      card𝕂 EF * (batchingErrorOf (S.instanceSetup i₀)
          (S.groupNumOpened (S.logN i₀ + S.params.logBlowup)) δ δ' +
        friErrorWith S.domainSetup S.friHeights δ) +
        if NearTogether (S.instanceSetup i₀) δ' (groupComponents p lα lβ α ζ i₀) ∧
          ConstraintsHoldAt (S.instanceSetup i₀) (publicValues i₀) α ζ (p.openings lα lβ α ζ i₀)
            (S.challenges lα lβ i₀) (p.terminal lα lβ i₀)
        then card𝕂 EF else 0 := by
  set m := S.groupNumOpened (S.logN i₀ + S.params.logBlowup)
  have hle1 (a : 𝕂) : friAcceptanceWith S.domainSetup (Batch.groupDeepWord p lα lβ α ζ a)
      S.friHeights (Batch.groupDeepWord p lα lβ α ζ a _) ≤ 1 := acceptance_le_one _ _ _ _ _ _
  by_cases hH : (∑ i with S.lookups i ≠ [], p.terminal lα lβ i) = 0 ∧
    ∀ i, ConstraintsHoldAt (S.instanceSetup i) (publicValues i) α ζ
      (p.openings lα lβ α ζ i) (S.challenges lα lβ i) (p.terminal lα lβ i)
  · rw [Finset.sum_congr rfl fun a _ ↦ ite_eq_left hH]
    by_cases hG : NearTogether (S.instanceSetup i₀) δ' (groupComponents p lα lβ α ζ i₀)
    · rw [ite_eq_left ⟨hG, hH.2 i₀⟩]
      refine le_add_left ((Finset.sum_le_sum fun a _ ↦ hle1 a).trans ?_)
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    · rw [ite_eq_right fun h ↦ hG h.1, add_zero]
      have hb := batchingStep (S.instanceSetup i₀) m δ δ' (groupComponents p lα lβ α ζ i₀) hG
      set P : 𝕂 → Prop := fun a ↦ Near (S.instanceSetup i₀) δ
        fun x ↦ ∑ k : Fin m, a ^ (k : Nat) * groupComponents p lα lβ α ζ i₀ k x
      have hnear : ((Finset.univ.filter P).card : ENNReal) ≤
          card𝕂 EF * batchingErrorOf (S.instanceSetup i₀) m δ δ' := by
        have h := (ENNReal.div_le_iff_le_mul (Or.inl (card𝕂_ne_zero (EF := EF)))
          (Or.inl (card𝕂_ne_top (EF := EF)))).mp hb
        rwa [mul_comm] at h
      calc ∑ a : 𝕂, friAcceptanceWith S.domainSetup (Batch.groupDeepWord p lα lβ α ζ a)
            S.friHeights (Batch.groupDeepWord p lα lβ α ζ a _)
          ≤ ∑ a : 𝕂, ((if P a then 1 else 0) + friErrorWith S.domainSetup S.friHeights δ) := by
            refine Finset.sum_le_sum fun a _ ↦ ?_
            split_ifs with ha
            · exact (hle1 a).trans le_self_add
            · rw [zero_add]
              refine batchFriStep S p lα lβ α ζ a δ i₀ ?_
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
/-- The acceptance at lookup challenges at which instance `i₀` fails is at most its error and
FRI's. -/
theorem acceptanceAt_le {withLookups : Bool} (S : Batch.Setup EF withLookups)
    (publicValues : Fin S.k → List F) (p : Batch.Prover S) (δ δ' : NNReal)
    (hδ' : (δ' : ℝ) < 1 - S.rate) (lα lβ : 𝕂) (i₀ : Fin S.k)
    (hfail₀ : Failing S publicValues δ' p.trace (p.perm lα lβ) (p.terminal lα lβ) lα lβ i₀) :
    Batch.acceptanceAt publicValues p lα lβ ≤
      S.instanceError δ δ' i₀ + friErrorWith S.domainSetup S.friHeights δ := by
  set I := S.instanceSetup i₀
  have hrate : I.rate = S.rate := by
    rw [Iop.Setup.rate, Batch.Setup.rate, Iop.Setup.n, Iop.Setup.size, pow_add, Nat.cast_mul]
    have : ((2 ^ S.logN i₀ : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  set chs := S.challenges lα lβ i₀
  set τ := p.terminal lα lβ i₀
  obtain ⟨bad, hbad, hgood⟩ := exists_bad_alphas (publicValues i₀) chs τ
    (p.instanceProver lα lβ i₀) δ' (hrate ▸ hδ') hfail₀
  set ℓT := I.listSize (Fin I.air.width) δ'
  set ℓP := I.permListSize δ'
  set ℓQ := I.listSize (Fin I.chunks × Fin (Challenge.d EF)) δ'
  set E := batchingErrorOf I (S.groupNumOpened (S.logN i₀ + S.params.logBlowup)) δ
      ((δ' : ℝ) - 2 / I.size) + friErrorWith S.domainSetup S.friHeights δ
  set D := I.identityDegree
  -- The `ζ` with near components and instance `i₀`'s check passing, for one `α`.
  have hcount : ∀ α : 𝕂, ((Finset.univ.filter fun ζ : 𝕂 ↦
      NearTogether I ((δ' : ℝ) - 2 / I.size) (groupComponents p lα lβ α ζ i₀) ∧
        ConstraintsHoldAt I (publicValues i₀) α ζ (p.openings lα lβ α ζ i₀) chs τ).card :
          ENNReal) ≤
      I.n + ((if α ∈ bad then card𝕂 EF else 0) + (ℓT * ℓP * ℓQ * D : Nat)) := by
    intro α
    by_cases hα : α ∈ bad
    · simp only [hα, ↓reduceIte]
      refine le_trans ?_ (le_add_left le_self_add)
      exact Nat.cast_le.mpr (Finset.card_le_univ _)
    simp only [hα, ↓reduceIte, zero_add]
    rw [← Nat.cast_add]
    refine Nat.cast_le.mpr ((Finset.card_le_card fun ζ hζ ↦ ?_).trans (hgood α hα))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ ⊢
    exact ⟨nearTogether_instance p lα lβ α ζ i₀ _ hζ.1, hζ.2⟩
  -- Summing over `a` and `ζ`, for one `α`.
  have hα : ∀ α : 𝕂, ∑ ζ : 𝕂, ∑ a : 𝕂,
      (if (∑ i with S.lookups i ≠ [], p.terminal lα lβ i) = 0 ∧
        ∀ i, ConstraintsHoldAt (S.instanceSetup i) (publicValues i) α ζ
          (p.openings lα lβ α ζ i) (S.challenges lα lβ i) (p.terminal lα lβ i)
        then friAcceptanceWith S.domainSetup (Batch.groupDeepWord p lα lβ α ζ a) S.friHeights
          (Batch.groupDeepWord p lα lβ α ζ a _) else 0) ≤
      card𝕂 EF ^ 2 * E + card𝕂 EF * (I.n + ((if α ∈ bad then card𝕂 EF else 0) +
        (ℓT * ℓP * ℓQ * D : Nat))) := by
    intro α
    refine (Finset.sum_le_sum fun ζ _ ↦
      batch_sum_a_le publicValues p δ ((δ' : ℝ) - 2 / I.size) lα lβ α ζ i₀).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      ← mul_assoc, ← pow_two, mul_comm _ (card𝕂 EF)]
    exact add_le_add le_rfl (mul_le_mul_right (hcount α) _)
  -- Summing over `α`.
  have hsum : ∑ α : 𝕂, ∑ ζ : 𝕂, ∑ a : 𝕂,
      (if (∑ i with S.lookups i ≠ [], p.terminal lα lβ i) = 0 ∧
        ∀ i, ConstraintsHoldAt (S.instanceSetup i) (publicValues i) α ζ
          (p.openings lα lβ α ζ i) (S.challenges lα lβ i) (p.terminal lα lβ i)
        then friAcceptanceWith S.domainSetup (Batch.groupDeepWord p lα lβ α ζ a) S.friHeights
          (Batch.groupDeepWord p lα lβ α ζ a _) else 0) ≤
      card𝕂 EF ^ 3 * E + card𝕂 EF ^ 2 * (I.n + bad.card + (ℓT * ℓP * ℓQ * D : Nat)) := by
    refine (Finset.sum_le_sum fun α _ ↦ hα α).trans_eq ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.sum_const, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
    ring
  -- The error of instance `i₀`'s challenges `α` and `ζ`.
  have hI : ((I.n + bad.card + (ℓT * ℓP * ℓQ * D : Nat) : ENNReal)) / card𝕂 EF ≤
      foldingError I δ' + outOfDomainError I δ' := by
    have key : (I.n + bad.card + (ℓT * ℓP * ℓQ * D : Nat) : ENNReal) ≤
        ((ℓT * ℓP * (I.numConstraints - 1) : Nat) : ENNReal) +
          ((ℓT * ℓP * ℓQ * D + I.n : Nat) : ENNReal) := by
      have hbad' : bad.card ≤ ℓT * ℓP * (I.numConstraints - 1) := hbad
      have hk : I.n + bad.card + ℓT * ℓP * ℓQ * D ≤
          ℓT * ℓP * (I.numConstraints - 1) + (ℓT * ℓP * ℓQ * D + I.n) := by omega
      exact_mod_cast hk
    refine (ENNReal.div_le_div_right key (card𝕂 EF)).trans_eq ?_
    rw [← ENNReal.div_add_div_same, foldingError, outOfDomainError]
  calc Batch.acceptanceAt publicValues p lα lβ
      ≤ (card𝕂 EF)⁻¹ ^ 3 * (card𝕂 EF ^ 3 * E +
          card𝕂 EF ^ 2 * (I.n + bad.card + (ℓT * ℓP * ℓQ * D : Nat))) :=
        mul_le_mul_right hsum _
    _ = E + (I.n + bad.card + (ℓT * ℓP * ℓQ * D : Nat)) / card𝕂 EF := inv_cube_mul _ _
    _ ≤ E + (foldingError I δ' + outOfDomainError I δ') := add_le_add le_rfl hI
    _ = S.instanceError δ δ' i₀ + friErrorWith S.domainSetup S.friHeights δ := by
        rw [Batch.Setup.instanceError]
        ring

open Classical in
/-- The acceptance at lookup challenges at which the terminals do not sum to zero is zero. -/
theorem acceptanceAt_eq_zero {withLookups : Bool} {S : Batch.Setup EF withLookups}
    (publicValues : Fin S.k → List F) (p : Batch.Prover S) (lα lβ : 𝕂)
    (h : (∑ i with S.lookups i ≠ [], p.terminal lα lβ i) ≠ 0) :
    Batch.acceptanceAt publicValues p lα lβ = 0 := by
  rw [Batch.acceptanceAt]
  simp only [h, false_and, ↓reduceIte, Finset.sum_const_zero, mul_zero]

open Classical in
/-- Knowledge soundness of the batch STARK, from the steps. -/
theorem batchAcceptance_le {withLookups : Bool} (S : Batch.Setup EF withLookups)
    (publicValues : Fin S.k → List F) (p : Batch.Prover S) (δ δ' : NNReal)
    (hδ' : (δ' : ℝ) < 1 - S.rate)
    (hfail : ∀ traces ∈ Batch.closeTraces S δ' p.trace, ¬ S.Satisfied traces publicValues) :
    Batch.acceptance publicValues p ≤ Batch.knowledgeError S δ δ' := by
  set E := (⨆ i, S.instanceError δ δ' i) + friErrorWith S.domainSetup S.friHeights δ
  set B := Finset.univ.filter fun z : 𝕂 × 𝕂 ↦ Batch.LookupBad S publicValues δ' p.trace z.1 z.2
  -- At every pair, bad or not.
  have hat : ∀ z : 𝕂 × 𝕂, Batch.acceptanceAt publicValues p z.1 z.2 ≤
      (if z ∈ B then 1 else 0) + E := by
    intro z
    by_cases hz : z ∈ B
    · rw [ite_eq_left hz]
      refine le_add_right ?_
      rw [Batch.acceptanceAt]
      calc (card𝕂 EF)⁻¹ ^ 3 * _ ≤ (card𝕂 EF)⁻¹ ^ 3 * ∑ _α : 𝕂, ∑ _ζ : 𝕂, ∑ _a : 𝕂, (1 : ENNReal) :=
            by
              refine mul_le_mul_right (Finset.sum_le_sum fun α _ ↦ Finset.sum_le_sum fun ζ _ ↦
                Finset.sum_le_sum fun a _ ↦ ?_) _
              split_ifs
              · exact acceptance_le_one _ _ _ _ _ _
              · exact zero_le_one
        _ = 1 := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
            have h3 : card𝕂 EF * (card𝕂 EF * card𝕂 EF) = card𝕂 EF ^ 3 := by ring
            rw [h3, ← mul_pow, ENNReal.inv_mul_cancel card𝕂_ne_zero card𝕂_ne_top, one_pow]
    · rw [ite_eq_right hz, zero_add]
      by_cases hsum : (∑ i with S.lookups i ≠ [], p.terminal z.1 z.2 i) = 0
      · obtain ⟨i₀, hi₀⟩ := exists_failing_instance publicValues δ' p.trace (p.perm z.1 z.2)
          (p.terminal z.1 z.2) z.1 z.2 hfail
          (fun hb ↦ hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)) hsum
        exact (acceptanceAt_le S publicValues p δ δ' hδ' z.1 z.2 i₀ hi₀).trans
          (add_le_add (le_iSup (fun i ↦ S.instanceError δ δ' i) i₀) le_rfl)
      · rw [acceptanceAt_eq_zero publicValues p z.1 z.2 hsum]
        exact bot_le
  have hB : (B.card : ENNReal) ≤ (S.traceListSize δ' *
      (S.numInteractions + (S.numInteractions - 1) * S.lookupWidth) : Nat) * card𝕂 EF := by
    exact_mod_cast Batch.card_lookupBad_le S publicValues δ' p.trace
  calc Batch.acceptance publicValues p
      = (card𝕂 EF)⁻¹ ^ 2 * ∑ z : 𝕂 × 𝕂, Batch.acceptanceAt publicValues p z.1 z.2 := by
        rw [Batch.acceptance, ← Finset.sum_product']
        rfl
    _ ≤ (card𝕂 EF)⁻¹ ^ 2 * ∑ z : 𝕂 × 𝕂, ((if z ∈ B then 1 else 0) + E) :=
        mul_le_mul_right (Finset.sum_le_sum fun z _ ↦ hat z) _
    _ = (card𝕂 EF)⁻¹ ^ 2 * (B.card + card𝕂 EF ^ 2 * E) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, mul_one,
          Fintype.card_prod, Nat.cast_mul, ← pow_two]
    _ ≤ (card𝕂 EF)⁻¹ ^ 2 * ((S.traceListSize δ' *
          (S.numInteractions + (S.numInteractions - 1) * S.lookupWidth) : Nat) * card𝕂 EF +
          card𝕂 EF ^ 2 * E) := mul_le_mul_right (add_le_add hB le_rfl) _
    _ = S.lookupError δ' + E := by
        set M : ENNReal := ((S.traceListSize δ' *
          (S.numInteractions + (S.numInteractions - 1) * S.lookupWidth) : Nat) : ENNReal)
        have h1 : (card𝕂 EF)⁻¹ ^ 2 * (M * card𝕂 EF) = M / card𝕂 EF := by
          rw [pow_two, mul_comm M, ← mul_assoc, mul_assoc (card𝕂 EF)⁻¹,
            ENNReal.inv_mul_cancel card𝕂_ne_zero card𝕂_ne_top, mul_one, div_eq_mul_inv,
            mul_comm]
        have h2 : (card𝕂 EF)⁻¹ ^ 2 * (card𝕂 EF ^ 2 * E) = E := by
          rw [← mul_assoc, ← mul_pow, ENNReal.inv_mul_cancel card𝕂_ne_zero card𝕂_ne_top,
            one_pow, one_mul]
        rw [mul_add, h1, h2, Batch.Setup.lookupError]
    _ = Batch.knowledgeError S δ δ' := by rw [Batch.knowledgeError, add_assoc]

end CompStark.Sound
