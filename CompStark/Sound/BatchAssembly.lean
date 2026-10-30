/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.BatchLogUp
public import Mathlib.Data.Finset.Sort

/-! # The batch STARK's instance pieces

The batch STARK's round arguments (`Sound/BatchRbr.lean`) rest on these facts about the
instances:

* the batched DEEP word of a domain size is the combination, by the powers of `a`, of the DEEP
  components of the opened words of the instances of that size (`groupDeepWord_eq`), and if
  those components are `δ'`-near the code on a common set, so are each instance's
  (`nearTogether_instance`);
* FRI injects the batched words of the shorter domains at their sizes (`mem_friHeights`,
  `fits_friHeights`);
* if no tuple of close traces satisfies the batch, the lookup challenges are not bad
  (`LookupBad`) and the terminals sum to zero, some instance has no close trace and close
  permutation trace that satisfy all its constraints (`exists_failing_instance`): otherwise the
  close traces satisfy every AIR, so their buses do not balance, and the terminals sum to the
  messages' nonzero sum of fractions (`sum_terminals_eq`).
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
  simp only [Batch.Setup.friHeights, List.mem_filter, List.mem_reverse, List.mem_range,
    List.any_eq_true, List.mem_finRange, true_and, beq_iff_eq]
  constructor
  · rintro ⟨hlt, i, hi⟩
    exact ⟨i, hi, hlt.ne⟩
  · rintro ⟨i, hi, hne⟩
    have := S.logN_le_top i
    exact ⟨lt_of_le_of_ne (by omega) hne, i, hi⟩

/-- The sizes where FRI injects fit below the tallest domain and at or above the final one. -/
theorem fits_friHeights :
    Rounds.Fits (S.params.logFinalPolyLen + S.params.logBlowup)
      (S.logN S.top + S.params.logBlowup) S.friHeights := by
  refine ⟨?_, fun m hm ↦ ?_⟩
  · refine (List.Pairwise.filter _ ?_)
    rw [List.pairwise_reverse]
    exact List.pairwise_lt_range
  · obtain ⟨i, rfl, hne⟩ := (mem_friHeights S m).mp hm
    have := S.logN_le_top i
    have := (S.valid i).finalPolyFits
    omega

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

end CompStark.Sound
