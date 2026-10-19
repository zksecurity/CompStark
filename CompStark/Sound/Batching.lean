/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Steps

/-! # The batching step

`batchingStep`: if one of the opened words `ws k` is not `δ`-near the code, the set of `a` for
which `∑ₖ aᵏ ws k` is `δ`-near the code has density at most `batchingError`.

The argument is by inclusion of events. If the combination agrees with a codeword on a set `T` of
at least `N (1 - δ)` points, its projection to `T` lies in the projected code; `ws k` projected to
`T` does not, as it would then be `δ`-near the code on the same `T`. So `a` lies in the
mutual-correlated-agreement event `IsMCA` of the powers generator for the family `ws`, whose
uniform probability is the event's density, and at most the supremum `mcaError` over families.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop CoreDefinitions LinearCode

local notation "𝕂" => KoalaBear.Ext4

/-- A combination `δ`-near the code, of words one of which is not, is an MCA event for the powers
generator. -/
theorem isMCA_of_near (S : Setup) (δ : NNReal) {M : Nat} (ws : Fin (M + 1) → S.Point → 𝕂)
    (hfar : ∃ k, ¬ Near S δ (ws k)) (a : 𝕂)
    (hnear : Near S δ fun i ↦ ∑ k : Fin (M + 1), a ^ (k : Nat) * ws k i) :
    IsMCA (univariatePowersGenerator 𝕂 M) S.code a ws δ := by
  obtain ⟨T, hT, u, hu, hagree⟩ := hnear
  obtain ⟨k, hk⟩ := hfar
  refine ⟨T, by rwa [Fintype.card_fin], ?_, k, ?_⟩
  · refine Submodule.mem_map.mpr ⟨u, hu, funext fun i ↦ ?_⟩
    simp only [LinearMap.funLeft_apply, projectedWord, Set.domRestrict_apply, smul_eq_mul]
    exact (hagree i.1 i.2).symm
  · intro hmem
    obtain ⟨v, hv, heq⟩ := Submodule.mem_map.mp hmem
    exact hk ⟨T, hT, v, hv, fun i hi ↦ (congrFun heq ⟨i, hi⟩).symm⟩

open Classical in
/-- `batchingStep` for `M + 1` words. -/
theorem density_near_le_mcaError (S : Setup) (δ : NNReal) {M : Nat}
    (ws : Fin (M + 1) → S.Point → 𝕂) (hfar : ∃ k, ¬ Near S δ (ws k)) :
    ((Finset.univ.filter fun a : 𝕂 ↦
        Near S δ fun i ↦ ∑ k : Fin (M + 1), a ^ (k : Nat) * ws k i).card : ENNReal)
      / Fintype.card 𝕂 ≤ mcaError (univariatePowersGenerator 𝕂 M) S.code δ := by
  refine le_iSup_of_le ws ?_
  rw [SampleableType.prEvent_uniformSample]
  apply ENNReal.div_le_div_right
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro a
  simp only [Finset.mem_filter_univ]
  exact isMCA_of_near S δ ws hfar a

/-- Batching by powers keeps a far word far, except with probability `batchingError`. -/
theorem batchingStep (S : Setup) : BatchingStep S := by
  intro δ ws hfar
  unfold batchingError
  generalize S.numOpened = m at ws hfar ⊢
  cases m with
  | zero => exact absurd hfar fun ⟨k, _⟩ ↦ k.elim0
  | succ M => exact density_near_le_mcaError S δ ws hfar

end CompStark.Sound
