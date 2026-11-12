/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import VCVio.OracleComp.QueryTracking.CostModel

/-! Rescaling worst-case query budgets: a pointwise multiple of a finite cost model inherits the
multiple of its budget. -/

@[expose] public section
namespace CompStark.Compiled
open OracleComp OracleSpec
open scoped ENNReal

section Cost

variable {ι : Type} {spec : OracleSpec ι} [∀ t, Nonempty (spec.Range t)]

/-- A budget under one cost model scales to every pointwise smaller multiple of it. -/
theorem worstCaseCostBound_scale {α : Type} (program : OracleComp spec α)
    (cost scaled : ι → ℝ≥0∞) (finite : ∀ query, cost query ≠ ⊤) (factor : ℝ≥0∞) (pointwise : ∀ query, scaled query ≤ factor * cost query)
    (budget : ℝ≥0∞) (bounded : WorstCaseCostBound program ⟨cost⟩ budget) :
    WorstCaseCostBound program ⟨scaled⟩ (factor * budget) := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => simp only [worstCaseCostBound_pure, zero_le]
  | query_bind query next ih =>
    rw [worstCaseCostBound_query_bind_iff] at bounded ⊢
    intro answer z supported
    obtain ⟨x, hx⟩ := OracleComp.support_nonempty (next answer)
    have hx' : x ∈ support (Prod.fst <$> costDist (next answer) ⟨cost⟩) := by
      simpa only [fst_map_costDist] using hx
    rw [support_map] at hx'
    obtain ⟨⟨_, c⟩, hc, -⟩ := hx'
    have first : cost query ≤ budget :=
      le_trans le_self_add (bounded answer _ hc)
    have rest : WorstCaseCostBound (next answer) ⟨cost⟩ (budget - cost query) := by
      rw [worstCaseCostBound_iff_support_bound]
      intro w hw
      exact ENNReal.le_sub_of_add_le_left (finite query) (bounded answer w hw)
    have restScaled := (worstCaseCostBound_iff_support_bound _ _ _).mp
      (ih answer (budget - cost query) rest) z supported
    calc (⟨scaled⟩ : CostModel spec ℝ≥0∞).queryCost query + Multiplicative.toAdd z.2
        ≤ factor * cost query + factor * (budget - cost query) := add_le_add (pointwise query) restScaled
      _ = factor * budget := by rw [← mul_add, add_tsub_cancel_of_le first]

end Cost

end CompStark.Compiled
