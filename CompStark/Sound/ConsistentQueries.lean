/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ArkLib.ProofSystem.Fri.Spec.QuerySoundness

/-! # FRI's query density for a recommitted input word

ArkLib's FRI query analysis (`Fri.Spec.acceptingQueries_density_le`) bounds the density of the
points where every query check passes, for a history whose initial oracle is far from the code.
Plonky3 does not run FRI on the batched DEEP word itself: it commits that word again as the first
commit-phase oracle `f₀'`, and each query compares `f₀'` with the DEEP word only at the queried
point. So the input that must be far is the DEEP word `word`, not `f₀'`, and a query passes when
its checks pass and `f₀'` agrees with `word` there.

`consistentQueries_density_le` bounds the density of those points by the same
`1 - min (θ - k · loss) (δ - (k + 1) · loss)`: on a large set of accepting points, ArkLib's
`exists_codeword_agree_of_acceptingQueries` yields a codeword agreeing with `f₀'` on most of it,
hence with `word` where `f₀' = word`; a word `δ`-far from the code leaves little room for that.
-/

@[expose] public section
namespace Fri.Spec
open Domain ReedSolomon

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)

/-- The points where every query check passes and the initial oracle agrees with `word`. -/
noncomputable def consistentQueries (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k) (word : Fin (2 ^ n) → F) :
    Finset (Fin (2 ^ n)) := by
  classical
  exact (acceptingQueries s hs o α).filter fun z ↦ initialWord s o z = word z

/-- For a safe history with a valid final polynomial and a word at distance at least `δ` from the
code, the points where the query checks pass and the initial oracle agrees with the word have
density at most `1 - min (θ - k · loss) (δ - (k + 1) · loss)`. -/
theorem consistentQueries_density_le
    (hs : (∑ j, (s j).val) ≤ n) (o : ∀ j, FinalOracleStatement s ω j)
    (α : FinalStatement F k) (word : Fin (2 ^ n) → F) (θ δ loss : ℝ) (hloss : 0 ≤ loss)
    (hsafe : SafeHistory s d o α θ loss)
    (hdegree : (finalPolynomial s o).natDegree < d.val)
    (hdist : ∀ u ∈ code ω (2 ^ (∑ j, (s j).val) * d.val),
      δ ≤ (Code.relHammingDist word u : ℝ)) :
    ((consistentQueries s hs o α word).card : ℝ) / 2 ^ n ≤
      1 - min (θ - k * loss) (δ - ((k : ℝ) + 1) * loss) := by
  classical
  refine accepting_density_le_of_lossy_agreement ω word _ θ δ _ _ (fun hlarge ↦ ?_) hdist
  obtain ⟨u, hu, S', hS', hcard, hagree⟩ := exists_codeword_agree_of_acceptingQueries s d hs o α
    θ loss hloss hsafe hdegree (consistentQueries s hs o α word)
    (Finset.filter_subset _ _) hlarge
  refine ⟨u, hu, S', hS', hcard, fun z hz ↦ ?_⟩
  have hz' := hS' hz
  simp only [consistentQueries, Finset.mem_filter] at hz'
  rw [hagree z hz, hz'.2]

end Fri.Spec
