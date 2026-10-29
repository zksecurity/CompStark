/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.SoundnessError
public import CompStark.Lookup.Poly

/-! # The steps of the soundness proof

`knowledgeSoundness` and `batchKnowledgeSoundness` follow from four facts about a STARK, stated
here as propositions and proved in their own files:

* `FriStep`: FRI rejects words far from the code (`FriGame.acceptance_le`).
* `BatchingStep`: batching by powers keeps summands that are not `δ'`-near on a common set
  `δ`-far, except for few `a` (correlated agreement).
* `DecodingStep`: if the DEEP summands are near on a common set and `ζ` lies off the trace
  domain and off `L`, the claimed values are those of a candidate trace, permutation trace and
  quotient.
* `AlgebraStep`: if a candidate trace and permutation trace fail a constraint on some row
  (`Holds`), the constraint check at `ζ` passes for few `(α, ζ)`.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop Polynomial

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

variable {lookups : List (Lookup F)}

/-- The DEEP quotient of a word `f` with claimed value `y` at `z`: `(y - f(x)) / (z - x)`. -/
noncomputable def deepComponent (S : Setup EF lookups) (f : S.Point → F) (z y : 𝕂) : S.Point → 𝕂 :=
  fun i ↦ (y - algebraMap F 𝕂 (f i)) / (z - S.domain i)

/-- `ζ` lies off the trace domain `H = ⟨ω_n⟩`: the check's denominators `Z_H(ζ)`, `ζ - 1`,
`ζ - ω_n⁻¹` are nonzero. -/
def OffTraceDomain (S : Setup EF lookups) (ζ : 𝕂) : Prop := ζ ^ S.n ≠ 1

/-- `ζ` lies off the domain `L`, where the DEEP quotients at `ζ` divide by zero; then so does
`ζ ω_n`, `L` being a coset of a group that holds `ω_n` (`offDomain_mul_rootOfUnity`). -/
def OffDomain (S : Setup EF lookups) (ζ : 𝕂) : Prop := ∀ i, S.domain i ≠ ζ

/-- FRI accepts a word that is not `δ`-near the code with probability at most `friError`. -/
def FriStep (S : Setup EF lookups) : Prop :=
  ∀ (δ : NNReal) (w : S.Point → 𝕂), ¬ Near S δ w → friAcceptance S w ≤ friError S δ

/-- FRI accepts with probability at most `1`. -/
def FriAtMostOne (S : Setup EF lookups) : Prop := ∀ w : S.Point → 𝕂, friAcceptance S w ≤ 1

open Classical in
/-- If `m` words are not near the code on a common set at radius `δ'`, their combination by the
powers of a uniform `a` is `δ`-near the code with probability at most `batchingErrorOf`. -/
def BatchingStep (S : Setup EF lookups) : Prop :=
  ∀ (m : Nat) (δ : NNReal) (δ' : ℝ) (ws : Fin m → S.Point → 𝕂), ¬ NearTogether S δ' ws →
    ((Finset.univ.filter fun a : 𝕂 ↦
        Near S δ fun i ↦ ∑ k : Fin m, a ^ (k : Nat) * ws k i).card : ENNReal)
      / Fintype.card 𝕂 ≤ batchingErrorOf S m δ δ'

/-- The preprocessed trace's polynomials have degree below `n`. -/
theorem natDegree_preprocessedPoly_le (S : Setup EF lookups) (j : Nat) :
    (S.preprocessedPoly j).natDegree ≤ S.n := by
  rcases eq_or_ne (S.preprocessedPoly j) 0 with h | h
  · rw [h, natDegree_zero]; exact Nat.zero_le _
  · have := Lagrange.degree_interpolate_lt (s := Finset.range S.n)
      (v := fun i ↦ twoAdicGen (F := F) S.logN ^ i)
      (fun i ↦ S.air.preprocessed.getD (i * S.air.preprocessedWidth + j) 0) ?_
    · rw [Finset.card_range] at this
      exact ((natDegree_lt_iff_degree_lt h).mpr this).le
    · intro a ha b hb hab
      exact (BaseField.isPrimitiveRoot_twoAdicGen (F := F) S.logN
        (by have := S.valid.twoAdic; omega)).pow_inj
        (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hab

/-- The preprocessed trace's polynomials take its values on the trace domain. -/
theorem eval_preprocessedPoly (S : Setup EF lookups) (j i : Nat) (hi : i < S.n) :
    (S.preprocessedPoly j).eval (twoAdicGen S.logN ^ i) =
      S.air.preprocessed.getD (i * S.air.preprocessedWidth + j) 0 :=
  Lagrange.eval_interpolate_at_node _
    (fun a ha b hb hab ↦ (BaseField.isPrimitiveRoot_twoAdicGen (F := F) S.logN
      (by have := S.valid.twoAdic; omega)).pow_inj
      (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hab) (Finset.mem_range.mpr hi)

/-- The claimed values of polynomials `trace`, `quotient` and `perm` (the permutation trace's
coordinates), and of the preprocessed trace's: the true ones at `ζ`. -/
noncomputable def trueOpenings (S : Setup EF lookups) (trace : Fin S.air.width → F[X])
    (quotient : Fin S.chunks → Fin (Challenge.d EF) → F[X]) (ζ : 𝕂)
    (perm : Fin S.permWidth → Fin (Challenge.d EF) → F[X] := fun _ _ ↦ 0) : Openings S where
  traceAt j := aeval ζ (trace j)
  traceNext j := aeval (ζ * rootOfUnity S.logN) (trace (Fin.castLE S.air.mainNextWidth_le j))
  quotientAt c e := aeval ζ (quotient c e)
  preprocessedAt j := aeval ζ (S.preprocessedPoly j)
  preprocessedNext j := aeval (ζ * rootOfUnity S.logN) (S.preprocessedPoly j)
  permAt c e := aeval ζ (perm c e)
  permNext c e := aeval (ζ * rootOfUnity S.logN) (perm c e)

theorem length_openedWords {S : Setup EF lookups} (p : Prover S) (α ζ : 𝕂) :
    (openedWords p α ζ).length = S.numOpened := by
  simp only [openedWords, List.length_append, List.length_map, List.length_finRange,
    List.length_flatMap, List.map_const', List.sum_replicate, smul_eq_mul, Setup.numOpened]
  ring

/-- The DEEP components of the opened words, by position. -/
noncomputable def components {S : Setup EF lookups} (p : Prover S) (α ζ : 𝕂) :
    Fin S.numOpened → S.Point → 𝕂 := fun k ↦
  let w := (openedWords p α ζ)[k.val]'(by rw [length_openedWords]; exact k.isLt)
  deepComponent S w.1 w.2.1 w.2.2

/-- The permutation trace's columns on row `r` of the trace domain, from its coordinates'
polynomials `perm`: column `c`'s value `∑ₑ genᵉ R_{c,e}(ωʳ)` (`permValue`). -/
noncomputable def permRow (S : Setup EF lookups)
    (perm : Fin S.permWidth → Fin (Challenge.d EF) → F[X]) (r : Nat) : Nat → 𝕂 :=
  permValue fun c e ↦ lift ((perm c e).eval (twoAdicGen S.logN ^ r))

/-- A trace and a permutation trace (its coordinates' polynomials `perm`) satisfy every constraint
of the instance on every row: the trace satisfies the AIR, and the LogUp constraints vanish on the
rows of the traces and the permutation trace, with the lookup challenges and the terminal. -/
structure Holds (S : Setup EF lookups) (publicValues : List F) (challenges : List 𝕂) (terminal : 𝕂)
    (trace : Array F) (perm : Fin S.permWidth → Fin (Challenge.d EF) → F[X]) : Prop where
  air : S.air.Satisfied S.logN trace publicValues
  lookups : ∀ g ∈ S.extConstraints, ∀ r < S.n,
    g.eval ((S.air.traceRow S.logN trace publicValues r).map lift)
      ⟨permRow S perm r, permRow S perm (r + 1), (challenges.getD · 0), terminal⟩ = 0

/-- If the DEEP components of the opened words are `δ`-near the code on a common set, `δ` below
`1 - rate` and `ζ` off the trace domain and off `L`, the claimed values are those of polynomials
of degree at most `n` that agree with the trace, quotient and permutation words on one common set
of `(1 - δ) N` points: a candidate of the list decoding of the committed words as one family
(`Setup.Committed`). -/
def DecodingStep (S : Setup EF lookups) : Prop :=
  ∀ (δ : NNReal), (δ : ℝ) < 1 - S.rate → ∀ (prover : Prover S) (α ζ : 𝕂), OffTraceDomain S ζ →
    OffDomain S ζ → NearTogether S δ (components prover α ζ) →
    ∃ (trace : Fin S.air.width → F[X]) (quotient : Fin S.chunks → Fin (Challenge.d EF) → F[X])
      (perm : Fin S.permWidth → Fin (Challenge.d EF) → F[X]),
      (∀ j, (trace j).natDegree ≤ S.n) ∧ (∀ c e, (quotient c e).natDegree ≤ S.n) ∧
      (∀ c e, (perm c e).natDegree ≤ S.n) ∧
      Agree S δ (S.committed prover.trace prover.perm (prover.quotient α))
        (S.committed trace perm quotient) ∧
      prover.openings α ζ = trueOpenings S trace quotient ζ perm

open Classical in
/-- If the trace of polynomials `trace` and the permutation trace of polynomials `perm` fail a
constraint on some row (`Holds`), then for all but `#constraints - 1` values of `α`, whatever the
quotient's polynomials, the constraints hold at at most `identityDegree` values of `ζ` off the
trace domain, with the true values. -/
def AlgebraStep (S : Setup EF lookups) : Prop :=
  ∀ (publicValues : List F) (challenges : List 𝕂) (terminal : 𝕂) (trace : Fin S.air.width → F[X])
    (perm : Fin S.permWidth → Fin (Challenge.d EF) → F[X]),
    (∀ j, (trace j).natDegree ≤ S.n) → (∀ c e, (perm c e).natDegree ≤ S.n) →
    ¬ Holds S publicValues challenges terminal (traceOf S trace) perm →
    ∃ bad : Finset 𝕂, bad.card ≤ S.numConstraints - 1 ∧
      ∀ α ∉ bad, ∀ quotient : Fin S.chunks → Fin (Challenge.d EF) → F[X],
        (∀ c e, (quotient c e).natDegree ≤ S.n) →
        (Finset.univ.filter fun ζ : 𝕂 ↦ OffTraceDomain S ζ ∧
          ConstraintsHoldAt S publicValues α ζ (trueOpenings S trace quotient ζ perm) challenges
            terminal).card ≤
          S.identityDegree

end CompStark.Sound
