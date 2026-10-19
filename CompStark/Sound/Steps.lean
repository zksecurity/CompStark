/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Soundness

/-! # The steps of the soundness proof

`knowledgeSoundness` follows from four facts, stated here as propositions and proved in their
own files:

* `FriStep`: FRI rejects words far from the code (ArkLib's FRI soundness).
* `BatchingStep`: batching by powers keeps a far summand far, except for few `a` (correlated
  agreement).
* `DecodingStep`: if every DEEP summand is close to the code and `ζ` lies outside the base field,
  the claimed values are those of the decoded polynomials.
* `AlgebraStep`: if the decoded trace fails the AIR, the constraint check at `ζ` passes for few
  `(α, ζ)`.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop Polynomial

local notation "𝔽" => KoalaBear.Field
local notation "𝕂" => KoalaBear.Ext4
local notation "F" => KoalaBear.Fast.Field

/-- A word agrees with a codeword of `S.code` on at least `(1 - δ) N` points. -/
def Near (S : Setup) (δ : ℝ) (w : S.Point → 𝕂) : Prop :=
  ∃ T : Finset S.Point, (T.card : ℝ) ≥ S.size * (1 - δ) ∧ ∃ u ∈ S.code, ∀ i ∈ T, w i = u i

/-- The DEEP quotient of a word `f` with claimed value `y` at `z`: `(y - f(x)) / (z - x)`. -/
noncomputable def deepComponent (S : Setup) (f : S.Point → 𝔽) (z y : 𝕂) : S.Point → 𝕂 :=
  fun i ↦ (y - algebraMap 𝔽 𝕂 (f i)) / (z - S.domain i)

/-- `ζ` is not in the base field. -/
def OutsideBase (ζ : 𝕂) : Prop := ζ ∉ Set.range (algebraMap 𝔽 𝕂)

/-- The polynomial of degree at most `n` closest to a word on `L`: the extractor's decoding. -/
noncomputable def decoded (S : Setup) (f : S.Point → 𝔽) : 𝔽[X] :=
  closestPolynomial (S.n + 1) (fun i : S.Point ↦ basePoint (S.logN + S.params.logBlowup) i) f

/-- FRI accepts a word that is not `δ`-near the code with probability at most `friError`. -/
def FriStep (S : Setup) : Prop :=
  ∀ (δ : NNReal) (w : S.Point → 𝕂), ¬ Near S δ w → friAcceptance S w ≤ friError S δ

/-- FRI accepts with probability at most `1`. -/
def FriAtMostOne (S : Setup) : Prop := ∀ w : S.Point → 𝕂, friAcceptance S w ≤ 1

open Classical in
/-- If one of `numOpened` words is not `δ`-near the code, their combination by the powers of a
uniform `a` is `δ`-near the code with probability at most `batchingError`. -/
def BatchingStep (S : Setup) : Prop :=
  ∀ (δ : NNReal) (ws : Fin S.numOpened → S.Point → 𝕂), (∃ k, ¬ Near S δ (ws k)) →
    ((Finset.univ.filter fun a : 𝕂 ↦ Near S δ fun i ↦ ∑ k : Fin S.numOpened, a ^ (k : Nat) * ws k i).card : ENNReal)
      / Fintype.card 𝕂 ≤ batchingError S δ

/-- If every DEEP component of the opened words is `δ`-near the code, `δ` within the
unique-decoding radius and `ζ` outside the base field, the claimed values are the decoded
polynomials' values. -/
def DecodingStep (S : Setup) : Prop :=
  ∀ (δ : NNReal), δ ≤ S.uniqueDecodingRadius → ∀ (prover : Prover S) (α ζ : 𝕂), OutsideBase ζ →
    (∀ w ∈ openedWords prover α ζ, Near S δ (deepComponent S w.1 w.2.1 w.2.2)) →
    let o := prover.openings α ζ
    (∀ j, o.traceAt j = aeval ζ (decoded S (prover.trace j))) ∧
    (∀ j, o.traceNext j = aeval (ζ * rootOfUnity S.logN) (decoded S (prover.trace j))) ∧
    (∀ c e, o.quotientAt c e = aeval ζ (decoded S (prover.quotient α c e)))

/-- The claimed values of polynomials `trace` and `quotient`: the true ones at `ζ`. -/
noncomputable def trueOpenings (S : Setup) (trace : Fin S.air.width → 𝔽[X])
    (quotient : Fin S.chunks → Fin 4 → 𝔽[X]) (ζ : 𝕂) : Openings S where
  traceAt j := aeval ζ (trace j)
  traceNext j := aeval (ζ * rootOfUnity S.logN) (trace j)
  quotientAt c e := aeval ζ (quotient c e)

/-- The trace whose columns take the values of `trace` on the trace domain's rows. -/
noncomputable def traceOf (S : Setup) (trace : Fin S.air.width → 𝔽[X]) : Array F :=
  Array.ofFn fun r : Fin (S.n * S.air.width) ↦
    let (row, column) := finProdFinEquiv.symm r
    KoalaBear.Fast.ringEquiv.symm
      ((trace column).eval (Montgomery.Native32.FastField.toField (twoAdicGen S.logN) ^ row.val))

open Classical in
/-- If the trace of polynomials `trace` fails the AIR, then for all but `#constraints - 1` values
of `α`, whatever the quotient's polynomials, the constraints hold at at most `identityDegree`
values of `ζ` outside the base field, with the true values. -/
def AlgebraStep (S : Setup) : Prop :=
  ∀ (publicValues : List F) (trace : Fin S.air.width → 𝔽[X]),
    (∀ j, (trace j).natDegree ≤ S.n) →
    ¬ S.air.Satisfied S.logN (traceOf S trace) publicValues →
    ∃ bad : Finset 𝕂, bad.card ≤ S.air.constraints.length - 1 ∧
      ∀ α ∉ bad, ∀ quotient : Fin S.chunks → Fin 4 → 𝔽[X], (∀ c e, (quotient c e).natDegree ≤ S.n) →
        (Finset.univ.filter fun ζ : 𝕂 ↦ OutsideBase ζ ∧
          ConstraintsHoldAt S publicValues α ζ (trueOpenings S trace quotient ζ)).card ≤
          S.identityDegree

end CompStark.Sound
