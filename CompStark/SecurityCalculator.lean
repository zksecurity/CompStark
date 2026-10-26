/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.BatchNonInteractiveError
public import CompStark.Sound.McaBound

/-! # The security calculator

Rational upper bounds on the knowledge errors (`knowledgeError`, `Batch.knowledgeError`) and the
random-oracle round errors (`roundError`, `Batch.roundError`), computed from a setup's numbers:
its `Shape` (its constraint count and identity degree, its opened words, whether it has lookups),
its lookups' interactions `T` and widest tuple `W`, its heights and FRI's parameters, for a base
field of `p` elements and the challenge field's degree `d`. Every term is a rational number, so
the calculator runs as code (`#eval`, `Report`) and in the kernel (`decide +kernel`), which
evaluates the AIR's structure itself; the theorems of `CompStark/Security.lean` turn a checked
bound into a bound on the error.

The analysis is the one of `CompStark/Sound/Numbers.lean`, at any FRI arity, with an MCA bound `B`
(`McaBound`: `uniqueDecoding` within the unique-decoding radius, `johnson` up to the Johnson
radius, or the smaller of two) and the free parameters of `Analysis`: FRI's proximity `δ`, the
extractor's `δ' ≥ δ` below the Johnson radius `1 - √ρ`, and a proximity loss `loss`. With
`K = p ^ d`, `N` the domain's size, `δ'' = δ' - 2/N` and `ℓ` the list bound at `δ'` (`1` below the
unique-decoding radius, `⌊(1 - δ' - ρ) / ((1 - δ')² - ρ)⌋` above, the Johnson bound):

* constraint folding: `ℓ ℓₚ (#constraints - 1) / K`, `ℓₚ` the permutation trace's list bound, `1`
  without lookups;
* out of domain: `(ℓ identityDegree + n) / K`, `ℓ` bounding the list of the committed words as
  one family;
* batching `m` words: `B`'s count for curves of degree `m - 1` on `N` points over `K`, or for
  `δ < δ''` and `δ ≤ (1 - ρ) / 2 - 1/N` the curve bound `(m - 1) max(T₁, T₂) / K`,
  `T₁ = (1 - ρ - δ) / (δ (1 - ρ - 2δ))`, `T₂ = δ'' / (δ'' - δ)`, if smaller;
* FRI's folds, Plonky3's schedule as a plan of folds (`FriGame.Rounds.plan`): a fold by `2 ^ k`
  onto `2 ^ m` points batching `M = 2 ^ k - 1` words (one more if it injects an input) costs `B`'s
  count for curves of degree `M` on `2 ^ m` points over `K`, or if smaller and
  `δ ≤ (1 - ρ) / 2 - 2 ^ (-m)` the lossy bound `M max(T₁, δ_int / loss) / K`, `δ_int = δ + loss`;
* FRI's queries: `(1 - δ + #folds · loss) ^ numQueries`;
* a batch's lookup challenges: `ℓᵏ (T + (T - 1) W) / K` for `k` instances.

The knowledge error is at most the sum of the terms, a batch's with each instance term at its
worst instance. In the random-oracle model every round is one oracle answer and the round error
is at most the largest term, each round after `α` multiplied by its grinding's `powFraction`,
FRI's folds bounded by their largest fold and its queries by
`(1 - δ + #folds · loss + 1/p) ^ numQueries`.

`Setup.Secure p B A bits` and `Setup.SecureRo p B A bits` (and the batch's) are decidable: the
analysis fits the setup (`Setup.Fits`: `B` admits batching and every fold at `δ`) and the bound is
at most `2 ^ (-bits)`. The analysis need not be picked by hand: `Setup.bestAnalysis`
(`bestAnalysisRo`, and the batch's) searches the radii and the loss for the smallest bound, and
`decide +kernel` checks the analysis it finds.
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound

/-- The free parameters of the analysis, as rationals: FRI's proximity `δ`, the extractor's `δ'`
and the proximity loss `loss` of FRI's folds. -/
structure Analysis where
  δ : ℚ
  δ' : ℚ
  loss : ℚ
  deriving Repr, DecidableEq

namespace Analysis
variable (A : Analysis)

/-- The curve bound's `T₁ = (1 - ρ - δ) / (δ (1 - ρ - 2δ))` at rate `ρ`. -/
def curveT₁ (ρ : ℚ) : ℚ := (1 - ρ - A.δ) / (A.δ * (1 - ρ - 2 * A.δ))

/-- The lossy bound of one fold at rate `ρ`, `max(T₁, T₂, δ_int / loss)` with
`δ_int = δ + loss` (`LossyMca.lossyBound`). -/
def lossyBound (ρ : ℚ) : ℚ :=
  max (max (A.curveT₁ ρ) ((A.δ + A.loss) / (A.δ + A.loss - A.δ))) ((A.δ + A.loss) / A.loss)

/-- A fold of FRI's plan at rate `1 / 2 ^ lb`, times `|𝕂|`: onto `2 ^ m` points, batching `M`
words besides the first, the MCA bound `B`'s count for the code of degree below `2 ^ (m - lb)`, or
the lossy bound `M max(T₁, T₂, δ_int / loss)` if smaller and `δ ≤ (1 - ρ) / 2 - 2 ^ (-m)`. -/
def levelBound (B : McaBound) (lb : ℕ) (f : ℕ × ℕ × Bool) : ℚ :=
  let M := FriGame.Rounds.foldWords f
  let count := B.count (2 ^ f.2.1) (2 ^ (f.2.1 - lb)) M A.δ
  if A.δ ≤ (1 - 1 / 2 ^ lb) / 2 - 1 / 2 ^ f.2.1 then
    min ((M : ℚ) * A.lossyBound (1 / 2 ^ lb)) count
  else count

/-- `B` admits every fold of `plan` at rate `1 / 2 ^ lb`. -/
def Admits (B : McaBound) (lb : ℕ) (plan : List (ℕ × ℕ × Bool)) : Prop :=
  ∀ f ∈ plan, B.admits (2 ^ f.2.1) (2 ^ (f.2.1 - lb)) A.δ

instance (B : McaBound) (lb : ℕ) (plan : List (ℕ × ℕ × Bool)) : Decidable (A.Admits B lb plan) :=
  by unfold Admits; infer_instance

/-- The list bound at `δ'` and rate `ρ`: `1` below the unique-decoding radius `(1 - ρ) / 2`, and
the Johnson bound `⌊(1 - δ' - ρ) / ((1 - δ')² - ρ)⌋` above it. -/
def listBound (ρ : ℚ) : ℕ :=
  if A.δ' < (1 - ρ) / 2 then 1 else ⌊(1 - A.δ' - ρ) / ((1 - A.δ') ^ 2 - ρ)⌋₊

/-- The analysis' conditions at rate `ρ`: `δ` and `loss` positive, `δ ≤ δ'`, and `δ'` below the
Johnson radius `1 - √ρ`. -/
def Valid (ρ : ℚ) : Prop :=
  0 < A.δ ∧ 0 < A.loss ∧ A.δ ≤ A.δ' ∧ A.δ' < 1 ∧ ρ < (1 - A.δ') ^ 2

instance (ρ : ℚ) : Decidable (A.Valid ρ) := by unfold Valid; infer_instance

end Analysis

/-- `powFraction F bits` for `|F| = p`: `((p - 1) / 2 ^ bits + 1) / p`. -/
def powFractionQ (p bits : ℕ) : ℚ := (((p - 1) / 2 ^ bits + 1 : ℕ) : ℚ) / p

/-- The largest of a list of rationals, `0` if empty. -/
def maxQ (l : List ℚ) : ℚ := l.foldr max 0

/-- The sum of a list of named terms. -/
def sumTerms (l : List (String × ℚ)) : ℚ := l.foldr (fun x s ↦ x.2 + s) 0

/-- The largest of a list of named terms, `0` if empty. -/
def maxTerms (l : List (String × ℚ)) : ℚ := l.foldr (fun x s ↦ max x.2 s) 0

/-- What the calculator reads of an instance's AIR and lookups: its constraint count, its identity
degree and its opened words, whether it proves lookups, and its log trace length `logN`. -/
structure Shape where
  numConstraints : ℕ
  identityDegree : ℕ
  numOpened : ℕ
  lookups : Bool
  logN : ℕ

namespace Shape
variable (c : Shape) (logBlowup : ℕ) (B : McaBound) (A : Analysis)

/-- The permutation trace's list bound at `δ'`, `1` without lookups. -/
def permListBound : ℕ := if c.lookups then A.listBound (1 / 2 ^ logBlowup) else 1

/-- Constraint folding, times `|𝕂|`: `ℓ ℓₚ (#constraints - 1)`. -/
def foldingNum : ℚ :=
  (A.listBound (1 / 2 ^ logBlowup) * c.permListBound logBlowup A * (c.numConstraints - 1) : ℕ)

/-- The out-of-domain point, times `|𝕂|`: `ℓ identityDegree + n`, `ℓ` the list bound of the
committed words as one family. -/
def outOfDomainNum : ℚ := (A.listBound (1 / 2 ^ logBlowup) * c.identityDegree + 2 ^ c.logN : ℕ)

/-- Batching `m` opened words on the domain of `N = 2 ^ (logN + logBlowup)` points at rate
`ρ = 1 / 2 ^ logBlowup`, times `|𝕂|`: the MCA bound `B`'s count for curves of degree `m - 1`, or
for `δ < δ'' = δ' - 2/N` and `δ ≤ (1 - ρ) / 2 - 1/N` the curve bound `(m - 1) max(T₁, T₂)` if
smaller. -/
def batchingNum (m : ℕ) : ℚ :=
  let N : ℕ := 2 ^ (c.logN + logBlowup)
  let ρ : ℚ := 1 / 2 ^ logBlowup
  let count := B.count N (2 ^ c.logN) (m - 1) A.δ
  if A.δ < A.δ' - 2 / N ∧ A.δ ≤ (1 - ρ) / 2 - 1 / N then
    min count (((m - 1 : ℕ) : ℚ) * max (A.curveT₁ ρ) ((A.δ' - 2 / N) / (A.δ' - 2 / N - A.δ)))
  else count

end Shape

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

namespace Setup
variable {lookups : List (Lookup F)} (S : Setup EF lookups)

/-- The rate `1 / 2 ^ logBlowup`. -/
def rateQ : ℚ := 1 / 2 ^ S.params.logBlowup

/-- The setup's shape. -/
def shape : Shape := ⟨S.numConstraints, S.identityDegree, S.numOpened, !lookups.isEmpty, S.logN⟩

/-- The folds of FRI on `L`, with inputs injected at the log sizes `heights`, as data
(`FriGame.Rounds.plan`, `Setup.friRounds`). -/
def friPlan (heights : List ℕ) : List (ℕ × ℕ × Bool) :=
  FriGame.Rounds.plan S.params.maxLogArity (S.params.logFinalPolyLen + S.params.logBlowup)
    (S.logN + S.params.logBlowup) (S.logN + S.params.logBlowup) heights

/-- The analysis fits `S` with the MCA bound `B`: it is valid at `S`'s rate, `δ ≤ δ' - 2/N`, and
`B` admits batching and FRI's folds. -/
def Fits (B : McaBound) (A : Analysis) : Prop :=
  A.Valid S.rateQ ∧ A.δ ≤ A.δ' - 2 / S.size ∧ B.admits S.size S.n A.δ ∧
    A.Admits B S.params.logBlowup (S.friPlan [])

instance (B : McaBound) (A : Analysis) : Decidable (S.Fits B A) := by
  unfold Fits; infer_instance

/-- FRI's folds with inputs injected at `heights`, times `|𝕂|`: the sum of the level bounds of the
plan's folds. -/
def friFoldsNum (B : McaBound) (A : Analysis) (heights : List ℕ) : ℚ :=
  ((S.friPlan heights).map (A.levelBound B S.params.logBlowup)).sum

/-- FRI's largest fold with inputs injected at `heights`, times `|𝕂|`. -/
def friFoldMax (B : McaBound) (A : Analysis) (heights : List ℕ) : ℚ :=
  maxQ ((S.friPlan heights).map (A.levelBound B S.params.logBlowup))

/-- The density `1 - δ + #folds · loss` of query positions where FRI's checks may pass. -/
def queryDensity (A : Analysis) (heights : List ℕ) : ℚ :=
  1 - A.δ + (S.friPlan heights).length * A.loss

/-- The terms of the knowledge error's bound for `|F| = p`, by challenge, for the shape `c`. -/
def knowledgeErrorTermsOf (c : Shape) (p : ℕ) (B : McaBound) (A : Analysis) :
    List (String × ℚ) :=
  [("constraint folding", c.foldingNum S.params.logBlowup A / (p : ℚ) ^ Challenge.d EF),
    ("out of domain", c.outOfDomainNum S.params.logBlowup A / (p : ℚ) ^ Challenge.d EF),
    ("batching", c.batchingNum S.params.logBlowup B A c.numOpened / (p : ℚ) ^ Challenge.d EF),
    ("FRI folds", S.friFoldsNum B A [] / (p : ℚ) ^ Challenge.d EF),
    ("FRI queries", S.queryDensity A [] ^ S.params.numQueries)]

/-- The terms of the knowledge error's bound for `|F| = p`, by challenge. -/
def knowledgeErrorTerms (p : ℕ) (B : McaBound) (A : Analysis) : List (String × ℚ) :=
  S.knowledgeErrorTermsOf S.shape p B A

/-- The bound on the knowledge error: the sum of its terms. -/
def knowledgeErrorBound (p : ℕ) (B : McaBound) (A : Analysis) : ℚ :=
  sumTerms (S.knowledgeErrorTerms p B A)

/-- The calculator certifies `bits` bits of knowledge soundness with the MCA bound `B`. -/
def Secure (p : ℕ) (B : McaBound) (A : Analysis) (bits : ℕ) : Prop :=
  S.Fits B A ∧ S.knowledgeErrorBound p B A ≤ 1 / 2 ^ bits

instance (p : ℕ) (B : McaBound) (A : Analysis) (bits : ℕ) : Decidable (S.Secure p B A bits) := by
  unfold Secure; infer_instance

end Setup

namespace Setup
variable (S : Setup EF)

/-- The terms of the round error's bound for `|F| = p`, by round, each after `α` credited with
its grinding, for the shape `c`. -/
def roundErrorTermsOf (c : Shape) (p : ℕ) (B : McaBound) (A : Analysis) :
    List (String × ℚ) :=
  [("constraint folding", c.foldingNum S.params.logBlowup A / (p : ℚ) ^ Challenge.d EF),
    ("out of domain", powFractionQ p S.params.oodPowBits *
      (c.outOfDomainNum S.params.logBlowup A / (p : ℚ) ^ Challenge.d EF)),
    ("batching", powFractionQ p S.params.batchPowBits *
      (c.batchingNum S.params.logBlowup B A c.numOpened / (p : ℚ) ^ Challenge.d EF)),
    ("FRI folds", powFractionQ p S.params.commitPowBits *
      (S.friFoldMax B A [] / (p : ℚ) ^ Challenge.d EF)),
    ("FRI queries", powFractionQ p S.params.queryPowBits *
      (S.queryDensity A [] + 1 / p) ^ S.params.numQueries)]

/-- The terms of the round error's bound for `|F| = p`, by round. -/
def roundErrorTerms (p : ℕ) (B : McaBound) (A : Analysis) : List (String × ℚ) :=
  S.roundErrorTermsOf S.shape p B A

/-- The bound on the round error: the largest of its terms. -/
def roundErrorBound (p : ℕ) (B : McaBound) (A : Analysis) : ℚ :=
  maxTerms (S.roundErrorTerms p B A)

/-- The calculator certifies `bits` bits per oracle answer with the MCA bound `B`. -/
def SecureRo (p : ℕ) (B : McaBound) (A : Analysis) (bits : ℕ) : Prop :=
  S.Fits B A ∧ S.roundErrorBound p B A ≤ 1 / 2 ^ bits

instance (p : ℕ) (B : McaBound) (A : Analysis) (bits : ℕ) : Decidable (S.SecureRo p B A bits) := by
  unfold SecureRo; infer_instance

end Setup

/-- The opened words of the shapes of log trace length `logN`, batched together. -/
def groupNumOpenedOf (shapes : List Shape) (logN : ℕ) : ℕ :=
  (shapes.map fun c ↦ if c.logN = logN then c.numOpened else 0).sum

namespace Batch.Setup
variable {withLookups : Bool} (S : Batch.Setup EF withLookups)

/-- The instances' shapes. -/
def shapes : List Shape := (List.finRange S.k).map fun i ↦ (S.instanceSetup i).shape

/-- LogUp's numbers, `T + (T - 1) W`. -/
def lookupCount : ℕ := S.numInteractions + (S.numInteractions - 1) * S.lookupWidth

/-- The analysis fits `S` with the MCA bound `B`: it is valid at the rate, `δ ≤ δ' - 2/N` on every
domain, and `B` admits each instance's batching and FRI's folds. -/
def Fits (B : McaBound) (A : Analysis) : Prop :=
  A.Valid S.domainSetup.rateQ ∧
    (∀ i ∈ List.finRange S.k, A.δ ≤ A.δ' - 2 / (S.instanceSetup i).size ∧
      B.admits (S.instanceSetup i).size (S.instanceSetup i).n A.δ) ∧
    A.Admits B S.params.logBlowup (S.domainSetup.friPlan S.friHeights)

instance (B : McaBound) (A : Analysis) : Decidable (S.Fits B A) := by unfold Fits; infer_instance

/-- The terms of the batch's knowledge error bound for `|F| = p`, the instance terms at their
worst instance, for the instances' shapes `cs` and LogUp's numbers `lookupCount`: LogUp's error
`ℓᵏ (T + (T - 1) W)`, each instance's batching over the opened words of its domain size. -/
def knowledgeErrorTermsOf (cs : List Shape) (lookupCount p : ℕ) (B : McaBound) (A : Analysis) :
    List (String × ℚ) :=
  let lb := S.params.logBlowup
  [("lookup challenges", ((A.listBound S.domainSetup.rateQ ^ S.k * lookupCount : ℕ) : ℚ) /
      (p : ℚ) ^ Challenge.d EF),
    ("constraint folding", maxQ (cs.map (·.foldingNum lb A)) / (p : ℚ) ^ Challenge.d EF),
    ("out of domain", maxQ (cs.map (·.outOfDomainNum lb A)) / (p : ℚ) ^ Challenge.d EF),
    ("batching", maxQ (cs.map fun c ↦ c.batchingNum lb B A (groupNumOpenedOf cs c.logN)) /
      (p : ℚ) ^ Challenge.d EF),
    ("FRI folds", S.domainSetup.friFoldsNum B A S.friHeights / (p : ℚ) ^ Challenge.d EF),
    ("FRI queries", S.domainSetup.queryDensity A S.friHeights ^ S.params.numQueries)]

/-- The terms of the batch's knowledge error bound for `|F| = p`. -/
def knowledgeErrorTerms (p : ℕ) (B : McaBound) (A : Analysis) : List (String × ℚ) :=
  S.knowledgeErrorTermsOf S.shapes S.lookupCount p B A

/-- The bound on the batch's knowledge error: the sum of its terms. -/
def knowledgeErrorBound (p : ℕ) (B : McaBound) (A : Analysis) : ℚ :=
  sumTerms (S.knowledgeErrorTerms p B A)

/-- The calculator certifies `bits` bits of knowledge soundness for the batch with the MCA bound
`B`. -/
def Secure (p : ℕ) (B : McaBound) (A : Analysis) (bits : ℕ) : Prop :=
  S.Fits B A ∧ S.knowledgeErrorBound p B A ≤ 1 / 2 ^ bits

instance (p : ℕ) (B : McaBound) (A : Analysis) (bits : ℕ) : Decidable (S.Secure p B A bits) := by
  unfold Secure; infer_instance

/-- The terms of the batch's round error bound for `|F| = p`, by round, the instance terms at
their worst instance, each but `α` credited with its grinding, for the instances' shapes `cs` and
LogUp's numbers `lookupCount`. -/
def roundErrorTermsOf (cs : List Shape) (lookupCount p : ℕ) (B : McaBound) (A : Analysis) :
    List (String × ℚ) :=
  let lb := S.params.logBlowup
  [("lookup challenges", powFractionQ p S.params.lookupPowBits *
      (((A.listBound S.domainSetup.rateQ ^ S.k * lookupCount : ℕ) : ℚ) /
        (p : ℚ) ^ Challenge.d EF)),
    ("constraint folding", maxQ (cs.map (·.foldingNum lb A)) / (p : ℚ) ^ Challenge.d EF),
    ("out of domain", powFractionQ p S.params.oodPowBits *
      (maxQ (cs.map (·.outOfDomainNum lb A)) / (p : ℚ) ^ Challenge.d EF)),
    ("batching", powFractionQ p S.params.batchPowBits *
      (maxQ (cs.map fun c ↦ c.batchingNum lb B A (groupNumOpenedOf cs c.logN)) /
        (p : ℚ) ^ Challenge.d EF)),
    ("FRI folds", powFractionQ p S.params.commitPowBits *
      (S.domainSetup.friFoldMax B A S.friHeights / (p : ℚ) ^ Challenge.d EF)),
    ("FRI queries", powFractionQ p S.params.queryPowBits *
      (S.domainSetup.queryDensity A S.friHeights + 1 / p) ^ S.params.numQueries)]

/-- The terms of the batch's round error bound for `|F| = p`. -/
def roundErrorTerms (p : ℕ) (B : McaBound) (A : Analysis) : List (String × ℚ) :=
  S.roundErrorTermsOf S.shapes S.lookupCount p B A

/-- The bound on the batch's round error: the largest of its terms. -/
def roundErrorBound (p : ℕ) (B : McaBound) (A : Analysis) : ℚ :=
  maxTerms (S.roundErrorTerms p B A)

/-- The calculator certifies `bits` bits per oracle answer for the batch with the MCA bound `B`. -/
def SecureRo (p : ℕ) (B : McaBound) (A : Analysis) (bits : ℕ) : Prop :=
  S.Fits B A ∧ S.roundErrorBound p B A ≤ 1 / 2 ^ bits

instance (p : ℕ) (B : McaBound) (A : Analysis) (bits : ℕ) : Decidable (S.SecureRo p B A bits) := by
  unfold SecureRo; infer_instance

end Batch.Setup

/-! ### The search

The bounds pull the parameters apart: the queries want `δ` large and a small loss, the curve and
lossy bounds want them away from the unique-decoding radius `u = (1 - ρ) / 2`, the MCA bound's
counts grow with `δ`, and the list sizes want `δ'` small. `search` minimizes a bound over a grid of
analyses by coordinate descent, with `J = 1 - r`, `r ≥ √ρ` a dyadic upper bound: FRI at
`u - 2 ^ (-a)` for `a ≤ 40`, at `(a - 40) / 64` of the way from `u` to `J` for `40 < a ≤ 104`,
and at `J - (J - u) / (64 · 2 ^ (a - 104))` for `104 < a ≤ 124`; the loss `2 ^ (-b)`; and the
extractor, for `c < 16`, at `u - 2 ^ (-a-1-c)` below `u` and at `δ + (J - δ) / 2 ^ (c + 1)` above
it, or for `16 ≤ c < 23` at `(c - 15) / 8` of the way from `u` to `J`. It is computation only: what
it finds is checked by `Secure` or `SecureRo`. -/

/-- The analysis at grid point `(a, b, c)` for rate `ρ`. -/
def Analysis.grid (ρ : ℚ) (a b c : ℕ) : Analysis :=
  let udr := (1 - ρ) / 2
  let johnson := 1 - McaBound.sqrtUpper ρ
  let δ := if a ≤ 40 then udr - 1 / 2 ^ a
    else if a ≤ 104 then udr + (a - 40) * (johnson - udr) / 64
    else johnson - (johnson - udr) / (64 * 2 ^ (a - 104))
  ⟨δ,
    if c < 16 then (if a ≤ 40 then udr - 1 / 2 ^ (a + 1 + c) else δ + (johnson - δ) / 2 ^ (c + 1))
    else udr + (c - 15) * (johnson - udr) / 8,
    1 / 2 ^ b⟩

/-- `x` is a better value than `y`: smaller, or `y` does not fit. -/
def better : Option ℚ → Option ℚ → Bool
  | some x, some y => x < y
  | some _, none => true
  | none, _ => false

/-- The best point of `f` among `lo, …, hi` and the current `(x, f x)`. -/
def bestOn (f : ℕ → Option ℚ) (lo hi : ℕ) (cur : ℕ × Option ℚ) : ℕ × Option ℚ :=
  (List.range (hi + 1 - lo)).foldl (fun best i ↦
    let v := f (lo + i)
    if better v best.2 then (lo + i, v) else best) cur

/-- Coordinate descent of `bound` (`none` where the analysis does not fit) over the grid, `rounds`
times over `a ∈ [1, 124]`, `b ∈ [1, 60]` and `c ∈ [0, 22]`, from `(8, 16, 1)`. -/
def search (ρ : ℚ) (bound : Analysis → Option ℚ) : (rounds : ℕ) → ℕ × ℕ × ℕ → ℕ × ℕ × ℕ
  | 0, x => x
  | rounds + 1, (a, b, c) =>
    let f (a b c : ℕ) := bound (Analysis.grid ρ a b c)
    let a := (bestOn (f · b c) 1 124 (a, f a b c)).1
    let b := (bestOn (f a · c) 1 60 (b, f a b c)).1
    let c := (bestOn (f a b ·) 0 22 (c, f a b c)).1
    search ρ bound rounds (a, b, c)

/-- The analysis `search` finds in three rounds. -/
def bestAnalysisOf (ρ : ℚ) (bound : Analysis → Option ℚ) : Analysis :=
  let (a, b, c) := search ρ bound 3 (8, 16, 1)
  Analysis.grid ρ a b c

/-- The analysis of the smallest knowledge error bound the search finds for `|F| = p` with the MCA
bound `B`. -/
def Setup.bestAnalysis {lookups : List (Lookup F)} (S : Setup EF lookups) (p : ℕ)
    (B : McaBound) : Analysis :=
  let c := S.shape
  bestAnalysisOf S.rateQ fun A ↦
    if S.Fits B A then some (sumTerms (S.knowledgeErrorTermsOf c p B A)) else none

/-- The analysis of the smallest round error bound the search finds for `|F| = p` with the MCA
bound `B`. -/
def Setup.bestAnalysisRo (S : Setup EF) (p : ℕ) (B : McaBound) : Analysis :=
  let c := S.shape
  bestAnalysisOf S.rateQ fun A ↦
    if S.Fits B A then some (maxTerms (S.roundErrorTermsOf c p B A)) else none

/-- The analysis of the smallest batch knowledge error bound the search finds for `|F| = p` with
the MCA bound `B`. -/
def Batch.Setup.bestAnalysis {withLookups : Bool} (S : Batch.Setup EF withLookups) (p : ℕ)
    (B : McaBound) : Analysis :=
  let cs := S.shapes
  let t := S.lookupCount
  bestAnalysisOf S.domainSetup.rateQ fun A ↦
    if S.Fits B A then some (sumTerms (S.knowledgeErrorTermsOf cs t p B A)) else none

/-- The analysis of the smallest batch round error bound the search finds for `|F| = p` with the
MCA bound `B`. -/
def Batch.Setup.bestAnalysisRo {withLookups : Bool} (S : Batch.Setup EF withLookups) (p : ℕ)
    (B : McaBound) : Analysis :=
  let cs := S.shapes
  let t := S.lookupCount
  bestAnalysisOf S.domainSetup.rateQ fun A ↦
    if S.Fits B A then some (maxTerms (S.roundErrorTermsOf cs t p B A)) else none

/-! ### Reports -/

/-- `log₂ n` as a float, from the leading `61` bits of `n`. -/
def log2Float (n : ℕ) : Float :=
  let s := n.log2 - 60
  Float.log2 (n >>> s).toFloat + s.toFloat

/-- The bits of security of an error `x`: `-log₂ x`, infinite for `x ≤ 0`. -/
def securityBits (x : ℚ) : Float :=
  if x ≤ 0 then 1 / 0 else log2Float x.den - log2Float x.num.natAbs

/-- A rational as a float. -/
def ratFloat (x : ℚ) : Float :=
  (if x < 0 then -1 else 1) * Float.exp2 (log2Float x.num.natAbs - log2Float x.den)

/-- A calculator's report: the analysis, whether it fits the setup, and the bits of security of
each term and of the bound. -/
structure Report where
  analysis : Analysis
  fits : Bool
  terms : List (String × Float)
  total : Float

instance : Repr Report where
  reprPrec r _ :=
    let analysis := s!"δ: {ratFloat r.analysis.δ}, δ': {ratFloat r.analysis.δ'}, " ++
      s!"loss: 2^{-securityBits r.analysis.loss}"
    .joinSep (((analysis :: s!"fits: {r.fits}" :: r.terms.map fun (n, b) ↦ s!"{n}: {b}") ++
      [s!"total: {r.total}"]).map Std.Format.text) .line

/-- A report from the analysis, its fit, the terms and the bound. -/
def Report.of (A : Analysis) (fits : Bool) (terms : List (String × ℚ)) (bound : ℚ) : Report :=
  ⟨A, fits, terms.map fun (n, x) ↦ (n, securityBits x), securityBits bound⟩

/-- The knowledge error's report for `|F| = p` with the MCA bound `B`. -/
def Setup.knowledgeErrorReport {lookups : List (Lookup F)} (S : Setup EF lookups) (p : ℕ)
    (B : McaBound) (A : Analysis) : Report :=
  .of A (decide (S.Fits B A)) (S.knowledgeErrorTerms p B A) (S.knowledgeErrorBound p B A)

/-- The round error's report for `|F| = p` with the MCA bound `B`. -/
def Setup.roundErrorReport (S : Setup EF) (p : ℕ) (B : McaBound) (A : Analysis) : Report :=
  .of A (decide (S.Fits B A)) (S.roundErrorTerms p B A) (S.roundErrorBound p B A)

/-- The batch's knowledge error report for `|F| = p` with the MCA bound `B`. -/
def Batch.Setup.knowledgeErrorReport {withLookups : Bool} (S : Batch.Setup EF withLookups)
    (p : ℕ) (B : McaBound) (A : Analysis) : Report :=
  .of A (decide (S.Fits B A)) (S.knowledgeErrorTerms p B A) (S.knowledgeErrorBound p B A)

/-- The batch's round error report for `|F| = p` with the MCA bound `B`. -/
def Batch.Setup.roundErrorReport {withLookups : Bool} (S : Batch.Setup EF withLookups) (p : ℕ)
    (B : McaBound) (A : Analysis) : Report :=
  .of A (decide (S.Fits B A)) (S.roundErrorTerms p B A) (S.roundErrorBound p B A)

end CompStark.Iop
