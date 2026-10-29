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
`K = p ^ d`, `N` the domain's size and `ℓ` the list bound at `δ'` (`1` below the
unique-decoding radius, `⌊(1 - δ' - ρ) / ((1 - δ')² - ρ)⌋` above, the Johnson bound):

* constraint folding: `ℓ ℓₚ (#constraints - 1) / K`, `ℓₚ` the permutation trace's list bound, `1`
  without lookups;
* out of domain: `(ℓ identityDegree + n + N) / K`, `ℓ` bounding the list of the committed words
  as one family;
* batching `m` words: `B`'s count for curves of degree `m - 1` on `N` points over `K`, or for
  `δ < δ'` and `δ ≤ (1 - ρ) / 2 - 1/N` the curve bound `(m - 1) max(T₁, T₂) / K`,
  `T₁ = (1 - ρ - δ) / (δ (1 - ρ - 2δ))`, `T₂ = δ' / (δ' - δ)`, if smaller;
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
at most `2 ^ (-bits)`; a statement's (`Statement.Secure`, `Batch.Statement.Secure`, and their
`SecureRo`) checks every trace length the verifier admits. The analysis need not be picked by
hand: `Setup.bestAnalysis` (`bestAnalysisRo`) searches the radii and the loss for the smallest
bound, and `decide +kernel` checks the analysis it finds.
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

/-- The out-of-domain point, times `|𝕂|`: `ℓ identityDegree + n + N`, `ℓ` the list bound of the
committed words as one family. -/
def outOfDomainNum : ℚ :=
  (A.listBound (1 / 2 ^ logBlowup) * c.identityDegree + 2 ^ c.logN + 2 ^ (c.logN + logBlowup) : ℕ)

/-- Batching `m` opened words on the domain of `N = 2 ^ (logN + logBlowup)` points at rate
`ρ = 1 / 2 ^ logBlowup`, times `|𝕂|`: the MCA bound `B`'s count for curves of degree `m - 1`, or
for `δ < δ'` and `δ ≤ (1 - ρ) / 2 - 1/N` the curve bound `(m - 1) max(T₁, T₂)` if smaller. -/
def batchingNum (m : ℕ) : ℚ :=
  let N : ℕ := 2 ^ (c.logN + logBlowup)
  let ρ : ℚ := 1 / 2 ^ logBlowup
  let count := B.count N (2 ^ c.logN) (m - 1) A.δ
  if A.δ < A.δ' ∧ A.δ ≤ (1 - ρ) / 2 - 1 / N then
    min count (((m - 1 : ℕ) : ℚ) * max (A.curveT₁ ρ) (A.δ' / (A.δ' - A.δ)))
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

/-- The analysis fits `S` with the MCA bound `B`: it is valid at `S`'s rate, and `B` admits
batching and FRI's folds. -/
def Fits (B : McaBound) (A : Analysis) : Prop :=
  A.Valid S.rateQ ∧ B.admits S.size S.n A.δ ∧
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

/-- The analysis fits `S` with the MCA bound `B`: it is valid at the rate, and `B` admits each
instance's batching and FRI's folds. -/
def Fits (B : McaBound) (A : Analysis) : Prop :=
  A.Valid S.domainSetup.rateQ ∧
    (∀ i ∈ List.finRange S.k, B.admits (S.instanceSetup i).size (S.instanceSetup i).n A.δ) ∧
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



/-! ### Statements

A statement's round error is the largest over the trace lengths the verifier admits
(`Statement.roundError`), and so is its knowledge error (`Statement.knowledgeError`).
`Statement.SecureRo` and `Statement.Secure` check every admitted length below the two-adicity at
one analysis: the verifier's checks on a length are a Boolean (`Statement.admits`), and at the
length where FRI does not fold the calculator's terms bound the error without folds
(`roundError0_le_bound`). -/

namespace Statement
variable (C : Statement F)

/-- The verifier's checks on a trace length `2 ^ n`, as a Boolean: the periodic columns fit, `L`
and the quotient domain fit the two-adic subgroups, FRI's parameters are positive, its final
polynomial no longer than the trace, and a preprocessed AIR's length is its trace's. -/
def admits (n : ℕ) : Bool :=
  C.air.periodicFits n && decide (n + C.params.logBlowup ≤ twoAdicity F) &&
    decide (n + C.air.logQuotientChunks n ≤ twoAdicity F) && decide (0 < C.params.maxLogArity) &&
    decide (C.params.logFinalPolyLen ≤ n) && decide (0 < C.params.numQueries) &&
    decide (0 < C.params.logBlowup) &&
    (C.air.preprocessedWidth == 0 || n == C.preprocessedLogN)

theorem admits_iff (n : ℕ) : C.admits n = true ↔ C.Admits n := by
  simp only [admits, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨hp, ht⟩, hq⟩, hm⟩, hf⟩, hn⟩, hb⟩, hpre⟩
    refine ⟨⟨C.colsInWidth, hp, ht, hq, hm, hf, hn, hb⟩, fun hw ↦ ?_⟩
    rcases hpre with h0 | h
    · omega
    · exact h
  · rintro ⟨hs, hpre⟩
    refine ⟨⟨⟨⟨⟨⟨⟨hs.periodicFits, hs.twoAdic⟩, hs.quotientFits⟩, hs.folds⟩, hs.finalPolyFits⟩,
      hs.queries⟩, hs.blowup⟩, ?_⟩
    by_cases hw : C.air.preprocessedWidth = 0
    · exact Or.inl hw
    · exact Or.inr (hpre (Nat.pos_of_ne_zero hw))

variable (EF : Type) [Challenge F EF]

/-- The STARK at a length `admits` admits. -/
def setupOf (n : ℕ) (h : C.admits n = true) : Setup EF :=
  C.setupAt EF n ((C.admits_iff n).mp h)

/-- The calculator certifies `bits` bits per oracle answer at the analysis `A` at every trace
length the verifier admits. -/
def SecureRo (p : ℕ) (B : McaBound) (A : Analysis) (bits : ℕ) : Prop :=
  ∀ n < twoAdicity F + 1, ∀ h : C.admits n = true, (C.setupOf EF n h).SecureRo p B A bits

instance (p : ℕ) (B : McaBound) (A : Analysis) (bits : ℕ) :
    Decidable (C.SecureRo EF p B A bits) := by
  unfold SecureRo; infer_instance

/-- The calculator certifies `bits` bits of knowledge soundness at the analysis `A` at every trace
length the verifier admits. -/
def Secure (p : ℕ) (B : McaBound) (A : Analysis) (bits : ℕ) : Prop :=
  ∀ n < twoAdicity F + 1, ∀ h : C.admits n = true, (C.setupOf EF n h).Secure p B A bits

instance (p : ℕ) (B : McaBound) (A : Analysis) (bits : ℕ) :
    Decidable (C.Secure EF p B A bits) := by
  unfold Secure; infer_instance

end Statement

/-! ### Batch statements

A batch statement's round error is the largest over the vectors of trace lengths the verifier
admits (`Batch.Statement.roundError`). The vectors are too many to enumerate (`25 ^ 3` for three
instances over KoalaBear), so the statement's terms (`Batch.Statement.roundErrorTerms`) bound each
term of the batch's bound (`Batch.Setup.roundErrorTerms`) over the term's own parameters: the
verifier's checks on an instance's length are a Boolean (`Batch.Statement.admits`), and the
admitted vectors are those of admitted lengths. Constraint folding, the out-of-domain point and
batching take the largest over every instance's shape at every admitted length (`allShapes`),
batching at the most opened words a domain size can have (`groupBound`); LogUp is at every
instance's longest admitted length (`lookupCountMax`), its interactions growing with every length;
FRI's folds at every arity, target height and injection a fold can have (`foldPlans`); and the
queries at the most folds, `twoAdicity - logBlowup - logFinalPolyLen`. The knowledge error's terms
(`Batch.Statement.knowledgeErrorTerms`) are the same without grinding, but for FRI's folds, which
the knowledge error sums over the plan: a plan's folds fold onto distinct heights
(`FriGame.Rounds.pairwise_plan`), so the sum over the heights of the worst fold onto each bounds
it. -/

namespace Batch.Statement
variable (C : Batch.Statement F)

/-- The verifier's checks on instance `i`'s length `2 ^ m`, as a Boolean: the periodic columns
fit, its domain and its quotient domain, without and with the lookups' LogUp constraints, fit the
two-adic subgroups, FRI's parameters are positive, its final polynomial no longer than the trace,
and an instance with preprocessed columns is at its keygen height. -/
def admits (i : Fin C.k) (m : ℕ) : Bool :=
  (C.air i).periodicFits m && decide (m + C.params.logBlowup ≤ twoAdicity F) &&
    decide (m + (C.air i).logQuotientChunks m ≤ twoAdicity F) &&
    decide (m + (C.air i).logQuotientChunksWith m (Lookup.logUpConstraints (C.lookups i)) ≤
      twoAdicity F) &&
    decide (0 < C.params.maxLogArity) && decide (C.params.logFinalPolyLen ≤ m) &&
    decide (0 < C.params.numQueries) && decide (0 < C.params.logBlowup) &&
    ((C.air i).preprocessedWidth == 0 || m == C.keyLogN i)

theorem admits_spec {i : Fin C.k} {m : ℕ} (h : C.admits i m = true) :
    SoundConfig C.params (C.air i) m ∧
      m + (C.air i).logQuotientChunksWith m (Lookup.logUpConstraints (C.lookups i)) ≤
        twoAdicity F ∧ (0 < (C.air i).preprocessedWidth → m = C.keyLogN i) := by
  simp only [admits, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hp, ht⟩, hq⟩, hw⟩, hm⟩, hf⟩, hn⟩, hb⟩, hpre⟩ := h
  refine ⟨⟨C.colsInWidth i, hp, ht, hq, hm, hf, hn, hb⟩, hw, fun hpw ↦ ?_⟩
  rcases hpre with h0 | h
  · omega
  · exact h

/-- An admitted vector's lengths each pass the verifier's checks on their instance. -/
theorem _root_.CompStark.Iop.Batch.Statement.Admits.admits {C : Batch.Statement F}
    {n : Fin C.k → ℕ} (h : C.Admits n) (i : Fin C.k) : C.admits i (n i) = true := by
  have hs := h.sound i
  simp only [Batch.Statement.admits, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨hs.periodicFits, hs.twoAdic⟩, hs.quotientFits⟩, h.quotient i⟩, hs.folds⟩,
    hs.finalPolyFits⟩, hs.queries⟩, hs.blowup⟩, ?_⟩
  by_cases hw : (C.air i).preprocessedWidth = 0
  · exact Or.inl hw
  · exact Or.inr (h.keyed i (Nat.pos_of_ne_zero hw))

/-- Instance `i`'s longest admitted length, `0` if it has none. -/
def maxLength (i : Fin C.k) : ℕ :=
  ((List.range (twoAdicity F + 1)).filter (C.admits i)).foldr max 0

/-- LogUp's numbers `T + (T - 1) W` with every instance at its longest admitted length. -/
def lookupCountMax : ℕ :=
  let T := ((List.finRange C.k).map fun i ↦
    2 ^ C.maxLength i * ((C.lookups i).map (·.tuples.length)).sum).sum
  T + (T - 1) * Lookup.maxWidth (List.ofFn C.lookups).flatten

/-- The log sizes FRI's folds can fold onto on a vector of admitted lengths:
`logFinalPolyLen + logBlowup ≤ m` below the two-adicity. -/
def foldHeights : List ℕ :=
  List.range' (C.params.logFinalPolyLen + C.params.logBlowup)
    (twoAdicity F - (C.params.logFinalPolyLen + C.params.logBlowup))

/-- The folds FRI can make onto `2 ^ m` points, as data (`FriGame.Rounds.plan`): by `1` to
`maxLogArity` bits, injecting an input or not. -/
def foldsOnto (m : ℕ) : List (ℕ × ℕ × Bool) :=
  (List.range' 1 C.params.maxLogArity).flatMap fun la ↦ [(la, m, false), (la, m, true)]

/-- The folds FRI can make on a vector of admitted lengths: onto every height of `foldHeights`. -/
def foldPlans : List (ℕ × ℕ × Bool) := C.foldHeights.flatMap C.foldsOnto

variable (EF : Type) [Challenge F EF]

/-- Instance `i` as a STARK of its own on `2 ^ m` rows, at a length `admits` admits. -/
def instanceOf (i : Fin C.k) (m : ℕ) (h : C.admits i m = true) : Iop.Setup EF (C.lookups i) :=
  ⟨C.params, C.air i, m, (C.admits_spec h).1,
    C.lookupsValid_of_quotient i m (C.admits_spec h).2.1⟩

/-- Instance `i`'s shapes at its admitted lengths. -/
def shapesAt (i : Fin C.k) : List Shape :=
  (List.range (twoAdicity F + 1)).flatMap fun m ↦
    if h : C.admits i m = true then [(C.instanceOf EF i m h).shape] else []

/-- Every instance's shapes at its admitted lengths. -/
def allShapes : List Shape := (List.finRange C.k).flatMap (C.shapesAt EF)

/-- The most opened words a domain size can batch: every instance's most at an admitted
length. -/
def groupBound : ℕ :=
  ((List.finRange C.k).map fun i ↦ ((C.shapesAt EF i).map (·.numOpened)).foldr max 0).sum

/-- The analysis fits every vector of admitted lengths with the MCA bound `B`: it is valid at the
rate, and `B` admits every instance's batching at every admitted length and every fold FRI can
make. -/
def Fits (B : McaBound) (A : Analysis) : Prop :=
  A.Valid (1 / 2 ^ C.params.logBlowup) ∧
    (∀ c ∈ C.allShapes EF, B.admits (2 ^ (c.logN + C.params.logBlowup)) (2 ^ c.logN) A.δ) ∧
    A.Admits B C.params.logBlowup C.foldPlans

instance (B : McaBound) (A : Analysis) : Decidable (C.Fits EF B A) := by
  unfold Fits; infer_instance

/-- The terms of the statement's round error bound for `|F| = p`, by round, each the largest of
the batch's term over the term's parameters at the admitted vectors of lengths. -/
def roundErrorTerms (p : ℕ) (B : McaBound) (A : Analysis) : List (String × ℚ) :=
  let lb := C.params.logBlowup
  let K := (p : ℚ) ^ Challenge.d EF
  [("lookup challenges", powFractionQ p C.params.lookupPowBits *
      (((A.listBound (1 / 2 ^ lb) ^ C.k * C.lookupCountMax : ℕ) : ℚ) / K)),
    ("constraint folding", maxQ ((C.allShapes EF).map (·.foldingNum lb A)) / K),
    ("out of domain", powFractionQ p C.params.oodPowBits *
      (maxQ ((C.allShapes EF).map (·.outOfDomainNum lb A)) / K)),
    ("batching", powFractionQ p C.params.batchPowBits *
      (maxQ ((C.allShapes EF).map fun c ↦ c.batchingNum lb B A (C.groupBound EF)) / K)),
    ("FRI folds", powFractionQ p C.params.commitPowBits *
      (maxQ (C.foldPlans.map (A.levelBound B lb)) / K)),
    ("FRI queries", powFractionQ p C.params.queryPowBits *
      (1 - A.δ + ((twoAdicity F - (C.params.logFinalPolyLen + lb) : ℕ) : ℚ) * A.loss + 1 / p) ^
        C.params.numQueries)]

/-- The bound on the statement's round error: the largest of its terms. -/
def roundErrorBound (p : ℕ) (B : McaBound) (A : Analysis) : ℚ :=
  maxTerms (C.roundErrorTerms EF p B A)

/-- The calculator certifies `bits` bits per oracle answer at the analysis `A` at every vector of
trace lengths the verifier admits. -/
def SecureRo (p : ℕ) (B : McaBound) (A : Analysis) (bits : ℕ) : Prop :=
  C.Fits EF B A ∧ C.roundErrorBound EF p B A ≤ 1 / 2 ^ bits

instance (p : ℕ) (B : McaBound) (A : Analysis) (bits : ℕ) :
    Decidable (C.SecureRo EF p B A bits) := by
  unfold SecureRo; infer_instance

/-- The terms of the statement's knowledge error bound for `|F| = p`, by challenge, each the
largest of the batch's term over the term's parameters at the admitted vectors of lengths. FRI's
folds are a sum over the plan's folds, whose target sizes are distinct: the sum over the heights
`foldHeights` of the worst fold onto each bounds it. -/
def knowledgeErrorTerms (p : ℕ) (B : McaBound) (A : Analysis) : List (String × ℚ) :=
  let lb := C.params.logBlowup
  let K := (p : ℚ) ^ Challenge.d EF
  [("lookup challenges", ((A.listBound (1 / 2 ^ lb) ^ C.k * C.lookupCountMax : ℕ) : ℚ) / K),
    ("constraint folding", maxQ ((C.allShapes EF).map (·.foldingNum lb A)) / K),
    ("out of domain", maxQ ((C.allShapes EF).map (·.outOfDomainNum lb A)) / K),
    ("batching", maxQ ((C.allShapes EF).map fun c ↦ c.batchingNum lb B A (C.groupBound EF)) / K),
    ("FRI folds",
      (C.foldHeights.map fun m ↦ maxQ ((C.foldsOnto m).map (A.levelBound B lb))).sum / K),
    ("FRI queries",
      (1 - A.δ + ((twoAdicity F - (C.params.logFinalPolyLen + lb) : ℕ) : ℚ) * A.loss) ^
        C.params.numQueries)]

/-- The bound on the statement's knowledge error: the sum of its terms. -/
def knowledgeErrorBound (p : ℕ) (B : McaBound) (A : Analysis) : ℚ :=
  sumTerms (C.knowledgeErrorTerms EF p B A)

/-- The calculator certifies `bits` bits of knowledge soundness at the analysis `A` at every vector
of trace lengths the verifier admits. -/
def Secure (p : ℕ) (B : McaBound) (A : Analysis) (bits : ℕ) : Prop :=
  C.Fits EF B A ∧ C.knowledgeErrorBound EF p B A ≤ 1 / 2 ^ bits

instance (p : ℕ) (B : McaBound) (A : Analysis) (bits : ℕ) :
    Decidable (C.Secure EF p B A bits) := by
  unfold Secure; infer_instance

end Batch.Statement

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

/-- The batch statement's knowledge error report for `|F| = p` with the MCA bound `B`. -/
def Batch.Statement.knowledgeErrorReport (C : Batch.Statement F) (EF : Type) [Challenge F EF]
    (p : ℕ) (B : McaBound) (A : Analysis) : Report :=
  .of A (decide (C.Fits EF B A)) (C.knowledgeErrorTerms EF p B A)
    (C.knowledgeErrorBound EF p B A)

/-- The batch statement's round error report for `|F| = p` with the MCA bound `B`. -/
def Batch.Statement.roundErrorReport (C : Batch.Statement F) (EF : Type) [Challenge F EF]
    (p : ℕ) (B : McaBound) (A : Analysis) : Report :=
  .of A (decide (C.Fits EF B A)) (C.roundErrorTerms EF p B A) (C.roundErrorBound EF p B A)


end CompStark.Iop
