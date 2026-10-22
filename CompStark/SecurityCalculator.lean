/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.BatchNonInteractiveError

/-! # The security calculator

Rational upper bounds on the knowledge errors (`knowledgeError`, `Batch.knowledgeError`) and the
random-oracle round errors (`roundError`, `Batch.roundError`), computed from a setup's numbers:
its constraint count and identity degree, its opened words, its lookups' interactions `T` and
widest tuple `W`, its heights and FRI's parameters, for a base field of `p` elements and the
challenge field's degree `d`. Every term is a rational number, so the calculator runs as code
(`#eval`, `Report`) and in the kernel (`decide +kernel`), which evaluates the AIR's structure
itself; the theorems of `CompStark/Security.lean` turn a checked bound into a bound on the error.

The analysis is the one of `CompStark/Sound/Numbers.lean`, at FRI arity `2`, with the free
parameters of `Analysis`: FRI's proximity `δ`, the extractor's `δ'` below the unique-decoding
radius `(1 - ρ) / 2`, a proximity loss `loss` and a log size `t`. With `K = p ^ d`, `N` the domain's
size and `δ'' = δ' - 2/N`:

* constraint folding: `(#constraints - 1) / K`;
* out of domain: `(identityDegree + n) / K`;
* batching `m` words: `(m - 1) N / K` (the powers MCA bound), or for `δ < δ''` the curve bound
  `(m - 1) max(T₁, T₂) / K`, `T₁ = (1 - ρ - δ) / (δ (1 - ρ - 2δ))`, `T₂ = δ'' / (δ'' - δ)`, if
  smaller;
* FRI's folds: each fold onto a domain of at least `2 ^ t` points, and each injected word, the
  lossy bound `B = max(T₁, δ_int / loss)`, `δ_int = δ + loss`; the smaller folds `2 ^ t`
  together, all over `K`;
* FRI's queries: `(1 - δ + #folds · loss) ^ numQueries`;
* a batch's lookup challenges: `(T + (T - 1) W) / K`.

The knowledge error is at most the sum of the terms, a batch's with each instance term at its
worst instance. In the random-oracle model every round is one oracle answer and the round error
is at most the largest term, each round after `α` multiplied by its grinding's `powFraction`,
FRI's folds bounded by `max(B, 2 ^ t) / K` (`max(2 B, 2 ^ t) / K` for a batch, whose injecting
folds pay twice) and its queries by `(1 - δ + #folds · loss + 1/p) ^ numQueries`.

`Setup.Secure p A bits` and `Setup.SecureRo p A bits` (and the batch's) are decidable: the
analysis fits the setup (`Setup.Fits`) and the bound is at most `2 ^ (-bits)`.
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark

/-- The free parameters of the analysis, as rationals: FRI's proximity `δ`, the extractor's `δ'`,
the proximity loss `loss` of FRI's folds, and the log size `t` of the smallest domain on which a
fold takes the lossy bound. -/
structure Analysis where
  δ : ℚ
  δ' : ℚ
  loss : ℚ
  t : ℕ

namespace Analysis
variable (A : Analysis)

/-- The curve bound's `T₁ = (1 - ρ - δ) / (δ (1 - ρ - 2δ))` at rate `ρ`. -/
def curveT₁ (ρ : ℚ) : ℚ := (1 - ρ - A.δ) / (A.δ * (1 - ρ - 2 * A.δ))

/-- The lossy bound of one fold at rate `ρ`, `max(T₁, T₂, δ_int / loss)` with
`δ_int = δ + loss` (`LossyMca.lossyBound`). -/
def lossyBound (ρ : ℚ) : ℚ :=
  max (max (A.curveT₁ ρ) ((A.δ + A.loss) / (A.δ + A.loss - A.δ))) ((A.δ + A.loss) / A.loss)

/-- The analysis' conditions at rate `ρ`: `δ` and `loss` positive, `δ'` below the
unique-decoding radius `(1 - ρ) / 2`, and `δ` below it by `2 ^ (-t)`. -/
def Valid (ρ : ℚ) : Prop :=
  0 < A.δ ∧ 0 < A.loss ∧ A.δ' < (1 - ρ) / 2 ∧ A.δ ≤ (1 - ρ) / 2 - 1 / 2 ^ A.t

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

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

namespace Setup
variable {lookups : List (Lookup F)} (S : Setup EF lookups)

/-- The rate `1 / 2 ^ logBlowup`. -/
def rateQ : ℚ := 1 / 2 ^ S.params.logBlowup

/-- The analysis fits `S`: FRI folds by arity `2`, the analysis is valid at `S`'s rate, and
`δ ≤ δ' - 2/N`. -/
def Fits (A : Analysis) : Prop :=
  S.params.maxLogArity = 1 ∧ A.Valid S.rateQ ∧ A.δ ≤ A.δ' - 2 / S.size

instance (A : Analysis) : Decidable (S.Fits A) := by unfold Fits; infer_instance

/-- Batching `m` opened words, times `|𝕂|`: the powers MCA bound `(m - 1) N`, or for
`δ < δ'' = δ' - 2/N` the curve bound `(m - 1) max(T₁, T₂)` if smaller. -/
def batchingNum (A : Analysis) (m : ℕ) : ℚ :=
  if A.δ < A.δ' - 2 / S.size then
    min (((m - 1) * S.size : ℕ) : ℚ) (((m - 1 : ℕ) : ℚ) * max (A.curveT₁ S.rateQ)
      ((A.δ' - 2 / S.size) / (A.δ' - 2 / S.size - A.δ)))
  else (((m - 1) * S.size : ℕ) : ℚ)

/-- FRI's folds with `injected` injected words, times `|𝕂|`: the lossy bound for each fold onto a
domain of at least `2 ^ t` points and each injected word, and `2 ^ t` for the smaller folds. -/
def friFoldsNum (A : Analysis) (injected : ℕ) : ℚ :=
  ((S.logN + S.params.logBlowup - A.t + injected : ℕ) : ℚ) * A.lossyBound S.rateQ + 2 ^ A.t

/-- The density `1 - δ + #folds · loss` of query positions where FRI's checks may pass. -/
def queryDensity (A : Analysis) : ℚ :=
  1 - A.δ + ((S.logN - S.params.logFinalPolyLen : ℕ) : ℚ) * A.loss

/-- The terms of the knowledge error's bound for `|F| = p`, by challenge. -/
def knowledgeErrorTerms (p : ℕ) (A : Analysis) : List (String × ℚ) :=
  [("constraint folding", ((S.numConstraints - 1 : ℕ) : ℚ) / (p : ℚ) ^ Challenge.d EF),
    ("out of domain", ((S.identityDegree + S.n : ℕ) : ℚ) / (p : ℚ) ^ Challenge.d EF),
    ("batching", S.batchingNum A S.numOpened / (p : ℚ) ^ Challenge.d EF),
    ("FRI folds", S.friFoldsNum A 0 / (p : ℚ) ^ Challenge.d EF),
    ("FRI queries", S.queryDensity A ^ S.params.numQueries)]

/-- The bound on the knowledge error: the sum of its terms. -/
def knowledgeErrorBound (p : ℕ) (A : Analysis) : ℚ := sumTerms (S.knowledgeErrorTerms p A)

/-- The calculator certifies `bits` bits of knowledge soundness. -/
def Secure (p : ℕ) (A : Analysis) (bits : ℕ) : Prop :=
  S.Fits A ∧ S.knowledgeErrorBound p A ≤ 1 / 2 ^ bits

instance (p : ℕ) (A : Analysis) (bits : ℕ) : Decidable (S.Secure p A bits) := by
  unfold Secure; infer_instance

end Setup

namespace Setup
variable (S : Setup EF)

/-- The terms of the round error's bound for `|F| = p`, by round, each after `α` credited with
its grinding. -/
def roundErrorTerms (p : ℕ) (A : Analysis) : List (String × ℚ) :=
  [("constraint folding", ((S.numConstraints - 1 : ℕ) : ℚ) / (p : ℚ) ^ Challenge.d EF),
    ("out of domain", powFractionQ p S.params.oodPowBits *
      (((S.identityDegree + S.n : ℕ) : ℚ) / (p : ℚ) ^ Challenge.d EF)),
    ("batching", powFractionQ p S.params.batchPowBits *
      (S.batchingNum A S.numOpened / (p : ℚ) ^ Challenge.d EF)),
    ("FRI folds", powFractionQ p S.params.commitPowBits *
      (max (A.lossyBound S.rateQ) (2 ^ A.t) / (p : ℚ) ^ Challenge.d EF)),
    ("FRI queries", powFractionQ p S.params.queryPowBits *
      (S.queryDensity A + 1 / p) ^ S.params.numQueries)]

/-- The bound on the round error: the largest of its terms. -/
def roundErrorBound (p : ℕ) (A : Analysis) : ℚ := maxTerms (S.roundErrorTerms p A)

/-- The calculator certifies `bits` bits per oracle answer. -/
def SecureRo (p : ℕ) (A : Analysis) (bits : ℕ) : Prop :=
  S.Fits A ∧ S.roundErrorBound p A ≤ 1 / 2 ^ bits

instance (p : ℕ) (A : Analysis) (bits : ℕ) : Decidable (S.SecureRo p A bits) := by
  unfold SecureRo; infer_instance

end Setup

namespace Batch.Setup
variable {withLookups : Bool} (S : Batch.Setup EF withLookups)

/-- The number of opened words of the instances whose domains have `2 ^ m` points, as a list
sum (`groupNumOpened`). -/
def groupNumOpenedL (m : ℕ) : ℕ :=
  ((List.finRange S.k).map fun j ↦
    if S.logN j + S.params.logBlowup = m then (S.instanceSetup j).numOpened else 0).sum

/-- The largest of an instance term. -/
def maxInstances (f : Fin S.k → ℚ) : ℚ := maxQ ((List.finRange S.k).map f)

/-- LogUp's error times `|𝕂|`: `T + (T - 1) W`. -/
def lookupNum : ℚ := ((S.numInteractions + (S.numInteractions - 1) * S.lookupWidth : ℕ) : ℚ)

/-- Instance `i`'s batching, times `|𝕂|`: the opened words of its domain size. -/
def batchingNum (A : Analysis) (i : Fin S.k) : ℚ :=
  (S.instanceSetup i).batchingNum A (S.groupNumOpenedL (S.logN i + S.params.logBlowup))

/-- The analysis fits `S`: FRI folds by arity `2`, the analysis is valid at the rate,
`δ ≤ δ' - 2/N` on every domain, and FRI injects at heights of at least `2 ^ t` points. -/
def Fits (A : Analysis) : Prop :=
  S.params.maxLogArity = 1 ∧ A.Valid S.domainSetup.rateQ ∧
    (∀ i ∈ List.finRange S.k, A.δ ≤ A.δ' - 2 / (S.instanceSetup i).size) ∧
    ∀ m ∈ S.friHeights, A.t ≤ m

instance (A : Analysis) : Decidable (S.Fits A) := by unfold Fits; infer_instance

/-- The worst instance's constraint folding, times `|𝕂|`. -/
def foldingNum : ℚ := S.maxInstances fun i ↦ ((S.instanceSetup i).numConstraints - 1 : ℕ)

/-- The worst instance's out-of-domain term, times `|𝕂|`. -/
def outOfDomainNum : ℚ :=
  S.maxInstances fun i ↦ ((S.instanceSetup i).identityDegree + (S.instanceSetup i).n : ℕ)

/-- The terms of the batch's knowledge error bound for `|F| = p`, the instance terms at their
worst instance. -/
def knowledgeErrorTerms (p : ℕ) (A : Analysis) : List (String × ℚ) :=
  [("lookup challenges", S.lookupNum / (p : ℚ) ^ Challenge.d EF),
    ("constraint folding", S.foldingNum / (p : ℚ) ^ Challenge.d EF),
    ("out of domain", S.outOfDomainNum / (p : ℚ) ^ Challenge.d EF),
    ("batching", S.maxInstances (S.batchingNum A) / (p : ℚ) ^ Challenge.d EF),
    ("FRI folds", S.domainSetup.friFoldsNum A S.friHeights.length / (p : ℚ) ^ Challenge.d EF),
    ("FRI queries", S.domainSetup.queryDensity A ^ S.params.numQueries)]

/-- The bound on the batch's knowledge error: the sum of its terms. -/
def knowledgeErrorBound (p : ℕ) (A : Analysis) : ℚ := sumTerms (S.knowledgeErrorTerms p A)

/-- The calculator certifies `bits` bits of knowledge soundness for the batch. -/
def Secure (p : ℕ) (A : Analysis) (bits : ℕ) : Prop :=
  S.Fits A ∧ S.knowledgeErrorBound p A ≤ 1 / 2 ^ bits

instance (p : ℕ) (A : Analysis) (bits : ℕ) : Decidable (S.Secure p A bits) := by
  unfold Secure; infer_instance

/-- The terms of the batch's round error bound for `|F| = p`, by round, the instance terms at
their worst instance, each but `α` credited with its grinding. -/
def roundErrorTerms (p : ℕ) (A : Analysis) : List (String × ℚ) :=
  [("lookup challenges", powFractionQ p S.params.lookupPowBits *
      (S.lookupNum / (p : ℚ) ^ Challenge.d EF)),
    ("constraint folding", S.foldingNum / (p : ℚ) ^ Challenge.d EF),
    ("out of domain", powFractionQ p S.params.oodPowBits *
      (S.outOfDomainNum / (p : ℚ) ^ Challenge.d EF)),
    ("batching", powFractionQ p S.params.batchPowBits *
      (S.maxInstances (S.batchingNum A) / (p : ℚ) ^ Challenge.d EF)),
    ("FRI folds", powFractionQ p S.params.commitPowBits *
      (max (2 * A.lossyBound S.domainSetup.rateQ) (2 ^ A.t) / (p : ℚ) ^ Challenge.d EF)),
    ("FRI queries", powFractionQ p S.params.queryPowBits *
      (S.domainSetup.queryDensity A + 1 / p) ^ S.params.numQueries)]

/-- The bound on the batch's round error: the largest of its terms. -/
def roundErrorBound (p : ℕ) (A : Analysis) : ℚ := maxTerms (S.roundErrorTerms p A)

/-- The calculator certifies `bits` bits per oracle answer for the batch. -/
def SecureRo (p : ℕ) (A : Analysis) (bits : ℕ) : Prop :=
  S.Fits A ∧ S.roundErrorBound p A ≤ 1 / 2 ^ bits

instance (p : ℕ) (A : Analysis) (bits : ℕ) : Decidable (S.SecureRo p A bits) := by
  unfold SecureRo; infer_instance

end Batch.Setup

/-! ### Reports -/

/-- `log₂ n` as a float, from the leading `61` bits of `n`. -/
def log2Float (n : ℕ) : Float :=
  let s := n.log2 - 60
  Float.log2 (n >>> s).toFloat + s.toFloat

/-- The bits of security of an error `x`: `-log₂ x`, infinite for `x ≤ 0`. -/
def securityBits (x : ℚ) : Float :=
  if x ≤ 0 then 1 / 0 else log2Float x.den - log2Float x.num.natAbs

/-- A calculator's report: whether the analysis fits the setup, and the bits of security of each
term and of the bound. -/
structure Report where
  fits : Bool
  terms : List (String × Float)
  total : Float

instance : Repr Report where
  reprPrec r _ := .joinSep (((s!"fits: {r.fits}" :: r.terms.map fun (n, b) ↦ s!"{n}: {b}") ++
    [s!"total: {r.total}"]).map Std.Format.text) .line

/-- A report from the analysis' fit, the terms and the bound. -/
def Report.of (fits : Bool) (terms : List (String × ℚ)) (bound : ℚ) : Report :=
  ⟨fits, terms.map fun (n, x) ↦ (n, securityBits x), securityBits bound⟩

/-- The knowledge error's report for `|F| = p`. -/
def Setup.knowledgeErrorReport {lookups : List (Lookup F)} (S : Setup EF lookups) (p : ℕ)
    (A : Analysis) : Report :=
  .of (decide (S.Fits A)) (S.knowledgeErrorTerms p A) (S.knowledgeErrorBound p A)

/-- The round error's report for `|F| = p`. -/
def Setup.roundErrorReport (S : Setup EF) (p : ℕ) (A : Analysis) : Report :=
  .of (decide (S.Fits A)) (S.roundErrorTerms p A) (S.roundErrorBound p A)

/-- The batch's knowledge error report for `|F| = p`. -/
def Batch.Setup.knowledgeErrorReport {withLookups : Bool} (S : Batch.Setup EF withLookups)
    (p : ℕ) (A : Analysis) : Report :=
  .of (decide (S.Fits A)) (S.knowledgeErrorTerms p A) (S.knowledgeErrorBound p A)

/-- The batch's round error report for `|F| = p`. -/
def Batch.Setup.roundErrorReport {withLookups : Bool} (S : Batch.Setup EF withLookups) (p : ℕ)
    (A : Analysis) : Report :=
  .of (decide (S.Fits A)) (S.roundErrorTerms p A) (S.roundErrorBound p A)

end CompStark.Iop
