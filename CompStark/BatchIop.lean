/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Iop
public import Mathlib.Data.Finset.Sort

/-! # The batch STARK as an interactive oracle proof

The protocol behind `verifyBatchWith`, with oracles in place of the Merkle commitments and uniform
challenges in place of Fiat–Shamir, for a `Batch.Setup`: FRI parameters and `k ≥ 1` AIR instances,
instance `i` with a trace of `2 ^ logN i` rows. Each instance is a STARK of its own
(`Setup.instanceSetup`, `CompStark/Iop.lean`), on its own domain `Lᵢ` of
`2 ^ (logN i + logBlowup)` points; the rounds are the STARK's, every instance in each:

1. The prover sends every instance's extended trace (`Prover.trace`).
2. The verifier samples one constraint-folding challenge `α`.
3. The prover sends every instance's quotient chunks (`Prover.quotient`).
4. The verifier samples one out-of-domain point `ζ`.
5. The prover sends every instance's claimed values (`Prover.openings`). The verifier checks
   every instance's constraints at `ζ` (`ConstraintsHoldAt`).
6. The verifier samples the batching challenge `a`.
7. As Plonky3's commitment scheme reduces the openings by height, the verifier batches, for each
   domain size, the DEEP quotients of the opened words of the instances of that size, in Plonky3's
   order (`groupOpened`: the main traces, the quotients, the preprocessed traces), by the powers
   of `a` starting over at each size (`groupDeepWord`). The prover shows with FRI that these words
   are close to polynomials of degree below their traces' lengths: FRI runs on the tallest word
   and injects each shorter one when its folds reach that size (`friAcceptanceWith`).

`acceptance` is the probability that the verifier accepts. The extractor list-decodes every
instance's committed trace: `closeTraces` are the tuples of traces, one per instance, each close
to that instance's committed trace (`Iop.closeTraces`).
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

namespace Batch

/-- A batch STARK to prove with over the challenge field `EF`: FRI parameters and `k ≥ 1` AIRs,
instance `i` with a trace of `2 ^ logN i` rows in a valid configuration (`ValidConfig`), with at
least one FRI fold. -/
structure Setup (EF : Type) [Challenge F EF] where
  params : Fri.Params
  /-- The number of instances. -/
  k : Nat
  air : Fin k → Air F
  logN : Fin k → Nat
  valid : ∀ i, ValidConfig params (air i) (logN i)
  /-- FRI's final polynomial is shorter than every trace, so FRI folds at least once. -/
  folds : ∀ i, params.logFinalPolyLen < logN i
  /-- The batch has an instance. -/
  nonempty : 0 < k

namespace Setup
variable (S : Setup EF)

/-- Instance `i` as a STARK of its own. -/
abbrev instanceSetup (i : Fin S.k) : Iop.Setup EF :=
  ⟨S.params, S.air i, S.logN i, S.valid i, S.folds i⟩

/-- An instance of the largest trace length. -/
noncomputable def top : Fin S.k :=
  Classical.choose (Finset.exists_max_image Finset.univ S.logN ⟨⟨0, S.nonempty⟩, Finset.mem_univ _⟩)

theorem logN_le_top (i : Fin S.k) : S.logN i ≤ S.logN S.top :=
  (Classical.choose_spec (Finset.exists_max_image Finset.univ S.logN
    ⟨⟨0, S.nonempty⟩, Finset.mem_univ _⟩)).2 i (Finset.mem_univ _)

/-- The tallest instance's setup, for FRI, which runs on its domain. -/
noncomputable abbrev domainSetup : Iop.Setup EF := S.instanceSetup S.top

/-- The log sizes of the domains below the tallest, tallest first: where FRI injects the
batched DEEP words of the shorter instances. -/
noncomputable def friHeights : List ℕ :=
  ((Finset.univ.image fun i ↦ S.logN i + S.params.logBlowup).erase
    (S.logN S.top + S.params.logBlowup)).sort (· ≥ ·)

end Setup

/-! ### The prover -/

/-- A prover: every instance's oracles and messages, each a function of the challenges before
it. -/
structure Prover (S : Setup EF) where
  /-- Every instance's extended trace: each column's values on its domain. -/
  trace : (i : Fin S.k) → Fin (S.air i).width → (S.instanceSetup i).Point → F
  /-- Every instance's quotient chunks, after `α`. -/
  quotient : (α : 𝕂) → (i : Fin S.k) → Fin (S.instanceSetup i).chunks → Fin (Challenge.d EF) →
    (S.instanceSetup i).Point → F
  /-- Every instance's claimed values, after `α` and `ζ`. -/
  openings : (α ζ : 𝕂) → (i : Fin S.k) → Openings (S.instanceSetup i)

/-- Instance `i`'s part of the prover. -/
def Prover.instanceProver {S : Setup EF} (p : Prover S) (i : Fin S.k) :
    Iop.Prover (S.instanceSetup i) :=
  ⟨p.trace i, fun α ↦ p.quotient α i, fun α ζ ↦ p.openings α ζ i⟩

/-! ### The verifier -/

/-- A STARK's opened trace words: the columns at `ζ`, then, if opened, at `ζ ω_n`. -/
noncomputable def mainOpened {S : Iop.Setup EF} (p : Iop.Prover S) (α ζ : 𝕂) :
    List ((S.Point → F) × 𝕂 × 𝕂) :=
  let o := p.openings α ζ
  (List.finRange S.air.width).map (fun j ↦ (p.trace j, ζ, o.traceAt j)) ++
  (List.finRange S.air.mainNextWidth).map (fun j ↦
    (p.trace (Fin.castLE S.air.mainNextWidth_le j), ζ * rootOfUnity S.logN, o.traceNext j))

/-- A STARK's opened quotient words: each chunk's coordinates at `ζ`. -/
noncomputable def quotientOpened {S : Iop.Setup EF} (p : Iop.Prover S) (α ζ : 𝕂) :
    List ((S.Point → F) × 𝕂 × 𝕂) :=
  (List.finRange S.chunks).flatMap fun c ↦ (List.finRange (Challenge.d EF)).map fun e ↦
    (p.quotient α c e, ζ, (p.openings α ζ).quotientAt c e)

/-- A STARK's opened preprocessed words: the columns at `ζ`, then, if opened, at `ζ ω_n`. -/
noncomputable def preprocessedOpened {S : Iop.Setup EF} (p : Iop.Prover S) (α ζ : 𝕂) :
    List ((S.Point → F) × 𝕂 × 𝕂) :=
  let o := p.openings α ζ
  (List.finRange S.air.preprocessedWidth).map
    (fun j ↦ (S.preprocessedWord j.val, ζ, o.preprocessedAt j)) ++
  (List.finRange S.air.preprocessedNextWidth).map
    (fun j ↦ (S.preprocessedWord j.val, ζ * rootOfUnity S.logN, o.preprocessedNext j))

/-- Instance `i`'s opened words, read as words on a domain of `2 ^ m` points if its domain has
that size, and none otherwise. -/
def onSize {S : Setup EF} (i : Fin S.k) (m : ℕ)
    (words : List (((S.instanceSetup i).Point → F) × 𝕂 × 𝕂)) :
    List ((Fin (2 ^ m) → F) × 𝕂 × 𝕂) :=
  if h : S.logN i + S.params.logBlowup = m then
    words.map fun w ↦ (fun x ↦ w.1 (Fin.cast (by rw [h]) x), w.2)
  else []

/-- The opened words of the instances whose domains have `2 ^ m` points, with their points and
claimed values, in Plonky3's batching order: the commitment scheme's rounds, every instance of
that size in each: the main traces, the quotients, the preprocessed traces. -/
noncomputable def groupOpened {S : Setup EF} (p : Prover S) (α ζ : 𝕂) (m : ℕ) :
    List ((Fin (2 ^ m) → F) × 𝕂 × 𝕂) :=
  (List.finRange S.k).flatMap (fun i ↦ onSize i m (mainOpened (p.instanceProver i) α ζ)) ++
  (List.finRange S.k).flatMap (fun i ↦ onSize i m (quotientOpened (p.instanceProver i) α ζ)) ++
  (List.finRange S.k).flatMap (fun i ↦ onSize i m (preprocessedOpened (p.instanceProver i) α ζ))

/-- The batched DEEP word of the domain of `2 ^ m` points `g ⟨ω_m⟩`:
`∑ᵢ aⁱ (yᵢ - fᵢ(x)) / (zᵢ - x)` over its opened words, at each point `x`. -/
noncomputable def groupDeepWord {S : Setup EF} (p : Prover S) (α ζ a : 𝕂) (m : ℕ)
    (x : Fin (2 ^ m)) : 𝕂 :=
  ((groupOpened p α ζ m).zipIdx.map fun ((f, z, y), k) ↦
    a ^ k * (y - algebraMap F 𝕂 (f x)) / (z - lift (basePoint m x))).sum

open Classical in
/-- The probability that the verifier accepts `prover`: over uniform `α`, `ζ` and `a`, every
instance's constraints hold at `ζ` and FRI accepts the batched DEEP words, the tallest as FRI's
word and the shorter ones injected. -/
noncomputable def acceptance {S : Setup EF} (publicValues : Fin S.k → List F) (prover : Prover S) :
    ENNReal :=
  (Fintype.card 𝕂 : ENNReal)⁻¹ ^ 3 * ∑ α : 𝕂, ∑ ζ : 𝕂, ∑ a : 𝕂,
    if ∀ i, ConstraintsHoldAt (S.instanceSetup i) (publicValues i) α ζ (prover.openings α ζ i)
    then friAcceptanceWith S.domainSetup (groupDeepWord prover α ζ a) S.friHeights
      (groupDeepWord prover α ζ a _) else 0

/-! ### The extractor: list decoding -/

/-- The tuples of traces the extractor reads off the committed trace words at proximity `δ`: one
trace per instance, each of `Iop.closeTraces`. -/
def closeTraces (S : Setup EF) (δ : ℝ)
    (words : (i : Fin S.k) → Fin (S.air i).width → (S.instanceSetup i).Point → F) :
    Set (Fin S.k → Array F) :=
  {traces | ∀ i, traces i ∈ Iop.closeTraces (S.instanceSetup i) δ (words i)}

end Batch

/-! ### A STARK is a batch of one instance -/

/-- A STARK as a batch of one instance. -/
abbrev Setup.toBatch (S : Iop.Setup EF) : Batch.Setup EF :=
  ⟨S.params, 1, fun _ ↦ S.air, fun _ ↦ S.logN, fun _ ↦ S.valid, fun _ ↦ S.folds, Nat.one_pos⟩

/-- A STARK prover as a prover of a batch of one instance. -/
abbrev Prover.toBatch {S : Iop.Setup EF} (p : Iop.Prover S) : Batch.Prover S.toBatch :=
  ⟨fun _ ↦ p.trace, fun α _ ↦ p.quotient α, fun α ζ _ ↦ p.openings α ζ⟩

end CompStark.Iop
