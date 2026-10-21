/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Iop

/-! # The batch STARK as an interactive oracle proof

The protocol behind `verifyBatchWith`, with oracles in place of the Merkle commitments and uniform
challenges in place of Fiat–Shamir, for a `Batch.Setup`: FRI parameters and `k ≥ 1` AIR instances
whose traces have `2 ^ logN` rows each. Instances of mixed heights, whose inputs FRI rolls in
mid-folding, are not covered yet. Each instance is a STARK of its own (`Setup.instanceSetup`,
`CompStark/Iop.lean`) on the shared domain `L` of `2 ^ (logN + logBlowup)` points; the rounds are
the STARK's, every instance in each:

1. The prover sends every instance's extended trace (`Prover.trace`).
2. The verifier samples one constraint-folding challenge `α`.
3. The prover sends every instance's quotient chunks (`Prover.quotient`).
4. The verifier samples one out-of-domain point `ζ`.
5. The prover sends every instance's claimed values (`Prover.openings`). The verifier checks
   every instance's constraints at `ζ` (`ConstraintsHoldAt`).
6. The verifier samples the batching challenge `a`.
7. The prover shows with FRI that the batched DEEP word over all opened words, in Plonky3's order
   (`openedWords`: the main traces, the quotients, the preprocessed traces), is close to a
   polynomial of degree below `2 ^ logN` (`deepWord`).

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
each with a trace of `2 ^ logN` rows in a valid configuration (`ValidConfig`), with at least one
FRI fold. -/
structure Setup (EF : Type) [Challenge F EF] where
  params : Fri.Params
  logN : Nat
  /-- The number of instances. -/
  k : Nat
  air : Fin k → Air F
  valid : ∀ i, ValidConfig params (air i) logN
  /-- FRI's final polynomial is shorter than the traces, so FRI folds at least once. -/
  folds : params.logFinalPolyLen < logN
  /-- The batch has an instance. -/
  nonempty : 0 < k

namespace Setup
variable (S : Setup EF)

/-- Instance `i` as a STARK of its own. -/
abbrev instanceSetup (i : Fin S.k) : Iop.Setup EF :=
  ⟨S.params, S.air i, S.logN, S.valid i, S.folds⟩

/-- The first instance's setup, for what all instances share: the domain `L`, its code and FRI. -/
abbrev domainSetup : Iop.Setup EF := S.instanceSetup ⟨0, S.nonempty⟩

/-- The points of `L`, every instance's. -/
abbrev Point : Type := Fin (2 ^ (S.logN + S.params.logBlowup))

end Setup

/-! ### The prover -/

/-- A prover: every instance's oracles and messages, each a function of the challenges before
it. -/
structure Prover (S : Setup EF) where
  /-- Every instance's extended trace: each column's values on `L`. -/
  trace : (i : Fin S.k) → Fin (S.air i).width → S.Point → F
  /-- Every instance's quotient chunks, after `α`. -/
  quotient : (α : 𝕂) → (i : Fin S.k) → Fin (S.instanceSetup i).chunks → Fin (Challenge.d EF) →
    S.Point → F
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

/-- The opened words with their points and claimed values, in Plonky3's batching order: the
commitment scheme's rounds, every instance in each: the main traces, the quotients, the
preprocessed traces. -/
noncomputable def openedWords {S : Setup EF} (p : Prover S) (α ζ : 𝕂) :
    List ((S.Point → F) × 𝕂 × 𝕂) :=
  (List.finRange S.k).flatMap (fun i ↦
    mainOpened (S := S.instanceSetup i) (p.instanceProver i) α ζ) ++
  (List.finRange S.k).flatMap (fun i ↦
    quotientOpened (S := S.instanceSetup i) (p.instanceProver i) α ζ) ++
  (List.finRange S.k).flatMap (fun i ↦
    preprocessedOpened (S := S.instanceSetup i) (p.instanceProver i) α ζ)

/-- The batched DEEP word: `∑ᵢ aⁱ (yᵢ - fᵢ(x)) / (zᵢ - x)` at each point `x` of `L`. -/
noncomputable def deepWord {S : Setup EF} (p : Prover S) (α ζ a : 𝕂) (i : S.Point) : 𝕂 :=
  ((openedWords p α ζ).zipIdx.map fun ((f, z, y), k) ↦
    a ^ k * (y - algebraMap F 𝕂 (f i)) / (z - S.domainSetup.domain i)).sum

open Classical in
/-- The probability that the verifier accepts `prover`: over uniform `α`, `ζ` and `a`, every
instance's constraints hold at `ζ` and FRI accepts the batched DEEP word. -/
noncomputable def acceptance {S : Setup EF} (publicValues : Fin S.k → List F) (prover : Prover S) :
    ENNReal :=
  (Fintype.card 𝕂 : ENNReal)⁻¹ ^ 3 * ∑ α : 𝕂, ∑ ζ : 𝕂, ∑ a : 𝕂,
    if ∀ i, ConstraintsHoldAt (S.instanceSetup i) (publicValues i) α ζ (prover.openings α ζ i)
    then friAcceptance S.domainSetup (deepWord prover α ζ a) else 0

/-! ### The extractor: list decoding -/

/-- The tuples of traces the extractor reads off the committed trace words at proximity `δ`: one
trace per instance, each of `Iop.closeTraces`. -/
def closeTraces (S : Setup EF) (δ : ℝ) (words : (i : Fin S.k) → Fin (S.air i).width → S.Point → F) :
    Set (Fin S.k → Array F) :=
  {traces | ∀ i, traces i ∈ Iop.closeTraces (S.instanceSetup i) δ (words i)}

end Batch

/-! ### A STARK is a batch of one instance -/

/-- A STARK as a batch of one instance. -/
abbrev Setup.toBatch (S : Iop.Setup EF) : Batch.Setup EF :=
  ⟨S.params, S.logN, 1, fun _ ↦ S.air, fun _ ↦ S.valid, S.folds, Nat.one_pos⟩

/-- A STARK prover as a prover of a batch of one instance. -/
abbrev Prover.toBatch {S : Iop.Setup EF} (p : Iop.Prover S) : Batch.Prover S.toBatch :=
  ⟨fun _ ↦ p.trace, fun α _ ↦ p.quotient α, fun α ζ _ ↦ p.openings α ζ⟩

end CompStark.Iop
