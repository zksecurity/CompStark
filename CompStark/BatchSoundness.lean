/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Interaction.BatchKnowledge
public import CompStark.Sound.Inclusion

/-! # Knowledge soundness of the batch STARK

The batch STARK, as an interactive oracle protocol on ArkLib's interaction layer
(`CompStark/Interaction/Batch.lean`), is knowledge sound: against any prover, the probability
that the verifier accepts while no tuple of traces of the lengths the prover claims, each close to
the trace its instance's prover commits to, satisfies a relation `R` (`Statement.farAcceptance`)
is at most the statement's knowledge error, the largest over the admitted vectors
(`Statement.knowledgeError`, `CompStark/BatchSoundnessError.lean`), for `R` the batch's relation:
every AIR and every bus balanced in the field (`Setup.Satisfied`).

The proof is a round-by-round knowledge certificate
(`CompStark/Interaction/BatchKnowledge.lean`), the doomed-transcript argument of
`CompStark/Sound/BatchRbr.lean` appended to ArkLib's FRI certificate. It first spends the lookup
challenges: unless they are bad for some tuple of close traces satisfying every AIR but unbalanced
(`Sound/BatchLogUp.lean`, `Sound/LogUp.lean`), the terminals of close permutation traces
satisfying their LogUp constraints sum to the messages' nonzero sum of fractions
(`Sound/Telescope.lean`), so the verifier rejects, or some instance has no close trace and close
permutation trace satisfying all its constraints. The STARK's rounds then run on that instance,
among the instances of its domain's size: batching by powers keeps DEEP quotients that are not
near on a common set far; the DEEP quotients of that size near on a common set make the
instance's near too, which forces its claimed values to be those of a candidate trace,
permutation trace and quotient; and its constraint check at `ζ` is a polynomial identity that a
failing candidate satisfies at few points. FRI rejects when the batched word of that size is far
from low degree, be it FRI's word or injected mid-folding.

A lookup's tuples are queries, of positive weight, or provided table entries, of weight `0` and
any multiplicity. The base field being the prime field `ℤ/p`, balance in the field makes the
queries included in what is provided when they are few (`Sound.Batch.included_of_balanced`): the
claimed lengths pass the verifier's multiplicity bound `∑ᵢ wᵢ 2 ^ logNᵢ < p`
(`Setup.HeightBounded`), which the verifier checks on every length vector it admits
(`Statement.Admits`), so if every AIR keeps its queries' multiplicities within their weights
(`Air.CountsBounded`, an obligation of the AIRs the verifier does not check), then for every bus
and tuple of values, some row of some instance provides it, or its queries' multiplicities, read
as the integers of magnitude below `p / 2` they stand for, sum to zero (`Setup.Included`). So the
knowledge error also bounds acceptance while no tuple of close traces satisfies the batch with
lookup inclusion (`batchKnowledgeSoundness_inclusion`).
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound _root_.Interaction _root_.Interaction.Oracle OracleComp
open OracleSpec

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

namespace Batch.Statement
variable (C : Batch.Statement F) (EF : Type) [Challenge F EF] (publicValues : Fin C.k → List F)

/-- The probability that the verifier accepts `prover` while no tuple of traces close to the
traces it commits to, at proximity `δ' n` for the lengths `2 ^ n i` it claims, satisfies `R` at
those lengths. -/
noncomputable def farAcceptance (δ' : (Fin C.k → ℕ) → NNReal)
    (R : C.Length → (Fin C.k → Array F) → Prop) {OutP : (C.protocol EF).tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec (C.protocol EF).tree
      (C.protocol EF).roles OutP) : ENNReal :=
  Pr{let result ← (executeStrategies unifSpec (C.protocol EF).tree (C.protocol EF).roles
    (C.protocol EF).oracles noAccess noImpl prover (C.verifier EF publicValues))}[
      result.2.2 = true ∧
        ∀ traces ∈ Batch.closeTraces (C.setup EF result.1.1) (δ' result.1.1.1)
            ((C.setup EF result.1.1).traceWords result.1.2.1),
          ¬ R result.1.1 traces]

/-- A weaker relation is accepted while no close tuple satisfies it at most as often as a
stronger one. -/
theorem farAcceptance_mono (δ' : (Fin C.k → ℕ) → NNReal)
    {R R' : C.Length → (Fin C.k → Array F) → Prop} (h : ∀ n traces, R n traces → R' n traces)
    {OutP : (C.protocol EF).tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec (C.protocol EF).tree
      (C.protocol EF).roles OutP) :
    C.farAcceptance EF publicValues δ' R' prover ≤ C.farAcceptance EF publicValues δ' R prover :=
  prEvent_mono _ _ _ fun _ hr ↦ ⟨hr.1, fun traces ht hR ↦ hr.2 traces ht (h _ _ hR)⟩

end Batch.Statement

/-- **Knowledge soundness of the batch STARK.** Against any prover, the verifier accepts while no
tuple of traces of the lengths the prover claims, each close to its instance's committed trace,
satisfies the batch (every instance's AIR, and every bus balanced) with probability at most the
statement's knowledge error, the largest over the admitted vectors. FRI tests proximity `δ n`, and
the extractor list-decodes every instance at any `δ' n` below `1 - rate`. -/
theorem batchKnowledgeSoundness (C : Batch.Statement F) (publicValues : Fin C.k → List F)
    {OutP : (C.protocol EF).tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec (C.protocol EF).tree
      (C.protocol EF).roles OutP)
    (δ δ' : (Fin C.k → ℕ) → NNReal) (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate) :
    C.farAcceptance EF publicValues δ' (fun n traces ↦ (C.setup EF n).Satisfied traces publicValues)
      prover ≤ C.knowledgeError EF δ δ' :=
  Batch.Statement.extraction_le_knowledgeError C EF publicValues δ δ' hδ' prover

/-- **Knowledge soundness of the batch STARK, with lookup inclusion.** For a batch statement whose
AIRs keep their queries' multiplicities within their weights at every admitted vector of lengths:
against any prover, the verifier accepts while no tuple of traces of the lengths the prover claims,
each close to its instance's committed trace, satisfies every AIR with every bus's queries
included in what is provided, with probability at most the statement's knowledge error. -/
theorem batchKnowledgeSoundness_inclusion (C : Batch.Statement F)
    (publicValues : Fin C.k → List F) {OutP : (C.protocol EF).tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec (C.protocol EF).tree
      (C.protocol EF).roles OutP)
    (δ δ' : (Fin C.k → ℕ) → NNReal) (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate)
    (hcounts : ∀ n, C.Admits n → ∀ i, (C.air i).CountsBounded (n i)) :
    C.farAcceptance EF publicValues δ'
      (fun n traces ↦ (C.setup EF n).SatisfiedWithInclusion traces publicValues) prover ≤
      C.knowledgeError EF δ δ' :=
  (C.farAcceptance_mono EF publicValues δ' (fun n traces hsat ↦
    Batch.satisfiedWithInclusion_of_satisfied (C.setup EF n) traces publicValues
      (C.heightBounded_setupAt (EF := EF) n.1 n.2) (hcounts n.1 n.2) hsat) prover).trans
    (batchKnowledgeSoundness C publicValues prover δ δ' hδ')

end CompStark.Iop
