/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.BatchAssembly
public import CompStark.Sound.Inclusion

/-! # Knowledge soundness of the batch STARK

The batch STARK, as an interactive oracle proof (`CompStark/BatchIop.lean`), is knowledge sound:
for a prover that claims a vector of trace lengths the verifier admits and plays the batch there
(`Statement.Prover`), if no tuple of traces of those lengths, each close to the trace its
instance's prover commits to, satisfies the batch, every AIR and every bus balanced in the field
(`Setup.Satisfied`), the verifier accepts with probability at most the statement's knowledge
error, the largest over the admitted vectors (`Statement.knowledgeError`,
`CompStark/BatchSoundnessError.lean`).

The proof (`Sound/BatchAssembly.lean`) first spends the lookup challenges: unless they are bad
for some tuple of close traces satisfying every AIR but unbalanced (`Sound/BatchLogUp.lean`,
`Sound/LogUp.lean`), the terminals of close permutation traces satisfying their LogUp
constraints sum to the messages' nonzero sum of fractions (`Sound/Telescope.lean`), so the
verifier rejects, or some instance has no close trace and close permutation trace satisfying all
its constraints. It runs the single STARK's argument (`CompStark/Soundness.lean`) on that
instance, among the instances of its domain's size: FRI rejects when the batched word of that
size is far from low degree, be it FRI's word or injected mid-folding (`Sound/FriGame.lean`);
batching by powers keeps DEEP quotients that are not near on a common set far; the DEEP quotients
of that size near on a common set make the instance's near too, which forces its claimed values
to be those of a candidate trace, permutation trace and quotient; and its constraint check at `ζ`
is a polynomial identity that a failing candidate satisfies at few points.

A lookup's tuples are queries, of positive weight, or provided table entries, of weight `0` and
any multiplicity. The base field being the prime field `ℤ/p`, balance in the field makes the
queries included in what is provided when they are few (`Sound.Batch.included_of_balanced`): if
the claimed lengths pass the verifier's multiplicity bound `∑ᵢ wᵢ 2 ^ logNᵢ < p`
(`Setup.HeightBounded`) and every AIR keeps its queries' multiplicities within their weights
(`Air.CountsBounded`, an obligation of the AIRs the verifier does not check), then for every bus
and tuple of values,
some row of some instance provides it, or its queries' multiplicities, read as the integers of
magnitude below `p / 2` they stand for, sum to zero (`Setup.Included`). So the knowledge error
also bounds acceptance while no tuple of close traces satisfies the batch with lookup inclusion
(`batchKnowledgeSoundness_inclusion`).
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- **Knowledge soundness of the batch STARK.** For a prover that claims a vector of trace lengths
the verifier admits and plays the batch there: if no tuple of traces of those lengths, each close
to its instance's committed trace, satisfies the batch (every instance's AIR, and every bus
balanced), the verifier accepts the prover with probability at most the statement's knowledge
error, the largest over the admitted vectors. FRI tests proximity `δ n`, and the extractor
list-decodes every instance at any `δ' n` below `1 - rate`. -/
theorem batchKnowledgeSoundness (C : Batch.Statement F) (publicValues : Fin C.k → List F)
    (prover : C.Prover EF) (δ δ' : (Fin C.k → ℕ) → NNReal)
    (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate) :
    (∀ traces ∈ Batch.closeTraces prover.setup (δ' prover.logN) prover.prover.trace,
      ¬ prover.setup.Satisfied traces publicValues) →
      Batch.acceptance publicValues prover.prover ≤ C.knowledgeError EF δ δ' := fun h ↦
  (batchAcceptance_le prover.setup publicValues prover.prover _ _ (hδ' _ prover.admits) h).trans
    (le_iSup₂ (f := fun n hn ↦ Batch.knowledgeError (C.setupAt EF n hn) (δ n) (δ' n))
      prover.logN prover.admits)

/-- **Knowledge soundness of the batch STARK, with lookup inclusion.** For a batch statement whose
AIRs keep their queries' multiplicities within their weights at every admitted vector of lengths,
and a prover whose claimed lengths pass the verifier's multiplicity bound, which rejects the
others: if no tuple of traces of those lengths, each close to its instance's committed trace,
satisfies every AIR with every bus's queries included in what is provided, the verifier accepts
with probability at most the statement's knowledge error. -/
theorem batchKnowledgeSoundness_inclusion (C : Batch.Statement F)
    (publicValues : Fin C.k → List F) (prover : C.Prover EF) (δ δ' : (Fin C.k → ℕ) → NNReal)
    (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate)
    (hcounts : ∀ n, C.Admits n → ∀ i, (C.air i).CountsBounded (n i))
    (hbound : prover.setup.HeightBounded) :
    (∀ traces ∈ Batch.closeTraces prover.setup (δ' prover.logN) prover.prover.trace,
      ¬ prover.setup.SatisfiedWithInclusion traces publicValues) →
      Batch.acceptance publicValues prover.prover ≤ C.knowledgeError EF δ δ' :=
  fun h ↦ batchKnowledgeSoundness C publicValues prover δ δ' hδ' fun traces ht hsat ↦
    h traces ht (Batch.satisfiedWithInclusion_of_satisfied prover.setup traces publicValues hbound
      (hcounts _ prover.admits) hsat)

end CompStark.Iop
