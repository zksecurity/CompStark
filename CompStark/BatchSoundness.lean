/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.BatchAssembly
public import CompStark.Sound.Inclusion

/-! # Knowledge soundness of the batch STARK

The batch STARK, as an interactive oracle proof (`CompStark/BatchIop.lean`), is knowledge sound:
if no tuple of traces, each close to the trace its instance's prover commits to, satisfies the
batch, every AIR and every bus balanced in the field (`Setup.Satisfied`), the verifier accepts
with probability at most the knowledge error (`CompStark/BatchSoundnessError.lean`).

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
the batch passes the verifier's multiplicity bound `∑ᵢ wᵢ 2 ^ logNᵢ < p` (`Setup.HeightBounded`)
and every AIR keeps its queries' multiplicities within their weights (`Air.CountsBounded`, an
obligation of the AIRs the verifier does not check), then for every bus and tuple of values,
some row of some instance provides it, or its queries' multiplicities, read as the integers of
magnitude below `p / 2` they stand for, sum to zero (`Setup.Included`). So the knowledge error
also bounds acceptance while no tuple of close traces satisfies the batch with lookup inclusion
(`batchKnowledgeSoundness_inclusion`).
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- **Knowledge soundness of the batch STARK.** If no tuple of traces, each close to its
instance's committed trace, satisfies the batch (every instance's AIR, and every bus balanced),
the verifier accepts the prover with probability at most the knowledge error: FRI tests proximity
`δ`, and the extractor list-decodes every instance at any `δ'` below `1 - rate`. -/
theorem batchKnowledgeSoundness {withLookups : Bool} (S : Batch.Setup EF withLookups)
    (publicValues : Fin S.k → List F) (prover : Batch.Prover S) (δ δ' : NNReal)
    (hδ' : (δ' : ℝ) < 1 - S.rate) :
    (∀ traces ∈ Batch.closeTraces S δ' prover.trace, ¬ S.Satisfied traces publicValues) →
      Batch.acceptance publicValues prover ≤ Batch.knowledgeError S δ δ' :=
  batchAcceptance_le S publicValues prover δ δ' hδ'

/-- **Knowledge soundness of the batch STARK, with lookup inclusion.** For a batch within the
verifier's multiplicity bound, whose AIRs keep their queries' multiplicities within their
weights: if no tuple of traces, each close to its instance's committed trace, satisfies every AIR
with every bus's queries included in what is provided, the verifier accepts with probability at
most the knowledge error. -/
theorem batchKnowledgeSoundness_inclusion {withLookups : Bool} (S : Batch.Setup EF withLookups)
    (publicValues : Fin S.k → List F) (prover : Batch.Prover S) (δ δ' : NNReal)
    (hδ' : (δ' : ℝ) < 1 - S.rate) (hbound : S.HeightBounded)
    (hcounts : ∀ i, (S.air i).CountsBounded (S.logN i)) :
    (∀ traces ∈ Batch.closeTraces S δ' prover.trace,
      ¬ S.SatisfiedWithInclusion traces publicValues) →
      Batch.acceptance publicValues prover ≤ Batch.knowledgeError S δ δ' :=
  fun h ↦ batchKnowledgeSoundness S publicValues prover δ δ' hδ' fun traces ht hsat ↦
    h traces ht (Batch.satisfiedWithInclusion_of_satisfied S traces publicValues hbound hcounts
      hsat)

end CompStark.Iop
