/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.BatchAssembly
public import CompStark.Sound.BalancedInt

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

The base field being the prime field `ℤ/p`, balance in the field is balance over the integers when
the multiplicities are small (`Sound.Batch.balanced_int`): if the batch passes the verifier's
multiplicity bound `∑ᵢ wᵢ 2 ^ logNᵢ < p` (`Setup.HeightBounded`) and the AIRs keep every row's
multiplicities within their count weights (`Setup.CountsBounded`, an obligation of the AIRs the
verifier does not check), the satisfying traces satisfy the batch over the integers
(`Setup.SatisfiedInt`): every bus balances as a multiset, its multiplicities read as the integers
of magnitude below `p / 2` they stand for. So the knowledge error also bounds acceptance while no
tuple of close traces satisfies the batch over the integers (`batchKnowledgeSoundness_int`).
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

/-- **Knowledge soundness of the batch STARK, over the integers.** For a batch within the
verifier's multiplicity bound, whose AIRs keep every row's multiplicities within their count
weights: if no tuple of traces, each close to its instance's committed trace, satisfies every AIR
with every bus balanced as a multiset, the verifier accepts with probability at most the knowledge
error. -/
theorem batchKnowledgeSoundness_int {withLookups : Bool} (S : Batch.Setup EF withLookups)
    (publicValues : Fin S.k → List F) (prover : Batch.Prover S) (δ δ' : NNReal)
    (hδ' : (δ' : ℝ) < 1 - S.rate) (hbound : S.HeightBounded)
    (hcounts : ∀ traces, (∀ i, (S.air i).Satisfied (S.logN i) (traces i) (publicValues i)) →
      S.CountsBounded traces publicValues) :
    (∀ traces ∈ Batch.closeTraces S δ' prover.trace, ¬ S.SatisfiedInt traces publicValues) →
      Batch.acceptance publicValues prover ≤ Batch.knowledgeError S δ δ' :=
  fun h ↦ batchKnowledgeSoundness S publicValues prover δ δ' hδ' fun traces ht hsat ↦
    h traces ht (Batch.satisfiedInt_of_satisfied S traces publicValues hbound
      (hcounts traces hsat.air) hsat)

end CompStark.Iop
