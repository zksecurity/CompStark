/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BatchAssembly

/-! # Knowledge soundness of the batch STARK in the random-oracle model

The non-interactive batch STARK (`verifyBatchWith`), with the verifier's hashes as random oracles
(`CompStark/BatchRandomOracle.lean`), is knowledge sound, LogUp lookups included: a prover making
at most `Q` oracle calls gets a proof accepted while no tuple of traces close to the ones it
committed to satisfies the batch (every AIR, and every bus balanced) with probability at most
`q · roundError + hashError F h q`, `q = Q + verifierQueries`. `roundError` is the largest error of
one oracle answer, the lookup challenges' LogUp error and every round of the batch IOP at its
worst instance, each credited with its grinding, FRI's folds with the shorter instances' words
injected (`CompStark/BatchNonInteractiveError.lean`), and `hashError` bounds collisions and
predictions of digests, `h` the Merkle cap height.

The batch's common data, the commitment to the instances' preprocessed traces, is part of the
statement: the game computes it on the oracles before the prover runs (`Setup.setupRo`), and
`verifierQueries` counts the setup's calls with the verifier's.

The committed traces are read off the prover's own hash queries (`committedTraces`), so the
extractor is straight-line; the permutation traces it needs on the way are read off the queries
under the permutation commitment, auxiliary to the output. The proof (`CompStark/Ni/Batch*.lean`)
mirrors the STARK's: it bounds, query by query, the probability that a fresh answer clashes with a
known digest or makes its round bad (`Ni/BatchRoundBounds.lean`), and shows that an accepted proof
the extractor cannot open forces such a query (`Ni/BatchBadQuery.lean`): the verifier's checks hold
for the extracted transcript (`Ni/BatchBcs.lean`), whose commitments bind the trees of mixed heights
the prover committed to, and safe rounds then give satisfying traces (`Sound/BatchRbr.lean`).
`Ni/BatchAssembly.lean` sums the bounds.

With lookup inclusion (`batchKnowledgeSoundness_ro_inclusion`), as for the interactive batch
(`CompStark/BatchSoundness.lean`): an accepting verifier checked the multiplicity bound
`∑ᵢ wᵢ 2 ^ logNᵢ < p`, so for AIRs that keep their queries' multiplicities within their weights
(`Air.CountsBounded`), traces satisfying the batch have every bus's queries included in what is
provided (`Sound.Batch.included_of_balanced`), and the same bound holds for the event that no
tuple of close traces satisfies the batch with lookup inclusion (`Setup.SatisfiedWithInclusion`).
-/

@[expose] public section
namespace CompStark.Iop.Batch
open CompStark.Stark CompStark.Ni

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- **Knowledge soundness of the batch STARK in the random-oracle model.** A prover making at
most `Q` oracle calls gets a proof for the instances' trace lengths accepted, while no tuple of
traces close to the ones it committed to satisfies the batch, with probability at most
`q · roundError + hashError F h q`, `q = Q + verifierQueries`: FRI tests proximity `δ`, and the
extractor list-decodes at any `δ'` below `1 - rate`. The Merkle cap fits below the commit-phase
tree FRI's first fold makes of every instance (`Setup.CapFits`). -/
theorem batchKnowledgeSoundness_ro (S : Setup EF) [S.CapFits] (publicValues : Fin S.k → List F)
    (δ δ' : NNReal) (hδ' : (δ' : ℝ) < 1 - S.rate) (Q : Nat) (prover : NIProver S)
    (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← run S publicValues prover}[
      verdict = .ok () ∧ proof.degreeBits.toList = List.ofFn S.logN ∧
        ∀ traces ∈ closeTraces S δ' (committedTraces S log proof),
          ¬ S.Satisfied traces publicValues] ≤
      (Q + S.verifierQueries) * roundError S δ δ' +
        hashError F S.params.capHeight (Q + S.verifierQueries) :=
  prob_unopenedB_le S publicValues δ δ' hδ' Q prover hQ

/-- **Knowledge soundness of the batch STARK in the random-oracle model, with lookup
inclusion.** For AIRs that keep their queries' multiplicities within their weights: a prover
making at most `Q` oracle calls gets a proof for the instances' trace lengths accepted, while no
tuple of traces close to the ones it committed to satisfies every AIR with every bus's queries
included in what is provided, with probability at most `q · roundError + hashError F h q`,
`q = Q + verifierQueries`. -/
theorem batchKnowledgeSoundness_ro_inclusion (S : Setup EF) [S.CapFits] (publicValues : Fin S.k → List F)
    (δ δ' : NNReal) (hδ' : (δ' : ℝ) < 1 - S.rate) (Q : Nat) (prover : NIProver S)
    (hQ : prover.IsTotalQueryBound Q) (hcounts : ∀ i, (S.air i).CountsBounded (S.logN i)) :
    Pr{let (proof, log, verdict) ← run S publicValues prover}[
      verdict = .ok () ∧ proof.degreeBits.toList = List.ofFn S.logN ∧
        ∀ traces ∈ closeTraces S δ' (committedTraces S log proof),
          ¬ S.SatisfiedWithInclusion traces publicValues] ≤
      (Q + S.verifierQueries) * roundError S δ δ' +
        hashError F S.params.capHeight (Q + S.verifierQueries) :=
  prob_unopenedInclusionB_le S publicValues δ δ' hδ' Q prover hQ hcounts

end CompStark.Iop.Batch
