/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BatchAssembly

/-! # Knowledge soundness of the batch STARK in the random-oracle model

The non-interactive batch STARK (`verifyBatchWith`, Plonky3's `verify_batch`), with the
verifier's hashes as random oracles (`CompStark/BatchRandomOracle.lean`), is knowledge sound for a
batch statement (`Statement`: FRI parameters, the AIRs and their keygen heights and lookups, no
trace lengths), LogUp lookups included: a prover making at most `Q` oracle calls gets a proof
accepted, of the trace lengths it claims, while no tuple of traces of those lengths close to the
ones it committed to satisfies the batch at those lengths (every AIR, and every bus balanced), with
probability at most `q · roundError + hashError F (h + 1) q`, `q = Q + verifierQueries`.
`roundError` is the largest error of one oracle answer over the vectors of trace lengths the
verifier admits (`Statement.Admits`, which every accepted proof's lengths are,
`Statement.admits_of_ok`): the lookup challenges' LogUp error and every round of the batch IOP at
its worst instance, each credited with its grinding, FRI's folds with the shorter instances' words
injected (`CompStark/BatchNonInteractiveError.lean`). `hashError` bounds collisions and
predictions of digests, `h` the Merkle cap height: a commitment round binds the `2 ^ h` digests at
the start of its input and the `2 ^ h` ending before its commit-phase grinding witness, whatever
the cap's height clamped to its tree.

The vectors of lengths share one term per query, not one each: the transcript observes every
instance's degree bits right after the batch's domain separator (`batchSeed`), the same at every
vector, so a fresh answer can only be bad at the vector its transcript has
(`Ni/BatchLengths.lean`). The degree bits are observed as extension elements whose first
coordinate is the length, and an admitted length is at most the two-adicity, below `p`, so this
holds on every base field.

The batch's common data, the commitment to the instances' preprocessed traces at their keygen
heights, is part of the statement: the game computes it on the oracles before the prover runs
(`Statement.setupRo`), and `verifierQueries` counts the setup's calls with the verifier's, the
verifier's on a proof of any lengths.

The committed traces are read off the prover's own hash queries (`committedTraces`), so the
extractor is straight-line; the permutation traces it needs on the way are read off the queries
under the permutation commitment, auxiliary to the output. The proof (`CompStark/Ni/Batch*.lean`)
mirrors the STARK's: it bounds, query by query, the probability that a fresh answer clashes with a
known digest or makes its round bad at some admitted vector of lengths (`Ni/BatchRoundBounds.lean`,
`Ni/BatchLengths.lean`), and shows that an accepted proof the extractor cannot open forces such a
query (`Ni/BatchBadQuery.lean`): the verifier's checks hold for the extracted transcript
(`Ni/BatchBcs.lean`), whose commitments bind the trees of mixed heights the prover committed to,
and safe rounds then give satisfying traces (`Sound/BatchRbr.lean`). `Ni/BatchAssembly.lean` sums
the bounds.

With lookup inclusion (`batchKnowledgeSoundness_ro_inclusion`), as for the interactive batch
(`CompStark/BatchSoundness.lean`): an accepting verifier checked the multiplicity bound
`∑ᵢ wᵢ 2 ^ logNᵢ < p`, so for AIRs that keep their queries' multiplicities within their weights
(`Air.CountsBounded`) at every admitted vector, traces satisfying the batch have every bus's
queries included in what is provided (`Sound.Batch.included_of_balanced`), and the same bound
holds for the event that no tuple of close traces satisfies the batch with lookup inclusion
(`Setup.SatisfiedWithInclusion`).
-/

@[expose] public section
namespace CompStark.Iop.Batch
open CompStark.Stark CompStark.Ni

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- **Knowledge soundness of the batch STARK in the random-oracle model.** A prover making at
most `Q` oracle calls gets a proof accepted while no tuple of traces of the proof's lengths close
to the ones it committed to satisfies the batch at those lengths, with probability at most
`q · roundError + hashError F (h + 1) q`, `q = Q + verifierQueries`: FRI tests proximity `δ n`,
and the extractor list-decodes at any `δ' n` below `1 - rate`, on traces of `2 ^ n i` rows. -/
theorem batchKnowledgeSoundness_ro (C : Statement F) (publicValues : Fin C.k → List F)
    (δ δ' : (Fin C.k → ℕ) → NNReal) (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate) (Q : Nat)
    (prover : C.NIProver EF) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← C.run publicValues prover}[
      verdict = .ok () ∧
        ∀ h : C.Admits (C.lengthsOf proof),
          ∀ traces ∈ closeTraces (C.setupAt EF _ h) (δ' (C.lengthsOf proof))
              (committedTraces (C.setupAt EF _ h) log proof),
            ¬ (C.setupAt EF _ h).Satisfied traces publicValues] ≤
      (Q + C.verifierQueries EF) * C.roundError EF δ δ' +
        hashError F (C.params.capHeight + 1) (Q + C.verifierQueries EF) :=
  prob_unopenedB_le C publicValues δ δ' hδ' Q prover hQ

/-- **Knowledge soundness of the batch STARK in the random-oracle model, with lookup
inclusion.** For AIRs that keep their queries' multiplicities within their weights at every
admitted vector of lengths: a prover making at most `Q` oracle calls gets a proof accepted, while
no tuple of traces of the proof's lengths close to the ones it committed to satisfies every AIR
with every bus's queries included in what is provided, with probability at most
`q · roundError + hashError F (h + 1) q`, `q = Q + verifierQueries`. -/
theorem batchKnowledgeSoundness_ro_inclusion (C : Statement F) (publicValues : Fin C.k → List F)
    (δ δ' : (Fin C.k → ℕ) → NNReal) (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate) (Q : Nat)
    (prover : C.NIProver EF) (hQ : prover.IsTotalQueryBound Q)
    (hcounts : ∀ n, C.Admits n → ∀ i, (C.air i).CountsBounded (n i)) :
    Pr{let (proof, log, verdict) ← C.run publicValues prover}[
      verdict = .ok () ∧
        ∀ h : C.Admits (C.lengthsOf proof),
          ∀ traces ∈ closeTraces (C.setupAt EF _ h) (δ' (C.lengthsOf proof))
              (committedTraces (C.setupAt EF _ h) log proof),
            ¬ (C.setupAt EF _ h).SatisfiedWithInclusion traces publicValues] ≤
      (Q + C.verifierQueries EF) * C.roundError EF δ δ' +
        hashError F (C.params.capHeight + 1) (Q + C.verifierQueries EF) :=
  prob_unopenedInclusionB_le C publicValues δ δ' hδ' Q prover hQ hcounts

end CompStark.Iop.Batch
