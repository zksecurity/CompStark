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
`q · roundError + hashError F q`, `q = Q + verifierQueries`. `roundError` is the largest error of
one oracle answer, the lookup challenges' LogUp error and every round of the batch IOP at its
worst instance, each credited with its grinding, FRI's folds with the shorter instances' words
injected (`CompStark/BatchNonInteractiveError.lean`), and `hashError` bounds collisions and
predictions of digests.

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
-/

@[expose] public section
namespace CompStark.Iop.Batch
open CompStark.Stark CompStark.Ni

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- **Knowledge soundness of the batch STARK in the random-oracle model.** A prover making at
most `Q` oracle calls gets a proof for the instances' trace lengths accepted, while no tuple of
traces close to the ones it committed to satisfies the batch, with probability at most
`q · roundError + hashError F q`, `q = Q + verifierQueries`: FRI tests proximity `δ`, and the
extractor list-decodes at any `δ'` below `1 - rate`. -/
theorem batchKnowledgeSoundness_ro (S : Setup EF) (publicValues : Fin S.k → List F)
    (δ δ' : NNReal) (hδ' : (δ' : ℝ) < 1 - S.rate) (Q : Nat) (prover : NIProver S)
    (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← run S publicValues prover}[
      verdict = .ok () ∧ proof.degreeBits.toList = List.ofFn S.logN ∧
        ∀ traces ∈ closeTraces S δ' (committedTraces S log proof),
          ¬ S.Satisfied traces publicValues] ≤
      (Q + S.verifierQueries) * roundError S δ δ' + hashError F (Q + S.verifierQueries) :=
  prob_unopenedB_le S publicValues δ δ' hδ' Q prover hQ

end CompStark.Iop.Batch
