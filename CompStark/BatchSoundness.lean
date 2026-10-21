/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.BatchAssembly

/-! # Knowledge soundness of the batch STARK

The batch STARK, as an interactive oracle proof (`CompStark/BatchIop.lean`), is knowledge sound:
if no tuple of traces, each close to the trace its instance's prover commits to, satisfies every
AIR, the verifier accepts with probability at most the knowledge error
(`CompStark/BatchSoundnessError.lean`).

The proof (`Sound/BatchAssembly.lean`) finds an instance none of whose close traces satisfies its
AIR and runs the single STARK's argument (`CompStark/Soundness.lean`) on it: FRI rejects words far
from low degree; batching by powers keeps DEEP quotients that are not near on a common set far;
the DEEP quotients of all opened words near on a common set make that instance's near too, which
forces its claimed values to be those of a candidate trace and quotient; and its constraint check
at `ζ` is a polynomial identity that a failing candidate satisfies at few points.
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- **Knowledge soundness of the batch STARK.** If no tuple of traces, each close to its
instance's committed trace, satisfies every instance's AIR, the verifier accepts the prover with
probability at most the knowledge error: FRI tests proximity `δ`, and the extractor list-decodes
every instance at any `δ'` below `1 - rate`. -/
theorem batchKnowledgeSoundness (S : Batch.Setup EF) (publicValues : Fin S.k → List F)
    (prover : Batch.Prover S) (δ δ' : NNReal) (hδ' : (δ' : ℝ) < 1 - S.rate) :
    (∀ traces ∈ Batch.closeTraces S δ' prover.trace,
      ¬ ∀ i, (S.air i).Satisfied S.logN (traces i) (publicValues i)) →
      Batch.acceptance publicValues prover ≤ Batch.knowledgeError S δ δ' :=
  batchAcceptance_le S publicValues prover δ δ' hδ'

end CompStark.Iop
