/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.BatchSoundness
public import CompStark.Sound.Single

/-! # Knowledge soundness of the STARK

The STARK, as an interactive oracle proof (`CompStark/Iop.lean`), is knowledge sound: if no trace
close to the one a prover commits to satisfies the AIR, the verifier accepts that prover with
probability at most the knowledge error (`CompStark/SoundnessError.lean`).

A STARK is a batch of one instance (`Setup.toBatch`), with the same acceptance and knowledge
error (`Sound/Single.lean`), so this is `batchKnowledgeSoundness` (`CompStark/BatchSoundness.lean`)
for one instance. The proof (`CompStark/Sound/`) bounds the acceptance probability challenge by
challenge: FRI rejects words far from low degree (`Sound/Fri.lean`, `Sound/FriGame.lean`);
batching by powers keeps DEEP quotients that are not near on a common set far
(`Sound/Batching.lean`); DEEP quotients near on a common set force the claimed values to be those
of a candidate trace and quotient, polynomials close to the committed words
(`Sound/Decoding.lean`); and then the constraint check at `ζ` is a polynomial identity that a
failing candidate satisfies at few points (`Sound/Algebra.lean`). `Sound/Assembly.lean` and
`Sound/BatchAssembly.lean` sum the bounds.
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- **Knowledge soundness.** If no trace close to the prover's committed trace satisfies the AIR,
the verifier accepts the prover with probability at most the knowledge error: FRI tests proximity
`δ`, and the extractor list-decodes at any `δ'` below `1 - rate` (typically `δ' ≥ δ`, the
difference being the proximity loss of batching). So a
prover accepted with higher probability has committed to a trace within `δ'` of one that
satisfies the AIR. -/
theorem knowledgeSoundness (S : Setup EF) [S.Folds] (publicValues : List F) (prover : Prover S)
    (δ δ' : NNReal) (hδ' : (δ' : ℝ) < 1 - S.rate) :
    (∀ trace ∈ closeTraces S δ' prover.trace, ¬ S.air.Satisfied S.logN trace publicValues) →
      acceptance publicValues prover ≤ knowledgeError S δ δ' := by
  intro h
  rw [← acceptance_toBatch, ← knowledgeError_toBatch]
  exact batchKnowledgeSoundness S.toBatch (fun _ ↦ publicValues) prover.toBatch δ δ'
    (by rwa [rate_toBatch]) fun traces htraces hsat ↦
      h _ (htraces ⟨0, Nat.one_pos⟩) (hsat.air ⟨0, Nat.one_pos⟩)

end CompStark.Iop
