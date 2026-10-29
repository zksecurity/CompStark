/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.BatchSoundness
public import CompStark.Sound.Single

/-! # Knowledge soundness of the STARK

The STARK, as an interactive oracle proof (`CompStark/Iop.lean`), is knowledge sound: for a
prover that claims a trace length the verifier admits and plays the STARK there
(`Statement.Prover`), if no trace of that length close to the one it commits to satisfies the AIR,
the verifier accepts it with probability at most the statement's knowledge error, the largest over
the admitted lengths (`Statement.knowledgeError`, `CompStark/SoundnessError.lean`).

At each length, a STARK is a batch of one instance (`Setup.toBatch`), with the same acceptance and
knowledge error (`Sound/Single.lean`), so this is the batch's argument
(`CompStark/BatchSoundness.lean`) for one instance. The proof (`CompStark/Sound/`) bounds the
acceptance probability challenge by challenge: FRI rejects words far from low degree
(`Sound/Fri.lean`, `Sound/FriGame.lean`); batching by powers keeps DEEP quotients that are not near
on a common set far (`Sound/Batching.lean`); DEEP quotients near on a common set force the claimed
values to be those of a candidate trace and quotient, polynomials close to the committed words
(`Sound/Decoding.lean`); and then the constraint check at `ζ` is a polynomial identity that a
failing candidate satisfies at few points (`Sound/Algebra.lean`). `Sound/Assembly.lean` and
`Sound/BatchAssembly.lean` sum the bounds.
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- **Knowledge soundness.** For a prover that claims a trace length the verifier admits and plays
the STARK there: if no trace of that length close to the prover's committed trace satisfies the
AIR, the verifier accepts the prover with probability at most the statement's knowledge error, the
largest over the admitted lengths. FRI tests proximity `δ n`, and the extractor list-decodes at any
`δ' n` below `1 - rate` (typically `δ' n ≥ δ n`, the difference being the proximity loss of
batching). So a prover accepted with higher probability has committed to a trace within
`δ' n` of one that satisfies the AIR. -/
theorem knowledgeSoundness (C : Statement F) (publicValues : List F) (prover : C.Prover EF)
    (δ δ' : ℕ → NNReal) (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate) :
    (∀ trace ∈ closeTraces prover.setup (δ' prover.logN) prover.prover.trace,
      ¬ C.air.Satisfied prover.logN trace publicValues) →
      acceptance publicValues prover.prover ≤ C.knowledgeError EF δ δ' := by
  intro h
  refine le_trans ?_ (le_iSup₂ (f := fun n hn ↦ knowledgeError (C.setupAt EF n hn) (δ n) (δ' n))
    prover.logN prover.admits)
  rw [← acceptance_toBatch, ← knowledgeError_toBatch]
  exact batchAcceptance_le prover.setup.toBatch (fun _ ↦ publicValues) prover.prover.toBatch _ _
    (by rw [rate_toBatch, Statement.rate_setupAt]; exact hδ' _ prover.admits)
    fun traces htraces hsat ↦ h _ (htraces ⟨0, Nat.one_pos⟩) (hsat.air ⟨0, Nat.one_pos⟩)

end CompStark.Iop
