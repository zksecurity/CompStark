/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Interaction.StarkKnowledge

/-! # Knowledge soundness of the STARK

The STARK, as an interactive oracle protocol on ArkLib's interaction layer
(`CompStark/Interaction/Stark.lean`), is knowledge sound: against any prover, the probability that
the verifier accepts while no trace of the length the prover claims, close to the trace it commits
to, satisfies the AIR (`Statement.farAcceptance`) is at most the statement's knowledge error, the
largest over the admitted lengths (`Statement.knowledgeError`, `CompStark/SoundnessError.lean`).

The proof is a round-by-round knowledge certificate (`CompStark/Interaction/StarkKnowledge.lean`):
the doomed-transcript argument of `CompStark/Sound/Rbr.lean` for the challenges `α`, `ζ` and `a`,
appended to ArkLib's FRI certificate. Its rounds: batching by powers keeps DEEP quotients that are
not near on a common set far (`Sound/Batching.lean`); DEEP quotients near on a common set force
the claimed values to be those of a candidate trace and quotient, polynomials close to the
committed words (`Sound/Decoding.lean`); and then the constraint check at `ζ` is a polynomial
identity that a failing candidate satisfies at few points (`Sound/Algebra.lean`).
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound _root_.Interaction _root_.Interaction.Oracle OracleComp
open OracleSpec

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- The probability that the verifier accepts `prover` while no trace close to the trace it
commits to, at proximity `δ' n` for the length `2 ^ n` it claims, satisfies the AIR there. -/
noncomputable def Statement.farAcceptance (C : Statement F) (EF : Type) [Challenge F EF]
    (publicValues : List F) (δ' : ℕ → NNReal) {OutP : (C.protocol EF).tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec (C.protocol EF).tree
      (C.protocol EF).roles OutP) : ENNReal :=
  Pr{let result ← (executeStrategies unifSpec (C.protocol EF).tree (C.protocol EF).roles
    (C.protocol EF).oracles noAccess noImpl prover (C.verifier EF publicValues))}[
      result.2.2 = true ∧
        ∀ trace ∈ closeTraces (C.setup EF result.1.1) (δ' result.1.1.1)
            ((C.setup EF result.1.1).traceWords result.1.2.1),
          ¬ C.air.Satisfied result.1.1.1 trace publicValues]

/-- **Knowledge soundness.** Against any prover, the verifier accepts while no trace of the length
the prover claims, close to the trace it commits to, satisfies the AIR with probability at most
the statement's knowledge error, the largest over the admitted lengths. FRI tests proximity
`δ n`, and the extractor list-decodes at any `δ' n` below `1 - rate` (typically `δ' n ≥ δ n`, the
difference being the proximity loss of batching). -/
theorem knowledgeSoundness (C : Statement F) (publicValues : List F)
    {OutP : (C.protocol EF).tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec (C.protocol EF).tree
      (C.protocol EF).roles OutP)
    (δ δ' : ℕ → NNReal) (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate) :
    C.farAcceptance EF publicValues δ' prover ≤ C.knowledgeError EF δ δ' :=
  Statement.extraction_le_knowledgeError C EF publicValues δ δ' hδ' prover

end CompStark.Iop
