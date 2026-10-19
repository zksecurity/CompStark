/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Assembly
public import CompStark.Sound.Fri
public import CompStark.Sound.Batching
public import CompStark.Sound.Decoding
public import CompStark.Sound.Algebra

/-! # Knowledge soundness of the STARK

The STARK, as an interactive oracle proof (`CompStark/Iop.lean`), is knowledge sound: if the
trace the extractor reads off a prover does not satisfy the AIR, the verifier accepts that prover
with probability at most the knowledge error (`CompStark/SoundnessError.lean`).

The proof (`CompStark/Sound/`) bounds the acceptance probability challenge by challenge: FRI
rejects words far from low degree (ArkLib's FRI soundness, `Sound/Fri.lean`); batching by powers
keeps a far DEEP quotient far (`Sound/Batching.lean`); near DEEP quotients force the claimed
values to be the decoded polynomials' (`Sound/Decoding.lean`); and then the constraint check at
`ζ` is a polynomial identity that a failing trace satisfies at few points (`Sound/Algebra.lean`).
`Sound/Assembly.lean` sums the bounds.
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound

local notation "F" => KoalaBear.Fast.Field

/-- **Knowledge soundness.** If the trace extracted from a prover does not satisfy the AIR, the
verifier accepts the prover with probability at most the knowledge error, at any proximity up to
the unique-decoding radius. -/
theorem knowledgeSoundness (S : Setup) (publicValues : List F) (prover : Prover S)
    (δ : NNReal) (hδ : δ ≤ S.uniqueDecodingRadius) :
    ¬ S.air.Satisfied S.logN (extract prover) publicValues →
      acceptance publicValues prover ≤ knowledgeError S δ :=
  knowledgeSoundness_of (friStep S) (friAtMostOne S) (batchingStep S) (decodingStep S)
    (algebraStep S) publicValues prover δ hδ

end CompStark.Iop
