/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.Assembly

/-! # Knowledge soundness in the random-oracle model

The non-interactive STARK, with the verifier's hashes as random oracles
(`CompStark/RandomOracle.lean`), is knowledge sound: a prover making at most `Q` oracle calls gets
a proof accepted while no trace close to the one it committed to satisfies the AIR with
probability at most `q · roundError + hashError q`, `q = Q + verifierQueries`. `roundError` is the
largest error of one oracle answer, every round of the interactive oracle proof credited with its
grinding, and `hashError` bounds collisions and predictions of digests (`CompStark/NonInteractiveError.lean`).

The committed trace is read off the prover's own hash queries (`committedTrace`), so the extractor
is straight-line. The proof (`CompStark/Ni/`) bounds, query by query, the probability that a fresh
answer clashes with a known digest or makes its round bad (`Ni/RoundBounds.lean`), and shows that
an accepted proof the extractor cannot open forces such a query (`Ni/BadQuery.lean`): without
clashes, every round is parsed in order and binds what the extractor reads, the verifier's checks
hold for the extracted transcript (`Ni/Bcs.lean`), and safe rounds then give a satisfying trace
(`Sound/Rbr.lean`). `Ni/Assembly.lean` sums the bounds.
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Ni

local notation "F" => KoalaBear.Fast.Field

/-- **Knowledge soundness in the random-oracle model.** A prover making at most `Q` oracle calls
gets a proof for `2 ^ logN` rows accepted, while no trace close to the one it committed to
satisfies the AIR, with probability at most `q · roundError + hashError q`,
`q = Q + verifierQueries`: FRI tests proximity `δ`, and the extractor list-decodes at any `δ'`
below `1 - rate`. -/
theorem knowledgeSoundness_ro (S : Setup KoalaBear.Fast.Ext4) (publicValues : List F)
    (δ δ' : NNReal)
    (hδ' : (δ' : ℝ) < 1 - S.rate) (Q : Nat) (prover : NIProver S)
    (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← run S publicValues prover}[
      verdict = .ok () ∧ proof.degreeBits = S.logN ∧
        ∀ trace ∈ closeTraces S δ' (committedTrace S log proof),
          ¬ S.air.Satisfied S.logN trace publicValues] ≤
      (Q + S.verifierQueries) * roundError S δ δ' + hashError (Q + S.verifierQueries) :=
  prob_unopened_le S publicValues δ δ' hδ' Q prover hQ

end CompStark.Iop
