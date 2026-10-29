/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.Assembly

/-! # Knowledge soundness in the random-oracle model

The non-interactive STARK, with the verifier's hashes as random oracles
(`CompStark/RandomOracle.lean`), is knowledge sound for a statement, an AIR with FRI parameters and
no trace length: a prover making at most `Q` oracle calls gets a proof accepted, of the trace
length it claims, while no trace of that length close to the one it committed to satisfies the AIR
at that length, with probability at most `q · roundError + hashError F (h + 1) q`,
`q = Q + verifierQueries`. `roundError` is the largest error of one oracle answer over the trace
lengths the verifier admits (`Statement.Admits`), every round of the interactive oracle proof
credited with its grinding, and `hashError` bounds collisions and predictions of digests, `h` the
Merkle cap height (`CompStark/NonInteractiveError.lean`). The lengths share one term per query,
not one each: the STARK's domain separator puts the length into every transcript, so a fresh answer
can only be bad at the length its transcript has. That needs the challenger to read the domain
separator's bytes in chunks of at least one byte and the lengths to fit its eight bytes: a base
field of at least `2 ^ 8` elements with two-adicity below `2 ^ 64`. Plonky3's `uni-stark` observes
the length only there, as eight big-endian bytes of the instance label; its `batch-stark` also
observes every degree as a field element below `p`, so the batch needs neither assumption.

The preprocessed trace is part of the AIR, so of the statement: the game computes its verifying key
on the oracles before the prover runs (`Statement.setupRo`), at the length its rows fix, which the
verifier's shape check then requires of the proof; `verifierQueries` counts the setup's calls with
the verifier's. The extractor outputs only the main trace.

The committed trace is read off the prover's own hash queries (`committedTrace`), so the extractor
is straight-line. The proof (`CompStark/Ni/`) bounds, query by query, the probability that a fresh
answer clashes with a known digest or makes its round bad at some admitted length
(`Ni/RoundBounds.lean`, `Ni/Lengths.lean`), and shows that an accepted proof the extractor cannot
open forces such a query (`Ni/BadQuery.lean`): its length is admitted, and without clashes, every
round is parsed in order and binds what the extractor reads, the verifier's checks hold for the
extracted transcript (`Ni/Bcs.lean`), whose preprocessed columns are the AIR's since the setup's
queries bind the key's root (`Ni/Setup.lean`), and safe rounds then give a satisfying trace
(`Sound/Rbr.lean`). `Ni/Assembly.lean` sums the bounds.
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Ni

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- **Knowledge soundness in the random-oracle model.** On a base field of at least `2 ^ 8`
elements with two-adicity below `2 ^ 64`, a prover making at most `Q` oracle calls gets a proof
accepted while no trace of the proof's length close to the one it committed to satisfies the AIR
at that length, with probability at most `q · roundError + hashError F (h + 1) q`,
`q = Q + verifierQueries`: FRI tests proximity `δ n`, and the extractor list-decodes at any `δ' n`
below `1 - rate`, on `2 ^ n` rows. -/
theorem knowledgeSoundness_ro (C : Statement F) (publicValues : List F)
    (h8 : 2 ^ 8 ≤ Nat.card F) (h64 : twoAdicity F < 2 ^ 64) (δ δ' : ℕ → NNReal)
    (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate) (Q : Nat) (prover : C.NIProver EF)
    (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← C.run publicValues prover}[
      verdict = .ok () ∧
        ∀ h : C.Admits proof.degreeBits,
          ∀ trace ∈ closeTraces (C.setupAt EF _ h) (δ' proof.degreeBits)
              (committedTrace (C.setupAt EF _ h) log proof),
            ¬ C.air.Satisfied proof.degreeBits trace publicValues] ≤
      (Q + C.verifierQueries EF) * C.roundError EF δ δ' +
        hashError F (C.params.capHeight + 1) (Q + C.verifierQueries EF) :=
  prob_unopened_le C publicValues δ δ' h8 h64 hδ' Q prover hQ

end CompStark.Iop
