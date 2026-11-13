/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compiled.Check

/-! The honest Fiat–Shamir prover of a presentation. A `Prover` gives, at each move of the
presentation, the prover's message from the duplex state and, at each verifier move, its
continuation for the drawn challenge. `Presentation.run` drives it: it absorbs every message,
commits every Merkle word to the root of its rows, draws every challenge from the duplex, and
searches every grinding nonce. -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

@[expose] public section

namespace CompStark.Compiled

open CompStark.BinaryFields CompStark.Keccak
open Interaction Interaction.Oracle Interaction.Oracle.Security

/-- The honest prover of a presentation: its messages from the duplex state, its Merkle words as
leaf rows, and its continuation at every drawn challenge. -/
def Presentation.Prover : {original : Protocol} → Presentation original → Type
  | _, .refine wire _ => wire.Prover
  | _, .done => PUnit
  | _, @Presentation.sender Moves _ _ _ next => Transcript.State → (move : Moves) × (next move).Prover
  | _, @Presentation.reveal Messages _ _ _ _ next => Transcript.State → Messages × next.Prover
  | _, @Presentation.merkle Messages _ _ _ _ next => Transcript.State → Messages × (ℕ → List K) × next.Prover
  | _, @Presentation.announce _ _ _ _ _ _ => PEmpty
  | _, .grind _ next => next.Prover
  | _, @Presentation.challenge Challenge _ _ _ _ _ _ _ next =>
      Transcript.State → Challenge → next.Prover

/-- The first nonce, below a search bound, that passes a grinding test. -/
def grindSearch (state : Transcript.State) (bits : ℕ) : (fuel : ℕ) → Option E
  | 0 => none
  | fuel + 1 =>
    let nonce := E.ofLimbs (K.ofBits fuel) 0 0
    if (Transcript.grindCheck state bits nonce).1 then some nonce else grindSearch state bits fuel

/-- The grinding search bound. -/
def grindFuel : ℕ := 2 ^ 26

/-- Drive a prover: its compiled path and, in commitment order, the rows of every Merkle word;
`none` if a grinding search fails. -/
def Presentation.run : {original : Protocol} → (presentation : Presentation original) →
    presentation.Prover → Transcript.State →
    Option ((StandardBcs.compile Commit.Digest presentation.coin).tree.ExecutionPath × List (ℕ → List K))
  | _, .refine wire _, prover, state => wire.run prover state
  | _, .done, _, _ => some (PUnit.unit, [])
  | _, @Presentation.sender _ _ _ encode next, prover, state =>
      let step := prover state
      (Presentation.run (next step.1) step.2 (Transcript.replay state (encode step.1))).map
        fun result => (⟨step.1, result.1⟩, result.2)
  | _, @Presentation.reveal _ _ _ _ encode next, prover, state =>
      let step := prover state
      (next.run step.2 (Transcript.replay state (encode step.1))).map
        fun result => (⟨step.1, result.1⟩, result.2)
  | _, @Presentation.merkle _ _ _ _ layout next, prover, state =>
      let step := prover state
      let root := Commit.root layout.height fun i => Commit.restoreLeaf layout.leafWords (step.2.1 i)
      (next.run step.2.2 (Transcript.replay state (Transcript.digestEvents root))).map
        fun result => (⟨root, result.1⟩, step.2.1 :: result.2)
  | _, @Presentation.announce _ _ _ _ _ _, prover, _ => nomatch prover
  | _, .grind bits next, prover, state =>
      (grindSearch state bits grindFuel).bind fun nonce =>
        (next.run prover (Transcript.grindCheck state bits nonce).2).map
          fun result => (⟨nonce, result.1⟩, result.2)
  | _, @Presentation.challenge _ _ _ _ _ _ _ draw next, prover, state =>
      let drawn := draw.run state
      (next.run (prover state drawn.1) drawn.2).map fun result => (⟨drawn.1, result.1⟩, result.2)

/-- A prover of a presentation followed by a prover of its suffix chosen from the presentation's
authored path. -/
def Presentation.Prover.append {first second : Protocol} :
    (presentation : Presentation first) → (suffix : Presentation second) →
    presentation.Prover → (first.tree.ExecutionPath → suffix.Prover) →
    (presentation.append suffix).Prover
  | .refine wire projection, suffix, prover, next =>
      Prover.append wire suffix prover fun path => next (projection.path path)
  | .done, _, _, next => next PUnit.unit
  | @Presentation.sender _ _ _ _ rest, suffix, prover, next => fun state =>
      let step := prover state
      ⟨step.1, Prover.append (rest step.1) suffix step.2 fun path => next ⟨step.1, path⟩⟩
  | @Presentation.reveal _ _ _ _ _ rest, suffix, prover, next => fun state =>
      let step := prover state
      (step.1, Prover.append rest suffix step.2 fun path => next ⟨step.1, path⟩)
  | @Presentation.merkle _ _ _ _ _ rest, suffix, prover, next => fun state =>
      let step := prover state
      (step.1, step.2.1, Prover.append rest suffix step.2.2 fun path => next ⟨step.1, path⟩)
  | @Presentation.announce _ _ _ _ _ _, _, prover, _ => nomatch prover
  | .grind _ rest, suffix, prover, next => Prover.append rest suffix prover next
  | @Presentation.challenge _ _ _ _ _ move shape _ rest, suffix, prover, next => fun state challenge =>
      Prover.append rest suffix (prover state challenge) fun path =>
        next ⟨move challenge, cast (congrArg (fun protocol : Protocol => protocol.tree.ExecutionPath)
          (shape challenge).symm) path⟩

end CompStark.Compiled
