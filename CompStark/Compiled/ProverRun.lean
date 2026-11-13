/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compiled.ProverChecks
public import CompStark.Compiled.Transfer

/-! The ideal run of a prover: the authored path it produces against the duplex, its words in place
of their roots (`Presentation.idealRun`). It composes along appended presentations
(`idealRun_append`), and the compiled run's path, reconstructed from the prover's own rows, is the
ideal run's path when every Merkle word decodes from its rows (`run_reconstruct`). -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

@[expose] public section

namespace CompStark.Compiled

open CompStark.BinaryFields CompStark.Keccak CompStark.Compose
open Interaction Interaction.Oracle Interaction.Oracle.Security

/-- The authored path a prover produces against the duplex and the duplex state after it; `none`
if a grinding search fails. -/
def Presentation.idealRun : {original : Protocol} → (presentation : Presentation original) →
    presentation.Prover → Transcript.State → Option (original.tree.ExecutionPath × Transcript.State)
  | _, .refine wire projection, prover, state =>
      (wire.idealRun prover state).map fun result => (projection.path result.1, result.2)
  | _, .done, _, state => some (PUnit.unit, state)
  | _, @Presentation.sender _ _ _ encode next, prover, state =>
      let step := prover state
      ((next step.1).idealRun step.2 (Transcript.replay state (encode step.1))).map
        fun result => (⟨step.1, result.1⟩, result.2)
  | _, @Presentation.reveal _ _ _ _ encode next, prover, state =>
      let step := prover state
      (next.idealRun step.2 (Transcript.replay state (encode step.1))).map
        fun result => (⟨step.1, result.1⟩, result.2)
  | _, @Presentation.merkle _ _ _ _ layout next, prover, state =>
      let step := prover state
      let root := Commit.root layout.height fun i => Commit.restoreLeaf layout.leafWords (step.2.1 i)
      (next.idealRun step.2.2 (Transcript.replay state (Transcript.digestEvents root))).map
        fun result => (⟨step.1, result.1⟩, result.2)
  | _, @Presentation.announce _ _ _ _ _ _, prover, _ => nomatch prover
  | _, .grind bits next, prover, state =>
      (grindSearch state bits grindFuel).bind fun nonce =>
        next.idealRun prover (Transcript.grindCheck state bits nonce).2
  | _, @Presentation.challenge _ _ _ _ _ move shape draw next, prover, state =>
      let drawn := draw.run state
      (next.idealRun (prover state drawn.1) drawn.2).map fun result =>
        (⟨move drawn.1, cast (congrArg (fun protocol : Protocol => protocol.tree.ExecutionPath)
          (shape drawn.1).symm) result.1⟩, result.2)

/-- The ideal run of a sender. -/
theorem Presentation.idealRun_sender {Moves : Type} [DecidableEq Moves] {rest : Moves → Protocol}
    (encode : Moves → List Transcript.Event) (next : (move : Moves) → Presentation (rest move))
    (prover : (Presentation.sender encode next).Prover) (state : Transcript.State) :
    (Presentation.sender encode next).idealRun prover state =
      ((next (prover state).1).idealRun (prover state).2
        (Transcript.replay state (encode (prover state).1))).map
        fun result => (⟨(prover state).1, result.1⟩, result.2) := rfl

/-- The ideal run of a Merkle word. -/
theorem Presentation.idealRun_merkle {Messages : Type} [DecidableEq Messages]
    {interface : OracleInterface Messages} {rest : Protocol} (layout : LeafLayout Messages)
    (next : Presentation rest) (prover : (Presentation.merkle (interface := interface) layout next).Prover)
    (state : Transcript.State) :
    (Presentation.merkle (interface := interface) layout next).idealRun prover state =
      (next.idealRun (prover state).2.2 (Transcript.replay state (Transcript.digestEvents
        (Commit.root layout.height fun i => Commit.restoreLeaf layout.leafWords ((prover state).2.1 i))))).map
        fun result => (⟨(prover state).1, result.1⟩, result.2) := rfl

/-- The ideal run of a grinding move. -/
theorem Presentation.idealRun_grind {original : Protocol} (bits : ℕ) (next : Presentation original)
    (prover : (Presentation.grind bits next).Prover) (state : Transcript.State) :
    (Presentation.grind bits next).idealRun prover state =
      (grindSearch state bits grindFuel).bind fun nonce =>
        next.idealRun prover (Transcript.grindCheck state bits nonce).2 := rfl

/-- The ideal run of a challenge whose move is the challenge. -/
theorem Presentation.idealRun_challenge {Challenge : Type} [SampleableType Challenge] {tail : Protocol}
    (draw : Draw Challenge) (next : Presentation tail)
    (prover : (Presentation.challenge (rest := fun _ => tail) id (fun _ => rfl) draw next).Prover)
    (state : Transcript.State) :
    (Presentation.challenge (rest := fun _ => tail) id (fun _ => rfl) draw next).idealRun prover state =
      (next.idealRun (prover state (draw.run state).1) (draw.run state).2).map
        fun result => (⟨(draw.run state).1, result.1⟩, result.2) := rfl

/-- Joining commutes with a transport of the prefix's protocol. -/
theorem joinPath_cast {first next : Protocol} (equal : first = next) (second : Protocol)
    (head : next.tree.ExecutionPath) (tail : second.tree.ExecutionPath) :
    joinPath first second (cast (congrArg (fun p : Protocol => p.tree.ExecutionPath) equal.symm) head)
      tail =
      cast (congrArg (fun p : Protocol => p.tree.ExecutionPath)
        (congrArg (fun p => appendProtocol p second) equal).symm) (joinPath next second head tail) := by
  subst next
  rfl

/-- A projection extended over a suffix projects a joined path in its prefix. -/
theorem Projection.path_join {source target : Protocol} (projection : Projection source target)
    (suffix : Protocol) (head : source.tree.ExecutionPath) (tail : suffix.tree.ExecutionPath) :
    (projection.append suffix).path (joinPath source suffix head tail) =
      joinPath target suffix (projection.path head) tail := by
  induction projection with
  | refl => rfl
  | read next ih => exact ih head.1 head.2
  | @sender Wire Moves source target map next ih =>
      exact congrArg (Sigma.mk (map head.1)) (ih head.1 head.2)
  | @challenge Challenge source target next ih =>
      exact congrArg (Sigma.mk head.1) (ih head.1 head.2)
  | oracle next ih => exact congrArg (Sigma.mk head.1) (ih head.2)

/-- The ideal run of an appended prover runs the prefix, then the suffix's prover at the prefix's
path from the prefix's final state. -/
theorem Presentation.idealRun_append {first second : Protocol} :
    (presentation : Presentation first) → (suffix : Presentation second) →
    (prover : presentation.Prover) → (next : first.tree.ExecutionPath → suffix.Prover) →
    (state : Transcript.State) →
    (presentation.append suffix).idealRun (Prover.append presentation suffix prover next) state =
      (presentation.idealRun prover state).bind fun head =>
        (suffix.idealRun (next head.1) head.2).map fun tail =>
          (joinPath first second head.1 tail.1, tail.2)
  | .refine wire projection, suffix, prover, next, state => by
      change ((wire.append suffix).idealRun (Prover.append wire suffix prover
          fun path => next (projection.path path)) state).map
        (fun result => ((projection.append second).path result.1, result.2)) = _
      rw [idealRun_append wire suffix prover _ state]
      change (((wire.idealRun prover state).bind fun head =>
          (suffix.idealRun (next (projection.path head.1)) head.2).map fun tail =>
            (joinPath _ second head.1 tail.1, tail.2)).map _) =
        ((wire.idealRun prover state).map fun result => (projection.path result.1, result.2)).bind _
      cases wire.idealRun prover state with
      | none => rfl
      | some head =>
          dsimp only [Option.bind, Option.map]
          cases suffix.idealRun (next (projection.path head.1)) head.2 with
          | none => rfl
          | some tail =>
              exact congrArg (fun path => some (path, tail.2))
                (Projection.path_join projection second head.1 tail.1)
  | .done, suffix, _, next, state => by
      change suffix.idealRun (next PUnit.unit) state = (suffix.idealRun (next PUnit.unit) state).map _
      cases suffix.idealRun (next PUnit.unit) state <;> rfl
  | @Presentation.sender _ _ _ encode rest, suffix, prover, next, state => by
      change (((rest (prover state).1).append suffix).idealRun
          (Prover.append (rest (prover state).1) suffix (prover state).2
            fun path => next ⟨(prover state).1, path⟩)
          (Transcript.replay state (encode (prover state).1))).map _ = _
      rw [idealRun_append (rest (prover state).1) suffix (prover state).2 _ _]
      change _ = (((rest (prover state).1).idealRun (prover state).2
        (Transcript.replay state (encode (prover state).1))).map _).bind _
      cases (rest (prover state).1).idealRun (prover state).2
          (Transcript.replay state (encode (prover state).1)) with
      | none => rfl
      | some head =>
          dsimp only [Option.bind, Option.map]
          cases suffix.idealRun (next ⟨(prover state).1, head.1⟩) head.2 <;> rfl
  | @Presentation.reveal _ _ _ _ encode rest, suffix, prover, next, state => by
      change ((rest.append suffix).idealRun
          (Prover.append rest suffix (prover state).2 fun path => next ⟨(prover state).1, path⟩)
          (Transcript.replay state (encode (prover state).1))).map _ = _
      rw [idealRun_append rest suffix (prover state).2 _ _]
      change _ = ((rest.idealRun (prover state).2
        (Transcript.replay state (encode (prover state).1))).map _).bind _
      cases rest.idealRun (prover state).2 (Transcript.replay state (encode (prover state).1)) with
      | none => rfl
      | some head =>
          dsimp only [Option.bind, Option.map]
          cases suffix.idealRun (next ⟨(prover state).1, head.1⟩) head.2 <;> rfl
  | @Presentation.merkle _ _ _ _ layout rest, suffix, prover, next, state => by
      change ((rest.append suffix).idealRun
          (Prover.append rest suffix (prover state).2.2 fun path => next ⟨(prover state).1, path⟩)
          (Transcript.replay state (Transcript.digestEvents (Commit.root layout.height
            fun i => Commit.restoreLeaf layout.leafWords ((prover state).2.1 i))))).map _ = _
      rw [idealRun_append rest suffix (prover state).2.2 _ _]
      change _ = ((rest.idealRun (prover state).2.2 (Transcript.replay state
        (Transcript.digestEvents (Commit.root layout.height
          fun i => Commit.restoreLeaf layout.leafWords ((prover state).2.1 i))))).map _).bind _
      cases rest.idealRun (prover state).2.2 (Transcript.replay state
          (Transcript.digestEvents (Commit.root layout.height
            fun i => Commit.restoreLeaf layout.leafWords ((prover state).2.1 i)))) with
      | none => rfl
      | some head =>
          dsimp only [Option.bind, Option.map]
          cases suffix.idealRun (next ⟨(prover state).1, head.1⟩) head.2 <;> rfl
  | @Presentation.announce _ _ _ _ _ _, _, prover, _, _ => nomatch prover
  | .grind bits rest, suffix, prover, next, state => by
      change ((grindSearch state bits grindFuel).bind fun nonce =>
          (rest.append suffix).idealRun (Prover.append rest suffix prover next)
            (Transcript.grindCheck state bits nonce).2) =
        ((grindSearch state bits grindFuel).bind fun nonce =>
          rest.idealRun prover (Transcript.grindCheck state bits nonce).2).bind _
      cases grindSearch state bits grindFuel with
      | none => rfl
      | some nonce =>
          exact idealRun_append rest suffix prover next (Transcript.grindCheck state bits nonce).2
  | @Presentation.challenge _ _ _ _ tail move shape draw rest, suffix, prover, next, state => by
      change ((rest.append suffix).idealRun
          (Prover.append rest suffix (prover state (draw.run state).1) fun path =>
            next ⟨move (draw.run state).1, cast (congrArg (fun protocol : Protocol => protocol.tree.ExecutionPath)
              (shape (draw.run state).1).symm) path⟩) (draw.run state).2).map _ = _
      rw [idealRun_append rest suffix (prover state (draw.run state).1) _ _]
      change _ = ((rest.idealRun (prover state (draw.run state).1) (draw.run state).2).map _).bind _
      cases rest.idealRun (prover state (draw.run state).1) (draw.run state).2 with
      | none => rfl
      | some head =>
          dsimp only [Option.bind, Option.map]
          cases suffix.idealRun _ head.2 with
          | none => rfl
          | some result =>
              exact congrArg (fun path => some (path, result.2)) (congrArg (Sigma.mk (move (draw.run state).1))
                (joinPath_cast (shape (draw.run state).1) second head.1 result.1).symm)

/-- Every Merkle word a prover sends decodes from the complete leaf images of its rows. -/
def Presentation.Prover.Faithful : {original : Protocol} → (presentation : Presentation original) →
    presentation.Prover → Prop
  | _, .refine wire _, prover => Prover.Faithful wire prover
  | _, .done, _ => True
  | _, @Presentation.sender _ _ _ _ next, prover =>
      ∀ state, Prover.Faithful (next (prover state).1) (prover state).2
  | _, @Presentation.reveal _ _ _ _ _ next, prover => ∀ state, Prover.Faithful next (prover state).2
  | _, @Presentation.merkle _ _ _ _ layout next, prover => ∀ state,
      layout.decode (fun i => some (Commit.restoreLeaf layout.leafWords ((prover state).2.1 i))) =
        (prover state).1 ∧ Prover.Faithful next (prover state).2.2
  | _, @Presentation.announce _ _ _ _ _ _, _ => True
  | _, .grind _ next, prover => Prover.Faithful next prover
  | _, @Presentation.challenge _ _ _ _ _ _ _ _ next, prover =>
      ∀ state challenge, Prover.Faithful next (prover state challenge)

/-- A faithful prover's compiled path, reconstructed from complete leaf images of its rows, is its
ideal run's path. -/
theorem Presentation.run_reconstruct : {original : Protocol} → (presentation : Presentation original) →
    (prover : presentation.Prover) → Prover.Faithful presentation prover →
    (state : Transcript.State) →
    (result : (StandardBcs.compile Commit.Digest presentation.coin).tree.ExecutionPath ×
      List (ℕ → List K)) →
    presentation.run prover state = some result →
    (openings : Openings) → (leaves : ℕ → TreeOpening → ℕ → Option (List K)) → (slot : ℕ) →
    (∀ i (bound : i < result.2.length) tree, leaves (slot + i) tree =
      fun column => some (Commit.restoreLeaf tree.leafWords (result.2[i] column))) →
    ∃ after, presentation.idealRun prover state =
      some (presentation.reconstruct result.1 openings leaves slot, after)
  | _, .refine wire projection, prover, faithful, state, result, h, openings, leaves, slot, rows => by
      obtain ⟨after, ideal⟩ := run_reconstruct wire prover faithful state result h openings leaves slot rows
      exact ⟨after, by
        change (wire.idealRun prover state).map _ = _
        rw [ideal]
        rfl⟩
  | _, .done, _, _, state, result, h, _, _, _, _ => ⟨state, by cases h; rfl⟩
  | _, @Presentation.sender _ _ _ encode next, prover, faithful, state, result, h, openings, leaves, slot, rows => by
      obtain ⟨tail, htail, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨after, ideal⟩ := run_reconstruct (next (prover state).1) (prover state).2 (faithful state)
        _ tail htail openings leaves slot rows
      exact ⟨after, by
        change ((next (prover state).1).idealRun (prover state).2 _).map _ = _
        rw [ideal]
        rfl⟩
  | _, @Presentation.reveal _ _ _ _ encode next, prover, faithful, state, result, h, openings, leaves, slot, rows => by
      obtain ⟨tail, htail, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨after, ideal⟩ := run_reconstruct next (prover state).2 (faithful state)
        _ tail htail openings leaves slot rows
      exact ⟨after, by
        change (next.idealRun (prover state).2 _).map _ = _
        rw [ideal]
        rfl⟩
  | _, @Presentation.merkle Messages _ interface rest layout next, prover, faithful, state, result, h,
      openings, leaves, slot, rows => by
      obtain ⟨tail, htail, rfl⟩ := Option.map_eq_some_iff.mp h
      have shifted : ∀ i (bound : i < tail.2.length) tree, leaves (slot + 1 + i) tree =
          fun column => some (Commit.restoreLeaf tree.leafWords (tail.2[i] column)) := by
        intro i bound tree
        have := rows (i + 1) (by simp only [List.length_cons]; omega) tree
        rw [show slot + 1 + i = slot + (i + 1) by omega]
        exact this
      obtain ⟨after, ideal⟩ := run_reconstruct next (prover state).2.2 (faithful state).2
        _ tail htail openings leaves (slot + 1) shifted
      refine ⟨after, ?_⟩
      change (next.idealRun (prover state).2.2 _).map _ = _
      rw [ideal]
      let tree : TreeOpening :=
        ⟨Commit.root layout.height fun i => Commit.restoreLeaf layout.leafWords ((prover state).2.1 i),
          layout.height, layout.rowWords, layout.leafWords, openingAt openings slot⟩
      have word : leaves slot tree = fun column =>
          some (Commit.restoreLeaf layout.leafWords ((prover state).2.1 column)) :=
        rows 0 (by simp only [List.length_cons]; omega) tree
      have decoded : layout.decode (leaves slot tree) = (prover state).1 := by
        rw [word]
        exact (faithful state).1
      exact congrArg (fun message => some ((⟨message, next.reconstruct tail.1 openings leaves (slot + 1)⟩ :
        (Protocol.oracleWith Messages interface rest).tree.ExecutionPath), after)) decoded.symm
  | _, @Presentation.announce _ _ _ _ _ _, prover, _, _, _, _, _, _, _, _ => nomatch prover
  | _, .grind bits next, prover, faithful, state, result, h, openings, leaves, slot, rows => by
      obtain ⟨nonce, hnonce, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨tail, htail, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨after, ideal⟩ := run_reconstruct next prover faithful _ tail htail openings leaves slot rows
      exact ⟨after, by
        change ((grindSearch state bits grindFuel).bind fun nonce =>
          next.idealRun prover (Transcript.grindCheck state bits nonce).2) = _
        rw [hnonce]
        exact ideal⟩
  | _, @Presentation.challenge _ _ _ _ _ move shape draw next, prover, faithful, state, result, h,
      openings, leaves, slot, rows => by
      obtain ⟨tail, htail, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨after, ideal⟩ := run_reconstruct next (prover state (draw.run state).1)
        (faithful state _) _ tail htail openings leaves slot rows
      exact ⟨after, by
        change (next.idealRun (prover state (draw.run state).1) (draw.run state).2).map _ = _
        rw [ideal]
        rfl⟩

end CompStark.Compiled
