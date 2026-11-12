/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compose.Reduction

/-! Prefix-causal projections retain extra prover data and map transmitted messages to ideal moves. -/

set_option autoImplicit false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

@[expose] public section
namespace CompStark.Compiled
open Interaction Interaction.Oracle Interaction.Oracle.Security


/-- A causal simulation of an ideal protocol by a richer public wire protocol. -/
inductive Projection : Protocol → Protocol → Type 1
  /-- Identical protocol trees project identically. -/
  | refl (protocol : Protocol) : Projection protocol protocol
  /-- An extra prover read retains data in the remaining projection. -/
  | read {Moves : Type} {source : Moves → Protocol} {target : Protocol}
      (next : (move : Moves) → Projection (source move) target) :
      Projection (.public .sender Moves source) target
  /-- A transmitted message determines one ideal sender move. -/
  | sender {Wire Moves : Type} {source : Wire → Protocol} {target : Moves → Protocol}
      (map : Wire → Moves) (next : (wire : Wire) → Projection (source wire) (target (map wire))) :
      Projection (.public .sender Wire source) (.public .sender Moves target)
  /-- A verifier challenge is shared; its value may select the remaining projection. -/
  | challenge {Challenge : Type} {source target : Challenge → Protocol}
      (next : (challenge : Challenge) → Projection (source challenge) (target challenge)) :
      Projection (.public .receiver Challenge source) (.public .receiver Challenge target)
  /-- Oracle words and their interfaces are preserved. -/
  | oracle {Messages : Type} {interface : OracleInterface Messages} {source target : Protocol}
      (next : Projection source target) :
      Projection (.oracleWith Messages interface source) (.oracleWith Messages interface target)

/-- Project an execution using only the data already read at each ideal move. -/
def Projection.path : {source target : Protocol} → Projection source target →
    source.tree.ExecutionPath → target.tree.ExecutionPath
  | _, _, .refl _, path => path
  | _, _, .read next, path => (next path.1).path path.2
  | _, _, .sender map next, path => ⟨map path.1, (next path.1).path path.2⟩
  | _, _, .challenge next, path => ⟨path.1, (next path.1).path path.2⟩
  | _, _, .oracle next, path => ⟨path.1, next.path path.2⟩

/-- Pull back the ideal extractor, using identity backward maps at additional prover reads. -/
def Projection.extractor : {source target : Protocol} → Projection source target →
    {state : KnowledgeState} → RoundExtractor target.tree state → RoundExtractor source.tree state
  | _, _, .refl _, _, extractor => extractor
  | _, _, .read next, state, extractor => fun move =>
      ⟨state, id, (next move).extractor extractor⟩
  | _, _, .sender map next, _, extractor => fun wire =>
      ⟨(extractor (map wire)).1, (extractor (map wire)).2.1,
        (next wire).extractor (extractor (map wire)).2.2⟩
  | _, _, .challenge next, _, extractor => fun challenge =>
      ⟨(extractor challenge).1, (extractor challenge).2.1,
        (next challenge).extractor (extractor challenge).2.2⟩
  | _, _, .oracle next, _, extractor => fun message =>
      ⟨(extractor message).1, (extractor message).2.1,
        next.extractor (extractor message).2.2⟩

/-- Projection preserves the exact terminal knowledge state. -/
theorem Projection.terminalState_eq {source target : Protocol} (projection : Projection source target)
    {state : KnowledgeState} (extractor : RoundExtractor target.tree state)
    (path : source.tree.ExecutionPath) :
    (projection.extractor extractor).terminalState path = extractor.terminalState (projection.path path) := by
  induction projection generalizing state with
  | refl => rfl
  | read next ih => exact ih path.1 extractor path.2
  | sender map next ih => exact ih path.1 (extractor (map path.1)).2.2 path.2
  | challenge next ih => exact ih path.1 (extractor path.1).2.2 path.2
  | oracle next ih => exact ih (extractor path.1).2.2 path.2

/-- Projection preserves the composed backward extraction map and its terminal witness. -/
theorem Projection.extractWitness_eq {source target : Protocol} (projection : Projection source target)
    {state : KnowledgeState} (extractor : RoundExtractor target.tree state)
    (path : source.tree.ExecutionPath)
    (witness : ((projection.extractor extractor).terminalState path).Witness) :
    (projection.extractor extractor).extractWitness path witness =
      extractor.extractWitness (projection.path path)
        (projection.terminalState_eq extractor path ▸ witness) := by
  induction projection generalizing state with
  | refl => rfl
  | read next ih => exact ih path.1 extractor path.2 witness
  | sender map next ih =>
      exact congrArg (extractor (map path.1)).2.1 (ih path.1 _ path.2 witness)
  | challenge next ih => exact congrArg (extractor path.1).2.1 (ih path.1 _ path.2 witness)
  | oracle next ih => exact congrArg (extractor path.1).2.1 (ih _ path.2 witness)

/-- Extra reads and mapped senders preserve every ideal prover knowledge implication. -/
theorem Projection.prover_preserving {source target : Protocol} (projection : Projection source target)
    {state : KnowledgeState} (extractor : RoundExtractor target.tree state)
    (preserving : extractor.IsProverPreserving target.roles) :
    (projection.extractor extractor).IsProverPreserving source.roles := by
  induction projection generalizing state with
  | refl => exact preserving
  | read next ih => exact ⟨fun _ _ _ known => known, fun move => ih move extractor preserving⟩
  | sender map next ih =>
      exact ⟨fun wire => preserving.1 (map wire), fun wire => ih wire _ (preserving.2 (map wire))⟩
  | challenge next ih =>
      exact ⟨fun challenge => preserving.1 challenge, fun challenge => ih challenge _ (preserving.2 challenge)⟩
  | oracle next ih => exact ⟨preserving.1, fun message => ih _ (preserving.2 message)⟩

/-- A causal projection extends over an unchanged protocol suffix. -/
def Projection.append {source target : Protocol} (projection : Projection source target)
    (suffix : Protocol) : Projection (CompStark.Compose.appendProtocol source suffix)
      (CompStark.Compose.appendProtocol target suffix) :=
  match projection with
  | .refl _ => .refl _
  | .read next => .read fun move => (next move).append suffix
  | @Projection.sender Wire Moves source target map next =>
      @Projection.sender Wire Moves
        (fun wire => CompStark.Compose.appendProtocol (source wire) suffix)
        (fun move => CompStark.Compose.appendProtocol (target move) suffix)
        map fun wire => (next wire).append suffix
  | .challenge next => .challenge fun challenge => (next challenge).append suffix
  | .oracle next => .oracle (next.append suffix)

/-- Splitting a projected appended execution preserves its suffix path exactly. -/
theorem Projection.splitPath_append {source target : Protocol} (projection : Projection source target)
    (suffix : Protocol) (path : (CompStark.Compose.appendProtocol source suffix).tree.ExecutionPath) :
    CompStark.Compose.splitPath target suffix ((projection.append suffix).path path) =
      (projection.path (CompStark.Compose.splitPath source suffix path).1,
        (CompStark.Compose.splitPath source suffix path).2) := by
  induction projection with
  | refl => rfl
  | read next ih => exact ih path.1 path.2
  | @sender Wire Moves source target map next ih =>
      exact congrArg (fun pair : (target (map path.1)).tree.ExecutionPath × suffix.tree.ExecutionPath =>
        ((Sigma.mk (map path.1) pair.1 : (Protocol.public .sender Moves target).tree.ExecutionPath), pair.2))
        (ih path.1 path.2)
  | @challenge Challenge source target next ih =>
      exact congrArg (fun pair : (target path.1).tree.ExecutionPath × suffix.tree.ExecutionPath =>
        ((Sigma.mk path.1 pair.1 : (Protocol.public .receiver Challenge target).tree.ExecutionPath), pair.2))
        (ih path.1 path.2)
  | @oracle Messages interface source target next ih =>
      exact congrArg (fun pair : target.tree.ExecutionPath × suffix.tree.ExecutionPath =>
        ((Sigma.mk path.1 pair.1 : (Protocol.oracleWith Messages interface target).tree.ExecutionPath), pair.2))
        (ih path.2)

end CompStark.Compiled
