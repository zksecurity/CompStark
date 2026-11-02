/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ArkLib.ProofSystem.Fri.Interaction.Soundness
import all PolyFun.Interaction.Basic.StrategyOver

/-! # Executing verifiers node by node

A verifier on ArkLib's interaction layer that samples a challenge uniformly at a receiver node,
receives a public message at a sender node or an oracle message at an oracle node, and continues,
executes as the challenge, the prover's response and the execution of the continuation
(`executeStrategies_sample`, `executeStrategies_receive`, `executeStrategies_receiveOracle`). A
verifier whose final action is mapped executes to the mapped output
(`executeStrategies_mapOutput`).
-/

@[expose] public section
namespace CompStark.Interaction
open _root_.Interaction _root_.Interaction.Oracle OracleComp OracleSpec

variable {ι : Type} (ambient : OracleSpec ι)

set_option backward.isDefEq.respectTransparency false in
/-- A verifier sampling the challenge `sample` at a receiver node. -/
theorem executeStrategies_sample {M : Type} {rest : M → Oracle.TypeTree}
    (roles : (m : M) → (rest m).RoleDecoration) (oracles : (TypeTree.public M rest).OracleDecoration)
    (A : PFunctor) (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    {OutP : (TypeTree.public M rest).ExecutionPath → Type}
    {OutV : (TypeTree.public M rest).BranchPath → Type}
    (prover : Prover.Strategy ambient (.public M rest) ⟨.receiver, roles⟩ OutP)
    (sample : OracleComp ambient M)
    (next : (m : M) → Verifier.Strategy ambient (rest m) (roles m) (oracles.2 m) A
      (fun path ↦ OutV ⟨m, path⟩)) :
    executeStrategies ambient (.public M rest) ⟨.receiver, roles⟩ oracles A impl prover
      (show Verifier.Strategy ambient (.public M rest) ⟨.receiver, roles⟩ oracles A OutV from do
        let m ← liftComp sample _
        return ⟨m, next m⟩) = (do
        let m ← sample
        let p ← prover m
        let result ← executeStrategies ambient (rest m) (roles m) (oracles.2 m) A impl
          (OutP := fun path ↦ OutP ⟨m, path⟩) (OutV := fun path ↦ OutV ⟨m, path⟩) p (next m)
        return ⟨⟨m, result.1⟩, result.2.1, result.2.2⟩) := by
  rw [executeStrategies_public_receiver]
  simp only [simulateQ_bind, Fri.Interaction.simulateQ_liftAccessImpl_liftComp, simulateQ_pure,
    bind_assoc, pure_bind]

set_option backward.isDefEq.respectTransparency false in
/-- A verifier receiving a public message at a sender node. -/
theorem executeStrategies_receive {M : Type} {rest : M → Oracle.TypeTree}
    (roles : (m : M) → (rest m).RoleDecoration) (oracles : (TypeTree.public M rest).OracleDecoration)
    (A : PFunctor) (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    {OutP : (TypeTree.public M rest).ExecutionPath → Type}
    {OutV : (TypeTree.public M rest).BranchPath → Type}
    (prover : Prover.Strategy ambient (.public M rest) ⟨.sender, roles⟩ OutP)
    (next : (m : M) → Verifier.Strategy ambient (rest m) (roles m) (oracles.2 m) A
      (fun path ↦ OutV ⟨m, path⟩)) :
    executeStrategies ambient (.public M rest) ⟨.sender, roles⟩ oracles A impl prover
      (show Verifier.Strategy ambient (.public M rest) ⟨.sender, roles⟩ oracles A OutV from
        fun m ↦ pure (next m)) = (do
        let chosen ← prover
        let result ← executeStrategies ambient (rest chosen.1) (roles chosen.1)
          (oracles.2 chosen.1) A impl (OutP := fun path ↦ OutP ⟨chosen.1, path⟩)
          (OutV := fun path ↦ OutV ⟨chosen.1, path⟩) chosen.2 (next chosen.1)
        return ⟨⟨chosen.1, result.1⟩, result.2.1, result.2.2⟩) := by
  rw [executeStrategies_public_sender]
  simp only [simulateQ_pure, pure_bind]

set_option backward.isDefEq.respectTransparency false in
/-- A verifier receiving an oracle message. -/
theorem executeStrategies_receiveOracle {M : Type} {rest : PUnit → Oracle.TypeTree}
    (roles : (TypeTree.oracle M rest).RoleDecoration)
    (oracles : (TypeTree.oracle M rest).OracleDecoration)
    (A : PFunctor) (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    {OutP : (TypeTree.oracle M rest).ExecutionPath → Type}
    {OutV : (TypeTree.oracle M rest).BranchPath → Type}
    (prover : Prover.Strategy ambient (.oracle M rest) roles OutP)
    (next : Verifier.Strategy ambient (rest PUnit.unit) (roles.2 PUnit.unit)
      (oracles.2 PUnit.unit) (Access.extend A oracles.1) (fun path ↦ OutV ⟨PUnit.unit, path⟩)) :
    executeStrategies ambient (.oracle M rest) roles oracles A impl prover
      (show Verifier.Strategy ambient (.oracle M rest) roles oracles A OutV from pure next) = (do
        let chosen ← prover
        let result ← executeStrategies ambient (rest PUnit.unit) (roles.2 PUnit.unit)
          (oracles.2 PUnit.unit) (Access.extend A oracles.1)
          (Access.extendImpl A oracles.1 impl chosen.1)
          (OutP := fun path ↦ OutP ⟨chosen.1, path⟩)
          (OutV := fun path ↦ OutV ⟨PUnit.unit, path⟩) chosen.2 next
        return ⟨⟨chosen.1, result.1⟩, result.2.1, result.2.2⟩) := by
  rw [executeStrategies_oracle]
  simp only [simulateQ_pure, pure_bind]

section MapOutput

variable {M : Type} {rest : M → Oracle.TypeTree} {A : PFunctor}

set_option backward.isDefEq.respectTransparency false in
theorem mapOutput_sender (roles : (m : M) → (rest m).RoleDecoration)
    (oracles : (TypeTree.public M rest).OracleDecoration)
    {B C : (TypeTree.public M rest).BranchPath → Type}
    (f : (path : (TypeTree.public M rest).BranchPath) → B path → C path)
    (verifier : Verifier.Fragment ambient (.public M rest) ⟨.sender, roles⟩ oracles A B) (m : M) :
    (Verifier.Fragment.mapOutput ambient f verifier :
      Verifier.Fragment ambient (.public M rest) ⟨.sender, roles⟩ oracles A C) m =
      Verifier.Fragment.mapOutput ambient (fun path ↦ f ⟨m, path⟩) <$>
        (verifier m : OracleComp _ _) := by
  simp only [Verifier.Fragment.mapOutput, ShapeOver.mapOutput, Verifier.localShape,
    Verifier.decorate]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem mapOutput_receiver (roles : (m : M) → (rest m).RoleDecoration)
    (oracles : (TypeTree.public M rest).OracleDecoration)
    {B C : (TypeTree.public M rest).BranchPath → Type}
    (f : (path : (TypeTree.public M rest).BranchPath) → B path → C path)
    (verifier : Verifier.Fragment ambient (.public M rest) ⟨.receiver, roles⟩ oracles A B) :
    (Verifier.Fragment.mapOutput ambient f verifier : OracleComp _ _) =
      (fun next ↦ ⟨next.1, Verifier.Fragment.mapOutput ambient (fun path ↦ f ⟨next.1, path⟩)
        next.2⟩) <$> (verifier : OracleComp _ _) := by
  simp only [Verifier.Fragment.mapOutput, ShapeOver.mapOutput, Verifier.localShape,
    Verifier.decorate]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem mapOutput_oracle {rest : PUnit → Oracle.TypeTree}
    (roles : (TypeTree.oracle M rest).RoleDecoration)
    (oracles : (TypeTree.oracle M rest).OracleDecoration)
    {B C : (TypeTree.oracle M rest).BranchPath → Type}
    (f : (path : (TypeTree.oracle M rest).BranchPath) → B path → C path)
    (verifier : Verifier.Fragment ambient (.oracle M rest) roles oracles A B) :
    (Verifier.Fragment.mapOutput ambient f verifier : OracleComp _ _) =
      Verifier.Fragment.mapOutput ambient (fun path ↦ f ⟨PUnit.unit, path⟩) <$>
        (verifier : OracleComp _ _) := by
  simp only [Verifier.Fragment.mapOutput, ShapeOver.mapOutput, Verifier.localShape,
    Verifier.decorate]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem mapOutput_done (roles : TypeTree.done.RoleDecoration)
    (oracles : TypeTree.done.OracleDecoration) {B C : TypeTree.done.BranchPath → Type}
    (f : (path : TypeTree.done.BranchPath) → B path → C path)
    (verifier : Verifier.Fragment ambient .done roles oracles A B) :
    (Verifier.Fragment.mapOutput ambient f verifier : C PUnit.unit) =
      f PUnit.unit (verifier : B PUnit.unit) := by
  simp only [Verifier.Fragment.mapOutput, ShapeOver.mapOutput]

end MapOutput

set_option backward.isDefEq.respectTransparency false in
/-- A verifier whose final action is mapped by `g` executes to the mapped output. -/
theorem executeStrategies_mapOutput :
    (tree : Oracle.TypeTree) → (roles : tree.RoleDecoration) → (oracles : tree.OracleDecoration) →
    (A : PFunctor) → (impl : QueryImpl (OracleSpec.ofPFunctor A) Id) →
    {OutP : tree.ExecutionPath → Type} → {B C : tree.BranchPath → Type} →
    (g : (path : tree.BranchPath) → B path → C path) →
    (prover : Prover.Strategy ambient tree roles OutP) →
    (verifier : Verifier.Strategy ambient tree roles oracles A B) →
    executeStrategies ambient tree roles oracles A impl prover
      (Verifier.Fragment.mapOutput ambient (fun path act ↦ g path <$> act) verifier) =
      (fun result ↦ ⟨result.1, result.2.1, g result.1.toBranchPath result.2.2⟩) <$>
        executeStrategies ambient tree roles oracles A impl prover verifier
  | .done, _, _, A, impl, OutP, B, C, g, prover, verifier => by
    change executeStrategies ambient .done PUnit.unit PUnit.unit A impl prover _ =
      _ <$> executeStrategies ambient .done PUnit.unit PUnit.unit A impl prover _
    rw [executeStrategies_done, executeStrategies_done, mapOutput_done]
    simp only [simulateQ_map, map_bind, map_pure, bind_map_left]
    rfl
  | .public M rest, ⟨.sender, roles⟩, oracles, A, impl, OutP, B, C, g, prover, verifier => by
    rw [executeStrategies_public_sender, executeStrategies_public_sender]
    simp only [map_bind, map_pure, mapOutput_sender, simulateQ_map, bind_map_left]
    refine bind_congr fun chosen ↦ bind_congr fun next ↦ ?_
    erw [executeStrategies_mapOutput (rest chosen.1) (roles chosen.1) (oracles.2 chosen.1) A impl
      (fun path ↦ g ⟨chosen.1, path⟩)
      (OutP := fun path ↦ OutP ⟨chosen.1, path⟩) chosen.2 next]
    simp only [bind_map_left]
    rfl
  | .public M rest, ⟨.receiver, roles⟩, oracles, A, impl, OutP, B, C, g, prover, verifier => by
    rw [executeStrategies_public_receiver, executeStrategies_public_receiver]
    simp only [map_bind, map_pure, mapOutput_receiver, simulateQ_map, bind_map_left]
    refine bind_congr fun chosen ↦ bind_congr fun next ↦ ?_
    erw [executeStrategies_mapOutput (rest chosen.1) (roles chosen.1) (oracles.2 chosen.1) A impl
      (fun path ↦ g ⟨chosen.1, path⟩)
      (OutP := fun path ↦ OutP ⟨chosen.1, path⟩) next chosen.2]
    simp only [bind_map_left]
    rfl
  | .oracle M rest, roles, oracles, A, impl, OutP, B, C, g, prover, verifier => by
    rw [executeStrategies_oracle, executeStrategies_oracle]
    simp only [map_bind, map_pure, mapOutput_oracle, simulateQ_map, bind_map_left]
    refine bind_congr fun chosen ↦ bind_congr fun next ↦ ?_
    erw [executeStrategies_mapOutput (rest PUnit.unit) (roles.2 PUnit.unit) (oracles.2 PUnit.unit)
      (Access.extend A oracles.1) (Access.extendImpl A oracles.1 impl chosen.1)
      (fun path ↦ g ⟨PUnit.unit, path⟩)
      (OutP := fun path ↦ OutP ⟨chosen.1, path⟩) chosen.2 next]
    simp only [bind_map_left]
    rfl

end CompStark.Interaction
