/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.PositionSemantics
public import CompStark.Keccak.GkrProver.NativeBatching

/-! Committed-witness shifted evaluations and position messages of complete native layers. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak CompStark.Keccak.Gkr BF64

/-- Native pack equality scales use any explicitly identified entering dimension. -/
theorem nativePackRun_scale_dimension (w : SlicedWitness) (d : Nat) (claim : Claim) (s : W) (early : Array W)
    (writer : Writer) (value : W) (n : Nat) (hc : claim.point.size=n) :
    let final := nativePackRun w d claim s early writer value
    final.scale=eqEval (fun i : Fin n => claim.point[i.val]!) (fun i => final.point[i.val]!) := by
  subst n
  exact nativePackRun_scale w d claim s early writer value

/-- The single remaining native pack row is the committed factor at the complete sampled pack point. -/
theorem nativePackRun_get_protocol (w : SlicedWitness) {h : Nat} (q : Witness (h+4))
    (hn : w.nLog=h+8) (hw : PreChiRefines w q) (d : Fin 12) (s : W) (claim : Claim)
    (hc : claim.point.size=h+5) (early : Array W) (writer : Writer) (value : W) (j : Fin 1600) :
    let final := nativePackRun w d.val claim s early writer value
    final.table.get j.val=linearAtPack q d s (fun i : Fin (h+5) => final.point[i.val]!) j := by
  dsimp only
  rw [← PackedE.get_toArray _ _ (by
    rw [nativePackRun_table_size w (by omega) d.val claim (by omega) s early writer value]
    exact j.isLt)]
  exact nativePackRun_factor_protocol w q hn hw d s claim hc early writer value j

attribute [local irreducible] product nativePackRun positionLoop earlyValues prepareWeightMaps
  binaryValues Writer.sample Writer.writeAll instanceWeights sum evaluate eqTable transposeWeights

/-- Every evaluation transmitted by an actual native layer is its committed shifted-factor evaluation. -/
theorem proveLayerM_evaluations_protocol (writer : Writer) (w : SlicedWitness) {h : Nat}
    (q : Witness (h+4)) (hn : w.nLog=h+8) (hw : PreChiRefines w q) (d : Fin 12) (claim : Claim)
    (hc : claim.point.size=h+5) (hweights : claim.weights.size=1600) (k : Fin 3) :
    let result := Id.run (proveLayerM (M := Id) (fun _ _ => pure ()) writer w d.val claim prepareRmfeProducts)
    result.1.evaluations[k.val]! = shiftedEvaluation q d result.1.s
      (fun i : Fin (h+5) => result.1.packPoint[i.val]!)
      (fun i : Fin 11 => result.1.positionPoint[i.val]!) k.val := by
  rw [proveLayerM_eq_runs]
  dsimp only [layerFromRuns]
  set prod := product w d.val claim prepareRmfeProducts
  set sampled := (writer.writeAll prod.message).sample
  set early := earlyValues w d.val claim
    (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare sampled.1)) prepareRmfeProducts
    (binaryValues prod.packs claim.point (CompStark.Sumcheck.prepare sampled.1))
  set pack := nativePackRun w d.val claim sampled.1 early sampled.2 (evaluate prod.message sampled.1)
  change ((positionLoop pack.writer (claim.weights++Array.replicate 448 0) (positionFactors pack.table)
    pack.scale (sum (instanceWeights sampled.1)) 11).factors.map (·[0]!))[k.val]! = _
  exact positionLoop_evaluations_protocol q d claim hweights sampled.1 pack.scale
    (fun i : Fin (h+5) => pack.point[i.val]!) pack.table
    (nativePackRun_get_protocol w q hn hw d sampled.1 claim hc early sampled.2 (evaluate prod.message sampled.1))
    pack.writer k

/-- Interpreting an actual native layer preserves its committed shifted evaluations in the verifier field. -/
theorem proveLayerM_evaluations_toField (writer : Writer) (w : SlicedWitness) {h : Nat}
    (q : Witness (h+4)) (hn : w.nLog=h+8) (hw : PreChiRefines w q) (d : Fin 12) (claim : Claim)
    (hc : claim.point.size=h+5) (hweights : claim.weights.size=1600) (k : Fin 3) :
    let result := Id.run (proveLayerM (M := Id) (fun _ _ => pure ()) writer w d.val claim prepareRmfeProducts)
    (result.1.toProtocol (h+4)).evaluations k = shiftedEvaluation q d (result.1.toProtocol (h+4)).point
      (result.1.toProtocol (h+4)).packPoint (result.1.toProtocol (h+4)).positionPoint k.val := by
  dsimp only [Layer.toProtocol]
  rw [proveLayerM_evaluations_protocol writer w q hn hw d claim hc hweights k]
  exact shiftedEvaluation_map WordExt3.ringEquiv.toRingHom q d _ _ _ k.val

/-- Every actual native position round is the committed protocol's honest cubic coefficient strategy. -/
theorem proveLayerM_position_protocol (writer : Writer) (w : SlicedWitness) {h : Nat}
    (q : Witness (h+4)) (hn : w.nLog=h+8) (hw : PreChiRefines w q) (d : Fin 12) (claim : Claim)
    (hc : claim.point.size=h+5) (hweights : claim.weights.size=1600) :
    let result := Id.run (proveLayerM (M := Id) (fun _ _ => pure ()) writer w d.val claim prepareRmfeProducts)
    (result.1.toWordProtocol (h+4)).positionPolys =
      honestPositionRounds q d (claim.toWordProtocol (h+4)) (result.1.toWordProtocol (h+4)) := by
  rw [proveLayerM_eq_runs]
  dsimp only [layerFromRuns]
  set prod := product w d.val claim prepareRmfeProducts
  set sampled := (writer.writeAll prod.message).sample
  set early := earlyValues w d.val claim
    (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare sampled.1)) prepareRmfeProducts
    (binaryValues prod.packs claim.point (CompStark.Sumcheck.prepare sampled.1))
  set pack := nativePackRun w d.val claim sampled.1 early sampled.2 (evaluate prod.message sampled.1)
  set pos := positionLoop pack.writer (claim.weights++Array.replicate 448 0)
    (positionFactors pack.table) pack.scale (sum (instanceWeights sampled.1)) 11
  let t : Layer := ⟨prod.message,sampled.1,pack.messages,pack.point,pos.messages,pos.point,
    pos.factors.map (·[0]!),((pos.writer.writeAll (pos.factors.map (·[0]!))).sample).1⟩
  change (t.toWordProtocol (h+4)).positionPolys =
    honestPositionRounds q d (claim.toWordProtocol (h+4)) (t.toWordProtocol (h+4))
  have ht : ∀ j : Fin 1600,pack.table.get j.val=
      linearAtPack q d (t.toWordProtocol (h+4)).point (t.toWordProtocol (h+4)).packPoint j :=
    nativePackRun_get_protocol w q hn hw d sampled.1 claim hc early sampled.2 (evaluate prod.message sampled.1)
  have hscale : eqEval (claim.toWordProtocol (h+4)).point (t.toWordProtocol (h+4)).packPoint=pack.scale :=
    (nativePackRun_scale_dimension w d.val claim sampled.1 early sampled.2
      (evaluate prod.message sampled.1) (h+5) hc).symm
  have hh := positionLoop_messages_protocol q d claim hweights (t.toWordProtocol (h+4)) pack.table ht pack.writer
  rw [hscale] at hh
  exact hh

/-- All actual native position messages equal the honest specification messages in the verifier field. -/
theorem proveLayerM_position_toField (writer : Writer) (w : SlicedWitness) {h : Nat}
    (q : Witness (h+4)) (hn : w.nLog=h+8) (hw : PreChiRefines w q) (d : Fin 12) (claim : Claim)
    (hc : claim.point.size=h+5) (hweights : claim.weights.size=1600) :
    let result := Id.run (proveLayerM (M := Id) (fun _ _ => pure ()) writer w d.val claim prepareRmfeProducts)
    (result.1.toProtocol (h+4)).positionPolys =
      honestPositionRounds q d (claim.toProtocol (h+4)) (result.1.toProtocol (h+4)) := by
  let : Fintype Ext3 := Fintype.ofFinite Ext3
  have hcard : 3<Fintype.card Ext3 := by rw [BF64.card_ext3]; decide
  let result := Id.run (proveLayerM (M := Id) (fun _ _ => pure ()) writer w d.val claim prepareRmfeProducts)
  have hh := proveLayerM_position_protocol writer w q hn hw d claim hc hweights
  dsimp only
  unfold honestPositionRounds at hh ⊢
  funext i
  change (WordExt3.ringEquiv (((result.1.toWordProtocol (h+4)).positionPolys i).1),
    fun k : Fin 2 => WordExt3.ringEquiv (((result.1.toWordProtocol (h+4)).positionPolys i).2 k)) = _
  rw [congrFun hh i]
  exact honestCompressedRounds_equiv (n := 11) (degree := 2) WordExt3.ringEquiv
    (positionSummand q d (claim.toWordProtocol (h+4)) (result.1.toWordProtocol (h+4)))
    (positionSummand q d (claim.toProtocol (h+4)) (result.1.toProtocol (h+4)))
    (positionCoordinateDegree q d (claim.toWordProtocol (h+4)) (result.1.toWordProtocol (h+4)))
    (positionCoordinateDegree q d (claim.toProtocol (h+4)) (result.1.toProtocol (h+4)))
    (positionSummand_toField q d claim result.1) hcard _ i

end CompStark.Keccak.GkrProver
