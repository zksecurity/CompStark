/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.NativePackSemantics
public import CompStark.Keccak.GkrProver.CofactorTransport
public import CompStark.Keccak.GkrProver.Completeness

/-! Equality of the complete native layer with its honest specification strategy. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak CompStark.Keccak.Gkr BF64

attribute [local irreducible] product nativePackRun positionLoop earlyValues prepareWeightMaps
  binaryValues Writer.sample Writer.writeAll instanceWeights sum evaluate eqTable transposeWeights

/-- All pack messages authored by a production layer equal its committed honest strategy. -/
theorem proveLayerM_pack_protocol (writer : Writer) (w : SlicedWitness) {h : Nat}
    (q : Witness (h+4)) (hn : w.nLog=h+8) (hw : PreChiRefines w q) (d : Fin 12) (claim : Claim)
    (hc : claim.point.size=h+5) (hbound : 1600*(2^w.nLog/64)≤USize.size) :
    let result := Id.run (proveLayerM (M := Id) (fun _ _ => pure ()) writer w d.val claim prepareRmfeProducts)
    (result.1.toWordProtocol (h+4)).packPolys = honestPackRounds q d (claim.toWordProtocol (h+4))
      (result.1.toWordProtocol (h+4)).point (result.1.toWordProtocol (h+4)).packPoint := by
  rw [proveLayerM_eq_runs]
  dsimp only [layerFromRuns]
  funext i
  exact nativePackRun_honest w q hn hw d claim hc hbound _ _ _ i

/-- Every native pack coefficient equals its honest specification coefficient in the verifier field. -/
theorem proveLayerM_pack_toField (writer : Writer) (w : SlicedWitness) {h : Nat}
    (q : Witness (h+4)) (hn : w.nLog=h+8) (hw : PreChiRefines w q) (d : Fin 12) (claim : Claim)
    (hc : claim.point.size=h+5) (hbound : 1600*(2^w.nLog/64)≤USize.size) :
    let result := Id.run (proveLayerM (M := Id) (fun _ _ => pure ()) writer w d.val claim prepareRmfeProducts)
    (result.1.toProtocol (h+4)).packPolys = honestPackRounds q d (claim.toProtocol (h+4))
      (result.1.toProtocol (h+4)).point (result.1.toProtocol (h+4)).packPoint := by
  let result := Id.run (proveLayerM (M := Id) (fun _ _ => pure ()) writer w d.val claim prepareRmfeProducts)
  have hh := proveLayerM_pack_protocol writer w q hn hw d claim hc hbound
  dsimp only
  funext i
  change (WordExt3.ringEquiv (((result.1.toWordProtocol (h+4)).packPolys i).1),
    fun k : Fin 1 => WordExt3.ringEquiv (((result.1.toWordProtocol (h+4)).packPolys i).2 k)) = _
  rw [congrFun hh i]
  exact honestPackRounds_toField q d claim result.1.s _ i

/-- Sliced product addresses fit whenever the complete sliced state allocation fits. -/
theorem productAddresses_lt (w : SlicedWitness) {h : Nat} (hn : w.nLog=h+8)
    (hbound : 1600*(2^w.nLog/64)≤USize.size) (b : Fin (2^(h+4))) (j : Fin 1600) :
    j.val*(2^w.nLog/64)+b.val/4<USize.size := by
  have hg : 2^w.nLog/64=2^(h+2) := by
    rw [hn,show h+8=(h+2)+6 by omega,pow_add]
    exact Nat.mul_div_cancel _ (by decide)
  have hb : b.val/4<2^w.nLog/64 := by
    rw [hg,Nat.div_lt_iff_lt_mul (by decide)]
    have hp : 2^(h+4)=2^(h+2)*4 := by rw [show h+4=(h+2)+2 by omega,pow_add]; rfl
    exact b.isLt.trans_eq hp
  exact (row_index_lt hb j).trans_le hbound

/-- Component equality determines a complete protocol layer. -/
theorem protocolLayer_ext {F : Type} {p : Nat} {a b : LayerTranscript F p}
    (h0 : a.product=b.product) (h1 : a.point=b.point) (h2 : a.packPolys=b.packPolys)
    (h3 : a.packPoint=b.packPoint) (h4 : a.positionPolys=b.positionPolys)
    (h5 : a.positionPoint=b.positionPoint) (h6 : a.evaluations=b.evaluations) (h7 : a.beta=b.beta) : a=b := by
  cases a; cases b
  cases h0; cases h1; cases h2; cases h3; cases h4; cases h5; cases h6; cases h7
  rfl

/-- The complete production layer equals the specification layer at its sampled challenges. -/
theorem proveLayerM_honest (writer : Writer) (w : SlicedWitness) {h : Nat}
    (q : Witness (h+4)) (hn : w.nLog=h+8) (hw : PreChiRefines w q) (d : Fin 12) (claim : Claim)
    (hc : claim.point.size=h+5) (hweights : claim.weights.size=1600)
    (hbound : 1600*(2^w.nLog/64)≤USize.size) :
    let result := Id.run (proveLayerM (M := Id) (fun _ _ => pure ()) writer w d.val claim prepareRmfeProducts)
    result.1.toProtocol (h+4) = honestLayer q d (claim.toProtocol (h+4))
      (result.1.toProtocol (h+4)).point (result.1.toProtocol (h+4)).packPoint
      (result.1.toProtocol (h+4)).positionPoint (result.1.toProtocol (h+4)).beta := by
  let result := Id.run (proveLayerM (M := Id) (fun _ _ => pure ()) writer w d.val claim prepareRmfeProducts)
  have hprod : (result.1.toProtocol (h+4)).product=honestProductMessage q d (claim.toProtocol (h+4)) := by
    funext i
    dsimp only [result]
    rw [proveLayerM_eq_runs]
    exact product_message_honest_toField w q (by omega) hw d claim hc (productAddresses_lt w hn hbound) i
  dsimp only
  apply protocolLayer_ext (a := result.1.toProtocol (h+4))
    (b := honestLayer q d (claim.toProtocol (h+4))
      (result.1.toProtocol (h+4)).point (result.1.toProtocol (h+4)).packPoint
      (result.1.toProtocol (h+4)).positionPoint (result.1.toProtocol (h+4)).beta)
  · exact hprod
  · rfl
  · exact proveLayerM_pack_toField writer w q hn hw d claim hc hbound
  · rfl
  · exact proveLayerM_position_toField writer w q hn hw d claim hc hweights
  · rfl
  · exact funext (proveLayerM_evaluations_toField writer w q hn hw d claim hc hweights)
  · rfl

end CompStark.Keccak.GkrProver
