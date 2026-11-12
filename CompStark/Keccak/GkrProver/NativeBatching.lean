/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.NativeSetup
public import CompStark.Keccak.GkrProver.TransposeSemantics

/-! Native beta batching agrees with the protocol's complete next claim. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr BF64

/-- Component equality determines a protocol claim. -/
theorem protocolClaim_ext {F : Type} {p : Nat} {a b : CompStark.Keccak.Gkr.Claim F p}
    (hv : a.value=b.value) (hm : a.mu=b.mu) (hp : a.point=b.point) (hw : a.weights=b.weights) : a=b := by
  cases a
  cases b
  cases hv
  cases hm
  cases hp
  cases hw
  rfl

/-- The actual position loop retains exactly eleven sampled coordinates. -/
theorem positionLoop_point_size (writer : Writer) (weights : Array W) (factors : Array (Array W))
    (scale kappa : W) (n : Nat) :
    (positionLoop writer weights factors scale kappa n).point.size=n := by
  rw [positionLoop_eq_run]
  simpa only [Array.size_empty,Nat.zero_add] using
    (positionRun_lengths scale kappa ⟨weights,factors,#[],#[],writer⟩ n).1

attribute [local irreducible] product nativePackRun positionLoop earlyValues prepareWeightMaps
  binaryValues Writer.sample Writer.writeAll instanceWeights sum evaluate eqTable transposeWeights

/-- Native equality weights and sparse transposition retain the protocol's beta-batched position weights. -/
theorem batchWeights_toField (point : Array W) (hp : point.size=11) (beta : W) (j : Fin 1600) :
    (transposeWeights (Array.ofFn fun k : Fin 1600 =>
      (eqTable point)[k.val]!+beta*(eqTable point)[shift k.val 4]!+
        (beta*beta)*(eqTable point)[shift k.val 3]!))[j.val]!.toField =
      linearTranspose (fun k => eqWeight (fun i : Fin 11 => point[i.val]!.toField) k.val+
        beta.toField*eqWeight (fun i : Fin 11 => point[i.val]!.toField) (along k 4).val+
        beta.toField^2*eqWeight (fun i : Fin 11 => point[i.val]!.toField) (along k 3).val) j := by
  rw [transposeWeights_toField]
  apply congrArg (fun weights : Fin 1600 → CompStark.BinaryFields.E => linearTranspose weights j)
  funext k
  rw [ofFn_get!]
  change WordExt3.ringEquiv (_+_+_) = _
  rw [map_add,map_add,map_mul,map_mul,map_mul]
  have heq (i : Fin 1600) : (eqTable point)[i.val]!.toField =
      eqWeight (fun j : Fin 11 => point[j.val]!.toField) i.val :=
    eqTable_dimension_toField point 11 hp ⟨i.val,by omega⟩
  change (eqTable point)[k.val]!.toField+beta.toField*(eqTable point)[shift k.val 4]!.toField+
    (beta.toField*beta.toField)*(eqTable point)[shift k.val 3]!.toField = _
  rw [shift_eq,shift_eq,heq k,heq (along k 4),heq (along k 3),pow_two]

/-- A dummy layer supplies defaulting lookup only in intermediate structural-loop statements. -/
local instance : Inhabited Layer := ⟨⟨#[],0,#[],#[],#[],#[],#[],0⟩⟩

/-- Beta batching in an actual production layer is the protocol's next claim in every component. -/
theorem proveLayerM_nextClaim (writer : Writer) (w : SlicedWitness) (d : Nat) (claim : Claim)
    (products : RmfeProducts) (p : Nat) :
    let result := Id.run (proveLayerM (M := Id) (fun _ _ => pure ()) writer w d claim products)
    result.2.1.toProtocol p = nextClaim (result.1.toProtocol p) := by
  rw [proveLayerM_eq_runs]
  dsimp only [layerFromRuns]
  set prod := product w d claim products
  set sampled := (writer.writeAll prod.message).sample
  set early := earlyValues w d claim
    (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare sampled.1)) products
    (binaryValues prod.packs claim.point (CompStark.Sumcheck.prepare sampled.1))
  set pack := nativePackRun w d claim sampled.1 early sampled.2 (evaluate prod.message sampled.1)
  set factors := Array.ofFn (fun k : Fin 3 => Array.ofFn fun j : Fin 2048 =>
    if j.val<1600 then pack.table.get (shift j.val k.val) else lane 0)
  set pos := positionLoop pack.writer (claim.weights++Array.replicate 448 0) factors pack.scale (sum (instanceWeights sampled.1)) 11
  set beta := (pos.writer.writeAll (pos.factors.map (·[0]!))).sample
  have hpos : pos.point.size=11 := positionLoop_point_size ..
  apply protocolClaim_ext
  · change ((_+beta.1*(_+beta.1*_)) : W).toField = _
    simp only [Layer.toProtocol,nextClaim]
    change WordExt3.ringEquiv (_+beta.1*(_+beta.1*_)) = _
    rw [map_add,map_mul,map_add,map_mul]
    change (pos.factors.map (·[0]!))[0]!.toField+
      beta.1.toField*((pos.factors.map (·[0]!))[1]!.toField+
        beta.1.toField*(pos.factors.map (·[0]!))[2]!.toField) =
      (pos.factors.map (·[0]!))[0]!.toField+
        beta.1.toField*(pos.factors.map (·[0]!))[1]!.toField+
        beta.1.toField^2*(pos.factors.map (·[0]!))[2]!.toField
    ring
  · funext i
    change (instanceWeights sampled.1)[i.val]!.toField = muAt sampled.1.toField i
    exact (congrArg WordExt3.toField
      ((instanceWeights_eq sampled.1 i).trans (mu_eq sampled.1 i).symm)).trans (mu_toField sampled.1 i)
  · rfl
  · funext j
    exact batchWeights_toField pos.point hpos beta.1 j

/-- Mutable state carried by the complete twelve-layer native loop. -/
abbrev NativeLayerState := Claim × Writer × Array Layer

/-- One native layer transition in the full prover's mutable-state order. -/
def nativeLayerStateStep (w : SlicedWitness) (products : RmfeProducts)
    (state : NativeLayerState) (d : Nat) : NativeLayerState :=
  let result := proveLayerM (M := Id) (fun _ _ => pure ()) state.2.1 w d state.1 products
  (result.2.1,result.2.2,state.2.2.push result.1)

/-- One full-loop transition stores the exact next claim of its newly appended layer. -/
theorem nativeLayerStateStep_next (w : SlicedWitness) (products : RmfeProducts)
    (state : NativeLayerState) (d p : Nat) :
    let final := nativeLayerStateStep w products state d
    final.1.toProtocol p = nextClaim (final.2.2.back!.toProtocol p) := by
  dsimp only [nativeLayerStateStep]
  rw [Array.back!_push]
  exact proveLayerM_nextClaim state.2.1 w d state.1 products p

/-- A nonempty native layer fold retains the exact next claim of its final authored layer. -/
theorem nativeLayerFold_next (w : SlicedWitness) (products : RmfeProducts)
    (indices : List Nat) (state : NativeLayerState) (p : Nat) (hn : indices≠[]) :
    let final := indices.foldl (nativeLayerStateStep w products) state
    final.1.toProtocol p = nextClaim (final.2.2.back!.toProtocol p) := by
  induction indices generalizing state with
  | nil => exact False.elim (hn rfl)
  | cons d indices ih =>
    rw [List.foldl_cons]
    by_cases hnil : indices=[]
    · subst indices
      exact nativeLayerStateStep_next w products state d p
    · exact ih _ hnil

attribute [local irreducible] proveLayerM proveOpenings Writer.sampleMany outputWords dot prepareRmfeProducts

/-- The actual full native reduction retains exactly the next claim of its twelfth protocol layer. -/
theorem prove_finalClaim_next (writer : Writer) (w : SlicedWitness) (committed : Array UInt64)
    (batch output : Array W) (p : Nat) :
    let result := prove writer w committed batch output
    result.finalClaim.toProtocol p =
      nextClaim ((result.toProtocol p (prove_layers_size ..)).layers (Fin.last 11)) := by
  have hlast (result : Reduction) (height : result.layers.size=12) :
      (result.toProtocol p height).layers (Fin.last 11) = result.layers.back!.toProtocol p := by
    simp only [Reduction.toProtocol,Fin.val_last,Array.back!,height]
    rw [getElem!_pos _ _ (by rw [height]; decide)]
  dsimp only
  rw [hlast]
  have hbind {A B : Type} (a : Id A) (f : A → Id B) : a >>= f = f a := rfl
  simp only [prove,proveM,Std.Legacy.Range.forIn_eq_forIn_range',
    hbind,List.forIn_pure_yield_eq_foldl,Id.run_pure]
  apply nativeLayerFold_next w prepareRmfeProducts
  decide

/-- All four terminal-opening obligations hold for the actual complete native prover. -/
theorem prove_openings_honest (writer : Writer) (w : SlicedWitness) (committed : Array UInt64)
    (batch output : Array W) (p : Nat) (hp : 3≤p) (hn : w.nLog=p+4) (hb : batch.size=p+4)
    (hc : committed.size/(2^(p+4))=64) :
    let result := prove writer w committed batch output
    let t := result.toProtocol p (prove_layers_size ..)
    t.openings.outputPolys = honestWordRounds (CompStark.BinaryFields.ofK CompStark.BinaryFields.g)
        (committedWitness p committed) t ∧
      t.openings.outputValue = mle
        (middleWord (CompStark.BinaryFields.ofK CompStark.BinaryFields.g) (committedWitness p committed) t)
        t.openings.outputPoint ∧
      t.openings.inputPolys = honestInputRounds (committedWitness p committed) t ∧
      ∀ z,t.openings.slices z =
        mle (fun slot => mle (fun b => ZMod.castHom (dvd_refl 2) CompStark.BinaryFields.E
          (committedWitness p committed b slot z))
          (inputInstancePoint (nextClaim (t.layers (Fin.last 11))) t.openings.inputPoint))
          (inputSlotPoint t.openings.inputPoint) := by
  let result := prove writer w committed batch output
  have hs := prove_setup writer w committed batch output
  have hshape := prove_finalClaim_shape writer w committed batch output p hb
  obtain ⟨finalWriter,hopening⟩ := prove_openings_eq writer w committed batch output
  have hcall : result.openings =
      (proveOpenings finalWriter committed (2^(p+4)) (outputWords committed (2^(p+4)) result.batchPoint)
        (wordOpeningWeights result.segment result.lanes) result.middle result.finalClaim).1 := by
    rw [hs.1]
    simpa only [hn] using hopening
  exact Reduction.openings_honest result p hp (prove_layers_size ..) finalWriter committed
    ((congrArg Array.size hs.1).trans hb) hs.2.1 hc hshape.1 hshape.2.1 hcall
    (prove_finalClaim_next writer w committed batch output p).symm

end CompStark.Keccak.GkrProver
