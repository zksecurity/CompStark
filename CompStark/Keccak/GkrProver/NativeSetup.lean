/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.NativeOpening
public import CompStark.Keccak.GkrProver.LayerTrace

/-! Shape preservation and retained setup of the complete native prover. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64 CompStark.Keccak.Gkr CompStark.BinaryFields
open scoped BigOperators

attribute [local irreducible] Writer.sample

/-- Sampling a challenge vector retains exactly its requested number of coordinates. -/
theorem Writer.sampleMany_size (writer : Writer) (n : Nat) :
    (writer.sampleMany n).1.size = n := by
  simp only [Writer.sampleMany,Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure,Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  let step (state : Writer × Array W) (_ : Nat) :=
    let sampled := state.1.sample
    (sampled.2,state.2.push sampled.1)
  have hsize (indices : List Nat) (state : Writer × Array W) :
      (indices.foldl step state).2.size = state.2.size+indices.length := by
    induction indices generalizing state with
    | nil => simp only [List.foldl_nil,List.length_nil,Nat.add_zero]
    | cons i indices ih =>
      rw [List.foldl_cons,ih]
      change (state.2.push _).size+indices.length = _
      rw [Array.size_push,List.length_cons]
      omega
  change ((List.range' 0 n).foldl step _).2.size = n
  rw [hsize]
  simp only [Array.size_empty,List.length_range',Nat.zero_add]

attribute [local irreducible] nativePackRun positionLoop product earlyValues binaryValues
  prepareWeightMaps eqTable transposeWeights

/-- One production layer preserves the pack dimension and resets the sixteen RMFE weights. -/
theorem proveLayerM_claim_shape (writer : Writer) (w : SlicedWitness) (d : Nat) (claim : Claim)
    (products : RmfeProducts) :
    let next := (Id.run (proveLayerM (M := Id) (fun _ _ => pure ()) writer w d claim products)).2.1
    next.point.size = claim.point.size ∧ next.mu.size = 16 ∧ next.weights.size = 1600 := by
  rw [proveLayerM_eq_runs]
  dsimp only [layerFromRuns]
  refine ⟨(nativePackRun_lengths ..).1,?_,?_⟩
  · exact Array.size_ofFn ..
  · unfold transposeWeights
    exact Array.size_ofFn ..

attribute [local irreducible] proveLayerM proveOpenings Writer.sampleMany outputWords dot prepareRmfeProducts

/-- The complete production prover retains the supplied batch, five lane challenges, and the middle-word evaluation. -/
theorem prove_setup (writer : Writer) (w : SlicedWitness) (committed : Array UInt64)
    (batch output : Array W) :
    let result := prove writer w committed batch output
    result.batchPoint = batch ∧ result.lanes.size = 5 ∧
      result.middle = dot (outputWords committed (2^w.nLog) batch)
        (wordOpeningWeights result.segment result.lanes) := by
  have hbind {A B : Type} (a : Id A) (f : A → Id B) : a >>= f = f a := rfl
  simp only [prove,proveM,wordOpeningWeights,Std.Legacy.Range.forIn_eq_forIn_range',
    hbind,List.forIn_pure_yield_eq_foldl,Id.run_pure]
  exact ⟨True.intro,Writer.sampleMany_size _ 5,True.intro⟩

/-- The terminal production claim has the entering pack dimension and the fixed RMFE and position dimensions. -/
theorem prove_finalClaim_shape (writer : Writer) (w : SlicedWitness) (committed : Array UInt64)
    (batch output : Array W) (p : Nat) (hb : batch.size = p+4) :
    let result := prove writer w committed batch output
    result.finalClaim.point.size = p+1 ∧ result.finalClaim.mu.size = 16 ∧
      result.finalClaim.weights.size = 1600 := by
  have hbind {A B : Type} (a : Id A) (f : A → Id B) : a >>= f = f a := rfl
  simp only [prove,proveM,Std.Legacy.Range.forIn_eq_forIn_range',
    hbind,List.forIn_pure_yield_eq_foldl,Id.run_pure]
  let step (state : Claim × Writer × Array Layer) (d : Nat) :=
    let result := proveLayerM (M := Id) (fun _ _ => pure ()) state.2.1 w d state.1 prepareRmfeProducts
    (result.2.1,result.2.2,state.2.2.push result.1)
  have hshape (indices : List Nat) (state : Claim × Writer × Array Layer)
      (h : state.1.point.size = p+1 ∧ state.1.mu.size = 16 ∧ state.1.weights.size = 1600) :
      let final := (indices.foldl step state).1
      final.point.size = p+1 ∧ final.mu.size = 16 ∧ final.weights.size = 1600 := by
    induction indices generalizing state with
    | nil => exact h
    | cons d indices ih =>
      rw [List.foldl_cons]
      apply ih
      have hs := proveLayerM_claim_shape state.2.1 w d state.1 prepareRmfeProducts
      exact ⟨hs.1.trans h.1,hs.2⟩
  apply hshape
  refine ⟨?_,?_,Array.size_ofFn ..⟩
  · simp only [Array.size_push,Array.size_extract,Nat.min_self,hb]
    omega
  · rw [eqTable_size,Array.size_extract,hb]
    rfl

/-- The native dot-product accumulator is its complete mathematical scalar sum. -/
theorem dot_eq_sum (a b : Array W) :
    dot a b = ∑ i ∈ Finset.range a.size, a[i]!*b[i]! := by
  simp only [dot,Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure,Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range']
  have hh := foldl_value_sum id (fun state i => state+a[i]!*b[i]!)
    (fun i => a[i]!*b[i]!) (fun _ _ => rfl) (List.range a.size) 0
  simpa only [id_eq,list_range_sum,zero_add] using hh

/-- The actual native middle scalar satisfies the protocol's committed-middle claim. -/
theorem prove_middle (writer : Writer) (w : SlicedWitness) (committed : Array UInt64)
    (batch output : Array W) (p : Nat) (hn : w.nLog=p+4) (hb : batch.size=p+4)
    (hc : committed.size/(2^(p+4))=64) :
    MiddleHolds (ofK g) (committedWitness p committed)
      ((prove writer w committed batch output).toProtocol p (prove_layers_size ..)) := by
  let result := prove writer w committed batch output
  let t := result.toProtocol p (prove_layers_size ..)
  have hs := prove_setup writer w committed batch output
  have hwords := outputWords_size committed (2^(p+4)) batch
  rw [hc] at hwords
  have hsum : result.middle.toField = ∑ slot : Fin 64,
      (if 25 ≤ slot.val ∧ slot.val<50 then (1-t.segment)*eqWeight t.lanePoint (slot.val-25) else 0)*
        middleWord (ofK g) (committedWitness p committed) t slot := by
    rw [hs.2.2,hn,dot_eq_sum,hwords]
    change WordExt3.ringEquiv (∑ i ∈ Finset.range 64,_)=_
    rw [map_sum,← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro slot _
    change WordExt3.ringEquiv (_*_)=_
    rw [map_mul]
    change (outputWords committed (2^(p+4)) batch)[slot.val]!.toField *
      (wordOpeningWeights result.segment result.lanes)[slot.val]!.toField = _
    rw [wordOpeningWeights_toField _ _ hs.2.1,
      outputWords_middleWord committed batch p hb hc t (by
        change (fun i : Fin (p+4) => result.batchPoint[i.val]!.toField) = _
        rw [hs.1])]
    exact mul_comm _ _
  have hh := word_start_identity (ofK g) (committedWitness p committed) t (fun _ => 0)
  rw [residualSum_zero] at hh
  simp only [wordSummand,mle_cubePoint] at hh
  exact hsum.trans hh

end CompStark.Keccak.GkrProver
