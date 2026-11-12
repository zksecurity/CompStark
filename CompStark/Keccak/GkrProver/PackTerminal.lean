/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.PackSemantics

/-! Exact equality factors and terminal committed factors of the complete native pack loop. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak CompStark.Keccak.Gkr BF64
open scoped BigOperators

/-- A sequence of native pack transitions preserves every already sampled coordinate and message. -/
theorem nativePackFold_prefix (w : SlicedWitness) (d : Nat) (claim : Claim) (s : W) (early : Array W)
    (indices : List Nat) (state : PackResult) :
    (∀ i,i<state.point.size → (indices.foldl (nativePackStep w d claim s early) state).point[i]! = state.point[i]!) ∧
      (∀ i,i<state.messages.size →
        (indices.foldl (nativePackStep w d claim s early) state).messages[i]! = state.messages[i]!) := by
  induction indices generalizing state with
  | nil => exact ⟨fun _ _ => rfl,fun _ _ => rfl⟩
  | cons round indices ih =>
    rw [List.foldl_cons]
    have hh := ih (nativePackStep w d claim s early state round)
    constructor
    · intro i hi
      rw [hh.1 i (by rw [(nativePackStep_lengths w d claim s early state round).1]; omega)]
      exact array_push_get_old _ _ _ hi
    · intro i hi
      rw [hh.2 i (by rw [(nativePackStep_lengths w d claim s early state round).2]; omega)]
      exact array_push_get_old _ _ _ hi

/-- Equality kernels split into their initial coordinates and final characteristic-two factor. -/
theorem eqEval_last {F : Type} [CommRing F] [CharP F 2] {n : Nat}
    (a b : Fin (n+1) → F) :
    eqEval a b = eqEval (fun i => a i.castSucc) (fun i => b i.castSucc) *
      (1+a (Fin.last n)+b (Fin.last n)) := by
  simp only [eqEval,Fin.prod_univ_castSucc]
  congr 1
  rw [CharTwo.sub_eq_add,CharTwo.sub_eq_add]
  have hz := CharTwo.add_self_eq_zero (a (Fin.last n)*b (Fin.last n))
  linear_combination hz

/-- The scale after any complete indexed prefix is exactly its evaluated equality kernel. -/
theorem nativePackPrefix_scale (w : SlicedWitness) (d : Nat) (claim : Claim) (s : W) (early : Array W)
    (writer : Writer) (value : W) (n : Nat) :
    let state := (List.range n).foldl (nativePackStep w d claim s early)
      ⟨PackedE.zeros 0,lane 1,value,#[],#[],writer⟩
    state.scale = eqEval (fun i : Fin n => claim.point[i.val]!) (fun i => state.point[i.val]!) := by
  induction n with
  | zero => simp only [List.range_zero,List.foldl_nil,eqEval,Fin.prod_univ_zero]; rfl
  | succ n ih =>
    rw [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    let state := (List.range n).foldl (nativePackStep w d claim s early)
      ⟨PackedE.zeros 0,lane 1,value,#[],#[],writer⟩
    have hs : state.point.size=n := by
      simpa only [state,List.length_range,Array.size_empty,Nat.zero_add] using
        (nativePackFold_lengths w d claim s early (List.range n)
          ⟨PackedE.zeros 0,lane 1,value,#[],#[],writer⟩).1
    let next := nativePackStep w d claim s early state n
    have hold (i : Fin n) : next.point[i.val]! = state.point[i.val]! :=
      array_push_get_old _ _ _ (by rw [hs]; exact i.isLt)
    have hstep : next.scale=state.scale*(1+claim.point[n]!+next.point[n]!) := by
      dsimp only [next,nativePackStep]
      rw [← hs,array_push_get_last]
    change next.scale = eqEval (fun i : Fin (n+1) => claim.point[i.val]!) (fun i => next.point[i.val]!)
    rw [hstep,eqEval_last]
    simp only [Fin.val_castSucc,Fin.val_last,hold]
    exact congrArg (fun scale : W => scale*(1+claim.point[n]!+next.point[n]!)) ih

/-- The full native pack run retains the exact equality kernel at all of its sampled coordinates. -/
theorem nativePackRun_scale (w : SlicedWitness) (d : Nat) (claim : Claim) (s : W) (early : Array W)
    (writer : Writer) (value : W) :
    let final := nativePackRun w d claim s early writer value
    final.scale = eqEval (fun i : Fin claim.point.size => claim.point[i.val]!) (fun i => final.point[i.val]!) :=
  nativePackPrefix_scale w d claim s early writer value claim.point.size

/-- The fourth native transition materializes the retained table at exactly its sampled four-coordinate point. -/
theorem nativePackBoundary_table (w : SlicedWitness) (d : Nat) (claim : Claim) (s : W) (early : Array W)
    (writer : Writer) (value : W) :
    let state := (List.range 4).foldl (nativePackStep w d claim s early)
      ⟨PackedE.zeros 0,lane 1,value,#[],#[],writer⟩
    state.table = packedTable w d (instanceWeights s) state.point := by
  rw [show (4 : Nat)=3+1 from rfl,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
  simp only [nativePackStep,show (3 : Nat)<4 from by decide,ite_true]

/-- Terminal retained-factor interpolation uses any explicitly identified suffix dimension. -/
theorem latePackRun_terminal_dimension (weights : Array W) (kappa : W) (point : List W)
    (state : PackResult) (n : Nat) (hn : point.length=n) (ht : state.table.size=2^n*1600) :
    let final := latePackRun weights kappa point state
    ∀ j : Fin 1600,final.table.toArray[j.val]! =
      mle (fun row : Fin (2^n) => state.table.toArray[row.val*1600+j.val]!)
        (fun k : Fin n => final.point[state.point.size+k.val]!) := by
  subst n
  exact (latePackRun_terminal weights kappa point state ht).2

/-- A retained pack suffix evaluates each committed factor at its low and high sampled pack blocks. -/
theorem latePackRun_factor_protocol (w : SlicedWitness) {h : Nat} (q : Witness (h+4))
    (hn : w.nLog=h+8) (hw : PreChiRefines w q) (d : Fin 12) (s : W) (claim : Claim)
    (suffix : List W) (hs : suffix.length=h+1) (state : PackResult)
    (hp : state.point.size=4) (ht : state.table=packedTable w d.val (instanceWeights s) state.point)
    (j : Fin 1600) :
    let final := latePackRun claim.weights (sum (instanceWeights s)) suffix state
    final.table.toArray[j.val]! =
      linearAtPack q d s (joinPoint (a := 4) (b := h+1)
        (fun i : Fin 4 => state.point[i.val]!) (fun i : Fin (h+1) => final.point[4+i.val]!)) j := by
  dsimp only
  have hsize : state.table.size=2^(h+1)*1600 := by
    rw [ht,packedTable_size,retainedRows_eq w hn,pow_succ]
    omega
  have hh := latePackRun_terminal_dimension claim.weights (sum (instanceWeights s)) suffix state (h+1) hs hsize j
  simp only [hp,ht] at hh
  rw [hh]
  exact packedTable_column_protocol w q hn hw d s state.point hp _ j

/-- The full native pack run reaches the committed factor evaluations at its actual sampled pack point. -/
theorem nativePackRun_factor_protocol (w : SlicedWitness) {h : Nat} (q : Witness (h+4))
    (hn : w.nLog=h+8) (hw : PreChiRefines w q) (d : Fin 12) (s : W) (claim : Claim)
    (hc : claim.point.size=h+5) (early : Array W) (writer : Writer) (value : W) (j : Fin 1600) :
    let final := nativePackRun w d.val claim s early writer value
    final.table.toArray[j.val]! = linearAtPack q d s (fun i : Fin (h+5) => final.point[i.val]!) j := by
  let state := (List.range 4).foldl (nativePackStep w d.val claim s early)
    ⟨PackedE.zeros 0,lane 1,value,#[],#[],writer⟩
  let suffix := (claim.point.extract 4 claim.point.size).toList
  have hs : suffix.length=h+1 := by
    simp only [suffix,Array.length_toList,Array.size_extract,Nat.min_self,hc]
    omega
  have hp : state.point.size=4 := by
    simpa only [state,List.length_range,Array.size_empty,Nat.zero_add] using
      (nativePackFold_lengths w d.val claim s early (List.range 4)
        ⟨PackedE.zeros 0,lane 1,value,#[],#[],writer⟩).1
  rw [nativePackRun_suffix w d.val claim s early writer value (by omega)]
  change (latePackRun claim.weights (sum (instanceWeights s)) suffix state).table.toArray[j.val]! = _
  rw [latePackRun_factor_protocol w q hn hw d s claim suffix hs state hp
    (nativePackBoundary_table w d.val claim s early writer value) j]
  apply congrArg (fun point : Fin (h+5) → W => linearAtPack q d s point j)
  funext i
  dsimp only [joinPoint]
  split
  · rename_i hi
    exact ((latePackRun_prefix claim.weights (sum (instanceWeights s)) suffix state).1 i.val (by omega)).symm
  · rename_i hi
    congr 1
    omega

/-- Folding every coordinate of a correctly shaped retained table leaves exactly one Keccak row. -/
theorem latePackRun_table_size (weights : Array W) (kappa : W) (point : List W) (state : PackResult)
    (ht : state.table.size=2^point.length*1600) :
    (latePackRun weights kappa point state).table.size=1600 := by
  induction point generalizing state with
  | nil => simpa only [List.length_nil,pow_zero,Nat.one_mul,latePackRun] using ht
  | cons r suffix ih =>
    rw [latePackRun]
    apply ih
    dsimp only [latePackStep]
    rw [foldPacked_size,ht,List.length_cons,pow_succ]
    omega

/-- The complete native pack run reduces its factor table to one Keccak row. -/
theorem nativePackRun_table_size (w : SlicedWitness) (hn : 8 ≤ w.nLog) (d : Nat) (claim : Claim)
    (hc : claim.point.size=w.nLog-3) (s : W) (early : Array W) (writer : Writer) (value : W) :
    (nativePackRun w d claim s early writer value).table.size=1600 := by
  rw [nativePackRun_suffix w d claim s early writer value (by omega)]
  apply latePackRun_table_size
  rw [nativePackBoundary_table,packedTable_size,Array.length_toList,packBoundary_rows w hn claim hc]

end CompStark.Keccak.GkrProver
