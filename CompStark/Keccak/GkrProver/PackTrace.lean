/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.LayerTrace

/-! Remaining-sum invariants at the production early-to-retained pack transition. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr BF64

attribute [local irreducible] earlyValues prepareWeightMaps prepareRmfeProducts product binaryValues
  packedTable eqTable Writer.sample Writer.writeAll

/-- Every production pack transition after the fourth coordinate is its certified retained-table transition. -/
theorem nativePackStep_late (w : SlicedWitness) (d : Nat) (claim : Claim) (s : W) (early : Array W)
    (state : PackResult) (i : Nat) (hi : 4 ≤ i) :
    nativePackStep w d claim s early state i =
      latePackStep claim.weights (claim.point.extract (i+1) claim.point.size)
        (sum (instanceWeights s)) claim.point[i]! state := by
  simp only [nativePackStep,latePackStep,ite_eq_right (show ¬i < 4 by omega),
    ite_eq_right (show i ≠ 3 by omega),ite_eq_left hi]

/-- The fourth actual production transition establishes the exact retained-table remaining sum. -/
theorem nativePackStep_boundary (w : SlicedWitness) (hn : 8 ≤ w.nLog) (d : Nat) (claim : Claim)
    (hc : claim.point.size = w.nLog-3) (hbound : 1600*(2^w.nLog/64) ≤ USize.size)
    (s : W) (state : PackResult) (hp : state.point.size = 3) :
    let early := earlyValues w d claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
      prepareRmfeProducts (binaryValues (product w d claim prepareRmfeProducts).packs claim.point
        (CompStark.Sumcheck.prepare s))
    let next := nativePackStep w d claim s early state 3
    next.table.size = 2^(claim.point.extract 4 claim.point.size).toList.length*1600 ∧
      next.value = packRemainingValue claim.weights (sum (instanceWeights s))
        (claim.point.extract 4 claim.point.size).toList next := by
  dsimp only
  let early := earlyValues w d claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
    prepareRmfeProducts (binaryValues (product w d claim prepareRmfeProducts).packs claim.point
      (CompStark.Sumcheck.prepare s))
  let coefficients := (earlyRound early claim.point state.point).map (state.scale*·)
  let r := ((state.writer.writeAll #[coefficients[1]!,coefficients[2]!]).sample).1
  have ht : (nativePackStep w d claim s early state 3).table =
      packedTable w d (instanceWeights s) (state.point.push r) := by
    simp only [nativePackStep,show (3 : Nat) < 4 from by decide,ite_true]
    rfl
  constructor
  · rw [ht,packedTable_size,Array.length_toList,packBoundary_rows w hn claim hc]
  · have hh := packBoundary_running_sum w hn d claim hc hbound s state.point hp state.scale r
    dsimp only [nativePackStep,packRemainingValue]
    simp only [show (3 : Nat) < 4 from by decide,ite_true]
    convert hh using 1
    simp only [Array.getElem!_toList]
    congr 1

/-- A structural retained-pack suffix is its exact indexed transition fold. -/
theorem latePackRun_eq_fold (weights : Array W) (kappa : W) (point : List W) (state : PackResult) :
    latePackRun weights kappa point state =
      (List.range point.length).foldl (fun state i =>
        latePackStep weights (point.drop (i+1)).toArray kappa point[i]! state) state := by
  induction point generalizing state with
  | nil => rfl
  | cons entering suffix ih =>
    rw [List.length_cons,List.range_succ_eq_map,List.foldl_cons,List.foldl_map]
    simp only [Nat.zero_add,List.drop_succ_cons,List.drop_zero,List.getElem!_cons_zero]
    rw [latePackRun,ih]
    rfl

/-- All production pack transitions after the four early coordinates form the certified retained-table suffix run. -/
theorem nativePackRun_suffix (w : SlicedWitness) (d : Nat) (claim : Claim) (s : W) (early : Array W)
    (writer : Writer) (value : W) (hc : 4 ≤ claim.point.size) :
    nativePackRun w d claim s early writer value =
      latePackRun claim.weights (sum (instanceWeights s)) (claim.point.extract 4 claim.point.size).toList
        ((List.range 4).foldl (nativePackStep w d claim s early)
          ⟨PackedE.zeros 0,lane 1,value,#[],#[],writer⟩) := by
  have hrange : List.range claim.point.size =
      List.range 4++(List.range (claim.point.size-4)).map (4+·) := by
    conv_lhs => rw [show claim.point.size = 4+(claim.point.size-4) by omega]
    exact List.range_add
  rw [nativePackRun,hrange,List.foldl_append,List.foldl_map,latePackRun_eq_fold]
  simp only [Array.length_toList,Array.size_extract,Nat.min_self]
  apply List.foldl_rel (r := Eq) rfl
  intro i hi a b hab
  subst b
  have hi : i < claim.point.size-4 := List.mem_range.mp hi
  rw [nativePackStep_late w d claim s early a (4+i) (by omega)]
  have htail : (((claim.point.extract 4 claim.point.size).toList).drop (i+1)).toArray =
      claim.point.extract (4+i+1) claim.point.size := by
    rw [List.toArray_drop,Array.toArray_toList,Array.extract_extract]
    simp only [Array.size_extract,Nat.min_self]
    rw [show min (4+(claim.point.size-4)) claim.point.size = claim.point.size by omega]
    congr 1
  have hget : ((claim.point.extract 4 claim.point.size).toList)[i]! = claim.point[4+i]! := by
    rw [Array.getElem!_toList,getElem!_pos _ _ (by
      simp only [Array.size_extract,Nat.min_self]; exact hi),Array.getElem_extract,
      ← getElem!_pos claim.point (4+i) (by omega)]
  rw [htail,hget]

/-- The fourth production pack transition initializes the complete retained suffix invariant from the actual early prefix. -/
theorem nativePackRun_boundary (w : SlicedWitness) (hn : 8 ≤ w.nLog) (d : Nat) (claim : Claim)
    (hc : claim.point.size = w.nLog-3) (hbound : 1600*(2^w.nLog/64) ≤ USize.size)
    (s : W) (writer : Writer) (value : W) :
    let early := earlyValues w d claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
      prepareRmfeProducts (binaryValues (product w d claim prepareRmfeProducts).packs claim.point
        (CompStark.Sumcheck.prepare s))
    let boundary := (List.range 4).foldl (nativePackStep w d claim s early)
      ⟨PackedE.zeros 0,lane 1,value,#[],#[],writer⟩
    boundary.table.size = 2^(claim.point.extract 4 claim.point.size).toList.length*1600 ∧
      boundary.value = packRemainingValue claim.weights (sum (instanceWeights s))
        (claim.point.extract 4 claim.point.size).toList boundary := by
  dsimp only
  rw [show (4 : Nat) = 3+1 from rfl,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
  apply nativePackStep_boundary w hn d claim hc hbound s
  let early := earlyValues w d claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
    prepareRmfeProducts (binaryValues (product w d claim prepareRmfeProducts).packs claim.point
      (CompStark.Sumcheck.prepare s))
  have hh := (nativePackFold_lengths w d claim s early (List.range 3)
    ⟨PackedE.zeros 0,lane 1,value,#[],#[],writer⟩).1
  simpa only [early,Array.size_empty,List.length_range,Nat.zero_add] using hh

/-- The actual complete production pack run reaches one row and preserves the exact terminal chi claim. -/
theorem nativePackRun_invariant (w : SlicedWitness) (hn : 8 ≤ w.nLog) (d : Nat) (claim : Claim)
    (hc : claim.point.size = w.nLog-3) (hbound : 1600*(2^w.nLog/64) ≤ USize.size)
    (s : W) (writer : Writer) (value : W) :
    let early := earlyValues w d claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
      prepareRmfeProducts (binaryValues (product w d claim prepareRmfeProducts).packs claim.point
        (CompStark.Sumcheck.prepare s))
    let final := nativePackRun w d claim s early writer value
    final.table.size = 1600 ∧ final.value = packRemainingValue claim.weights (sum (instanceWeights s)) [] final := by
  dsimp only
  rw [nativePackRun_suffix w d claim s _ writer value (by omega)]
  have hh := nativePackRun_boundary w hn d claim hc hbound s writer value
  exact latePackRun_invariant claim.weights (sum (instanceWeights s)) _ _ hh.1 hh.2

/-- The retained part of the actual production pack transcript is its honest quadratic-cofactor strategy. -/
theorem nativePackRun_late_honest (w : SlicedWitness) (hn : 8 ≤ w.nLog) (d : Nat) (claim : Claim)
    (hc : claim.point.size = w.nLog-3) (hbound : 1600*(2^w.nLog/64) ≤ USize.size)
    (s : W) (writer : Writer) (value : W) (i : Fin (claim.point.extract 4 claim.point.size).toList.length) :
    let early := earlyValues w d claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
      prepareRmfeProducts (binaryValues (product w d claim prepareRmfeProducts).packs claim.point
        (CompStark.Sumcheck.prepare s))
    let boundary := (List.range 4).foldl (nativePackStep w d claim s early)
      ⟨PackedE.zeros 0,lane 1,value,#[],#[],writer⟩
    let final := nativePackRun w d claim s early writer value
    cofactorMessageOfArray final.messages[4+i.val]! =
      honestCofactorRounds
        (packTableCofactor boundary.table claim.weights (claim.point.extract 4 claim.point.size).toList.length
          boundary.scale (sum (instanceWeights s)))
        (packTableCofactor_degree boundary.table claim.weights (claim.point.extract 4 claim.point.size).toList.length
          boundary.scale (sum (instanceWeights s)))
        (fun k => (claim.point.extract 4 claim.point.size).toList[k.val]!)
        (fun k => final.point[4+k.val]!) i := by
  dsimp only
  rw [nativePackRun_suffix w d claim s _ writer value (by omega)]
  let early := earlyValues w d claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
    prepareRmfeProducts (binaryValues (product w d claim prepareRmfeProducts).packs claim.point
      (CompStark.Sumcheck.prepare s))
  let boundary := (List.range 4).foldl (nativePackStep w d claim s early)
    ⟨PackedE.zeros 0,lane 1,value,#[],#[],writer⟩
  have hb := nativePackRun_boundary w hn d claim hc hbound s writer value
  have hl := nativePackFold_lengths w d claim s early (List.range 4)
    ⟨PackedE.zeros 0,lane 1,value,#[],#[],writer⟩
  have hpoint : boundary.point.size = 4 := by
    simpa only [boundary,List.length_range,Array.size_empty,Nat.zero_add] using hl.1
  have hmessage : boundary.messages.size = 4 := by
    simpa only [boundary,List.length_range,Array.size_empty,Nat.zero_add] using hl.2
  have hh := latePackRun_honest claim.weights (sum (instanceWeights s))
    (claim.point.extract 4 claim.point.size).toList boundary hb.1 hb.2 i
  simpa only [hpoint,hmessage] using hh

end CompStark.Keccak.GkrProver
