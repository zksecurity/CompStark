/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Algorithms derived from succinctlabs/flock (flock-core), MIT OR Apache-2.0.
Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum.
Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang.
-/
module
public import CompStark.Pcs.ChallengeFold
public import Mathlib.Data.List.OfFn

/-! A fused adjacent restriction and next-message pass for later WHIR rounds. -/
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
@[expose] public section
namespace CompStark.Pcs
open BF64

/-- Two adjacent restricted witness values and their corresponding weights. -/
structure FoldMessagePair where
  /-- Low witness endpoint of the next round. -/
  tableLow : WordExt3
  /-- High witness endpoint of the next round. -/
  tableHigh : WordExt3
  /-- Low weight endpoint of the next round. -/
  weightLow : WordExt3
  /-- High weight endpoint of the next round. -/
  weightHigh : WordExt3

/-- Retained restricted tables and the next two compressed message coefficients. -/
structure FoldMessageState where
  /-- Restricted witness coordinates in adjacent-pair order. -/
  table : Array WordExt3
  /-- Restricted weight coordinates in adjacent-pair order. -/
  weight : Array WordExt3
  /-- Accumulated constant coefficient. -/
  constant : WordExt3
  /-- Accumulated quadratic coefficient. -/
  quadratic : WordExt3

/-- Consume one pair of restricted coordinates and author its message contributions. -/
@[inline] def FoldMessageState.push (state : FoldMessageState) (pair : FoldMessagePair) : FoldMessageState :=
  ⟨(state.table.push pair.tableLow).push pair.tableHigh,
    (state.weight.push pair.weightLow).push pair.weightHigh,
    WordExt3.add state.constant (roundProduct pair.tableLow pair.weightLow),
    WordExt3.add state.quadratic (roundProduct (WordExt3.add pair.tableLow pair.tableHigh)
      (WordExt3.add pair.weightLow pair.weightHigh))⟩

/-- The ordered witness pair associated with one fused message block. -/
def FoldMessagePair.table (pair : FoldMessagePair) : List WordExt3 := [pair.tableLow,pair.tableHigh]

/-- The ordered weight pair associated with one fused message block. -/
def FoldMessagePair.weight (pair : FoldMessagePair) : List WordExt3 := [pair.weightLow,pair.weightHigh]

/-- Fused accumulation preserves both ordered output lists and both finite message sums. -/
theorem foldMessageState_refines {α : Type} (values : α → FoldMessagePair) (xs : List α) (state : FoldMessageState) :
    let result := xs.foldl (fun state i => state.push (values i)) state
    result.table.toList = state.table.toList ++ xs.flatMap (fun i => (values i).table) ∧
    result.weight.toList = state.weight.toList ++ xs.flatMap (fun i => (values i).weight) ∧
    result.constant.toField = state.constant.toField +
      (xs.map fun i => (values i).tableLow.toField*(values i).weightLow.toField).sum ∧
    result.quadratic.toField = state.quadratic.toField +
      (xs.map fun i => ((values i).tableLow.toField+(values i).tableHigh.toField)*
        ((values i).weightLow.toField+(values i).weightHigh.toField)).sum := by
  induction xs generalizing state with
  | nil => simp only [List.foldl_nil,List.flatMap_nil,List.map_nil,List.sum_nil,List.append_nil,add_zero,and_self]
  | cons i xs ih =>
    dsimp only
    rw [List.foldl_cons]
    have rest := ih (state.push (values i))
    simp only [FoldMessageState.push,Array.toList_push,WordExt3.toField_add,roundProduct_eq,
      WordExt3.toField_mul,List.flatMap_cons,List.map_cons,List.sum_cons,
      FoldMessagePair.table,FoldMessagePair.weight] at rest ⊢
    rcases rest with ⟨table,weight,constant,quadratic⟩
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using table
    · simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using weight
    · rw [constant]
      exact add_assoc _ _ _
    · rw [quadratic]
      exact add_assoc _ _ _

/-- Restrict one adjacent pair without materializing an intermediate output array. -/
@[inline] def foldedCoordinate (r : Sumcheck.Prepared) (rows : Nat)
    (values : Vector WordExt3 (4*rows)) (i : Fin (2*rows)) : WordExt3 :=
  have bound : 2*i.val+1 < 4*rows := by have := i.isLt; omega
  r.interpolate values[2*i.val] values[2*i.val+1]

/-- Restrict four input coordinates while they are resident for the following message pair. -/
@[inline] def foldMessagePair (r : Sumcheck.Prepared) (rows : Nat)
    (table weight : Vector WordExt3 (4*rows)) (i : Fin rows) : FoldMessagePair :=
  let low : Fin (2*rows) := ⟨2*i.val,by have := i.isLt; omega⟩
  let high : Fin (2*rows) := ⟨2*i.val+1,by have := i.isLt; omega⟩
  ⟨foldedCoordinate r rows table low,foldedCoordinate r rows table high,
    foldedCoordinate r rows weight low,foldedCoordinate r rows weight high⟩

/-- Fold adjacent input pairs and author the next message in one ordered pass. -/
def foldMessage (r : WordExt3) (rows : Nat) (table weight : Vector WordExt3 (4*rows)) : FoldMessageState :=
  let shared := Sumcheck.prepare r
  (List.finRange rows).foldl (fun state i => state.push (foldMessagePair shared rows table weight i))
    ⟨Array.emptyWithCapacity (2*rows),Array.emptyWithCapacity (2*rows),0,0⟩

/-- Flattening consecutive pairs preserves the row-major coordinate order. -/
theorem pairedList {α : Type} (rows : Nat) (f : Fin (2*rows) → α) :
    (List.finRange rows).flatMap (fun i =>
      [f ⟨2*i.val,by have := i.isLt; omega⟩,f ⟨2*i.val+1,by have := i.isLt; omega⟩]) = List.ofFn f := by
  rw [List.ofFn_mul',List.finRange,List.flatMap_def,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  simp only [List.ofFn_succ,List.ofFn_zero]
  rfl

/-- The fused pass writes exactly the adjacent witness restriction. -/
theorem foldMessage_table (r : WordExt3) (rows : Nat) (table weight : Vector WordExt3 (4*rows)) :
    (foldMessage r rows table weight).table =
      (Vector.ofFn (foldedCoordinate (Sumcheck.prepare r) rows table)).toArray := by
  apply Array.toList_inj.mp
  have same := (foldMessageState_refines (foldMessagePair (Sumcheck.prepare r) rows table weight)
    (List.finRange rows) ⟨Array.emptyWithCapacity (2*rows),Array.emptyWithCapacity (2*rows),0,0⟩).1
  simpa only [foldMessage,Array.emptyWithCapacity_eq,Array.toList_empty,List.nil_append,foldMessagePair,
    FoldMessagePair.table,Vector.toArray_ofFn,Array.toList_ofFn,pairedList] using same

/-- The fused pass writes exactly the adjacent weight restriction. -/
theorem foldMessage_weight (r : WordExt3) (rows : Nat) (table weight : Vector WordExt3 (4*rows)) :
    (foldMessage r rows table weight).weight =
      (Vector.ofFn (foldedCoordinate (Sumcheck.prepare r) rows weight)).toArray := by
  apply Array.toList_inj.mp
  have same := (foldMessageState_refines (foldMessagePair (Sumcheck.prepare r) rows table weight)
    (List.finRange rows) ⟨Array.emptyWithCapacity (2*rows),Array.emptyWithCapacity (2*rows),0,0⟩).2.1
  simpa only [foldMessage,Array.emptyWithCapacity_eq,Array.toList_empty,List.nil_append,foldMessagePair,
    FoldMessagePair.weight,Vector.toArray_ofFn,Array.toList_ofFn,pairedList] using same

/-- The fused constant coefficient is the exact sum of freshly restricted low products. -/
theorem foldMessage_constant (r : WordExt3) (rows : Nat) (table weight : Vector WordExt3 (4*rows)) :
    (foldMessage r rows table weight).constant.toField =
      ∑ i : Fin rows, (foldMessagePair (Sumcheck.prepare r) rows table weight i).tableLow.toField *
        (foldMessagePair (Sumcheck.prepare r) rows table weight i).weightLow.toField := by
  have same := (foldMessageState_refines (foldMessagePair (Sumcheck.prepare r) rows table weight)
    (List.finRange rows) ⟨Array.emptyWithCapacity (2*rows),Array.emptyWithCapacity (2*rows),0,0⟩).2.2.1
  simpa only [foldMessage,List.finRange,List.map_ofFn,Function.comp_apply,List.sum_ofFn,
    show (0 : WordExt3).toField = (0 : Ext3) from rfl,zero_add] using same

/-- The fused quadratic coefficient is the exact sum of restricted endpoint differences. -/
theorem foldMessage_quadratic (r : WordExt3) (rows : Nat) (table weight : Vector WordExt3 (4*rows)) :
    (foldMessage r rows table weight).quadratic.toField =
      ∑ i : Fin rows,
        ((foldMessagePair (Sumcheck.prepare r) rows table weight i).tableLow.toField+
          (foldMessagePair (Sumcheck.prepare r) rows table weight i).tableHigh.toField)*
        ((foldMessagePair (Sumcheck.prepare r) rows table weight i).weightLow.toField+
          (foldMessagePair (Sumcheck.prepare r) rows table weight i).weightHigh.toField) := by
  have same := (foldMessageState_refines (foldMessagePair (Sumcheck.prepare r) rows table weight)
    (List.finRange rows) ⟨Array.emptyWithCapacity (2*rows),Array.emptyWithCapacity (2*rows),0,0⟩).2.2.2
  simpa only [foldMessage,List.finRange,List.map_ofFn,Function.comp_apply,List.sum_ofFn,
    show (0 : WordExt3).toField = (0 : Ext3) from rfl,zero_add] using same

/-- Adjacent folding in vector form has the coordinates consumed by the fused pass. -/
theorem foldedCoordinate_eq (r : WordExt3) (rows : Nat) (table : Vector WordExt3 (4*rows)) :
    Vector.ofFn (foldedCoordinate (Sumcheck.prepare r) rows table) =
      (Sumcheck.fold (Sumcheck.prepare r) (2*rows) 1
        (Vector.ofFn fun i => table[i.val]'(by have := i.isLt; omega))).cast (by omega) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_cast,Vector.getElem_ofFn,Sumcheck.fold,foldedCoordinate,
    Nat.mul_one,Nat.div_one,Nat.mod_one,Nat.add_zero]

/-- Fused next-message coefficients agree with the complete separate message pass. -/
theorem foldMessage_coefficients (r : WordExt3) (rows : Nat) (table weight : Vector WordExt3 (4*rows)) :
    #v[(foldMessage r rows table weight).constant,(foldMessage r rows table weight).quadratic] =
      roundCoefficients rows 1
        (Vector.ofFn fun i => (foldMessage r rows table weight).table[i.val]!)
        (Vector.ofFn fun i => (foldMessage r rows table weight).weight[i.val]!) := by
  apply Vector.ext
  intro i hi
  have index : i = 0 ∨ i = 1 := by omega
  rcases index with rfl | rfl
  all_goals apply WordExt3.toField_injective
  · change (foldMessage r rows table weight).constant.toField = _
    rw [roundCoefficients_constant,foldMessage_constant]
    apply Fintype.sum_equiv (finCongr (Nat.mul_one rows).symm)
    intro q
    have low : 2*q.val < 2*rows := by have := q.isLt; omega
    simp only [foldMessage_table,foldMessage_weight,Fin.getElem_fin,Vector.getElem_ofFn,
      Vector.toArray_ofFn,foldMessagePair,roundLow,Nat.mul_one,Nat.div_one,Nat.mod_one,Nat.add_zero,finCongr_apply,Fin.val_cast]
    rw [getElem!_pos _ _ (by simpa only [Array.size_ofFn] using low),
      getElem!_pos _ _ (by simpa only [Array.size_ofFn] using low)]
    simp only [Array.getElem_ofFn]
  · change (foldMessage r rows table weight).quadratic.toField = _
    rw [roundCoefficients_quadratic,foldMessage_quadratic]
    apply Fintype.sum_equiv (finCongr (Nat.mul_one rows).symm)
    intro q
    have low : 2*q.val < 2*rows := by have := q.isLt; omega
    have high : 2*q.val+1 < 2*rows := by have := q.isLt; omega
    simp only [foldMessage_table,foldMessage_weight,Fin.getElem_fin,Vector.getElem_ofFn,
      Vector.toArray_ofFn,foldMessagePair,roundLow,roundHigh,Nat.mul_one,Nat.div_one,Nat.mod_one,Nat.add_zero,finCongr_apply,Fin.val_cast]
    rw [getElem!_pos _ _ (by simpa only [Array.size_ofFn] using low),
      getElem!_pos _ _ (by simpa only [Array.size_ofFn] using high),
      getElem!_pos _ _ (by simpa only [Array.size_ofFn] using low),
      getElem!_pos _ _ (by simpa only [Array.size_ofFn] using high)]
    simp only [Array.getElem_ofFn]

/-- Four direct challenge restrictions for a short fused round. -/
@[inline] def foldMessagePairDirect (r : WordExt3) (rows : Nat)
    (table weight : Vector WordExt3 (4*rows)) (i : Fin rows) : FoldMessagePair :=
  let restrict := fun values : Vector WordExt3 (4*rows) => fun k : Nat => fun bound : 2*k+1 < 4*rows =>
    let a := values[2*k]
    WordExt3.add a (roundProduct r (WordExt3.add a values[2*k+1]))
  ⟨restrict table (2*i.val) (by have := i.isLt; omega),
    restrict table (2*i.val+1) (by have := i.isLt; omega),
    restrict weight (2*i.val) (by have := i.isLt; omega),
    restrict weight (2*i.val+1) (by have := i.isLt; omega)⟩

/-- Direct challenge products equal all four prepared restrictions. -/
theorem foldMessagePairDirect_eq (r : WordExt3) (rows : Nat)
    (table weight : Vector WordExt3 (4*rows)) (i : Fin rows) :
    foldMessagePairDirect r rows table weight i = foldMessagePair (Sumcheck.prepare r) rows table weight i := by
  simp only [foldMessagePairDirect,foldMessagePair,foldedCoordinate,Sumcheck.Prepared.interpolate,
    Sumcheck.prepared_mul_eq,roundProduct_eq]

/-- Fused restriction and message traversal without a materialized index list. -/
def foldMessageNative (r : WordExt3) (rows : Nat) (table weight : Vector WordExt3 (4*rows)) : FoldMessageState :=
  let initial : FoldMessageState :=
    ⟨Array.emptyWithCapacity (2*rows),Array.emptyWithCapacity (2*rows),0,0⟩
  if 2*rows ≤ 256 then
    Fin.foldl rows (fun state i => state.push (foldMessagePairDirect r rows table weight i)) initial
  else
    let shared := Sumcheck.prepare r
    Fin.foldl rows (fun state i => state.push (foldMessagePair shared rows table weight i)) initial

/-- The native fused traversal retains both output arrays and both compressed coefficients. -/
@[csimp] theorem foldMessage_code : @foldMessage = @foldMessageNative := by
  funext r rows table weight
  unfold foldMessageNative
  split
  · simp only [foldMessagePairDirect_eq,Fin.foldl_eq_foldl_finRange]
    rfl
  · rw [Fin.foldl_eq_foldl_finRange]
    rfl

end CompStark.Pcs
