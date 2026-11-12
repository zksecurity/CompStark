/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.QuadraticTerminal
public import CompStark.Keccak.GkrProver.InputBitSemantics

/-! Composition of the word, low-instance and slot opening runs. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr BF64
open scoped BigOperators

/-- Contract the native retained bit table against all committed-slot and bit weights. -/
def openingPerInstance (folded weights : Array W) : Array W :=
  Array.ofFn fun i : Fin 16 => Id.run do
    let mut a : W := 0
    for slot in [:64] do
      for z in [:64] do a := a+folded[(i.val+16*slot)*64+z]!*weights[slot*64+z]!
    return a

/-- Contract the native retained bit table against the four sampled low instance coordinates. -/
def openingAtInstance (folded point : Array W) : Array W :=
  let eq := eqTable point
  Array.ofFn fun offset : Fin 4096 => Id.run do
    let slot := offset.val/64
    let z := offset.val%64
    let mut a : W := 0
    for i in [:16] do a := a+eq[i]!*folded[(i+16*slot)*64+z]!
    return a

/-- Retain the three actual quadratic runs used by the production opening prover. -/
structure OpeningRuns where
  /-- Six word-slot rounds. -/
  word : QuadraticResult
  /-- Four low-instance rounds. -/
  low : QuadraticResult
  /-- Six committed-slot rounds retaining all sixty-four bit columns. -/
  slot : QuadraticResult

/-- The complete production opening calculation decomposed into its three quadratic runs. -/
def openingRuns (writer : Writer) (committed : Array UInt64) (n : Nat)
    (words wordWeights : Array W) (middle : W) (claim : Claim) : OpeningRuns :=
  let word := proveQuadratics writer words wordWeights 1 1 middle 6
  let folded := inputBits committed n (claim.point.extract 0 (claim.point.size-1))
  let weights := inputWeights claim
  let low := proveQuadratics (word.writer.write word.a[0]!) (openingPerInstance folded weights)
    claim.mu 1 1 claim.value 4
  let slot := proveQuadratics low.writer (openingAtInstance folded low.point) weights 64 low.b[0]! low.value 6
  ⟨word,low,slot⟩

/-- The complete production opening output is exactly the retained word, low-instance and slot run data. -/
theorem proveOpenings_eq_runs (writer : Writer) (committed : Array UInt64) (n : Nat)
    (words wordWeights : Array W) (middle : W) (claim : Claim) :
    proveOpenings writer committed n words wordWeights middle claim =
      let runs := openingRuns writer committed n words wordWeights middle claim
      (⟨runs.word.messages,runs.word.point,runs.word.a[0]!,
        runs.low.messages++runs.slot.messages,runs.low.point++runs.slot.point,runs.slot.a⟩,
        runs.slot.writer.writeAll runs.slot.a) := rfl

/-- Every low-instance factor is the full weighted sum of its retained committed bit columns. -/
theorem openingPerInstance_get (folded weights : Array W) (i : Fin 16) :
    (openingPerInstance folded weights)[i.val]! =
      ∑ slot : Fin 64,∑ z : Fin 64,folded[(i.val+16*slot.val)*64+z.val]!*weights[slot.val*64+z.val]! := by
  rw [getElem!_pos _ _ (by simp only [openingPerInstance,Array.size_ofFn]; exact i.isLt)]
  simp only [openingPerInstance,Array.getElem_ofFn,Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure,Std.Legacy.Range.size,Nat.sub_zero,
    Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range']
  have hsum (xs : List Nat) (term : Nat → W) (value : W) :
      xs.foldl (fun value j => value+term j) value = value+(xs.map term).sum := by
    induction xs generalizing value with
    | nil => simp only [List.foldl_nil,List.map_nil,List.sum_nil,add_zero]
    | cons j xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,add_assoc]
  simp only [hsum]
  rw [zero_add,list_range_sum,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro slot _
  rw [list_range_sum,← Fin.sum_univ_eq_sum_range]

/-- Every bit column at the sampled low instance point is its complete equality-weighted contraction. -/
theorem openingAtInstance_get (folded point : Array W) (slot z : Fin 64) :
    (openingAtInstance folded point)[64*slot.val+z.val]! =
      ∑ i : Fin 16,(eqTable point)[i.val]!*folded[(i.val+16*slot.val)*64+z.val]! := by
  have hb : 64*slot.val+z.val < 4096 := by have := slot.isLt; have := z.isLt; omega
  rw [getElem!_pos _ _ (by simp only [openingAtInstance,Array.size_ofFn]; exact hb)]
  simp only [openingAtInstance,Array.getElem_ofFn,Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure,Std.Legacy.Range.size,Nat.sub_zero,
    Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range']
  have hd : (64*slot.val+z.val)/64 = slot.val := by have := z.isLt; omega
  have hm : (64*slot.val+z.val)%64 = z.val := by have := z.isLt; omega
  rw [hd,hm]
  have hsum (xs : List Nat) (value : W) :
      xs.foldl (fun value i => value+(eqTable point)[i]!*folded[(i+16*slot.val)*64+z.val]!) value =
        value+(xs.map (fun i => (eqTable point)[i]!*folded[(i+16*slot.val)*64+z.val]!)).sum := by
    induction xs generalizing value with
    | nil => simp only [List.foldl_nil,List.map_nil,List.sum_nil,add_zero]
    | cons i xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,add_assoc]
  rw [hsum,zero_add,list_range_sum,← Fin.sum_univ_eq_sum_range]

/-- The low-instance contraction retains all sixteen RMFE input coordinates. -/
theorem openingPerInstance_size (folded weights : Array W) :
    (openingPerInstance folded weights).size = 16 := Array.size_ofFn ..

/-- Low-instance binding retains all sixty-four committed slots and their sixty-four bit columns. -/
theorem openingAtInstance_size (folded point : Array W) :
    (openingAtInstance folded point).size = 4096 := Array.size_ofFn ..

/-- The committed-slot opening has exactly one weight for every retained bit coordinate. -/
theorem inputWeights_size (claim : Claim) : (inputWeights claim).size = 4096 := Array.size_ofFn ..

attribute [local irreducible] proveQuadratics inputBits openingPerInstance openingAtInstance inputWeights

/-- A native equality-table entry uses any explicitly certified coordinate dimension. -/
theorem eqTable_get_dimension (point : Array W) (n : Nat) (hn : point.size = n) (i : Fin (2^n)) :
    (eqTable point)[i.val]! = eqWeight (fun k : Fin n => point[k.val]!) i.val := by
  subst n
  exact eqTable_get point i.val i.isLt

/-- The native three-stage opening run has the exact six, four and six transcript dimensions. -/
theorem openingRuns_lengths (writer : Writer) (committed : Array UInt64) (n : Nat)
    (words wordWeights : Array W) (middle : W) (claim : Claim) :
    let runs := openingRuns writer committed n words wordWeights middle claim
    runs.word.point.size = 6 ∧ runs.word.messages.size = 6 ∧
      runs.low.point.size = 4 ∧ runs.low.messages.size = 4 ∧
      runs.slot.point.size = 6 ∧ runs.slot.messages.size = 6 := by
  dsimp only [openingRuns]
  simp only [proveQuadratics_point_size,proveQuadratics_messages_size,and_self]

/-- The production word opening returns the full committed-word interpolation. -/
theorem proveOpenings_outputValue (writer : Writer) (committed : Array UInt64) (n : Nat)
    (words wordWeights : Array W) (middle : W) (claim : Claim)
    (hw : words.size = 64) (hweights : wordWeights.size = 64) :
    let result := (proveOpenings writer committed n words wordWeights middle claim).1
    result.outputValue = mle (fun slot : Fin 64 => words[slot.val]!)
      (fun k : Fin 6 => result.outputPoint[k.val]!) := by
  rw [proveOpenings_eq_runs]
  dsimp only [openingRuns]
  have hh := proveQuadratics_terminal writer words wordWeights 1 1 middle 6
    (by decide) (by simpa only [Nat.reducePow,Nat.mul_one] using hw) (hw.trans hweights.symm)
  have hh0 := hh.2.2.1 (0 : Fin 1)
  simp only [Fin.val_zero,Nat.mul_one,Nat.add_zero] at hh0
  convert hh0 using 1

/-- All three actual opening blocks transmit their complete honest quadratic coefficient strategies. -/
theorem openingRuns_honest (writer : Writer) (committed : Array UInt64) (n : Nat)
    (words wordWeights : Array W) (middle : W) (claim : Claim)
    (hw : words.size = 64) (hweights : wordWeights.size = 64) (hmu : claim.mu.size = 16) :
    let runs := openingRuns writer committed n words wordWeights middle claim
    let folded := inputBits committed n (claim.point.extract 0 (claim.point.size-1))
    let weights := inputWeights claim
    (fun i : Fin 6 => quadraticMessageOfArray runs.word.messages[i.val]!) =
      honestCompressedRounds (quadraticSummand words wordWeights 1 6 1)
        (quadraticSummand_degree words wordWeights 1 6 1) (fun i => runs.word.point[i.val]!) ∧
    (fun i : Fin 4 => quadraticMessageOfArray runs.low.messages[i.val]!) =
      honestCompressedRounds (quadraticSummand (openingPerInstance folded weights) claim.mu 1 4 1)
        (quadraticSummand_degree (openingPerInstance folded weights) claim.mu 1 4 1)
        (fun i => runs.low.point[i.val]!) ∧
    (fun i : Fin 6 => quadraticMessageOfArray runs.slot.messages[i.val]!) =
      honestCompressedRounds (quadraticSummand (openingAtInstance folded runs.low.point) weights 64 6 runs.low.b[0]!)
        (quadraticSummand_degree (openingAtInstance folded runs.low.point) weights 64 6 runs.low.b[0]!)
        (fun i => runs.slot.point[i.val]!) := by
  dsimp only [openingRuns]
  refine ⟨?_,?_,?_⟩
  · exact proveQuadratics_honest writer words wordWeights 1 1 middle 6 (by decide)
      (by simpa only [Nat.reducePow,Nat.mul_one] using hw) (hw.trans hweights.symm)
  · apply proveQuadratics_honest
    · decide
    · rw [openingPerInstance_size]
      rfl
    · rw [openingPerInstance_size,hmu]
  · apply proveQuadratics_honest
    · decide
    · rw [openingAtInstance_size]
      rfl
    · rw [openingAtInstance_size,inputWeights_size]

/-- Every terminal input slice is the exact low-instance and committed-slot interpolation of the retained bit table. -/
theorem openingRuns_slices (writer : Writer) (committed : Array UInt64) (n : Nat)
    (words wordWeights : Array W) (middle : W) (claim : Claim) (z : Fin 64) :
    let runs := openingRuns writer committed n words wordWeights middle claim
    let folded := inputBits committed n (claim.point.extract 0 (claim.point.size-1))
    runs.slot.a[z.val]! =
      mle (fun slot : Fin 64 =>
        mle (fun inst : Fin 16 => folded[(inst.val+16*slot.val)*64+z.val]!)
          (fun k : Fin 4 => runs.low.point[k.val]!))
        (fun k : Fin 6 => runs.slot.point[k.val]!) := by
  let runs := openingRuns writer committed n words wordWeights middle claim
  let folded := inputBits committed n (claim.point.extract 0 (claim.point.size-1))
  have ht := proveQuadratics_terminal runs.low.writer (openingAtInstance folded runs.low.point)
    (inputWeights claim) 64 runs.low.b[0]! runs.low.value 6 (by decide)
      (by rw [openingAtInstance_size]; rfl) (by rw [openingAtInstance_size,inputWeights_size])
  have hs : proveQuadratics runs.low.writer (openingAtInstance folded runs.low.point)
      (inputWeights claim) 64 runs.low.b[0]! runs.low.value 6 = runs.slot := by
    dsimp only [runs,folded,openingRuns]
  dsimp only at ht
  rw [hs] at ht
  change runs.slot.a[z.val]! = _
  rw [ht.2.2.1 z]
  apply congrArg (fun table : Fin 64 → W => mle table (fun k : Fin 6 => runs.slot.point[k.val]!))
  funext slot
  rw [Nat.mul_comm slot.val 64,openingAtInstance_get folded runs.low.point ⟨slot.val,slot.isLt⟩ z]
  unfold mle
  apply Finset.sum_congr rfl
  intro inst _
  rw [eqTable_get_dimension runs.low.point 4
    (openingRuns_lengths writer committed n words wordWeights middle claim).2.2.1 inst]

end CompStark.Keccak.GkrProver
