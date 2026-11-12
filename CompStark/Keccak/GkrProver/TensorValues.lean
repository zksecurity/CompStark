/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.TensorBlocks

/-! Structural accumulation semantics of the production early-pack tensor. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak BF64
open scoped BigOperators

/-- Add a complete native tensor block at its equality-table weight. -/
def addTensorBlock (values : Array W) (weight : W) (sums : FixedWords 243) : Array W :=
  (List.range 81).foldl (fun values q =>
    if ternaryBinary[q]! = 0 then
      values.set! q (values[q]!+weight*tripleValue sums q) else values) values

/-- The initial tensor copies the retained product values at exactly the finite endpoints. -/
def initialTensorValues (binary : Array W) : Array W :=
  Array.ofFn fun q : Fin 81 =>
    let (b,hi) := ternaryPlan[q.val]!
    if hi = 81 then binary[b]! else lane 0

/-- A conditional yielding step is one yielding step with the conditional state. -/
theorem ite_pure_yield {A : Type} (p : Prop) [Decidable p] (a b : A) :
    (if p then pure (.yield a) else pure (.yield b) : Id (ForInStep A)) =
      pure (.yield (if p then a else b)) := by
  split <;> rfl

/-- The production tensor loop is the structural fold of its complete position blocks. -/
theorem earlyValues_eq_blocks (w : SlicedWitness) (d : Nat) (claim : Claim)
    (maps : FixedWords (1600*6*256*3)) (products : RmfeProducts) (binary : Array W) :
    earlyValues w d claim maps products binary =
      (List.range 2).foldl (fun values m =>
        (List.range (2^(w.nLog-4)/16)).foldl (fun values block =>
          addTensorBlock values
            (eqTable (claim.point.extract 4 claim.point.size))[m*(2^(w.nLog-4)/16)+block]!
            (tensorBlock maps (mixedEmbeddings w.layers[12*(m+1)-d]!
              (2^w.nLog/64) (16*block)) products)) values)
        (initialTensorValues binary) := by
  simp (disch := first | exact Membership.mem.upper ‹_› | omega) only
    [earlyValues,earlyPosition_eq_column]
  simp only [ite_pure_yield,forIn'_eq_forIn,Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure,Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range']
  rfl

/-- A fold of pointwise additions preserves the array length. -/
theorem foldl_set_add_size (indices : List Nat) (term : Nat → W) (values : Array W) :
    (indices.foldl (fun out k => out.set! k (out[k]!+term k)) values).size = values.size := by
  induction indices generalizing values with
  | nil => rfl
  | cons k ks ih => rw [List.foldl_cons,ih,Array.size_set!]

/-- Distinct pointwise additions change exactly the listed array coordinates. -/
theorem foldl_set_add_get (indices : List Nat) (hnd : indices.Nodup) (term : Nat → W)
    (values : Array W) (i : Nat) (hi : i < values.size) :
    (indices.foldl (fun out k => out.set! k (out[k]!+term k)) values)[i]! =
      values[i]!+if i ∈ indices then term i else 0 := by
  induction indices generalizing values with
  | nil => rw [List.foldl_nil,ite_eq_right List.not_mem_nil,add_zero]
  | cons k ks ih =>
    obtain ⟨hk,hks⟩ := List.nodup_cons.mp hnd
    rw [List.foldl_cons,ih hks _ (by rw [Array.size_set!]; exact hi)]
    by_cases he : k = i
    · subst k
      rw [Array.getElem!_set!_self _ _ _ hi,ite_eq_right hk,
        ite_eq_left List.mem_cons_self,add_zero]
    · rw [Array.getElem!_set!_ne _ _ _ _ he]
      by_cases hm : i ∈ ks
      · rw [ite_eq_left hm,ite_eq_left (List.mem_cons_of_mem k hm)]
      · rw [ite_eq_right hm,ite_eq_right (by
          simp only [List.mem_cons,hm,or_false]; exact Ne.symm he),add_zero]

/-- A complete tensor block update preserves the eighty-one tensor entries. -/
theorem addTensorBlock_size (values : Array W) (weight : W) (sums : FixedWords 243) :
    (addTensorBlock values weight sums).size = values.size := by
  unfold addTensorBlock
  generalize List.range 81 = qs
  induction qs generalizing values with
  | nil => rfl
  | cons q qs ih =>
    rw [List.foldl_cons,ih]
    split
    · exact Array.size_set! ..
    · rfl

/-- A complete block adds precisely the selected nonbinary endpoint at every tensor coordinate. -/
theorem addTensorBlock_get (values : Array W) (hv : values.size = 81)
    (weight : W) (sums : FixedWords 243) (q : Fin 81) :
    (addTensorBlock values weight sums)[q.val]! =
      values[q.val]!+if ternaryBinary[q.val]! = 0 then weight*tripleValue sums q.val else 0 := by
  unfold addTensorBlock
  have hf (xs : List Nat) (out : Array W) :
      (xs.foldl (fun out k => if ternaryBinary[k]! = 0 then
        out.set! k (out[k]!+weight*tripleValue sums k) else out) out) =
      ((xs.filter fun k => ternaryBinary[k]! = 0).foldl
        (fun out k => out.set! k (out[k]!+weight*tripleValue sums k)) out) := by
    induction xs generalizing out with
    | nil => rfl
    | cons k ks ih =>
      rw [List.foldl_cons,List.filter_cons]
      by_cases hk : ternaryBinary[k]! = 0
      · simp only [hk,ite_true,decide_true,ih,List.foldl_cons]
      · simp only [hk,ite_false,decide_false,Bool.false_eq_true,ih]
  rw [hf,foldl_set_add_get _ ((List.nodup_range (n := 81)).filter _) _ _ q.val (by rw [hv]; exact q.isLt)]
  have hm : (q.val ∈ (List.range 81).filter (fun k => ternaryBinary[k]! = 0)) ↔
      ternaryBinary[q.val]! = 0 := by
    simp only [List.mem_filter,List.mem_range,q.isLt,true_and,decide_eq_true_eq]
  simp only [hm]

/-- Array-valued folds retain their dimension and accumulate one selected coordinate exactly. -/
theorem foldl_array_value_sum {A S : Type} (view : S → Array W) (step : S → A → S)
    (term : A → W) {n : Nat} (i : Fin n)
    (hsize : ∀ state a, (view state).size = n → (view (step state a)).size = n)
    (hget : ∀ state a, (view state).size = n →
      (view (step state a))[i.val]! = (view state)[i.val]!+term a)
    (xs : List A) (state : S) (hs : (view state).size = n) :
    (view (xs.foldl step state)).size = n ∧
      (view (xs.foldl step state))[i.val]! = (view state)[i.val]!+(xs.map term).sum := by
  induction xs generalizing state with
  | nil => exact ⟨hs,(add_zero _).symm⟩
  | cons a xs ih =>
    rw [List.foldl_cons]
    obtain ⟨hlen,hval⟩ := ih (step state a) (hsize state a hs)
    refine ⟨hlen,?_⟩
    rw [hval,hget state a hs,List.map_cons,List.sum_cons,add_assoc]

/-- Every production early-pack tensor coordinate is the exact equality-weighted block sum. -/
theorem earlyValues_blocks_get (w : SlicedWitness) (d : Nat) (claim : Claim)
    (maps : FixedWords (1600*6*256*3)) (products : RmfeProducts) (binary : Array W) (q : Fin 81) :
    (earlyValues w d claim maps products binary).size = 81 ∧
    (earlyValues w d claim maps products binary)[q.val]! =
      (initialTensorValues binary)[q.val]! +
        ∑ m ∈ Finset.range 2, ∑ b ∈ Finset.range (2^(w.nLog-4)/16),
          if ternaryBinary[q.val]! = 0 then
            (eqTable (claim.point.extract 4 claim.point.size))[m*(2^(w.nLog-4)/16)+b]! *
              tripleValue (tensorBlock maps (mixedEmbeddings w.layers[12*(m+1)-d]!
                (2^w.nLog/64) (16*b)) products) q.val else 0 := by
  let term (m b : Nat) := if ternaryBinary[q.val]! = 0 then
    (eqTable (claim.point.extract 4 claim.point.size))[m*(2^(w.nLog-4)/16)+b]! *
      tripleValue (tensorBlock maps (mixedEmbeddings w.layers[12*(m+1)-d]!
        (2^w.nLog/64) (16*b)) products) q.val else 0
  let step (m : Nat) (values : Array W) (b : Nat) :=
    addTensorBlock values
      (eqTable (claim.point.extract 4 claim.point.size))[m*(2^(w.nLog-4)/16)+b]!
      (tensorBlock maps (mixedEmbeddings w.layers[12*(m+1)-d]! (2^w.nLog/64) (16*b)) products)
  let outer (values : Array W) (m : Nat) := (List.range (2^(w.nLog-4)/16)).foldl (step m) values
  have hinner (m : Nat) (values : Array W) (hv : values.size = 81) :
      (outer values m).size = 81 ∧ (outer values m)[q.val]! =
        values[q.val]!+∑ b ∈ Finset.range (2^(w.nLog-4)/16),term m b := by
    have h := foldl_array_value_sum id (step m) (term m) q
      (by intro v b hv; exact (addTensorBlock_size ..).trans hv)
      (by intro v b hv; exact addTensorBlock_get v hv _ _ q)
      (List.range (2^(w.nLog-4)/16)) values hv
    rw [list_range_sum] at h
    exact h
  have h := foldl_array_value_sum id outer
    (fun m => ∑ b ∈ Finset.range (2^(w.nLog-4)/16),term m b) q
    (by intro v m hv; exact (hinner m v hv).1)
    (by intro v m hv; exact (hinner m v hv).2)
    (List.range 2) (initialTensorValues binary) (Array.size_ofFn ..)
  rw [earlyValues_eq_blocks]
  rw [list_range_sum] at h
  exact h

/-- The byte flag is one exactly at the finite tensor endpoints. -/
theorem ternaryBinary_get (q : Fin 81) :
    ternaryBinary[q.val]! = if (ternaryPlan[q.val]!).2 = 81 then 1 else 0 := by
  rw [getElem!_pos _ _ (by simpa only [ternaryBinary,ByteArray.size,Array.size_ofFn] using q.isLt)]
  change (Array.ofFn (fun q : Fin 81 => if (ternaryPlan[q.val]!).2 = 81 then (1 : UInt8) else 0))[q.val] = _
  rw [Array.getElem_ofFn]

section
attribute [local irreducible] earlyValues prepareWeightMaps prepareRmfeProducts tensorBlock
  mixedEmbeddings ternaryPlan

/-- The complete production tensor uses retained finite values and exact lifted products at infinity. -/
theorem earlyValues_get (w : SlicedWitness) (d : Nat) (claim : Claim) (s : W)
    (binary : Array W) (q : Fin 81) :
    (earlyValues w d claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
      prepareRmfeProducts binary)[q.val]! =
      if (ternaryPlan[q.val]!).2 = 81 then binary[(ternaryPlan[q.val]!).1]! else
        ∑ m ∈ Finset.range 2, ∑ b ∈ Finset.range (2^(w.nLog-4)/16),
          (eqTable (claim.point.extract 4 claim.point.size))[m*(2^(w.nLog-4)/16)+b]! *
            ∑ j : Fin 1600, tensorColumnProduct claim.weights s w.layers[12*(m+1)-d]!
              (2^w.nLog/64) (16*b) j q := by
  rw [(earlyValues_blocks_get w d claim _ _ binary q).2]
  have hi : (initialTensorValues binary)[q.val]! =
      if (ternaryPlan[q.val]!).2 = 81 then binary[(ternaryPlan[q.val]!).1]! else 0 := by
    unfold initialTensorValues
    rw [getElem!_pos _ _ (by rw [Array.size_ofFn]; exact q.isLt),Array.getElem_ofFn]
    generalize ternaryPlan[q.val]! = plan
    rcases plan with ⟨b,hi⟩
    rfl
  rw [hi,ternaryBinary_get]
  by_cases hf : (ternaryPlan[q.val]!).2 = 81
  · simp only [hf,ite_true,show (1 : UInt8) ≠ 0 from by decide,ite_false,Finset.sum_const_zero,add_zero]
  · simp only [hf,ite_false,ite_true,zero_add]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro b _
    rw [tensorBlock_get,ternaryBinary_get,ite_eq_right hf,ite_eq_left (by decide)]

end

end CompStark.Keccak.GkrProver
