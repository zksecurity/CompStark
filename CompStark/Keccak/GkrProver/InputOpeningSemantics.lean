/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.OpeningSemantics
public import CompStark.Keccak.GkrProver.SumcheckBlocks

/-! Composition of the native low-instance and committed-slot opening strategies. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr CompStark.BinaryFields BF64
open scoped BigOperators

/-- The quadratic input-opening summand represented by the native retained bit and weight buffers. -/
noncomputable def inputBufferSummand (folded weights mu : Array W) (point : Fin 10 → W) : W :=
  mle (fun inst : Fin 16 => mu[inst.val]!) (inputLowPoint point) *
    ∑ z : Fin 64,mle (fun slot : Fin 64 => weights[64*slot.val+z.val]!) (inputSlotPoint point) *
      mle (fun slot : Fin 64 =>
        mle (fun inst : Fin 16 => folded[(inst.val+16*slot.val)*64+z.val]!) (inputLowPoint point))
        (inputSlotPoint point)

attribute [local irreducible] inputBits eqTable openingRuns proveQuadratics openingPerInstance openingAtInstance

/-- Concatenating the input opening's blocks retains both exact coordinate vectors. -/
theorem inputPoints_join (low : Fin 4 → W) (high : Fin 6 → W) :
    inputLowPoint (joinPoint low high) = low ∧ inputSlotPoint (joinPoint low high) = high := by
  constructor
  · funext i
    simp only [inputLowPoint,joinPoint,i.isLt,dite_true]
  · funext i
    simp only [inputSlotPoint,joinPoint,show ¬i.val+4 < 4 by omega,dite_false,Nat.add_sub_cancel]

/-- Low-instance contraction commutes with all slot-and-bit position sums. -/
theorem openingPerInstance_mle (folded weights : Array W) (point : Fin 4 → W) :
    mle (fun inst : Fin 16 => (openingPerInstance folded weights)[inst.val]!) point =
      ∑ slot : Fin 64,∑ z : Fin 64, weights[64*slot.val+z.val]! *
        mle (fun inst : Fin 16 => folded[(inst.val+16*slot.val)*64+z.val]!) point := by
  simp only [mle,openingPerInstance_get,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro slot _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro inst _
  rw [Nat.mul_comm slot.val 64]
  ring

/-- Summing out the six Boolean slot coordinates gives the native four-round low-instance summand. -/
theorem inputBufferSummand_low (folded weights mu : Array W) (point : Fin 4 → W) :
    quadraticSummand (openingPerInstance folded weights) mu 1 4 1 point =
      booleanSum (fun high : Fin 6 → W => inputBufferSummand folded weights mu (joinPoint point high)) := by
  simp only [quadraticSummand,Fin.sum_univ_one,Fin.val_zero,Nat.mul_one,Nat.add_zero,one_mul]
  trans (∑ slot : Fin 64,∑ z : Fin 64,weights[64*slot.val+z.val]! *
    mle (fun inst : Fin 16 => folded[(inst.val+16*slot.val)*64+z.val]!) point) *
      mle (fun inst : Fin 16 => mu[inst.val]!) point
  · exact congrArg (fun value : W => value*mle (fun inst : Fin 16 => mu[inst.val]!) point)
      (openingPerInstance_mle folded weights point)
  · rw [booleanSum_eq_residual _ (fun _ => 0),residualSum_zero]
    simp only [inputBufferSummand,(inputPoints_join point _).1,(inputPoints_join point _).2,mle_cubePoint]
    rw [← Finset.mul_sum,mul_comm]
    rfl

/-- The native low-point binding of every retained bit column is its complete multilinear interpolation. -/
theorem openingAtInstance_mle (folded point : Array W) (hp : point.size = 4) (slot z : Fin 64) :
    (openingAtInstance folded point)[64*slot.val+z.val]! =
      mle (fun inst : Fin 16 => folded[(inst.val+16*slot.val)*64+z.val]!)
        (fun i : Fin 4 => point[i.val]!) := by
  rw [openingAtInstance_get]
  unfold mle
  apply Finset.sum_congr rfl
  intro inst _
  rw [eqTable_get_dimension point 4 hp inst]

/-- Binding the four low coordinates gives exactly the native six-round committed-slot summand. -/
theorem inputBufferSummand_slot (folded weights mu point : Array W) (hp : point.size = 4)
    (high : Fin 6 → W) :
    inputBufferSummand folded weights mu (joinPoint (fun i : Fin 4 => point[i.val]!) high) =
      quadraticSummand (openingAtInstance folded point) weights 64 6
        (mle (fun inst : Fin 16 => mu[inst.val]!) (fun i : Fin 4 => point[i.val]!)) high := by
  simp only [inputBufferSummand,(inputPoints_join _ high).1,(inputPoints_join _ high).2,quadraticSummand]
  apply congrArg (fun value : W => mle (fun inst : Fin 16 => mu[inst.val]!)
    (fun i : Fin 4 => point[i.val]!) * value)
  apply Finset.sum_congr rfl
  intro z _
  have htable : (fun slot : Fin 64 => (openingAtInstance folded point)[slot.val*64+z.val]!) =
      (fun slot : Fin 64 => mle (fun inst : Fin 16 => folded[(inst.val+16*slot.val)*64+z.val]!)
        (fun i : Fin 4 => point[i.val]!)) := by
    funext slot
    rw [Nat.mul_comm slot.val 64,openingAtInstance_mle folded point hp slot z]
  have ht := congrArg (fun table : Fin 64 → W => mle (n := 6) table high) htable
  have hw : (fun slot : Fin 64 => weights[slot.val*64+z.val]!) =
      (fun slot : Fin 64 => weights[64*slot.val+z.val]!) := by
    funext slot
    rw [Nat.mul_comm slot.val 64]
  have hww := congrArg (fun table : Fin 64 → W => mle (n := 6) table high) hw
  exact (mul_comm _ _).trans (congrArg₂ (fun a b : W => a*b) ht.symm hww.symm)

/-- Native committed-slot weights are exactly the word-field protocol input weights. -/
theorem inputWeights_toWord {p : Nat} (claim : Claim) (shape : claim.point.size = p+1)
    (slot z : Fin 64) :
    (inputWeights claim)[64*slot.val+z.val]! = inputWeight (claim.toWordProtocol p) slot z := by
  have hd : (64*slot.val+z.val)/64 = slot.val := by omega
  have hm : (64*slot.val+z.val)%64 = z.val := by omega
  have hi : 64*slot.val+z.val < 4096 := by have := slot.isLt; have := z.isLt; omega
  rw [getElem!_pos _ _ (by simpa only [inputWeights,Array.size_ofFn] using hi)]
  simp only [inputWeights,Array.getElem_ofFn,hd,hm,inputWeight,Claim.toWordProtocol,Fin.val_last]
  by_cases hs : slot.val < 50
  · rw [ite_eq_left hs,dite_eq_left hs]
    by_cases hl : slot.val < 25
    · rw [ite_eq_left hl,ite_eq_left hl]
      simp only [Array.back!,shape,Nat.add_sub_cancel,CharTwo.sub_eq_add]
    · rw [ite_eq_right hl,ite_eq_right hl]
      simp only [Array.back!,shape,Nat.add_sub_cancel]
  · rw [ite_eq_right hs,dite_eq_right hs]

/-- Arbitrary input-opening challenges evaluate the native bit buffer as the committed protocol tensor. -/
theorem inputBits_tensor_eval (committed : Array UInt64) (claim : Claim) (p : Nat)
    (hp : 3 ≤ p) (hc : claim.point.size = p+1) (z : Fin 64) (point : Fin 10 → W) :
    mle (fun slot : Fin 64 => mle (fun inst : Fin 16 =>
      (inputBits committed (2^(p+4)) (claim.point.extract 0 (claim.point.size-1)))[(inst.val+16*slot.val)*64+z.val]!)
        (inputLowPoint point)) (inputSlotPoint point) =
      mle (inputTensorBits (committedWitness p committed) (claim.toWordProtocol p) z) point := by
  conv_rhs => rw [inputTensorBits_split]
  apply congrArg (fun table : Fin 64 → W => mle (n := 6) table (inputSlotPoint point))
  funext slot
  apply congrArg (fun table : Fin 16 → W => mle (n := 4) table (inputLowPoint point))
  funext inst
  exact inputBits_inputTensorBits committed claim p hp hc slot inst z

/-- The native opening buffers represent the protocol input summand for the actual terminal claim. -/
theorem inputBufferSummand_protocol (committed : Array UInt64) (claim : Claim) (p : Nat)
    (hp : 3 ≤ p) (hc : claim.point.size = p+1) (t : Transcript W p)
    (hclaim : nextClaim (t.layers (Fin.last 11)) = claim.toWordProtocol p) (point : Fin 10 → W) :
    inputBufferSummand (inputBits committed (2^(p+4)) (claim.point.extract 0 (claim.point.size-1)))
      (inputWeights claim) claim.mu point = inputSummand (committedWitness p committed) t point := by
  unfold inputBufferSummand inputSummand
  rw [hclaim]
  change mle (fun inst : Fin 16 => claim.mu[inst.val]!) (inputLowPoint point) * _ =
    mle (fun inst : Fin 16 => claim.mu[inst.val]!) (inputLowPoint point) * _
  apply congrArg (fun value : W => mle (fun inst : Fin 16 => claim.mu[inst.val]!) (inputLowPoint point) * value)
  apply Finset.sum_congr rfl
  intro z _
  have hw : (fun slot : Fin 64 => (inputWeights claim)[64*slot.val+z.val]!) =
      (fun slot : Fin 64 => inputWeight (claim.toWordProtocol p) slot z) := by
    funext slot
    exact inputWeights_toWord claim hc slot z
  rw [hw,inputBits_tensor_eval committed claim p hp hc z point,inputTensorBits_eval]
  rfl

/-- Arbitrary native input challenges give the verifier-field committed-bit interpolation. -/
theorem inputBits_tensor_eval_toField (committed : Array UInt64) (claim : Claim) (p : Nat)
    (hp : 3 ≤ p) (hc : claim.point.size = p+1) (z : Fin 64) (point : Fin 10 → W) :
    (mle (fun slot : Fin 64 => mle (fun inst : Fin 16 =>
      (inputBits committed (2^(p+4)) (claim.point.extract 0 (claim.point.size-1)))[(inst.val+16*slot.val)*64+z.val]!)
        (inputLowPoint point)) (inputSlotPoint point)).toField =
      mle (fun slot => mle (fun b => ZMod.castHom (dvd_refl 2) E (committedWitness p committed b slot z))
        (inputInstancePoint (claim.toProtocol p) (fun i => (point i).toField)))
        (inputSlotPoint (fun i => (point i).toField)) := by
  rw [inputBits_tensor_eval committed claim p hp hc z point,inputTensorBits_eval,mle_toField (n := 6)]
  simp only [mle_toField (n := p+4),inputInstancePoint_toField]
  rfl

/-- The native retained input buffers evaluate to the protocol input summand over the verifier's field. -/
theorem inputBufferSummand_protocol_toField (committed : Array UInt64) (claim : Claim) (p : Nat)
    (hp : 3 ≤ p) (hc : claim.point.size = p+1) (t : Transcript E p)
    (hclaim : nextClaim (t.layers (Fin.last 11)) = claim.toProtocol p) (point : Fin 10 → W) :
    (inputBufferSummand (inputBits committed (2^(p+4)) (claim.point.extract 0 (claim.point.size-1)))
      (inputWeights claim) claim.mu point).toField =
      inputSummand (committedWitness p committed) t (fun i => (point i).toField) := by
  unfold inputBufferSummand inputSummand
  rw [hclaim]
  have hmul (a b : W) : (a*b).toField = a.toField*b.toField := WordExt3.ringEquiv.map_mul a b
  rw [hmul,mle_toField (n := 4)]
  change mle (fun inst : Fin 16 => claim.mu[inst.val]!.toField) (inputLowPoint (fun i => (point i).toField)) * _ =
    mle (fun inst : Fin 16 => claim.mu[inst.val]!.toField) (inputLowPoint (fun i => (point i).toField)) * _
  apply congrArg (fun value : E =>
    mle (fun inst : Fin 16 => claim.mu[inst.val]!.toField) (inputLowPoint (fun i => (point i).toField)) * value)
  change WordExt3.ringEquiv (∑ z : Fin 64,_) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  change WordExt3.toField ((_ : W)*_) = _
  rw [hmul,mle_toField (n := 6),inputBits_tensor_eval_toField committed claim p hp hc z point]
  apply congrArg (fun value : E => value *
    mle (fun slot => mle (fun b => ZMod.castHom (dvd_refl 2) E (committedWitness p committed b slot z))
      (inputInstancePoint (claim.toProtocol p) (fun i => (point i).toField)))
        (inputSlotPoint (fun i => (point i).toField)))
  apply congrArg (fun table : Fin 64 → E => mle (n := 6) table (inputSlotPoint (fun i => (point i).toField)))
  funext slot
  exact inputWeights_toField claim hc slot z

end CompStark.Keccak.GkrProver
