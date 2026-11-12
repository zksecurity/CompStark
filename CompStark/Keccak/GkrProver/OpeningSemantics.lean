/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.OpeningTrace
public import CompStark.Keccak.Gkr.OpeningAlgebra
public import CompStark.Keccak.GkrProver.FieldTransport

/-! Committed-witness semantics of the native terminal input slices. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr CompStark.BinaryFields BF64
open scoped BigOperators

/-- Interpret a native running claim over the word field, retaining the verifier's dimensions. -/
def Claim.toWordProtocol (claim : Claim) (p : Nat) : CompStark.Keccak.Gkr.Claim W p where
  value := claim.value
  mu i := claim.mu[i.val]!
  point i := claim.point[i.val]!
  weights j := claim.weights[j.val]!

/-- The complete committed word block, including spare slots, interpreted as a protocol bit witness. -/
def committedWitness (p : Nat) (committed : Array UInt64) : Witness p :=
  fun b slot z => sliceBit committed[slot.val*2^(p+4)+b.val]! z

/-- Casting a sliced committed bit gives its exact zero-or-one word-field value. -/
theorem sliceBit_cast (word : UInt64) (z : Fin 64) :
    ZMod.castHom (dvd_refl 2) W (sliceBit word z) =
      if word.toNat.testBit z.val then 1 else 0 := by
  unfold sliceBit
  change (ZMod.castHom (dvd_refl 2) W)
    (if word.toNat.testBit z.val then (1 : ZMod 2) else 0) = _
  split <;> simp only [map_one,map_zero]

/-- Removing the segment coordinate leaves exactly the claim's high instance coordinates. -/
theorem claimHighPoint_size (claim : Claim) (p : Nat) (hc : claim.point.size = p+1) :
    (claim.point.extract 0 (claim.point.size-1)).size = p := by
  rw [Array.size_extract,hc]
  omega

/-- Every retained high-instance coordinate is the same coordinate of the entering claim. -/
theorem claimHighPoint_get (claim : Claim) (p : Nat) (hc : claim.point.size = p+1) (i : Fin p) :
    (claim.point.extract 0 (claim.point.size-1))[i.val]! = claim.point[i.val]! := by
  rw [getElem!_pos _ _ (by rw [claimHighPoint_size claim p hc]; exact i.isLt),Array.getElem_extract]
  simpa only [Nat.zero_add] using
    (getElem!_pos claim.point i.val (by rw [hc]; have := i.isLt; omega)).symm

/-- The high-instance opening table contains an exact number of complete eight-instance byte groups. -/
theorem inputBits_group_shape (p : Nat) (hp : 3 ≤ p) :
    2^p = 8*(2^(p+4)/128) := by
  rw [show p+4 = (p-3)+7 by omega,pow_add]
  rw [show 2^7 = (128 : Nat) from rfl,Nat.mul_div_cancel _ (by decide)]
  rw [show p = (p-3)+3 by omega,pow_add]
  norm_num
  omega

attribute [local irreducible] inputBits eqTable proveQuadratics openingRuns

/-- Every native retained input cell is exactly the protocol's committed tensor-bit table entry. -/
theorem inputBits_inputTensorBits (committed : Array UInt64) (claim : Claim) (p : Nat)
    (hp : 3 ≤ p) (hc : claim.point.size = p+1) (slot : Fin 64) (inst : Fin 16) (z : Fin 64) :
    (inputBits committed (2^(p+4)) (claim.point.extract 0 (claim.point.size-1)))[(inst.val+16*slot.val)*64+z.val]! =
      inputTensorBits (committedWitness p committed) (claim.toWordProtocol p) z
        ⟨inst.val+16*slot.val,by have := inst.isLt; have := slot.isLt; omega⟩ := by
  rw [inputBits_weighted committed _ _ (by
    rw [claimHighPoint_size claim p hc]
    exact inputBits_group_shape p hp)]
  rw [claimHighPoint_size claim p hc,← Fin.sum_univ_eq_sum_range]
  unfold inputTensorBits mle
  have hd : (inst.val+16*slot.val)/16 = slot.val := by have := inst.isLt; omega
  have hm : (inst.val+16*slot.val)%16 = inst.val := by have := inst.isLt; omega
  simp only [hd,hm,committedWitness,Claim.toWordProtocol,packInstance,sliceBit_cast]
  apply Finset.sum_congr rfl
  intro row _
  rw [eqTable_get_dimension _ p (claimHighPoint_size claim p hc) row]
  simp only [claimHighPoint_get claim p hc]
  rw [show slot.val*2^(p+4)+16*row.val+inst.val =
    slot.val*2^(p+4)+(inst.val+16*row.val) by omega]
  rfl

/-- Low and slot opening coordinates are read from their exact concatenated wire point. -/
theorem openingRuns_points (writer : Writer) (committed : Array UInt64) (n : Nat)
    (words wordWeights : Array W) (middle : W) (claim : Claim) :
    let runs := openingRuns writer committed n words wordWeights middle claim
    let point : Fin 10 → W := fun i => (runs.low.point++runs.slot.point)[i.val]!
    inputLowPoint point = (fun i : Fin 4 => runs.low.point[i.val]!) ∧
      inputSlotPoint point = (fun i : Fin 6 => runs.slot.point[i.val]!) := by
  let runs := openingRuns writer committed n words wordWeights middle claim
  have hl : runs.low.point.size = 4 :=
    (openingRuns_lengths writer committed n words wordWeights middle claim).2.2.1
  have hs : runs.slot.point.size = 6 :=
    (openingRuns_lengths writer committed n words wordWeights middle claim).2.2.2.2.1
  constructor
  · funext i
    dsimp only [inputLowPoint]
    rw [getElem!_pos _ _ (by rw [Array.size_append,hl,hs]; have := i.isLt; omega),
      Array.getElem_append_left (by rw [hl]; exact i.isLt)]
    exact (getElem!_pos _ _ (by rw [hl]; exact i.isLt)).symm
  · funext i
    dsimp only [inputSlotPoint]
    rw [getElem!_pos _ _ (by rw [Array.size_append,hl,hs]; have := i.isLt; omega),
      Array.getElem_append_right (by rw [hl]; omega)]
    change runs.slot.point[i.val+4-runs.low.point.size] = runs.slot.point[i.val]!
    simp only [hl,Nat.add_sub_cancel]
    exact (getElem!_pos runs.slot.point i.val (by rw [hs]; exact i.isLt)).symm

/-- Splitting the committed tensor separates its four low instance coordinates from its six slots. -/
theorem inputTensorBits_split (q : Witness p) (claim : CompStark.Keccak.Gkr.Claim W p)
    (z : Fin 64) (point : Fin 10 → W) :
    mle (inputTensorBits q claim z) point =
      mle (fun slot : Fin 64 => mle (fun inst : Fin 16 =>
        inputTensorBits q claim z ⟨inst.val+16*slot.val,by have := inst.isLt; have := slot.isLt; omega⟩)
          (inputLowPoint point)) (inputSlotPoint point) := by
  let table := inputTensorBits q claim z
  have h := mle_split (a := 4) (b := 6)
    (fun inst : Fin 16 => fun slot : Fin 64 =>
      table ⟨inst.val+16*slot.val,by have := inst.isLt; have := slot.isLt; omega⟩) point
  have ht : (fun w : Fin 1024 => table ⟨w.val%16+16*(w.val/16),by omega⟩) = table := by
    funext w
    exact congrArg table (Fin.ext (Nat.mod_add_div w.val 16))
  change mle (fun w : Fin 1024 => table ⟨w.val%16+16*(w.val/16),by omega⟩) point = _ at h
  rw [ht] at h
  exact h

/-- Every native terminal slice is the specification's committed tensor-bit interpolation. -/
theorem openingRuns_tensor_slices (writer : Writer) (committed : Array UInt64)
    (words wordWeights : Array W) (middle : W) (claim : Claim) (p : Nat)
    (hp : 3 ≤ p) (hc : claim.point.size = p+1) (z : Fin 64) :
    let runs := openingRuns writer committed (2^(p+4)) words wordWeights middle claim
    let point : Fin 10 → W := fun i => (runs.low.point++runs.slot.point)[i.val]!
    runs.slot.a[z.val]! = mle (inputTensorBits (committedWitness p committed)
      (claim.toWordProtocol p) z) point := by
  dsimp only
  rw [openingRuns_slices]
  conv_rhs => rw [inputTensorBits_split]
  have hpoints := openingRuns_points writer committed (2^(p+4)) words wordWeights middle claim
  rw [hpoints.1,hpoints.2]
  apply congrArg (fun table : Fin 64 → W => mle (n := 6) table
    (fun i => (openingRuns writer committed (2^(p+4)) words wordWeights middle claim).slot.point[i.val]!))
  funext slot
  apply congrArg (fun table : Fin 16 → W => mle (n := 4) table
    (fun i => (openingRuns writer committed (2^(p+4)) words wordWeights middle claim).low.point[i.val]!))
  funext inst
  exact inputBits_inputTensorBits committed claim p hp hc slot inst z

/-- All native input-opening outputs are the specification's full committed instance-and-slot evaluations. -/
theorem proveOpenings_input_slices (writer : Writer) (committed : Array UInt64)
    (words wordWeights : Array W) (middle : W) (claim : Claim) (p : Nat)
    (hp : 3 ≤ p) (hc : claim.point.size = p+1) (z : Fin 64) :
    let result := (proveOpenings writer committed (2^(p+4)) words wordWeights middle claim).1
    let point : Fin 10 → W := fun i => result.inputPoint[i.val]!
    result.slices[z.val]! =
      mle (fun slot => mle (fun b => ZMod.castHom (dvd_refl 2) W (committedWitness p committed b slot z))
        (inputInstancePoint (claim.toWordProtocol p) point)) (inputSlotPoint point) := by
  rw [proveOpenings_eq_runs]
  exact (openingRuns_tensor_slices writer committed words wordWeights middle claim p hp hc z).trans
    (inputTensorBits_eval _ _ _ _)

/-- Native multilinear evaluations transport to the verifier's field at any certified dimension. -/
theorem mle_toField {n : Nat} (table : Fin (2^n) → W) (point : Fin n → W) :
    (mle table point).toField = mle (fun i => (table i).toField) (fun i => (point i).toField) :=
  mle_map (n := n) WordExt3.ringEquiv.toRingHom table point

/-- The native input instance point has exactly the protocol's low and retained high coordinates. -/
theorem inputInstancePoint_toField (claim : Claim) (p : Nat) (point : Fin 10 → W) :
    (fun i => (inputInstancePoint (claim.toWordProtocol p) point i).toField) =
      inputInstancePoint (claim.toProtocol p) (fun i => (point i).toField) := by
  funext i
  unfold inputInstancePoint
  split <;> rfl

/-- Every native input slice is the verifier-field committed-witness opening value. -/
theorem proveOpenings_input_slices_toField (writer : Writer) (committed : Array UInt64)
    (words wordWeights : Array W) (middle : W) (claim : Claim) (p : Nat)
    (hp : 3 ≤ p) (hc : claim.point.size = p+1) (z : Fin 64) :
    let result := (proveOpenings writer committed (2^(p+4)) words wordWeights middle claim).1
    let point : Fin 10 → E := fun i => result.inputPoint[i.val]!.toField
    result.slices[z.val]!.toField =
      mle (fun slot => mle (fun b => ZMod.castHom (dvd_refl 2) E (committedWitness p committed b slot z))
        (inputInstancePoint (claim.toProtocol p) point)) (inputSlotPoint point) := by
  dsimp only
  rw [proveOpenings_input_slices writer committed words wordWeights middle claim p hp hc z]
  rw [mle_toField (n := 6)]
  simp only [mle_toField (n := p+4),
    inputInstancePoint_toField]
  rfl

end CompStark.Keccak.GkrProver
