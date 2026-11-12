/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.BinaryValues

/-! Exact evaluation of the retained forty-seven-coefficient product polynomials. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak BF64
open scoped BigOperators

/-- Structural byte reduction preserves the complete coefficient-buffer length. -/
theorem reducePayloadDigits_size (n digit : Nat) (buckets : FixedWords (6*256*3))
    (out : PackedE) (hout : out.size = 47) :
    (reducePayloadDigits n digit buckets out).size = 47 := by
  induction n generalizing digit buckets out with
  | zero => exact hout
  | succ n ih =>
    rw [reducePayloadDigits]
    exact ih _ _ _ (reducePayloadBits_size digit 8 buckets out hout)

/-- The production weighted payload contains exactly forty-seven coefficients. -/
theorem weightedPayload_size (payload : FixedWords 1600) (weights : FixedWords 4800) :
    (weightedPayload payload weights).size = 47 := by
  rw [weightedPayload_loop]
  change (bucketDigitLoop (_,_,(0 : Nat).toUSize)).2.1.size = _
  rw [bucketDigitLoop_eq 6 0 (by omega)]
  exact reducePayloadDigits_size _ _ _ _ rfl

/-- Each retained native segment-pack row has the complete protocol product length. -/
theorem productRow_size (w : SlicedWitness) (d : Nat) (claim : Claim) (maps : RmfeProducts)
    (m b : Nat) : (productRow w d claim maps m b).size = 47 :=
  weightedPayload_size _ _

/-- Every prepared native chi payload fits the transmitted forty-seven binary coefficients. -/
theorem productCell_bound47 (state : Array UInt64) (groups offset : USize) (bits : UInt64) (j : Nat) :
    (productCell state groups offset bits prepareRmfeProducts j).toNat < 2^47 := by
  apply BinaryField.BitVec_lt_two_pow_of_toPoly_degree_lt
  rw [productCell,UInt64.toBitVec_xor,BinaryField.toPoly_xor,
    prepareRmfeProducts_ones_poly,prepareRmfeProducts_mul_poly]
  exact lt_of_le_of_lt
    (Polynomial.degree_add_le_of_degree_le (Embedding.kemb_mul_degree _ _) (Embedding.kemb_mul_degree _ _))
    (by decide)

/-- A chi payload evaluates as exactly its forty-seven retained bits. -/
theorem payloadWordPolynomial_eval47 (p : UInt64) (hp : p.toNat < 2^47) (s : W) :
    (payloadWordPolynomial p).eval s = ∑ k : Fin 47, if p.toNat.testBit k.val then s^k.val else 0 := by
  have hd : (payloadWordPolynomial p).natDegree < 47 := by
    by_cases hz : payloadWordPolynomial p = 0
    · rw [hz,Polynomial.natDegree_zero]; decide
    · apply (Polynomial.natDegree_lt_iff_degree_lt hz).mpr
      exact lt_of_le_of_lt Polynomial.degree_map_le (BinaryField.toPoly_degree_of_lt_two_pow p.toBitVec hp)
  rw [Polynomial.eval_eq_sum_range' hd,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  have hk : k.val < 64 := by have := k.isLt; omega
  rw [payloadWordPolynomial,Polynomial.coeff_map,BinaryField.toPoly_coeff,dite_eq_left hk]
  change (ZMod.castHom (dvd_refl 2) W) (if p.toNat.testBit k.val then (1 : ZMod 2) else 0)*s^k.val = _
  split <;> simp only [map_one,map_zero,one_mul,zero_mul]

/-- Evaluating a retained row gives the exact weighted sum of all native RMFE chi evaluations. -/
theorem productRow_eval (w : SlicedWitness) (d : Nat) (claim : Claim) (s : W) (m b : Nat) :
    evaluatePackedLoop (productRow w d claim prepareRmfeProducts m b) (CompStark.Sumcheck.prepare s)
      (productRow w d claim prepareRmfeProducts m b).size 0 =
      ∑ j : Fin 1600, claim.weights[j.val]! *
        (payloadWordPolynomial (productCell w.layers[12*(m+1)-d]! (2^w.nLog/64).toUSize
          (b/4).toUSize (16*(b%4)).toUInt64 prepareRmfeProducts j.val)).eval s := by
  rw [evaluatePackedLoop_eq,productRow_size,mul_zero,add_zero,← Fin.sum_univ_eq_sum_range]
  simp only [productRow_get,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [payloadWordPolynomial_eval47 _ (productCell_bound47 ..),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  split <;> simp only [mul_zero,zero_mul]

end CompStark.Keccak.GkrProver
