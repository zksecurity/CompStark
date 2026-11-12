/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.WeightMapProofs

/-! Polynomial evaluation semantics of the six-byte native position maps. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators

/-- The scalar machine address of one native byte-map coordinate is its natural row-major address. -/
theorem weightByte_address (j : Fin 1600) (byte : Fin 6) (c : Fin 3) (digit : UInt8) :
    (4608*j.val).toUSize+768*byte.val.toUSize+3*digit.toUSize+c.val.toUSize =
      (3*(1536*j.val+256*byte.val+digit.toNat)+c.val).toUSize := by
  have hd : digit.toNat.toUSize = digit.toUSize := by
    apply USize.toNat_inj.mp
    rw [usize_small digit.toNat (by have := digit.toNat_lt; omega),UInt8.toNat_toUSize]
  rw [show 3*(1536*j.val+256*byte.val+digit.toNat)+c.val =
    4608*j.val+768*byte.val+3*digit.toNat+c.val by omega]
  simp only [Nat.toUSize,USize.ofNat_add,USize.ofNat_mul] at hd ⊢
  rw [hd]
  rfl

/-- Each proved native byte lookup reads its certified scalar coordinate in the structural map. -/
theorem weightByte_readWord (maps : FixedWords (1600*6*256*3)) (j : Fin 1600)
    (hb : (4608*j.val).toUSize.toNat ≤ 7372800-4608) (byte : Fin 6) (c : Fin 3)
    (hbyte : byte.val.toUSize.toNat < 6) (hc : c.val.toUSize.toNat < 3) (digit : UInt8) :
    weightByte maps (4608*j.val).toUSize hb byte.val.toUSize hbyte c.val.toUSize hc digit =
      readWord maps (3*(1536*j.val+256*byte.val+digit.toNat)+c.val) := by
  rw [weightByte_eq,weightByte_address]
  rfl

/-- The three coordinate lookups of one native byte reconstruct its complete weighted subset sum. -/
theorem weightByte_value (weights : Array W) (s : W) (j : Fin 1600)
    (hb : (4608*j.val).toUSize.toNat ≤ 7372800-4608) (byte : Fin 6)
    (hbyte : byte.val.toUSize.toNat < 6) (digit : UInt8) :
    (⟨⟨weightByte (prepareWeightMaps weights (CompStark.Sumcheck.prepare s))
      (4608*j.val).toUSize hb byte.val.toUSize hbyte (0 : Nat).toUSize
      (by rw [usize_small 0 (by decide)]; decide) digit⟩,
      ⟨weightByte (prepareWeightMaps weights (CompStark.Sumcheck.prepare s))
        (4608*j.val).toUSize hb byte.val.toUSize hbyte (1 : Nat).toUSize
        (by rw [usize_small 1 (by decide)]; decide) digit⟩,
      ⟨weightByte (prepareWeightMaps weights (CompStark.Sumcheck.prepare s))
        (4608*j.val).toUSize hb byte.val.toUSize hbyte (2 : Nat).toUSize
        (by rw [usize_small 2 (by decide)]; decide) digit⟩⟩ : W) =
      byteSubset (fun bit => weights[j.val]!*s^(8*byte.val+bit)) 8 digit.toNat := by
  rw [weightByte_readWord _ j hb byte (⟨0,by decide⟩ : Fin 3),weightByte_readWord _ j hb byte (⟨1,by decide⟩ : Fin 3),
    weightByte_readWord _ j hb byte (⟨2,by decide⟩ : Fin 3)]
  change tripleValue _ (1536*j.val+256*byte.val+digit.toNat) = _
  exact prepareWeightMaps_get weights s j byte ⟨digit.toNat,digit.toNat_lt⟩

/-- Evaluate all three scalar coordinates of a binary polynomial with the native six-byte maps. -/
def evalWeightValue (maps : FixedWords (1600*6*256*3)) (base : USize)
    (hb : base.toNat ≤ 7372800-4608) (p : UInt64) : W :=
  ⟨⟨evalWeightCoordinate maps base hb 0 (usize_toNat_lt (by decide) (by decide)) p⟩,
    ⟨evalWeightCoordinate maps base hb 1 (usize_toNat_lt (by decide) (by decide)) p⟩,
    ⟨evalWeightCoordinate maps base hb 2 (usize_toNat_lt (by decide) (by decide)) p⟩⟩

/-- The three scalar byte lookups interpreted as one extension-field value. -/
def weightByteValue (maps : FixedWords (1600*6*256*3)) (base : USize)
    (hb : base.toNat ≤ 7372800-4608) (byte : USize) (hbyte : byte.toNat < 6)
    (digit : UInt8) : W :=
  ⟨⟨weightByte maps base hb byte hbyte 0 (usize_toNat_lt (by decide) (by decide)) digit⟩,
    ⟨weightByte maps base hb byte hbyte 1 (usize_toNat_lt (by decide) (by decide)) digit⟩,
    ⟨weightByte maps base hb byte hbyte 2 (usize_toNat_lt (by decide) (by decide)) digit⟩⟩

/-- Native coordinate XOR is the extension-field sum of all six byte contributions. -/
theorem evalWeightValue_bytes (maps : FixedWords (1600*6*256*3)) (base : USize)
    (hb : base.toNat ≤ 7372800-4608) (p : UInt64) :
    evalWeightValue maps base hb p =
      weightByteValue maps base hb 0 (usize_toNat_lt (by decide) (by decide)) p.toUInt8+
      weightByteValue maps base hb 1 (usize_toNat_lt (by decide) (by decide)) (p >>> 8).toUInt8+
      weightByteValue maps base hb 2 (usize_toNat_lt (by decide) (by decide)) (p >>> 16).toUInt8+
      weightByteValue maps base hb 3 (usize_toNat_lt (by decide) (by decide)) (p >>> 24).toUInt8+
      weightByteValue maps base hb 4 (usize_toNat_lt (by decide) (by decide)) (p >>> 32).toUInt8+
      weightByteValue maps base hb 5 (usize_toNat_lt (by decide) (by decide)) (p >>> 40).toUInt8 := by
  rfl

/-- Complete extension-byte reads have the exact weighted subset semantics of the native map builder. -/
theorem weightByteValue_get (weights : Array W) (s : W) (j : Fin 1600)
    (hb : (4608*j.val).toUSize.toNat ≤ 7372800-4608) (byte : Fin 6)
    (hbyte : byte.val.toUSize.toNat < 6) (digit : UInt8) :
    weightByteValue (prepareWeightMaps weights (CompStark.Sumcheck.prepare s))
      (4608*j.val).toUSize hb byte.val.toUSize hbyte digit =
      byteSubset (fun bit => weights[j.val]!*s^(8*byte.val+bit)) 8 digit.toNat := by
  have hzero : (0 : Nat).toUSize = (0 : USize) := by
    apply USize.toNat_inj.mp
    rw [usize_small 0 (by decide),USize.toNat_zero]
  have hone : (1 : Nat).toUSize = (1 : USize) := rfl
  have htwo : (2 : Nat).toUSize = (2 : USize) := rfl
  simpa only [hzero,hone,htwo,weightByteValue] using weightByte_value weights s j hb byte hbyte digit

/-- A native polynomial evaluation is the finite sum of its six extension-byte contributions. -/
theorem evalWeightValue_sum (maps : FixedWords (1600*6*256*3)) (base : USize)
    (hb : base.toNat ≤ 7372800-4608) (p : UInt64) :
    evalWeightValue maps base hb p =
      ∑ byte : Fin 6, weightByteValue maps base hb byte.val.toUSize
        (by rw [usize_small byte.val (by have := byte.isLt; omega)]; exact byte.isLt)
        (p >>> (8*byte.val).toUInt64).toUInt8 := by
  rw [Fin.sum_univ_six]
  rw [evalWeightValue_bytes]
  simp only [Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.mul_one ]
  rfl

/-- A byte lookup retains exactly the eight polynomial bits at its little-endian offset. -/
theorem wordByte_testBit (p : UInt64) (byte bit : Nat) (hb : byte < 6) (hi : bit < 8) :
    ((p >>> (8*byte).toUInt64).toUInt8).toNat.testBit bit = p.toNat.testBit (8*byte+bit) := by
  have hs : (8*byte).toUInt64.toNat%64 = 8*byte := by
    rw [Nat.toUInt64,UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)]
  simp only [UInt64.toNat_toUInt8,Nat.testBit_mod_two_pow,hi,decide_true,Bool.true_and,
    UInt64.toNat_shiftRight,hs,Nat.testBit_shiftRight]

/-- Native six-byte evaluation sums precisely the selected weighted polynomial coefficients. -/
theorem evalWeightValue_coefficients (weights : Array W) (s : W) (j : Fin 1600)
    (hb : (4608*j.val).toUSize.toNat ≤ 7372800-4608) (p : UInt64) :
    evalWeightValue (prepareWeightMaps weights (CompStark.Sumcheck.prepare s))
      (4608*j.val).toUSize hb p =
      ∑ k : Fin 48, if p.toNat.testBit k.val then weights[j.val]!*s^k.val else 0 := by
  rw [evalWeightValue_sum]
  simp only [weightByteValue_get,byteSubset]
  have h := (finProdFinEquiv (m := 6) (n := 8)).sum_comp
    (fun k : Fin 48 => if p.toNat.testBit k.val then weights[j.val]!*s^k.val else 0)
  rw [Fintype.sum_prod_type] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro byte _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro bit _
  rw [wordByte_testBit p byte.val bit.val byte.isLt bit.isLt]
  change (if p.toNat.testBit (8*byte.val+bit.val) then weights[j.val]!*s^(8*byte.val+bit.val) else 0) =
    if p.toNat.testBit (bit.val+8*byte.val) then weights[j.val]!*s^(bit.val+8*byte.val) else 0
  rw [Nat.add_comm bit.val (8*byte.val)]

/-- A payload confined to six bytes evaluates as precisely its forty-eight binary coefficients. -/
theorem payloadWordPolynomial_eval48 (p : UInt64) (hp : p.toNat < 2^48) (s : W) :
    (payloadWordPolynomial p).eval s = ∑ k : Fin 48, if p.toNat.testBit k.val then s^k.val else 0 := by
  have hd : (payloadWordPolynomial p).natDegree < 48 := by
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

/-- All three native map coordinates recover the complete weighted binary-polynomial evaluation. -/
theorem evalWeightValue_polynomial (weights : Array W) (s : W) (j : Fin 1600)
    (hb : (4608*j.val).toUSize.toNat ≤ 7372800-4608) (p : UInt64) (hp : p.toNat < 2^48) :
    evalWeightValue (prepareWeightMaps weights (CompStark.Sumcheck.prepare s))
      (4608*j.val).toUSize hb p = weights[j.val]!*(payloadWordPolynomial p).eval s := by
  rw [evalWeightValue_coefficients,payloadWordPolynomial_eval48 p hp,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  split <;> simp only [mul_zero]

/-- Every prepared RMFE product stays within the six bytes consumed by the native evaluation maps. -/
theorem prepareRmfeProducts_mul_bound48 (a b : UInt64) :
    (prepareRmfeProducts.mul a b).toNat < 2^48 := by
  apply BinaryField.BitVec_lt_two_pow_of_toPoly_degree_lt
  rw [prepareRmfeProducts_mul_poly]
  exact lt_of_le_of_lt (CompStark.Keccak.Embedding.kemb_mul_degree _ _) (by decide)

/-- The complete native position map evaluates a weighted product of its two RMFE factors. -/
theorem evalWeightValue_rmfeProduct (weights : Array W) (s : W) (j : Fin 1600)
    (hb : (4608*j.val).toUSize.toNat ≤ 7372800-4608) (a b : UInt64) :
    evalWeightValue (prepareWeightMaps weights (CompStark.Sumcheck.prepare s))
      (4608*j.val).toUSize hb (prepareRmfeProducts.mul a b) =
      weights[j.val]!*(rmfeValue s (lane a)*rmfeValue s (lane b)) := by
  rw [evalWeightValue_polynomial _ _ _ _ _ (prepareRmfeProducts_mul_bound48 a b),rmfeProduct_eval]

end CompStark.Keccak.GkrProver
