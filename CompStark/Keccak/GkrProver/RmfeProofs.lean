/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.Rmfe

/-! Polynomial refinement of byte-pair RMFE products through the certified embedding. -/

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak BinaryField Polynomial
open scoped BigOperators
/-- All certified embedding columns fit within their 24 coefficient bits. -/
theorem embeddingColumns_bound (i : Fin 16) : Embedding.embeddingWords i < 2^24 := by
  decide +revert
/-- Every coefficient of a certified embedding basis is its encoded binary bit. -/
theorem embeddingBasis_coeff (i : Fin 16) (n : Nat) :
    (Embedding.basis i).coeff n = if (Embedding.embeddingWords i).testBit n then 1 else 0 := by
  rw [Embedding.basis, Embedding.coeff_toPoly]
  by_cases hn : n < 24
  · simp only [Embedding.basisCoeffs, Embedding.wordCoeffs, List.getElem?_ofFn, hn, dite_true,
      Option.getD_some]
    split <;> rfl
  · have hz : (Embedding.embeddingWords i).testBit n = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (embeddingColumns_bound i)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    simp only [Embedding.basisCoeffs, Embedding.wordCoeffs, List.getElem?_ofFn, hn, dite_false,
      Option.getD_none, Nat.cast_zero, hz, Bool.false_eq_true, ite_false]
/-- Each packed embedding column denotes the certified RMFE basis polynomial. -/
theorem embeddingColumn_poly (i : Fin 16) :
    toPoly (Embedding.embeddingWords i).toUInt64.toBitVec = Embedding.basis i := by
  apply Polynomial.ext
  intro n
  rw [embeddingBasis_coeff, toPoly_coeff]
  have hw : (Embedding.embeddingWords i).toUInt64.toNat = Embedding.embeddingWords i := by
    rw [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt
      (lt_trans (embeddingColumns_bound i) (by decide))]
  by_cases hn : n < 64
  · simp only [hn, dite_true, BitVec.getLsb]
    change (if (Embedding.embeddingWords i).toUInt64.toNat.testBit n then (1 : ZMod 2) else 0) = _
    rw [hw]
  · have hz : (Embedding.embeddingWords i).testBit n = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (embeddingColumns_bound i)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    simp only [hn, dite_false, hz, Bool.false_eq_true, ite_false]
/-- Binary polynomial interpretation commutes with every byte-prefix linear combination. -/
theorem embeddingPart_poly (shift : Nat) (a : UInt8) (n : Nat) :
    toPoly (embeddingPart shift a n).toBitVec =
      ∑ i : Fin n, if a.toNat.testBit i.val then
        toPoly embeddingColumns[shift+i.val]!.toUInt64.toBitVec else 0 := by
  induction n with
  | zero => simp only [embeddingPart, UInt64.toBitVec_ofNat, toPoly_zero_eq_zero, Fin.sum_univ_zero]
  | succ n ih =>
    rw [embeddingPart, UInt64.toBitVec_xor, toPoly_xor, ih, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    by_cases h : a.toNat.testBit n <;> simp only [h, Bool.false_eq_true, ite_true, ite_false, UInt64.toBitVec_ofNat, toPoly_zero_eq_zero]
/-- Each cached embedding byte denotes its eight certified basis columns. -/
theorem embeddingByte_poly (shift : Nat) (hs : shift+8 ≤ 16) (a : UInt8) :
    toPoly (embeddingByte shift a).toBitVec =
      ∑ i : Fin 8, if a.toNat.testBit i.val then
        Embedding.basis ⟨shift+i.val,by have := i.isLt; omega⟩ else 0 := by
  rw [embeddingByte, embeddingPart_poly]
  apply Finset.sum_congr rfl
  intro i _hi
  have hb : shift+i.val < 16 := by have := i.isLt; omega
  simp only [embeddingColumns, getElem!_pos, Array.size_ofFn, hb, Array.getElem_ofFn,
    embeddingColumn_poly]
/-- The native raw embedding denotes the certified sixteen-coordinate RMFE polynomial. -/
theorem embeddingRaw_poly (a : UInt64) :
    toPoly (embeddingRaw a).toBitVec = Embedding.kemb
      (fun i : Fin 16 => if a.toNat.testBit i.val then (1 : ZMod 2) else 0) := by
  rw [embeddingRaw, UInt64.toBitVec_xor, toPoly_xor,
    embeddingByte_poly 0 (by decide), embeddingByte_poly 8 (by decide)]
  change _ = ∑ i : Fin 16, (if a.toNat.testBit i.val then (1 : ZMod 2) else 0) •
    (Embedding.basis i).map (ZMod.castHom (dvd_refl 2) (ZMod 2))
  rw [ZMod.castHom_self]
  simp only [Polynomial.map_id, ite_smul, one_smul, zero_smul]
  rw [Fin.sum_univ_add (a := 8) (b := 8)]
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro i _hi
    simp only [UInt64.toNat_toUInt8, Nat.testBit_mod_two_pow, i.isLt, decide_true,
      Bool.true_and, Nat.zero_add, Fin.val_castAdd]
    rfl
  · apply Finset.sum_congr rfl
    intro i _hi
    simp only [UInt64.toNat_toUInt8, Nat.testBit_mod_two_pow, i.isLt, decide_true,
      Bool.true_and, UInt64.toNat_shiftRight, Fin.val_natAdd]
    change (if (a.toNat >>> 8).testBit i.val then _ else _) = _
    rw [Nat.testBit_shiftRight]
    rfl
/-- Every native byte prefix stays within the twenty-four RMFE coefficient bits. -/
theorem embeddingPart_bound (shift : Nat) (a : UInt8) (n : Nat) (hn : shift+n ≤ 16) :
    (embeddingPart shift a n).toNat < 2^24 := by
  induction n with
  | zero => change (0 : UInt64).toNat < 2^24; decide
  | succ n ih =>
    rw [embeddingPart, UInt64.toNat_xor]
    apply Nat.xor_lt_two_pow (ih (by omega))
    split
    · have hb : shift+n < 16 := by omega
      simp only [embeddingColumns, getElem!_pos, Array.size_ofFn, hb, Array.getElem_ofFn,
        Nat.toUInt64, UInt64.toNat_ofNat']
      exact lt_of_le_of_lt (Nat.mod_le _ _) (embeddingColumns_bound ⟨shift+n,hb⟩)
    · decide
/-- Every raw sixteen-bit embedding fits in twenty-four polynomial coefficients. -/
theorem embeddingRaw_bound (a : UInt64) : (embeddingRaw a).toNat < 2^24 := by
  rw [embeddingRaw, UInt64.toNat_xor]
  exact Nat.xor_lt_two_pow (embeddingPart_bound 0 _ 8 (by decide))
    (embeddingPart_bound 8 _ 8 (by decide))
/-- Narrowing an RMFE embedding to the word-product limb preserves its polynomial. -/
theorem embeddingRaw_narrow (a : UInt64) :
    toPoly ((embeddingRaw a).toBitVec.setWidth 32) = toPoly (embeddingRaw a).toBitVec := by
  have h : ((embeddingRaw a).toBitVec.setWidth 32).setWidth 64 = (embeddingRaw a).toBitVec :=
    BitVec.setWidth_setWidth_eq_self (by
      change (embeddingRaw a).toNat < (BitVec.twoPow 64 32).toNat
      rw [BitVec.toNat_twoPow_of_lt (by decide : 32 < 64)]
      exact lt_trans (embeddingRaw_bound a) (by decide))
  have hp := toPoly_zeroExtendTo ((embeddingRaw a).toBitVec.setWidth 32) (w := 64) (by decide)
  change toPoly (((embeddingRaw a).toBitVec.setWidth 32).setWidth 64) = _ at hp
  rw [h] at hp
  exact hp.symm
/-- Prepared byte-pair multiplication is multiplication of the certified RMFE polynomials. -/
theorem prepareRmfeProducts_mul_poly (a b : UInt64) :
    toPoly (prepareRmfeProducts.mul a b).toBitVec =
      Embedding.kemb (fun i : Fin 16 => if a.toNat.testBit i.val then (1 : ZMod 2) else 0) *
      Embedding.kemb (fun i : Fin 16 => if b.toNat.testBit i.val then (1 : ZMod 2) else 0) := by
  rw [prepareRmfeProducts_mul, binaryProduct_poly, embeddingRaw_narrow, embeddingRaw_narrow,
    embeddingRaw_poly, embeddingRaw_poly]
/-- The certified RMFE projection of a prepared product is the pointwise input product. -/
theorem prepareRmfeProducts_mul_project (a b : UInt64) (i : Fin 16) :
    Embedding.kproj (toPoly (prepareRmfeProducts.mul a b).toBitVec) i =
      (if a.toNat.testBit i.val then (1 : ZMod 2) else 0) *
      (if b.toNat.testBit i.val then (1 : ZMod 2) else 0) := by
  rw [prepareRmfeProducts_mul_poly]
  exact congrFun (Embedding.kproj_kemb_mul _ _) i
/-- The all-ones raw input denotes the all-ones certified embedding. -/
theorem embeddingRaw_ones_poly : toPoly (embeddingRaw 65535).toBitVec =
    Embedding.kemb (fun _ : Fin 16 => (1 : ZMod 2)) := by
  rw [embeddingRaw_poly]
  apply congrArg Embedding.kemb
  funext i
  have h : ∀ i : Fin 16, (65535 : UInt64).toNat.testBit i.val = true := by decide
  rw [h i]
  rfl
/-- Prepared affine products denote multiplication by the all-ones RMFE polynomial. -/
theorem prepareRmfeProducts_ones_poly (a : UInt64) :
    toPoly (prepareRmfeProducts.ones a).toBitVec =
      Embedding.kemb (fun _ : Fin 16 => (1 : ZMod 2)) *
      Embedding.kemb (fun i : Fin 16 => if a.toNat.testBit i.val then (1 : ZMod 2) else 0) := by
  rw [prepareRmfeProducts_ones, binaryProduct_poly, embeddingRaw_narrow, embeddingRaw_narrow,
    embeddingRaw_ones_poly, embeddingRaw_poly]
/-- The native RMFE chi payload denotes the affine binary product polynomial. -/
theorem prepareRmfeProducts_chi_poly (a b c : UInt64) :
    toPoly (prepareRmfeProducts.ones (a ^^^ c) ^^^ prepareRmfeProducts.mul b c).toBitVec =
      toPoly (embeddingRaw 65535).toBitVec * toPoly (embeddingRaw a).toBitVec +
      (toPoly (embeddingRaw 65535).toBitVec + toPoly (embeddingRaw b).toBitVec) *
        toPoly (embeddingRaw c).toBitVec := by
  rw [UInt64.toBitVec_xor, toPoly_xor, prepareRmfeProducts_ones,
    prepareRmfeProducts_mul, binaryProduct_poly, binaryProduct_poly,
    embeddingRaw_narrow, embeddingRaw_narrow, embeddingRaw_narrow, embeddingRaw_narrow,
    embeddingRaw_xor, UInt64.toBitVec_xor, toPoly_xor]
  ring

end CompStark.Keccak.GkrProver
