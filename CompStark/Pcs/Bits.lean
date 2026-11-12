/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.BinaryDomain
public import CompStark.Keccak.Gkr.Protocol

/-! Polynomial-basis bit decomposition of every physical Keccak word. -/

@[expose] public section

namespace CompStark.Pcs

open CompStark.BinaryFields

/-- Little-endian polynomial-basis bit coordinates of a base-field word. -/
def wordBits (word : K) (bit : Fin 64) : ZMod 2 :=
  if word.toBitVec[bit.val] then 1 else 0

/-- Polynomial-basis bit coordinates preserve addition. -/
theorem wordBits_add (a b : K) : wordBits (a + b) = wordBits a + wordBits b := by
  funext bit
  change (if (a.toBitVec ^^^ b.toBitVec)[bit.val] then (1 : ZMod 2) else 0) = _
  simp only [BitVec.getElem_xor, Pi.add_apply, wordBits]
  cases a.toBitVec[bit.val] <;> cases b.toBitVec[bit.val] <;> decide

/-- The polynomial-basis coordinate map is binary-linear. -/
noncomputable def wordBitsLinear : K →ₗ[ZMod 2] (Fin 64 → ZMod 2) where
  toFun := wordBits
  map_add' := wordBits_add
  map_smul' c a := by
    rcases Pcs.binary_cases c with rfl | rfl <;> funext bit <;>
      simp only [RingHom.id_apply, zero_smul, one_smul]
    change (if (BitVec.ofNat 64 0)[bit.val] then (1 : ZMod 2) else 0) = 0
    rw [BitVec.getElem_zero_ofNat_zero]
    rfl

/-- Equal polynomial-basis bits give equal words. -/
theorem wordBits_injective : Function.Injective wordBits := by
  intro a b h
  apply BF64.toBitVec_injective
  apply BitVec.eq_of_getElem_eq
  intro bit hb
  have equal := congrFun h ⟨bit, hb⟩
  dsimp [wordBits] at equal
  cases ha : a.toBitVec[bit] <;> cases hb : b.toBitVec[bit] <;>
    simp_all only [Bool.false_eq_true, ↓reduceIte, zero_ne_one, one_ne_zero]

/-- Each field power `g^i`, for `i < 64`, has exactly its own bit set. -/
theorem wordBits_power (i : Fin 64) : wordBits (g ^ i.val) = Pi.single i 1 := by
  have powers : ∀ i j : Fin 64, (g ^ i.val).toBitVec[j.val] = decide (j = i) := by
    decide +kernel
  funext j
  simp only [wordBits, powers, decide_eq_true_eq, Pi.single_apply]

/-- The sum of the 64 polynomial-basis bits packs back to the same base-field word. -/
theorem wordBits_pack (word : K) :
    (∑ bit : Fin 64, (ZMod.castHom (dvd_refl 2) K) (wordBits word bit) * g ^ bit.val) = word := by
  apply wordBits_injective
  change wordBitsLinear (∑ bit : Fin 64,
    (ZMod.castHom (dvd_refl 2) K) (wordBits word bit) * g ^ bit.val) = wordBitsLinear word
  have term (bit : Fin 64) :
      (ZMod.castHom (dvd_refl 2) K) (wordBits word bit) * g ^ bit.val =
        wordBits word bit • g ^ bit.val := rfl
  simp only [term, map_sum, map_smul, wordBitsLinear, LinearMap.coe_mk, AddHom.coe_mk,
    wordBits_power]
  funext bit
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- Packing a base word's bit coordinates commutes with the field inclusion. -/
theorem wordBits_laneValue (word : K) :
    Keccak.Gkr.laneValue (ofK g) (wordBits word) = ofK word := by
  calc
    _ = (algebraMap K E) (∑ bit : Fin 64,
        (ZMod.castHom (dvd_refl 2) K) (wordBits word bit) * g ^ bit.val) := by
      simp only [Keccak.Gkr.laneValue, map_sum, map_mul, map_pow]
      apply Finset.sum_congr rfl
      intro bit _
      congr 1
    _ = _ := congrArg (algebraMap K E) (wordBits_pack word)

end CompStark.Pcs
