/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Sumcheck.ByteMap
public import CompStark.Sumcheck.Buffer
public import Mathlib.Data.List.Iterate
public import CompPoly.Fields.Binary.BF64.WordExt3Proofs
/-! Fixed-multiplier byte maps constructed by joining two small nibble tables. -/
@[expose] public section
namespace CompStark.Sumcheck
set_option maxRecDepth 4096
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
open BF64
/-- A byte is the XOR of its two disjoint four-bit digits. -/
theorem byte_split (d : Fin 256) :
    (UInt64.ofNat (d.val % 16) ^^^ (UInt64.ofNat (d.val / 16) <<< 4)) =
      UInt64.ofNat d.val := by
  decide +revert

/-- Each byte position has sixteen low-nibble and sixteen high-nibble products. -/
def nibbleProductsSpec (a : Word) : Packed.Buffer 256 :=
  fillWords 256 (lt_of_lt_of_le (by decide) USize.le_size) fun i =>
    let digit := UInt64.ofNat (i.val % 16)
    let digit := if i.val % 32 < 16 then digit else digit <<< 4
    Word.mulMasked a ⟨digit <<< UInt64.ofNat (8 * (i.val / 32))⟩
/-- Successive polynomial-basis shifts using the certified reduction-tail kernel. -/
def shiftedWord (a : Word) : Nat → Word
  | 0 => a
  | n + 1 => ⟨Word.xtime (shiftedWord a n).val⟩
/-- Shifting any word is scalar multiplication by the shifted unit word. -/
theorem shiftedWord_mul (a : Word) (n : Nat) :
    (shiftedWord a n).toField = a.toField * (shiftedWord ⟨1⟩ n).toField := by
  induction n with
  | zero => exact (mul_one a.toField).symm
  | succ n ih =>
    change (⟨Word.xtime (shiftedWord a n).val⟩ : Word).toField =
      a.toField * (⟨Word.xtime (shiftedWord ⟨1⟩ n).val⟩ : Word).toField
    rw [Word.toField_xtime, Word.toField_xtime]
    change (⟨2⟩ : Word).toField * (shiftedWord a n).toField =
      a.toField * ((⟨2⟩ : Word).toField * (shiftedWord ⟨1⟩ n).toField)
    rw [ih]
    ring
/-- Iteration of the scalar shift kernel has the same word as recursive polynomial shifts. -/
theorem shiftedWord_iterate (a : Word) (n : Nat) :
    (fun w : Word => (⟨Word.xtime w.val⟩ : Word))^[n] a = shiftedWord a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl
/-- Select the four basis words belonging to one nibble at its polynomial offset. -/
@[inline] def selectNibble (basis : Nat → Word) (i : Fin 256) : Word :=
  let pos := 4 * (i.val / 16)
  Word.add
    (Word.add (if i.val.testBit 0 then basis pos else ⟨0⟩)
      (if i.val.testBit 1 then basis (pos + 1) else ⟨0⟩))
    (Word.add (if i.val.testBit 2 then basis (pos + 2) else ⟨0⟩)
      (if i.val.testBit 3 then basis (pos + 3) else ⟨0⟩))
/-- The nibble selector reads only the sixty-four polynomial basis coordinates. -/
theorem selectNibble_congr (f g : Nat → Word) (i : Fin 256)
    (h : ∀ k < 64, f k = g k) : selectNibble f i = selectNibble g i := by
  have hi := i.isLt
  dsimp only [selectNibble]
  rw [h (4 * (i.val / 16)) (by omega), h (4 * (i.val / 16) + 1) (by omega),
    h (4 * (i.val / 16) + 2) (by omega), h (4 * (i.val / 16) + 3) (by omega)]
/-- Shifted unit words select precisely the production nibble coefficient word. -/
theorem selectNibble_unit (i : Fin 256) :
    selectNibble (shiftedWord ⟨1⟩) i =
      let digit := UInt64.ofNat (i.val % 16)
      let digit := if i.val % 32 < 16 then digit else digit <<< 4
      (⟨digit <<< UInt64.ofNat (8 * (i.val / 32))⟩ : Word) := by
  decide +revert
/-- XOR selection distributes the common scalar across its four basis contributions. -/
theorem selectNibble_mul (a : Word) (i : Fin 256) :
    (selectNibble (shiftedWord a) i).toField =
      a.toField * (selectNibble (shiftedWord ⟨1⟩) i).toField := by
  dsimp only [selectNibble]
  split_ifs <;> simp only [Word.toField_add, shiftedWord_mul a,
    show (⟨0⟩ : Word).toField = 0 from rfl] <;> ring
/-- Build nibble products from shared polynomial shifts, with no variable products. -/
def nibbleProducts (a : Word) : Packed.Buffer 256 :=
  let basis := (List.iterate (fun w : Word => (⟨Word.xtime w.val⟩ : Word)) a 64).toArray
  fillWords 256 (lt_of_lt_of_le (by decide) USize.le_size) fun i =>
    selectNibble (fun k => basis[k]!) i
/-- Shared polynomial shifts give exactly the independent scalar nibble products. -/
theorem nibbleProducts_eq (a : Word) : nibbleProducts a = nibbleProductsSpec a := by
  unfold nibbleProducts nibbleProductsSpec
  apply congrArg (fillWords 256 (lt_of_lt_of_le (by decide) USize.le_size))
  funext i
  rw [selectNibble_congr _ (shiftedWord a) i (by
    intro k hk
    rw [getElem!_pos _ k (by simpa only [List.size_toArray, List.length_iterate] using hk),
      List.getElem_toArray, List.getElem_iterate, shiftedWord_iterate])]
  apply Word.toField_injective
  rw [selectNibble_mul, selectNibble_unit, Word.toField_mulMasked]

/-- Exact machine-size indices of a byte's two nibble products. -/
theorem nibbleIndices (i : USize) (hi : i.toNat < 2048) :
    (32 * (i / 256) + i % 16).toNat = 32 * (i.toNat / 256) + i.toNat % 16 ∧
      (32 * (i / 256) + 16 + (i % 256) / 16).toNat =
        32 * (i.toNat / 256) + 16 + (i.toNat % 256) / 16 := by
  have hs : 2 ^ System.Platform.numBits = USize.size := rfl
  have hn (n : Nat) (h : n < 4294967296) : (USize.ofNat n).toNat = n :=
    USize.toNat_ofNat_of_lt' (lt_of_lt_of_le h USize.le_size)
  simp only [USize.toNat_add, USize.toNat_mul, USize.toNat_div, USize.toNat_mod,
    show (256 : USize).toNat = 256 from hn 256 (by decide),
    show (32 : USize).toNat = 32 from hn 32 (by decide),
    show (16 : USize).toNat = 16 from hn 16 (by decide), hs]
  have hl := USize.le_size
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  exact ⟨True.intro, True.intro⟩


/-- Join prepared nibble products to construct all 2,048 byte products. -/
def byteMap (a : Word) : Word.ByteMap :=
  let parts := nibbleProducts a
  ⟨fillWordBuffer 2048 (lt_of_lt_of_le (by decide) USize.le_size) fun u hi =>
    Word.add
      (readWord parts (32 * (u / 256) + u % 16) (by
        rw [(nibbleIndices u hi).1]; omega)
        (lt_of_lt_of_le (by decide) USize.le_size))
      (readWord parts (32 * (u / 256) + 16 + (u % 256) / 16) (by
        rw [(nibbleIndices u hi).2]; omega)
        (lt_of_lt_of_le (by decide) USize.le_size))⟩
/-- Joining the two nibble products gives the exact canonical byte map. -/
theorem byteMap_eq (a : Word) : byteMap a = Word.ByteMap.ofScalar a := by
  simp only [byteMap, fillWordBuffer_eq]
  apply congrArg (fun f => Word.ByteMap.mk (Packed.ofFn 2048 f))
  funext i
  have hu : i.val.toUSize.toNat = i.val := USize.toNat_ofNat_of_lt' (lt_of_lt_of_le
    (lt_trans i.isLt (by decide)) USize.le_size)
  have hiu : i.val.toUSize.toNat < 2048 := by rw [hu]; exact i.isLt
  simp only [readWord_eq, (nibbleIndices i.val.toUSize hiu).1,
    (nibbleIndices i.val.toUSize hiu).2, hu, nibbleProducts_eq, nibbleProductsSpec, fillWords_eq, Packed.read_ofFn]
  have hi := i.isLt
  have hl : (32 * (i.val / 256) + i.val % 16) % 16 = i.val % 16 := by omega
  have hh : (32 * (i.val / 256) + 16 + (i.val % 256) / 16) % 16 =
      (i.val % 256) / 16 := by omega
  have hlp : (32 * (i.val / 256) + i.val % 16) / 32 = i.val / 256 := by omega
  have hhp : (32 * (i.val / 256) + 16 + (i.val % 256) / 16) / 32 = i.val / 256 := by omega
  have hlt : (32 * (i.val / 256) + i.val % 16) % 32 < 16 := by omega
  have hht : ¬(32 * (i.val / 256) + 16 + (i.val % 256) / 16) % 32 < 16 := by omega
  simp only [hl, hh, hlp, hhp, hlt, hht, ↓reduceIte]
  apply Word.toField_injective
  rw [Word.toField_add, Word.toField_mulMasked, Word.toField_mulMasked, Word.toField_mul,
    ← mul_add, ← Word.toField_add]
  congr 2
  apply congrArg Word.mk
  apply UInt64.toBitVec_inj.mp
  simp only [UInt64.toBitVec_xor, UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq']
  rw [← BitVec.shiftLeft_xor_distrib]
  congr 1
  have hs := congrArg UInt64.toBitVec (byte_split ⟨i.val % 256, by omega⟩)
  simp only [UInt64.toBitVec_xor, UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq'] at hs
  simpa only [Nat.mod_mod_of_dvd i.val (by decide : 16 ∣ 256)] using hs
end CompStark.Sumcheck
