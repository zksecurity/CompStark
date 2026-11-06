/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Sumcheck.ByteMap
public import CompStark.Sumcheck.Buffer
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
def nibbleProducts (a : Word) : Packed.Buffer 256 :=
  fillWords 256 (lt_of_lt_of_le (by decide) USize.le_size) fun i =>
    let digit := UInt64.ofNat (i.val % 16)
    let digit := if i.val % 32 < 16 then digit else digit <<< 4
    Word.mulMasked a ⟨digit <<< UInt64.ofNat (8 * (i.val / 32))⟩
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
  ⟨fillWords 2048 (lt_of_lt_of_le (by decide) USize.le_size) fun i =>
    let u := i.val.toUSize
    have hu : u.toNat = i.val := USize.toNat_ofNat_of_lt' (lt_of_lt_of_le
      (lt_trans i.isLt (by decide)) USize.le_size)
    have hi : u.toNat < 2048 := by rw [hu]; exact i.isLt
    Word.add
      (readWord parts (32 * (u / 256) + u % 16) (by
        rw [(nibbleIndices u hi).1, hu]; have := i.isLt; omega)
        (lt_of_lt_of_le (by decide) USize.le_size))
      (readWord parts (32 * (u / 256) + 16 + (u % 256) / 16) (by
        rw [(nibbleIndices u hi).2, hu]; have := i.isLt; omega)
        (lt_of_lt_of_le (by decide) USize.le_size))⟩
/-- Joining the two nibble products gives the exact canonical byte map. -/
theorem byteMap_eq (a : Word) : byteMap a = Word.ByteMap.ofScalar a := by
  simp only [byteMap, fillWords_eq]
  apply congrArg (fun f => Word.ByteMap.mk (Packed.ofFn 2048 f))
  funext i
  have hu : i.val.toUSize.toNat = i.val := USize.toNat_ofNat_of_lt' (lt_of_lt_of_le
    (lt_trans i.isLt (by decide)) USize.le_size)
  have hiu : i.val.toUSize.toNat < 2048 := by rw [hu]; exact i.isLt
  simp only [readWord_eq, (nibbleIndices i.val.toUSize hiu).1,
    (nibbleIndices i.val.toUSize hiu).2, hu, nibbleProducts, fillWords_eq, Packed.read_ofFn]
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
