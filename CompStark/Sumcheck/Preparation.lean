/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Sumcheck.ByteMap
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
  Packed.ofFn 256 fun i =>
    let digit := UInt64.ofNat (i.val % 16)
    let digit := if i.val % 32 < 16 then digit else digit <<< 4
    Word.mulMasked a ⟨digit <<< UInt64.ofNat (8 * (i.val / 32))⟩
/-- Join prepared nibble products to construct all 2,048 byte products. -/
def byteMap (a : Word) : Word.ByteMap :=
  let parts := nibbleProducts a
  ⟨Packed.ofFn 2048 fun i =>
    Word.add
      (Packed.read parts ⟨32 * (i.val / 256) + i.val % 16, by have := i.isLt; omega⟩)
      (Packed.read parts ⟨32 * (i.val / 256) + 16 + (i.val % 256) / 16,
        by have := i.isLt; omega⟩)⟩
/-- Joining the two nibble products gives the exact canonical byte map. -/
theorem byteMap_eq (a : Word) : byteMap a = Word.ByteMap.ofScalar a := by
  apply congrArg (fun f => Word.ByteMap.mk (Packed.ofFn 2048 f))
  funext i
  simp only [nibbleProducts, Packed.read_ofFn]
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
