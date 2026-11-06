/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompPoly.Fields.Binary.BF64.FixedMapProofs

/-! Machine-size loads for shared binary-field multiplier maps. -/

@[expose] public section
namespace CompStark.Sumcheck
open BF64

/-- A bounded byte-map word index has an exact machine-size byte offset. -/
theorem mapOffset_nat (i : USize) (hi : i.toNat < 2048) :
    (i * 8).toNat = 8 * i.toNat := by
  have h8 : (8 : USize).toNat = 8 :=
    USize.toNat_ofNat_of_lt' (lt_of_lt_of_le (by decide) USize.le_size)
  rw [USize.toNat_mul, h8, Nat.mod_eq_of_lt (lt_of_lt_of_le (by omega) USize.le_size)]
  omega

/-- Read a byte-map word using only machine-size offsets in the native kernel. -/
@[inline] def mapRead (map : Word.ByteMap) (i : USize) (hi : i.toNat < 2048) : Word :=
  let off := i * 8
  let ho := mapOffset_nat i hi
  let lo := map.table.val.bytes.ugetUInt32LE off (by
    have hs := map.table.val.byteSize
    rw [map.table.property] at hs
    rw [ho, hs]
    omega)
  let high := map.table.val.bytes.ugetUInt32LE (off + 4) (by
    have hs := map.table.val.byteSize
    rw [map.table.property] at hs
    have h4 : (4 : USize).toNat = 4 :=
      USize.toNat_ofNat_of_lt' (lt_of_lt_of_le (by decide) USize.le_size)
    rw [USize.toNat_add, ho, h4, Nat.mod_eq_of_lt (lt_of_lt_of_le (by omega) USize.le_size), hs]
    omega)
  ⟨lo.toUInt64 ||| (high.toUInt64 <<< 32)⟩

/-- Machine-size map loads agree with canonical packed map reads. -/
theorem mapRead_eq (map : Word.ByteMap) (i : USize) (hi : i.toNat < 2048) :
    mapRead map i hi = Packed.read map.table ⟨i.toNat, hi⟩ := by
  have h4 : (4 : USize).toNat = 4 :=
    USize.toNat_ofNat_of_lt' (lt_of_lt_of_le (by decide) USize.le_size)
  simp only [mapRead, Packed.read, Packed.get, ByteArray.ugetUInt32LE,
    ByteArray.getUInt32LE, mapOffset_nat i hi, USize.toNat_add, h4]
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le (by omega) USize.le_size)]

/-- Position and byte coordinates have an exact packed-table index. -/
theorem mapIndex_nat (position : Fin 8) (digit : UInt8) :
    (position.val.toUSize * 256 + digit.toUSize).toNat = 256 * position.val + digit.toNat := by
  have hp := position.isLt
  have hd := digit.toNat_lt
  have h256 : (256 : USize).toNat = 256 :=
    USize.toNat_ofNat_of_lt' (lt_of_lt_of_le (by decide) USize.le_size)
  have hm : (position.val.toUSize * 256).toNat = 256 * position.val := by
    rw [USize.toNat_mul,
      USize.toNat_ofNat_of_lt' (lt_of_lt_of_le (by omega) USize.le_size), h256,
      Nat.mod_eq_of_lt (lt_of_lt_of_le (by omega) USize.le_size)]
    omega
  rw [USize.toNat_add, hm, UInt8.toNat_toUSize,
    Nat.mod_eq_of_lt (lt_of_lt_of_le (by omega) USize.le_size)]

/-- A lookup at one byte position uses an unboxed byte and an unboxed table offset. -/
@[inline] def mapByte (map : Word.ByteMap) (position : Fin 8) (digit : UInt8) : Word :=
  mapRead map (position.val.toUSize * 256 + digit.toUSize) (by
    rw [mapIndex_nat]
    have := position.isLt
    have := digit.toNat_lt
    omega)

/-- A machine-size byte lookup is the canonical position-major product entry. -/
theorem mapByte_eq (map : Word.ByteMap) (position : Fin 8) (digit : UInt8) :
    mapByte map position digit =
      Packed.read map.table ⟨256 * position.val + digit.toNat,
        by have := position.isLt; have := digit.toNat_lt; omega⟩ := by
  rw [mapByte, mapRead_eq]
  congr 1
  exact Fin.ext (mapIndex_nat position digit)

/-- A byte conversion selects precisely the eight low bits used by the canonical map. -/
theorem byteDigit_nat (value : UInt64) : value.toUInt8.toNat = (value &&& 255).toNat := by
  simp only [UInt64.toNat_toUInt8, UInt64.toNat_and]
  exact (Nat.and_two_pow_sub_one_eq_mod value.toNat 8).symm

/-- Fixed multiplication with eight machine-size packed-map reads. -/
@[inline] def mapMul (map : Word.ByteMap) (a : Word) : Word :=
  let acc := mapByte map ⟨0, by decide⟩ a.val.toUInt8
  let acc := Word.add acc (mapByte map ⟨1, by decide⟩ (a.val >>> 8).toUInt8)
  let acc := Word.add acc (mapByte map ⟨2, by decide⟩ (a.val >>> 16).toUInt8)
  let acc := Word.add acc (mapByte map ⟨3, by decide⟩ (a.val >>> 24).toUInt8)
  let acc := Word.add acc (mapByte map ⟨4, by decide⟩ (a.val >>> 32).toUInt8)
  let acc := Word.add acc (mapByte map ⟨5, by decide⟩ (a.val >>> 40).toUInt8)
  let acc := Word.add acc (mapByte map ⟨6, by decide⟩ (a.val >>> 48).toUInt8)
  Word.add acc (mapByte map ⟨7, by decide⟩ (a.val >>> 56).toUInt8)

/-- Machine-size lookup multiplication equals the certified fixed-multiplier kernel. -/
theorem mapMul_eq (map : Word.ByteMap) (a : Word) : mapMul map a = map.mul a := by
  simp only [mapMul, mapByte_eq, byteDigit_nat, Word.ByteMap.mul]
  rfl

end CompStark.Sumcheck
