/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompPoly.Fields.Binary.BF64.WordField
public import CompStark.Sumcheck.Fold
public import CompPoly.Fields.Binary.BF64.WordExt3Dot
import Init.Data.ByteArray.Lemmas

/-! Contiguous extension tables and shared-scalar multiplication for GKR folds. -/

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64

/-- Zero bytes allocated by doubling raw byte arrays, without a boxed intermediate array. -/
def zeroBytes (n : Nat) : ByteArray :=
  if _h : n = 0 then ByteArray.empty else
    let half := zeroBytes (n/2)
    let even := half ++ half
    if n%2 = 0 then even else even.push 0
termination_by n

/-- Raw zero allocation has exactly its requested byte length. -/
theorem zeroBytes_size (n : Nat) : (zeroBytes n).size = n := by
  rw [zeroBytes]
  split
  · rename_i h
    rw [ByteArray.size_empty, h]
  · rename_i h
    have ih := zeroBytes_size (n/2)
    split
    · simp only [ByteArray.size_append, ih]
      omega
    · simp only [ByteArray.size_push, ByteArray.size_append, ih]
      omega
termination_by n

/-- A fixed-length word buffer whose runtime representation is its byte array. -/
abbrev FixedWords (n : Nat) := {a : ByteArray // a.size = 8*n ∧ n < 2^29}

/-- Allocate a contiguous fixed-length word buffer bounded on both Lean target widths. -/
def zeroWords (n : Nat) (small : n < 2^29 := by omega) : FixedWords n :=
  ⟨zeroBytes (8*n), zeroBytes_size _, small⟩

/-- A fixed buffer of little-endian 32-bit Boolean assignments. -/
abbrev FixedDWords (n : Nat) := {a : ByteArray // a.size = 4*n ∧ n < 2^30}

/-- Allocate a fixed contiguous assignment buffer. -/
def zeroDWords (n : Nat) (small : n < 2^30 := by omega) : FixedDWords n :=
  ⟨zeroBytes (4*n),zeroBytes_size _,small⟩

/-- A proved assignment coordinate has its exact machine byte offset. -/
theorem dwordOffset (a : FixedDWords n) (i : USize) (hi : i < n.toUSize) :
    (4*i).toNat = 4*i.toNat := by
  have hn : n < USize.size := lt_of_lt_of_le (lt_trans a.property.2 (by decide)) USize.le_size
  have hi : i.toNat < n := by
    simpa only [USize.lt_iff_toNat_lt,Nat.toUSize,USize.toNat_ofNat_of_lt' hn] using hi
  have h4 : (4 : USize).toNat = 4 := USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)
  rw [USize.toNat_mul,h4]
  change (4*i.toNat)%USize.size = 4*i.toNat
  exact Nat.mod_eq_of_lt (by have := a.property.2; have := USize.le_size; omega)

/-- Load one 32-bit assignment with an erased machine bounds proof. -/
@[inline] def getUDWord (a : FixedDWords n) (i : USize) (hi : i < n.toUSize) : UInt32 :=
  a.val.ugetUInt32LE (4*i) (by
    rw [dwordOffset a i hi,a.property.1]
    have hn : n < USize.size := lt_of_lt_of_le (lt_trans a.property.2 (by decide)) USize.le_size
    have : i.toNat < n := by
      simpa only [USize.lt_iff_toNat_lt,Nat.toUSize,USize.toNat_ofNat_of_lt' hn] using hi
    omega)

/-- Read a checked assignment coordinate, returning zero outside the buffer. -/
@[inline] def readUDWord (a : FixedDWords n) (i : USize) : UInt32 :=
  if hi : i < n.toUSize then getUDWord a i hi else 0

/-- A proved assignment read is the checked read at the same coordinate. -/
theorem getUDWord_eq_readUDWord (a : FixedDWords n) (i : USize) (hi : i < n.toUSize) :
    getUDWord a i hi = readUDWord a i := by
  rw [readUDWord,dite_eq_left hi]

/-- Store an assignment with an erased bounds proof and unique buffer ownership. -/
@[inline] def setUDWord (a : FixedDWords n) (i : USize) (hi : i < n.toUSize) (v : UInt32) : FixedDWords n :=
  let bytes := a.val.usetUInt32LE (4*i) v (by
    rw [dwordOffset a i hi,a.property.1]
    have hn : n < USize.size := lt_of_lt_of_le (lt_trans a.property.2 (by decide)) USize.le_size
    have : i.toNat < n := by
      simpa only [USize.lt_iff_toNat_lt,Nat.toUSize,USize.toNat_ofNat_of_lt' hn] using hi
    omega)
  ⟨bytes,by simp only [bytes,ByteArray.usetUInt32LE,ByteArray.size_setUInt32LE!,a.property.1],a.property.2⟩

/-- Update a checked assignment coordinate. -/
@[inline] def writeUDWord (a : FixedDWords n) (i : USize) (v : UInt32) : FixedDWords n :=
  if hi : i < n.toUSize then setUDWord a i hi v else a

/-- Machine byte offsets do not wrap for a word in a fixed buffer. -/
theorem wordOffsets (a : FixedWords n) (i : USize) (hi : i < n.toUSize) :
    (8*i).toNat = 8*i.toNat ∧ (8*i+4).toNat = 8*i.toNat+4 := by
  have hn : n < USize.size := lt_of_lt_of_le (lt_trans a.property.2 (by decide)) USize.le_size
  have hi : i.toNat < n := by
    simpa only [USize.lt_iff_toNat_lt, Nat.toUSize, USize.toNat_ofNat_of_lt' hn] using hi
  have h8 : (8 : USize).toNat = 8 := USize.toNat_ofNat_of_lt (n := 8) (lt_of_lt_of_le (by decide) USize.le_size)
  have h4 : (4 : USize).toNat = 4 := USize.toNat_ofNat_of_lt (n := 4) (lt_of_lt_of_le (by decide) USize.le_size)
  have hb : 8*i.toNat+4 < USize.size := by
    have := a.property.2
    have := USize.le_size
    omega
  have ho : (8*i).toNat = 8*i.toNat := by
    rw [USize.toNat_mul, h8]
    change (8*i.toNat) % USize.size = 8*i.toNat
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨ho, ?_⟩
  rw [USize.toNat_add, ho, h4]
  change (8*i.toNat+4) % USize.size = 8*i.toNat+4
  exact Nat.mod_eq_of_lt hb

/-- Load a scalar word whose machine coordinate is in bounds. -/
@[inline] def getUWord (a : FixedWords n) (i : USize) (h : i < n.toUSize) : UInt64 :=
    let bound := wordOffsets a i h
    (a.val.ugetUInt32LE (8*i) (by
      rw [bound.1, a.property.1]
      have hn : n < USize.size := lt_of_lt_of_le (lt_trans a.property.2 (by decide)) USize.le_size
      have : i.toNat < n := by simpa only [USize.lt_iff_toNat_lt, Nat.toUSize, USize.toNat_ofNat_of_lt' hn] using h
      omega)).toUInt64 |||
      ((a.val.ugetUInt32LE (8*i+4) (by
        rw [bound.2, a.property.1]
        have hn : n < USize.size := lt_of_lt_of_le (lt_trans a.property.2 (by decide)) USize.le_size
        have : i.toNat < n := by simpa only [USize.lt_iff_toNat_lt, Nat.toUSize, USize.toNat_ofNat_of_lt' hn] using h
        omega)).toUInt64 <<< 32)

/-- Load a scalar word using machine offsets and one machine bounds check. -/
@[inline] def readUWord (a : FixedWords n) (i : USize) : UInt64 :=
  if h : i < n.toUSize then getUWord a i h else 0

/-- A proved in-bounds read is exactly the checked scalar read. -/
theorem getUWord_eq_readUWord (a : FixedWords n) (i : USize) (h : i < n.toUSize) :
    getUWord a i h = readUWord a i := by
  rw [readUWord, dite_eq_left h]

/-- Small natural coordinates fit both supported machine widths without reduction. -/
theorem usize_toNat_lt {n b : Nat} (hn : n < b) (hb : b ≤ 2^32) : (USize.ofNat n).toNat < b := by
  rw [USize.toNat_ofNat_of_lt' (n := n) (lt_of_lt_of_le (lt_of_lt_of_le hn hb) USize.le_size)]
  exact hn

/-- Update an in-bounds scalar with its bounds proof erased from the native stores. -/
@[inline] def setUWord (a : FixedWords n) (i : USize) (h : i < n.toUSize) (v : UInt64) : FixedWords n :=
  have hn : n < USize.size := lt_of_lt_of_le (lt_trans a.property.2 (by decide)) USize.le_size
  have hi : i.toNat < n := by simpa only [USize.lt_iff_toNat_lt, Nat.toUSize, USize.toNat_ofNat_of_lt' hn] using h
  let bound := wordOffsets a i h
  let lower := a.val.usetUInt32LE (8*i) v.toUInt32 (by rw [bound.1, a.property.1]; omega)
  let bytes := lower.usetUInt32LE (8*i+4) (v >>> 32).toUInt32 (by
    simp only [lower, ByteArray.usetUInt32LE, ByteArray.size_setUInt32LE!]
    rw [bound.2, a.property.1]
    omega)
  ⟨bytes, by simp only [bytes, lower, ByteArray.usetUInt32LE, ByteArray.size_setUInt32LE!, a.property.1], a.property.2⟩

/-- Update a scalar word while retaining only the uniquely owned byte array at runtime. -/
@[inline] def writeUWord (a : FixedWords n) (i : USize) (v : UInt64) : FixedWords n :=
  if h : i < n.toUSize then setUWord a i h v else a

/-- A proved in-bounds store is exactly the checked scalar store. -/
theorem setUWord_eq_writeUWord (a : FixedWords n) (i : USize) (h : i < n.toUSize) (v : UInt64) :
    setUWord a i h v = writeUWord a i v := by
  rw [writeUWord, dite_eq_left h]

/-- Load a scalar at a protocol-level natural coordinate. -/
@[inline] def readWord (a : FixedWords n) (i : Nat) : UInt64 := readUWord a i.toUSize

/-- Update a scalar at a protocol-level natural coordinate. -/
@[inline] def writeWord (a : FixedWords n) (i : Nat) (v : UInt64) : FixedWords n := writeUWord a i.toUSize v

/-- Contiguous extension coefficients with an exact element count. -/
structure PackedE where
  /-- Number of extension elements. -/
  size : Nat
  /-- Constant, linear and quadratic words of each element. -/
  data : WordExt3.Buffer size

namespace PackedE

/-- Allocate a zero-filled extension table. -/
def zeros (n : Nat) : PackedE :=
  ⟨n, ⟨⟨3*n, zeroBytes (24*n), by rw [zeroBytes_size]; omega⟩, rfl⟩⟩

/-- The empty table is the default value used by checked-index panics. -/
instance : Inhabited PackedE := ⟨zeros 0⟩

/-- Load an extension element at a checked numeric coordinate. -/
@[inline] def get (a : PackedE) (i : Nat) : WordExt3 :=
  if h : i < a.size then WordExt3.read a.data ⟨i,h⟩ else panic! "extension table index"

/-- Store an extension element without boxing its three coefficient words. -/
@[inline] def set (a : PackedE) (i : Nat) (v : WordExt3) : PackedE :=
  if h : i < a.size then
    ⟨a.size, Packed.write (Packed.write (Packed.write a.data
      ⟨3*i, by omega⟩ v.c0) ⟨3*i+1, by omega⟩ v.c1) ⟨3*i+2, by omega⟩ v.c2⟩
  else panic! "extension table index"

/-- Materialize one immutable array at the packed-table boundary. -/
def ofArray (a : Array WordExt3) : PackedE :=
  ⟨a.size, WordExt3.ofFn a.size fun i => a[i.val]⟩

/-- Recover retained scalar values at a protocol boundary. -/
def toArray (a : PackedE) : Array WordExt3 := Array.ofFn fun i : Fin a.size => a.get i.val

end PackedE

/-- One row-major coordinate interpolated with a prepared extension multiplier. -/
@[inline] def foldPackedCell (table : PackedE) (width : Nat) (map : CompStark.Sumcheck.Prepared) (i : Nat) : WordExt3 :=
  let offset := 2*(i/width)*width+i%width
  let a := table.get offset
  WordExt3.add a (map.mul (WordExt3.add a (table.get (offset+width))))

/-- Fill the result in descending coordinate order with scalar loop state. -/
def foldPackedLoop (table : PackedE) (width : Nat) (map : CompStark.Sumcheck.Prepared) : Nat → PackedE → PackedE
  | 0, out => out
  | n+1, out => foldPackedLoop table width map n (out.set n (foldPackedCell table width map n))

/-- Fold a row-major table by one challenge, preparing its multiplier once. -/
def foldPacked (table : PackedE) (width : Nat) (r : WordExt3) : PackedE :=
  let count := table.size/(2*width)*width
  foldPackedLoop table width (CompStark.Sumcheck.prepare r) count (PackedE.zeros count)

end CompStark.Keccak.GkrProver
