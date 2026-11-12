/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.Packed
public import CompStark.Keccak.GkrProver.Kernels
import all CompPoly.Fields.Binary.BF64.WordExt3Dot

/-! Exact coordinate semantics of the native extension buffers. -/

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64

/-- Raw zero allocation agrees with the specification's boxed zero array. -/
theorem zeroBytes_data (n : Nat) : (zeroBytes n).data = Array.replicate n 0 := by
  rw [zeroBytes]
  split
  · rename_i h
    subst n
    rfl
  · have ih := zeroBytes_data (n/2)
    split
    · simp only [ByteArray.data_append, ih, Array.replicate_append_replicate]
      congr 1
      omega
    · change ((zeroBytes (n/2) ++ zeroBytes (n/2)).data).push 0 = _
      rw [ByteArray.data_append, ih, Array.replicate_append_replicate, ← Array.replicate_succ]
      congr 1
      omega
termination_by n

/-- Updating an extension buffer changes exactly its selected element. -/
theorem PackedE.get_set (a : PackedE) (i j : Nat) (hi : i < a.size) (hj : j < a.size) (v : WordExt3) :
    (a.set i v).get j = if i = j then v else a.get j := by
  have he (u v : Nat) (hu : u < 3) (hv : v < 3) :
      3*i+u = 3*j+v ↔ i=j ∧ u=v := by omega
  simp only [PackedE.set, hi, ↓reduceDIte]
  simp only [PackedE.get, hj, ↓reduceDIte, WordExt3.read, Packed.read_write, Fin.ext_iff]
  have h00 := he 0 0 (by omega) (by omega)
  have h01 := he 0 1 (by omega) (by omega)
  have h02 := he 0 2 (by omega) (by omega)
  have h10 := he 1 0 (by omega) (by omega)
  have h11 := he 1 1 (by omega) (by omega)
  have h12 := he 1 2 (by omega) (by omega)
  have h20 := he 2 0 (by omega) (by omega)
  have h21 := he 2 1 (by omega) (by omega)
  have h22 := he 2 2 (by omega) (by omega)
  simp only [Nat.add_zero] at h00 h01 h02 h10 h20
  simp only [h00, h01, h02, h10, h11, h12, h20, h21, h22]
  by_cases h : i=j
  · subst j
    simp only [and_self, and_false, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [h, false_and, ite_false]

/-- Materializing an array preserves every in-bounds extension element. -/
theorem PackedE.get_ofArray (a : Array WordExt3) (i : Nat) (hi : i < a.size) :
    (PackedE.ofArray a).get i = a[i] := by
  simp only [PackedE.ofArray, PackedE.get, hi, ↓reduceDIte, WordExt3.read_ofFn]
/-- Updating an in-bounds extension coordinate preserves the element count. -/
theorem PackedE.size_set (a : PackedE) (i : Nat) (v : WordExt3) (hi : i < a.size) :
    (a.set i v).size = a.size := by
  simp only [PackedE.set, hi, ↓reduceDIte]

/-- The folding loop retains the exact result-buffer length. -/
theorem foldPackedLoop_size (table : PackedE) (width : Nat) (map : CompStark.Sumcheck.Prepared)
    (n : Nat) (out : PackedE) (hn : n ≤ out.size) :
    (foldPackedLoop table width map n out).size = out.size := by
  induction n generalizing out with
  | zero => rfl
  | succ n ih =>
    rw [foldPackedLoop, ih _ (by rw [PackedE.size_set _ _ _ (by omega)]; omega),
      PackedE.size_set _ _ _ (by omega)]

/-- The folding loop computes each selected coordinate and preserves the suffix. -/
theorem foldPackedLoop_get (table : PackedE) (width : Nat) (map : CompStark.Sumcheck.Prepared)
    (n : Nat) (out : PackedE) (hn : n ≤ out.size) (i : Nat) (hi : i < out.size) :
    (foldPackedLoop table width map n out).get i =
      if i < n then foldPackedCell table width map i else out.get i := by
  induction n generalizing out with
  | zero => simp only [foldPackedLoop, Nat.not_lt_zero, ite_false]
  | succ n ih =>
    have hn' : n < out.size := by omega
    rw [foldPackedLoop, ih _ (by rw [PackedE.size_set _ _ _ hn']; omega)
      (by rw [PackedE.size_set _ _ _ hn']; exact hi)]
    by_cases h : i < n
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, PackedE.get_set _ _ _ hn' hi]
      by_cases he : i=n
      · subst i
        rw [ite_eq_left rfl, ite_eq_left (by omega)]
      · rw [ite_eq_right (Ne.symm he), ite_eq_right (by omega)]

/-- The packed fold has the same row-major shape as the specification fold. -/
theorem foldPacked_size (table : PackedE) (width : Nat) (r : WordExt3) :
    (foldPacked table width r).size = table.size/(2*width)*width :=
  foldPackedLoop_size _ _ _ _ _ (Nat.le_refl _)

/-- Every native fold coordinate is the exact multilinear affine interpolation. -/
theorem foldPacked_get (table : PackedE) (width : Nat) (r : WordExt3)
    (i : Nat) (hi : i < table.size/(2*width)*width) :
    (foldPacked table width r).get i =
      line (table.get (2*(i/width)*width+i%width))
        (table.get (2*(i/width)*width+i%width+width)) r := by
  rw [foldPacked, foldPackedLoop_get table width (CompStark.Sumcheck.prepare r) _ _ (by rfl) i hi, ite_eq_left hi]
  simp only [foldPackedCell, CompStark.Sumcheck.prepared_mul_eq, line]
  rfl

/-- Materializing a packed table preserves its in-bounds element values. -/
theorem PackedE.get_toArray (a : PackedE) (i : Nat) (hi : i < a.size) :
    a.toArray[i]! = a.get i := by
  rw [getElem!_pos _ _ (by simpa only [PackedE.toArray, Array.size_ofFn] using hi)]
  exact Array.getElem_ofFn _

/-- Both endpoints of a retained row-major fold coordinate lie in the source table. -/
theorem fold_indices {size width i : Nat} (hi : i < size/(2*width)*width) :
    2*(i/width)*width+i%width+width < size := by
  have hw : 0 < width := by
    by_contra h
    have hz : width=0 := by omega
    simp only [hz, Nat.mul_zero, Nat.not_lt_zero] at hi
  have hr : i/width < size/(2*width) := (Nat.div_lt_iff_lt_mul hw).mpr hi
  have hm := Nat.mul_le_mul_right (2*width) (Nat.succ_le_of_lt hr)
  have hb := Nat.div_mul_le_self size (2*width)
  have hrem := Nat.mod_lt i hw
  nlinarith

/-- The complete packed folding kernel equals the specification array fold. -/
theorem foldPacked_toArray (table : PackedE) (width : Nat) (r : WordExt3) :
    (foldPacked table width r).toArray = fold table.toArray width r := by
  apply Array.ext
  · simp only [PackedE.toArray, Array.size_ofFn, foldPacked_size, fold]
  · intro i hi hj
    have hcount : i < table.size/(2*width)*width := by
      simpa only [PackedE.toArray, Array.size_ofFn, foldPacked_size] using hi
    have high := fold_indices hcount
    have low : 2*(i/width)*width+i%width < table.size := by omega
    simp only [PackedE.toArray, fold, Array.getElem_ofFn]
    change (foldPacked table width r).get i =
      line table.toArray[2*(i/width)*width+i%width]!
        table.toArray[(2*(i/width)+1)*width+i%width]! r
    rw [foldPacked_get table width r i hcount]
    have index : (2*(i/width)+1)*width+i%width = 2*(i/width)*width+i%width+width := by ring
    rw [index, PackedE.get_toArray _ _ low, PackedE.get_toArray _ _ high]

/-- A machine assignment read is the exact natural-coordinate little-endian load. -/
theorem getUDWord_eq_getUInt32LE (a : FixedDWords n) (i : USize) (hi : i < n.toUSize) :
    getUDWord a i hi = a.val.getUInt32LE! (4*i.toNat) := by
  simp only [getUDWord,ByteArray.ugetUInt32LE,dwordOffset a i hi]

/-- A machine assignment store changes exactly its four natural-coordinate bytes. -/
theorem setUDWord_val (a : FixedDWords n) (i : USize) (hi : i < n.toUSize) (v : UInt32) :
    (setUDWord a i hi v).val = a.val.setUInt32LE! (4*i.toNat) v := by
  simp only [setUDWord,ByteArray.usetUInt32LE,dwordOffset a i hi]

/-- Updating a 32-bit assignment preserves every other complete assignment. -/
theorem getUDWord_setUDWord (a : FixedDWords n) (i j : USize)
    (hi : i < n.toUSize) (hj : j < n.toUSize) (v : UInt32) :
    getUDWord (setUDWord a i hi v) j hj = if i = j then v else getUDWord a j hj := by
  rw [getUDWord_eq_getUInt32LE,setUDWord_val,getUDWord_eq_getUInt32LE]
  have hn : n < USize.size := lt_of_lt_of_le (lt_trans a.property.2 (by decide)) USize.le_size
  have hb : 4*j.toNat+4 ≤ a.val.size := by
    have hj' : j.toNat < n := by
      simpa only [USize.lt_iff_toNat_lt,Nat.toUSize,USize.toNat_ofNat_of_lt' hn] using hj
    rw [a.property.1]
    omega
  by_cases he : i = j
  · subst j
    rw [ite_eq_left rfl,ByteArray.getUInt32LE!_setUInt32LE!_self _ _ _ hb]
  · rw [ite_eq_right he,ByteArray.getUInt32LE!_setUInt32LE!_of_disjoint _ _ _ _ hb]
    have hne : i.toNat ≠ j.toNat := fun h => he (USize.toNat_inj.mp h)
    omega

/-- View a fixed machine buffer as the certified natural-coordinate buffer. -/
def FixedWords.toBuffer (a : FixedWords n) : Packed.Buffer n :=
  ⟨⟨n, a.val, a.property.1⟩, rfl⟩
/-- Machine and natural coordinates read identical scalar words. -/
theorem getUWord_toBuffer (a : FixedWords n) (i : USize) (hi : i < n.toUSize) :
    getUWord a i hi = (Packed.read a.toBuffer ⟨i.toNat, by
      have hn : n < USize.size := lt_of_lt_of_le (lt_trans a.property.2 (by decide)) USize.le_size
      simpa only [USize.lt_iff_toNat_lt, Nat.toUSize, USize.toNat_ofNat_of_lt' hn] using hi⟩).val := by
  simp only [getUWord, ByteArray.ugetUInt32LE, (wordOffsets a i hi).1, (wordOffsets a i hi).2]
  rfl
/-- Machine and natural stores produce identical complete byte buffers. -/
theorem setUWord_toBuffer (a : FixedWords n) (i : USize) (hi : i < n.toUSize) (v : UInt64) :
    (setUWord a i hi v).toBuffer = Packed.write a.toBuffer ⟨i.toNat, by
      have hn : n < USize.size := lt_of_lt_of_le (lt_trans a.property.2 (by decide)) USize.le_size
      simpa only [USize.lt_iff_toNat_lt, Nat.toUSize, USize.toNat_ofNat_of_lt' hn] using hi⟩ ⟨v⟩ := by
  simp only [setUWord, ByteArray.usetUInt32LE, (wordOffsets a i hi).1, (wordOffsets a i hi).2]
  rfl
/-- A machine store changes exactly its selected scalar coordinate. -/
theorem getUWord_setUWord (a : FixedWords n) (i j : USize)
    (hi : i < n.toUSize) (hj : j < n.toUSize) (v : UInt64) :
    getUWord (setUWord a i hi v) j hj = if i = j then v else getUWord a j hj := by
  rw [getUWord_toBuffer, setUWord_toBuffer, Packed.read_write]
  simp only [Fin.ext_iff, USize.toNat_inj, apply_ite, ← getUWord_toBuffer a j hj]
  split <;> rfl
/-- Natural coordinates of a fixed buffer fit both supported machine widths. -/
theorem FixedWords.index_bound (a : FixedWords n) (i : Nat) (hi : i < n) :
    i.toUSize < n.toUSize := by
  have hn : n < USize.size := lt_of_lt_of_le (lt_trans a.property.2 (by decide)) USize.le_size
  rw [USize.lt_iff_toNat_lt]
  change i % USize.size < n % USize.size
  rw [Nat.mod_eq_of_lt (lt_trans hi hn), Nat.mod_eq_of_lt hn]
  exact hi
/-- Natural-coordinate stores retain all other fixed-buffer words. -/
theorem readWord_writeWord (a : FixedWords n) (i j : Nat) (hi : i < n) (hj : j < n) (v : UInt64) :
    readWord (writeWord a i v) j = if i = j then v else readWord a j := by
  have hib := a.index_bound i hi
  have hjb := a.index_bound j hj
  have hn : n < USize.size := lt_of_lt_of_le (lt_trans a.property.2 (by decide)) USize.le_size
  have he : i.toUSize = j.toUSize ↔ i = j := by
    rw [← USize.toNat_inj]
    change (i % USize.size = j % USize.size) ↔ i = j
    rw [Nat.mod_eq_of_lt (lt_trans hi hn), Nat.mod_eq_of_lt (lt_trans hj hn)]
  simp only [readWord, writeWord, ← setUWord_eq_writeUWord a _ hib,
    ← getUWord_eq_readUWord _ _ hjb, getUWord_setUWord, he]
/-- Every in-bounds byte of the raw zero allocator is zero. -/
theorem zeroBytes_get (n i : Nat) (hi : i < n) : (zeroBytes n).get! i = 0 := by
  change (zeroBytes n).data[i]! = 0
  rw [zeroBytes_data, getElem!_pos _ _ (by simpa only [Array.size_replicate] using hi)]
  exact Array.getElem_replicate _
/-- Every in-bounds word of a zero machine buffer is zero. -/
theorem getUWord_zeroWords (n : Nat) (hn : n < 2^29) (i : USize) (hi : i < n.toUSize) :
    getUWord (zeroWords n hn) i hi = 0 := by
  have hn' : n < USize.size := lt_of_lt_of_le (lt_trans hn (by decide)) USize.le_size
  have hi' : i.toNat < n := by
    simpa only [USize.lt_iff_toNat_lt, Nat.toUSize, USize.toNat_ofNat_of_lt' hn'] using hi
  simp only [getUWord, ByteArray.ugetUInt32LE, (wordOffsets (zeroWords n hn) i hi).1,
    (wordOffsets (zeroWords n hn) i hi).2, zeroWords, ByteArray.getUInt32LE!]
  simp only [zeroBytes_size, show 8*i.toNat+4 ≤ 8*n by omega,
    show 8*i.toNat+4+4 ≤ 8*n by omega, ite_true,
    zeroBytes_get _ _ (show 8*i.toNat < 8*n by omega),
    zeroBytes_get _ _ (show 8*i.toNat+1 < 8*n by omega),
    zeroBytes_get _ _ (show 8*i.toNat+2 < 8*n by omega),
    zeroBytes_get _ _ (show 8*i.toNat+3 < 8*n by omega),
    zeroBytes_get _ _ (show 8*i.toNat+4 < 8*n by omega),
    zeroBytes_get _ _ (show 8*i.toNat+4+1 < 8*n by omega),
    zeroBytes_get _ _ (show 8*i.toNat+4+2 < 8*n by omega),
    zeroBytes_get _ _ (show 8*i.toNat+4+3 < 8*n by omega)]
  rfl

/-- Every in-bounds 32-bit assignment of an empty tensor is zero. -/
theorem getUDWord_zeroDWords (n : Nat) (hn : n < 2^30) (i : USize) (hi : i < n.toUSize) :
    getUDWord (zeroDWords n hn) i hi = 0 := by
  have hn' : n < USize.size := lt_of_lt_of_le (lt_trans hn (by decide)) USize.le_size
  have hi' : i.toNat < n := by
    simpa only [USize.lt_iff_toNat_lt,Nat.toUSize,USize.toNat_ofNat_of_lt' hn'] using hi
  rw [getUDWord_eq_getUInt32LE]
  simp only [zeroDWords,ByteArray.getUInt32LE!,zeroBytes_size,
    show 4*i.toNat+4 ≤ 4*n by omega,ite_true,
    zeroBytes_get _ _ (show 4*i.toNat < 4*n by omega),
    zeroBytes_get _ _ (show 4*i.toNat+1 < 4*n by omega),
    zeroBytes_get _ _ (show 4*i.toNat+2 < 4*n by omega),
    zeroBytes_get _ _ (show 4*i.toNat+3 < 4*n by omega)]
  rfl

end CompStark.Keccak.GkrProver
