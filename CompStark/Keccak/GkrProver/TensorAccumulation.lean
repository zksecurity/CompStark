/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.WeightMapEval

/-! Native position-by-position accumulation of the ternary quadratic tensor. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators

/-- The three scalar native tensor accumulators add one complete extension value. -/
theorem accumulateTensor_triple (q : Fin 81) (out : FixedWords 243) (v : W) :
    accumulateTensor q.val.toUSize
      (by rw [usize_small q.val (by have := q.isLt; omega)]; exact q.isLt)
      (accumulateTensor q.val.toUSize
        (by rw [usize_small q.val (by have := q.isLt; omega)]; exact q.isLt)
        (accumulateTensor q.val.toUSize
          (by rw [usize_small q.val (by have := q.isLt; omega)]; exact q.isLt)
          out 0 (usize_toNat_lt (by decide) (by decide)) v.c0.val)
        1 (usize_toNat_lt (by decide) (by decide)) v.c1.val)
      2 (usize_toNat_lt (by decide) (by decide)) v.c2.val =
      storeTriple out q.val (tripleValue out q.val+v) := by
  have hq := q.isLt
  have h1 (v0 : UInt64) : readWord (writeWord out (3*q.val) v0) (3*q.val+1) =
      readWord out (3*q.val+1) := by
    rw [readWord_writeWord _ _ _ (by omega) (by omega),ite_eq_right (by omega)]
  have h2 (v0 v1 : UInt64) : readWord (writeWord (writeWord out (3*q.val) v0)
      (3*q.val+1) v1) (3*q.val+2) = readWord out (3*q.val+2) := by
    rw [readWord_writeWord _ _ _ (by omega) (by omega),ite_eq_right (by omega),
      readWord_writeWord _ _ _ (by omega) (by omega),ite_eq_right (by omega)]
  simp only [accumulateTensor_eq,storeTriple,tripleValue]
  simp only [readWord,writeWord,Nat.toUSize,USize.ofNat_add,USize.ofNat_mul,
    show USize.ofNat 3 = (3 : USize) from rfl,
    show USize.ofNat 1 = (1 : USize) from rfl,
    show USize.ofNat 2 = (2 : USize) from rfl] at h1 h2 ⊢
  simp only [USize.add_zero]
  rw [h1,h2]
  rfl

/-- The weighted RMFE product stored for one position at one compact ternary assignment. -/
def tensorPositionValue (maps : FixedWords (1600*6*256*3)) (mixed : FixedDWords (81*1600))
    (products : RmfeProducts) (base : USize) (hb : base.toNat ≤ 7372800-4608)
    (j1 j2 : USize) (q : Nat) : W :=
  evalWeightValue maps base hb (products.mul
    (readUDWord mixed (1600*q.toUSize+j1)).toUInt64
    (readUDWord mixed (1600*q.toUSize+j2)).toUInt64)

/-- A bounded machine byte read agrees with its natural checked read. -/
theorem byteArray_uget_nat (bytes : ByteArray) (i : Nat) (hi : i < 2^32)
    (hb : i.toUSize.toNat < bytes.size) :
    bytes.uget i.toUSize hb = bytes[i]! := by
  have hn := usize_small i hi
  rw [getElem!_pos bytes i (by omega)]
  cases bytes with
  | mk data =>
    have hb' : i < data.size := by
      change i.toUSize.toNat < data.size at hb
      omega
    change data[i.toUSize.toNat] = data[i]
    simp only [hn]

/-- A native position step is one complete extension-value addition at its ternary assignment. -/
theorem earlyPosition_step (maps : FixedWords (1600*6*256*3)) (mixed : FixedDWords (81*1600))
    (products : RmfeProducts) (j1 j2 : USize) (hj1 : j1.toNat < 1600) (hj2 : j2.toNat < 1600)
    (base : USize) (hb : base.toNat ≤ 7372800-4608) (q : Fin 81) (out : FixedWords 243) :
    earlyPosition maps mixed products j1 j2 hj1 hj2 base hb q.val.toUSize out =
      earlyPosition maps mixed products j1 j2 hj1 hj2 base hb (q.val+1).toUSize
        (if ternaryBinary[q.val]! = 1 then out else
          storeTriple out q.val (tripleValue out q.val+tensorPositionValue maps mixed products base hb j1 j2 q.val)) := by
  have hq : q.val.toUSize < 81 := by
    rw [USize.lt_iff_toNat_lt,usize_small q.val (by have := q.isLt; omega)]
    simpa only [USize.reduceToNat] using q.isLt
  rw [earlyPosition,dite_eq_left hq]
  have hnext : q.val.toUSize+1 = (q.val+1).toUSize := by
    simp only [Nat.toUSize,USize.ofNat_add]
    rfl
  rw [hnext]
  simp only [tensorWord_eq]
  have hflag : ternaryBinary.uget q.val.toUSize (by
      simpa only [ternaryBinary,ByteArray.size,Array.size_ofFn] using
        (show q.val.toUSize.toNat < 81 by
          rw [usize_small q.val (by have := q.isLt; omega)]; exact q.isLt)) =
      ternaryBinary[q.val]! := by
    exact byteArray_uget_nat _ q.val (by have := q.isLt; omega) _
  rw [hflag]
  by_cases hf : ternaryBinary[q.val]! = 1
  · simp only [hf,ite_true]
  · simp only [hf,ite_false]
    have h := accumulateTensor_triple q out (tensorPositionValue maps mixed products base hb j1 j2 q.val)
    exact congrArg (earlyPosition maps mixed products j1 j2 hj1 hj2 base hb (q.val+1).toUSize) h

/-- A complete native position traversal adds precisely the selected nonbinary tensor endpoint. -/
theorem earlyPosition_get (maps : FixedWords (1600*6*256*3)) (mixed : FixedDWords (81*1600))
    (products : RmfeProducts) (j1 j2 : USize) (hj1 : j1.toNat < 1600) (hj2 : j2.toNat < 1600)
    (base : USize) (hb : base.toNat ≤ 7372800-4608) (start : Nat) (hs : start ≤ 81)
    (out : FixedWords 243) (q : Fin 81) :
    tripleValue (earlyPosition maps mixed products j1 j2 hj1 hj2 base hb start.toUSize out) q.val =
      tripleValue out q.val + if start ≤ q.val ∧ ternaryBinary[q.val]! ≠ 1 then
        tensorPositionValue maps mixed products base hb j1 j2 q.val else 0 := by
  by_cases hstart : start < 81
  · rw [earlyPosition_step maps mixed products j1 j2 hj1 hj2 base hb ⟨start,hstart⟩ out,
      earlyPosition_get maps mixed products j1 j2 hj1 hj2 base hb (start+1) (by omega)]
    by_cases hf : ternaryBinary[start]! = 1
    · rw [ite_eq_left hf]
      have he : (start+1 ≤ q.val ∧ ternaryBinary[q.val]! ≠ 1) ↔
          (start ≤ q.val ∧ ternaryBinary[q.val]! ≠ 1) := by
        constructor
        · intro h; exact ⟨by omega,h.2⟩
        · intro h
          have hn : q.val ≠ start := by intro he; rw [he,hf] at h; exact h.2 rfl
          exact ⟨by omega,h.2⟩
      simp only [he]
    · rw [ite_eq_right hf,tripleValue_store _ _ _ _ (by omega) (by have := q.isLt; omega)]
      by_cases he : q.val = start
      · subst start
        rw [ite_eq_left rfl,
          ite_eq_right (show ¬(q.val+1 ≤ q.val ∧ ternaryBinary[q.val]! ≠ 1) by omega),
          ite_eq_left (show q.val ≤ q.val ∧ ternaryBinary[q.val]! ≠ 1 from ⟨le_rfl,hf⟩),add_zero]
      · rw [ite_eq_right he]
        have hcond : (start+1 ≤ q.val ∧ ternaryBinary[q.val]! ≠ 1) ↔
            (start ≤ q.val ∧ ternaryBinary[q.val]! ≠ 1) := by
          constructor <;> rintro ⟨hle,hflag⟩ <;> exact ⟨by omega,hflag⟩
        simp only [hcond]
  · have he : start = 81 := by omega
    subst start
    rw [earlyPosition,dite_eq_right (by rw [USize.lt_iff_toNat_lt,usize_small 81 (by decide)]; simp only [USize.reduceToNat,lt_self_iff_false,not_false_eq_true])]
    rw [ite_eq_right (by have := q.isLt; omega),add_zero]
termination_by 81-start

end CompStark.Keccak.GkrProver
