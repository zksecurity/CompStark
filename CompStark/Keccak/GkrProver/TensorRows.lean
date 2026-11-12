/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Keccak.GkrProver.TensorValues
public import CompStark.Keccak.GkrProver.NativeLoops
public import CompStark.Keccak.GkrProver.PackedWords
/-! Scalar accumulation of the position dimension of the early Keccak tensor. -/
@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
/-- Machine row shifts preserve bounded Keccak position coordinates. -/
theorem shiftU_small (j k : Nat) (hj : j < 1600) (hk : k < 5) :
    shiftU j.toUSize k.toUSize = (shift j k).toUSize := by
  have hs := USize.le_size
  have hshift : shift j k < 1600 := (CompStark.Keccak.Gkr.along ⟨j,hj⟩ k).isLt
  have hj' : j.toUSize.toNat = j := payloadIndex j (by omega)
  have hk' : k.toUSize.toNat = k := payloadIndex k (by omega)
  have h64 : (64 : USize).toNat = 64 := USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) hs)
  have h5 : (5 : USize).toNat = 5 := USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) hs)
  apply USize.toNat_inj.mp
  rw [payloadIndex (shift j k) (by omega)]
  simp only [shiftU, USize.toNat_add, USize.toNat_mul, USize.toNat_div, USize.toNat_mod, hj', hk', h64, h5]
  change (64*((((j/64%5+k)%USize.size)%5+(5*(j/64/5))%USize.size)%USize.size)%USize.size+j%64)%USize.size = shift j k
  unfold shift at hshift ⊢
  simp (disch := omega) only [Nat.mod_eq_of_lt]
/-- Weighted product at a total position coordinate of one ternary row. -/
@[inline] def tensorPositionAt (maps : FixedWords (1600*6*256*3))
    (mixed : FixedDWords (81*1600)) (products : RmfeProducts) (j q : Nat) : W :=
  let j := j%1600
  let base := (4608*j).toUSize
  have hb : base.toNat ≤ 7372800-4608 := by
    have hj : j < 1600 := Nat.mod_lt _ (by decide)
    rw [usize_small _ (by omega)]; omega
  let p := products.mul
    (readUDWord mixed (1600*q.toUSize+(shift j 1).toUSize)).toUInt64
    (readUDWord mixed (1600*q.toUSize+(shift j 2).toUSize)).toUInt64
  ⟨⟨evalWeightCoordinate maps base hb 0 (usize_toNat_lt (by decide) (by decide)) p⟩,
    ⟨evalWeightCoordinate maps base hb 1 (usize_toNat_lt (by decide) (by decide)) p⟩,
    ⟨evalWeightCoordinate maps base hb 2 (usize_toNat_lt (by decide) (by decide)) p⟩⟩
/-- A complete position update adds precisely its selected row value. -/
theorem tensorColumn_row (maps : FixedWords (1600*6*256*3))
    (mixed : FixedDWords (81*1600)) (products : RmfeProducts)
    (j : Nat) (q : Fin 81) (out : FixedWords 243) :
    tripleValue (tensorColumn maps mixed products j out) q.val = tripleValue out q.val +
      if ternaryBinary[q.val]! ≠ 1 then tensorPositionAt maps mixed products j q.val else 0 := by
  unfold tensorColumn
  have hz : (0 : USize) = (0 : Nat).toUSize := rfl
  rw [hz, earlyPosition_get _ _ _ _ _ _ _ _ _ 0 (by omega)]
  simp only [Nat.zero_le, true_and]
  rfl
/-- Every retained tensor row is the exact sum of its position contributions. -/
theorem tensorBlock_row (maps : FixedWords (1600*6*256*3))
    (mixed : FixedDWords (81*1600)) (products : RmfeProducts) (q : Fin 81) :
    tripleValue (tensorBlock maps mixed products) q.val =
      ∑ j ∈ Finset.range 1600,
        if ternaryBinary[q.val]! ≠ 1 then tensorPositionAt maps mixed products j q.val else 0 := by
  rw [tensorBlock, foldl_value_sum (fun out => tripleValue out q.val)
    (fun out j => tensorColumn maps mixed products j out)
    (fun j => if ternaryBinary[q.val]! ≠ 1 then tensorPositionAt maps mixed products j q.val else 0)
    (fun out j => tensorColumn_row maps mixed products j q out),
    tripleValue_zero _ _ _ (by have := q.isLt; omega), zero_add, list_range_sum]
/-- Hold all three row sums in scalar recursive arguments until the final result. -/
def tensorRowLoop (maps : FixedWords (1600*6*256*3)) (mixed : FixedDWords (81*1600))
    (products : RmfeProducts) (q : Nat) : Nat → UInt64 → UInt64 → UInt64 → W
  | 0, a0, a1, a2 => ⟨⟨a0⟩,⟨a1⟩,⟨a2⟩⟩
  | n+1, a0, a1, a2 =>
    let v := tensorPositionAt maps mixed products n q
    tensorRowLoop maps mixed products q n (a0 ^^^ v.c0.val) (a1 ^^^ v.c1.val) (a2 ^^^ v.c2.val)
/-- Scalar row accumulation is the complete finite position sum. -/
theorem tensorRowLoop_eq (maps : FixedWords (1600*6*256*3)) (mixed : FixedDWords (81*1600))
    (products : RmfeProducts) (q n : Nat) (a0 a1 a2 : UInt64) :
    tensorRowLoop maps mixed products q n a0 a1 a2 =
      (⟨⟨a0⟩,⟨a1⟩,⟨a2⟩⟩ : W) + ∑ j ∈ Finset.range n, tensorPositionAt maps mixed products j q := by
  induction n generalizing a0 a1 a2 with
  | zero => simp only [tensorRowLoop, Finset.range_zero, Finset.sum_empty, add_zero]
  | succ n ih =>
    rw [tensorRowLoop, ih, Finset.sum_range_succ]
    change ((⟨⟨a0⟩,⟨a1⟩,⟨a2⟩⟩ : W)+tensorPositionAt maps mixed products n q)+_ = _
    ac_rfl
/-- The two neighbor coordinates shared by every ternary tensor row. -/
def tensorShifts : FixedWords 3200 :=
  fixedWordsOfFn 3200 (by decide) (fun i => (shift (i.val/2) (i.val%2+1)).toUInt64)
/-- Native address of one shared neighbor coordinate. -/
@[inline] def tensorShiftIndex (j c : USize) : USize := 2*j+c
/-- Neighbor-index arithmetic is exact on both target widths. -/
theorem tensorShiftIndex_nat (j : USize) (hj : j.toNat < 1600) (c : USize) (hc : c.toNat < 2) :
    (tensorShiftIndex j c).toNat = 2*j.toNat+c.toNat := by
  have hs := USize.le_size
  have h2 : (2 : USize).toNat = 2 := USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) hs)
  rw [tensorShiftIndex, USize.toNat_add, USize.toNat_mul, h2]
  change ((2*j.toNat)%USize.size+c.toNat)%USize.size = 2*j.toNat+c.toNat
  have hm : 2*j.toNat < USize.size := by omega
  rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (by omega)]
/-- Load a precomputed neighbor coordinate with an erased native bound. -/
@[inline] def tensorShift (j : USize) (hj : j.toNat < 1600) (c : USize) (hc : c.toNat < 2) : USize :=
  (getUWord tensorShifts (tensorShiftIndex j c) (by
    rw [USize.lt_iff_toNat_lt, tensorShiftIndex_nat j hj c hc,
      USize.toNat_ofNat_of_lt' (lt_of_lt_of_le (by decide) USize.le_size)]
    omega)).toUSize
/-- Shared neighbor words are exactly the reference row shifts. -/
theorem tensorShift_eq (j : USize) (hj : j.toNat < 1600) (c : USize) (hc : c.toNat < 2) :
    tensorShift j hj c hc = (shift j.toNat (c.toNat+1)).toUSize := by
  rw [tensorShift, tensorShifts, getUWord_fixedWordsOfFn]
  simp only [tensorShiftIndex_nat j hj c hc]
  have hd : (2*j.toNat+c.toNat)/2 = j.toNat := by omega
  have hm : (2*j.toNat+c.toNat)%2 = c.toNat := by omega
  simp only [hd, hm, Nat.toUInt64, UInt64.toUSize_ofNat']
/-- Every shared neighbor coordinate remains inside its packed tensor row. -/
theorem tensorShift_bound (j : USize) (hj : j.toNat < 1600) (c : USize) (hc : c.toNat < 2) :
    (tensorShift j hj c hc).toNat < 1600 := by
  have h : shift j.toNat (c.toNat+1) < 1600 :=
    (CompStark.Keccak.Gkr.along ⟨j.toNat,hj⟩ (c.toNat+1)).isLt
  rw [tensorShift_eq, payloadIndex _ (by omega)]
  exact h
/-- Evaluate one weighted product using native position and row addresses. -/
@[inline] def tensorPositionNative (maps : FixedWords (1600*6*256*3))
    (mixed : FixedDWords (81*1600)) (products : RmfeProducts) (j : USize)
    (hj : j.toNat < 1600) (q : USize) (hq : q.toNat < 81) : W :=
  let base := 4608*j
  have hb : base.toNat ≤ 7372800-4608 := by
    have hn : (4608 : USize).toNat = 4608 := USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)
    simp only [base, USize.toNat_mul, hn]
    exact le_trans (Nat.mod_le _ _) (by omega)
  let p := products.mul
    (tensorWord mixed q hq
      (tensorShift j hj 0 (by simp only [USize.toNat_zero]; decide)) (tensorShift_bound j hj 0 (by simp only [USize.toNat_zero]; decide)))
    (tensorWord mixed q hq
      (tensorShift j hj 1 (by simp only [USize.toNat_one]; decide)) (tensorShift_bound j hj 1 (by simp only [USize.toNat_one]; decide)))
  ⟨⟨evalWeightCoordinate maps base hb 0 (usize_toNat_lt (by decide) (by decide)) p⟩,
    ⟨evalWeightCoordinate maps base hb 1 (usize_toNat_lt (by decide) (by decide)) p⟩,
    ⟨evalWeightCoordinate maps base hb 2 (usize_toNat_lt (by decide) (by decide)) p⟩⟩
/-- Native weighted position evaluation preserves the exact reference field element. -/
theorem tensorPositionNative_eq (maps : FixedWords (1600*6*256*3))
    (mixed : FixedDWords (81*1600)) (products : RmfeProducts) (j : USize)
    (hj : j.toNat < 1600) (q : USize) (hq : q.toNat < 81) :
    tensorPositionNative maps mixed products j hj q hq = tensorPositionAt maps mixed products j.toNat q.toNat := by
  have hb : (4608*j.toNat).toUSize = 4608*j := by
    simp only [Nat.toUSize, USize.ofNat_mul, USize.ofNat_toNat]
    rfl
  unfold tensorPositionAt tensorPositionNative
  simp only [Nat.mod_eq_of_lt hj, hb, tensorWord_eq, tensorShift_eq, USize.toNat_zero, USize.toNat_one, USize.ofNat_toNat,
    Nat.zero_add, Nat.reduceAdd]
/-- Native countdown state for one tensor row, with its bound erased from execution. -/
def tensorRowLoopU (maps : FixedWords (1600*6*256*3)) (mixed : FixedDWords (81*1600))
    (products : RmfeProducts) (q : USize) (hq : q.toNat < 81) (n : USize) (hn : n.toNat ≤ 1600)
    (a0 a1 a2 : UInt64) : W :=
  if hz : n = 0 then ⟨⟨a0⟩,⟨a1⟩,⟨a2⟩⟩ else
    have h1 : (1 : USize) ≤ n := by
      rw [USize.le_iff_toNat_le, USize.toNat_one]
      have hne : n.toNat ≠ 0 := fun h => hz (USize.toNat_inj.mp h)
      omega
    have hj : (n-1).toNat < 1600 := by
      rw [USize.toNat_sub_of_le _ _ h1, USize.toNat_one]
      have hp : 0 < n.toNat := by
        have hp1 : 1 ≤ n.toNat := by simpa only [USize.le_iff_toNat_le, USize.toNat_one] using h1
        omega
      omega
    let v := tensorPositionNative maps mixed products (n-1) hj q hq
    tensorRowLoopU maps mixed products q hq (n-1) (by omega)
      (a0 ^^^ v.c0.val) (a1 ^^^ v.c1.val) (a2 ^^^ v.c2.val)
termination_by n.toNat
decreasing_by
  rw [USize.toNat_sub_of_le _ _ h1, USize.toNat_one]
  have hp : 0 < n.toNat := by
    have hp1 : 1 ≤ n.toNat := by simpa only [USize.le_iff_toNat_le, USize.toNat_one] using h1
    omega
  omega
/-- Native countdown accumulation preserves all three reference row sums. -/
theorem tensorRowLoopU_eq (maps : FixedWords (1600*6*256*3)) (mixed : FixedDWords (81*1600))
    (products : RmfeProducts) (q : USize) (hq : q.toNat < 81) (n : USize) (hn : n.toNat ≤ 1600) (a0 a1 a2 : UInt64) :
    tensorRowLoopU maps mixed products q hq n hn a0 a1 a2 =
      tensorRowLoop maps mixed products q.toNat n.toNat a0 a1 a2 := by
  rw [tensorRowLoopU]
  split
  · rename_i hz
    subst n
    rfl
  · rename_i hz
    have h1 : (1 : USize) ≤ n := by
      rw [USize.le_iff_toNat_le, USize.toNat_one]
      have hne : n.toNat ≠ 0 := fun h => hz (USize.toNat_inj.mp h)
      omega
    have hj : (n-1).toNat < 1600 := by
      rw [USize.toNat_sub_of_le _ _ h1, USize.toNat_one]
      have hp : 0 < n.toNat := by
        have hp1 : 1 ≤ n.toNat := by simpa only [USize.le_iff_toNat_le, USize.toNat_one] using h1
        omega
      omega
    have he : n.toNat = (n-1).toNat+1 := by
      rw [USize.toNat_sub_of_le _ _ h1, USize.toNat_one]
      have hp : 0 < n.toNat := by
        have hp1 : 1 ≤ n.toNat := by simpa only [USize.le_iff_toNat_le, USize.toNat_one] using h1
        omega
      omega
    rw [tensorRowLoopU_eq, tensorPositionNative_eq]
    conv_rhs => rw [he, tensorRowLoop]
termination_by n.toNat
decreasing_by
  rw [USize.toNat_sub_of_le _ _ (by assumption), USize.toNat_one]
  have _hp : n.toNat ≠ 0 := fun h => (by assumption : n ≠ 0) (USize.toNat_inj.mp h)
  omega
/-- A natural packed coordinate reads the same word through the certified buffer view. -/
theorem readWord_buffer (a : FixedWords n) (i : Nat) (hi : i < n) :
    readWord a i = (Packed.read a.toBuffer ⟨i,hi⟩).val := by
  rw [readWord, ← getUWord_eq_readUWord a _ (a.index_bound i hi), getUWord_toBuffer]
  congr 2
  apply Fin.ext
  exact USize.toNat_ofNat_of_lt' (lt_trans hi (lt_of_lt_of_le (lt_trans a.property.2 (by decide)) USize.le_size))
/-- A complete packed tensor is determined by its 81 extension coordinates. -/
theorem tensorBuffer_ext (a b : FixedWords 243)
    (same : ∀ q : Fin 81, tripleValue a q.val = tripleValue b q.val) : a = b := by
  have h := packed_ext a.toBuffer.val b.toBuffer.val rfl (by
    intro i
    have hi : i.val < 243 := i.isLt
    have hs := same ⟨i.val/3,by omega⟩
    have hr : i.val%3 = 0 ∨ i.val%3 = 1 ∨ i.val%3 = 2 := by omega
    rcases hr with hr | hr | hr
    · have hc := congrArg (fun v : W => v.c0.val) hs
      change readWord a (3*(i.val/3)) = readWord b (3*(i.val/3)) at hc
      rw [show 3*(i.val/3) = i.val by omega, readWord_buffer a _ hi, readWord_buffer b _ hi] at hc
      exact congrArg Word.mk hc
    · have hc := congrArg (fun v : W => v.c1.val) hs
      change readWord a (3*(i.val/3)+1) = readWord b (3*(i.val/3)+1) at hc
      rw [show 3*(i.val/3)+1 = i.val by omega, readWord_buffer a _ hi, readWord_buffer b _ hi] at hc
      exact congrArg Word.mk hc
    · have hc := congrArg (fun v : W => v.c2.val) hs
      change readWord a (3*(i.val/3)+2) = readWord b (3*(i.val/3)+2) at hc
      rw [show 3*(i.val/3)+2 = i.val by omega, readWord_buffer a _ hi, readWord_buffer b _ hi] at hc
      exact congrArg Word.mk hc)
  exact Subtype.ext (congrArg Packed.bytes h)
/-- The native tensor position count is exact on both machine widths. -/
theorem tensorCount : (1600 : USize).toNat = 1600 :=
  USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)
/-- A normalized ternary row has an exact bounded machine coordinate. -/
theorem tensorResidue_bound (q : Nat) : (q%81).toUSize.toNat < 81 := by
  have h := Nat.mod_lt q (by decide : 0 < 81)
  rw [payloadIndex _ (by omega)]
  exact h
/-- Store each nonbinary tensor row only after all of its positions have been summed. -/
def tensorBlockRows (maps : FixedWords (1600*6*256*3)) (mixed : FixedDWords (81*1600))
    (products : RmfeProducts) : FixedWords 243 :=
  (List.range 81).foldl (fun out q => storeTriple out q
    (if ternaryBinary[q]! = 1 then 0 else
      tensorRowLoopU maps mixed products (q%81).toUSize (tensorResidue_bound q)
        1600 (by rw [tensorCount]) 0 0 0)) (zeroWords 243)
/-- Row-major scalar accumulation preserves every byte of the tensor block. -/
@[csimp] theorem tensorBlock_code : tensorBlock = tensorBlockRows := by
  funext maps mixed products
  apply tensorBuffer_ext
  intro q
  rw [tensorBlock_row]
  have hf (xs : List Nat) (out : FixedWords 243) (hb : ∀ k ∈ xs, k < 81) :
      tripleValue (xs.foldl (fun out k => storeTriple out k
        (if ternaryBinary[k]! = 1 then 0 else tensorRowLoopU maps mixed products (k%81).toUSize (tensorResidue_bound k) 1600 (by rw [tensorCount]) 0 0 0)) out) q.val =
      if q.val ∈ xs then
        (if ternaryBinary[q.val]! = 1 then 0 else tensorRowLoopU maps mixed products (q.val%81).toUSize (tensorResidue_bound q.val) 1600 (by rw [tensorCount]) 0 0 0)
      else tripleValue out q.val := by
    induction xs generalizing out with
    | nil => simp only [List.foldl_nil, List.not_mem_nil, ite_false]
    | cons k ks ih =>
      rw [List.foldl_cons, ih _ (by intro k hk; exact hb k (List.mem_cons_of_mem _ hk))]
      by_cases hm : q.val ∈ ks
      · rw [ite_eq_left hm, ite_eq_left (List.mem_cons_of_mem k hm)]
      · rw [ite_eq_right hm, tripleValue_store _ _ _ _ (by have := hb k List.mem_cons_self; omega) (by have := q.isLt; omega)]
        by_cases he : q.val = k
        · subst k; simp only [List.mem_cons_self, ite_true]
        · simp only [List.mem_cons, hm, or_false, he, ite_false]
  rw [tensorBlockRows, hf _ _ (by intro k hk; exact List.mem_range.mp hk),
    ite_eq_left (List.mem_range.mpr q.isLt)]
  by_cases flag : ternaryBinary[q.val]! = 1
  · simp only [flag, ne_eq, not_true_eq_false, ite_false, Finset.sum_const_zero, ite_true]
  · simp only [flag, ne_eq, not_false_eq_true, ite_true, ite_false]
    rw [tensorRowLoopU_eq, tensorCount, tensorRowLoop_eq, payloadIndex _ (by have := Nat.mod_lt q.val (by decide : 0 < 81); omega), Nat.mod_eq_of_lt q.isLt]
    exact (zero_add _).symm
/-- Compile the early-value driver with scalar position sums and packed tensor storage. -/
def earlyValuesRows (w : SlicedWitness) (d : Nat) (claim : Claim)
    (maps : FixedWords (1600*6*256*3)) (products : RmfeProducts) (binary : Array W) : Array W :=
  let eq := eqTable (claim.point.extract 4 claim.point.size)
  let blocks := 2^(w.nLog-4)/16
  let groups := 2^w.nLog/64
  let indices := List.range blocks
  (List.range 2).foldl (fun values m =>
    let state := w.layers[12*(m+1)-d]!
    indices.foldl (fun values block =>
      addTensorBlock values eq[m*blocks+block]!
        (tensorBlock maps (mixedEmbeddings state groups (16*block)) products)) values)
    (initialTensorValues binary)
/-- Scalar row accumulation preserves every early-round field element. -/
@[csimp] theorem earlyValues_rows_code : earlyValues = earlyValuesRows := by
  funext w d claim maps products binary
  exact earlyValues_eq_blocks w d claim maps products binary
end CompStark.Keccak.GkrProver
