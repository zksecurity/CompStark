/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.ProductAccumulation

/-! Semantics of the native four-coordinate ternary pack tensor. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators

/-- A Boolean vertex belongs to a ternary assignment when it agrees at every finite coordinate. -/
def ternarySelect (q b : Nat) : Bool :=
  decide (∀ i : Fin 4, q/3^i.val%3 = 2 ∨ q/3^i.val%3 = (b.testBit i.val).toNat)

/-- The materialized ternary plan names a Boolean vertex or two smaller endpoint assignments. -/
theorem ternaryPlan_semantics : ∀ q : Fin 81,
    let plan := ternaryPlan[q.val]!
    if plan.2 = 81 then
      plan.1 < 16 ∧ ∀ b : Fin 16, ternarySelect q.val b.val = decide (b.val = plan.1)
    else plan.1 < q.val ∧ plan.2 < q.val ∧
      ∀ b : Fin 16, ternarySelect q.val b.val =
        (ternarySelect plan.1 b.val ^^ ternarySelect plan.2 b.val) := by
  intro q
  simp only [ternaryPlan,getElem!_pos,Array.size_ofFn,Fin.isLt,Array.getElem_ofFn]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  revert q
  decide

/-- Ternary assignment evaluation as the sum of the selected Boolean vertices. -/
def ternaryValue (values : Fin 16 → W) (q : Nat) : W :=
  ∑ b : Fin 16, if ternarySelect q b.val then values b else 0

/-- A binary native plan selects exactly its named Boolean pack. -/
theorem ternaryValue_binary (values : Fin 16 → W) (q : Fin 81)
    (hb : (ternaryPlan[q.val]!).2 = 81) :
    ternaryValue values q.val = values ⟨(ternaryPlan[q.val]!).1,by
      have h := ternaryPlan_semantics q
      rw [ite_eq_left hb] at h
      exact h.1⟩ := by
  have h := ternaryPlan_semantics q
  rw [ite_eq_left hb] at h
  unfold ternaryValue
  simp only [h.2,decide_eq_true_eq]
  have hi := Finset.sum_ite_eq' (Finset.univ : Finset (Fin 16))
    (⟨(ternaryPlan[q.val]!).1,h.1⟩ : Fin 16) values
  simpa only [Fin.ext_iff,Finset.mem_univ,ite_true] using hi

/-- An infinity digit selects the characteristic-two sum of its two lower endpoint assignments. -/
theorem ternaryValue_infinity (values : Fin 16 → W) (q : Fin 81)
    (hb : (ternaryPlan[q.val]!).2 ≠ 81) :
    ternaryValue values q.val = ternaryValue values (ternaryPlan[q.val]!).1 +
      ternaryValue values (ternaryPlan[q.val]!).2 := by
  have h := ternaryPlan_semantics q
  rw [ite_eq_right hb] at h
  unfold ternaryValue
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [h.2.2 b]
  cases ternarySelect (ternaryPlan[q.val]!).1 b.val <;>
    cases ternarySelect (ternaryPlan[q.val]!).2 b.val <;>
    simp only [Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true,ite_true,
      Bool.false_eq_true,ite_false,add_zero,zero_add,CharTwo.add_self_eq_zero]

/-- One natural-coordinate ternary-row cell, retaining the two source rows for infinity digits. -/
def mixedRowValue (state : Array UInt64) (groups offset : USize) (bits : UInt64)
    (lo hi : Nat) (binary : Bool) (out : FixedWords (81*1600)) (j : Nat) : UInt64 :=
  if binary then (state[(j.toUSize*groups+offset).toNat]! >>> bits) &&& 65535
  else readWord out (lo+j) ^^^ readWord out (hi+j)

/-- A structural natural-position view of the word-width ternary-row loop. -/
def mixedRowNat (state : Array UInt64) (groups offset : USize) (bits : UInt64)
    (lo hi target : Nat) (binary : Bool) (j : Nat) (out : FixedWords (81*1600)) : FixedWords (81*1600) :=
  if _h : j < 1600 then
    mixedRowNat state groups offset bits lo hi target binary (j+1)
      (writeWord out (target+j) (mixedRowValue state groups offset bits lo hi binary out j))
  else out
termination_by 1600-j

/-- Machine-position ternary-row recursion equals its structural natural-coordinate form. -/
theorem mixedRowReference_eq_nat (state : Array UInt64) (groups offset : USize) (bits : UInt64)
    (lo hi target : Nat) (binary : Bool) (j : Nat) (hj : j ≤ 1600)
    (out : FixedWords (81*1600)) :
    mixedRowReference state groups offset bits lo.toUSize hi.toUSize target.toUSize binary j.toUSize out =
      mixedRowNat state groups offset bits lo hi target binary j out := by
  have hguard : j.toUSize < 1600 ↔ j < 1600 := by
    rw [USize.lt_iff_toNat_lt,usize_small j (by omega)]
    simp only [USize.reduceToNat]
  rw [mixedRowReference,mixedRowNat]
  by_cases h : j < 1600
  · rw [dite_eq_left (hguard.mpr h),dite_eq_left h]
    have hnext : j.toUSize+1 = (j+1).toUSize := by
      simp only [Nat.toUSize,USize.ofNat_add]
      rfl
    rw [hnext,mixedRowReference_eq_nat state groups offset bits lo hi target binary (j+1) (by omega)]
    simp only [mixedRowValue,readWord,writeWord,Nat.toUSize,USize.ofNat_add]
  · rw [dite_eq_right (by exact fun hg => h (hguard.mp hg)),dite_eq_right h]
termination_by 1600-j

/-- A target-row store preserves every infinity source cell in the preceding rows. -/
theorem mixedRowValue_store (state : Array UInt64) (groups offset : USize) (bits : UInt64)
    (lo hi target j k : Nat) (binary : Bool) (hj : j < 1600) (hk : k < 1600)
    (ht : target+1600 ≤ 81*1600)
    (hsource : binary = true ∨ (lo+1600 ≤ target ∧ hi+1600 ≤ target))
    (out : FixedWords (81*1600)) (v : UInt64) :
    mixedRowValue state groups offset bits lo hi binary (writeWord out (target+j) v) k =
      mixedRowValue state groups offset bits lo hi binary out k := by
  cases binary
  · have hs : lo+1600 ≤ target ∧ hi+1600 ≤ target := by
      simpa only [Bool.false_eq_true,false_or] using hsource
    simp only [mixedRowValue,Bool.false_eq_true,ite_false]
    rw [readWord_writeWord _ _ _ (by omega) (by omega),ite_eq_right (by omega),
      readWord_writeWord _ _ _ (by omega) (by omega),ite_eq_right (by omega)]
  · rfl

/-- A complete ternary-row loop writes the prescribed suffix and retains every other word. -/
theorem mixedRowNat_get (state : Array UInt64) (groups offset : USize) (bits : UInt64)
    (lo hi target : Nat) (binary : Bool) (start : Nat) (hs : start ≤ 1600)
    (ht : target+1600 ≤ 81*1600)
    (hsource : binary = true ∨ (lo+1600 ≤ target ∧ hi+1600 ≤ target))
    (out : FixedWords (81*1600)) (i : Fin (81*1600)) :
    readWord (mixedRowNat state groups offset bits lo hi target binary start out) i.val =
      if target+start ≤ i.val ∧ i.val < target+1600
      then mixedRowValue state groups offset bits lo hi binary out (i.val-target)
      else readWord out i.val := by
  rw [mixedRowNat]
  split
  · rename_i hstart
    rw [mixedRowNat_get state groups offset bits lo hi target binary (start+1) (by omega)
      ht hsource]
    by_cases htail : target+(start+1) ≤ i.val ∧ i.val < target+1600
    · rw [ite_eq_left htail,ite_eq_left (by omega),
        mixedRowValue_store state groups offset bits lo hi target start (i.val-target)
          binary hstart (by omega) ht hsource]
    · rw [ite_eq_right htail,readWord_writeWord _ _ _ (by omega) i.isLt]
      by_cases he : target+start = i.val
      · rw [ite_eq_left he,ite_eq_left (by omega)]
        congr 1
        omega
      · rw [ite_eq_right he,ite_eq_right (by omega)]
  · rw [ite_eq_right (by omega)]
termination_by 1600-start

/-- The native XOR word is extension-field addition on embedded lanes. -/
theorem lane_xor (a b : UInt64) : lane (a ^^^ b) = lane a+lane b := by
  change (⟨⟨a ^^^ b⟩,⟨0⟩,⟨0⟩⟩ : W) = ⟨⟨a ^^^ b⟩,⟨0 ^^^ 0⟩,⟨0 ^^^ 0⟩⟩
  rw [UInt64.xor_self]

/-- The sixteen Boolean pack vertices of one position in a source state. -/
def tensorVertices (state : Array UInt64) (groups base : Nat) (j : Fin 1600) (b : Fin 16) : W :=
  lane ((state[(j.val.toUSize*groups.toUSize+((base+b.val)/4).toUSize).toNat]!
    >>> (16*((base+b.val)%4)).toUInt64) &&& 65535)

/-- Fill one complete word-width ternary assignment using the native plan. -/
def tensorStep (state : Array UInt64) (groups base : Nat) (out : FixedWords (81*1600))
    (q : Nat) : FixedWords (81*1600) :=
  let (lo,hi) := ternaryPlan[q]!
  let b := base+lo
  mixedRowReference state groups.toUSize (b/4).toUSize (16*(b%4)).toUInt64
    (1600*lo).toUSize (1600*hi).toUSize (1600*q).toUSize (hi==81) 0 out

/-- One ternary assignment step preserves earlier rows and fills its own complete row. -/
theorem tensorStep_get (state : Array UInt64) (groups base : Nat) (out : FixedWords (81*1600))
    (q row : Fin 81) (hr : row.val ≤ q.val) (j : Fin 1600) :
    readWord (tensorStep state groups base out q.val) (1600*row.val+j.val) =
      if row = q then
        mixedRowValue state groups.toUSize ((base+(ternaryPlan[q.val]!).1)/4).toUSize
          (16*((base+(ternaryPlan[q.val]!).1)%4)).toUInt64
          (1600*(ternaryPlan[q.val]!).1) (1600*(ternaryPlan[q.val]!).2)
          ((ternaryPlan[q.val]!).2==81) out j.val
      else readWord out (1600*row.val+j.val) := by
  have hq := q.isLt
  have hj := j.isLt
  have hsource : ((ternaryPlan[q.val]!).2==81) = true ∨
      (1600*(ternaryPlan[q.val]!).1+1600 ≤ 1600*q.val ∧
        1600*(ternaryPlan[q.val]!).2+1600 ≤ 1600*q.val) := by
    have hp := ternaryPlan_semantics q
    by_cases hb : (ternaryPlan[q.val]!).2 = 81
    · exact Or.inl (beq_iff_eq.mpr hb)
    · rw [ite_eq_right hb] at hp
      exact Or.inr ⟨by omega,by omega⟩
  have hidx : 1600*row.val+j.val < 81*1600 := by omega
  unfold tensorStep
  dsimp only
  have href := mixedRowReference_eq_nat state groups.toUSize
    ((base+(ternaryPlan[q.val]!).1)/4).toUSize
    (16*((base+(ternaryPlan[q.val]!).1)%4)).toUInt64
    (1600*(ternaryPlan[q.val]!).1) (1600*(ternaryPlan[q.val]!).2) (1600*q.val)
    ((ternaryPlan[q.val]!).2==81) 0 (by omega) out
  have hzero : (0 : Nat).toUSize = (0 : USize) := by
    apply USize.toNat_inj.mp
    rw [usize_small 0 (by omega),USize.toNat_zero]
  rw [hzero] at href
  rw [href,mixedRowNat_get _ _ _ _ _ _ _ _ 0 (by omega) (by omega) hsource _ ⟨1600*row.val+j.val,hidx⟩]
  dsimp only
  by_cases he : row = q
  · subst row
    rw [ite_eq_left (by omega),ite_eq_left rfl]
    congr 1
    omega
  · have hne : row.val ≠ q.val := fun h => he (Fin.ext h)
    rw [ite_eq_right (by omega),ite_eq_right he]

/-- The first native ternary assignments as a structural fold over natural row indices. -/
def mixedTensorPrefix (state : Array UInt64) (groups base n : Nat) : FixedWords (81*1600) :=
  (List.range n).foldl (tensorStep state groups base) (zeroWords (81*1600))

/-- Extending a tensor prefix writes precisely its next planned assignment. -/
theorem mixedTensorPrefix_succ (state : Array UInt64) (groups base n : Nat) :
    mixedTensorPrefix state groups base (n+1) =
      tensorStep state groups base (mixedTensorPrefix state groups base n) n := by
  rw [mixedTensorPrefix,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
  rfl

/-- Every completed native ternary row is the sum of its selected Boolean pack vertices. -/
theorem mixedTensorPrefix_get (state : Array UInt64) (groups base n : Nat) (hn : n ≤ 81)
    (q : Fin 81) (hq : q.val < n) (j : Fin 1600) :
    lane (readWord (mixedTensorPrefix state groups base n) (1600*q.val+j.val)) =
      ternaryValue (tensorVertices state groups base j) q.val := by
  induction n generalizing q with
  | zero => omega
  | succ n ih =>
    have hqn : q.val ≤ n := by omega
    rw [mixedTensorPrefix_succ,tensorStep_get state groups base _ ⟨n,by omega⟩ q hqn j]
    by_cases he : q.val = n
    · have hqe : q = (⟨n,by omega⟩ : Fin 81) := Fin.ext he
      rw [ite_eq_left hqe,← hqe]
      have hp := ternaryPlan_semantics q
      by_cases hb : (ternaryPlan[q.val]!).2 = 81
      · rw [ternaryValue_binary _ q hb]
        simp only [mixedRowValue,hb,BEq.rfl,ite_true]
        rfl
      · rw [ite_eq_right hb] at hp
        rw [ternaryValue_infinity _ q hb]
        simp only [mixedRowValue,beq_eq_false_iff_ne.mpr hb,Bool.false_eq_true,ite_false]
        rw [lane_xor,
          ih (by omega) ⟨(ternaryPlan[q.val]!).1,by omega⟩ (by dsimp only; omega),
          ih (by omega) ⟨(ternaryPlan[q.val]!).2,by omega⟩ (by dsimp only; omega)]
    · have hqne : q ≠ (⟨n,by omega⟩ : Fin 81) := fun h => he (congrArg Fin.val h)
      rw [ite_eq_right hqne]
      exact ih (by omega) q (by omega)

/-- The word-width reference tensor is exactly the complete 81-assignment structural prefix. -/
theorem mixedEmbeddingsReference_eq_prefix (state : Array UInt64) (groups base : Nat) :
    mixedEmbeddingsReference state groups base = mixedTensorPrefix state groups base 81 := by
  simp only [mixedEmbeddingsReference,Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure,
    Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range']
  rfl

/-- The full word-width native tensor has the exact ternary Boolean-vertex semantics. -/
theorem mixedEmbeddingsReference_value (state : Array UInt64) (groups base : Nat)
    (q : Fin 81) (j : Fin 1600) :
    lane (readWord (mixedEmbeddingsReference state groups base) (1600*q.val+j.val)) =
      ternaryValue (tensorVertices state groups base j) q.val := by
  rw [mixedEmbeddingsReference_eq_prefix]
  exact mixedTensorPrefix_get state groups base 81 (by omega) q q.isLt j

/-- Every completed assignment remains a sixteen-bit Boolean pack after endpoint XORs. -/
theorem mixedTensorPrefix_bound (state : Array UInt64) (groups base n : Nat) (hn : n ≤ 81)
    (q : Fin 81) (hq : q.val < n) (j : Fin 1600) :
    (readWord (mixedTensorPrefix state groups base n) (1600*q.val+j.val)).toNat < 2^16 := by
  induction n generalizing q with
  | zero => omega
  | succ n ih =>
    have hqn : q.val ≤ n := by omega
    rw [mixedTensorPrefix_succ,tensorStep_get state groups base _ ⟨n,by omega⟩ q hqn j]
    by_cases he : q.val = n
    · have hqe : q = (⟨n,by omega⟩ : Fin 81) := Fin.ext he
      rw [ite_eq_left hqe,← hqe]
      have hp := ternaryPlan_semantics q
      by_cases hb : (ternaryPlan[q.val]!).2 = 81
      · simp only [mixedRowValue,hb,BEq.rfl,ite_true,UInt64.toNat_and]
        have hmask := Nat.and_le_right (n :=
          (state[((j.val).toUSize*groups.toUSize+
            ((base+(ternaryPlan[q.val]!).1)/4).toUSize).toNat]!
            >>> (16*((base+(ternaryPlan[q.val]!).1)%4)).toUInt64).toNat) (m := 65535)
        exact lt_of_le_of_lt hmask (by decide)
      · rw [ite_eq_right hb] at hp
        simp only [mixedRowValue,beq_eq_false_iff_ne.mpr hb,Bool.false_eq_true,ite_false,
          UInt64.toNat_xor]
        exact Nat.xor_lt_two_pow
          (ih (by omega) ⟨(ternaryPlan[q.val]!).1,by omega⟩ (by dsimp only; omega))
          (ih (by omega) ⟨(ternaryPlan[q.val]!).2,by omega⟩ (by dsimp only; omega))
    · have hqne : q ≠ (⟨n,by omega⟩ : Fin 81) := fun h => he (congrArg Fin.val h)
      rw [ite_eq_right hqne]
      exact ih (by omega) q (by omega)

/-- The compact native tensor stores the entire assignment word without truncation. -/
theorem mixedEmbeddings_word (state : Array UInt64) (groups base : Nat)
    (q : Fin 81) (j : Fin 1600) :
    (readUDWord (mixedEmbeddings state groups base) (1600*q.val+j.val).toUSize).toUInt64 =
      readWord (mixedEmbeddingsReference state groups base) (1600*q.val+j.val) := by
  have h := mixedEmbeddings_refines state groups base (1600*q.val+j.val).toUSize
  change readUDWord _ _ = (readWord _ _).toUInt32 at h
  rw [h]
  apply UInt64.toNat_inj.mp
  rw [UInt32.toNat_toUInt64,UInt64.toNat_toUInt32,Nat.mod_eq_of_lt]
  rw [mixedEmbeddingsReference_eq_prefix]
  exact lt_trans (mixedTensorPrefix_bound state groups base 81 (by omega) q q.isLt j) (by decide)

/-- Production 32-bit assignments have the exact Boolean-vertex and infinity-endpoint semantics. -/
theorem mixedEmbeddings_value (state : Array UInt64) (groups base : Nat)
    (q : Fin 81) (j : Fin 1600) :
    lane (readUDWord (mixedEmbeddings state groups base) (1600*q.val+j.val).toUSize).toUInt64 =
      ternaryValue (tensorVertices state groups base j) q.val := by
  rw [mixedEmbeddings_word,mixedEmbeddingsReference_value]

end CompStark.Keccak.GkrProver
