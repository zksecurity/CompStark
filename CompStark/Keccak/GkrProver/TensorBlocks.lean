/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.TensorAccumulation

/-! Exact weighted-position sums of the production early-pack tensor blocks. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak BF64
open scoped BigOperators

/-- One bounded position update, with a total natural index for structural list folds. -/
def tensorColumn (maps : FixedWords (1600*6*256*3)) (mixed : FixedDWords (81*1600))
    (products : RmfeProducts) (j : Nat) (out : FixedWords 243) : FixedWords 243 :=
  let j := j%1600
  have hj : j < 1600 := Nat.mod_lt _ (by decide)
  have hs (k : Nat) : (shift j k).toUSize.toNat < 1600 := by
    have hk : shift j k < 1600 := (Gkr.along ⟨j,hj⟩ k).isLt
    rw [usize_small _ (by omega)]
    exact hk
  have hb : (4608*j).toUSize.toNat ≤ 7372800-4608 := by
    rw [usize_small _ (by omega)]; omega
  earlyPosition maps mixed products (shift j 1).toUSize (shift j 2).toUSize
    (hs 1) (hs 2) (4608*j).toUSize hb 0 out

/-- A bounded production position update is its proof-independent list-fold step. -/
theorem earlyPosition_eq_column (maps : FixedWords (1600*6*256*3)) (mixed : FixedDWords (81*1600))
    (products : RmfeProducts) (j : Nat) (hj : j < 1600)
    (hs1 : (shift j 1).toUSize.toNat < 1600) (hs2 : (shift j 2).toUSize.toNat < 1600)
    (hb : (4608*j).toUSize.toNat ≤ 7372800-4608) (out : FixedWords 243) :
    earlyPosition maps mixed products (shift j 1).toUSize (shift j 2).toUSize
      hs1 hs2 (4608*j).toUSize hb 0 out = tensorColumn maps mixed products j out := by
  unfold tensorColumn
  simp only [Nat.mod_eq_of_lt hj]

/-- The complete native position loop as a structural list fold. -/
def tensorBlock (maps : FixedWords (1600*6*256*3)) (mixed : FixedDWords (81*1600))
    (products : RmfeProducts) : FixedWords 243 :=
  (List.range 1600).foldl (fun out j => tensorColumn maps mixed products j out) (zeroWords 243)

/-- A scalar view of a fold with additive updates is its initial value plus the term sum. -/
theorem foldl_value_sum {A S : Type} (view : S → W) (step : S → A → S) (term : A → W)
    (hget : ∀ state a, view (step state a) = view state+term a)
    (xs : List A) (state : S) :
    view (xs.foldl step state) = view state+(xs.map term).sum := by
  induction xs generalizing state with
  | nil => exact (add_zero _).symm
  | cons a xs ih => rw [List.foldl_cons,ih,hget,List.map_cons,List.sum_cons,add_assoc]

/-- A single weighted product at one compact tensor endpoint. -/
noncomputable def tensorColumnProduct (weights : Array W) (s : W)
    (state : Array UInt64) (groups base : Nat) (j : Fin 1600) (q : Fin 81) : W :=
  weights[j.val]! *
    ternaryLift 4 (tensorFactor s state groups base (Gkr.along j 1)) q.val *
      ternaryLift 4 (tensorFactor s state groups base (Gkr.along j 2)) q.val

/-- Every native position update adds the exact product of its lifted RMFE factors. -/
theorem tensorColumn_get (weights : Array W) (s : W) (state : Array UInt64) (groups base j : Nat)
    (out : FixedWords 243) (q : Fin 81) :
    tripleValue (tensorColumn (prepareWeightMaps weights (CompStark.Sumcheck.prepare s))
      (mixedEmbeddings state groups base) prepareRmfeProducts j out) q.val =
      tripleValue out q.val + if ternaryBinary[q.val]! ≠ 1 then
        tensorColumnProduct weights s state groups base ⟨j%1600,Nat.mod_lt _ (by decide)⟩ q else 0 := by
  unfold tensorColumn
  have hzero : (0 : USize) = (0 : Nat).toUSize := by
    apply USize.toNat_inj.mp
    rw [USize.toNat_zero,usize_small 0 (by decide)]
  rw [hzero,earlyPosition_get _ _ _ _ _ _ _ _ _ 0 (by omega)]
  simp only [Nat.zero_le,true_and]
  by_cases hf : ternaryBinary[q.val]! = 1
  · rw [ite_eq_right (not_not_intro hf),ite_eq_right (not_not_intro hf)]
  · rw [ite_eq_left hf,ite_eq_left hf]
    congr 1
    unfold tensorPositionValue
    rw [evalWeightValue_rmfeProduct weights s ⟨j%1600,Nat.mod_lt _ (by decide)⟩]
    have haddr (k : Nat) : 1600*q.val.toUSize+(shift (j%1600) k).toUSize =
        (1600*q.val+shift (j%1600) k).toUSize := by
      simp only [Nat.toUSize,USize.ofNat_add,USize.ofNat_mul]
      rfl
    have hmix (k : Nat) := mixedEmbeddings_rmfeValue s state groups base q
      (Gkr.along ⟨j%1600,Nat.mod_lt _ (by decide)⟩ k)
    simp only [← shift_eq] at hmix
    rw [haddr 1,haddr 2,hmix 1,hmix 2]
    unfold tensorColumnProduct tensorFactor
    ring

/-- A production tensor block stores precisely the sum of all nonbinary weighted position products. -/
theorem tensorBlock_get (weights : Array W) (s : W) (state : Array UInt64) (groups base : Nat)
    (q : Fin 81) :
    tripleValue (tensorBlock (prepareWeightMaps weights (CompStark.Sumcheck.prepare s))
      (mixedEmbeddings state groups base) prepareRmfeProducts) q.val =
      if ternaryBinary[q.val]! ≠ 1 then
        ∑ j : Fin 1600, tensorColumnProduct weights s state groups base j q else 0 := by
  unfold tensorBlock
  rw [foldl_value_sum (fun out => tripleValue out q.val)
    (fun out j => tensorColumn _ _ _ j out)
    (fun j => if ternaryBinary[q.val]! ≠ 1 then
      tensorColumnProduct weights s state groups base ⟨j%1600,Nat.mod_lt _ (by decide)⟩ q else 0)
    (fun out j => tensorColumn_get weights s state groups base j out q),
    tripleValue_zero _ (by decide) _ (by have := q.isLt; omega),zero_add,list_range_sum]
  by_cases hf : ternaryBinary[q.val]! = 1
  · simp only [hf,ne_eq,not_true_eq_false,ite_false,Finset.sum_const_zero]
  · rw [ite_eq_left hf]
    simp only [ite_eq_left hf]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt j.isLt)

end CompStark.Keccak.GkrProver
