/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Data.List.Range
/-! Machine-indexed accumulation with the same ordered semantics as a natural-index fold. -/
@[expose] public section
namespace CompStark.Sumcheck

/-- A bounded machine-index successor has its exact natural value. -/
theorem index_successor (limit i : USize) (hi : i < limit) :
    (i + 1).toNat = i.toNat + 1 := by
  have hs : 2 ^ System.Platform.numBits = USize.size := rfl
  have hlim := limit.toNat_lt_size
  have hib := USize.lt_iff_toNat_lt.mp hi
  rw [USize.toNat_add, show (1 : USize).toNat = 1 from
    USize.toNat_ofNat_of_lt' (lt_of_lt_of_le (by decide) USize.le_size), hs,
    Nat.mod_eq_of_lt (by omega)]

/-- Accumulate in ascending machine-index order, specializing the step function. -/
@[specialize] def indexFold (limit : USize) (f : USize → α → α) (i : USize) (state : α) : α :=
  if hi : i < limit then indexFold limit f (i + 1) (f i state) else state
termination_by limit.toNat - i.toNat
decreasing_by rw [index_successor limit i hi]; have := USize.lt_iff_toNat_lt.mp hi; omega

/-- The machine-index loop agrees with an ordered fold over the remaining natural interval. -/
theorem indexFold_eq (limit : USize) (f : USize → α → α) (i : USize) (state : α) :
    indexFold limit f i state =
      (List.range' i.toNat (limit.toNat - i.toNat)).foldl (fun state j => f j.toUSize state) state := by
  fun_induction indexFold limit f i state with
  | case1 i state hi ih =>
    have hib := USize.lt_iff_toNat_lt.mp hi
    have he : limit.toNat - i.toNat = (limit.toNat - (i.toNat + 1)) + 1 := by omega
    rw [he, List.range'_succ, List.foldl_cons]
    simp only [Nat.toUSize, USize.ofNat_toNat]
    rw [ih, index_successor limit i hi]
  | case2 i state hi =>
    have hib : limit.toNat ≤ i.toNat := by
      have hnot : ¬ i.toNat < limit.toNat := by simpa only [USize.lt_iff_toNat_lt] using hi
      omega
    simp only [Nat.sub_eq_zero_of_le hib, List.range'_zero, List.foldl_nil]

/-- Starting at zero gives the usual complete ascending index fold. -/
theorem indexFold_zero (limit : USize) (f : USize → α → α) (state : α) :
    indexFold limit f 0 state =
      (List.range limit.toNat).foldl (fun state j => f j.toUSize state) state := by
  rw [indexFold_eq]
  simp only [show (0 : USize).toNat = 0 from rfl, Nat.sub_zero, ← List.range_eq_range']

end CompStark.Sumcheck
