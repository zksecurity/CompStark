/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.BucketProofs
import Init.Internal.Order.While

/-! Structural interpretations of the production payload reduction loops. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64

/-- Native byte-reduction loop state, including its current bit and width. -/
abbrev BucketBitState := FixedWords (6*256*3) × PackedE × USize × USize

/-- One production bit-reduction iteration with its scalar machine loop state. -/
def bucketBitBody (digit : USize) (_ : Unit) (state : BucketBitState) : Id (ForInStep BucketBitState) :=
  let buckets := state.1
  let out := state.2.1
  let width := state.2.2.1
  let bit := state.2.2.2
  if width != 0 then
    let column := reduceBucketColumn digit width width.toNat buckets 0 0 0
    let buckets := column.buckets
    if (8*digit+bit).toNat < 47 then
      pure (.yield (buckets,out.set (8*digit+bit).toNat column.value,width >>> (1 : USize),bit-1))
    else pure (.yield (buckets,out,width >>> (1 : USize),bit-1))
  else pure (.done state)

/-- The production bit loop with its anonymous iteration body given a semantic name. -/
def bucketBitLoop (digit : USize) (state : BucketBitState) : BucketBitState :=
  Lean.Loop.forIn (m := Id) {} state (bucketBitBody digit)

/-- Projection of the retained byte buckets and coefficient buffer. -/
def BucketBitState.result (state : BucketBitState) : FixedWords (6*256*3) × PackedE :=
  (state.1,state.2.1)

/-- A zero-width production loop returns its current buffers for every terminal bit value. -/
theorem bucketBitLoop_zero (digit bit : USize) (buckets : FixedWords (6*256*3)) (out : PackedE) :
    bucketBitLoop digit (buckets,out,0,bit) = (buckets,out,0,bit) := by
  rw [bucketBitLoop,Lean.Loop.forIn_eq_of_monadTail]
  simp only [bucketBitBody,bne_self_eq_false,Bool.false_eq_true,ite_false,pure_bind]
  rfl

/-- Small natural indices have exact scalar machine coordinates on both supported widths. -/
theorem usize_small (n : Nat) (hn : n < 2^32) : n.toUSize.toNat = n := by
  exact USize.toNat_ofNat_of_lt' (lt_of_lt_of_le hn USize.le_size)

/-- A one-bit machine shift is natural division by two on small indices. -/
theorem usize_half (n : Nat) (hn : n < 2^32) :
    n.toUSize >>> (1 : USize) = (n/2).toUSize := by
  apply USize.toNat_inj.mp
  have hp : 1 < System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> omega
  rw [USize.toNat_shiftRight,usize_small n hn,USize.toNat_one,
    Nat.mod_eq_of_lt hp,Nat.shiftRight_eq_div_pow,
    usize_small (n/2) (by omega)]

/-- Positive small machine coordinates subtract one without wrapping. -/
theorem usize_pred (n : Nat) (hn : n < 2^32) (hpos : 0 < n) :
    n.toUSize-1 = (n-1).toUSize := by
  apply USize.toNat_inj.mp
  have hle : (1 : USize) ≤ n.toUSize := by
    rw [USize.le_iff_toNat_le,USize.toNat_one,usize_small n hn]
    omega
  rw [USize.toNat_sub_of_le _ _ hle,usize_small n hn,USize.toNat_one,
    usize_small (n-1) (by omega)]

/-- A positive production bit-loop step agrees with the natural-coordinate column reduction. -/
theorem bucketBitLoop_step (digit bit : Nat) (hd : digit < 6) (hb : bit < 8)
    (buckets : FixedWords (6*256*3)) (out : PackedE) :
    bucketBitLoop digit.toUSize (buckets,out,(2^bit).toUSize,bit.toUSize) =
      let column := reduceBuckets digit (2^bit) (2^bit) buckets 0
      let out := if 8*digit+bit < 47 then out.set (8*digit+bit) column.value else out
      bucketBitLoop digit.toUSize
        (column.buckets,out,(2^bit).toUSize >>> (1 : USize),bit.toUSize-1) := by
  have hw : 2^bit ≤ 128 := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : bit ≤ 7)
  have hwNat := usize_small (2^bit) (by omega)
  have hwNe : (2^bit).toUSize ≠ 0 := by
    intro h
    have hh := congrArg USize.toNat h
    rw [hwNat,USize.toNat_zero] at hh
    have := Nat.two_pow_pos bit
    omega
  have hi : (8*digit.toUSize+bit.toUSize).toNat = 8*digit+bit := by
    have he : (8*digit+bit).toUSize = 8*digit.toUSize+bit.toUSize := by
      simp only [Nat.toUSize,USize.ofNat_add,USize.ofNat_mul]
      rfl
    rw [← he,usize_small _ (by omega)]
  rw [bucketBitLoop,Lean.Loop.forIn_eq_of_monadTail]
  simp only [bucketBitBody]
  rw [ite_eq_left (bne_iff_ne.mpr hwNe)]
  simp only [hwNat,hi,reduceBucketColumn_eq digit (2^bit) (2^bit) hd hw (by omega)]
  split <;> rfl

/-- The terminating production bit loop is exactly the structural eight-bit reducer. -/
theorem bucketBitLoop_eq (digit n : Nat) (hd : digit < 6) (hn : n ≤ 8)
    (buckets : FixedWords (6*256*3)) (out : PackedE) :
    (bucketBitLoop digit.toUSize
      (buckets,out,(if n = 0 then 0 else 2^(n-1)).toUSize,(n-1).toUSize)).result =
      reducePayloadBits digit n buckets out := by
  induction n generalizing buckets out with
  | zero =>
    rw [ite_eq_left rfl]
    change (bucketBitLoop digit.toUSize (buckets,out,0,0)).result = _
    rw [bucketBitLoop_zero]
    rfl
  | succ n ih =>
    rw [ite_eq_right (by omega)]
    simp only [Nat.add_sub_cancel]
    rw [bucketBitLoop_step digit n hd (by omega)]
    by_cases hz : n = 0
    · subst n
      dsimp only
      have he : (2^0).toUSize >>> (1 : USize) = 0 := by
        change (1 : Nat).toUSize >>> (1 : USize) = (0 : Nat).toUSize
        exact usize_half 1 (by decide)
      rw [he,bucketBitLoop_zero]
      rfl
    · have hwidth : (2^n).toUSize >>> (1 : USize) = (if n = 0 then 0 else 2^(n-1)).toUSize := by
        have hsmall : 2^n < 2^32 := by
          have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : n ≤ 7)
          omega
        rw [usize_half _ hsmall,ite_eq_right hz]
        congr 1
        have hp := Nat.pow_sub_mul_pow 2 (show 1 ≤ n by omega)
        simp only [Nat.pow_one] at hp
        omega
      have hbit : n.toUSize-1 = (n-1).toUSize := usize_pred n (by omega) (by omega)
      rw [hwidth,hbit,ih (by omega)]
      rfl

/-- Native six-digit loop state. -/
abbrev BucketDigitState := FixedWords (6*256*3) × PackedE × USize

/-- One production byte iteration, including all eight bit-column reductions. -/
def bucketDigitBody (_ : Unit) (state : BucketDigitState) : Id (ForInStep BucketDigitState) :=
  let buckets := state.1
  let out := state.2.1
  let digit := state.2.2
  if digit < 6 then
    let next := bucketBitLoop digit (buckets,out,128,7)
    pure (.yield (next.1,next.2.1,digit+1))
  else pure (.done state)

/-- The production six-byte loop with its anonymous body named. -/
def bucketDigitLoop (state : BucketDigitState) : BucketDigitState :=
  Lean.Loop.forIn (m := Id) {} state bucketDigitBody

/-- Naming the production loops preserves the complete weighted-payload implementation. -/
theorem weightedPayload_loop (payload : FixedWords 1600) (weights : FixedWords 4800) :
    weightedPayload payload weights =
      (bucketDigitLoop (scatterPayload payload weights 0 (zeroWords (6*256*3)),PackedE.zeros 47,0)).2.1 := by
  rfl

end CompStark.Keccak.GkrProver
