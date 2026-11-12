/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.BucketLoops

/-! Complete weighted coefficient semantics for the production RMFE payload. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators

/-- The position-weight sum of one binary coefficient of the complete payload. -/
def payloadCoefficient (payload : FixedWords 1600) (weights : Nat → W) (bit : Nat) : W :=
  ∑ j ∈ Finset.range 1600, if (readWord payload j).toNat.testBit bit then weights j else 0

/-- Byte reduction writes the exact corresponding coefficients of the complete payload. -/
theorem reducePayloadBits_coefficient (payload : FixedWords 1600) (weights : Nat → W)
    (digit n : Nat) (hd : digit < 6) (hn : n ≤ 8)
    (buckets : FixedWords (6*256*3)) (out : PackedE) (hout : out.size = 47)
    (hm : BucketsMatch buckets digit (2^n) (payloadByte payload digit) weights) (i : Fin 47) :
    (reducePayloadBits digit n buckets out).2.get i.val =
      if 8*digit ≤ i.val ∧ i.val < 8*digit+n then payloadCoefficient payload weights i.val
      else out.get i.val := by
  rw [reducePayloadBits_get digit n hd hn buckets out hout (payloadByte payload digit) weights hm]
  by_cases h : 8*digit ≤ i.val ∧ i.val < 8*digit+n
  · rw [ite_eq_left h,ite_eq_left h,payloadCoefficient]
    apply Finset.sum_congr rfl
    intro j _
    rw [payloadByte_testBit payload digit j (i.val-8*digit) hd (by omega)]
    rw [show 8*digit+(i.val-8*digit) = i.val by omega]
  · rw [ite_eq_right h,ite_eq_right h]

/-- Structural recursion through the six little-endian byte digits. -/
def reducePayloadDigits : Nat → Nat → FixedWords (6*256*3) → PackedE → PackedE
  | 0, _, _, out => out
  | n+1, digit, buckets, out =>
    let next := reducePayloadBits digit 8 buckets out
    reducePayloadDigits n (digit+1) next.1 next.2

/-- Processing a consecutive byte interval writes precisely its payload coefficients. -/
theorem reducePayloadDigits_get (payload : FixedWords 1600) (weights : Nat → W)
    (n digit : Nat) (hn : digit+n ≤ 6) (buckets : FixedWords (6*256*3))
    (out : PackedE) (hout : out.size = 47)
    (hm : ∀ q, digit ≤ q → q < digit+n →
      BucketsMatch buckets q 256 (payloadByte payload q) weights) (i : Fin 47) :
    (reducePayloadDigits n digit buckets out).get i.val =
      if 8*digit ≤ i.val ∧ i.val < 8*(digit+n) then payloadCoefficient payload weights i.val
      else out.get i.val := by
  induction n generalizing digit buckets out with
  | zero => rw [reducePayloadDigits,ite_eq_right (by omega)]
  | succ n ih =>
    have hd : digit < 6 := by omega
    let next := reducePayloadBits digit 8 buckets out
    have hsize : next.2.size = 47 := reducePayloadBits_size digit 8 buckets out hout
    have hmatches : ∀ q, digit+1 ≤ q → q < digit+1+n →
        BucketsMatch next.1 q 256 (payloadByte payload q) weights := by
      intro q hq hqn k hk
      rw [reducePayloadBits_other digit 8 q k hd (by omega) (by omega) hk (by omega)]
      exact hm q (by omega) (by omega) k hk
    rw [reducePayloadDigits,ih (digit+1) (by omega) next.1 next.2 hsize hmatches]
    by_cases hlater : 8*(digit+1) ≤ i.val ∧ i.val < 8*(digit+1+n)
    · rw [ite_eq_left hlater,ite_eq_left (by omega)]
    · rw [ite_eq_right hlater]
      have hcurrent : BucketsMatch buckets digit (2^8) (payloadByte payload digit) weights :=
        hm digit (by omega) (by omega)
      rw [reducePayloadBits_coefficient payload weights digit 8 hd (by omega) buckets out hout hcurrent]
      by_cases hhere : 8*digit ≤ i.val ∧ i.val < 8*digit+8
      · rw [ite_eq_left hhere,ite_eq_left (by omega)]
      · rw [ite_eq_right hhere,ite_eq_right (by omega)]

/-- The native six-byte loop equals structural recursion through its remaining digits. -/
theorem bucketDigitLoop_eq (n digit : Nat) (hn : digit+n = 6)
    (buckets : FixedWords (6*256*3)) (out : PackedE) :
    (bucketDigitLoop (buckets,out,digit.toUSize)).2.1 =
      reducePayloadDigits n digit buckets out := by
  induction n generalizing digit buckets out with
  | zero =>
    have hd : digit = 6 := by omega
    subst digit
    rw [bucketDigitLoop,Lean.Loop.forIn_eq_of_monadTail]
    simp only [bucketDigitBody]
    have hguard : ¬(6 : Nat).toUSize < 6 := by
      rw [USize.lt_iff_toNat_lt,usize_small 6 (by decide)]
      simp only [USize.reduceToNat,Nat.lt_irrefl,not_false_eq_true]
    rw [ite_eq_right hguard]
    rfl
  | succ n ih =>
    have hd : digit < 6 := by omega
    have hguard : digit.toUSize < 6 := by
      rw [USize.lt_iff_toNat_lt,usize_small digit (by omega)]
      simpa only [USize.reduceToNat] using hd
    have hnext : (digit+1).toUSize = digit.toUSize+1 := by
      simp only [Nat.toUSize,USize.ofNat_add]
      rfl
    have hinner := bucketBitLoop_eq digit 8 hd (by omega) buckets out
    change (bucketBitLoop digit.toUSize (buckets,out,128,7)).result = _ at hinner
    have hbuf := congrArg Prod.fst hinner
    have hout := congrArg Prod.snd hinner
    dsimp only [BucketBitState.result] at hbuf hout
    rw [bucketDigitLoop,Lean.Loop.forIn_eq_of_monadTail]
    simp only [bucketDigitBody,hguard,ite_true,pure_bind]
    change (bucketDigitLoop
      ((bucketBitLoop digit.toUSize (buckets,out,128,7)).1,
        (bucketBitLoop digit.toUSize (buckets,out,128,7)).2.1,digit.toUSize+1)).2.1 = _
    rw [hbuf,hout,← hnext,ih (digit+1) (by omega)]
    rfl

/-- The initial scatter buffer satisfies the byte-residue invariant at full byte width. -/
theorem scatterPayload_match (payload : FixedWords 1600) (weights : Array W)
    (digit : Nat) (hd : digit < 6) :
    BucketsMatch (scatterPayload payload (weightDigits weights) 0 (zeroWords (6*256*3)))
      digit 256 (payloadByte payload digit) (fun j => weights[j]!) := by
  intro value hv
  rw [scatterPayload_weightDigits payload weights ⟨digit,hd⟩ ⟨value,hv⟩,
    Nat.Ico_zero_eq_range,byteBucketSum]
  apply Finset.sum_congr rfl
  intro j _
  have hbyte : payloadByte payload digit j < 256 := payloadDigit_bound _
  rw [Nat.mod_eq_of_lt hbyte]
  rfl

/-- The complete structural byte reducer computes every weighted payload coefficient. -/
theorem reducePayloadDigits_coefficient (payload : FixedWords 1600) (weights : Array W)
    (i : Fin 47) :
    (reducePayloadDigits 6 0
      (scatterPayload payload (weightDigits weights) 0 (zeroWords (6*256*3)))
      (PackedE.zeros 47)).get i.val = payloadCoefficient payload (fun j => weights[j]!) i.val := by
  rw [reducePayloadDigits_get payload (fun j => weights[j]!) 6 0 (by omega)
    _ _ (by rfl) (by intro q _ hq; exact scatterPayload_match payload weights q hq) i,
    ite_eq_left (by have := i.isLt; omega)]

/-- Every native weighted-payload coefficient equals its complete position-weight sum. -/
theorem weightedPayload_get (payload : FixedWords 1600) (weights : Array W) (i : Fin 47) :
    (weightedPayload payload (weightDigits weights)).get i.val =
      ∑ j : Fin 1600, if (readWord payload j.val).toNat.testBit i.val then weights[j.val]! else 0 := by
  rw [weightedPayload_loop]
  change (bucketDigitLoop (_,_,(0 : Nat).toUSize)).2.1.get i.val = _
  rw [bucketDigitLoop_eq 6 0 (by omega),reducePayloadDigits_coefficient,payloadCoefficient]
  exact (Fin.sum_univ_eq_sum_range _ 1600).symm

end CompStark.Keccak.GkrProver
