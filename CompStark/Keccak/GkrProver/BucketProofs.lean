/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.ProductProofs
import Init.Internal.Order.While

/-! Structural and coefficient semantics of the weighted payload bucket reduction. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators

/-- Add an extension weight to one byte bucket using its three scalar coordinates. -/
def addBucket (buckets : FixedWords (6*256*3)) (j : Nat) (v : W) : FixedWords (6*256*3) :=
  writeWord (writeWord (writeWord buckets (3*j) (readWord buckets (3*j) ^^^ v.c0.val))
    (3*j+1) (readWord buckets (3*j+1) ^^^ v.c1.val))
    (3*j+2) (readWord buckets (3*j+2) ^^^ v.c2.val)

/-- A bucket addition changes exactly its selected extension coordinate. -/
theorem bucketValue_addBucket (buckets : FixedWords (6*256*3)) (j i : Fin (6*256)) (v : W) :
    bucketValue (addBucket buckets j.val v) i.val =
      bucketValue buckets i.val + if j = i then v else 0 := by
  exact bucketValue_accumulate buckets j i v.c0.val v.c1.val v.c2.val

/-- The accumulated extension weight of a reduced bucket column. -/
def BucketColumn.value (column : BucketColumn) : W :=
  ⟨⟨column.c0⟩,⟨column.c1⟩,⟨column.c2⟩⟩

/-- Natural-coordinate structural recursion for the byte-bucket reduction. -/
def reduceBuckets (digit width : Nat) : Nat → FixedWords (6*256*3) → W → BucketColumn
  | 0, buckets, value => ⟨buckets,value.c0.val,value.c1.val,value.c2.val⟩
  | n+1, buckets, value =>
    let high := bucketValue buckets (256*digit+n+width)
    reduceBuckets digit width n (addBucket buckets (256*digit+n) high) (value+high)

/-- One machine reduction step equals its natural-coordinate bucket addition. -/
theorem reduceBucketColumn_step (digit width n : Nat) (hd : digit < 6)
    (hw : width ≤ 128) (hn : n < width) (buckets : FixedWords (6*256*3))
    (c0 c1 c2 : UInt64) :
    reduceBucketColumn digit.toUSize width.toUSize (n+1) buckets c0 c1 c2 =
      let high := bucketValue buckets (256*digit+n+width)
      reduceBucketColumn digit.toUSize width.toUSize n
        (addBucket buckets (256*digit+n) high)
        (c0 ^^^ high.c0.val) (c1 ^^^ high.c1.val) (c2 ^^^ high.c2.val) := by
  have hlo : 3*(256*digit+n)+2 < 6*256*3 := by omega
  rw [reduceBucketColumn]
  have he : (3*(256*digit+n+width)).toUSize =
      3*(256*digit.toUSize+n.toUSize)+3*width.toUSize := by
    rw [show 3*(256*digit+n+width) = 3*(256*digit+n)+3*width by omega]
    simp only [Nat.toUSize,USize.ofNat_add,USize.ofNat_mul]
    rfl
  unfold addBucket bucketValue
  simp only [readWord,writeWord,Nat.toUSize,USize.ofNat_add,USize.ofNat_mul] at he ⊢
  have h1 : readWord (writeWord buckets (3*(256*digit+n))
        (readWord buckets (3*(256*digit+n)) ^^^
          readWord buckets (3*(256*digit+n+width)))) (3*(256*digit+n)+1) =
      readWord buckets (3*(256*digit+n)+1) := by
    rw [readWord_writeWord _ _ _ (by omega) (by omega),ite_eq_right (by omega)]
  have h2 (v0 v1 : UInt64) :
      readWord (writeWord (writeWord buckets (3*(256*digit+n)) v0)
        (3*(256*digit+n)+1) v1) (3*(256*digit+n)+2) =
      readWord buckets (3*(256*digit+n)+2) := by
    rw [readWord_writeWord _ _ _ (by omega) (by omega),ite_eq_right (by omega),
      readWord_writeWord _ _ _ (by omega) (by omega),ite_eq_right (by omega)]
  simp only [readWord,writeWord,Nat.toUSize,USize.ofNat_add,USize.ofNat_mul] at h1 h2
  simp only [show USize.ofNat 3 = (3 : USize) from rfl,
    show USize.ofNat 256 = (256 : USize) from rfl,
    show USize.ofNat 1 = (1 : USize) from rfl,
    show USize.ofNat 2 = (2 : USize) from rfl] at he h1 h2 ⊢
  rw [he] at h1
  rw [he,h1,h2]

/-- The production scalar-state reducer equals a structural recursion on natural columns. -/
theorem reduceBucketColumn_eq (digit width n : Nat) (hd : digit < 6)
    (hw : width ≤ 128) (hn : n ≤ width) (buckets : FixedWords (6*256*3))
    (c0 c1 c2 : UInt64) :
    reduceBucketColumn digit.toUSize width.toUSize n buckets c0 c1 c2 =
      reduceBuckets digit width n buckets ⟨⟨c0⟩,⟨c1⟩,⟨c2⟩⟩ := by
  induction n generalizing buckets c0 c1 c2 with
  | zero => rfl
  | succ n ih =>
    rw [reduceBucketColumn_step digit width n hd hw (by omega),reduceBuckets]
    exact ih (by omega) _ _ _ _

/-- Reducing a column sums its high half and adds each high bucket to its paired low bucket. -/
theorem reduceBuckets_spec (digit width n : Nat) (hd : digit < 6)
    (hw : width ≤ 128) (hn : n ≤ width) (buckets : FixedWords (6*256*3)) (value : W) :
    (reduceBuckets digit width n buckets value).value =
        value + ∑ k ∈ Finset.range n, bucketValue buckets (256*digit+width+k) ∧
      ∀ i : Fin (6*256),
        bucketValue (reduceBuckets digit width n buckets value).buckets i.val =
          bucketValue buckets i.val +
            if 256*digit ≤ i.val ∧ i.val < 256*digit+n
            then bucketValue buckets (i.val+width) else 0 := by
  induction n generalizing buckets value with
  | zero =>
    constructor
    · simp only [reduceBuckets,BucketColumn.value,Finset.range_zero,Finset.sum_empty,add_zero]
    · intro i
      rw [reduceBuckets,ite_eq_right (by omega),add_zero]
  | succ n ih =>
    have hl : 256*digit+n < 6*256 := by omega
    let high := bucketValue buckets (256*digit+n+width)
    let next := addBucket buckets (256*digit+n) high
    obtain ⟨hc,hb⟩ := ih (by omega) next (value+high)
    have hh (k : Nat) (hk : k < width) :
        bucketValue next (256*digit+width+k) = bucketValue buckets (256*digit+width+k) := by
      have hidx : 256*digit+width+k < 6*256 := by omega
      rw [show next = addBucket buckets (256*digit+n) high from rfl,
        bucketValue_addBucket buckets ⟨256*digit+n,hl⟩ ⟨256*digit+width+k,hidx⟩ high,
        ite_eq_right (by intro he; have h := congrArg Fin.val he; dsimp only at h; omega),add_zero]
    constructor
    · change (reduceBuckets digit width n next (value+high)).value = _
      rw [hc,Finset.sum_range_succ]
      have hs : (∑ k ∈ Finset.range n, bucketValue next (256*digit+width+k)) =
          ∑ k ∈ Finset.range n, bucketValue buckets (256*digit+width+k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hh k (by have := Finset.mem_range.mp hk; omega)
      rw [hs]
      dsimp only [high]
      rw [show 256*digit+n+width = 256*digit+width+n by omega]
      ac_rfl
    · intro i
      change bucketValue (reduceBuckets digit width n next (value+high)).buckets i.val = _
      rw [hb i]
      have hi := i.isLt
      rw [show next = addBucket buckets (256*digit+n) high from rfl,
        bucketValue_addBucket buckets ⟨256*digit+n,hl⟩ i high]
      by_cases hsmall : 256*digit ≤ i.val ∧ i.val < 256*digit+n
      · have hne : (⟨256*digit+n,hl⟩ : Fin (6*256)) ≠ i := by
          intro he
          have h := congrArg Fin.val he
          dsimp only at h
          omega
        rw [ite_eq_right hne,add_zero,ite_eq_left hsmall,ite_eq_left (by omega)]
        have hidx : i.val+width < 6*256 := by omega
        rw [bucketValue_addBucket buckets ⟨256*digit+n,hl⟩ ⟨i.val+width,hidx⟩ high,
          ite_eq_right (by intro he; have h := congrArg Fin.val he; dsimp only at h; omega),add_zero]
      · rw [ite_eq_right hsmall]
        by_cases he : (⟨256*digit+n,hl⟩ : Fin (6*256)) = i
        · have hei := congrArg Fin.val he
          dsimp only at hei
          rw [ite_eq_left he,ite_eq_left (by omega),add_zero]
          congr 1
          dsimp only [high]
          congr 1
          omega
        · have hnei : 256*digit+n ≠ i.val := fun h => he (Fin.ext h)
          rw [ite_eq_right he,ite_eq_right (by omega),add_zero,add_zero]

/-- Position weights grouped by the low bits of a byte. -/
def byteBucketSum (bytes : Nat → Nat) (weights : Nat → W) (width value : Nat) : W :=
  ∑ j ∈ Finset.range 1600, if bytes j % width = value then weights j else 0

/-- The two halves of a double-width residue partition a single-width residue. -/
theorem residue_halves (x width value : Nat) (hw : 0 < width) (hv : value < width) :
    x % width = value ↔ x % (2*width) = value ∨ x % (2*width) = value+width := by
  have hm := Nat.mod_lt x (show 0 < 2*width by omega)
  have he : x % (2*width) % width = x % width :=
    Nat.mod_mod_of_dvd x (dvd_mul_left width 2)
  by_cases h : x % (2*width) < width
  · rw [Nat.mod_eq_of_lt h] at he
    omega
  · have hh : x % (2*width) % width = x % (2*width)-width := by
      rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
    rw [hh] at he
    omega

/-- Folding paired byte buckets combines their disjoint position-weight sums. -/
theorem byteBucketSum_split (bytes : Nat → Nat) (weights : Nat → W)
    (width value : Nat) (hw : 0 < width) (hv : value < width) :
    byteBucketSum bytes weights (2*width) value +
        byteBucketSum bytes weights (2*width) (value+width) =
      byteBucketSum bytes weights width value := by
  rw [byteBucketSum,byteBucketSum,byteBucketSum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have he := residue_halves (bytes j) width value hw hv
  by_cases h0 : bytes j % (2*width) = value
  · rw [ite_eq_left h0,ite_eq_right (by omega),add_zero,ite_eq_left (he.mpr (Or.inl h0))]
  · rw [ite_eq_right h0,zero_add]
    by_cases h1 : bytes j % (2*width) = value+width
    · rw [ite_eq_left h1,ite_eq_left (he.mpr (Or.inr h1))]
    · rw [ite_eq_right h1,ite_eq_right (by tauto)]

/-- A live byte-bucket prefix groups position weights by its current residue width. -/
def BucketsMatch (buckets : FixedWords (6*256*3)) (digit width : Nat)
    (bytes : Nat → Nat) (weights : Nat → W) : Prop :=
  ∀ value < width, bucketValue buckets (256*digit+value) = byteBucketSum bytes weights width value

/-- Paired bucket reduction preserves the residue invariant at half the width. -/
theorem reduceBuckets_match (digit width : Nat) (hd : digit < 6) (hw : width ≤ 128)
    (hw0 : 0 < width) (buckets : FixedWords (6*256*3)) (value : W)
    (bytes : Nat → Nat) (weights : Nat → W)
    (hm : BucketsMatch buckets digit (2*width) bytes weights) :
    BucketsMatch (reduceBuckets digit width width buckets value).buckets digit width bytes weights := by
  intro k hk
  obtain ⟨_,hb⟩ := reduceBuckets_spec digit width width hd hw (by omega) buckets value
  have hi : 256*digit+k < 6*256 := by omega
  have h := hb ⟨256*digit+k,hi⟩
  dsimp only at h
  rw [ite_eq_left (by omega),hm k (by omega),
    show 256*digit+k+width = 256*digit+(k+width) by omega,
    hm (k+width) (by omega)] at h
  exact h.trans (byteBucketSum_split bytes weights width k hw0 hk)

/-- The high-half residue indicator is exactly the selected binary coefficient. -/
theorem testBit_high_half (x bit : Nat) :
    x.testBit bit = decide (2^bit ≤ x % (2*2^bit)) := by
  have hw : 0 < 2^bit := Nat.two_pow_pos bit
  have hr := Nat.mod_lt x (show 0 < 2*2^bit by omega)
  have he := Nat.testBit_mod_two_pow x (bit+1) bit
  simp only [Nat.lt_succ_self,decide_true,Bool.true_and] at he
  rw [Nat.pow_succ,show 2^bit*2 = 2*2^bit by omega] at he
  rw [← he,Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : 2^bit ≤ x % (2*2^bit)
  · have hd : x % (2*2^bit) / 2^bit = 1 := (Nat.div_eq_iff hw).mpr (by omega)
    rw [hd]
    simp only [Nat.reduceMod,h,decide_true]
  · rw [Nat.div_eq_of_lt (by omega)]
    simp only [Nat.zero_mod,Nat.reduceEqDiff,decide_false,h]

/-- Summing the high byte buckets selects exactly positions with the current bit set. -/
theorem byteBucketSum_high (bytes : Nat → Nat) (weights : Nat → W) (bit : Nat) :
    (∑ k ∈ Finset.range (2^bit), byteBucketSum bytes weights (2*2^bit) (2^bit+k)) =
      ∑ j ∈ Finset.range 1600, if (bytes j).testBit bit then weights j else 0 := by
  simp only [byteBucketSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [testBit_high_half]
  have hw := Nat.two_pow_pos bit
  have hr := Nat.mod_lt (bytes j) (show 0 < 2*2^bit by omega)
  by_cases h : 2^bit ≤ bytes j % (2*2^bit)
  · rw [ite_eq_left (by simpa only [decide_eq_true_eq] using h)]
    have hk : bytes j % (2*2^bit)-2^bit < 2^bit := by omega
    rw [Finset.sum_eq_single (bytes j % (2*2^bit)-2^bit)]
    · rw [ite_eq_left (by omega)]
    · intro k _ hne
      rw [ite_eq_right (by omega)]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hk)).elim
  · rw [ite_eq_right (by simpa only [decide_eq_true_eq] using h)]
    apply Finset.sum_eq_zero
    intro k _
    rw [ite_eq_right (by omega)]

/-- The accumulated column value is the position-weight sum for its selected byte bit. -/
theorem reduceBuckets_value (digit bit : Nat) (hd : digit < 6) (hb : bit < 8)
    (buckets : FixedWords (6*256*3)) (bytes : Nat → Nat) (weights : Nat → W)
    (hm : BucketsMatch buckets digit (2*2^bit) bytes weights) :
    (reduceBuckets digit (2^bit) (2^bit) buckets 0).value =
      ∑ j ∈ Finset.range 1600, if (bytes j).testBit bit then weights j else 0 := by
  have hw : 2^bit ≤ 128 := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show bit ≤ 7 by omega)
    exact this
  rw [(reduceBuckets_spec digit (2^bit) (2^bit) hd hw (by omega) buckets 0).1,zero_add]
  have hs : (∑ k ∈ Finset.range (2^bit), bucketValue buckets (256*digit+2^bit+k)) =
      ∑ k ∈ Finset.range (2^bit), byteBucketSum bytes weights (2*2^bit) (2^bit+k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [show 256*digit+2^bit+k = 256*digit+(2^bit+k) by omega]
    exact hm (2^bit+k) (by have := Finset.mem_range.mp hk; omega)
  rw [hs,byteBucketSum_high]

/-- The byte at a little-endian polynomial digit of one payload word. -/
def payloadByte (payload : FixedWords 1600) (digit j : Nat) : Nat :=
  ((readWord payload j >>> (8*digit).toUInt64) &&& 255).toNat

/-- Reading a payload byte preserves exactly its eight little-endian coefficients. -/
theorem payloadByte_testBit (payload : FixedWords 1600) (digit j bit : Nat)
    (hd : digit < 6) (hb : bit < 8) :
    (payloadByte payload digit j).testBit bit =
      (readWord payload j).toNat.testBit (8*digit+bit) := by
  have hs : ((8*digit).toUInt64).toNat % 64 = 8*digit := by
    rw [Nat.toUInt64,UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)]
  simp only [payloadByte,UInt64.toNat_and,UInt64.toNat_shiftRight,hs,UInt64.reduceToNat,
    Nat.testBit_and,Nat.testBit_shiftRight]
  have hm : (255 : Nat).testBit bit = true := by
    simpa only [show (2^8-1 : Nat) = 255 from rfl,hb,decide_true] using
      Nat.testBit_two_pow_sub_one 8 bit
  rw [hm,Bool.and_true]

/-- Reducing one digit preserves every bucket belonging to another digit. -/
theorem reduceBuckets_other (digit width n query byte : Nat) (hd : digit < 6)
    (hw : width ≤ 128) (hn : n ≤ width) (hq : query < 6) (hb : byte < 256)
    (hne : digit ≠ query) (buckets : FixedWords (6*256*3)) (value : W) :
    bucketValue (reduceBuckets digit width n buckets value).buckets (256*query+byte) =
      bucketValue buckets (256*query+byte) := by
  have hi : 256*query+byte < 6*256 := by omega
  have h := (reduceBuckets_spec digit width n hd hw hn buckets value).2 ⟨256*query+byte,hi⟩
  dsimp only at h
  rw [ite_eq_right (by omega),add_zero] at h
  exact h

/-- Structural recursion over the eight descending bit columns of one payload byte. -/
def reducePayloadBits (digit : Nat) : Nat → FixedWords (6*256*3) → PackedE →
    FixedWords (6*256*3) × PackedE
  | 0, buckets, out => (buckets,out)
  | bit+1, buckets, out =>
    let column := reduceBuckets digit (2^bit) (2^bit) buckets 0
    let out := if 8*digit+bit < 47 then out.set (8*digit+bit) column.value else out
    reducePayloadBits digit bit column.buckets out

/-- Structural byte reduction preserves the exact output length. -/
theorem reducePayloadBits_size (digit n : Nat) (buckets : FixedWords (6*256*3))
    (out : PackedE) (hout : out.size = 47) :
    (reducePayloadBits digit n buckets out).2.size = 47 := by
  induction n generalizing buckets out with
  | zero => exact hout
  | succ n ih =>
    rw [reducePayloadBits]
    apply ih
    split
    · rw [PackedE.size_set _ _ _ (by omega),hout]
    · exact hout

/-- Reduction of a byte preserves the initial buckets of every other digit. -/
theorem reducePayloadBits_other (digit n query byte : Nat) (hd : digit < 6)
    (hn : n ≤ 8) (hq : query < 6) (hb : byte < 256) (hne : digit ≠ query)
    (buckets : FixedWords (6*256*3)) (out : PackedE) :
    bucketValue (reducePayloadBits digit n buckets out).1 (256*query+byte) =
      bucketValue buckets (256*query+byte) := by
  induction n generalizing buckets out with
  | zero => rfl
  | succ n ih =>
    rw [reducePayloadBits,ih (by omega)]
    apply reduceBuckets_other digit (2^n) (2^n) query byte hd _ (by omega) hq hb hne
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : n ≤ 7)

/-- Each reduced output coefficient is precisely the position-weight sum for its payload bit. -/
theorem reducePayloadBits_get (digit n : Nat) (hd : digit < 6) (hn : n ≤ 8)
    (buckets : FixedWords (6*256*3)) (out : PackedE) (hout : out.size = 47)
    (bytes : Nat → Nat) (weights : Nat → W) (hm : BucketsMatch buckets digit (2^n) bytes weights)
    (i : Fin 47) :
    (reducePayloadBits digit n buckets out).2.get i.val =
      if 8*digit ≤ i.val ∧ i.val < 8*digit+n then
        ∑ j ∈ Finset.range 1600, if (bytes j).testBit (i.val-8*digit) then weights j else 0
      else out.get i.val := by
  induction n generalizing buckets out with
  | zero => rw [reducePayloadBits,ite_eq_right (by omega)]
  | succ n ih =>
    have hnb : n < 8 := by omega
    have hw : 2^n ≤ 128 := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : n ≤ 7)
    let column := reduceBuckets digit (2^n) (2^n) buckets 0
    have hm0 : BucketsMatch buckets digit (2*2^n) bytes weights := by
      simpa only [Nat.pow_succ,Nat.mul_comm] using hm
    have hm1 := reduceBuckets_match digit (2^n) hd hw (Nat.two_pow_pos n) buckets 0 bytes weights hm0
    have hc := reduceBuckets_value digit n hd hnb buckets bytes weights hm0
    rw [reducePayloadBits,ih (by omega) _ _ (by
      split
      · rw [PackedE.size_set _ _ _ (by omega),hout]
      · exact hout) hm1]
    have hi := i.isLt
    by_cases hsmall : 8*digit ≤ i.val ∧ i.val < 8*digit+n
    · rw [ite_eq_left hsmall,ite_eq_left (by omega)]
    · rw [ite_eq_right hsmall]
      by_cases hlast : i.val = 8*digit+n
      · have hbound : 8*digit+n < 47 := by omega
        rw [ite_eq_left hbound,PackedE.get_set _ _ _ (by omega) (by omega),
          ite_eq_left (by omega),ite_eq_left (by omega),hc]
        rw [show i.val-8*digit = n by omega]
      · have hcover : ¬(8*digit ≤ i.val ∧ i.val < 8*digit+(n+1)) := by omega
        rw [ite_eq_right hcover]
        split
        · rw [PackedE.get_set _ _ _ (by omega) (by omega),ite_eq_right (by omega)]
        · rfl

end CompStark.Keccak.GkrProver
