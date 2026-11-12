/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Keccak.GkrProver.Refinement
/-! Machine-indexed loops for binary Keccak payloads. -/
@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
/-- Small natural coordinates have their exact native representation. -/
theorem payloadIndex (j : Nat) (hj : j ≤ 1600) : j.toUSize.toNat = j := by
  rw [Nat.toUSize, USize.toNat_ofNat_of_lt' (by have := USize.le_size; omega)]
/-- The native successor of a payload coordinate does not wrap. -/
theorem payloadNext (j : USize) (hj : j.toNat < 1600) : (j+1).toNat = j.toNat+1 := by
  rw [USize.toNat_add, USize.toNat_one]
  change (j.toNat+1)%USize.size = j.toNat+1
  exact Nat.mod_eq_of_lt (by have := USize.le_size; omega)
/-- The payload bound is a native comparison on either supported word width. -/
theorem payloadBound (j : USize) : (j < (1600 : USize)) ↔ j.toNat < 1600 := by
  rw [USize.lt_iff_toNat_lt, USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)]
/-- Scatter the six payload digits using a native position counter. -/
def scatterPayloadLoop (payload : FixedWords 1600) (weights : FixedWords 4800)
    (j : USize) (buckets : FixedWords (6*256*3)) : FixedWords (6*256*3) :=
  if hj : j < 1600 then
    let p := readUWord payload j
    let w0 := readUWord weights (3*j)
    let w1 := readUWord weights (3*j+1)
    let w2 := readUWord weights (3*j+2)
    let buckets := scatterDigit buckets 0 p w0 w1 w2
    let buckets := scatterDigit buckets 1 (p >>> 8) w0 w1 w2
    let buckets := scatterDigit buckets 2 (p >>> 16) w0 w1 w2
    let buckets := scatterDigit buckets 3 (p >>> 24) w0 w1 w2
    let buckets := scatterDigit buckets 4 (p >>> 32) w0 w1 w2
    let buckets := scatterDigit buckets 5 (p >>> 40) w0 w1 w2
    scatterPayloadLoop payload weights (j+1) buckets
  else buckets
termination_by 1600-j.toNat
decreasing_by
  have hn : j.toNat < 1600 := (payloadBound j).mp (by assumption)
  rw [payloadNext j hn]
  omega
/-- Native scatter state preserves the exact reference buckets. -/
theorem scatterPayloadLoop_eq (payload : FixedWords 1600) (weights : FixedWords 4800)
    (j : USize) (out : FixedWords (6*256*3)) :
    scatterPayloadLoop payload weights j out = scatterPayload payload weights j.toNat out := by
  rw [scatterPayloadLoop, scatterPayload]
  split
  · rename_i hj
    have hn := (payloadBound j).mp hj
    simp only [hn, dite_true, USize.ofNat_toNat, Nat.toUSize]
    rw [scatterPayloadLoop_eq, payloadNext j hn]
  · rename_i hj
    simp only [show ¬j.toNat < 1600 from fun h => hj ((payloadBound j).mpr h), dite_false]
termination_by 1600-j.toNat
decreasing_by
  have hn : j.toNat < 1600 := by assumption
  rw [payloadNext j hn]
  omega
/-- Enter the native scatter loop from a natural prefix coordinate. -/
def scatterPayloadDirect (payload : FixedWords 1600) (weights : FixedWords 4800)
    (j : Nat) (out : FixedWords (6*256*3)) : FixedWords (6*256*3) :=
  if j < 1600 then scatterPayloadLoop payload weights j.toUSize out else out
/-- Native scatter preserves every payload bucket. -/
@[csimp] theorem scatterPayload_code : scatterPayload = scatterPayloadDirect := by
  funext payload weights j out
  unfold scatterPayloadDirect
  split
  · rename_i hj
    rw [scatterPayloadLoop_eq, payloadIndex j (by omega)]
  · rename_i hj
    rw [scatterPayload, dite_eq_right hj]
/-- Reduce a bucket column with a native countdown and scalar accumulators. -/
def reduceBucketColumnU (digit width n : USize) (buckets : FixedWords (6*256*3))
    (c0 c1 c2 : UInt64) : BucketColumn :=
  if hz : n = 0 then ⟨buckets,c0,c1,c2⟩ else
    have h1 : (1 : USize) ≤ n := by
      rw [USize.le_iff_toNat_le, USize.toNat_one]
      have hne : n.toNat ≠ 0 := fun h => hz (USize.toNat_inj.mp h)
      omega
    let low := 3*(256*digit+(n-1))
    let high := low+3*width
    let h0 := readUWord buckets high
    let h1 := readUWord buckets (high+1)
    let h2 := readUWord buckets (high+2)
    let buckets := writeUWord buckets low (readUWord buckets low ^^^ h0)
    let buckets := writeUWord buckets (low+1) (readUWord buckets (low+1) ^^^ h1)
    let buckets := writeUWord buckets (low+2) (readUWord buckets (low+2) ^^^ h2)
    reduceBucketColumnU digit width (n-1) buckets (c0 ^^^ h0) (c1 ^^^ h1) (c2 ^^^ h2)
termination_by n.toNat
decreasing_by
  rw [USize.toNat_sub_of_le _ _ (by assumption), USize.toNat_one]
  have _hp : 1 ≤ n.toNat := by simpa only [USize.le_iff_toNat_le, USize.toNat_one] using (by assumption : (1 : USize) ≤ n)
  omega
/-- Native reduction preserves the complete retained bucket state and all coordinates. -/
theorem reduceBucketColumnU_eq (digit width n : USize) (buckets : FixedWords (6*256*3))
    (c0 c1 c2 : UInt64) :
    reduceBucketColumnU digit width n buckets c0 c1 c2 =
      reduceBucketColumn digit width n.toNat buckets c0 c1 c2 := by
  rw [reduceBucketColumnU]
  split
  · rename_i hz
    subst n
    rfl
  · rename_i hz
    have h1 : (1 : USize) ≤ n := by
      rw [USize.le_iff_toNat_le, USize.toNat_one]
      have hne : n.toNat ≠ 0 := fun h => hz (USize.toNat_inj.mp h)
      omega
    have he : n.toNat = (n-1).toNat+1 := by
      rw [USize.toNat_sub_of_le _ _ h1, USize.toNat_one]
      have _hp : 1 ≤ n.toNat := by simpa only [USize.le_iff_toNat_le, USize.toNat_one] using h1
      omega
    rw [reduceBucketColumnU_eq]
    conv_rhs => rw [he, reduceBucketColumn]
    simp only [Nat.toUSize, USize.ofNat_toNat]
termination_by n.toNat
decreasing_by
  rw [USize.toNat_sub_of_le _ _ (by assumption), USize.toNat_one]
  have _hp : 1 ≤ n.toNat := by simpa only [USize.le_iff_toNat_le, USize.toNat_one] using (by assumption : (1 : USize) ≤ n)
  omega
/-- Compile the weightedPayload driver with machine-indexed payload loops. -/
def weightedPayloadNative (payload : FixedWords 1600) (weights : FixedWords 4800) : PackedE := Id.run do
  let mut buckets := scatterPayload payload weights 0 (zeroWords (6*256*3))
  let mut out := PackedE.zeros 47
  let mut digit : USize := 0
  while digit < 6 do
    let mut width : USize := 128
    let mut bit : USize := 7
    while width != 0 do
      let column := reduceBucketColumnU digit width width buckets 0 0 0
      buckets := column.buckets
      if (8*digit+bit).toNat < 47 then
        out := out.set (8*digit+bit).toNat ⟨⟨column.c0⟩,⟨column.c1⟩,⟨column.c2⟩⟩
      width := width >>> 1
      bit := bit-1
    digit := digit+1
  return out

/-- Native driver compilation preserves every weightedPayload result. -/
@[csimp] theorem weightedPayload_native_code : weightedPayload = weightedPayloadNative := by
  funext payload weights
  unfold weightedPayload weightedPayloadNative
  simp only [reduceBucketColumnU_eq]
end CompStark.Keccak.GkrProver
