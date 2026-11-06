/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Hash
import Mathlib.Tactic.IntervalCases

public section
namespace CompStark.Keccak

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- Every scalar round agrees with VCVio, for any continuation. -/
theorem roundWith_eq {α : Type} (k : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → α)
    (rc : UInt64) (s : Array UInt64) :
    roundWith k rc s[0]! s[1]! s[2]! s[3]! s[4]! s[5]! s[6]! s[7]! s[8]! s[9]! s[10]! s[11]! s[12]! s[13]! s[14]! s[15]! s[16]! s[17]! s[18]! s[19]! s[20]! s[21]! s[22]! s[23]! s[24]! =
      let t := VCVio.Algorithms.Keccak.round s rc
      k t[0]! t[1]! t[2]! t[3]! t[4]! t[5]! t[6]! t[7]! t[8]! t[9]! t[10]! t[11]! t[12]! t[13]! t[14]! t[15]! t[16]! t[17]! t[18]! t[19]! t[20]! t[21]! t[22]! t[23]! t[24]! := by
  simp [roundWith, VCVio.Algorithms.Keccak.round, VCVio.Algorithms.Keccak.rotl64,
    VCVio.Algorithms.Keccak.piLUT, VCVio.Algorithms.Keccak.rhoLUT, List.range_succ]

/-- Reading the 25 lanes reconstructs a state of the permutation's width. -/
theorem lanes_eq (s : Array UInt64) (hs : s.size = 25) :
    #[s[0]!, s[1]!, s[2]!, s[3]!, s[4]!, s[5]!, s[6]!, s[7]!, s[8]!, s[9]!, s[10]!, s[11]!, s[12]!, s[13]!, s[14]!, s[15]!, s[16]!, s[17]!, s[18]!, s[19]!, s[20]!, s[21]!, s[22]!, s[23]!, s[24]!] = s := by
  apply Array.ext
  · exact hs.symm
  · intro i hi hj
    have h : i < 25 := hi
    interval_cases i <;> simp_all

/-- Every VCVio round produces exactly 25 lanes. -/
@[simp] theorem size_round (s : Array UInt64) (rc : UInt64) :
    (VCVio.Algorithms.Keccak.round s rc).size = 25 := by
  simp [VCVio.Algorithms.Keccak.round]

/-- The scalar loop agrees with the specification after any number of rounds. -/
theorem permute_eq (n r : Nat) (s : Array UInt64) (hs : s.size = 25) :
    permute n r s[0]! s[1]! s[2]! s[3]! s[4]! s[5]! s[6]! s[7]! s[8]! s[9]! s[10]! s[11]! s[12]! s[13]! s[14]! s[15]! s[16]! s[17]! s[18]! s[19]! s[20]! s[21]! s[22]! s[23]! s[24]! =
      (List.range' r n).foldl (fun t j ↦
        VCVio.Algorithms.Keccak.round t VCVio.Algorithms.Keccak.roundConstants[j]!) s := by
  induction n generalizing r s with
  | zero => exact lanes_eq s hs
  | succ n ih =>
    rw [permute, roundWith_eq, ih _ _ (size_round _ _)]
    rfl

/-- A nonempty scalar run agrees for every input array. -/
theorem permute_succ_eq (n r : Nat) (s : Array UInt64) :
    permute (n + 1) r s[0]! s[1]! s[2]! s[3]! s[4]! s[5]! s[6]! s[7]! s[8]! s[9]! s[10]! s[11]! s[12]! s[13]! s[14]! s[15]! s[16]! s[17]! s[18]! s[19]! s[20]! s[21]! s[22]! s[23]! s[24]! =
      (List.range' r (n + 1)).foldl (fun t j ↦
        VCVio.Algorithms.Keccak.round t VCVio.Algorithms.Keccak.roundConstants[j]!) s := by
  rw [permute, roundWith_eq, permute_eq _ _ _ (size_round _ _)]
  rfl

/-- The complete scalar permutation is VCVio's Keccak-f[1600]. -/
@[simp] theorem f1600_eq (s : Array UInt64) :
    f1600 s = VCVio.Algorithms.Keccak.f1600 s := by
  simpa only [f1600, VCVio.Algorithms.Keccak.f1600, List.range_eq_range'] using
    permute_succ_eq 23 0 s

/-- Successive XORs into one lane combine, including out-of-bounds updates. -/
theorem xorAt_xorAt (s : Array UInt64) (i : Nat) (a b : UInt64) :
    xorAt (xorAt s i a) i b = xorAt s i (a ^^^ b) := by
  by_cases h : i < s.size
  · simp [xorAt, h, Array.set!_eq_setIfInBounds, UInt64.xor_assoc]
  · simp [xorAt, Array.set!_eq_setIfInBounds, Array.setIfInBounds, h]

/-- The byte-at-a-time absorb step of VCVio's sponge. -/
def absorbBytes (input : ByteArray) (offset : Nat) (initial : Array UInt64) :
    Array UInt64 := Id.run do
  let mut s := initial
  for i in [0:136] do
    let bv : UInt64 := input[offset + i]!.toNat.toUInt64
    s := xorAt s (i / 8) (bv <<< ((i % 8) * 8).toUInt64)
  return s

/-- Whole-lane loading absorbs exactly the same bytes as the reference loop. -/
theorem absorbBlock_eq (input : ByteArray) (offset : Nat) (s : Array UInt64) :
    absorbBlock input offset s = absorbBytes input offset s := by
  simp [absorbBlock, absorbBytes, List.range'_succ, xorAt_xorAt, readLane, UInt64.xor_assoc]

/-- The optimized absorber is VCVio's Keccak-256 absorber. -/
@[simp] theorem absorb_eq (input : ByteArray) :
    absorb input = VCVio.Algorithms.Keccak.absorb input 136 0x01 := by
  simp only [absorb, absorbBlock_eq, f1600_eq]
  rfl

/-- Exact equality of all digest bytes with VCVio's original Keccak-256. -/
@[simp] theorem keccak256_eq (input : ByteArray) :
    keccak256 input = VCVio.Algorithms.Keccak.keccak256 input := by
  simp only [keccak256, absorb_eq, VCVio.Algorithms.Keccak.keccak256]

/-- Independent permutation batches preserve input order and every output lane. -/
@[simp] theorem f1600Batch_eq (states : Array (Array UInt64)) :
    f1600Batch states = states.map VCVio.Algorithms.Keccak.f1600 := by
  exact congrArg (fun f : Array UInt64 → Array UInt64 ↦ states.map f) (funext f1600_eq)

/-- Independent hash batches preserve input order and every digest byte. -/
@[simp] theorem keccak256Batch_eq (inputs : Array ByteArray) :
    keccak256Batch inputs = inputs.map VCVio.Algorithms.Keccak.keccak256 := by
  exact congrArg (fun f : ByteArray → ByteArray ↦ inputs.map f) (funext keccak256_eq)

/-- Node hashing is the reference hash of the left and right child bytes. -/
@[simp] theorem hashNode_eq (left right : ByteArray) (hl : left.size = 32)
    (hr : right.size = 32) :
    hashNode left right hl hr = VCVio.Algorithms.Keccak.keccak256 (left ++ right) := by
  exact keccak256_eq _

/-- Leaf hashing is the reference hash of the complete 512-byte payload. -/
@[simp] theorem hashLeaf_eq (payload : ByteArray) (h : payload.size = 512) :
    hashLeaf payload h = VCVio.Algorithms.Keccak.keccak256 payload := by
  exact keccak256_eq _

/-- Keccak-256 always returns a 32-byte digest. -/
@[simp] theorem size_keccak256 (input : ByteArray) : (keccak256 input).size = 32 :=
  VCVio.Algorithms.Keccak.squeeze_size _ _

end CompStark.Keccak
