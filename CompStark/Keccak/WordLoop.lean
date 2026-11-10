/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Scalar

/-! Scalar Keccak rounds with unboxed counters and a lane-zero projection for nonce probes. -/

@[expose] public section
namespace CompStark.Keccak

/-- Scalar rounds with unboxed 32-bit loop counters. -/
def permute32 (n r : UInt32) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 : UInt64) : Array UInt64 :=
  if n = 0 then #[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24]
  else roundWith (permute32 (n - 1) (r + 1))
    VCVio.Algorithms.Keccak.roundConstants[r.toNat]! a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
termination_by n.toNat
 decreasing_by
  have hn : n.toNat ≠ 0 := by intro h; apply ‹¬n = 0›; exact UInt32.toNat_inj.mp h
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; change 1 ≤ n.toNat; omega)]
  change n.toNat - 1 < n.toNat
  omega

/-- Scalar rounds with unboxed 32-bit loop counters and only lane zero as output. -/
def permute32First (n r : UInt32) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 : UInt64) : UInt64 :=
  if n = 0 then a0
  else roundWith (permute32First (n - 1) (r + 1))
    VCVio.Algorithms.Keccak.roundConstants[r.toNat]! a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
termination_by n.toNat
 decreasing_by
  have hn : n.toNat ≠ 0 := by intro h; apply ‹¬n = 0›; exact UInt32.toNat_inj.mp h
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; change 1 ≤ n.toNat; omega)]
  change n.toNat - 1 < n.toNat
  omega

/-- Keccak-f[1600] over scalar lanes and unboxed loop counters. -/
def f1600WordLoop (s : Array UInt64) : Array UInt64 :=
  permute32 24 0
    s[0]! s[1]! s[2]! s[3]! s[4]! s[5]! s[6]! s[7]! s[8]! s[9]! s[10]! s[11]! s[12]! s[13]! s[14]! s[15]! s[16]! s[17]! s[18]! s[19]! s[20]! s[21]! s[22]! s[23]! s[24]!

/-- Read only lane zero of a permutation whose one input lane is overwritten. -/
def f1600FirstOverwrite (s : @& Array UInt64) (lane : Nat) (value : UInt64) : UInt64 :=
  permute32First 24 0
    (if lane = 0 then value else s[0]!) (if lane = 1 then value else s[1]!) (if lane = 2 then value else s[2]!) (if lane = 3 then value else s[3]!) (if lane = 4 then value else s[4]!)
    (if lane = 5 then value else s[5]!) (if lane = 6 then value else s[6]!) (if lane = 7 then value else s[7]!) (if lane = 8 then value else s[8]!) (if lane = 9 then value else s[9]!)
    (if lane = 10 then value else s[10]!) (if lane = 11 then value else s[11]!) (if lane = 12 then value else s[12]!) (if lane = 13 then value else s[13]!) (if lane = 14 then value else s[14]!)
    (if lane = 15 then value else s[15]!) (if lane = 16 then value else s[16]!) (if lane = 17 then value else s[17]!) (if lane = 18 then value else s[18]!) (if lane = 19 then value else s[19]!)
    (if lane = 20 then value else s[20]!) (if lane = 21 then value else s[21]!) (if lane = 22 then value else s[22]!) (if lane = 23 then value else s[23]!) (if lane = 24 then value else s[24]!)

/-- Unboxed counters execute the same scalar rounds before their counter range ends. -/
theorem permute32_eq (n r : Nat) (bound : n + r < 4294967296)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 : UInt64) :
    permute32 n.toUInt32 r.toUInt32 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 = permute n r a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 := by
  induction n generalizing r a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 with
  | zero => rw [permute32]; rfl
  | succ n ih =>
    have hn : (n + 1).toUInt32 ≠ 0 := by
      intro h
      have eq := congrArg UInt32.toNat h
      simp only [UInt32.toNat_ofNat', UInt32.toNat_zero] at eq
      omega
    have hsub : (n + 1).toUInt32 - 1 = n.toUInt32 := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_sub_of_le _ _ (by
        simp only [UInt32.le_iff_toNat_le, UInt32.toNat_one, UInt32.toNat_ofNat']; omega)]
      simp only [UInt32.toNat_ofNat', UInt32.toNat_one]
      omega
    have hadd : r.toUInt32 + 1 = (r + 1).toUInt32 := by
      apply UInt32.toNat_inj.mp
      simp only [UInt32.toNat_add, UInt32.toNat_one, UInt32.toNat_ofNat']
      omega
    have hr : r.toUInt32.toNat = r := by
      simp only [UInt32.toNat_ofNat']; omega
    rw [permute32, ite_eq_right hn, hsub, hadd, hr, permute]
    have tail : permute32 n.toUInt32 (r + 1).toUInt32 = permute n (r + 1) := by
      funext a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
      exact ih (r + 1) (by omega) a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    rw [tail]

/-- Unboxed loop counters retain the complete specification permutation. -/
@[csimp] theorem f1600_word_code : f1600 = f1600WordLoop := by
  funext s
  exact (permute32_eq 24 0 (by decide) s[0]! s[1]! s[2]! s[3]! s[4]! s[5]! s[6]! s[7]! s[8]! s[9]! s[10]! s[11]! s[12]! s[13]! s[14]! s[15]! s[16]! s[17]! s[18]! s[19]! s[20]! s[21]! s[22]! s[23]! s[24]!).symm

end CompStark.Keccak
