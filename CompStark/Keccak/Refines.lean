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

/-- A function of the round output can be fused into its scalar continuation. -/
theorem roundWith_map {α β : Type} (f : α → β) (k : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → α)
    (rc a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 : UInt64) :
    f (roundWith k rc a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24) =
      roundWith (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 => f (k a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24)) rc a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 := rfl

/-- Unboxed counters execute the same scalar rounds before their counter range ends. -/
theorem permute32First_eq (n r : Nat) (bound : n + r < 4294967296)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 : UInt64) :
    permute32First n.toUInt32 r.toUInt32 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 = (permute n r a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24)[0]! := by
  induction n generalizing r a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 with
  | zero => rw [permute32First]; rfl
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
    rw [permute32First, ite_eq_right hn, hsub, hadd, hr, permute, roundWith_map (fun s : Array UInt64 => s[0]!)]
    have tail : permute32First n.toUInt32 (r + 1).toUInt32 = (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 => (permute n (r + 1) a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24)[0]!) := by
      funext a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
      exact ih (r + 1) (by omega) a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    rw [tail]

/-- A nonce probe returns precisely the first lane of the full overwritten-state permutation. -/
theorem f1600FirstOverwrite_eq (s : Array UInt64) (hs : s.size = 25)
    (lane : Nat) (value : UInt64) :
    f1600FirstOverwrite s lane value = (f1600 (s.set! lane value))[0]! := by
  unfold f1600FirstOverwrite f1600
  have eq : permute32First 24 0 = (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 => (permute 24 0 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24)[0]!) := by
    funext a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    exact permute32First_eq 24 0 (by decide) a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
  rw [eq]
  have get (i : Nat) (hi : i < 25) :
      (s.set! lane value)[i]! = if lane = i then value else s[i]! := by
    by_cases h : lane = i
    · subst lane
      rw [ite_eq_left rfl, Array.getElem!_set!_self _ _ _ (by omega)]
    · rw [ite_eq_right h, Array.getElem!_set!_ne _ _ _ _ h]
  congr 2 <;> symm <;> exact get _ (by decide)

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

namespace Sponge
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem pack8_eq (a b c d e f g h : UInt8) :
  (a.toUInt32 ||| (b.toUInt32 <<< 8) ||| (c.toUInt32 <<< 16) ||| (d.toUInt32 <<< 24)).toUInt64 |||
    ((e.toUInt32 ||| (f.toUInt32 <<< 8) ||| (g.toUInt32 <<< 16) ||| (h.toUInt32 <<< 24)).toUInt64 <<< 32) =
    a.toUInt64 ^^^ (b.toUInt64 <<< 8) ^^^ (c.toUInt64 <<< 16) ^^^ (d.toUInt64 <<< 24) ^^^
    (e.toUInt64 <<< 32) ^^^ (f.toUInt64 <<< 40) ^^^ (g.toUInt64 <<< 48) ^^^ (h.toUInt64 <<< 56) := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_xor, UInt64.toBitVec_shiftLeft,
    UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt32.toBitVec_toUInt64,
    UInt8.toBitVec_toUInt32, UInt8.toBitVec_toUInt64,
    BitVec.shiftLeft_eq', BitVec.getLsbD_or, BitVec.getLsbD_xor,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp (disch := decide) [BitVec.getLsbD_of_ge]
/-- The two native word loads have the reference lane's little-endian order. -/
theorem loadLane_eq (input : ByteArray) (o : USize)
    (h : o.toNat + 8 ≤ input.size) (hu : o.toNat + 8 < USize.size) :
    loadLane input o h hu = readLane input o.toNat := by
  have he : (4 : USize).toNat = 4 := usize_lit 4 (by decide)
  have h4 : (o + 4).toNat = o.toNat + 4 := by
    change (o.toNat + (4 : USize).toNat) % USize.size = o.toNat + 4
    rw [he, Nat.mod_eq_of_lt (by omega)]
  simp only [loadLane, ByteArray.ugetUInt32LE, ByteArray.getUInt32LE!, h4,
    ite_eq_left (show o.toNat + 4 ≤ input.size by omega),
    ite_eq_left (show o.toNat + 4 + 4 ≤ input.size by omega),
    ByteArray.get!_eq_getElem!, readLane, Nat.add_assoc, Nat.add_zero]
  simp only [UInt64.shiftLeft_zero]
  exact pack8_eq ..

theorem get_set32 (s : ByteArray) (o i : Nat) (v : UInt32) (h : o+4 ≤ s.size) :
    (s.setUInt32LE! o v)[i]! =
      if o=i then v.toUInt8 else if o+1=i then (v >>> 8).toUInt8
      else if o+2=i then (v >>> 16).toUInt8 else if o+3=i then (v >>> 24).toUInt8
      else s[i]! := by
  rw [ByteArray.setUInt32LE!, ite_eq_left h]
  rw [ByteArray.getElem!_set! _ _ _ _ (by simp only [ByteArray.size_set!]; omega)]
  rw [ByteArray.getElem!_set! _ _ _ _ (by simp only [ByteArray.size_set!]; omega)]
  rw [ByteArray.getElem!_set! _ _ _ _ (by simp only [ByteArray.size_set!]; omega)]
  rw [ByteArray.getElem!_set! _ _ _ _ (by omega)]
  by_cases h0 : o=i <;> by_cases h1 : o+1=i <;> by_cases h2 : o+2=i <;>
    by_cases h3 : o+3=i <;> simp_all <;> omega


theorem get_set32_all (s : ByteArray) (o i : Nat) (v : UInt32) :
    (s.setUInt32LE! o v)[i]! = if o+4 ≤ s.size then
      (if o=i then v.toUInt8 else if o+1=i then (v >>> 8).toUInt8
      else if o+2=i then (v >>> 16).toUInt8 else if o+3=i then (v >>> 24).toUInt8
      else s[i]!) else s[i]! := by
  by_cases h : o+4 ≤ s.size
  · rw [ite_eq_left h, get_set32 _ _ _ _ h]
  · simp only [ByteArray.setUInt32LE!, ite_eq_right h]

theorem get_mk (a : Array UInt8) (i : Nat) : (ByteArray.mk a)[i]! = a[i]! := by
  by_cases h : i<a.size
  · rw [getElem!_pos (ByteArray.mk a) i h, getElem!_pos a i h]
    exact ByteArray.getElem_eq_getElem_data
  · rw [getElem!_neg (ByteArray.mk a) i h, getElem!_neg a i h]

theorem size_mk (a : Array UInt8) : (ByteArray.mk a).size = a.size := rfl

theorem digest_stores (a b c d : UInt64) : digest a b c d =
    (((((((((ByteArray.mk (Array.replicate 32 0)).setUInt32LE! 0 (a).toUInt32).setUInt32LE! 4 (a >>> 32).toUInt32).setUInt32LE! 8 (b).toUInt32).setUInt32LE! 12 (b >>> 32).toUInt32).setUInt32LE! 16 (c).toUInt32).setUInt32LE! 20 (c >>> 32).toUInt32).setUInt32LE! 24 (d).toUInt32).setUInt32LE! 28 (d >>> 32).toUInt32) := by
  simp only [digest, putDigest, ByteArray.usetUInt32LE,
    usize_lit 0 (by decide), usize_lit 4 (by decide), usize_lit 8 (by decide), usize_lit 12 (by decide), usize_lit 16 (by decide), usize_lit 20 (by decide), usize_lit 24 (by decide), usize_lit 28 (by decide)]

theorem byteArray_ext (s t : ByteArray) (hs : s.size = t.size)
    (h : ∀ i, i < s.size → s[i]! = t[i]!) : s=t := by
  apply ByteArray.ext
  apply Array.ext hs
  intro i hi hj
  have he := h i hi
  simpa only [getElem!_pos s i hi, getElem!_pos t i hj, ByteArray.getElem_eq_getElem_data] using he

/-- Digest stores equal the reference's byte extraction. -/
theorem digest_eq (a b c d : UInt64) :
    digest a b c d = VCVio.Algorithms.Keccak.squeeze #[a,b,c,d] 32 := by
  have hs : (digest a b c d).size = 32 := by simp only [digest, size_putDigest]
  apply byteArray_ext _ _ (hs.trans (VCVio.Algorithms.Keccak.squeeze_size _ _).symm)
  intro i hi
  have h : i < 32 := by omega
  interval_cases i <;>
    simp only [digest_stores, get_set32_all, ByteArray.size_setUInt32LE!, size_mk,
      Array.size_replicate, get_mk, VCVio.Algorithms.Keccak.squeeze] <;>
    simp
  all_goals
    apply UInt8.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [UInt8.toBitVec_and,
      UInt64.toBitVec_toUInt8, UInt32.toBitVec_toUInt8, UInt64.toBitVec_toUInt32,
      UInt64.toBitVec_shiftRight, UInt32.toBitVec_shiftRight,
      BitVec.ushiftRight_eq', BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_setWidth]
    interval_cases j <;> simp (disch := decide)
def padding (p : Nat) : List UInt8 :=
  if p = 1 then [0x81] else 1 :: (List.replicate (p-2) 0 ++ [0x80])

theorem length_padding (p : Nat) (hp : 0 < p) : (padding p).length = p := by
  unfold padding
  split <;> simp_all
  omega

theorem get_padding (p i : Nat) (hp : 0 < p) (hi : i < p) :
    (padding p)[i]! = (if i=0 then (1 : UInt8) else 0) ^^^
      (if i+1=p then 0x80 else 0) := by
  by_cases hp1 : p = 1
  · subst p
    have hi0 : i = 0 := by omega
    subst i
    rfl
  · have hlen : (padding p).length = p := length_padding p hp
    simp only [padding, ite_eq_right hp1]
    rw [getElem!_pos _ _ (by simp only [List.length_cons, List.length_append, List.length_replicate]; omega)]
    by_cases hi0 : i=0
    · subst i
      simp [show 1 ≠ p by omega]
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
      simp only [List.getElem_cons_succ, Nat.succ_ne_zero, ite_false]
      by_cases hj : j < p-2
      · simp [List.getElem_append_left (show j < (List.replicate (p-2) (0 : UInt8)).length by simpa only [List.length_replicate] using hj), List.getElem_replicate,
          show ¬ (j+1+1=p) by omega]
      · have he : j=p-2 := by omega
        simp [he, List.getElem_append_right, show p-2+1+1=p by omega]

def padded (input : ByteArray) : ByteArray :=
  input ++ ByteArray.mk (padding (136-input.size%136)).toArray

theorem size_padded (input : ByteArray) :
    (padded input).size = (input.size/136+1)*136 := by
  have hm := Nat.mod_lt input.size (by decide : 0 < 136)
  have hd := Nat.div_add_mod input.size 136
  unfold padded
  rw [ByteArray.size_append]
  change input.size + (padding (136-input.size%136)).length = _
  rw [length_padding _ (by omega)]
  omega

theorem get_padded (input : ByteArray) (i : Nat) (hi : i < (padded input).size) :
    (padded input)[i]! =
      (if i < input.size then input[i]! else if i = input.size then 1 else 0) ^^^
      (if i+1=(padded input).size then 0x80 else 0) := by
  have hp : 0 < 136-input.size%136 := by have := Nat.mod_lt input.size (by decide : 0<136); omega
  have hs : (padded input).size = input.size + (136-input.size%136) := by
    unfold padded
    rw [ByteArray.size_append]
    change input.size + (padding (136-input.size%136)).length = _
    rw [length_padding _ hp]
  rw [hs] at hi
  rw [hs]
  rw [getElem!_pos (padded input) i (by omega)]
  by_cases h : i < input.size
  · simp only [padded, ByteArray.getElem_append_left h]
    rw [ite_eq_left h, getElem!_pos input i h,
      ite_eq_right (show ¬(i+1=input.size+(136-input.size%136)) by omega), UInt8.xor_zero]
  · simp only [padded, ByteArray.getElem_append_right (show input.size ≤ i by omega)]
    have hj : i-input.size < (padding (136-input.size%136)).length := by rw [length_padding _ hp]; omega
    change (padding (136-input.size%136))[i-input.size]'hj = _
    rw [← getElem!_pos _ _ (by rw [length_padding _ hp]; omega), get_padding _ _ hp (by omega), ite_eq_right h]
    have h0 : (i-input.size=0) ↔ i=input.size := by omega
    have h1 : (i-input.size+1=136-input.size%136) ↔ i+1=input.size+(136-input.size%136) := by omega
    simp only [h0, h1]


def messageByte (input : ByteArray) (i : Nat) : UInt8 :=
  if i < input.size then input[i]! else if i=input.size then 1 else 0

def messageLane (input : ByteArray) (o : Nat) : UInt64 :=
  ((messageByte input (o+0)).toUInt64 <<< 0) ^^^
  ((messageByte input (o+1)).toUInt64 <<< 8) ^^^
  ((messageByte input (o+2)).toUInt64 <<< 16) ^^^
  ((messageByte input (o+3)).toUInt64 <<< 24) ^^^
  ((messageByte input (o+4)).toUInt64 <<< 32) ^^^
  ((messageByte input (o+5)).toUInt64 <<< 40) ^^^
  ((messageByte input (o+6)).toUInt64 <<< 48) ^^^
  ((messageByte input (o+7)).toUInt64 <<< 56)

theorem partialLane_eq (input : ByteArray) (o : Nat) (h0 : o ≤ input.size)
    (h8 : input.size < o+8) :
    partialLane input o (input.size-o) 0 0 = messageLane input o := by
  generalize hn : input.size-o = n
  have hn8 : n < 8 := by omega
  interval_cases n <;>
    simp (disch := omega) [partialLane, messageLane, messageByte, Nat.add_assoc,
      ite_eq_left, ite_eq_right]
  all_goals
    apply UInt64.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [UInt64.toBitVec_xor, UInt64.toBitVec_shiftLeft,
      UInt8.toBitVec_toUInt64, BitVec.shiftLeft_eq', BitVec.getLsbD_xor,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    interval_cases j <;> simp (disch := decide) [BitVec.getLsbD_of_ge]

theorem lastLane_eq (input : ByteArray) (o : Nat) (hu : input.size < USize.size) :
    lastLane input o hu = messageLane input o := by
  unfold lastLane
  split
  · next h =>
    rw [loadLane_eq, USize.toNat_ofNat_of_lt' (by omega)]
    simp (disch := omega) [readLane, messageLane, messageByte, ite_eq_left]
  · split
    · next h h0 => exact partialLane_eq input o h0 (by omega)
    · next h h0 =>
      simp (disch := omega) [messageLane, messageByte, ite_eq_right]
      rfl


theorem get_padded_prefix (input : ByteArray) (i : Nat) (hi : i < input.size) :
    (padded input)[i]! = input[i]! := by
  have hp : i < (padded input).size := by rw [size_padded]; omega
  rw [getElem!_pos (padded input) i hp, getElem!_pos input i hi]
  exact ByteArray.getElem_append_left hi

theorem readLane_prefix (input : ByteArray) (o : Nat) (ho : o+8 ≤ input.size) :
    readLane (padded input) o = readLane input o := by
  simp (disch := omega) only [readLane, get_padded_prefix]

theorem readLane_final (input : ByteArray) (offset i : Nat) (hi : i ≤ 16)
    (hf : (padded input).size = offset+136) :
    readLane (padded input) (offset+i*8) = messageLane input (offset+i*8) ^^^
      (if i=16 then 0x8000000000000000 else 0) := by
  have get (j : Nat) (hj : j < 136) :
      (padded input)[offset+j]! = messageByte input (offset+j) ^^^
        (if j=135 then 0x80 else 0) := by
    rw [get_padded input (offset+j) (by omega)]
    change messageByte input (offset+j) ^^^ _ = _
    congr 1
    have he : (offset+j+1=(padded input).size) ↔ j=135 := by omega
    simp only [he]
  have hz : (0 : UInt8).toUInt64 = 0 := rfl
  have hh : (128 : UInt8).toUInt64 <<< 56 = 0x8000000000000000 := by decide
  by_cases h16 : i=16
  · subst i
    simp (disch := omega) only [readLane, messageLane, Nat.add_assoc,
      get, ite_eq_right, ite_true, UInt8.toUInt64_xor, UInt64.shiftLeft_xor,
      hz, hh, UInt64.xor_zero, UInt64.xor_assoc]
  · simp (disch := omega) only [readLane, messageLane, Nat.add_assoc,
      get, ite_eq_right, UInt8.toUInt64_xor,
      hz, UInt64.xor_zero]


theorem absorbBlock_args {α : Type} (k : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → α)
    (input : ByteArray) (offset : Nat) (s : Array UInt64) (hs : s.size = 25) :
    k (s[0]! ^^^ readLane input (offset+0*8)) (s[1]! ^^^ readLane input (offset+1*8)) (s[2]! ^^^ readLane input (offset+2*8)) (s[3]! ^^^ readLane input (offset+3*8)) (s[4]! ^^^ readLane input (offset+4*8)) (s[5]! ^^^ readLane input (offset+5*8)) (s[6]! ^^^ readLane input (offset+6*8)) (s[7]! ^^^ readLane input (offset+7*8)) (s[8]! ^^^ readLane input (offset+8*8)) (s[9]! ^^^ readLane input (offset+9*8)) (s[10]! ^^^ readLane input (offset+10*8)) (s[11]! ^^^ readLane input (offset+11*8)) (s[12]! ^^^ readLane input (offset+12*8)) (s[13]! ^^^ readLane input (offset+13*8)) (s[14]! ^^^ readLane input (offset+14*8)) (s[15]! ^^^ readLane input (offset+15*8)) (s[16]! ^^^ readLane input (offset+16*8)) s[17]! s[18]! s[19]! s[20]! s[21]! s[22]! s[23]! s[24]! =
      let t := absorbBlock input offset s
      k t[0]! t[1]! t[2]! t[3]! t[4]! t[5]! t[6]! t[7]! t[8]! t[9]! t[10]! t[11]! t[12]! t[13]! t[14]! t[15]! t[16]! t[17]! t[18]! t[19]! t[20]! t[21]! t[22]! t[23]! t[24]! := by
  simp [absorbBlock, List.range'_succ, xorAt, hs]

theorem absorbWith_eq {α : Type} (k : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → α)
    (input : ByteArray) (hu : input.size < USize.size) (b : Nat)
    (hb : b ≤ input.size/136) (s : Array UInt64) (hs : s.size=25) :
    absorbWith input hu (b*136) k s[0]! s[1]! s[2]! s[3]! s[4]! s[5]! s[6]! s[7]! s[8]! s[9]! s[10]! s[11]! s[12]! s[13]! s[14]! s[15]! s[16]! s[17]! s[18]! s[19]! s[20]! s[21]! s[22]! s[23]! s[24]! =
      let t := absorbBlock (padded input) (b*136) s
      k t[0]! t[1]! t[2]! t[3]! t[4]! t[5]! t[6]! t[7]! t[8]! t[9]! t[10]! t[11]! t[12]! t[13]! t[14]! t[15]! t[16]! t[17]! t[18]! t[19]! t[20]! t[21]! t[22]! t[23]! t[24]! := by
  rw [← absorbBlock_args k _ _ _ hs]
  unfold absorbWith
  split
  · next h =>
    simp (disch := omega) only [loadLane_eq, USize.toNat_ofNat_of_lt', readLane_prefix]
  · next h =>
    have hf : (padded input).size = b*136+136 := by rw [size_padded]; omega
    have l0 := readLane_final input (b*136) 0 (by decide) hf
    have l1 := readLane_final input (b*136) 1 (by decide) hf
    have l2 := readLane_final input (b*136) 2 (by decide) hf
    have l3 := readLane_final input (b*136) 3 (by decide) hf
    have l4 := readLane_final input (b*136) 4 (by decide) hf
    have l5 := readLane_final input (b*136) 5 (by decide) hf
    have l6 := readLane_final input (b*136) 6 (by decide) hf
    have l7 := readLane_final input (b*136) 7 (by decide) hf
    have l8 := readLane_final input (b*136) 8 (by decide) hf
    have l9 := readLane_final input (b*136) 9 (by decide) hf
    have l10 := readLane_final input (b*136) 10 (by decide) hf
    have l11 := readLane_final input (b*136) 11 (by decide) hf
    have l12 := readLane_final input (b*136) 12 (by decide) hf
    have l13 := readLane_final input (b*136) 13 (by decide) hf
    have l14 := readLane_final input (b*136) 14 (by decide) hf
    have l15 := readLane_final input (b*136) 15 (by decide) hf
    have l16 := readLane_final input (b*136) 16 (by decide) hf
    simp only [lastLane_eq, l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, ↓reduceIte, Nat.reduceEqDiff,
      UInt64.xor_zero, UInt64.xor_assoc]

set_option maxHeartbeats 2000000 in
theorem run_rounds_eq (input : ByteArray) (hu : input.size < USize.size)
    (blocks offset rounds : Nat) (hr : rounds ≤ 24) (s : Array UInt64) :
    run input hu (blocks+rounds) rounds offset s[0]! s[1]! s[2]! s[3]! s[4]! s[5]! s[6]! s[7]! s[8]! s[9]! s[10]! s[11]! s[12]! s[13]! s[14]! s[15]! s[16]! s[17]! s[18]! s[19]! s[20]! s[21]! s[22]! s[23]! s[24]! =
      let t := (List.range' (24-rounds) rounds).foldl
        (fun t j ↦ VCVio.Algorithms.Keccak.round t VCVio.Algorithms.Keccak.roundConstants[j]!) s
      run input hu blocks 0 offset t[0]! t[1]! t[2]! t[3]! t[4]! t[5]! t[6]! t[7]! t[8]! t[9]! t[10]! t[11]! t[12]! t[13]! t[14]! t[15]! t[16]! t[17]! t[18]! t[19]! t[20]! t[21]! t[22]! t[23]! t[24]! := by
  induction rounds generalizing s with
  | zero => rfl
  | succ n ih =>
    have he : blocks+(n+1)=(blocks+n)+1 := by omega
    rw [he, run.eq_3, roundWith_eq, ih (by omega)]
    have hrc : 24-(n+1)=23-n := by omega
    have hn : 24-n=23-n+1 := by omega
    simp only [List.range'_succ, List.foldl_cons, hrc, hn]


theorem digest_state_eq (s : Array UInt64) :
    digest s[0]! s[1]! s[2]! s[3]! = VCVio.Algorithms.Keccak.squeeze s 32 := by
  rw [digest_eq]
  apply byteArray_ext _ _ (by simp only [VCVio.Algorithms.Keccak.squeeze_size])
  intro i hi
  have hi32 : i < 32 := by simpa only [VCVio.Algorithms.Keccak.squeeze_size] using hi
  interval_cases i <;> simp only [VCVio.Algorithms.Keccak.squeeze, get_mk] <;> simp

@[simp] theorem size_absorbBlock (input : ByteArray) (offset : Nat) (s : Array UInt64) :
    (absorbBlock input offset s).size = s.size := by
  simp [absorbBlock, List.range'_succ, xorAt]

@[simp] theorem size_f1600 (s : Array UInt64) :
    (VCVio.Algorithms.Keccak.f1600 s).size = 25 := by
  unfold VCVio.Algorithms.Keccak.f1600
  rw [show List.range 24 = List.range 23 ++ [23] by decide, List.foldl_append]
  exact size_round _ _

theorem run_24_eq (input : ByteArray) (hu : input.size < USize.size)
    (steps offset : Nat) (s : Array UInt64) :
    run input hu (steps+24) 24 offset s[0]! s[1]! s[2]! s[3]! s[4]! s[5]! s[6]! s[7]! s[8]! s[9]! s[10]! s[11]! s[12]! s[13]! s[14]! s[15]! s[16]! s[17]! s[18]! s[19]! s[20]! s[21]! s[22]! s[23]! s[24]! =
      let t := VCVio.Algorithms.Keccak.f1600 s
      run input hu steps 0 offset t[0]! t[1]! t[2]! t[3]! t[4]! t[5]! t[6]! t[7]! t[8]! t[9]! t[10]! t[11]! t[12]! t[13]! t[14]! t[15]! t[16]! t[17]! t[18]! t[19]! t[20]! t[21]! t[22]! t[23]! t[24]! := by
  simpa only [Nat.sub_self, ← List.range_eq_range', VCVio.Algorithms.Keccak.f1600] using
    run_rounds_eq input hu steps offset 24 (by decide) s

theorem run_blocks_eq (input : ByteArray) (hu : input.size < USize.size)
    (blocks b : Nat) (hremain : blocks+b=input.size/136+1)
    (s : Array UInt64) (hs : s.size=25) :
    run input hu (blocks*25) 0 (b*136) s[0]! s[1]! s[2]! s[3]! s[4]! s[5]! s[6]! s[7]! s[8]! s[9]! s[10]! s[11]! s[12]! s[13]! s[14]! s[15]! s[16]! s[17]! s[18]! s[19]! s[20]! s[21]! s[22]! s[23]! s[24]! =
      VCVio.Algorithms.Keccak.squeeze
        ((List.range' b blocks).foldl (fun t j ↦
          VCVio.Algorithms.Keccak.f1600 (absorbBlock (padded input) (j*136) t)) s) 32 := by
  induction blocks generalizing b s with
  | zero => rw [Nat.zero_mul, run.eq_1, digest_state_eq]; rfl
  | succ n ih =>
    have he : (n+1)*25=(n*25+24)+1 := by omega
    rw [he, run.eq_2, absorbWith_eq _ _ _ b (by omega) s hs, run_24_eq]
    have hb : b*136+136=(b+1)*136 := by omega
    rw [hb, ih (b+1) (by omega) _ (size_f1600 _)]
    rfl


theorem absorb_fold (input : ByteArray) :
    absorb input =
      (List.range' 0 (input.size/136+1)).foldl (fun t j ↦
        VCVio.Algorithms.Keccak.f1600 (absorbBlock (padded input) (j*136) t))
        (Array.replicate 25 0) := by
  simp only [absorb, Std.Legacy.Range.forIn_eq_forIn_range']
  rw [List.forIn_pure_yield_eq_foldl (m := Id)]
  simp only [Id.run, bind, pure, f1600_eq, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  change (List.range' 0 ((padded input).size/136)).foldl _ _ = _
  rw [size_padded, Nat.mul_div_cancel _ (by decide : 0<136)]
  rfl

theorem keccak256_eq (input : ByteArray) (hu : input.size < USize.size) :
    keccak256 input hu = VCVio.Algorithms.Keccak.keccak256 input := by
  have hrun := run_blocks_eq input hu (input.size/136+1) 0 (by omega)
    (Array.replicate 25 0) (Array.size_replicate ..)
  have he : keccak256 input hu = VCVio.Algorithms.Keccak.squeeze
      ((List.range' 0 (input.size/136+1)).foldl (fun t j ↦
        VCVio.Algorithms.Keccak.f1600 (absorbBlock (padded input) (j*136) t))
        (Array.replicate 25 0)) 32 := by
    simpa [keccak256] using hrun
  rw [he, ← absorb_fold, CompStark.Keccak.absorb_eq]
  rfl


end Sponge

/-- Exact equality of all digest bytes with VCVio's original Keccak-256. -/
@[simp] theorem keccak256_eq (input : ByteArray) (hu : input.size < USize.size) :
    keccak256 input hu = VCVio.Algorithms.Keccak.keccak256 input := by
  exact Sponge.keccak256_eq input hu

/-- Independent permutation batches preserve input order and every output lane. -/
@[simp] theorem f1600Batch_eq (states : Array (Array UInt64)) :
    f1600Batch states = states.map VCVio.Algorithms.Keccak.f1600 := by
  exact congrArg (fun f : Array UInt64 → Array UInt64 ↦ states.map f) (funext f1600_eq)

/-- Independent hash batches preserve input order and every digest byte. -/
@[simp] theorem keccak256Batch_eq (inputs : Array ByteArray)
    (hu : ∀ input ∈ inputs, input.size < USize.size) :
    keccak256Batch inputs hu = inputs.map VCVio.Algorithms.Keccak.keccak256 := by
  simp only [keccak256Batch, keccak256_eq, Array.pmap_eq_map]

/-- Node hashing is the reference hash of the left and right child bytes. -/
@[simp] theorem hashNode_eq (left right : ByteArray) (hl : left.size = 32)
    (hr : right.size = 32) :
    hashNode left right hl hr = VCVio.Algorithms.Keccak.keccak256 (left ++ right) := by
  exact keccak256_eq _ _

/-- Leaf hashing is the reference hash of the complete 512-byte payload. -/
@[simp] theorem hashLeaf_eq (payload : ByteArray) (h : payload.size = 512) :
    hashLeaf payload h = VCVio.Algorithms.Keccak.keccak256 payload := by
  exact keccak256_eq _ _

/-- Keccak-256 always returns a 32-byte digest. -/
@[simp] theorem size_keccak256 (input : ByteArray) (hu : input.size < USize.size) :
    (keccak256 input hu).size = 32 := by
  rw [keccak256_eq]
  exact VCVio.Algorithms.Keccak.squeeze_size _ _

end CompStark.Keccak
