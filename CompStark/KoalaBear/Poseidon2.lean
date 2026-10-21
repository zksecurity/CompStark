/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.KoalaBear.Field
public import CompStark.Poseidon2.Impl
public import CompStark.Poseidon2.PackedCorrectness
public import CompStark.Poseidon2.PackedCorrectness24

/-! # Poseidon2 over KoalaBear

Plonky3's default KoalaBear instances (`Poseidon2.KoalaBear.width16`, `width24`) with the packed
kernels as their implementations: the permutation of one state runs in lane 0 of a packed group of
eight (`perm16`, `perm24`), and is the specification by the packed kernels' correctness
(`perm16_eq`, `perm24_eq`).
-/

@[expose] public section
namespace CompStark.KoalaBear
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTTFast.Packed (size_encode_fields ofWord ofWord_val)
open CompPoly.CPolynomial.NTTFast.Packed.Native (encodeFields encodeFields_eq read read_encode)
open CompStark.Poseidon2.Packed

local notation "F" => _root_.KoalaBear.Fast.Field

/-- The packed constants of the width-16 permutation. -/
def K16 : Packed16 := Packed16.ofParams (Poseidon2.KoalaBear.width16 F)

/-- The packed constants of the width-24 permutation. -/
def K24 : Packed24 := Packed24.ofParams (Poseidon2.KoalaBear.width24 F)

/-- The `8 t` words of a packed group of width `t` with `s` in lane 0 and zeros elsewhere. -/
def lane0 {t : Nat} (s : Vector F t) : Array F :=
  Array.ofFn (n := 8 * t) fun k ↦ if k.val % 8 = 0 then s.toArray.getD (k / 8) 0 else 0

/-- The width-16 permutation of one state, in lane 0 of a packed group. -/
def perm16 (s : Vector F 16) : Vector F 16 :=
  let out := permute16 K16 (encodeFields (lane0 s)) 0
  Vector.ofFn fun j ↦ ofWord (read out (8 * j.val))

/-- The width-24 permutation of one state, in lane 0 of a packed group. -/
def perm24 (s : Vector F 24) : Vector F 24 :=
  let out := permute24 K24 (encodeFields (lane0 s)) 0
  Vector.ofFn fun j ↦ ofWord (read out (8 * j.val))

theorem size_lane0 {t : Nat} (s : Vector F t) : (lane0 s).size = 8 * t := Array.size_ofFn

/-- Lane 0 of the group of `lane0 s` is `s`. -/
theorem lane_lane0 {t : Nat} (s : Vector F t) : lane t (lane0 s) 0 0 = s := by
  apply Vector.ext
  intro k hk
  simp only [lane, lane0, Vector.getElem_ofFn, Poseidon2.Packed.word, Nat.zero_add, Nat.add_zero,
    Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  rw [dite_eq_left_of_eq_true (eq_true (by omega))]
  simp only [Option.getD_some, Nat.mul_mod_right, ite_true, Nat.mul_div_cancel_left _
    (show 0 < 8 by decide), Vector.getElem_toArray, Array.getElem?_eq_getElem
    (show k < s.toArray.size by simp only [Vector.size_toArray]; exact hk)]

/-- Reading word `8 j` of an encoded group gives coordinate `j` of lane 0. -/
theorem read_lane {t : Nat} (ht : t ≤ 24) (W : Array F) (hW : W.size = 8 * t) (j : Nat)
    (hj : j < t) : ofWord (read (encode W) (8 * j)) = (lane t W 0 0)[j] := by
  have hs : (encode W).size < USize.size := by
    rw [size_encode_fields, hW]
    have := USize.le_size
    omega
  rw [read_encode W _ hs (by omega), ofWord_val]
  simp only [lane, Vector.getElem_ofFn, Poseidon2.Packed.word, Nat.zero_add, Nat.add_zero]

theorem perm16_eq (s : Vector F 16) :
    perm16 s = Poseidon2.permute (Poseidon2.KoalaBear.width16 F) s := by
  obtain ⟨W', e, hsz, hl, -⟩ := permute16_spec (Poseidon2.KoalaBear.width16 F) rfl rfl rfl rfl
    (lane0 s) 0 (by
      simp only [GroupFits, Fits, size_encode_fields, size_lane0, USize.toNat_zero]
      have := USize.le_size
      omega)
  have h0 := hl 0 (by decide)
  rw [USize.toNat_zero, lane_lane0] at h0
  rw [perm16, K16, encodeFields_eq, e]
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_ofFn, read_lane (by decide) W' (by rw [hsz, size_lane0]) j hj, h0]

theorem perm24_eq (s : Vector F 24) :
    perm24 s = Poseidon2.permute (Poseidon2.KoalaBear.width24 F) s := by
  obtain ⟨W', e, hsz, hl, -⟩ := permute24_spec (Poseidon2.KoalaBear.width24 F) rfl rfl rfl rfl
    (lane0 s) 0 (by
      simp only [GroupFits24, Fits, size_encode_fields, size_lane0, USize.toNat_zero]
      have := USize.le_size
      omega)
  have h0 := hl 0 (by decide)
  rw [USize.toNat_zero, lane_lane0] at h0
  rw [perm24, K24, encodeFields_eq, e]
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_ofFn, read_lane (by decide) W' (by rw [hsz, size_lane0]) j hj, h0]

/-- Plonky3's default KoalaBear Poseidon2 instances on the packed kernels. -/
instance instPoseidon2Field : Poseidon2Field F where
  params16 := Poseidon2.KoalaBear.width16 F
  params24 := Poseidon2.KoalaBear.width24 F
  perm16 := ⟨perm16, perm16_eq⟩
  perm24 := ⟨perm24, perm24_eq⟩

theorem params16_eq :
    (Poseidon2Field.params16 : Poseidon2.Params F 16) = Poseidon2.KoalaBear.width16 F := rfl

theorem params24_eq :
    (Poseidon2Field.params24 : Poseidon2.Params F 24) = Poseidon2.KoalaBear.width24 F := rfl

end CompStark.KoalaBear
