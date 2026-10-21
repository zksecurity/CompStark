/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.KoalaBear.Field
public import CompStark.Poseidon2.PackedField
public import CompStark.Poseidon2.PackedCorrectness
public import CompStark.Poseidon2.PackedCorrectness24

/-! # Poseidon2 over KoalaBear

Plonky3's default KoalaBear instances (`Poseidon2.KoalaBear.width16`, `width24`) with the packed
kernels as their implementations: the permutation of one state runs in lane 0 of a packed group of
eight (`perm16`, `perm24`), and is the specification by the packed kernels' correctness
(`perm16_eq`, `perm24_eq`). On whole groups of eight states the kernels are KoalaBear's
`PackedPoseidon2` instance, the fast prover's (`instPackedPoseidon2`).
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
  Vector.ofFn fun j ↦ ofWord _ (read out (8 * j.val))

/-- The width-24 permutation of one state, in lane 0 of a packed group. -/
def perm24 (s : Vector F 24) : Vector F 24 :=
  let out := permute24 K24 (encodeFields (lane0 s)) 0
  Vector.ofFn fun j ↦ ofWord _ (read out (8 * j.val))

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
    (hj : j < t) : ofWord _ (read (encode W) (8 * j)) = (lane t W 0 0)[j] := by
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

/-- A group whose states are `lane t W' 0 l = f (lane t W 0 l)` is the image of `W`. -/
theorem eq_map {t : Nat} (f : Vector F t → Vector F t) (W W' : Array F) (hs : W'.size = 8 * t)
    (hl : ∀ l < 8, lane t W' 0 l = f (lane t W 0 l)) : W' = Poseidon2.Group.map t f W := by
  apply Array.ext (by rw [hs, Poseidon2.Group.size_map])
  intro k h1 _
  have hk8 : k % 8 < 8 := Nat.mod_lt _ (by decide)
  have hj : k / 8 < t := by omega
  have e := congrArg (·[k / 8]'hj) (hl (k % 8) hk8)
  simp only [lane, Vector.getElem_ofFn, word, Nat.zero_add,
    Nat.div_add_mod k 8] at e
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1, Option.getD_some] at e
  rw [e]
  simp only [Poseidon2.Group.map, Array.getElem_ofFn]
  congr 2

theorem permute16_group (W : Array F) (hW : W.size = 8 * 16) :
    permute16 K16 (encode W) 0 =
      encode (Poseidon2.Group.map 16 (Poseidon2.permute (Poseidon2.KoalaBear.width16 F)) W) := by
  obtain ⟨W', e, hs, hl, -⟩ := permute16_spec (Poseidon2.KoalaBear.width16 F) rfl rfl rfl rfl W 0
    (by
      simp only [GroupFits, Fits, size_encode_fields, hW, USize.toNat_zero]
      have := USize.le_size
      omega)
  rw [K16, e, eq_map _ W W' (by rw [hs, hW]) hl]

theorem permute24_group (W : Array F) (hW : W.size = 8 * 24) :
    permute24 K24 (encode W) 0 =
      encode (Poseidon2.Group.map 24 (Poseidon2.permute (Poseidon2.KoalaBear.width24 F)) W) := by
  obtain ⟨W', e, hs, hl, -⟩ := permute24_spec (Poseidon2.KoalaBear.width24 F) rfl rfl rfl rfl W 0
    (by
      simp only [GroupFits24, Fits, size_encode_fields, hW, USize.toNat_zero]
      have := USize.le_size
      omega)
  rw [K24, e, eq_map _ W W' (by rw [hs, hW]) hl]

/-- KoalaBear's vectorized Poseidon2 kernels on groups of eight states. -/
instance instPackedPoseidon2 : Poseidon2.PackedPoseidon2 _root_.KoalaBear.fieldSize where
  permute16 b := permute16 K16 b 0
  permute24 b := permute24 K24 b 0
  permute16_encode := permute16_group
  permute24_encode := permute24_group

end CompStark.KoalaBear
