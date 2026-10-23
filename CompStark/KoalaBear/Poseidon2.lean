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

Poseidon2 instances of Plonky3's KoalaBear shape (`Instances`: the S-box `x ^ 3`, four initial
and four terminal full rounds and KoalaBear's internal diagonals, with any round constants) with
the packed kernels as their implementations: the permutation of one state runs in lane 0 of a
packed group of eight (`perm16`, `perm24`), and is the specification by the packed kernels'
correctness (`perm16_eq`, `perm24_eq`). On whole groups of eight states the kernels are a
`PackedPoseidon2` instance, the fast prover's (`Instances.packed`). The constants are a parameter
of the setup: `Instances.field` and `Instances.packed` give the instances to the verifier and the
provers. Plonky3's default constants (`Poseidon2.KoalaBear.width16`, `width24`) are the global
instances (`instPoseidon2Field`, `instPackedPoseidon2`).
-/

@[expose] public section
namespace CompStark.KoalaBear
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTTFast.Packed (size_encode_fields ofWord ofWord_val)
open CompPoly.CPolynomial.NTTFast.Packed.Native (encodeFields encodeFields_eq read read_encode)
open CompStark.Poseidon2.Packed

local notation "F" => _root_.KoalaBear.Fast.Field

/-- Poseidon2 instances of widths 16 and 24 over KoalaBear in Plonky3's KoalaBear shape, with
their packed constants. -/
structure Instances where
  params16 : Poseidon2.Params F 16
  params24 : Poseidon2.Params F 24
  /-- The packed constants of the width-16 permutation. -/
  K16 : Packed16
  /-- The packed constants of the width-24 permutation. -/
  K24 : Packed24
  K16_eq : K16 = Packed16.ofParams params16
  K24_eq : K24 = Packed24.ofParams params24
  degree16 : params16.degree = 3
  diagonal16 : params16.diagonal = Poseidon2.KoalaBear.diagonal16 F
  initial16 : params16.initial.length = 4
  terminal16 : params16.terminal.length = 4
  degree24 : params24.degree = 3
  diagonal24 : params24.diagonal = Poseidon2.KoalaBear.diagonal24 F
  initial24 : params24.initial.length = 4
  terminal24 : params24.terminal.length = 4

/-- The instances of the given round constants, as canonical values. -/
def Instances.ofNat (initial16 : List (Vector Nat 16)) (internal16 : List Nat)
    (terminal16 : List (Vector Nat 16)) (initial24 : List (Vector Nat 24)) (internal24 : List Nat)
    (terminal24 : List (Vector Nat 24)) (h16 : initial16.length = 4 ∧ terminal16.length = 4)
    (h24 : initial24.length = 4 ∧ terminal24.length = 4) : Instances :=
  let P16 := Poseidon2.Params.ofNat 3 initial16 internal16 terminal16
    (Poseidon2.KoalaBear.diagonal16 F)
  let P24 := Poseidon2.Params.ofNat 3 initial24 internal24 terminal24
    (Poseidon2.KoalaBear.diagonal24 F)
  { params16 := P16, params24 := P24, K16 := Packed16.ofParams P16, K24 := Packed24.ofParams P24
    K16_eq := rfl, K24_eq := rfl, degree16 := rfl, diagonal16 := rfl
    initial16 := by simp only [P16, Poseidon2.Params.ofNat, List.length_map, h16.1]
    terminal16 := by simp only [P16, Poseidon2.Params.ofNat, List.length_map, h16.2]
    degree24 := rfl, diagonal24 := rfl
    initial24 := by simp only [P24, Poseidon2.Params.ofNat, List.length_map, h24.1]
    terminal24 := by simp only [P24, Poseidon2.Params.ofNat, List.length_map, h24.2] }

/-- Plonky3's default instances. -/
def defaultInstances : Instances where
  params16 := Poseidon2.KoalaBear.width16 F
  params24 := Poseidon2.KoalaBear.width24 F
  K16 := Packed16.ofParams (Poseidon2.KoalaBear.width16 F)
  K24 := Packed24.ofParams (Poseidon2.KoalaBear.width24 F)
  K16_eq := rfl
  K24_eq := rfl
  degree16 := rfl
  diagonal16 := rfl
  initial16 := rfl
  terminal16 := rfl
  degree24 := rfl
  diagonal24 := rfl
  initial24 := rfl
  terminal24 := rfl

/-- The `8 t` words of a packed group of width `t` with `s` in lane 0 and zeros elsewhere. -/
def lane0 {t : Nat} (s : Vector F t) : Array F :=
  Array.ofFn (n := 8 * t) fun k ↦ if k.val % 8 = 0 then s.toArray.getD (k / 8) 0 else 0

/-- The packed group of `lane0 s`, written word by word into a zero group. -/
def lane0Words {t : Nat} (s : Vector F t) : ByteArray :=
  (List.range t).foldl (fun b j ↦ CompPoly.CPolynomial.NTTFast.Packed.Native.write b (8 * j)
    (s.toArray.getD j 0).val) (CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords (8 * t))

namespace Instances

variable (I : Instances)

/-- The width-16 permutation of one state, in lane 0 of a packed group. -/
def perm16 (s : Vector F 16) : Vector F 16 :=
  let out := permute16 I.K16 (lane0Words s) 0
  Vector.ofFn fun j ↦ ofWord _ (read out (8 * j.val))

/-- The width-24 permutation of one state, in lane 0 of a packed group. -/
def perm24 (s : Vector F 24) : Vector F 24 :=
  let out := permute24 I.K24 (lane0Words s) 0
  Vector.ofFn fun j ↦ ofWord _ (read out (8 * j.val))

end Instances

theorem size_lane0 {t : Nat} (s : Vector F t) : (lane0 s).size = 8 * t := Array.size_ofFn

/-- `lane0Words` is the encoded group of `lane0`. -/
theorem lane0Words_eq {t : Nat} (s : Vector F t) (ht : 4 * (8 * t) < USize.size) :
    lane0Words s = encode (lane0 s) := by
  have key : ∀ J ≤ t, (List.range J).foldl (fun b j ↦
      CompPoly.CPolynomial.NTTFast.Packed.Native.write b (8 * j) (s.toArray.getD j 0).val)
      (CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords (8 * t)) =
      encode (Array.ofFn (n := 8 * t) fun k ↦
        if k.val % 8 = 0 ∧ k.val / 8 < J then s.toArray.getD (k.val / 8) 0 else 0) := by
    intro J
    induction J with
    | zero =>
      intro _
      rw [List.range_zero, List.foldl_nil, CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords_eq,
        CompPoly.CPolynomial.NTTFast.Packed.encode_eq_map_val]
      refine congrArg _ (Array.ext (by rw [Array.size_map, Array.size_replicate, Array.size_ofFn])
        fun k _ _ ↦ ?_)
      rw [Array.getElem_map, Array.getElem_replicate, Array.getElem_ofFn,
        ite_eq_right (by omega)]
      rfl
    | succ J ih =>
      intro hJ
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
        CompPoly.CPolynomial.NTTFast.Packed.Native.write_encode _ _
          (by rw [size_encode_fields, Array.size_ofFn]; exact ht)
          (by rw [Array.size_ofFn]; omega)]
      refine congrArg _ (Array.ext (by rw [Array.size_setIfInBounds, Array.size_ofFn,
        Array.size_ofFn]) fun k h1 h2 ↦ ?_)
      rw [Array.getElem_setIfInBounds, Array.getElem_ofFn, Array.getElem_ofFn]
      dsimp only
      by_cases hk : 8 * J = k
      · rw [ite_eq_left hk, ite_eq_left (by omega), show k / 8 = J by omega]
      · rw [ite_eq_right hk]
        by_cases hk' : k % 8 = 0 ∧ k / 8 < J
        · rw [ite_eq_left hk', ite_eq_left (by omega)]
        · rw [ite_eq_right hk', ite_eq_right (by omega)]
      rw [Array.size_ofFn] at h2 ⊢
      exact h2
  rw [lane0Words, key t (Nat.le_refl _), lane0]
  refine congrArg _ (Array.ext (by rw [Array.size_ofFn, Array.size_ofFn]) fun k _ _ ↦ ?_)
  rw [Array.getElem_ofFn, Array.getElem_ofFn]
  dsimp only
  by_cases hk : k % 8 = 0
  · rw [ite_eq_left ⟨hk, by rw [Array.size_ofFn] at *; omega⟩, ite_eq_left hk]
  · rw [ite_eq_right (by omega), ite_eq_right hk]

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

namespace Instances

variable (I : Instances)

theorem perm16_eq (s : Vector F 16) : I.perm16 s = Poseidon2.permute I.params16 s := by
  obtain ⟨W', e, hsz, hl, -⟩ := permute16_spec I.params16 I.degree16 I.diagonal16 I.initial16
    I.terminal16 (lane0 s) 0 (by
      simp only [GroupFits, Fits, size_encode_fields, size_lane0, USize.toNat_zero]
      have := USize.le_size
      omega)
  have h0 := hl 0 (by decide)
  rw [USize.toNat_zero, lane_lane0] at h0
  rw [perm16, lane0Words_eq s (by have := USize.le_size; omega), I.K16_eq, e]
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_ofFn, read_lane (by decide) W' (by rw [hsz, size_lane0]) j hj, h0]

theorem perm24_eq (s : Vector F 24) : I.perm24 s = Poseidon2.permute I.params24 s := by
  obtain ⟨W', e, hsz, hl, -⟩ := permute24_spec I.params24 I.degree24 I.diagonal24 I.initial24
    I.terminal24 (lane0 s) 0 (by
      simp only [GroupFits24, Fits, size_encode_fields, size_lane0, USize.toNat_zero]
      have := USize.le_size
      omega)
  have h0 := hl 0 (by decide)
  rw [USize.toNat_zero, lane_lane0] at h0
  rw [perm24, lane0Words_eq s (by have := USize.le_size; omega), I.K24_eq, e]
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_ofFn, read_lane (by decide) W' (by rw [hsz, size_lane0]) j hj, h0]

/-- The instances on the packed kernels. -/
@[instance_reducible] def field : Poseidon2Field F where
  params16 := I.params16
  params24 := I.params24
  perm16 := ⟨I.perm16, I.perm16_eq⟩
  perm24 := ⟨I.perm24, I.perm24_eq⟩

end Instances

/-- Plonky3's default KoalaBear Poseidon2 instances on the packed kernels. -/
instance instPoseidon2Field : Poseidon2Field F := defaultInstances.field

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

namespace Instances

variable (I : Instances)

theorem permute16_group (W : Array F) (hW : W.size = 8 * 16) :
    permute16 I.K16 (encode W) 0 =
      encode (Poseidon2.Group.map 16 (Poseidon2.permute I.params16) W) := by
  obtain ⟨W', e, hs, hl, -⟩ := permute16_spec I.params16 I.degree16 I.diagonal16 I.initial16
    I.terminal16 W 0 (by
      simp only [GroupFits, Fits, size_encode_fields, hW, USize.toNat_zero]
      have := USize.le_size
      omega)
  rw [I.K16_eq, e, eq_map _ W W' (by rw [hs, hW]) hl]

theorem permute24_group (W : Array F) (hW : W.size = 8 * 24) :
    permute24 I.K24 (encode W) 0 =
      encode (Poseidon2.Group.map 24 (Poseidon2.permute I.params24) W) := by
  obtain ⟨W', e, hs, hl, -⟩ := permute24_spec I.params24 I.degree24 I.diagonal24 I.initial24
    I.terminal24 W 0 (by
      simp only [GroupFits24, Fits, size_encode_fields, hW, USize.toNat_zero]
      have := USize.le_size
      omega)
  rw [I.K24_eq, e, eq_map _ W W' (by rw [hs, hW]) hl]

/-- The vectorized Poseidon2 kernels of the instances on groups of eight states. -/
@[instance_reducible] def packed :
    @Poseidon2.PackedPoseidon2 _root_.KoalaBear.fieldSize _ I.field :=
  letI := I.field
  { permute16 b := permute16 I.K16 b 0
    permute24 b := permute24 I.K24 b 0
    permute16_encode := I.permute16_group
    permute24_encode := I.permute24_group }

end Instances

/-- KoalaBear's vectorized Poseidon2 kernels on groups of eight states, with Plonky3's default
constants. -/
instance instPackedPoseidon2 : Poseidon2.PackedPoseidon2 _root_.KoalaBear.fieldSize :=
  defaultInstances.packed

end CompStark.KoalaBear
