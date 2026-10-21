/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Poseidon2.Impl
public import CompPoly.Fields.Montgomery.Native32Bytes

/-! # Packed Poseidon2 over a Montgomery field

A group of eight states of width `t` holds coordinate `j` of state `l` at word `8 j + l`
(`Group.lane`). `PackedPoseidon2 p` gives permutations of whole groups of packed words for
Plonky3's Poseidon2 instances over `FastField p` (`Poseidon2Field`), which permute every state by
the specification (`permute16_encode`, `permute24_encode`). They are the fast prover's leaf hashes,
compressions and grinding. KoalaBear's are its vectorized kernels; every other field has the
instance state by state on its `Poseidon2Field` implementations (`PackedPoseidon2.ofLanes`).
-/

@[expose] public section
namespace CompStark.Poseidon2
open CompPoly.PackedRepr (encode decode)
open Montgomery.Native32

namespace Group

variable {F : Type} [Zero F]

/-- State `l` of a group of eight states of width `t`. -/
def lane (t : Nat) (W : Array F) (l : Nat) : Vector F t :=
  Vector.ofFn fun j ↦ W.getD (8 * j.val + l) 0

/-- Every state of a group of eight states of width `t` through `f`. -/
def map (t : Nat) (f : Vector F t → Vector F t) (W : Array F) : Array F :=
  Array.ofFn (n := 8 * t) fun k ↦ (f (lane t W (k.val % 8)))[k.val / 8]'(by omega)

@[simp] theorem size_map (t : Nat) (f : Vector F t → Vector F t) (W : Array F) :
    (map t f W).size = 8 * t :=
  Array.size_ofFn

/-- State `l < 8` of a mapped group is the image of state `l`. -/
theorem lane_map (t : Nat) (f : Vector F t → Vector F t) (W : Array F) (l : Nat) (hl : l < 8) :
    lane t (map t f W) l = f (lane t W l) := by
  apply Vector.ext
  intro j hj
  have e1 : (8 * j + l) / 8 = j := by omega
  have e2 : (8 * j + l) % 8 = l := by omega
  simp only [lane, map, Vector.getElem_ofFn, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
    show 8 * j + l < 8 * t by omega, dite_true, Option.getD_some, e1, e2]

end Group

variable (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)]

/-- Plonky3's Poseidon2 permutations over `FastField p` on groups of eight states as packed
words. -/
class PackedPoseidon2 where
  /-- The width-16 permutation of a group of eight states. -/
  permute16 : ByteArray → ByteArray
  /-- The width-24 permutation of a group of eight states. -/
  permute24 : ByteArray → ByteArray
  permute16_encode (W : Array (FastField p)) : W.size = 8 * 16 →
    permute16 (encode W) =
      encode (Group.map 16 (permute (Poseidon2Field.params16 (F := FastField p))) W)
  permute24_encode (W : Array (FastField p)) : W.size = 8 * 24 →
    permute24 (encode W) =
      encode (Group.map 24 (permute (Poseidon2Field.params24 (F := FastField p))) W)

/-- The packed permutations state by state, on the field's implementations. -/
@[instance_reducible] def PackedPoseidon2.ofLanes : PackedPoseidon2 p where
  permute16 b := encode (Group.map 16 (Poseidon2Field.perm16 (F := FastField p)).perm (decode b))
  permute24 b := encode (Group.map 24 (Poseidon2Field.perm24 (F := FastField p)).perm (decode b))
  permute16_encode W _ := by
    rw [CompPoly.PackedRepr.decode_encode, funext (Poseidon2Field.perm16 (F := FastField
        p)).perm_eq]
  permute24_encode W _ := by
    rw [CompPoly.PackedRepr.decode_encode, funext (Poseidon2Field.perm24 (F := FastField
        p)).perm_eq]

end CompStark.Poseidon2
