/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Poseidon2.Basic

/-! # Implementations of Poseidon2

An implementation of the permutation with parameters `P` (`Impl P`) is a function on states with a
proof that it is the specification `permute P`. Every field has one, the specification itself
(`Impl.spec`); a field with faster kernels supplies those instead.

`Poseidon2Field F` gives Plonky3's two Poseidon2 instances over `F`, of widths 16 and 24, each with
an implementation. Plonky3's hashes, challenger and STARK primitives are built on them.
-/

@[expose] public section
namespace CompStark

namespace Poseidon2

/-- An implementation of the permutation with parameters `P`. -/
structure Impl {F : Type*} [CommRing F] {t : Nat} (P : Params F t) where
  /-- The permutation. -/
  perm : Vector F t → Vector F t
  perm_eq (s : Vector F t) : perm s = permute P s

/-- The specification as an implementation. -/
def Impl.spec {F : Type*} [CommRing F] {t : Nat} (P : Params F t) : Impl P :=
  ⟨permute P, fun _ ↦ rfl⟩

end Poseidon2

/-- Plonky3's Poseidon2 instances over `F` of widths 16 and 24, with their implementations. -/
class Poseidon2Field (F : Type) [Field F] where
  /-- The width-16 instance, of the Merkle compression. -/
  params16 : Poseidon2.Params F 16
  /-- The width-24 instance, of the Merkle leaf hash and the challenger. -/
  params24 : Poseidon2.Params F 24
  perm16 : Poseidon2.Impl params16
  perm24 : Poseidon2.Impl params24

/-- The instances `P16` and `P24`, implemented by the specification. -/
abbrev Poseidon2Field.ofSpec {F : Type} [Field F] (P16 : Poseidon2.Params F 16)
    (P24 : Poseidon2.Params F 24) : Poseidon2Field F :=
  ⟨P16, P24, .spec P16, .spec P24⟩

end CompStark
