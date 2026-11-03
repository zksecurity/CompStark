/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.KoalaBear.Field
public import CompStark.Poseidon2.PackedInstances
public import CompStark.Poseidon2.PackedKoalaBear

/-! # Poseidon2 over KoalaBear

Plonky3's default KoalaBear instances (`Poseidon2.KoalaBear.width16`, `width24`) on KoalaBear's
packed kernels (`Poseidon2.Packed.Instances`): the global `Poseidon2Field` instance runs one state
in lane 0 of a packed group, the global `PackedPoseidon2` instance runs whole groups.
-/

@[expose] public section
namespace CompStark.KoalaBear
open CompStark.Poseidon2.Packed

local notation "F" => _root_.KoalaBear.Fast.Field

/-- Poseidon2 instances over KoalaBear on its packed kernels, with any round constants. -/
abbrev Instances : Type := Poseidon2.Packed.Instances _root_.KoalaBear.fieldSize

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

/-- The width-16 permutation of one state on the packed kernels, with Plonky3's default
constants: a definition of its own, so that it compiles to the field's kernels. -/
def perm16 (s : Vector F 16) : Vector F 16 := defaultInstances.perm16 s

/-- The width-24 permutation of one state on the packed kernels, with Plonky3's default
constants. -/
def perm24 (s : Vector F 24) : Vector F 24 := defaultInstances.perm24 s

/-- Plonky3's default KoalaBear Poseidon2 instances on the packed kernels. -/
instance instPoseidon2Field : Poseidon2Field F where
  params16 := Poseidon2.KoalaBear.width16 F
  params24 := Poseidon2.KoalaBear.width24 F
  perm16 := ⟨perm16, defaultInstances.perm16_eq⟩
  perm24 := ⟨perm24, defaultInstances.perm24_eq⟩

theorem params16_eq :
    (Poseidon2Field.params16 : Poseidon2.Params F 16) = Poseidon2.KoalaBear.width16 F := rfl

theorem params24_eq :
    (Poseidon2Field.params24 : Poseidon2.Params F 24) = Poseidon2.KoalaBear.width24 F := rfl

/-- The width-16 permutation of the group of eight states at word `0`, with Plonky3's default
constants. -/
def packed16 (b : ByteArray) : ByteArray :=
  permute16 _root_.KoalaBear.fieldSize defaultInstances.K16 b 0

/-- The width-24 permutation of the group of eight states at word `0`, with Plonky3's default
constants. -/
def packed24 (b : ByteArray) : ByteArray :=
  permute24 _root_.KoalaBear.fieldSize defaultInstances.K24 b 0

/-- KoalaBear's vectorized Poseidon2 kernels on groups of eight states, with Plonky3's default
constants. -/
instance instPackedPoseidon2 : Poseidon2.PackedPoseidon2 _root_.KoalaBear.fieldSize where
  permute16 := packed16
  permute24 := packed24
  permute16_encode := defaultInstances.permute16_group
  permute24_encode := defaultInstances.permute24_group

end CompStark.KoalaBear
