/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.BabyBear.Field
public import CompStark.Poseidon2.PackedInstances
public import CompStark.Poseidon2.PackedBabyBear

/-! # Poseidon2 over BabyBear

Plonky3's default BabyBear instances (`Poseidon2.BabyBear.width16`, `width24`) on BabyBear's
packed kernels (`Poseidon2.Packed.Instances`): the global `Poseidon2Field` instance runs one state
in lane 0 of a packed group, the global `PackedPoseidon2` instance runs whole groups.
-/

@[expose] public section
namespace CompStark.BabyBear
open CompStark.Poseidon2.Packed

local notation "F" => _root_.BabyBear.Fast.Field

/-- Poseidon2 instances over BabyBear on its packed kernels, with any round constants. -/
abbrev Instances : Type := Poseidon2.Packed.Instances _root_.BabyBear.fieldSize

/-- Plonky3's default instances. -/
def defaultInstances : Instances where
  params16 := Poseidon2.BabyBear.width16 F
  params24 := Poseidon2.BabyBear.width24 F
  K16 := Packed16.ofParams (Poseidon2.BabyBear.width16 F)
  K24 := Packed24.ofParams (Poseidon2.BabyBear.width24 F)
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

/-- Plonky3's default BabyBear Poseidon2 instances on the packed kernels. -/
instance instPoseidon2Field : Poseidon2Field F := defaultInstances.field

theorem params16_eq :
    (Poseidon2Field.params16 : Poseidon2.Params F 16) = Poseidon2.BabyBear.width16 F := rfl

theorem params24_eq :
    (Poseidon2Field.params24 : Poseidon2.Params F 24) = Poseidon2.BabyBear.width24 F := rfl

/-- BabyBear's vectorized Poseidon2 kernels on groups of eight states, with Plonky3's default
constants. -/
instance instPackedPoseidon2 : Poseidon2.PackedPoseidon2 _root_.BabyBear.fieldSize :=
  defaultInstances.packed

end CompStark.BabyBear
