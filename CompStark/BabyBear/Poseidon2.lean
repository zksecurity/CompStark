/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.BabyBear.Field
public import CompStark.Poseidon2.BabyBear
public import CompStark.Poseidon2.Impl

/-! # Poseidon2 over BabyBear

Plonky3's default BabyBear instances (`Poseidon2.BabyBear.width16`, `width24`), implemented by the
specification on the Montgomery field `BabyBear.Fast.Field`.
-/

@[expose] public section
namespace CompStark.BabyBear

local notation "F" => _root_.BabyBear.Fast.Field

/-- Plonky3's default BabyBear Poseidon2 instances on the specification. -/
instance instPoseidon2Field : Poseidon2Field F :=
  .ofSpec (Poseidon2.BabyBear.width16 F) (Poseidon2.BabyBear.width24 F)

end CompStark.BabyBear
