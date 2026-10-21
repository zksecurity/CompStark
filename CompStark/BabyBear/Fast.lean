/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Fast
public import CompStark.BabyBear.Poseidon2
public import CompStark.BabyBear.Challenge
public import CompPoly.Univariate.NTTFast.Packed.Instances

/-! # The fast prover over BabyBear

The fast backend over BabyBear and its quartic extension `BabyBear.Fast.Ext4` (`backendFor`), on
BabyBear's Poseidon2 implementation applied state by state to packed groups
(`PackedPoseidon2.ofLanes`) and CompPoly's compiled coset LDE. This module belongs to the
CPU-targeted native library, where the compiler specializes the generic backend with BabyBear's
constants. `Stark.Fast.prove_fast` applies once BabyBear's largest domains are addressable
(`DomainsAddressable`), which holds with 64-bit indices.
-/

@[expose] public section
namespace CompStark.BabyBear
open CompStark.Fri CompStark.Stark

local notation "F" => _root_.BabyBear.Fast.Field
local notation "EF" => _root_.BabyBear.Fast.Ext4

/-- BabyBear's Poseidon2 implementation on packed groups, state by state. -/
instance instPackedPoseidon2 : Poseidon2.PackedPoseidon2 _root_.BabyBear.fieldSize :=
  .ofLanes _

/-- The fast backend over BabyBear, with the extension plans and quotient tables of a proof of a
`2 ^ logN`-row trace and `2 ^ logChunks` quotient chunks prepared. -/
def backendFor (logN logBlowup logChunks : Nat) : Backend F EF 24 :=
  Stark.Fast.backendFor logN logBlowup logChunks

end CompStark.BabyBear
