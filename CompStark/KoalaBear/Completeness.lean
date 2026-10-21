/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Completeness
public import CompStark.KoalaBear.Poseidon2

/-! # Completeness over KoalaBear

`completeness` for Plonky3's KoalaBear configuration: the honest prover's proof of a satisfied
AIR verifies, over any challenge field, for example KoalaBear's quartic or quintic extension. The
bad luck it excludes (`NoBadLuck`) has probability about `2 ^ -93` for the quartic extension and
`2 ^ -124` for the quintic one (the out-of-domain point in the base field), and about
`exp (-2 ^ (31 - b))` for a proof-of-work search of `b` bits finding no witness.
-/

@[expose] public section
namespace CompStark.KoalaBear
open CompStark.Fri CompStark.Stark

local notation "F" => _root_.KoalaBear.Fast.Field

/-- **Completeness over KoalaBear.** For a valid configuration and an honest run over any
challenge field `EF` without bad luck, if the trace satisfies the AIR with as many public values
as the AIR declares, the honest prover's proof verifies. -/
theorem completeness {EF : Type} [Challenge F EF] {params : Params} {air : Air F} {logN : Nat}
    {trace : Array F} {publicValues : List F} (config : ValidConfig params air logN)
    (luck : NoBadLuck EF params air logN trace publicValues) :
    air.Satisfied logN trace publicValues → publicValues.length = air.numPublicValues →
      verify params air (prove EF params air logN trace publicValues) publicValues = .ok () :=
  Stark.completeness config luck

end CompStark.KoalaBear
