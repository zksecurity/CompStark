/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Fast.Refines
public import CompStark.KoalaBear.Poseidon2
public import CompStark.KoalaBear.Challenge
public import CompPoly.Univariate.NTTFast.Packed.Instances

/-! # The fast prover over KoalaBear

The fast backend over KoalaBear and its quartic extension `KoalaBear.Fast.Ext4`, on KoalaBear's
vectorized Poseidon2 and CompPoly's compiled coset LDE (`backendFor`). This module belongs to the
CPU-targeted native library: the compiler specializes the generic backend here, with KoalaBear's
constants as immediates. Its proofs are the specification's (`prove_fast`).
-/

@[expose] public section
namespace CompStark.KoalaBear
open CompStark.Fri CompStark.Stark

local notation "F" => _root_.KoalaBear.Fast.Field
local notation "EF" => _root_.KoalaBear.Fast.Ext4

/-- The fast backend over KoalaBear, with the extension plans and quotient tables of a proof of a
`2 ^ logN`-row trace and `2 ^ logChunks` quotient chunks prepared. -/
def backendFor (logN logBlowup logChunks : Nat) : Backend F EF 24 :=
  Stark.Fast.backendFor logN logBlowup logChunks

/-- KoalaBear's domains of extension elements, up to `4 · 2 ^ 24` words, are addressable. -/
theorem domainsAddressable : DomainsAddressable F EF := by
  unfold DomainsAddressable Addressable
  rw [Mont32.d_ext4, twoAdicity_eq]
  have := USize.le_size
  omega

/-- **The fast prover over KoalaBear is correct**: for an input of the shapes the prover supports
(`InputOk`), it produces the specification's proof, unless the out-of-domain point `ζ` lands in
the base field (probability about `2 ^ -93`). -/
theorem prove_fast {params : Params} {air : Air F} {logN : Nat} {trace : Array F}
    (publicValues : List F) (input : InputOk EF params air logN trace)
    (outOfDomain : Ext.OutsideBase (outOfDomainPoint EF params air logN trace publicValues)) :
    proveWith (backendFor logN params.logBlowup (air.logQuotientChunks logN)) params air logN trace
        publicValues =
      prove EF params air logN trace publicValues :=
  Stark.Fast.prove_fast (by rw [twoAdicity_eq]; decide) domainsAddressable publicValues input
    outOfDomain

end CompStark.KoalaBear
