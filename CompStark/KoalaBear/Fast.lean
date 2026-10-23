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

/-- The fast backend over KoalaBear, with the extension plans and quotient tables of instances of
the shapes `shapes` prepared: `(logN, logChunks)` for a `2 ^ logN`-row trace with `2 ^ logChunks`
quotient chunks. -/
def backendFor (logBlowup : Nat) (shapes : List (Nat × Nat)) : Backend F EF 24 :=
  Stark.Fast.backendFor logBlowup shapes

/-- KoalaBear's domains of extension elements, up to `4 · 2 ^ 24` words, are addressable. -/
theorem domainsAddressable : DomainsAddressable F EF := by
  unfold DomainsAddressable Addressable
  rw [Mont32.d_ext4, twoAdicity_eq]
  have := USize.le_size
  omega

/-- **The fast prover over KoalaBear is correct**: for a trace given as chunks of packed rows
(`Stark.Fast.RT`) of the shapes the prover supports (`InputOk`), it produces the specification's
proof, unless the out-of-domain point `ζ` lands in the base field (probability about
`2 ^ -93`). -/
theorem prove_fast {params : Params} {air : Air F} {logN : Nat} {words : Array ByteArray}
    {trace : Array F} (publicValues : List F) (encoded : Stark.Fast.RT logN air.width words trace)
    (input : InputOk EF params air logN trace)
    (outOfDomain : Ext.OutsideBase (outOfDomainPoint EF params air logN trace publicValues)) :
    proveWith (backendFor params.logBlowup [(logN, air.logQuotientChunks logN)]) params air logN
        words publicValues =
      prove EF params air logN trace publicValues :=
  Stark.Fast.prove_fast (by rw [twoAdicity_eq]; decide) domainsAddressable publicValues encoded
    input outOfDomain

/-- **The fast batch prover over KoalaBear is correct**: for traces given as chunks of packed rows
of a batch of the shapes the prover supports (`Batch.InputOk`) with a list of public values per
instance, it produces the specification's proof, unless the out-of-domain point `ζ` lands in the
base field. -/
theorem proveBatch_fast {params : Params} {instances : List (Batch.Instance F)}
    {words : List (Array ByteArray)} {traces : List (Array F)} {publicValues : List (List F)}
    (encoded : List.Forall₂ (fun t (m : Batch.Instance F × Array F) ↦
      Stark.Fast.RT m.1.logN m.1.air.width t m.2) words (instances.zip traces))
    (input : Batch.InputOk EF params instances traces)
    (publicValuesLength : publicValues.length = instances.length)
    (outOfDomain :
      Ext.OutsideBase (Batch.batchOutOfDomainPoint EF params instances traces publicValues)) :
    Batch.proveBatchWith (backendFor params.logBlowup (Batch.shapes instances)) params instances
        words publicValues =
      Batch.proveBatch EF params instances traces publicValues :=
  Stark.Fast.proveBatch_fast (by rw [twoAdicity_eq]; decide) domainsAddressable encoded input
    publicValuesLength outOfDomain

/-- The fast backend over KoalaBear on the Poseidon2 instances `I` (`backendFor` is it on Plonky3's
default ones), specialized here, in the CPU-targeted library. -/
def Instances.backendFor (I : Instances) (logBlowup : Nat) (shapes : List (Nat × Nat)) :
    Backend F EF 24 :=
  letI := I.field
  letI := I.packed
  Stark.Fast.backendFor logBlowup shapes

/-- **The fast prover over KoalaBear on the Poseidon2 instances `I` is correct** (`prove_fast`). -/
theorem Instances.prove_fast (I : Instances) {params : Params} {air : Air F} {logN : Nat}
    {words : Array ByteArray} {trace : Array F} (publicValues : List F)
    (encoded : Stark.Fast.RT logN air.width words trace)
    (input : InputOk EF params air logN trace)
    (outOfDomain : Ext.OutsideBase
      (@outOfDomainPoint F _ I.field EF _ params air logN trace publicValues)) :
    proveWith (I.backendFor params.logBlowup [(logN, air.logQuotientChunks logN)]) params air logN
        words publicValues =
      @prove F _ I.field EF _ params air logN trace publicValues :=
  letI := I.field
  letI := I.packed
  Stark.Fast.prove_fast (by rw [twoAdicity_eq]; decide) domainsAddressable publicValues encoded
    input outOfDomain

end CompStark.KoalaBear
