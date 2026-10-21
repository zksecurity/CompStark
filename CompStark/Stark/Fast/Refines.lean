/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Refines
public import CompStark.Batch.Refines
public import CompStark.Stark.Fast.Transcript
public import CompStark.Stark.Fast.Lde
public import CompStark.Stark.Fast.Commit
public import CompStark.Stark.Fast.Vectors
public import CompStark.Stark.Fast.Quotient
public import CompStark.Stark.Fast.Openings

/-! # The fast prover proves what the specification proves

Over a Montgomery field with a fourth root of unity (`2 ≤ twoAdicity`, for the norm of `invDenoms`)
whose largest domains of extension elements are addressable (`DomainsAddressable`), the fast
backend refines the specification (`backendFor_refines`), so its proofs are the specification's
(`prove_fast`), batch proofs included (`proveBatch_fast`).
-/

@[expose] public section
namespace CompStark.Stark.Fast
open CompStark.Fri CompStark.Poseidon2 Montgomery.Native32
open CompPoly.CPolynomial.NTTFast.Packed (PackedCosetLde)

variable {p : ℕ} [Mont32Field p] [Mont32BaseField p] [Binomial4 p] [Poseidon2Field (FastField p)]
  [PackedPoseidon2 p] [PackedCosetLde p]

local notation "F" => FastField p
local notation "EF" => Ext4 p

/-- The fast backend refines the specification. -/
def backendFor_refines (hζ : 2 ≤ twoAdicity F) (hA : DomainsAddressable F EF)
    (logBlowup : Nat) (shapes : List (Nat × Nat)) :
    Refines (backendFor (p := p) logBlowup shapes) :=
  have h16 : 16 * 2 ^ twoAdicity F < USize.size := by
    unfold DomainsAddressable Addressable at hA
    rw [Mont32.d_ext4] at hA
    omega
  { RM := RM
    RC := RC
    RV := RV
    transcript := transcript_eq
    lde := ldeWith_rel _ fun e he ↦ by
      obtain ⟨⟨n, c⟩, -, he⟩ := List.mem_flatMap.mp he
      exact ldePlans_valid n logBlowup c e he
    commit := commit_rel
    root := root_rel
    openAt := openAt_rel
    logHeight := fun h ↦ congrArg Nat.log2 (maxHeight_rel h)
    quotient := fun A pis d l _ _ _ _ alpha h hs hh hp hps hc ↦ by
      dsimp only [backendFor]
      split
      · rename_i n c T hfind
        have hmem := List.mem_of_find?_eq_some hfind
        have hd := List.find?_some hfind
        simp only [Bool.and_eq_true, beq_iff_eq] at hd
        obtain ⟨⟨n', c'⟩, -, he⟩ := List.mem_map.mp hmem
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        obtain ⟨rfl, rfl⟩ := hd
        exact quotientWith_rel A pis _ _ alpha h hs hh hp hps hc
      · exact quotientWith_rel A pis _ _ alpha h hs hh hp hps hc
    lookupQuotient := fun A ext pis d l _ _ _ _ _ _ chs t alpha h hp hr ↦
      lookupQuotient_rel A ext pis d l chs t alpha h hp hr
    openedAt := fun b zs _ _ h hs hz ↦ openedAt_rel hζ b zs h hs hz
    toArray := toArray_rel h16
    ofArray := ofArray_rel
    size := fun h ↦ h.1
    reduce := fun alpha _ _ h hok ↦ reduce_rel hζ alpha h hok
    fold2 := fun beta k _ _ h ha hk ↦ fold2_rel h16 beta k h ha hk
    addScaled := fun x _ _ _ _ hv hw hab ha ↦ addScaled_rel h16 x hv hw hab ha
    leaves := fun k _ _ h ha ↦ leaves_rel h16 k h ha }

/-- **The fast prover is correct.** For an input of the shapes the prover supports (`InputOk`),
it produces the specification's proof, unless the out-of-domain point `ζ` lands in the base field,
where both provers divide by zero and compute different garbage. -/
theorem prove_fast (hζ : 2 ≤ twoAdicity F) (hA : DomainsAddressable F EF) {params : Params}
    {air : Air F} {logN : Nat} {trace : Array F} (publicValues : List F)
    (input : InputOk EF params air logN trace)
    (outOfDomain : Ext.OutsideBase (outOfDomainPoint EF params air logN trace publicValues)) :
    proveWith (backendFor params.logBlowup [(logN, air.logQuotientChunks logN)]) params air logN
        trace publicValues =
      prove EF params air logN trace publicValues :=
  proveWith_refines hA (backendFor_refines hζ hA _ _) publicValues input outOfDomain

/-- **The fast batch prover is correct.** For a batch of the shapes the prover supports
(`Batch.InputOk`) with a list of public values per instance, it produces the specification's
proof, unless the out-of-domain point `ζ` lands in the base field. -/
theorem proveBatch_fast (hζ : 2 ≤ twoAdicity F) (hA : DomainsAddressable F EF) {params : Params}
    {instances : List (Batch.Instance F)} {traces : List (Array F)} {publicValues : List (List F)}
    (input : Batch.InputOk EF params instances traces)
    (publicValuesLength : publicValues.length = instances.length)
    (outOfDomain :
      Ext.OutsideBase (Batch.batchOutOfDomainPoint EF params instances traces publicValues)) :
    Batch.proveBatchWith (backendFor params.logBlowup (Batch.shapes instances)) params instances
        traces publicValues =
      Batch.proveBatch EF params instances traces publicValues :=
  Batch.proveBatchWith_refines hA (backendFor_refines hζ hA _ _) input publicValuesLength
    outOfDomain

end CompStark.Stark.Fast
