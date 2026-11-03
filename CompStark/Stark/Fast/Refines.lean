/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Refines
public import CompStark.Batch.Refines
public import CompStark.Stark.Fast.Transcript
public import CompStark.Stark.Fast.Lde
public import CompStark.Stark.Fast.Chunks
public import CompStark.Stark.Fast.Commit
public import CompStark.Stark.Fast.Vectors
public import CompStark.Stark.Fast.Quotient
public import CompStark.Stark.Fast.Openings
public import CompStark.Stark.Fast.Permutation

/-! # The fast prover proves what the specification proves

Over a Montgomery field whose largest domains of extension elements are addressable
(`DomainsAddressable`), the fast backend refines the specification (`backendFor_refines`), so its
proofs are the specification's (`prove_fast`), batch proofs included (`proveBatch_fast`).
-/

@[expose] public section
namespace CompStark.Stark.Fast
open CompStark.Fri CompStark.Poseidon2 Montgomery.Native32

variable {p : ℕ} [Mont32Field p] [Mont32BaseField p] [Poseidon2Field (FastField p)]
  [PackedPoseidon2 p] {EF : Type} [FastExt p EF] [Mont32.AlgebraId EF] [PlanesInv p EF]

local notation "F" => FastField p

/-- The fast backend refines the specification. -/
def backendFor_refines (hA : DomainsAddressable F EF)
    (kernels : List (AirKernel p)) (logBlowup : Nat) (shapes : List (Nat × Nat)) :
    Refines (backendFor (EF := EF) kernels logBlowup shapes) :=
  have h16 : 4 * (FastExt.d p EF * 2 ^ twoAdicity F) < USize.size := by
    unfold DomainsAddressable Addressable at hA
    rw [Mont32.d_eq] at hA
    omega
  { RT := RT
    RM := RM
    RC := RC
    RV := ExtPlanes.Rel
    RQ := QRel
    transcript := transcript_eq
    ldeTrace := fun logH bits shift w t m ⟨_, k, hk, ht⟩ hm hb ha ↦ by
      change RM (ldeWordsWith _ logH bits shift w t) _
      rw [ht]
      exact ldeWordsWith_rel _ (fun e he ↦ by
        obtain ⟨⟨n, c⟩, -, he⟩ := List.mem_flatMap.mp he
        exact ldePlans_valid n logBlowup c e he) logH bits shift w m k hk hm hb ha
    traceValues := fun ⟨hm, k, hk, ht⟩ ↦ by
      change CompPoly.PackedRepr.decode _ = _
      rw [ht, joinRows_rowChunks _ _ _ k hk hm, CompPoly.PackedRepr.decode_encode]
    lde := ldeWith_rel _ fun e he ↦ by
      obtain ⟨⟨n, c⟩, -, he⟩ := List.mem_flatMap.mp he
      exact ldePlans_valid n logBlowup c e he
    commit := commit_rel
    cap := fun h hc ↦ cap_rel hc h
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
        exact quotientWith_rel _ A pis _ _ alpha h hs hh hp hps hc
      · exact quotientWith_rel [] A pis _ _ alpha h hs hh hp hps hc
    lookupQuotient := fun A ext pis d l _ _ _ _ _ _ chs t alpha k h hs hh hp hps hr hrs hrh hk hc ↦
      by
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
        exact lookupQuotientWith_rel _ A ext pis _ _ chs t alpha k h hs hh hp hps hr hrs hrh hk hc
         
      · exact lookupQuotientWith_rel [] A ext pis _ _ chs t alpha k h hs hh hp hps hr hrs hrh hk hc
         
    combine := fun x _ _ _ _ hq hr hab ha ↦ combine_rel h16 x hq hr hab ha
    chunks := fun bits logN l _ _ hv ha hlb hb ↦ chunksWith_rel _ (fun e he ↦ by
        obtain ⟨⟨n, c⟩, -, he⟩ := List.mem_flatMap.mp he
        exact ldePlans_valid n logBlowup c e he) bits logN l hv ha hb
      (size_bound' h16 (by rw [ha]; exact Nat.pow_le_pow_right (by decide) (by omega)))
    permutation := fun bits A ls logN t pis chs hok ↦
      permutationLdeWith_rel _ (fun e he ↦ by
        obtain ⟨⟨n, c⟩, -, he⟩ := List.mem_flatMap.mp he
        exact ldePlans_valid n logBlowup c e he) bits A ls logN t pis chs hok

    toArray := toArray_rel h16
    ofArray := ExtPlanes.ofArray_rel
    size := fun h ↦ h.1
    openings := fun b _ _ h hok ↦ openings_rel b h hok
    fold := fun la beta s _ _ h ha hla hs ↦ fold_rel h16 (fun k hk ↦ by
        simp only [foldTables, Array.getElem_map, Array.getElem_range]) la beta s h ha hla hs
    addScaled := fun x _ _ _ _ hv hw hab ha ↦ addScaled_rel h16 x hv hw hab ha
    leaves := fun k _ _ h ha hk hp ↦ leaves_rel h16 k h ha hk hp }

/-- **The fast prover is correct.** For an input of the shapes the prover supports (`InputOk`),
it produces the specification's proof, unless the out-of-domain point `ζ` lands in the base field,
where both provers divide by zero and compute different garbage. -/
theorem prove_fast (hA : DomainsAddressable F EF)
    (kernels : List (AirKernel p)) {params : Params}
    {air : Air F} {logN : Nat} {words : Array ByteArray} {trace : Array F}
    (publicValues : List F) (encoded : RT logN air.width words trace)
    (input : InputOk EF params air logN trace)
    (outOfDomain : Ext.OutsideBase (outOfDomainPoint EF params air logN trace publicValues)) :
    proveWith (backendFor (EF := EF) kernels params.logBlowup [(logN, air.logQuotientChunks logN)])
        params
        air logN words publicValues =
      prove EF params air logN trace publicValues :=
  proveWith_refines hA (backendFor_refines hA _ _ _) publicValues encoded input outOfDomain

/-- **The fast batch prover is correct.** For a batch of the shapes the prover supports
(`Batch.InputOk`) with a list of public values per instance, it produces the specification's
proof, unless the out-of-domain point `ζ` lands in the base field. -/
theorem proveBatch_fast (hA : DomainsAddressable F EF)
    (kernels : List (AirKernel p)) {params : Params}
    {instances : List (Batch.Instance F)} {words : List (Array ByteArray)}
    {traces : List (Array F)} {publicValues : List (List F)}
    (encoded : List.Forall₂ (fun t (m : Batch.Instance F × Array F) ↦
      RT m.1.logN m.1.air.width t m.2) words (instances.zip traces))
    (input : Batch.InputOk EF params instances traces)
    (publicValuesLength : publicValues.length = instances.length)
    (outOfDomain :
      Ext.OutsideBase (Batch.batchOutOfDomainPoint EF params instances traces publicValues)) :
    Batch.proveBatchWith (backendFor (EF := EF) kernels params.logBlowup (Batch.shapes instances))
        params
        instances words publicValues =
      Batch.proveBatch EF params instances traces publicValues :=
  Batch.proveBatchWith_refines hA (backendFor_refines hA _ _ _) encoded input publicValuesLength
    outOfDomain

end CompStark.Stark.Fast
