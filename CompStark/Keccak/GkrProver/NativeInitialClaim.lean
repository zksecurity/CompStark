/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.NativeReductionTrace

/-! The production setup constructs the specification's first weighted claim. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak CompStark.Keccak.Gkr CompStark.BinaryFields BF64
open scoped BigOperators

/-- A one-bit machine word is the corresponding polynomial-basis power. -/
theorem basisWord_toField (z : Fin 64) :
    Word.toField ⟨1 <<< z.val.toUInt64⟩=g^z.val := by
  apply CompStark.Pcs.wordBits_injective
  rw [CompStark.Pcs.wordBits_power]
  have h : ∀ i : Fin 64,CompStark.Pcs.wordBits (Word.toField ⟨1 <<< i.val.toUInt64⟩)=Pi.single i 1 := by
    decide +kernel
  exact h z

/-- An in-bounds extracted array coordinate is its original coordinate. -/
theorem array_extract_get! {F : Type} [Inhabited F] (a : Array F) (lo hi i : Nat)
    (hs : i<(a.extract lo hi).size) : (a.extract lo hi)[i]! = a[lo+i]! := by
  rw [getElem!_pos (a.extract lo hi) i hs,Array.getElem_extract,← getElem!_pos a (lo+i) (by
    have hh := hs
    rw [Array.size_extract] at hh
    omega)]

attribute [local irreducible] eqTable dot outputWords Writer.sampleMany proveLayerM

/-- The native initial claim retains the entering pack dimension and all position weights. -/
theorem nativeInitialClaim_shape (batch output : Array W) (segment : W) (lanes : Array W) (middle : W)
    (p : Nat) (hb : batch.size=p+4) :
    (nativeInitialClaim batch output segment lanes middle).point.size=p+1 ∧
      (nativeInitialClaim batch output segment lanes middle).weights.size=1600 := by
  constructor
  · simp only [nativeInitialClaim,Array.size_push,Array.size_extract,Nat.min_self,hb]
    omega
  · exact Array.size_ofFn ..

/-- The production initial claim equals the protocol's first claim for the supplied output evaluations. -/
theorem nativeInitialClaim_toProtocol (batch output : Array W) (segment : W) (lanes : Array W) (middle : W)
    (p : Nat) (hb : batch.size=p+4) (hl : lanes.size=5)
    (out : Fin (2^(p+4)) → Fin 25 → E) (t : Transcript E p)
    (htb : t.instancePoint=fun i => batch[i.val]!.toField)
    (hts : t.segment=segment.toField) (htl : t.lanePoint=fun i => lanes[i.val]!.toField)
    (htm : t.middleValue=middle.toField)
    (ho : ∀ l : Fin 25,output[l.val]!.toField=mle (fun b => out b l) t.instancePoint) :
    (nativeInitialClaim batch output segment lanes middle).toProtocol p=firstClaim (ofK g) out t := by
  have hlow : (batch.extract 0 4).size=4 := by rw [Array.size_extract,hb]; omega
  have hhigh : (batch.extract 4 batch.size).size=p := by rw [Array.size_extract,Nat.min_self,hb]; omega
  apply protocolClaim_ext
  · change (middle+segment*dot ((eqTable lanes).extract 0 25) output).toField = _
    have heq : ((eqTable lanes).extract 0 25).size=25 := by rw [Array.size_extract,eqTable_size,hl]; decide
    rw [dot_eq_sum,heq]
    change WordExt3.ringEquiv (_+_*∑ i ∈ Finset.range 25,_) = _
    rw [map_add,map_mul,map_sum,← Fin.sum_univ_eq_sum_range]
    simp only [firstClaim,htm,hts]
    congr 2
    apply Finset.sum_congr rfl
    intro l _
    rw [map_mul]
    change ((eqTable lanes).extract 0 25)[l.val]!.toField*output[l.val]!.toField = _
    rw [array_extract_get! _ _ _ _ (by rw [heq]; exact l.isLt),Nat.zero_add,
      eqTable_dimension_toField lanes 5 hl ⟨l.val,by omega⟩,ho l,htl]
    rfl
  · funext i
    change (eqTable (batch.extract 0 4))[i.val]!.toField = _
    rw [eqTable_dimension_toField (batch.extract 0 4) 4 hlow i]
    simp only [firstClaim,htb]
    apply congrArg (fun point : Fin 4 → E => eqWeight point i.val)
    funext j
    rw [array_extract_get! _ _ _ _ (by rw [hlow]; exact j.isLt),Nat.zero_add]
  · funext i
    change ((batch.extract 4 batch.size).push segment)[i.val]!.toField = _
    simp only [firstClaim,htb,hts]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.val_last,Fin.lastCases_last]
      rw [← hhigh,array_push_get_last]
    · simp only [Fin.val_castSucc,Fin.lastCases_castSucc]
      rw [array_push_get_old _ _ _ (by rw [hhigh]; exact j.isLt),
        array_extract_get! _ _ _ _ (by rw [hhigh]; exact j.isLt)]
      congr 2
      omega
  · funext j
    change ((Array.ofFn fun k : Fin 1600 => WordExt3.mulScalar (eqTable lanes)[k.val/64]!
      ⟨1 <<< (k.val%64).toUInt64⟩)[j.val]!).toField = _
    rw [ofFn_get!,WordExt3.toField_mulScalar,basisWord_toField ⟨j.val%64,by omega⟩]
    rw [Algebra.smul_def]
    change ofK (g^(j.val%64))*(eqTable lanes)[j.val/64]!.toField = _
    rw [show ofK (g^(j.val%64))=(ofK g)^(j.val%64) from (map_pow (algebraMap K E) g (j.val%64)),eqTable_dimension_toField lanes 5 hl ⟨j.val/64,by have := j.isLt; omega⟩]
    simp only [firstClaim,htl]
    exact mul_comm _ _

end CompStark.Keccak.GkrProver
