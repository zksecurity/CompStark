/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.OpeningSemantics
public import CompStark.Keccak.GkrProver.ProductVertices

/-! Committed-witness semantics of native RMFE product coefficients. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak CompStark.Keccak.Gkr BF64
open scoped BigOperators

/-- Each retained pre-chi slice is the corresponding committed-witness segment state after its linear layer. -/
def PreChiRefines (w : SlicedWitness) {p : Nat} (q : Witness p) : Prop :=
  ∀ (d : Fin 12) (m : Fin 2) (b : Fin (2^p)) (i : Fin 16) (j : Fin 1600),
    sliceBit ((w.layers[12*(m.val+1)-d.val]!)[j.val*(2^w.nLog/64)+b.val/4]!)
      ⟨16*(b.val%4)+i.val,by omega⟩ =
        linear (segmentState q (packInstance i b) m (11-d.val) (by omega)) j

/-- The selected sixteen-bit subword retains exactly its source slice bit. -/
theorem packSubword_bit (raw : UInt64) (b : Nat) (i : Fin 16) :
    (((raw >>> (16*(b%4)).toUInt64) &&& 65535).toNat.testBit i.val) =
      raw.toNat.testBit (16*(b%4)+i.val) := by
  rw [UInt64.toNat_and,Nat.testBit_and,UInt64.toNat_shiftRight]
  have hm : (65535 : UInt64).toNat.testBit i.val = true := by
    have h : ∀ k : Fin 16, (65535 : UInt64).toNat.testBit k.val = true := by decide
    exact h i
  rw [hm,Bool.and_true,Nat.testBit_shiftRight]
  have hs : (16*(b%4)).toUInt64.toNat%64=16*(b%4) := by
    simp only [Nat.toUInt64,UInt64.toNat_ofNat']
    omega
  rw [hs]

/-- Embedding a selected raw subword gives the protocol embedding of its sixteen source slice bits. -/
theorem packSubword_polynomial (raw : UInt64) (b : Nat) :
    payloadWordPolynomial (embeddingRaw ((raw >>> (16*(b%4)).toUInt64) &&& 65535)) =
      Embedding.kemb (fun i : Fin 16 => ZMod.castHom (dvd_refl 2) W
        (sliceBit raw ⟨16*(b%4)+i.val,by omega⟩)) := by
  rw [payloadWordPolynomial,embeddingRaw_poly]
  simp only [Embedding.kemb,LinearMap.coe_mk,AddHom.coe_mk,Polynomial.map_sum,Polynomial.map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [packSubword_bit,sliceBit_cast,Polynomial.map_map]
  have hcast : (ZMod.castHom (dvd_refl 2) W).comp (ZMod.castHom (dvd_refl 2) (ZMod 2)) =
      ZMod.castHom (dvd_refl 2) W := by rw [ZMod.castHom_self,RingHom.comp_id]
  rw [hcast]
  split <;> simp only [map_one,map_zero]

/-- The all-ones payload polynomial is the protocol's affine RMFE factor. -/
theorem onesPayload_polynomial : payloadWordPolynomial (embeddingRaw 65535) =
    Embedding.kemb (fun _ : Fin 16 => (1 : W)) := by
  rw [payloadWordPolynomial,embeddingRaw_ones_poly]
  simp only [Embedding.kemb,LinearMap.coe_mk,AddHom.coe_mk,Polynomial.map_sum,
    one_smul,Polynomial.map_map]
  have hcast : (ZMod.castHom (dvd_refl 2) W).comp (ZMod.castHom (dvd_refl 2) (ZMod 2)) =
      ZMod.castHom (dvd_refl 2) W := by rw [ZMod.castHom_self,RingHom.comp_id]
  rw [hcast]

/-- Native product addressing is the natural sliced-state address whenever that address fits the machine word. -/
theorem productAddress_nat (groups b : Nat) (j : Fin 1600)
    (haddr : j.val*groups+b/4<USize.size) :
    (j.val.toUSize*groups.toUSize+(b/4).toUSize).toNat = j.val*groups+b/4 := by
  simp only [Nat.toUSize,← USize.ofNat_mul,← USize.ofNat_add,USize.toNat_ofNat']
  exact Nat.mod_eq_of_lt haddr

/-- A certified pre-chi slice gives the exact protocol RMFE factor at each product position. -/
theorem productFactor_protocol (w : SlicedWitness) {p : Nat} (q : Witness p) (hw : PreChiRefines w q)
    (d : Fin 12) (m : Fin 2) (b : Fin (2^p)) (j : Fin 1600) :
    payloadWordPolynomial (embeddingRaw
      (((w.layers[12*(m.val+1)-d.val]!)[j.val*(2^w.nLog/64)+b.val/4]! >>>
        (16*(b.val%4)).toUInt64) &&& 65535)) = packedLinear (E := W) q d m b j := by
  rw [packSubword_polynomial]
  apply congrArg (fun bits : Fin 16 → W => Embedding.kemb bits)
  funext i
  rw [hw d m b i j]

/-- Each native product payload is exactly the protocol's affine chi polynomial for its certified pre-chi slice. -/
theorem productCell_protocol (w : SlicedWitness) {p : Nat} (q : Witness p) (hw : PreChiRefines w q)
    (d : Fin 12) (m : Fin 2) (b : Fin (2^p)) (j : Fin 1600)
    (haddr : ∀ k : Fin 1600,k.val*(2^w.nLog/64)+b.val/4<USize.size) :
    payloadWordPolynomial (productCell w.layers[12*(m.val+1)-d.val]! (2^w.nLog/64).toUSize
      (b.val/4).toUSize (16*(b.val%4)).toUInt64 prepareRmfeProducts j.val) =
      (Embedding.kemb (fun _ : Fin 16 => (1 : W)))*packedLinear q d m b j+
        (Embedding.kemb (fun _ : Fin 16 => (1 : W))+packedLinear q d m b (along j 1))*
          packedLinear q d m b (along j 2) := by
  rw [productCell_payloadWordPolynomial]
  dsimp only
  have h1 : (1 : USize)=(1 : Nat).toUSize := rfl
  have h2 : (2 : USize)=(2 : Nat).toUSize := rfl
  rw [h1,h2,shiftU_eq_nat j 1 (by decide),shiftU_eq_nat j 2 (by decide),shift_eq,shift_eq]
  rw [productAddress_nat _ b.val j (haddr j),
    productAddress_nat _ b.val (along j 1) (haddr (along j 1)),
    productAddress_nat _ b.val (along j 2) (haddr (along j 2))]
  rw [onesPayload_polynomial,productFactor_protocol w q hw d m b j,
    productFactor_protocol w q hw d m b (along j 1),productFactor_protocol w q hw d m b (along j 2)]

/-- Every transmitted native product coefficient is the honest committed-witness RMFE product coefficient. -/
theorem product_message_honest (w : SlicedWitness) {p : Nat} (q : Witness p)
    (hn : w.nLog=p+4) (hw : PreChiRefines w q) (d : Fin 12) (claim : Claim)
    (hc : claim.point.size=p+1)
    (haddr : ∀ (b : Fin (2^p)) (j : Fin 1600),j.val*(2^w.nLog/64)+b.val/4<USize.size)
    (i : Fin 47) :
    (product w d.val claim prepareRmfeProducts).message[i.val]! =
      honestProductMessage q d (claim.toWordProtocol p) i := by
  rw [product_message_polynomial]
  have hp : w.nLog-4=p := by omega
  rw [hp]
  change Polynomial.coeff _ i.val = Polynomial.coeff _ i.val
  apply congrArg (fun P : Polynomial W => P.coeff i.val)
  rw [← Fin.sum_univ_eq_sum_range]
  unfold honestProduct
  apply Finset.sum_congr rfl
  intro m _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro j _
  rw [productCell_protocol w q hw d m b j (haddr b)]
  have hindex : m.val*2^p+b.val=b.val+2^p*m.val := by ac_rfl
  rw [hindex,eqTable_get_dimension claim.point (p+1) hc
    ⟨b.val+2^p*m.val,by
      rw [pow_succ]
      have hm : m.val=0 ∨ m.val=1 := by omega
      rcases hm with hm | hm <;> simp only [hm,Nat.mul_zero,Nat.mul_one,Nat.add_zero] <;> omega⟩]
  rfl

/-- Certified RMFE embedding commutes with coefficient-field homomorphisms. -/
theorem kemb_map {F G : Type} [CommRing F] [CharP F 2] [CommRing G] [CharP G 2]
    (e : F →+* G) (bits : Fin 16 → F) :
    (Embedding.kemb bits).map e = Embedding.kemb (fun i => e (bits i)) := by
  simp only [Embedding.kemb,LinearMap.coe_mk,AddHom.coe_mk,Polynomial.map_sum,
    Polynomial.map_smul,Polynomial.map_map]
  have hcast : e.comp (ZMod.castHom (dvd_refl 2) F) = ZMod.castHom (dvd_refl 2) G := by
    ext z
    exact zmod_cast_map e z
  rw [hcast]

/-- The honest product polynomial transports from native words to the verifier field. -/
theorem honestProduct_toField {p : Nat} (q : Witness p) (d : Fin 12) (claim : Claim) :
    (honestProduct q d (claim.toWordProtocol p)).map WordExt3.ringEquiv.toRingHom =
      honestProduct q d (claim.toProtocol p) := by
  simp only [honestProduct,Polynomial.map_sum,Polynomial.map_smul,Polynomial.map_add,
    Polynomial.map_mul,kemb_map,packedLinear,zmod_cast_map,map_one,map_mul,eqWeight_map,
    Claim.toWordProtocol,Claim.toProtocol]
  rfl

/-- Every interpreted native product message equals the specification's honest product message. -/
theorem product_message_honest_toField (w : SlicedWitness) {p : Nat} (q : Witness p)
    (hn : w.nLog=p+4) (hw : PreChiRefines w q) (d : Fin 12) (claim : Claim)
    (hc : claim.point.size=p+1)
    (haddr : ∀ (b : Fin (2^p)) (j : Fin 1600),j.val*(2^w.nLog/64)+b.val/4<USize.size)
    (i : Fin 47) :
    (product w d.val claim prepareRmfeProducts).message[i.val]!.toField =
      honestProductMessage q d (claim.toProtocol p) i := by
  rw [product_message_honest w q hn hw d claim hc haddr i]
  change WordExt3.ringEquiv ((honestProduct q d (claim.toWordProtocol p)).coeff i.val) = _
  change WordExt3.ringEquiv.toRingHom ((honestProduct q d (claim.toWordProtocol p)).coeff i.val) = _
  rw [← Polynomial.coeff_map,honestProduct_toField]
  rfl

end CompStark.Keccak.GkrProver
