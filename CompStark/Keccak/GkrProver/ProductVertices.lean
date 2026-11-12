/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.ProductEvaluation

/-! Shared Boolean-pack vertices of retained product rows and compact tensor assignments. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak BF64
open scoped BigOperators

/-- The scalar machine chi shift is exactly the natural position permutation. -/
theorem shiftU_eq_nat (j : Fin 1600) (k : Nat) (hk : k < 5) :
    shiftU j.val.toUSize k.toUSize = (shift j.val k).toUSize := by
  have hj := j.isLt
  have hs : shift j.val k < 1600 := (Gkr.along j k).isLt
  apply USize.toNat_inj.mp
  rw [usize_small _ (by omega)]
  simp only [shiftU,USize.toNat_add,USize.toNat_mul,USize.toNat_div,USize.toNat_mod,
    usize_small j.val (by omega),usize_small k (by omega),USize.reduceToNat]
  have hsize : 2^32 ≤ 2^System.Platform.numBits := USize.le_size
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  unfold shift
  rfl

/-- A retained chi payload evaluates on the exact Boolean vertices used by the compact tensor. -/
theorem productCell_eval_vertices (state : Array UInt64) (groups base : Nat) (b : Fin 16)
    (j : Fin 1600) (s : W) :
    (payloadWordPolynomial (productCell state groups.toUSize ((base+b.val)/4).toUSize
      (16*((base+b.val)%4)).toUInt64 prepareRmfeProducts j.val)).eval s =
      rmfeValue s (lane 65535)*rmfeValue s (tensorVertices state groups base j b) +
        (rmfeValue s (lane 65535)+rmfeValue s (tensorVertices state groups base (Gkr.along j 1) b))*
          rmfeValue s (tensorVertices state groups base (Gkr.along j 2) b) := by
  rw [productCell_payloadWordPolynomial]
  simp only [Polynomial.eval_add,Polynomial.eval_mul]
  have h1 : (1 : USize) = (1 : Nat).toUSize := rfl
  have h2 : (2 : USize) = (2 : Nat).toUSize := rfl
  rw [h1,h2,shiftU_eq_nat j 1 (by decide),shiftU_eq_nat j 2 (by decide),shift_eq,shift_eq]
  rfl

/-- Every retained segment-pack row evaluates to the complete weighted Boolean chi endpoints. -/
theorem productRow_eval_vertices (w : SlicedWitness) (d : Nat) (claim : Claim) (s : W)
    (m base : Nat) (b : Fin 16) :
    evaluatePackedLoop (productRow w d claim prepareRmfeProducts m (base+b.val))
      (CompStark.Sumcheck.prepare s) (productRow w d claim prepareRmfeProducts m (base+b.val)).size 0 =
      ∑ j : Fin 1600, claim.weights[j.val]! *
        (rmfeValue s (lane 65535)*rmfeValue s (tensorVertices w.layers[12*(m+1)-d]!
          (2^w.nLog/64) base j b) +
          (rmfeValue s (lane 65535)+rmfeValue s (tensorVertices w.layers[12*(m+1)-d]!
            (2^w.nLog/64) base (Gkr.along j 1) b))*
            rmfeValue s (tensorVertices w.layers[12*(m+1)-d]! (2^w.nLog/64) base (Gkr.along j 2) b)) := by
  rw [productRow_eval]
  apply Finset.sum_congr rfl
  intro j _
  rw [productCell_eval_vertices]

/-- Native RMFE evaluation is the protocol's weighted sum of the sixteen raw Boolean bits. -/
theorem rmfeValue_bits (s : W) (raw : UInt64) :
    rmfeValue s (lane raw) = ∑ i : Fin 16, Gkr.muAt s i *
      (if raw.toNat.testBit i.val then (1 : W) else 0) := by
  unfold rmfeValue payloadWordPolynomial
  simp only [lane]
  rw [embeddingRaw_poly]
  simp only [Embedding.kemb,LinearMap.coe_mk,AddHom.coe_mk,ZMod.castHom_self,
    Polynomial.map_id,Polynomial.map_sum,Polynomial.map_smul,
    Polynomial.eval_finsetSum,Polynomial.eval_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp only [map_one,map_zero,one_mul,zero_mul,mul_one,mul_zero,Gkr.muAt_eq_eval]

/-- The sixteen native instance weights sum to the protocol affine RMFE factor. -/
theorem instanceWeights_sum (s : W) : sum (instanceWeights s) = ∑ i : Fin 16, Gkr.muAt s i := by
  unfold sum
  rw [← Array.sum_eq_foldl,← Array.sum_toList]
  have hweights : instanceWeights s = Array.ofFn (fun i : Fin 16 => Gkr.muAt s i) := by
    apply Array.ext
    · simp only [instanceWeights,Array.size_ofFn]
    · intro i hi hj
      rw [← getElem!_pos _ i hi,← getElem!_pos _ i hj,
        instanceWeights_eq s ⟨i,by simpa only [Array.size_ofFn] using hj⟩]
      rw [getElem!_pos (Array.ofFn (fun i : Fin 16 => Gkr.muAt s i)) i hj,Array.getElem_ofFn]
  rw [hweights,Array.toList_ofFn,List.sum_ofFn]

/-- Summing the sixteen native instance weights gives the all-ones RMFE factor. -/
theorem kappa_eq_rmfeValue (s : W) : sum (instanceWeights s) = rmfeValue s (lane 65535) := by
  rw [instanceWeights_sum]
  unfold rmfeValue payloadWordPolynomial
  simp only [lane]
  rw [embeddingRaw_ones_poly]
  simp only [Embedding.kemb,LinearMap.coe_mk,AddHom.coe_mk,one_smul,
    Polynomial.map_sum,Polynomial.map_map]
  have hcast : (ZMod.castHom (dvd_refl 2) W).comp (ZMod.castHom (dvd_refl 2) (ZMod 2)) =
      ZMod.castHom (dvd_refl 2) W := by
    rw [ZMod.castHom_self,RingHom.comp_id]
  rw [hcast,Polynomial.eval_finsetSum]
  simp only [Gkr.muAt_eq_eval]

end CompStark.Keccak.GkrProver
