/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.TensorLift

/-! RMFE interpretation of compact native tensor assignments and their contractions. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators

/-- Evaluate the certified binary embedding of the constant word coordinate. -/
noncomputable def rmfeValue (s a : W) : W := (payloadWordPolynomial (embeddingRaw a.c0.val)).eval s

/-- RMFE evaluation preserves raw XOR addition of the assignment words. -/
theorem rmfeValue_add (s a b : W) : rmfeValue s (a+b) = rmfeValue s a+rmfeValue s b := by
  change (payloadWordPolynomial (embeddingRaw (a.c0.val ^^^ b.c0.val))).eval s = _
  simp only [embeddingRaw_xor,payloadWordPolynomial,UInt64.toBitVec_xor,
    BinaryField.toPoly_xor,Polynomial.map_add,Polynomial.eval_add]
  rfl

/-- RMFE evaluation is an additive map on raw assignment words. -/
noncomputable def rmfeValueHom (s : W) : W →+ W where
  toFun := rmfeValue s
  map_zero' := by
    have h := rmfeValue_add s 0 0
    rw [add_zero] at h
    exact (add_left_cancel ((add_zero (rmfeValue s 0)).trans h)).symm
  map_add' := rmfeValue_add s

/-- Evaluation of an RMFE product agrees with the product of its two lifted factors. -/
theorem rmfeProduct_eval (s : W) (a b : UInt64) :
    (payloadWordPolynomial (prepareRmfeProducts.mul a b)).eval s =
      rmfeValue s (lane a)*rmfeValue s (lane b) := by
  have hp : payloadWordPolynomial (prepareRmfeProducts.mul a b) =
      payloadWordPolynomial (embeddingRaw a)*payloadWordPolynomial (embeddingRaw b) := by
    simp only [payloadWordPolynomial,prepareRmfeProducts_mul,binaryProduct_poly,
      embeddingRaw_narrow,Polynomial.map_mul]
  rw [hp,Polynomial.eval_mul]
  rfl

/-- RMFE evaluation commutes with all four native selected-vertex assignments. -/
theorem rmfeValue_ternary (s : W) (values : Nat → W) (q : Fin 81) :
    rmfeValue s (ternaryValue (fun b => values b.val) q.val) =
      ternaryLift 4 (fun i => rmfeValue s (values i)) q.val := by
  rw [← ternaryLift_eq_value]
  exact (ternaryLift_map (rmfeValueHom s) 4 values q.val).symm

/-- A production tensor word is the exact lifted RMFE factor at its ternary assignment. -/
theorem mixedEmbeddings_rmfeValue (s : W) (state : Array UInt64) (groups base : Nat)
    (q : Fin 81) (j : Fin 1600) :
    rmfeValue s (lane (readUDWord (mixedEmbeddings state groups base)
      (1600*q.val+j.val).toUSize).toUInt64) =
      ternaryLift 4 (fun i => rmfeValue s
        (tensorVertices state groups base j ⟨i%16,Nat.mod_lt _ (by decide)⟩)) q.val := by
  rw [mixedEmbeddings_value]
  have hvertex : (fun b : Fin 16 =>
      tensorVertices state groups base j ⟨b.val%16,Nat.mod_lt _ (by decide)⟩) =
      tensorVertices state groups base j := by
    funext b
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt b.isLt)
  have h := rmfeValue_ternary s
    (fun i => tensorVertices state groups base j ⟨i%16,Nat.mod_lt _ (by decide)⟩) q
  rw [hvertex] at h
  exact h

/-- The sixteen RMFE-evaluated Boolean factors of one native tensor position. -/
noncomputable def tensorFactor (s : W) (state : Array UInt64) (groups base : Nat)
    (j : Fin 1600) (i : Nat) : W :=
  rmfeValue s (tensorVertices state groups base j ⟨i%16,Nat.mod_lt _ (by decide)⟩)

/-- A complete chi endpoint from native compact assignments, with degree-one terms at finite vertices. -/
noncomputable def mixedTensorEntry (s : W) (state : Array UInt64) (groups base : Nat)
    (a b c : Fin 1600) (kappa : W) (q : Fin 81) : W :=
  let value (j : Fin 1600) := rmfeValue s (lane
    (readUDWord (mixedEmbeddings state groups base) (1600*q.val+j.val).toUSize).toUInt64)
  if (ternaryPlan[q.val]!).2 = 81 then
    kappa*value a+(kappa+value b)*value c
  else value b*value c

/-- Native compact chi endpoints are the exact quadratic tensor of the lifted Boolean factors. -/
theorem mixedTensorEntry_eq (s : W) (state : Array UInt64) (groups base : Nat)
    (a b c : Fin 1600) (kappa : W) (q : Fin 81) :
    mixedTensorEntry s state groups base a b c kappa q =
      kappa*ternaryLinearLift 4 (tensorFactor s state groups base a) q.val+
      kappa*ternaryLinearLift 4 (tensorFactor s state groups base c) q.val+
      ternaryLift 4 (tensorFactor s state groups base b) q.val*
        ternaryLift 4 (tensorFactor s state groups base c) q.val := by
  unfold mixedTensorEntry
  simp only [mixedEmbeddings_rmfeValue,ternaryLinearLift_eq,ternaryPlan_finite]
  unfold tensorFactor
  split
  · ring
  · simp only [mul_zero,zero_add]

/-- Four production tensor contractions recover the exact chi expression at the sampled pack point. -/
theorem bindEarly_mixedTensor (s : W) (state : Array UInt64) (groups base : Nat)
    (a b c : Fin 1600) (kappa : W) (point : Array W) (hp : point.size = 4) :
    (bindEarly (Array.ofFn (mixedTensorEntry s state groups base a b c kappa)) point)[0]! =
      kappa*binaryInterpolate point.toList (tensorFactor s state groups base a) 0+
        (kappa+binaryInterpolate point.toList (tensorFactor s state groups base b) 0)*
          binaryInterpolate point.toList (tensorFactor s state groups base c) 0 := by
  rw [bindEarly_get _ point 1 (by rw [Array.size_ofFn,hp]; decide) 0 (by decide)]
  rw [← tensorInterpolate_chi]
  apply tensorInterpolate_congr
  intro i _ hi
  have hi81 : i < 81 := by
    simpa only [Array.length_toList,hp,Nat.mul_zero,Nat.zero_add,Nat.mul_one,Nat.reducePow] using hi
  rw [getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi81),Array.getElem_ofFn,
    mixedTensorEntry_eq]
  simp only [Array.length_toList,hp]

end CompStark.Keccak.GkrProver
