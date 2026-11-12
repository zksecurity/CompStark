/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.PhaseBoundaries

/-! # Transposed shifted evaluations at the beta batching boundary -/

set_option maxHeartbeats 600000
@[expose] public section
open Polynomial
open scoped BigOperators
namespace CompStark.Keccak.Gkr

/-- The inverse row shift for each of the three chi evaluations. -/
def inverseShift (k : Fin 3) : Nat := if k.val = 0 then 0 else 5-k.val

set_option maxRecDepth 8192 in
/-- A chi shift followed by its inverse returns the original position. -/
theorem along_inverseShift : ∀ (k : Fin 3) (j : Fin 1600),
    along (along j k.val) (inverseShift k) = j := by decide

/-- Every chi row shift permutes the 1600 positions. -/
noncomputable def alongEquiv (k : Fin 3) : Fin 1600 ≃ Fin 1600 :=
  Equiv.ofBijective (fun j => along j k.val) (by
    have hl : Function.LeftInverse (fun j : Fin 1600 => along j (inverseShift k))
        (fun j => along j k.val) := along_inverseShift k
    have hi := hl.injective
    exact ⟨hi,Finite.surjective_of_injective hi⟩)

/-- Pulling a chi shift through a weighted sum applies the inverse shift to the weights. -/
theorem shift_weight_pairing {E : Type*} [CommRing E]
    (z : Fin 11 → E) (a : Fin 1600 → E) (k : Fin 3) :
    ∑ j, eqWeight z j.val * a (along j k.val) =
      ∑ j, eqWeight z (along j (inverseShift k)).val * a j := by
  have h := (alongEquiv k).sum_comp
    (fun j => eqWeight z (along j (inverseShift k)).val * a j)
  simpa only [alongEquiv, Equiv.ofBijective_apply, along_inverseShift] using h

/-- A shifted position evaluation is the weighted sum of the real positions; padding contributes zero. -/
theorem shiftedEvaluation_sum {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (s : E) (r : Fin (p+1) → E) (z : Fin 11 → E) (k : Fin 3) :
    shiftedEvaluation q d s r z k.val = ∑ j : Fin 1600, eqWeight z j.val * linearAtPack q d s r (along j k.val) := by
  unfold shiftedEvaluation mle
  change (∑ j : Fin (1600+448), _) = _
  rw [Fin.sum_univ_add]
  have hh (j : Fin 448) : ¬1600+j.val < 1600 := by omega
  simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.isLt, dite_true, hh, dite_false,
    mul_zero, Finset.sum_const_zero, add_zero, Fin.eta]

/-- The characteristic-two coefficient map commutes with the linear Keccak layer. -/
theorem cast_linear {E : Type*} [CommRing E] [CharP E 2]
    (a : Fin 1600 → ZMod 2) (j : Fin 1600) :
    ZMod.castHom (dvd_refl 2) E (linear a j) =
      linear (fun i => ZMod.castHom (dvd_refl 2) E (a i)) j := by
  simp only [linear, map_add, map_sum]

/-- Packed evaluation and transposition give the same weighted preceding-layer claim. -/
theorem linearAtPack_pairing {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (s : E) (r : Fin (p+1) → E) (w : Fin 1600 → E) :
    (∑ j, w j * linearAtPack q d s r j) =
      ∑ m : Fin 2, ∑ b : Fin (2^p), ∑ i : Fin 16, ∑ j : Fin 1600,
        eqWeight r (b.val+2^p*m.val) * muAt s i * linearTranspose w j *
          ZMod.castHom (dvd_refl 2) E
            (segmentState q (packInstance i b) m (11-d.val) (by omega) j) := by
  simp only [linearAtPack, packedLinear, kemb_eval, cast_linear, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (eqWeight r (b.val+2^p*m.val) * muAt s i) *
        ∑ j, w j * linear (fun j => ZMod.castHom (dvd_refl 2) E
          (segmentState q (packInstance i b) m (11-d.val) (by omega) j)) j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [linearTranspose_adjoint, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The claim after beta is exactly the batching of the three honest shifted evaluations. -/
theorem beta_boundary_identity {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (t : LayerTranscript E p) :
    ClaimHolds q d.succ (nextClaim t) ↔
      polyEval t.evaluations t.beta = polyEval (fun k : Fin 3 =>
        shiftedEvaluation q d t.point t.packPoint t.positionPoint k.val) t.beta := by
  have he (k : Fin 3) := shift_weight_pairing t.positionPoint (linearAtPack q d t.point t.packPoint) k
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  norm_num [inverseShift] at h0 h1 h2
  have ht : 12-d.succ.val = 11-d.val := by simp only [Fin.val_succ]; omega
  simp only [ClaimHolds, nextClaim, ht]
  rw [← linearAtPack_pairing q d t.point t.packPoint]
  simp only [polyEval, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one, mul_one, shiftedEvaluation_sum, along_zero, add_mul, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum, mul_assoc, h1, h2]
  ring_nf

end CompStark.Keccak.Gkr
