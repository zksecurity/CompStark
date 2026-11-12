/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.OpeningAlgebra
public import CompStark.Keccak.Gkr.PhaseBoundaries

/-! # Boundary identities for committed-table openings -/

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
@[expose] public section
open Polynomial
open scoped BigOperators
namespace CompStark.Keccak.Gkr

/-- Enumerating positions is enumerating lanes and their little-endian slices. -/
theorem position_sum {A : Type*} [AddCommMonoid A] (f : Fin 1600 → A) :
    ∑ j, f j = ∑ l : Fin 25, ∑ z : Fin 64, f ⟨64*l.val+z.val,by omega⟩ := by
  have h := (finProdFinEquiv (m := 25) (n := 64)).sum_comp f
  rw [Fintype.sum_prod_type] at h
  exact h.symm

/-- The fourteen padded committed slots have zero input-opening weight. -/
theorem inputWeight_sum {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (c : Claim E p) (a : Fin 64 → Fin 64 → E) :
    (∑ slot : Fin 64, ∑ z : Fin 64, inputWeight c slot z * a slot z) =
      ∑ m : Fin 2, ∑ j : Fin 1600,
        (if m.val = 0 then 1-c.point (Fin.last p) else c.point (Fin.last p)) * c.weights j *
          a ⟨25*m.val+j.val/64,by omega⟩ ⟨j.val%64,by omega⟩ := by
  rw [Fin.sum_univ_add (a := 50) (b := 14)]
  have hh (i : Fin 14) : ¬(Fin.natAdd 50 i).val < 50 := by simp only [Fin.val_natAdd]; omega
  simp only [inputWeight, Fin.val_castAdd, hh, dite_false, zero_mul, Finset.sum_const_zero, add_zero]
  rw [Fin.sum_univ_add (a := 25) (b := 25), Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, ite_true, one_ne_zero, ite_false, Nat.mul_zero,
    Nat.zero_add, Nat.mul_one]
  simp_rw [position_sum]
  congr 1

/-- The Boolean input-opening sum equals the last weighted GKR claim. -/
theorem input_start_identity {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (t : Transcript E p) (r : Fin 10 → E) :
    ClaimHolds q (Fin.last 12) (nextClaim (t.layers (Fin.last 11))) ↔
      (nextClaim (t.layers (Fin.last 11))).value = residualSum (inputSummand q t) r 0 := by
  let c := nextClaim (t.layers (Fin.last 11))
  have hs : residualSum (inputSummand q t) r 0 =
      ∑ w : Fin 1024, ∑ z : Fin 64, inputTensorWeight c z w * inputTensorBits q c z w := by
    rw [residualSum_zero]
    apply Finset.sum_congr rfl
    intro w _
    rw [← inputPolynomial_eval]
    simp only [inputPolynomial, map_sum, map_mul, mle_eq_eval, mle_cubePoint, c]
  have ht : residualSum (inputSummand q t) r 0 =
      ∑ b : Fin (2^p), ∑ low : Fin 16,
        eqWeight (fun i => c.point i.castSucc) b.val * c.mu low *
          ∑ slot : Fin 64, ∑ z : Fin 64, inputWeight c slot z *
            ZMod.castHom (dvd_refl 2) E (q (packInstance low b) slot z) := by
    rw [hs]
    have he := cube_sum_split (a := 4) (b := 6)
      (f := fun w => ∑ z : Fin 64, inputTensorWeight c z w * inputTensorBits q c z w)
    change (∑ w : Fin 1024, ∑ z : Fin 64, inputTensorWeight c z w * inputTensorBits q c z w) = _ at he
    rw [he]
    have hmod (u : Fin 16) (v : Fin 64) : (u.val+16*v.val)%16 = u.val := by omega
    have hdiv (u : Fin 16) (v : Fin 64) : (u.val+16*v.val)/16 = v.val := by omega
    simp only [inputTensorWeight, inputTensorBits, show (2^4 : Nat) = 16 by decide, hmod, hdiv, Fin.eta,
      mle, Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2; ext low
      arg 2; ext slot
      rw [Finset.sum_comm]
    conv_lhs =>
      arg 2; ext low
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro low _
    apply Finset.sum_congr rfl
    intro slot _
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [ht]
  change c.value = _ ↔ c.value = _
  apply (congrArg (fun v : E => c.value = v) ?_).to_iff
  simp_rw [inputWeight_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro low _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.val_last, Nat.sub_self, segmentState, startState, eqWeight_last]
  ring

/-- A concatenated instance/slot evaluation is the nested slot and instance interpolation. -/
theorem mle_appendSlot {E : Type*} [CommRing E] {p : Nat}
    (a : Fin (2^(p+4)) → Fin 64 → E) (inst : Fin (p+4) → E) (slot : Fin 6 → E) :
    mle (fun b : Fin (2^(p+10)) =>
      a ⟨b.val%2^(p+4),Nat.mod_lt _ (by positivity)⟩
        ⟨b.val/2^(p+4),by
          apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
          simpa only [show p+10 = p+4+6 by omega, pow_add, show (2^6 : Nat)=64 by decide,
            Nat.mul_comm] using b.isLt⟩) (appendSlot inst slot) =
      mle (fun s => mle (fun b => a b s) inst) slot := by
  have h := mle_blocks (n := p+10) (a := p+4) (b := 6) (by omega) a (appendSlot inst slot)
  have hlo : (fun i : Fin (p+4) => appendSlot inst slot ⟨i.val,by omega⟩) = inst := by
    funext i; simp only [appendSlot, i.isLt, dite_true]
  have hhi : (fun i : Fin 6 => appendSlot inst slot ⟨p+4+i.val,by omega⟩) = slot := by
    funext i; simp only [appendSlot, show ¬p+4+i.val < p+4 by omega, dite_false, Nat.add_sub_cancel_left]
  rw [hlo,hhi] at h
  exact h

/-- Terminal PCS statements supply the exact committed word and bit-slice evaluations. -/
theorem terminal_opening_identities {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (q : Witness p) (t : Transcript E p) (h : TerminalRelation x q t) :
    t.openings.outputValue = mle (middleWord x q t) t.openings.outputPoint ∧
      ∀ z, t.openings.slices z =
        mle (fun slot => mle (fun b => ZMod.castHom (dvd_refl 2) E (q b slot z))
          (inputInstancePoint (nextClaim (t.layers (Fin.last 11))) t.openings.inputPoint))
          (inputSlotPoint t.openings.inputPoint) := by
  constructor
  · exact h.1.trans (mle_appendSlot (fun b slot => laneValue x (q b slot)) t.instancePoint t.openings.outputPoint)
  · intro z
    exact (h.2 z).trans (mle_appendSlot (fun b slot => ZMod.castHom (dvd_refl 2) E (q b slot z))
      (inputInstancePoint (nextClaim (t.layers (Fin.last 11))) t.openings.inputPoint)
      (inputSlotPoint t.openings.inputPoint))

end CompStark.Keccak.Gkr
