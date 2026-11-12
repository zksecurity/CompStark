/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Multilinear.GrandProduct
public import CompStark.Multilinear.Algebra.MaskedMle

/-! Finite-grid decisions for product-tree riders and the layer relations. -/

set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStark.Multilinear.GrandProduct
open CompStark.BinaryFields

/-- Restricted riders vanish on their finite mixed Boolean grid. -/
def RiderGrid {W : Type} (R : Riders W) (q : W) (mask : ℕ → Option E) : Prop :=
  ∀ i, ∀ j : Fin (2 ^ R.height i), mle (R.height i) (R.table q i)
    (maskedPoint (R.height i) mask (List.ofFn fun k : Fin (R.height i) => bit j.val k.val)) = 0

/-- Finite residual-grid vanishing has an executable decision. -/
instance {W : Type} (R : Riders W) (q : W) (mask : ℕ → Option E) :
    Decidable (RiderGrid R q mask) := by
  unfold RiderGrid
  infer_instance

/-- Finite-grid interpolation characterizes the universally restricted rider obligation. -/
theorem ridersRestricted_iff_grid {W : Type} (R : Riders W) (q : W)
    (mask : ℕ → Option E) : RidersRestricted R q mask ↔ RiderGrid R q mask := by
  unfold RidersRestricted RiderGrid rider
  apply forall_congr'
  intro i
  exact mle_masked_zero_iff (R.height i) (R.table q i) mask

/-- Zero rider tables are a finite check of their Boolean rows. -/
instance {W : Type} (R : Riders W) (q : W) : Decidable (RidersZero R q) := by
  unfold RidersZero
  infer_instance

/-- A zero rider table vanishes under every coordinate restriction. -/
theorem RidersZero.restricted {W : Type} {R : Riders W} {q : W}
    (zero : RidersZero R q) (mask : ℕ → Option E) : RidersRestricted R q mask := by
  intro i z length _
  exact (ridersRestricted_none_iff R q).mpr zero i z length
    (by intro k a absent _; cases absent)

/-- Restricted riders accept zero tables directly and otherwise decide the residual grid. -/
instance {W : Type} (R : Riders W) (q : W) (mask : ℕ → Option E) :
    Decidable (RidersRestricted R q mask) :=
  if zero : RidersZero R q then isTrue (zero.restricted mask)
  else decidable_of_iff (RiderGrid R q mask) (ridersRestricted_iff_grid R q mask).symm

/-- The layer's progressive rider state is decidable at every prefix. -/
instance {W : Type} (R : Riders W) (last : Bool) (ρ : ℕ) (χ u : List E) (q : W) :
    Decidable (riderState R last ρ χ u q) := by
  unfold riderState
  infer_instance

/-- Layer-claim truth is a finite collection of scalar equalities. -/
instance (μ m : ℕ) (leaves : Fin 3 → ℕ → E) (claim : Claim) :
    Decidable (claim.Holds μ m leaves) := by
  unfold Claim.Holds
  infer_instance

/-- The normalized round relation is decidable when the witness shape is. -/
instance {W : Type} (R : Riders W) [DecidablePred R.Fits] (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (point : List E)
    (lam current : E) (χ : List E) (active : Bool) (q : W) :
    Decidable (roundRelation R μ m ρ leaves last point lam current χ active q) := by
  unfold roundRelation
  infer_instance

/-- The interpolation relation checks the finite unsampled child grid and restricted riders. -/
instance {W : Type} (R : Riders W) [DecidablePred R.Fits] (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (χ u : List E)
    (children : Fin 3 → Fin (2 ^ ρ) → E) (active : Bool) (q : W) :
    Decidable (interpolationRelation R μ m ρ leaves last χ u children active q) := by
  unfold interpolationRelation
  infer_instance

/-- The entering layer relation checks full riders and the three claims. -/
instance {W : Type} (R : Riders W) [DecidablePred R.Fits] (μ m : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (claim : Claim) (active : Bool) (q : W) :
    Decidable (layerRelation R μ m leaves claim active q) := by
  unfold layerRelation
  infer_instance

end CompStark.Multilinear.GrandProduct
