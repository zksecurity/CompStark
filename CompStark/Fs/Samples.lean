/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.Observations

/-! # Samples as challenges

A round reads its challenges off the samples of a duplex answer: `d` samples as an element of `𝕂`
(`extEquiv`), and a grinding sample and `d` samples as a pair in `F × 𝕂` (`powExtEquiv`). Both are
bijections, so uniform samples give uniform challenges.
-/

@[expose] public section
namespace CompStark.Fs
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop CompStark.RandomOracle
open Polynomial Fri.Spec OracleSpec OracleComp
open scoped ENNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### Uniform samples -/

/-- `d` samples as an element of `𝕂`, lowest coefficient first. -/
noncomputable def extEquiv : (Fin (Challenge.d EF) → F) ≃ 𝕂 :=
  (Equiv.arrowCongr (Equiv.refl _) (Equiv.refl F)).trans
    (CompPoly.Extension.Ext.equivFn (Challenge.params EF)).symm

/-- A grinding sample and `d` samples as a pair in `F × 𝕂`. -/
noncomputable def powExtEquiv : (Fin (Challenge.d EF + 1) → F) ≃ F × 𝕂 :=
  (Fin.consEquiv fun _ ↦ F).symm.trans
    (Equiv.prodCongr (Equiv.refl F) extEquiv)

theorem powExtEquiv_apply (x : Fin (Challenge.d EF + 1) → F) :
    powExtEquiv x = ((x 0), extEquiv fun j ↦ x j.succ) := rfl

theorem prEvent_congr_iff {α : Type} (mx : ProbComp α) {p q : α → Prop} (h : ∀ x, p x ↔ q x) :
    Pr{let x ← mx}[p x] = Pr{let x ← mx}[q x] := by
  have : p = q := funext fun x ↦ propext (h x)
  rw [this]

end CompStark.Fs
