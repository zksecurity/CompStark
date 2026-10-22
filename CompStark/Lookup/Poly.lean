/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Complete.LogUp
public import CompStark.Stark.Constraints

/-! # The LogUp constraints as polynomials

The LogUp constraints over the polynomials of the traces, as `Stark/Constraints.lean` treats an
AIR's constraints, over the spec field `𝕂` of the challenge field:

* The columns an expression reads (`ExtExpr.colsBelow`, `CompStark/Lookup/LogUp.lean`): the LogUp
  constraints read the lookups' columns and the permutation trace's
  (`colsBelow_logUpConstraints`), and evaluation commutes with maps on the environments there
  (`ExtExpr.eval_hom`).
* `extPoly`: a LogUp constraint over the polynomials `T` of the trace, `Tp` of the preprocessed
  trace and `P` of the periodic columns, mapped to `𝕂[X]`, the polynomials `R` of the
  permutation trace's columns, and the challenges and the terminal as constants; its degree is at
  most `degBound` (`natDegree_extPoly`), and on the trace domain it takes the constraint's value on
  the rows (`eval_extPoly_root`).
-/

@[expose] public section
namespace CompStark.Lookup
open CompStark.Stark Polynomial

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]
local notation "K" => F
local notation "E" => Challenge.Spec EF

/-- The degree of an expression over polynomials is at most `degBound`. -/
theorem ExtExpr.natDegree_eval (n : Nat) (pd : Nat → Nat) (env : Expr.Env F E[X])
    (aux : ExtExpr.Env E[X])
    (hbase : ∀ e : Expr F, (e.eval env).natDegree ≤ e.degBound n pd)
    (hperm : ∀ c, (aux.perm c).natDegree ≤ n - 1) (hnext : ∀ c, (aux.permNext c).natDegree ≤ n - 1)
    (hch : ∀ j, (aux.challenge j).natDegree = 0) (hterm : aux.terminal.natDegree = 0) :
    ∀ g : ExtExpr F, (g.eval env aux).natDegree ≤ g.degBound n pd
  | .base e => hbase e
  | .perm c => hperm c
  | .permNext c => hnext c
  | .challenge j => (hch j).le
  | .terminal => hterm.le
  | .add a b => (natDegree_add_le _ _).trans (max_le_max
      (ExtExpr.natDegree_eval n pd env aux hbase hperm hnext hch hterm a)
      (ExtExpr.natDegree_eval n pd env aux hbase hperm hnext hch hterm b))
  | .sub a b => (natDegree_sub_le _ _).trans (max_le_max
      (ExtExpr.natDegree_eval n pd env aux hbase hperm hnext hch hterm a)
      (ExtExpr.natDegree_eval n pd env aux hbase hperm hnext hch hterm b))
  | .mul a b => natDegree_mul_le.trans (Nat.add_le_add
      (ExtExpr.natDegree_eval n pd env aux hbase hperm hnext hch hterm a)
      (ExtExpr.natDegree_eval n pd env aux hbase hperm hnext hch hterm b))

/-! ### The LogUp constraints as polynomials -/

/-- The permutation trace's values over polynomials: its column polynomials `R`, shifted by `ω`
for the next row, the challenges `chs` and the terminal as constants. -/
noncomputable def polyAux (w : F) (R : Nat → E[X]) (chs : List E) (terminal : E) :
    ExtExpr.Env E[X] :=
  ⟨R, fun c ↦ (R c).comp (C (algebraMap K E w) * X), fun j ↦ C (chs.getD j 0), C terminal⟩

/-- The constraint `g` over the polynomials `T`, `Tp`, `P` of the traces and periodic columns,
mapped to `𝕂[X]`, and `R` of the permutation trace. -/
noncomputable def extPoly (n : Nat) (w : F) (T Tp P : Nat → F[X]) (pis : List F) (R : Nat → E[X])
    (chs : List E) (terminal : E) (g : ExtExpr F) : E[X] :=
  g.eval ((polyEnv n w T Tp P pis).map (Polynomial.map (algebraMap K E)))
    (polyAux w R chs terminal)

/-- A LogUp constraint polynomial has degree at most `degBound`. -/
theorem natDegree_extPoly (n : Nat) (w : F) (T Tp P : Nat → F[X]) (pd : Nat → Nat) (pis : List F)
    (R : Nat → E[X]) (chs : List E) (terminal : E) (g : ExtExpr F)
    (hT : ∀ j, (T j).natDegree ≤ n - 1) (hTp : ∀ j, (Tp j).natDegree ≤ n - 1)
    (hP : ∀ j, (P j).natDegree ≤ pd j) (hR : ∀ c, (R c).natDegree ≤ n - 1) :
    (extPoly n w T Tp P pis R chs terminal g).natDegree ≤ g.degBound n pd := by
  refine ExtExpr.natDegree_eval n pd _ _ (fun e ↦ ?_) hR (fun c ↦ ?_) (fun _ ↦ natDegree_C _)
    (natDegree_C _) g
  · have := Expr.eval_map (mapRingHom (algebraMap K E)) (polyEnv n w T Tp P pis) e
    rw [coe_mapRingHom] at this
    rw [this]
    exact natDegree_map_le.trans (natDegree_constraintPoly n w T Tp P pd pis e hT hTp hP)
  · refine natDegree_comp_le.trans ?_
    have h1 : (C (algebraMap K E w) * X : E[X]).natDegree ≤ 1 :=
      (natDegree_C_mul_le _ _).trans natDegree_X_le
    calc (R c).natDegree * (C (algebraMap K E w) * X).natDegree ≤ (R c).natDegree * 1 :=
          Nat.mul_le_mul_left _ h1
      _ ≤ n - 1 := by rw [Nat.mul_one]; exact hR c

/-- On the trace domain, a LogUp constraint polynomial takes the constraint's value on the
trace's rows and the permutation polynomials' values there. -/
theorem eval_extPoly_root (A : Air F) (logN : Nat) (h : logN ≤ twoAdicity F) (trace : Array F)
    (pis : List F) (T Tp P : Nat → F[X]) (hT : TraceOn logN A.width trace T)
    (hTp : TraceOn logN A.preprocessedWidth A.preprocessed Tp) (hP : PeriodicOn A logN P)
    (R : Nat → E[X]) (chs : List E) (terminal : E) (pmw : Nat) (g : ExtExpr F)
    (hg : g.colsBelow A.width A.mainNextWidth A.preprocessedWidth A.preprocessedNextWidth pmw)
    (i : Nat) (hi : i < 2 ^ logN) :
    (extPoly (2 ^ logN) (twoAdicGen logN) T Tp P pis R chs terminal g).eval
        (algebraMap K E (twoAdicGen logN ^ i)) =
      g.eval ((A.traceRow logN trace pis i).map (algebraMap K E))
        ⟨fun c ↦ (R c).eval (algebraMap K E (twoAdicGen logN ^ i)),
          fun c ↦ (R c).eval (algebraMap K E (twoAdicGen logN ^ (i + 1))),
          (chs.getD · 0), terminal⟩ := by
  refine ExtExpr.eval_hom (eval (algebraMap K E (twoAdicGen logN ^ i))) (fun _ _ ↦ eval_add)
    (fun a b ↦ eval_sub a b _) (fun _ _ ↦ eval_mul) A.width A.mainNextWidth A.preprocessedWidth
    A.preprocessedNextWidth pmw _ _ _ _ (fun e he ↦ ?_) (fun _ _ ↦ rfl) (fun c _ ↦ ?_)
    (fun _ ↦ eval_C) eval_C g hg
  · have := Expr.eval_map (mapRingHom (algebraMap K E)) (polyEnv (2 ^ logN) (twoAdicGen logN) T Tp
      P pis) e
    rw [coe_mapRingHom] at this
    rw [this, eval_map_apply, Expr.eval_map (algebraMap K E)]
    exact congrArg (algebraMap K E) (eval_constraintPoly_root A logN h trace pis T Tp P hT hTp hP
      e he i hi)
  · simp only [polyAux]
    rw [eval_comp, eval_mul, eval_C, eval_X, ← map_mul, ← pow_succ']

end CompStark.Lookup
