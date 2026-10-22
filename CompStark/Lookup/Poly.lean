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

* `ExtExpr.colsBelow`: the columns an expression reads; the LogUp constraints read the lookups'
  columns and the permutation trace's (`colsBelow_logUpConstraints`), and evaluation commutes with
  maps on the environments there (`ExtExpr.eval_hom`).
* `extPoly`: a LogUp constraint over the polynomials `T` of the trace, `Tp` of the preprocessed
  trace and `P` of the periodic columns, mapped to `𝕂[X]`, the polynomials `R` of the
  permutation trace's columns, and the challenges and the terminal as constants; its degree is at
  most `degBound` (`natDegree_extPoly`), and on the trace domain it takes the constraint's value on
  the rows (`eval_extPoly_root`).
-/

@[expose] public section
namespace CompStark.Lookup
open CompStark.Stark Polynomial

variable {F : Type}
/-- Every base expression reads columns below `w`, `wNext`, `pw` and `pwNext` (`Expr.colsBelow`)
and every permutation column is below `pmw`. -/
def ExtExpr.colsBelow (w wNext pw pwNext pmw : Nat) : ExtExpr F → Bool
  | .base e => e.colsBelow w wNext pw pwNext
  | .perm c | .permNext c => c < pmw
  | .challenge _ | .terminal => true
  | .add a b | .sub a b | .mul a b =>
    a.colsBelow w wNext pw pwNext pmw && b.colsBelow w wNext pw pwNext pmw

/-- Evaluation commutes with a map that respects `+`, `-` and `*`, for expressions reading columns
below the widths (`ExtExpr.colsBelow`) of environments that agree there. -/
theorem ExtExpr.eval_hom {R S : Type*} [Add R] [Sub R] [Mul R] [Add S] [Sub S] [Mul S]
    (f : R → S) (hadd : ∀ a b, f (a + b) = f a + f b) (hsub : ∀ a b, f (a - b) = f a - f b)
    (hmul : ∀ a b, f (a * b) = f a * f b) (w wNext pw pwNext pmw : Nat) (env : Expr.Env F R)
    (env' : Expr.Env F S) (aux : ExtExpr.Env R) (aux' : ExtExpr.Env S)
    (hbase : ∀ e : Expr F, e.colsBelow w wNext pw pwNext = true → f (e.eval env) = e.eval env')
    (hperm : ∀ c < pmw, f (aux.perm c) = aux'.perm c)
    (hnext : ∀ c < pmw, f (aux.permNext c) = aux'.permNext c)
    (hch : ∀ j, f (aux.challenge j) = aux'.challenge j) (hterm : f aux.terminal = aux'.terminal) :
    ∀ g : ExtExpr F, g.colsBelow w wNext pw pwNext pmw = true →
      f (g.eval env aux) = g.eval env' aux'
  | .base e, h => hbase e h
  | .perm c, h => hperm c (of_decide_eq_true h)
  | .permNext c, h => hnext c (of_decide_eq_true h)
  | .challenge j, _ => hch j
  | .terminal, _ => hterm
  | .add a b, h => by
    simp only [ExtExpr.colsBelow, Bool.and_eq_true] at h
    simp only [ExtExpr.eval]
    rw [hadd, ExtExpr.eval_hom f hadd hsub hmul w wNext pw pwNext pmw env env' aux aux' hbase
      hperm hnext hch hterm a h.1, ExtExpr.eval_hom f hadd hsub hmul w wNext pw pwNext pmw env env'
      aux aux' hbase hperm hnext hch hterm b h.2]
  | .sub a b, h => by
    simp only [ExtExpr.colsBelow, Bool.and_eq_true] at h
    simp only [ExtExpr.eval]
    rw [hsub, ExtExpr.eval_hom f hadd hsub hmul w wNext pw pwNext pmw env env' aux aux' hbase
      hperm hnext hch hterm a h.1, ExtExpr.eval_hom f hadd hsub hmul w wNext pw pwNext pmw env env'
      aux aux' hbase hperm hnext hch hterm b h.2]
  | .mul a b, h => by
    simp only [ExtExpr.colsBelow, Bool.and_eq_true] at h
    simp only [ExtExpr.eval]
    rw [hmul, ExtExpr.eval_hom f hadd hsub hmul w wNext pw pwNext pmw env env' aux aux' hbase
      hperm hnext hch hterm a h.1, ExtExpr.eval_hom f hadd hsub hmul w wNext pw pwNext pmw env env'
      aux aux' hbase hperm hnext hch hterm b h.2]

/-! ### The LogUp constraints read the lookups' columns -/

section Cols
variable {w wNext pw pwNext pmw : Nat}

theorem colsBelow_denominator [Zero F] (a b : ExtExpr F) (t : List (Expr F))
    (ha : a.colsBelow w wNext pw pwNext pmw) (hb : b.colsBelow w wNext pw pwNext pmw)
    (ht : ∀ e ∈ t, e.colsBelow w wNext pw pwNext) :
    (denominator a b t).colsBelow w wNext pw pwNext pmw := by
  unfold denominator
  cases t with
  | nil =>
    show (a.colsBelow w wNext pw pwNext pmw && (ExtExpr.base (.const 0)).colsBelow w wNext pw
      pwNext pmw) = true
    rw [ha]; rfl
  | cons x xs =>
    show (a.colsBelow w wNext pw pwNext pmw && _) = true
    rw [ha, Bool.true_and]
    suffices h : ∀ (acc : ExtExpr F), acc.colsBelow w wNext pw pwNext pmw →
        (xs.foldl (fun acc y ↦ .base y + acc * b) acc).colsBelow w wNext pw pwNext pmw from
      h _ (ht x List.mem_cons_self)
    intro acc hacc
    induction xs generalizing acc with
    | nil => exact hacc
    | cons y ys ih =>
      rw [List.foldl_cons]
      refine ih (fun e he ↦ ht e (by
        rcases List.mem_cons.mp he with rfl | he
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))) _ ?_
      show ((ExtExpr.base y).colsBelow w wNext pw pwNext pmw &&
        (acc.colsBelow w wNext pw pwNext pmw && b.colsBelow w wNext pw pwNext pmw)) = true
      rw [hacc, hb]
      simpa only [ExtExpr.colsBelow, Bool.and_true] using
        ht y (List.mem_cons_of_mem _ List.mem_cons_self)

theorem colsBelow_foldFractions [Zero F] [One F] (ps : List (ExtExpr F × ExtExpr F))
    (h : ∀ p ∈ ps, p.1.colsBelow w wNext pw pwNext pmw ∧ p.2.colsBelow w wNext pw pwNext pmw) :
    (foldFractions ps).1.colsBelow w wNext pw pwNext pmw ∧
      (foldFractions ps).2.colsBelow w wNext pw pwNext pmw := by
  cases ps with
  | nil => simp only [foldFractions, ExtExpr.const, ExtExpr.colsBelow, Expr.colsBelow, and_self]
  | cons p ps =>
    obtain ⟨d, m⟩ := p
    simp only [foldFractions]
    suffices hs : ∀ (acc : ExtExpr F × ExtExpr F), acc.1.colsBelow w wNext pw pwNext pmw →
        acc.2.colsBelow w wNext pw pwNext pmw →
        (ps.foldl (fun (v, u) (d, m) ↦ (v * d + m * u, u * d)) acc).1.colsBelow w wNext pw pwNext
          pmw ∧
        (ps.foldl (fun (v, u) (d, m) ↦ (v * d + m * u, u * d)) acc).2.colsBelow w wNext pw pwNext
          pmw from
      hs _ (h _ List.mem_cons_self).2 (h _ List.mem_cons_self).1
    intro acc h1 h2
    induction ps generalizing acc with
    | nil => exact ⟨h1, h2⟩
    | cons q qs ih =>
      rw [List.foldl_cons]
      have hq := h q (List.mem_cons_of_mem _ List.mem_cons_self)
      refine ih (fun p hp ↦ h p (by
        rcases List.mem_cons.mp hp with rfl | hp
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))) _ ?_ ?_
      · show ((acc.1.colsBelow w wNext pw pwNext pmw && q.1.colsBelow w wNext pw pwNext pmw) &&
          (q.2.colsBelow w wNext pw pwNext pmw && acc.2.colsBelow w wNext pw pwNext pmw)) = true
        rw [h1, h2, hq.1, hq.2]; rfl
      · show (acc.2.colsBelow w wNext pw pwNext pmw && q.1.colsBelow w wNext pw pwNext pmw) = true
        rw [h2, hq.1]; rfl

theorem colsBelow_rowSum [Zero F] (k : Nat) (hk : k < pmw) :
    (rowSum (F := F) k).colsBelow w wNext pw pwNext pmw := by
  unfold rowSum
  suffices h : ∀ (l : List Nat) (acc : ExtExpr F), (∀ c ∈ l, c + 1 < pmw) →
      acc.colsBelow w wNext pw pwNext pmw →
      (l.foldl (fun s c ↦ s + .perm (c + 1)) acc).colsBelow w wNext pw pwNext pmw from
    h (List.range k) (ExtExpr.const (0 : F)) (fun c hc ↦ by have := List.mem_range.mp hc; omega)
      rfl
  intro l
  induction l with
  | nil => intro _ _ h; exact h
  | cons c l ih =>
    intro acc hl hacc
    rw [List.foldl_cons]
    refine ih _ (fun c' hc' ↦ hl c' (List.mem_cons_of_mem _ hc')) ?_
    show (acc.colsBelow w wNext pw pwNext pmw && decide (c + 1 < pmw)) = true
    rw [hacc, decide_eq_true (hl c List.mem_cons_self)]; rfl

/-- The LogUp constraints of lookups reading the columns below the widths read them, and the
permutation trace's accumulator and fraction columns. -/
theorem colsBelow_logUpConstraints [Zero F] [One F] (ls : List (Lookup F))
    (hls : ∀ l ∈ ls, ∀ x ∈ l.tuples, (∀ e ∈ x.1, e.colsBelow w wNext pw pwNext) ∧
      x.2.colsBelow w wNext pw pwNext) :
    ∀ g ∈ logUpConstraints ls, g.colsBelow w wNext pw pwNext (ls.length + 1) := by
  intro g hg
  unfold logUpConstraints at hg
  split at hg
  · exact absurd hg List.not_mem_nil
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨⟨l, c⟩, hlc, rfl⟩ := List.mem_map.mp hg
    have hc : c < ls.length := by have := (List.mem_zipIdx hlc).2.1; omega
    have hl : l ∈ ls := by
      have := (List.mem_zipIdx hlc).2.2
      rw [this]; exact List.getElem_mem _
    dsimp only
    unfold fractionPin
    have hf := colsBelow_foldFractions (w := w) (wNext := wNext) (pw := pw) (pwNext := pwNext)
      (pmw := ls.length + 1) (l.tuples.map fun (t, m) ↦
      (denominator (.challenge (2 * c)) (.challenge (2 * c + 1)) t, .base m)) fun p hp ↦ by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
        obtain ⟨t, m⟩ := x
        exact ⟨colsBelow_denominator _ _ _ rfl rfl (hls l hl _ hx).1, (hls l hl _ hx).2⟩
    show (((foldFractions _).2.colsBelow w wNext pw pwNext (ls.length + 1) &&
      decide (c + 1 < ls.length + 1)) && (foldFractions _).1.colsBelow w wNext pw pwNext
        (ls.length + 1)) = true
    rw [hf.1, hf.2, decide_eq_true (by omega)]; rfl
  · have hr := colsBelow_rowSum (F := F) (w := w) (wNext := wNext) (pw := pw) (pwNext := pwNext)
      ls.length (Nat.lt_succ_self _)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · show (true && decide (0 < ls.length + 1)) = true
      rw [decide_eq_true (Nat.succ_pos _)]; rfl
    · show (true && ((decide (0 < ls.length + 1) && decide (0 < ls.length + 1)) &&
        (rowSum ls.length).colsBelow w wNext pw pwNext (ls.length + 1))) = true
      rw [decide_eq_true (Nat.succ_pos _), hr]; rfl
    · show (true && ((true && decide (0 < ls.length + 1)) &&
        (rowSum ls.length).colsBelow w wNext pw pwNext (ls.length + 1))) = true
      rw [decide_eq_true (Nat.succ_pos _), hr]; rfl

end Cols

variable [BaseField F] {EF : Type} [Challenge F EF]
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
