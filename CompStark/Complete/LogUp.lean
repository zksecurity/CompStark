/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Batch.Prover
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Field.Basic

/-! # The honest permutation trace satisfies the LogUp constraints

The algebra behind the LogUp gadget's completeness, row by row:

* A fraction pin `U f - V` vanishes on the honest fraction `f = ∑ m / d`, `(V, U)` the fractions
  with their denominators cleared, when no tuple of non-zero multiplicity has a zero denominator
  (`foldValues_mul_sum`).
* The honest permutation trace's row `i` holds the accumulator `∑_{r < i}` of the rows' fractions
  and the row's fractions, its terminal the sum of all of them (`getD_permutationTrace`).
-/

@[expose] public section
namespace CompStark.Lookup
open CompStark.Stark

end CompStark.Lookup

namespace CompStark.Stark
variable {F : Type}

/-- An environment with `f` applied to every value. -/
def Expr.Env.map {R S : Type*} (f : R → S) (env : Expr.Env F R) :
    Expr.Env F S where
  cur c := f (env.cur c)
  next c := f (env.next c)
  prepCur c := f (env.prepCur c)
  prepNext c := f (env.prepNext c)
  periodic j := f (env.periodic j)
  pub j := f (env.pub j)
  const c := f (env.const c)
  isFirstRow := f env.isFirstRow
  isLastRow := f env.isLastRow
  isTransition := f env.isTransition

/-- Evaluation commutes with ring homomorphisms applied to every value of the environment. -/
theorem Expr.eval_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (env : Expr.Env F R) : ∀ e : Expr F, e.eval (env.map f) = f (e.eval env)
  | .cur _ | .next _ | .prepCur _ | .prepNext _ | .periodic _ | .pub _ | .const _ | .isFirstRow
  | .isLastRow | .isTransition => rfl
  | .add a b => by
    simp only [Expr.eval]; rw [Expr.eval_map f env a, Expr.eval_map f env b, map_add]
  | .sub a b => by
    simp only [Expr.eval]; rw [Expr.eval_map f env a, Expr.eval_map f env b, map_sub]
  | .mul a b => by
    simp only [Expr.eval]; rw [Expr.eval_map f env a, Expr.eval_map f env b, map_mul]

end CompStark.Stark

namespace CompStark.Lookup
open CompStark.Stark

/-! ### Fractions with their denominators cleared -/

section Fractions
variable {R : Type*} [CommRing R]

/-- One step of clearing denominators: `v / u + m / d = (v d + m u) / (u d)`. -/
def fracStep (x : R × R) (y : R × R) : R × R := (x.1 * y.1 + y.2 * x.2, x.2 * y.1)

/-- The numerator and the denominator `(V, U)` of `∑ᵢ mᵢ / dᵢ` over the pairs `(dᵢ, mᵢ)`
(`foldFractions` evaluated). -/
def foldValues : List (R × R) → R × R
  | [] => (0, 1)
  | (d, m) :: rest => rest.foldl fracStep (m, d)

section Field
variable {R : Type*} [Field R]

/-- Clearing denominators keeps `U · ∑ m / d = V` when no pair of non-zero multiplicity has a zero
denominator. -/
theorem foldl_fracStep (ts : List (R × R)) (hts : ∀ x ∈ ts, x.2 ≠ 0 → x.1 ≠ 0) (v u s : R)
    (h : u * s = v) :
    (ts.foldl fracStep (v, u)).2 * (s + (ts.map fun x ↦ x.2 * x.1⁻¹).sum) =
      (ts.foldl fracStep (v, u)).1 := by
  induction ts generalizing v u s with
  | nil => simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero, h]
  | cons y ts ih =>
    rw [List.foldl_cons, List.map_cons, List.sum_cons, ← add_assoc]
    refine ih (fun x hx ↦ hts x (List.mem_cons_of_mem _ hx)) _ _ _ ?_
    show u * y.1 * (s + y.2 * y.1⁻¹) = v * y.1 + y.2 * u
    by_cases hm : y.2 = 0
    · rw [hm, zero_mul, add_zero, zero_mul, add_zero, mul_comm u, mul_assoc, h, mul_comm]
    · have hd := hts y List.mem_cons_self hm
      rw [← h]
      field_simp

/-- `U · ∑ m / d = V` for the cleared numerator and denominator, when no pair of non-zero
multiplicity has a zero denominator. -/
theorem foldValues_mul_sum (ts : List (R × R)) (hts : ∀ x ∈ ts, x.2 ≠ 0 → x.1 ≠ 0) :
    (foldValues ts).2 * (ts.map fun x ↦ x.2 * x.1⁻¹).sum = (foldValues ts).1 := by
  cases ts with
  | nil => simp only [foldValues, List.map_nil, List.sum_nil, mul_zero]
  | cons y ts =>
    obtain ⟨d, m⟩ := y
    simp only [foldValues, List.map_cons, List.sum_cons]
    refine foldl_fracStep ts (fun x hx ↦ hts x (List.mem_cons_of_mem _ hx)) m d _ ?_
    by_cases hm : m = 0
    · rw [hm, zero_mul, mul_zero]
    · rw [mul_comm m, ← mul_assoc, mul_inv_cancel₀ (hts _ List.mem_cons_self hm), one_mul]

end Field

end Fractions

/-! ### Balanced sums -/

section Balance
variable {κ R : Type*} [DecidableEq κ] [CommRing R]

theorem sum_map_filter_split {α : Type*} (L : List α) (p : α → Prop) [DecidablePred p]
    (f : α → R) :
    (L.map f).sum = ((L.filter (p ·)).map f).sum + ((L.filter (¬p ·)).map f).sum := by
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil, List.filter_nil, add_zero]
  | cons x L ih =>
    rw [List.filter_cons, List.filter_cons, List.map_cons, List.sum_cons, ih]
    by_cases hx : p x
    · simp only [hx, decide_true, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.sum_cons]
      ring
    · simp only [hx, decide_false, Bool.false_eq_true, ↓reduceIte, not_false_eq_true, decide_true,
        List.map_cons, List.sum_cons]
      ring

/-- A sum of values weighted by a function of their keys vanishes when the values of every key
sum to zero. -/
theorem sum_weighted_eq_zero (D : κ → R) : ∀ (n : Nat) (L : List (κ × R)), L.length ≤ n →
    (∀ k, ((L.filter (·.1 = k)).map (·.2)).sum = 0) → (L.map fun x ↦ D x.1 * x.2).sum = 0
  | _, [], _, _ => rfl
  | 0, _ :: _, h, _ => absurd h (by simp only [List.length_cons]; omega)
  | n + 1, x :: L, hl, hb => by
    rw [sum_map_filter_split (x :: L) (·.1 = x.1)]
    have h1 : (((x :: L).filter (·.1 = x.1)).map fun y ↦ D y.1 * y.2).sum = 0 := by
      have : ((x :: L).filter (·.1 = x.1)).map (fun y ↦ D y.1 * y.2) =
          (((x :: L).filter (·.1 = x.1)).map (·.2)).map (D x.1 * ·) := by
        rw [List.map_map]
        refine List.map_congr_left fun y hy ↦ ?_
        have := (List.mem_filter.mp hy).2
        simp only [decide_eq_true_eq] at this
        simp only [Function.comp_apply, this]
      rw [this, List.sum_map_mul_left, List.map_id', hb x.1, mul_zero]
    rw [h1, zero_add]
    refine sum_weighted_eq_zero D n _ ?_ fun k ↦ ?_
    · have : ((x :: L).filter (¬·.1 = x.1)).length ≤ L.length := by
        simp only [List.filter_cons, not_true_eq_false, decide_false, Bool.false_eq_true,
          ↓reduceIte]
        exact List.length_filter_le _ _
      simp only [List.length_cons] at hl
      omega
    · by_cases hk : k = x.1
      · subst hk
        rw [List.filter_filter]
        have : ((x :: L).filter fun y ↦ decide (y.1 = x.1) && decide (¬y.1 = x.1)) = [] :=
          List.filter_eq_nil_iff.mpr fun y _ ↦ by
            by_cases h : y.1 = x.1 <;> simp only [h, decide_true, decide_false, not_true_eq_false,
              not_false_eq_true, Bool.and_false, Bool.false_and, Bool.false_eq_true,
              not_false_eq_true]
        rw [this]; rfl
      · rw [List.filter_filter]
        have : ((x :: L).filter fun y ↦ decide (y.1 = k) && decide (¬y.1 = x.1)) =
            (x :: L).filter (·.1 = k) :=
          List.filter_congr fun y _ ↦ by
            by_cases h : y.1 = k
            · simp only [h, hk, decide_true, not_false_eq_true, Bool.and_self]
            · simp only [h, decide_false, Bool.false_and]
        rw [this, hb k]

end Balance

/-! ### The LogUp constraints evaluated -/

section Eval
variable {F : Type} {K : Type*} [CommRing K]

/-- `∑ⱼ tⱼ bᵏ⁻¹⁻ʲ` by Horner's rule from the first of the values `t`, `0` without values. -/
def hornerFirst (b : K) : List K → K
  | [] => 0
  | x :: xs => xs.foldl (fun acc y ↦ y + acc * b) x

theorem ExtExpr.eval_hAdd (env : Expr.Env F K) (aux : ExtExpr.Env K) (a b : ExtExpr F) :
    (a + b).eval env aux = a.eval env aux + b.eval env aux := rfl
theorem ExtExpr.eval_hSub (env : Expr.Env F K) (aux : ExtExpr.Env K) (a b : ExtExpr F) :
    (a - b).eval env aux = a.eval env aux - b.eval env aux := rfl
theorem ExtExpr.eval_hMul (env : Expr.Env F K) (aux : ExtExpr.Env K) (a b : ExtExpr F) :
    (a * b).eval env aux = a.eval env aux * b.eval env aux := rfl

variable [Zero F]

theorem eval_denominator (env : Expr.Env F K) (aux : ExtExpr.Env K) (a b : ExtExpr F)
    (t : List (Expr F)) (h0 : env.const 0 = 0) :
    (denominator a b t).eval env aux =
      a.eval env aux - hornerFirst (b.eval env aux) (t.map (·.eval env)) := by
  unfold denominator
  cases t with
  | nil =>
    simp only [ExtExpr.eval_hSub, ExtExpr.const, ExtExpr.eval, Expr.eval, h0, List.map_nil,
      hornerFirst]
  | cons x xs =>
    simp only [ExtExpr.eval_hSub, List.map_cons, hornerFirst]
    congr 1
    suffices h : ∀ (acc : ExtExpr F), (xs.foldl (fun acc y ↦ .base y + acc * b) acc).eval env aux
        = (xs.map (·.eval env)).foldl (fun acc y ↦ y + acc * b.eval env aux) (acc.eval env aux) by
      exact h _
    induction xs with
    | nil => intro _; rfl
    | cons y ys ih => intro acc; rw [List.foldl_cons, ih]; rfl

theorem eval_foldFractions [One F] (env : Expr.Env F K) (aux : ExtExpr.Env K)
    (ps : List (ExtExpr F × ExtExpr F)) (h0 : env.const 0 = 0) (h1 : env.const 1 = 1) :
    ((foldFractions ps).1.eval env aux, (foldFractions ps).2.eval env aux) =
      foldValues (ps.map fun p ↦ (p.1.eval env aux, p.2.eval env aux)) := by
  cases ps with
  | nil => simp only [foldFractions, ExtExpr.const, ExtExpr.eval, Expr.eval, h0, h1,
      List.map_nil, foldValues]
  | cons p ps =>
    obtain ⟨d, m⟩ := p
    simp only [foldFractions, List.map_cons, foldValues]
    suffices h : ∀ (acc : ExtExpr F × ExtExpr F), ((ps.foldl (fun (v, u) (d, m) ↦
        (v * d + m * u, u * d)) acc).1.eval env aux, (ps.foldl (fun (v, u) (d, m) ↦
          (v * d + m * u, u * d)) acc).2.eval env aux) =
        (ps.map fun p ↦ (p.1.eval env aux, p.2.eval env aux)).foldl fracStep
          (acc.1.eval env aux, acc.2.eval env aux) by
      exact h _
    induction ps with
    | nil => intro _; rfl
    | cons q qs ih => intro acc; rw [List.foldl_cons, ih]; rfl

theorem eval_rowSum (env : Expr.Env F K) (aux : ExtExpr.Env K) (k : Nat) (h0 : env.const 0 = 0) :
    (rowSum k).eval env aux = ((List.range k).map fun c ↦ aux.perm (c + 1)).sum := by
  unfold rowSum
  rw [List.sum_eq_foldl]
  suffices h : ∀ (l : List Nat) (acc : ExtExpr F),
      (l.foldl (fun s c ↦ s + .perm (c + 1)) acc).eval env aux =
        (l.map fun c ↦ aux.perm (c + 1)).foldl (· + ·) (acc.eval env aux) by
    rw [h, ExtExpr.const, ExtExpr.eval, Expr.eval, h0]
  intro l
  induction l with
  | nil => intro _; rfl
  | cons c l ih => intro acc; rw [List.foldl_cons, ih]; rfl

/-- Lookup `c`'s fraction pin: `U f - V`, `(V, U)` the cleared fraction of its tuples with the
challenge pair `2 c`, `2 c + 1`, `f` its fraction column. -/
theorem eval_fractionPin [One F] (env : Expr.Env F K) (aux : ExtExpr.Env K) (c : Nat) (l : Lookup F)
    (h0 : env.const 0 = 0) (h1 : env.const 1 = 1) :
    (fractionPin c l).eval env aux =
      (foldValues (l.tuples.map fun (t, m) ↦ (aux.challenge (2 * c) -
        hornerFirst (aux.challenge (2 * c + 1)) (t.map (·.eval env)), m.eval env))).2 *
          aux.perm (c + 1) -
      (foldValues (l.tuples.map fun (t, m) ↦ (aux.challenge (2 * c) -
        hornerFirst (aux.challenge (2 * c + 1)) (t.map (·.eval env)), m.eval env))).1 := by
  have e := eval_foldFractions env aux (l.tuples.map fun (t, m) ↦
    (denominator (.challenge (2 * c)) (.challenge (2 * c + 1)) t, .base m)) h0 h1
  rw [List.map_map] at e
  have hm : ((fun p : ExtExpr F × ExtExpr F ↦ (p.1.eval env aux, p.2.eval env aux)) ∘
      fun (x : List (Expr F) × Expr F) ↦
        (denominator (.challenge (2 * c)) (.challenge (2 * c + 1)) x.1, ExtExpr.base x.2)) =
      fun (x : List (Expr F) × Expr F) ↦ (aux.challenge (2 * c) -
        hornerFirst (aux.challenge (2 * c + 1)) (x.1.map (·.eval env)), x.2.eval env) := by
    funext x
    simp only [Function.comp_apply, eval_denominator env aux _ _ _ h0]
    rfl
  rw [hm] at e
  unfold fractionPin
  dsimp only
  rw [← e]
  rfl

end Eval

end CompStark.Lookup

/-! ### The honest permutation trace -/

namespace CompStark.Lookup
open CompStark.Stark

section Permutation
variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- The accumulator before row `k`: the sum of the fractions of the rows before it. -/
def accAt (A : Air F) (ls : List (Lookup F)) (logN : Nat) (t : Array F) (pis : List F)
    (chs : List EF) (k : Nat) : EF :=
  (List.range k).foldl (fun acc r ↦ (rowFractions A ls logN t pis chs r).foldl (· + ·) acc) 0

/-- The permutation trace: row `r` the accumulator before it and its fractions. -/
theorem permutationTrace_eq (A : Air F) (ls : List (Lookup F)) (logN : Nat) (t : Array F)
    (pis : List F) (chs : List EF) :
    permutationTrace A ls logN t pis chs =
      (((List.range (2 ^ logN)).flatMap fun r ↦
        accAt A ls logN t pis chs r :: rowFractions A ls logN t pis chs r).toArray,
        accAt A ls logN t pis chs (2 ^ logN)) := by
  unfold permutationTrace
  generalize 2 ^ logN = n
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine Prod.ext ?_ ?_
    · show _ = _
      rw [← Array.toList_inj]
      simp only [Array.toList_append, Array.toList_push, List.append_assoc, List.singleton_append]
    · simp only [accAt, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem length_rowFractions (A : Air F) (ls : List (Lookup F)) (logN : Nat) (t : Array F)
    (pis : List F) (chs : List EF) (r : Nat) :
    (rowFractions A ls logN t pis chs r).length = ls.length := by
  simp only [rowFractions, List.length_map, List.length_zipIdx]

theorem getD_flatMap_uniform {α β : Type} (f : α → List β) (w : Nat)
    (hw : ∀ a, (f a).length = w) (d : β) (a0 : α) : ∀ (l : List α) (i j : Nat), i < l.length →
      j < w → (l.flatMap f).getD (i * w + j) d = (f (l.getD i a0)).getD j d
  | [], _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | a :: l, 0, j, _, hj => by
    rw [List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getD_cons_zero,
      List.getD_append _ _ _ _ (by rw [hw]; exact hj)]
  | a :: l, i + 1, j, hi, hj => by
    rw [List.flatMap_cons, List.getD_cons_succ, List.getD_append_right _ _ _ _ (by
      rw [hw]; nlinarith), hw, show (i + 1) * w + j - w = i * w + j by rw [Nat.succ_mul]; omega]
    exact getD_flatMap_uniform f w hw d a0 l i j (by simpa only [List.length_cons,
      Nat.add_lt_add_iff_right] using hi) hj

/-- Row `i`'s entries of the permutation trace: the accumulator before it, then its
fractions. -/
theorem getD_permutationTrace (A : Air F) (ls : List (Lookup F)) (logN : Nat) (t : Array F)
    (pis : List F) (chs : List EF) (i j : Nat) (hi : i < 2 ^ logN) (hj : j < ls.length + 1) :
    (permutationTrace A ls logN t pis chs).1.getD (i * (ls.length + 1) + j) 0 =
      (accAt A ls logN t pis chs i :: rowFractions A ls logN t pis chs i).getD j 0 := by
  have hr : (List.range (2 ^ logN)).getD i 0 = i := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_range]; exact hi), List.getElem_range]
  rw [permutationTrace_eq, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    ← List.getD_eq_getElem?_getD, getD_flatMap_uniform _ (ls.length + 1)
      (fun r ↦ by rw [List.length_cons, length_rowFractions]) 0 0 _ i j
      (by rw [List.length_range]; exact hi) hj, hr]

end Permutation

/-! ### The LogUp constraints on the honest rows -/

section Row
variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]
local notation "E" => Challenge.Spec EF

theorem toSpec_foldl_add (l : List EF) (a : EF) :
    Challenge.toSpec (l.foldl (· + ·) a) = Challenge.toSpec a + (l.map Challenge.toSpec).sum := by
  induction l generalizing a with
  | nil => simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | cons x l ih => rw [List.foldl_cons, ih, Challenge.toSpec_add, List.map_cons, List.sum_cons,
      add_assoc]

theorem toSpec_combine (b : EF) (ts : List F) :
    Challenge.toSpec (combine b ts) =
      hornerFirst (Challenge.toSpec b) (ts.map (algebraMap F E)) := by
  cases ts with
  | nil => exact Challenge.toSpec_zero
  | cons x xs =>
    simp only [combine, List.map_cons, hornerFirst]
    suffices h : ∀ acc : EF, Challenge.toSpec (xs.foldl (fun acc y ↦ Ext.ofBase y + acc * b) acc)
        = (xs.map (algebraMap F E)).foldl (fun acc y ↦ y + acc * Challenge.toSpec b)
          (Challenge.toSpec acc) by
      rw [h, Challenge.toSpec_ofBase']
    induction xs with
    | nil => intro _; rfl
    | cons y ys ih =>
      intro acc
      rw [List.foldl_cons, ih, List.map_cons, List.foldl_cons, Challenge.toSpec_add,
        Challenge.toSpec_mul, Challenge.toSpec_ofBase']

/-- A fraction of the honest trace is `∑ m / d` over its tuples. -/
theorem toSpec_fraction (env : Expr.Env F F) (a b : EF) (l : Lookup F) :
    Challenge.toSpec (fraction env a b l) = (l.tuples.map fun x ↦
      algebraMap F E (x.2.eval env) * (Challenge.toSpec a -
        hornerFirst (Challenge.toSpec b) (x.1.map fun e ↦ algebraMap F E (e.eval env)))⁻¹).sum := by
  unfold fraction
  suffices h : ∀ (ts : List (List (Expr F) × Expr F)) (s : EF), Challenge.toSpec (ts.foldl
      (fun s (t, m) ↦ if m.eval env = 0 then s else
        s + Challenge.smul (m.eval env) (a - combine b (t.map (·.eval env)))⁻¹) s) =
      Challenge.toSpec s + (ts.map fun x ↦ algebraMap F E (x.2.eval env) * (Challenge.toSpec a -
        hornerFirst (Challenge.toSpec b) (x.1.map fun e ↦ algebraMap F E (e.eval env)))⁻¹).sum by
    rw [h, Challenge.toSpec_zero, zero_add]
  intro ts
  induction ts with
  | nil => intro _; simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | cons x ts ih =>
    intro s
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, ← add_assoc]
    congr 1
    obtain ⟨t, m⟩ := x
    dsimp only
    split
    · rename_i hm; rw [hm, map_zero, zero_mul, add_zero]
    · rw [Challenge.toSpec_add, Challenge.toSpec_smul, Challenge.toSpec_inv, Challenge.toSpec_sub,
        toSpec_combine, List.map_map, Algebra.smul_def]
      rfl

/-- A row-local expression has the same value on the generation's row as on the trace's. -/
theorem Expr.eval_rowLocal (A : Air F) (logN : Nat) (t : Array F) (pis : List F) (i : Nat) :
    ∀ e : Expr F, e.rowLocal = true →
      e.eval (A.traceRow logN t pis i) = e.eval (generationRow A logN t pis i)
  | .cur _, _ | .next _, _ | .prepCur _, _ | .prepNext _, _ | .pub _, _ | .const _, _ => rfl
  | .periodic _, h | .isFirstRow, h | .isLastRow, h | .isTransition, h => nomatch h
  | .add a b, h | .sub a b, h | .mul a b, h => by
    simp only [Expr.rowLocal, Bool.and_eq_true] at h
    simp only [Expr.eval]
    rw [Expr.eval_rowLocal A logN t pis i a h.1, Expr.eval_rowLocal A logN t pis i b h.2]

/-- The honest permutation trace's values on row `i`: its rows `i` and `i + 1`, the challenges
`chs` and its terminal, in the spec field. -/
noncomputable def honestAux (A : Air F) (ls : List (Lookup F)) (logN : Nat) (t : Array F)
    (pis : List F) (chs : List EF) (i : Nat) : ExtExpr.Env E :=
  let pt := permutationTrace A ls logN t pis chs
  ⟨fun c ↦ Challenge.toSpec (pt.1.getD (i * (ls.length + 1) + c) 0),
    fun c ↦ Challenge.toSpec (pt.1.getD ((i + 1) % 2 ^ logN * (ls.length + 1) + c) 0),
    fun j ↦ Challenge.toSpec (chs.getD j 0), Challenge.toSpec pt.2⟩

/-- On row `i`, no tuple of non-zero multiplicity has a zero denominator. -/
def NoPoleAt (A : Air F) (ls : List (Lookup F)) (logN : Nat) (t : Array F) (pis : List F)
    (chs : List EF) (i : Nat) : Prop :=
  ∀ c (hc : c < ls.length), ∀ x ∈ ls[c].tuples,
    x.2.eval (generationRow A logN t pis i) ≠ 0 → chs.getD (2 * c) 0 -
      combine (chs.getD (2 * c + 1) 0) (x.1.map (·.eval (generationRow A logN t pis i))) ≠ 0

/-- **The honest permutation trace satisfies the LogUp constraints** on every row of the trace
domain, with Plonky3's selectors there, when the lookups are row-local and no tuple of non-zero
multiplicity has a zero denominator on the row. -/
theorem logUpConstraints_honest (A : Air F) (ls : List (Lookup F)) (logN : Nat)
    (h : logN ≤ twoAdicity F) (t : Array F) (pis : List F) (chs : List EF)
    (hrow : ∀ l ∈ ls, ∀ x ∈ l.tuples, (∀ e ∈ x.1, e.rowLocal) ∧ x.2.rowLocal) (i : Nat)
    (hi : i < 2 ^ logN) (hpole : NoPoleAt A ls logN t pis chs i) :
    ∀ g ∈ logUpConstraints ls, g.eval ((A.traceRow logN t pis i).map (algebraMap F E))
      (honestAux A ls logN t pis chs i) = 0 := by
  set env := (A.traceRow logN t pis i).map (algebraMap F E) with henv
  set aux := honestAux A ls logN t pis chs i with haux
  set L := ls.length
  set fs := rowFractions A ls logN t pis chs i with hfs
  have h0 : env.const 0 = 0 := map_zero _
  have h1 : env.const 1 = 1 := map_one _
  have hfl : fs.length = L := length_rowFractions ..
  -- the permutation trace's entries on rows `i` and `i + 1`
  have hacc : aux.perm 0 = Challenge.toSpec (accAt A ls logN t pis chs i) := by
    simp only [aux, honestAux]
    rw [getD_permutationTrace _ _ _ _ _ _ i 0 hi (Nat.succ_pos _)]
    rfl
  have hfrac : ∀ c < L, aux.perm (c + 1) = Challenge.toSpec (fs.getD c 0) := by
    intro c hc
    simp only [aux, honestAux]
    rw [getD_permutationTrace _ _ _ _ _ _ i (c + 1) hi (by omega)]
    rfl
  have hrs : (rowSum L).eval env aux = (fs.map Challenge.toSpec).sum := by
    rw [eval_rowSum env aux L h0]
    have : (List.range L).map (fun c ↦ aux.perm (c + 1)) = fs.map Challenge.toSpec := by
      refine List.ext_getElem (by rw [List.length_map, List.length_map, List.length_range, hfl])
        fun c h1 h2 ↦ ?_
      rw [List.getElem_map, List.getElem_map, List.getElem_range, hfrac c (by
        rw [List.length_map, List.length_range] at h1; exact h1),
        List.getD_eq_getElem _ _ (by rw [List.length_map] at h2; exact h2)]
    rw [this]
  have hstep : Challenge.toSpec (accAt A ls logN t pis chs (i + 1)) =
      Challenge.toSpec (accAt A ls logN t pis chs i) + (fs.map Challenge.toSpec).sum := by
    rw [accAt, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      toSpec_foldl_add]
    rfl
  have hw := BaseField.isPrimitiveRoot_twoAdicGen (F := F) logN h
  intro g hg
  unfold logUpConstraints at hg
  split at hg
  · exact absurd hg List.not_mem_nil
  rcases List.mem_append.mp hg with hg | hg
  · -- a fraction pin
    obtain ⟨⟨l, c⟩, hlc, rfl⟩ := List.mem_map.mp hg
    have hc : c < L := by have := (List.mem_zipIdx hlc).2.1; omega
    have hl : l = ls[c] := by
      have := (List.mem_zipIdx hlc).2.2; simp only [Nat.sub_zero] at this; exact this
    subst hl
    dsimp only
    rw [eval_fractionPin env aux c _ h0 h1, hfrac c hc, sub_eq_zero]
    have hc' : c < ls.length := hc
    have hfc : fs.getD c 0 = fraction (generationRow A logN t pis i) (chs.getD (2 * c) 0)
        (chs.getD (2 * c + 1) 0) (ls[c]'hc') := by
      have hcl : c < fs.length := by rw [hfl]; exact hc
      rw [List.getD_eq_getElem _ _ hcl]
      simp only [hfs, rowFractions, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    have hev : ∀ x ∈ ls[c].tuples, (∀ e ∈ x.1, e.eval env =
        algebraMap F E (e.eval (generationRow A logN t pis i))) ∧
        x.2.eval env = algebraMap F E (x.2.eval (generationRow A logN t pis i)) := by
      intro x hx
      have hr := hrow _ (List.getElem_mem hc) x hx
      exact ⟨fun e he ↦ by
          rw [henv, Expr.eval_map, Expr.eval_rowLocal A logN t pis i e (hr.1 e he)],
        by rw [henv, Expr.eval_map, Expr.eval_rowLocal A logN t pis i _ hr.2]⟩
    have hts : (ls[c].tuples.map fun x ↦ (aux.challenge (2 * c) -
        hornerFirst (aux.challenge (2 * c + 1)) (x.1.map (·.eval env)), x.2.eval env)) =
        ls[c].tuples.map fun x ↦ (Challenge.toSpec (chs.getD (2 * c) 0) -
          hornerFirst (Challenge.toSpec (chs.getD (2 * c + 1) 0))
            (x.1.map fun e ↦ algebraMap F E (e.eval (generationRow A logN t pis i))),
          algebraMap F E (x.2.eval (generationRow A logN t pis i))) := by
      refine List.map_congr_left fun x hx ↦ ?_
      obtain ⟨he, hm⟩ := hev x hx
      rw [hm, List.map_congr_left he]
      rfl
    rw [hts, hfc, toSpec_fraction]
    have := foldValues_mul_sum (ls[c].tuples.map fun x ↦ (Challenge.toSpec (chs.getD (2 * c) 0) -
          hornerFirst (Challenge.toSpec (chs.getD (2 * c + 1) 0))
            (x.1.map fun e ↦ algebraMap F E (e.eval (generationRow A logN t pis i))),
          algebraMap F E (x.2.eval (generationRow A logN t pis i)))) (fun y hy hm ↦ by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        have hm' : x.2.eval (generationRow A logN t pis i) ≠ 0 := fun h0' ↦ hm (by
          simp only [h0', map_zero])
        have hd := hpole c hc x hx hm'
        intro h0'
        apply hd
        refine Challenge.toSpec_injective ?_
        rw [Challenge.toSpec_sub, toSpec_combine, Challenge.toSpec_zero, ← h0', List.map_map]
        rfl)
    rw [List.map_map] at this
    exact this
  · -- the accumulator's constraints
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · simp only [ExtExpr.eval, hacc]
      by_cases h0i : i = 0
      · subst h0i
        simp only [accAt, List.range_zero, List.foldl_nil, Challenge.toSpec_zero, mul_zero]
      · simp only [henv, Expr.Env.map, Air.traceRow, Expr.eval, h0i, ↓reduceIte, map_zero,
          zero_mul]
    · simp only [ExtExpr.eval_hSub, ExtExpr.eval, hacc]
      by_cases hl : i + 1 = 2 ^ logN
      · have : (twoAdicGen logN : F) ^ i - (twoAdicGen logN)⁻¹ = 0 := by
          rw [sub_eq_zero]
          exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hl, hw.pow_eq_one])
        simp only [henv, Expr.Env.map, Air.traceRow, Expr.eval, this, map_zero, zero_mul]
      · have hn : aux.permNext 0 = Challenge.toSpec (accAt A ls logN t pis chs (i + 1)) := by
          simp only [aux, honestAux]
          rw [Nat.mod_eq_of_lt (by omega), getD_permutationTrace _ _ _ _ _ _ (i + 1) 0 (by omega)
            (Nat.succ_pos _)]
          rfl
        rw [hn, hstep, show (rowSum ls.length).eval env aux = _ from hrs]
        ring
    · simp only [ExtExpr.eval_hSub, ExtExpr.eval, hacc]
      by_cases hl : i + 1 = 2 ^ logN
      · have ht : aux.terminal = Challenge.toSpec (accAt A ls logN t pis chs (i + 1)) := by
          simp only [aux, honestAux]
          rw [permutationTrace_eq, hl]
        rw [ht, hstep, show (rowSum ls.length).eval env aux = _ from hrs]
        ring
      · simp only [henv, Expr.Env.map, Air.traceRow, Expr.eval, hl, ↓reduceIte, map_zero,
          zero_mul]

end Row

end CompStark.Lookup

/-! ### The terminals sum to the batch's weighted messages -/

namespace CompStark.Lookup
open CompStark.Stark

theorem foldl_busStep_length {F : Type} (inst : List (Lookup F))
    (s : List Nat × List (String × Nat) × Nat) :
    (inst.foldl busStep s).1.length = s.1.length + inst.length := by
  induction inst generalizing s with
  | nil => simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
  | cons l inst ih =>
    rw [List.foldl_cons, ih, List.length_cons]
    have : (busStep s l).1.length = s.1.length + 1 := by
      unfold busStep
      split
      · split <;> simp only [List.length_append, List.length_singleton]
      · simp only [List.length_append, List.length_singleton]
    omega

/-- Every instance's bus numbers are one per lookup. -/
theorem busIdsFrom_lengths {F : Type} (names : List (String × Nat)) (next : Nat) :
    ∀ ls : List (List (Lookup F)),
      List.Forall₂ (fun ids inst ↦ ids.length = inst.length) (busIdsFrom names next ls) ls
  | [] => .nil
  | inst :: ls => by
    simp only [busIdsFrom]
    exact .cons (by rw [foldl_busStep_length, List.length_nil, Nat.zero_add])
      (busIdsFrom_lengths _ _ ls)

section Terminals
variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]
local notation "E" => Challenge.Spec EF

/-- The denominator base of bus `b` for the pair `(α, β)` and the widest tuple `W`. -/
def busPrefix (alpha beta : EF) (W b : Nat) : EF := alpha + Ext.ofBase ((b + 1 : Nat) : F) *
  Ext.pow beta W

theorem getD_flatMap_pair (pre : Nat → EF) (beta : EF) (ids : List Nat) (c : Nat)
    (hc : c < ids.length) :
    (ids.flatMap fun b ↦ [pre b, beta]).getD (2 * c) 0 = pre (ids[c]) ∧
      (ids.flatMap fun b ↦ [pre b, beta]).getD (2 * c + 1) 0 = beta := by
  induction ids generalizing c with
  | nil => exact absurd hc (Nat.not_lt_zero _)
  | cons b ids ih =>
    rcases c with _ | c
    · simp only [List.flatMap_cons, Nat.mul_zero, List.cons_append, List.getD_cons_zero,
        Nat.zero_add, List.getD_cons_succ, List.getElem_cons_zero, and_self]
    · simp only [List.length_cons, Nat.add_lt_add_iff_right] at hc
      have := ih c hc
      simp only [List.flatMap_cons, List.cons_append, List.getElem_cons_succ]
      rw [show 2 * (c + 1) = 2 * c + 1 + 1 by ring, List.getD_cons_succ, List.getD_cons_succ,
        show 2 * c + 1 + 1 + 1 = 2 * c + 1 + 1 + 1 from rfl, List.getD_cons_succ,
        List.getD_cons_succ, List.nil_append]
      exact this

theorem sum_flatMap {α β : Type*} [AddCommMonoid β] (L : List α) (f : α → List β) :
    (L.flatMap f).sum = (L.map fun a ↦ (f a).sum).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [List.flatMap_cons, List.sum_append, ih, List.map_cons, List.sum_cons]

/-- With bus numbers `ids`, one per lookup, a row's fractions are the lookups' with their buses'
denominator bases. -/
theorem rowFractions_eq (A : Air F) (ls : List (Lookup F)) (logN : Nat) (t : Array F)
    (pis : List F) (ids : List Nat) (hl : ids.length = ls.length) (pre : Nat → EF) (beta : EF)
    (r : Nat) :
    rowFractions A ls logN t pis (ids.flatMap fun b ↦ [pre b, beta]) r =
      (ls.zip ids).map fun (l, b) ↦ fraction (generationRow A logN t pis r) (pre b) beta l := by
  refine List.ext_getElem (by simp only [rowFractions, List.length_map, List.length_zipIdx,
    List.length_zip, hl, Nat.min_self]) fun c h1 h2 ↦ ?_
  have hc : c < ls.length := by
    simp only [rowFractions, List.length_map, List.length_zipIdx] at h1; exact h1
  obtain ⟨ha, hb⟩ := getD_flatMap_pair pre beta ids c (by omega)
  simp only [rowFractions, List.getElem_map, List.getElem_zipIdx, List.getElem_zip, Nat.zero_add,
    ha, hb]

/-- The terminal of the honest permutation trace with bus numbers `ids` is the sum, over the
instance's rows, lookups and tuples, of the multiplicity over the denominator. -/
theorem toSpec_terminal (A : Air F) (ls : List (Lookup F)) (logN : Nat) (t : Array F)
    (pis : List F) (ids : List Nat) (hl : ids.length = ls.length) (pre : Nat → EF) (beta : EF) :
    Challenge.toSpec (permutationTrace A ls logN t pis (ids.flatMap fun b ↦ [pre b, beta])).2 =
      (((List.range (2 ^ logN)).flatMap fun r ↦ (ls.zip ids).flatMap fun (l, b) ↦
        l.tuples.map fun (es, m) ↦ ((b, es.map (Expr.eval (generationRow A logN t pis r))),
          Expr.eval (generationRow A logN t pis r) m)).map fun x ↦
        algebraMap F E x.2 * (Challenge.toSpec (pre x.1.1) -
          hornerFirst (Challenge.toSpec beta) (x.1.2.map (algebraMap F E)))⁻¹).sum := by
  rw [permutationTrace_eq, accAt]
  suffices h : ∀ (L : List Nat) (a : EF), Challenge.toSpec (L.foldl (fun acc r ↦
      (rowFractions A ls logN t pis (ids.flatMap fun b ↦ [pre b, beta]) r).foldl (· + ·) acc) a) =
      Challenge.toSpec a + ((L.flatMap fun r ↦ (ls.zip ids).flatMap fun (l, b) ↦
        l.tuples.map fun (es, m) ↦ ((b, es.map (Expr.eval (generationRow A logN t pis r))),
          Expr.eval (generationRow A logN t pis r) m)).map fun x ↦
        algebraMap F E x.2 * (Challenge.toSpec (pre x.1.1) -
          hornerFirst (Challenge.toSpec beta) (x.1.2.map (algebraMap F E)))⁻¹).sum by
    rw [h, Challenge.toSpec_zero, zero_add]
  intro L
  induction L with
  | nil => intro _; simp only [List.foldl_nil, List.flatMap_nil, List.map_nil, List.sum_nil,
      add_zero]
  | cons r L ih =>
    intro a
    rw [List.foldl_cons, ih, toSpec_foldl_add, List.flatMap_cons, List.map_append,
      List.sum_append, add_assoc]
    congr 2
    rw [rowFractions_eq A ls logN t pis ids hl pre beta r, List.map_map, List.map_flatMap,
      sum_flatMap]
    congr 1
    refine List.map_congr_left fun ⟨l, b⟩ _ ↦ ?_
    simp only [Function.comp_apply, toSpec_fraction, List.map_map]
    congr 1
    refine List.map_congr_left fun x _ ↦ ?_
    simp only [Function.comp_apply, List.map_map]
    rfl

end Terminals

end CompStark.Lookup

namespace CompStark.Batch
open CompStark.Stark CompStark.Lookup

section Terminals
variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]
local notation "E" => Challenge.Spec EF

/-- The honest terminals of instances with bus numbers `idss` sum to their messages, each
multiplicity over its denominator. -/
theorem toSpec_terminals_aux (pre : Nat → EF) (beta : EF) : ∀ (Is : List (Instance F))
    (ts : List (Array F)) (ps : List (List F)) (idss : List (List Nat)),
    ts.length = Is.length → ps.length = Is.length →
    List.Forall₂ (fun ids I ↦ ids.length = I.lookups.length) idss Is →
    ((((permutations Is ts ps (idss.map fun ids ↦ ids.flatMap fun b ↦ [pre b, beta])).map
        (·.map (·.2))).filterMap id).map Challenge.toSpec).sum =
      ((((Is.zip (ts.zip ps)).zip idss).flatMap fun ((I, t, p), ids) ↦
        (List.range (2 ^ I.logN)).flatMap fun r ↦ (I.lookups.zip ids).flatMap fun (l, b) ↦
          l.tuples.map fun (es, m) ↦ ((b, es.map (Expr.eval (generationRow I.air I.logN t p r))),
            Expr.eval (generationRow I.air I.logN t p r) m)).map fun x ↦
        algebraMap F E x.2 * (Challenge.toSpec (pre x.1.1) -
          hornerFirst (Challenge.toSpec beta) (x.1.2.map (algebraMap F E)))⁻¹).sum
  | [], _, _, _, _, _, .nil => rfl
  | I :: Is, t :: ts, p :: ps, ids :: idss, hts, hps, .cons hl hs => by
    have ih := toSpec_terminals_aux pre beta Is ts ps idss
      (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hts)
      (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hps) hs
    simp only [permutations, List.map_cons, List.zip_cons_cons] at ih ⊢
    rw [List.flatMap_cons, List.map_append, List.sum_append, ← ih]
    by_cases he : I.lookups.isEmpty
    · dsimp only
      have h0 : I.lookups = [] := List.isEmpty_iff.mp he
      simp only [h0, List.isEmpty_nil, ↓reduceIte, Option.map_none, List.filterMap_cons, id,
        List.zip_nil_left, List.flatMap_nil]
      rw [List.flatMap_eq_nil_iff.mpr (fun _ _ ↦ rfl), List.map_nil, List.sum_nil, zero_add]
    · dsimp only
      simp only [he, Bool.false_eq_true, ↓reduceIte, Option.map_some, List.filterMap_cons, id,
        List.map_cons, List.sum_cons]
      rw [toSpec_terminal I.air I.lookups I.logN t p ids hl pre beta]
  | _ :: _, [], _, _, h, _, _ => absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  | _ :: _, _ :: _, [], _, _, h, _ =>
    absurd h (by simp only [List.length_cons, List.length_nil]; omega)

theorem lookupConstraints_of_isEmpty (I : Instance F) (h : I.lookups.isEmpty = true) :
    I.air.lookupConstraints I.logN = [] := by
  show logUpConstraints I.lookups = []
  unfold logUpConstraints
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]

/-- **Balanced buses give terminals summing to zero.** -/
theorem terminals_sum_eq_zero (instances : List (Instance F)) (traces : List (Array F))
    (pis : List (List F)) (hts : traces.length = instances.length)
    (hps : pis.length = instances.length) (hbal : Balanced instances traces pis) (alpha beta : EF) :
    (((permutations instances traces pis (challengeLayout (instances.map (·.lookups)) alpha
      beta)).map (·.map (·.2))).filterMap id).foldl (· + ·) 0 = 0 := by
  refine Challenge.toSpec_injective ?_
  rw [toSpec_foldl_add, Challenge.toSpec_zero, zero_add]
  have hlen : List.Forall₂ (fun ids (I : Instance F) ↦ ids.length = I.lookups.length)
      (busIds (instances.map (·.lookups))) instances := by
    have := busIdsFrom_lengths [] 0 (instances.map (·.lookups))
    rw [List.forall₂_map_right_iff] at this
    exact this
  have e := toSpec_terminals_aux (busPrefix alpha beta (maxWidth
    (instances.map (·.lookups)).flatten)) beta instances traces pis _ hts hps hlen
  rw [show challengeLayout (instances.map (·.lookups)) alpha beta =
    (busIds (instances.map (·.lookups))).map fun ids ↦ ids.flatMap fun b ↦
      [busPrefix alpha beta (maxWidth (instances.map (·.lookups)).flatten) b, beta] from rfl, e]
  have hw := sum_weighted_eq_zero (fun k : Nat × List F ↦ (Challenge.toSpec (busPrefix alpha beta
      (maxWidth (instances.map (·.lookups)).flatten) k.1) -
    hornerFirst (Challenge.toSpec beta) (k.2.map (algebraMap F E)))⁻¹) _
    ((messages instances traces pis).map fun x ↦ (x.1, algebraMap F E x.2)) le_rfl fun k ↦ by
      have h := congrArg (algebraMap F E) (hbal k)
      rw [map_zero, map_list_sum, List.map_map] at h
      rw [List.filter_map, List.map_map]
      exact h
  rw [List.map_map] at hw
  refine Eq.trans ?_ hw
  refine congrArg List.sum (List.map_congr_left fun x _ ↦ ?_)
  simp only [Function.comp_apply]
  ring

end Terminals

end CompStark.Batch
