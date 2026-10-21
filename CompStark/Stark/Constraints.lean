/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Satisfied
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.LinearAlgebra.Lagrange

/-! # The constraints as polynomials

An AIR's constraints over polynomials, as the analysis of the constraint check sees them:

* `Expr.eval_hom`: evaluation commutes with maps that respect `+`, `-` and `*`.
* `constraintPoly`: a constraint over the polynomials `T` of the trace and `Tp` of the
  preprocessed trace, with the selector polynomials `firstSel`, `lastSel` and `X - ω⁻¹`; its
  degree is at most `degBound` (`natDegree_constraintPoly`), and on the trace domain `⟨ω⟩` it
  takes the constraint's value on the traces' rows (`eval_constraintPoly_root`). A satisfied
  constraint is `Z_H` times its quotient (`constraintPoly_eq`).
* Points `g ωᵐ` of the shifted cosets are not two-adic roots of unity (`genPoint_ne`).
* `horner`: Horner's rule, the folding of the constraints by `α`.
-/

@[expose] public section
namespace CompStark.Stark
open Polynomial

/-! ### Constraints under ring maps -/

/-- Evaluation commutes with a map that respects `+`, `-` and `*`, for expressions reading
columns below `w`, `pw` and `pwNext` (`colsBelow`) of environments that agree there. -/
theorem Expr.eval_hom {F : Type} {R S : Type*} [Add R] [Sub R] [Mul R] [Add S] [Sub S] [Mul S]
    (f : R → S)
    (hadd : ∀ a b, f (a + b) = f a + f b) (hsub : ∀ a b, f (a - b) = f a - f b)
    (hmul : ∀ a b, f (a * b) = f a * f b) (w pw pwNext : Nat) (r : Expr.Env F R)
    (s : Expr.Env F S)
    (hcur : ∀ c < w, f (r.cur c) = s.cur c) (hnext : ∀ c < w, f (r.next c) = s.next c)
    (hpcur : ∀ c < pw, f (r.prepCur c) = s.prepCur c)
    (hpnext : ∀ c < pwNext, f (r.prepNext c) = s.prepNext c)
    (hpub : ∀ j, f (r.pub j) = s.pub j) (hconst : ∀ c, f (r.const c) = s.const c)
    (h1 : f r.isFirstRow = s.isFirstRow) (h2 : f r.isLastRow = s.isLastRow)
    (h3 : f r.isTransition = s.isTransition) :
    ∀ e : Expr F, e.colsBelow w pw pwNext = true → f (e.eval r) = e.eval s
  | .cur c, h => hcur c (of_decide_eq_true h)
  | .next c, h => hnext c (of_decide_eq_true h)
  | .prepCur c, h => hpcur c (of_decide_eq_true h)
  | .prepNext c, h => hpnext c (of_decide_eq_true h)
  | .pub j, _ => hpub j
  | .const c, _ => hconst c
  | .isFirstRow, _ => h1
  | .isLastRow, _ => h2
  | .isTransition, _ => h3
  | .add a b, h => by
    simp only [Expr.colsBelow, Bool.and_eq_true] at h
    simp only [Expr.eval]
    rw [hadd, Expr.eval_hom f hadd hsub hmul w pw pwNext r s hcur hnext hpcur hpnext hpub hconst
      h1 h2 h3 a h.1, Expr.eval_hom f hadd hsub hmul w pw pwNext r s hcur hnext hpcur hpnext
      hpub hconst h1 h2 h3 b h.2]
  | .sub a b, h => by
    simp only [Expr.colsBelow, Bool.and_eq_true] at h
    simp only [Expr.eval]
    rw [hsub, Expr.eval_hom f hadd hsub hmul w pw pwNext r s hcur hnext hpcur hpnext hpub hconst
      h1 h2 h3 a h.1, Expr.eval_hom f hadd hsub hmul w pw pwNext r s hcur hnext hpcur hpnext
      hpub hconst h1 h2 h3 b h.2]
  | .mul a b, h => by
    simp only [Expr.colsBelow, Bool.and_eq_true] at h
    simp only [Expr.eval]
    rw [hmul, Expr.eval_hom f hadd hsub hmul w pw pwNext r s hcur hnext hpcur hpnext hpub hconst
      h1 h2 h3 a h.1, Expr.eval_hom f hadd hsub hmul w pw pwNext r s hcur hnext hpcur hpnext
      hpub hconst h1 h2 h3 b h.2]

/-- The degree of a constraint over polynomials is at most `degBound`. -/
theorem Expr.natDegree_eval {F : Type} [Field F] (n : Nat) (env : Expr.Env F F[X])
    (hcur : ∀ c, (env.cur c).natDegree ≤ n - 1) (hnext : ∀ c, (env.next c).natDegree ≤ n - 1)
    (hpcur : ∀ c, (env.prepCur c).natDegree ≤ n - 1)
    (hpnext : ∀ c, (env.prepNext c).natDegree ≤ n - 1)
    (hpub : ∀ j, (env.pub j).natDegree = 0) (hconst : ∀ c, (env.const c).natDegree = 0)
    (h1 : env.isFirstRow.natDegree ≤ n - 1) (h2 : env.isLastRow.natDegree ≤ n - 1)
    (h3 : env.isTransition.natDegree ≤ 1) : ∀ e : Expr F, (e.eval env).natDegree ≤ e.degBound n
  | .cur c => hcur c
  | .next c => hnext c
  | .prepCur c => hpcur c
  | .prepNext c => hpnext c
  | .pub j => (hpub j).le
  | .const c => (hconst c).le
  | .isFirstRow => h1
  | .isLastRow => h2
  | .isTransition => h3
  | .add a b => (natDegree_add_le _ _).trans (max_le_max
      (Expr.natDegree_eval n env hcur hnext hpcur hpnext hpub hconst h1 h2 h3 a)
      (Expr.natDegree_eval n env hcur hnext hpcur hpnext hpub hconst h1 h2 h3 b))
  | .sub a b => (natDegree_sub_le _ _).trans (max_le_max
      (Expr.natDegree_eval n env hcur hnext hpcur hpnext hpub hconst h1 h2 h3 a)
      (Expr.natDegree_eval n env hcur hnext hpcur hpnext hpub hconst h1 h2 h3 b))
  | .mul a b => natDegree_mul_le.trans (Nat.add_le_add
      (Expr.natDegree_eval n env hcur hnext hpcur hpnext hpub hconst h1 h2 h3 a)
      (Expr.natDegree_eval n env hcur hnext hpcur hpnext hpub hconst h1 h2 h3 b))

/-! ### The constraints as polynomials -/

section Polys
variable {F : Type} [BaseField F]

/-- `Z_H(X) / (X - 1) = 1 + X + … + X^(n-1)`. -/
noncomputable def firstSel (n : Nat) : F[X] := ∑ m ∈ Finset.range n, X ^ m

/-- `Z_H(X) / (X - ω⁻¹) = ω · (Z_H / (X - 1))(ω X)`. -/
noncomputable def lastSel (n : Nat) (w : F) : F[X] := C w * (firstSel n).comp (C w * X)

/-- The constraints' environment over the spec polynomials: the column polynomials `T` of the
trace and `Tp` of the preprocessed trace, shifted by `ω` for the next row, and the selectors. -/
noncomputable def polyEnv (n : Nat) (w : F) (T Tp : Nat → F[X]) (pis : List F) :
    Expr.Env F F[X] where
  cur := T
  next j := (T j).comp (C w * X)
  prepCur := Tp
  prepNext j := (Tp j).comp (C w * X)
  pub j := C (pis.getD j 0)
  const c := C c
  isFirstRow := firstSel n
  isLastRow := lastSel n w
  isTransition := X - C w⁻¹

/-- `(X - 1) · Z_H / (X - 1) = Z_H`, at any point. -/
theorem aeval_firstSel {S : Type*} [CommRing S] [Algebra F S] (n : Nat) (y : S) :
    aeval y (firstSel n : F[X]) * (y - 1) = y ^ n - 1 := by
  rw [firstSel, map_sum]
  simp only [map_pow, aeval_X]
  exact geom_sum_mul y n

/-- `(X - ω⁻¹) · Z_H / (X - ω⁻¹) = Z_H`, at any point, for `ωⁿ = 1`. -/
theorem aeval_lastSel {S : Type*} [CommRing S] [Algebra F S] (n : Nat) (w : F) (hw : w ≠ 0)
    (hwn : w ^ n = 1) (y : S) :
    aeval y (lastSel n w) * (y - algebraMap F S w⁻¹) = y ^ n - 1 := by
  have h := aeval_firstSel (F := F) n (algebraMap F S w * y)
  rw [lastSel, map_mul, aeval_comp, map_mul, aeval_C, aeval_X]
  have hw' : algebraMap F S w * algebraMap F S w⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hw, map_one]
  calc algebraMap F S w * aeval (algebraMap F S w * y) (firstSel n : F[X]) *
        (y - algebraMap F S w⁻¹)
      = aeval (algebraMap F S w * y) (firstSel n : F[X]) * (algebraMap F S w * y - 1) := by
        rw [← hw']; ring
    _ = y ^ n - 1 := by rw [h, mul_pow, ← map_pow, hwn, map_one, one_mul]

/-- The first-row selector has degree below `n`. -/
theorem natDegree_firstSel (n : Nat) : (firstSel n : F[X]).natDegree ≤ n - 1 :=
  natDegree_sum_le_of_forall_le _ _ fun m hm ↦
    (natDegree_X_pow_le m).trans (by have := Finset.mem_range.mp hm; omega)

/-- Composing with `w X` keeps the degree bound. -/
theorem natDegree_comp_shift (p : F[X]) (w : F) : (p.comp (C w * X)).natDegree ≤ p.natDegree :=
  natDegree_comp_le.trans (by
    have := (natDegree_C_mul_le w (X : F[X])).trans natDegree_X_le
    calc p.natDegree * (C w * X).natDegree ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ this
      _ = p.natDegree := Nat.mul_one _)

/-- The last-row selector has degree below `n`. -/
theorem natDegree_lastSel (n : Nat) (w : F) : (lastSel n w).natDegree ≤ n - 1 :=
  (natDegree_C_mul_le _ _).trans ((natDegree_comp_shift _ _).trans (natDegree_firstSel n))

/-- The constraint `c` over the polynomials `T` of the trace and `Tp` of the preprocessed
trace. -/
noncomputable def constraintPoly (n : Nat) (w : F) (T Tp : Nat → F[X]) (pis : List F)
    (c : Expr F) : F[X] :=
  c.eval (polyEnv n w T Tp pis)

/-- A constraint polynomial has degree at most `degBound`. -/
theorem natDegree_constraintPoly (n : Nat) (w : F) (T Tp : Nat → F[X]) (pis : List F)
    (c : Expr F) (hT : ∀ j, (T j).natDegree ≤ n - 1) (hTp : ∀ j, (Tp j).natDegree ≤ n - 1) :
    (constraintPoly n w T Tp pis c).natDegree ≤ c.degBound n :=
  Expr.natDegree_eval n (polyEnv n w T Tp pis) hT
    (fun j ↦ (natDegree_comp_shift _ _).trans (hT j)) hTp
    (fun j ↦ (natDegree_comp_shift _ _).trans (hTp j))
    (fun _ ↦ natDegree_C _) (fun _ ↦ natDegree_C _) (natDegree_firstSel n)
    (natDegree_lastSel n w) (natDegree_sub_le_of_le natDegree_X_le (natDegree_C _).le) c

/-! ### The two-adic subgroups and their cosets -/

/-- `ω ^ 2 ^ k = 1`. -/
theorem twoAdicGen_pow_self (k : Nat) (hk : k ≤ twoAdicity F) : twoAdicGen (F := F) k ^ 2 ^ k = 1 :=
  (BaseField.isPrimitiveRoot_twoAdicGen k hk).pow_eq_one

/-- A `2 ^ k`-th root of unity is a `2 ^ twoAdicity`-th one. -/
theorem root_pow_twoAdicity (y : F) (k : Nat) (hk : k ≤ twoAdicity F) (hy : y ^ 2 ^ k = 1) :
    y ^ 2 ^ twoAdicity F = 1 := by
  rw [show 2 ^ twoAdicity F = 2 ^ k * 2 ^ (twoAdicity F - k) by
    rw [← Nat.pow_add]; congr 1; omega, pow_mul, hy, one_pow]

/-- No point `g ωᵐ` of a coset of a two-adic subgroup is a two-adic root of unity. -/
theorem genPoint_pow_ne (k m : Nat) (hk : k ≤ twoAdicity F) (j : Nat) (hj : j ≤ twoAdicity F) :
    (gen * twoAdicGen (F := F) k ^ m) ^ 2 ^ j ≠ 1 := fun h ↦ by
  have := root_pow_twoAdicity _ j hj h
  rw [mul_pow, ← pow_mul, Nat.mul_comm m, pow_mul,
    root_pow_twoAdicity _ k hk (twoAdicGen_pow_self k hk), one_pow, mul_one] at this
  exact BaseField.gen_pow_ne_one this

/-- No point `g ωᵐ` is a two-adic root of unity. -/
theorem genPoint_ne (k m : Nat) (hk : k ≤ twoAdicity F) (y : F) (j : Nat) (hj : j ≤ twoAdicity F)
    (hy : y ^ 2 ^ j = 1) : gen * twoAdicGen (F := F) k ^ m ≠ y := fun h ↦
  genPoint_pow_ne k m hk j hj (by rw [h, hy])

/-! ### The constraints vanish on the trace domain -/

theorem eval_firstSel_mul (n : Nat) (y : F) : (firstSel n).eval y * (y - 1) = y ^ n - 1 := by
  rw [firstSel, eval_finsetSum]
  simp only [eval_pow, eval_X]
  exact geom_sum_mul y n

/-- The first-row selector is `n` at `1`. -/
theorem eval_firstSel_one (n : Nat) : (firstSel n).eval (1 : F) = n := by
  simp only [firstSel, eval_finsetSum, eval_pow, eval_X, one_pow, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]

/-- The first-row selector on `⟨ω⟩`. -/
theorem eval_firstSel_root (logN i : Nat) (h : logN ≤ twoAdicity F) (hi : i < 2 ^ logN) :
    (firstSel (2 ^ logN)).eval (twoAdicGen (F := F) logN ^ i) =
      if i = 0 then ((2 ^ logN : Nat) : F) else 0 := by
  split
  · rename_i h0
    rw [h0, pow_zero, eval_firstSel_one]
  · rename_i h0
    have hp := BaseField.isPrimitiveRoot_twoAdicGen (F := F) logN h
    have h1 : twoAdicGen (F := F) logN ^ i - 1 ≠ 0 :=
      sub_ne_zero.mpr (hp.pow_ne_one_of_pos_of_lt h0 hi)
    have := eval_firstSel_mul (2 ^ logN) (twoAdicGen (F := F) logN ^ i)
    rw [← pow_mul, Nat.mul_comm, pow_mul, hp.pow_eq_one, one_pow, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right h1

/-- The trace polynomials `T` take the trace's values on `⟨ω⟩`. -/
def TraceOn (logN w : Nat) (trace : Array F) (T : Nat → F[X]) : Prop :=
  ∀ j < w, ∀ i < 2 ^ logN, (T j).eval (twoAdicGen logN ^ i) = trace.getD (i * w + j) 0

/-- The next row's value of polynomials taking a trace's values on `⟨ω⟩`. -/
theorem eval_comp_root (logN : Nat) (h : logN ≤ twoAdicity F) (w : Nat) (trace : Array F)
    (T : Nat → F[X]) (hT : TraceOn logN w trace T) (j : Nat) (hj : j < w) (i : Nat) :
    ((T j).comp (C (twoAdicGen logN) * X)).eval (twoAdicGen logN ^ i) =
      trace.getD ((i + 1) % 2 ^ logN * w + j) 0 := by
  have hp := BaseField.isPrimitiveRoot_twoAdicGen (F := F) logN h
  have hsucc : twoAdicGen (F := F) logN ^ (i + 1) =
      twoAdicGen logN ^ ((i + 1) % 2 ^ logN) := by
    conv_lhs => rw [← Nat.mod_add_div (i + 1) (2 ^ logN)]
    rw [pow_add, pow_mul, hp.pow_eq_one, one_pow, mul_one]
  have hm : (i + 1) % 2 ^ logN < 2 ^ logN := Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [eval_comp, eval_mul, eval_C, eval_X, ← hT j hj _ hm, ← pow_succ', hsucc]

/-- The constraints over the polynomials of the trace and the preprocessed trace take the
constraints' values on the traces' rows. -/
theorem eval_constraintPoly_root (A : Air F) (logN : Nat) (h : logN ≤ twoAdicity F)
    (trace : Array F) (pis : List F) (T Tp : Nat → F[X]) (hT : TraceOn logN A.width trace T)
    (hTp : TraceOn logN A.preprocessedWidth A.preprocessed Tp) (c : Expr F)
    (hc : c.colsBelow A.width A.preprocessedWidth A.preprocessedNextWidth = true) (i : Nat)
    (hi : i < 2 ^ logN) :
    (constraintPoly (2 ^ logN) (twoAdicGen logN) T Tp pis c).eval (twoAdicGen logN ^ i) =
      c.eval (A.traceRow logN trace pis i) := by
  have hp := BaseField.isPrimitiveRoot_twoAdicGen (F := F) logN h
  have hsucc : twoAdicGen (F := F) logN ^ (i + 1) =
      twoAdicGen logN ^ ((i + 1) % 2 ^ logN) := by
    conv_lhs => rw [← Nat.mod_add_div (i + 1) (2 ^ logN)]
    rw [pow_add, pow_mul, hp.pow_eq_one, one_pow, mul_one]
  have hnw : A.preprocessedNextWidth ≤ A.preprocessedWidth := by
    unfold Air.preprocessedNextWidth; split <;> omega
  rw [constraintPoly]
  refine Expr.eval_hom (eval (twoAdicGen logN ^ i)) (fun _ _ ↦ eval_add)
    (fun a b ↦ eval_sub a b _) (fun _ _ ↦ eval_mul) A.width A.preprocessedWidth
    A.preprocessedNextWidth _ (A.traceRow logN trace pis i)
    (fun j hj ↦ hT j hj i hi) (fun j hj ↦ eval_comp_root logN h _ trace T hT j hj i)
    (fun j hj ↦ hTp j hj i hi)
    (fun j hj ↦ eval_comp_root logN h _ _ Tp hTp j (by omega) i)
    (fun _ ↦ eval_C) (fun _ ↦ eval_C) ?_ ?_ ?_ c hc
  · exact eval_firstSel_root logN i h hi
  · change (lastSel (2 ^ logN) (twoAdicGen logN)).eval (twoAdicGen logN ^ i) =
      (if i + 1 = 2 ^ logN then ((2 ^ logN : Nat) : F) * twoAdicGen logN else 0)
    have hm : (i + 1) % 2 ^ logN < 2 ^ logN := Nat.mod_lt _ (Nat.two_pow_pos _)
    rw [lastSel, eval_mul, eval_C, eval_comp, eval_mul, eval_C, eval_X, ← pow_succ', hsucc,
      eval_firstSel_root logN _ h hm]
    by_cases hl : i + 1 = 2 ^ logN
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hl),
        ite_eq_left_of_eq_true _ _ (eq_true (by rw [hl, Nat.mod_self])), mul_comm]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hl),
        ite_eq_right_of_eq_false _ _ (eq_false (by rw [Nat.mod_eq_of_lt (by omega)]; omega)),
        mul_zero]
  · change (X - C (twoAdicGen logN)⁻¹ : F[X]).eval (twoAdicGen logN ^ i) =
      twoAdicGen logN ^ i - (twoAdicGen logN)⁻¹
    rw [eval_sub, eval_X, eval_C]

/-- The trace domain's vanishing polynomial `Z_H = Xⁿ - 1`. -/
noncomputable abbrev zH (n : Nat) : F[X] := X ^ n - C 1

/-- A constraint that vanishes on the trace domain, divided by `Z_H`. -/
noncomputable def quotientPoly (logN : Nat) (T Tp : Nat → F[X]) (pis : List F) (c : Expr F) :
    F[X] :=
  constraintPoly (2 ^ logN) (twoAdicGen logN) T Tp pis c /ₘ zH (2 ^ logN)

/-- `Z_H` is monic. -/
theorem zH_monic (logN : Nat) : (zH (2 ^ logN) : F[X]).Monic :=
  monic_X_pow_sub_C 1 (Nat.two_pow_pos logN).ne'

/-- A polynomial vanishing on `⟨ω⟩` is `Z_H` times its quotient. -/
theorem eq_zH_mul (logN : Nat) (h : logN ≤ twoAdicity F) (p : F[X])
    (hp : ∀ i < 2 ^ logN, p.eval (twoAdicGen logN ^ i) = 0) : p = zH (2 ^ logN) *
    (p /ₘ zH (2 ^ logN)) := by
  have hr : p %ₘ zH (2 ^ logN) = 0 := by
    have hpr := BaseField.isPrimitiveRoot_twoAdicGen (F := F) logN h
    refine eq_zero_of_degree_lt_of_eval_index_eq_zero (Finset.range (2 ^ logN))
      (v := fun i ↦ twoAdicGen logN ^ i) (fun i hi j hj hij ↦ ?_) ?_ (fun i hi ↦ ?_)
    · exact hpr.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
    · rw [Finset.card_range]
      have := degree_modByMonic_lt p (zH_monic logN)
      rwa [degree_X_pow_sub_C (Nat.two_pow_pos logN)] at this
    · have e := congrArg (eval (twoAdicGen logN ^ i)) (modByMonic_add_div p (zH (2 ^ logN)))
      rw [eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_C, ← pow_mul, Nat.mul_comm,
        pow_mul, hpr.pow_eq_one, one_pow, sub_self, zero_mul, add_zero,
        hp i (Finset.mem_range.mp hi)] at e
      exact e
  have := modByMonic_add_div p (zH (2 ^ logN))
  rw [hr, zero_add] at this
  exact this.symm

/-- The trace polynomials have degree below `n`. -/
def TraceDeg (logN : Nat) (T : Nat → F[X]) : Prop := ∀ j, (T j).natDegree ≤ 2 ^ logN - 1

/-- A satisfied constraint is `Z_H` times its quotient. -/
theorem constraintPoly_eq (A : Air F) (logN : Nat) (h : logN ≤ twoAdicity F) (trace : Array F)
    (pis : List F) (T Tp : Nat → F[X]) (hT : TraceOn logN A.width trace T)
    (hTp : TraceOn logN A.preprocessedWidth A.preprocessed Tp)
    (hsat : A.ConstraintsVanish logN trace pis) (hcols : A.ColsInWidth) (c : Expr F)
    (hc : c ∈ A.constraints) :
    constraintPoly (2 ^ logN) (twoAdicGen logN) T Tp pis c =
      zH (2 ^ logN) * quotientPoly logN T Tp pis c :=
  eq_zH_mul logN h _ fun i hi ↦ by
    rw [eval_constraintPoly_root A logN h trace pis T Tp hT hTp c (hcols c hc) i hi,
      hsat c hc i hi]

/-- A constraint's quotient has degree below `k n`. -/
theorem natDegree_quotientPoly (A : Air F) (logN : Nat) (pis : List F) (T Tp : Nat → F[X])
    (hTd : TraceDeg logN T) (hTpd : TraceDeg logN Tp) (hdeg : A.DegreeFits logN) (c : Expr F)
    (hc : c ∈ A.constraints) :
    (quotientPoly logN T Tp pis c).natDegree < 2 ^ (logN + A.logQuotientChunks) := by
  rw [quotientPoly, natDegree_divByMonic _ (zH_monic logN), natDegree_X_pow_sub_C]
  have h1 := natDegree_constraintPoly (2 ^ logN) (twoAdicGen logN) T Tp pis c hTd hTpd
  have h2 := hdeg c hc
  have h3 := Nat.two_pow_pos (logN + A.logQuotientChunks)
  omega

/-! ### Horner's rule -/

/-- `∑ₖ lₖ aᴷ⁻¹⁻ᵏ` by Horner's rule, `K` the length of `l`. -/
def horner {R : Type*} [Add R] [Mul R] [Zero R] (l : List R) (a : R) : R :=
  l.foldl (fun acc v ↦ acc * a + v) 0

/-- Horner's rule from an accumulator. -/
theorem foldl_horner {R : Type*} [CommRing R] (a : R) :
    ∀ (l : List R) (x : R), l.foldl (fun acc v ↦ acc * a + v) x = x * a ^ l.length + horner l a
  | [], x => by rw [List.foldl_nil, List.length_nil, pow_zero, mul_one, horner, List.foldl_nil,
      add_zero]
  | v :: l, x => by
    have h1 := foldl_horner a l (x * a + v)
    have h2 := foldl_horner a l (0 * a + v)
    simp only [horner, List.foldl_cons, List.length_cons] at h1 h2 ⊢
    rw [h1, h2, pow_succ]
    ring

/-- Ring maps commute with Horner's rule. -/
theorem horner_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (l : List R) (a : R) :
    f (horner l a) = horner (l.map f) (f a) := by
  suffices h : ∀ (l : List R) (x : R), f (l.foldl (fun acc v ↦ acc * a + v) x) =
      (l.map f).foldl (fun acc v ↦ acc * f a + v) (f x) by
    rw [horner, horner, h, map_zero]
  intro l
  induction l with
  | nil => intro x; rfl
  | cons v l ih => intro x; rw [List.foldl_cons, ih, map_add, map_mul]; rfl

/-- Horner's rule is linear: scaling every term scales the result. -/
theorem horner_mul {R : Type*} [CommRing R] (l : List R) (a s : R) :
    horner (l.map (· * s)) a = horner l a * s := by
  suffices h : ∀ (l : List R) (x : R), (l.map (· * s)).foldl (fun acc v ↦ acc * a + v) (x * s) =
      l.foldl (fun acc v ↦ acc * a + v) x * s by
    have := h l 0
    rwa [zero_mul] at this
  intro l
  induction l with
  | nil => intro x; rfl
  | cons v l ih =>
    intro x
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, ← ih]
    congr 1
    ring

/-- Horner's rule is the sum of the terms weighted by descending powers. -/
theorem horner_eq_sum {R : Type*} [CommRing R] (a : R) : ∀ l : List R,
    horner l a = ((l.zip ((List.range l.length).map fun k ↦ a ^ (l.length - 1 - k))).map
      fun p ↦ p.1 * p.2).sum
  | [] => rfl
  | v :: l => by
    rw [horner, List.foldl_cons, foldl_horner, horner_eq_sum a l, List.length_cons,
      List.range_succ_eq_map, List.map_cons, List.zip_cons_cons, List.map_cons, List.sum_cons,
      List.map_map]
    congr 2
    · ring_nf
    · have : (fun k ↦ a ^ (l.length + 1 - 1 - k)) ∘ Nat.succ =
          fun k ↦ a ^ (l.length - 1 - k) := by
        funext k
        simp only [Function.comp_apply]
        congr 1
        omega
      rw [this]

/-- Horner's rule in `C a` keeps polynomials below a degree. -/
theorem natDegree_horner {R : Type*} [CommRing R] (N : Nat) (a : R) :
    ∀ (l : List R[X]) (x : R[X]), x.natDegree < N → (∀ p ∈ l, p.natDegree < N) →
      (l.foldl (fun acc v ↦ acc * C a + v) x).natDegree < N
  | [], x, hx, _ => hx
  | v :: l, x, hx, hl => by
    rw [List.foldl_cons]
    refine natDegree_horner N a l _ ?_ (fun p hp ↦ hl p (List.mem_cons_of_mem _ hp))
    refine (natDegree_add_le _ _).trans_lt (max_lt ?_ (hl v List.mem_cons_self))
    exact (natDegree_mul_C_le _ _).trans_lt hx

end Polys
end CompStark.Stark
