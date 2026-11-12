/-
Copyright (c) 2026 zkSecurity.
Adapted from Verified-zkEVM/leanerVM (Apache-2.0), revision a9d42bfdae8081a4e16aef1cd8526cdaa2a8f4d6:
LeanerVM.Protocol.Bus and TableSumcheck.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.BusDecomposition

/-! Constraints and bus forms as polynomials in a row's values: committed column `c` is the
variable `c`, preprocessed column `c` the variable `width + c`. Substituting multilinear columns
keeps every variable's degree at most the expression's degree. -/

@[expose] public section

namespace CompStark.Stark.Expr

open CompStark.BinaryFields

/-- An expression as a polynomial in a row's committed and preprocessed values. -/
noncomputable def toPoly (width : ℕ) : Expr K → MvPolynomial ℕ E
  | cur c => .X c
  | prepCur c => .X (width + c)
  | const c => .C (ofK c)
  | add a b => toPoly width a + toPoly width b
  | sub a b => toPoly width a - toPoly width b
  | mul a b => toPoly width a * toPoly width b
  | _ => 0

/-- A current-row expression in a table's columns evaluates as its polynomial. -/
theorem toPoly_eval (width pw : ℕ) (e : Expr K) (he : e.currentRow = true)
    (hcols : e.colsBelow width 0 pw 0 = true) (v p : ℕ → E) :
    MvPolynomial.eval (fun c ↦ if c < width then v c else p (c - width)) (toPoly width e) =
      e.eval (CompStark.Tables.System.envE v p) := by
  induction e with
  | cur c =>
    simp only [colsBelow, decide_eq_true_eq] at hcols
    simp only [toPoly, MvPolynomial.eval_X, hcols, ↓reduceIte]
    rfl
  | prepCur c =>
    simp only [toPoly, MvPolynomial.eval_X, show ¬ width + c < width by omega, ↓reduceIte,
      Nat.add_sub_cancel_left]
    rfl
  | const c => simp only [toPoly, MvPolynomial.eval_C]; rfl
  | add a b ha hb | sub a b ha hb | mul a b ha hb =>
    simp only [currentRow, colsBelow, Bool.and_eq_true] at he hcols
    simp only [toPoly, map_add, map_sub, map_mul, ha he.1 hcols.1, hb he.2 hcols.2]
    rfl
  | _ => simp [currentRow] at he

/-- Substituting multilinear values keeps every variable's degree at most the expression's. -/
theorem toPoly_bind_degreeOf {σ : Type} (width : ℕ) (e : Expr K) (P : ℕ → MvPolynomial σ E) (j : σ)
    (hP : ∀ c, (P c).degreeOf j ≤ 1) : (MvPolynomial.bind₁ P (toPoly width e)).degreeOf j ≤ e.degree := by
  induction e with
  | cur c => simpa only [toPoly, MvPolynomial.bind₁_X_right, degree] using hP c
  | prepCur c => simpa only [toPoly, MvPolynomial.bind₁_X_right, degree] using hP (width + c)
  | const c => simp only [toPoly, MvPolynomial.bind₁_C_right, MvPolynomial.degreeOf_C, Nat.zero_le]
  | add a b ha hb =>
    simpa only [toPoly, map_add, degree] using
      (MvPolynomial.degreeOf_add_le j _ _).trans (max_le_max ha hb)
  | sub a b ha hb =>
    simpa only [toPoly, map_sub, degree] using
      (MvPolynomial.degreeOf_sub_le j _ _).trans (max_le_max ha hb)
  | mul a b ha hb =>
    simpa only [toPoly, map_mul, degree] using
      (MvPolynomial.degreeOf_mul_le j _ _).trans (Nat.add_le_add ha hb)
  | _ => simp only [toPoly, map_zero, MvPolynomial.degreeOf_zero, Nat.zero_le]

end CompStark.Stark.Expr

namespace CompStark.Tables.System

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear

variable (S : System K) (k : ℕ) (α : Fin k → E) (β : E)

/-- A block's form as a polynomial in its table's row values. -/
noncomputable def formPoly (b : Block S.tables.length) : MvPolynomial ℕ E :=
  match b with
  | .interaction t I => .C β - ∑ j : Fin (2 ^ k),
      .C (∏ x : Fin k, eqFactor (α x) (bit j.val x.val)) *
        (.C (ofK (gpow (S.busIndex I.bus))) :: I.tuple.map (Expr.toPoly (S.table t).air.width)).getD j.val 0
  | .nonzero _ c => .X c

/-- The row value of variable `c` of table `t`: committed below the width, preprocessed above. -/
def cellValue (t : Fin S.tables.length) (v p : ℕ → E) (c : ℕ) : E :=
  if c < (S.table t).air.width then v c else p (c - (S.table t).air.width)

/-- A block of a well-formed table evaluates as its polynomial. -/
theorem formPoly_eval (hT : ∀ t, (S.table t).WellFormed) (b : Block S.tables.length)
    (hb : ∀ t c, b = .nonzero t c → c ∈ (S.table t).nonzero)
    (hI : ∀ t I, b = .interaction t I → I ∈ (S.table t).interactions) (v p : ℕ → E) :
    MvPolynomial.eval (S.cellValue (Block.table S b) v p) (S.formPoly k α β b) =
      S.formE k α β b v p := by
  cases b with
  | nonzero t c =>
    have hc := (hT t).2.2.2.2.2.1 c (hb t c rfl)
    simp only [formPoly, formE, MvPolynomial.eval_X, cellValue, Block.table, hc, ↓reduceIte]
  | interaction t I =>
    simp only [formPoly, formE, fingerprintE, map_sub, map_sum, map_mul, MvPolynomial.eval_C]
    apply congrArg (β - ·)
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
    apply congrArg (· * _)
    simp only [encodeE]
    rcases Nat.eq_zero_or_pos j.val with h0 | hpos
    · simp only [h0, List.getD_cons_zero, MvPolynomial.eval_C]
    · obtain ⟨m, hm⟩ : ∃ m, j.val = m + 1 := ⟨j.val - 1, by omega⟩
      simp only [hm, List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_map]
      cases hl : I.tuple[m]? with
      | none => simp only [Option.map_none, Option.getD_none, map_zero]
      | some e =>
        have he := List.mem_of_getElem? hl
        have hwf := (hT t).2.2.2.2.1 I (hI t I rfl) e he
        simp only [Option.map_some, Option.getD_some]
        exact Expr.toPoly_eval _ _ e hwf.1 hwf.2 v p

/-- The largest degree of a table's tuple entries. -/
def tupleDegree (t : Fin S.tables.length) : ℕ :=
  (((S.table t).interactions.flatMap (·.tuple)).map Expr.degree).foldl max 0

/-- A tuple entry's degree is at most its table's tuple degree. -/
theorem le_tupleDegree (t : Fin S.tables.length) (I : Interaction K)
    (hI : I ∈ (S.table t).interactions) (e : Expr K) (he : e ∈ I.tuple) :
    e.degree ≤ S.tupleDegree t := by
  have mem : e.degree ∈ ((S.table t).interactions.flatMap (·.tuple)).map Expr.degree :=
    List.mem_map.mpr ⟨e, List.mem_flatMap.mpr ⟨I, hI, he⟩, rfl⟩
  have bound (xs : List ℕ) (a x : ℕ) (hx : x ≤ a ∨ x ∈ xs) : x ≤ xs.foldl max a := by
    induction xs generalizing a with
    | nil => exact hx.resolve_right (List.not_mem_nil)
    | cons y xs ih =>
      apply ih
      rcases hx with h | h
      · exact Or.inl (h.trans (le_max_left _ _))
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inl (le_max_right _ _)
        · exact Or.inr h
  exact bound _ _ _ (Or.inr mem)

/-- Substituting multilinear values into a block's form keeps every degree at most its table's
tuple degree, and at least one. -/
theorem formPoly_bind_degreeOf {σ : Type} (b : Block S.tables.length)
    (hI : ∀ t I, b = .interaction t I → I ∈ (S.table t).interactions)
    (P : ℕ → MvPolynomial σ E) (j : σ) (hP : ∀ c, (P c).degreeOf j ≤ 1) :
    (MvPolynomial.bind₁ P (S.formPoly k α β b)).degreeOf j ≤
      max 1 (S.tupleDegree (Block.table S b)) := by
  classical
  cases b with
  | nonzero t c =>
    simp only [formPoly, MvPolynomial.bind₁_X_right]
    exact (hP c).trans (le_max_left _ _)
  | interaction t I =>
    simp only [formPoly, map_sub, MvPolynomial.bind₁_C_right, map_sum, map_mul]
    refine (MvPolynomial.degreeOf_sub_le j _ _).trans (max_le (by simp) ?_)
    refine (MvPolynomial.degreeOf_sum_le j _ _).trans (Finset.sup_le fun x _ ↦ ?_)
    refine (MvPolynomial.degreeOf_mul_le j _ _).trans ?_
    rw [MvPolynomial.degreeOf_C, zero_add]
    rcases Nat.eq_zero_or_pos x.val with h0 | hpos
    · simp only [h0, List.getD_cons_zero, MvPolynomial.bind₁_C_right, MvPolynomial.degreeOf_C,
        Nat.zero_le]
    · obtain ⟨m, hm⟩ : ∃ m, x.val = m + 1 := ⟨x.val - 1, by omega⟩
      simp only [hm, List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_map]
      cases hl : I.tuple[m]? with
      | none => simp only [Option.map_none, Option.getD_none, map_zero, MvPolynomial.degreeOf_zero,
          Nat.zero_le]
      | some e =>
        simp only [Option.map_some, Option.getD_some]
        exact (Expr.toPoly_bind_degreeOf _ e P j hP).trans ((S.le_tupleDegree t I (hI t I rfl) e
          (List.mem_of_getElem? hl)).trans (le_max_right _ _))

end CompStark.Tables.System
