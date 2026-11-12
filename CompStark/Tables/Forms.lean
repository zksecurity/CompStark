/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Decomposition
public import CompStark.Multilinear.Algebra.Mle

/-! A block's form at challenge-field column values, and the tables the bus opens directly.

`formE` evaluates a block at extension-field values of a row's committed and preprocessed
columns; on the Boolean rows it is the base-field form (`blockForm_eq_formE`). A table is opened
directly when it has no constraints, no nonzero columns and no padding, and every tuple entry is a
column, a preprocessed column or a constant: its leaves are affine in its columns, so the extension
of a block of it is its form at the columns' extensions (`mle_formE_direct`). Every other table's
forms go to the table sumcheck. -/

@[expose] public section

namespace CompStark.Stark.Expr

variable {F : Type}

/-- The expression is a column, a preprocessed column or a constant. -/
def atomic : Expr F → Bool
  | cur _ | prepCur _ | const _ => true
  | _ => false

end CompStark.Stark.Expr

namespace CompStark.Tables.System

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear

/-- The environment reading committed values `v` and preprocessed values `p` in the challenge
field. -/
def envE (v p : ℕ → E) : Expr.Env K E where
  cur := v
  next _ := 0
  prepCur := p
  prepNext _ := 0
  periodic _ := 0
  pub _ := 0
  const := ofK
  isFirstRow := 0
  isLastRow := 0
  isTransition := 0

/-- Evaluating a current-row expression commutes with the embedding into the challenge field. -/
theorem eval_ofK (env : Expr.Env K K) (hconst : ∀ c, env.const c = c) (e : Expr K)
    (he : e.currentRow = true) :
    ofK (e.eval env) = e.eval (envE (fun c ↦ ofK (env.cur c)) (fun c ↦ ofK (env.prepCur c))) := by
  induction e with
  | cur c | prepCur c => rfl
  | const c => simp only [Expr.eval, hconst]; rfl
  | next _ | prepNext _ | periodic _ | pub _ | isFirstRow | isLastRow | isTransition =>
    simp [Expr.currentRow] at he
  | add a b ha hb =>
    simp only [Expr.currentRow, Bool.and_eq_true] at he
    simp only [Expr.eval, ← ha he.1, ← hb he.2]; exact ofK_add _ _
  | sub a b ha hb =>
    simp only [Expr.currentRow, Bool.and_eq_true] at he
    simp only [Expr.eval, ← ha he.1, ← hb he.2]; exact map_sub (algebraMap K E) _ _
  | mul a b ha hb =>
    simp only [Expr.currentRow, Bool.and_eq_true] at he
    simp only [Expr.eval, ← ha he.1, ← hb he.2]; exact ofK_mul _ _

variable (S : System K) (L : Layout S.tables.length)

/-- The separator of bus `i` followed by a challenge-field tuple, padded with zeros. -/
def encodeE (k i : ℕ) (tuple : List E) : Fin (2 ^ k) → E :=
  fun j ↦ (ofK (gpow i) :: tuple).getD j.val 0

/-- Embedding a base-field encoding is the challenge-field encoding of the embedded tuple. -/
theorem encodeE_ofK (k i : ℕ) (tuple : List K) (j : Fin (2 ^ k)) :
    ofK (encode k i tuple)[j] = encodeE k i (tuple.map ofK) j := by
  simp only [encode, Fin.getElem_fin, Vector.getElem_ofFn, encodeE, ← List.map_cons]
  have zero : (0 : E) = ofK 0 := (map_zero (algebraMap K E)).symm
  rw [zero, List.getD_map]

variable (k : ℕ) (α : Fin k → E) (β : E)

/-- A block's form at challenge-field values `v` of its committed and `p` of its preprocessed
columns. -/
def formE (b : Block S.tables.length) (v p : ℕ → E) : E :=
  match b with
  | .interaction _ I => β - fingerprintE k α (encodeE k (S.busIndex I.bus) (I.tuple.map (Expr.eval (envE v p))))
  | .nonzero _ c => v c

/-- On a row, the base-field form is the challenge-field form of the embedded row. -/
theorem blockForm_eq_formE (b : Block S.tables.length) (env : Expr.Env K K) (row : ℕ → K)
    (hrow : ∀ c, env.cur c = row c) (hconst : ∀ c, env.const c = c)
    (hlocal : ∀ t I, b = .interaction t I → ∀ e ∈ I.tuple, e.currentRow = true) :
    S.blockForm k α β b env row =
      S.formE k α β b (fun c ↦ ofK (row c)) (fun c ↦ ofK (env.prepCur c)) := by
  cases b with
  | nonzero t c => rfl
  | interaction t I =>
    have hl : List.map (ofK ∘ Expr.eval env) I.tuple =
        List.map (Expr.eval (envE (fun c ↦ ofK (row c)) (fun c ↦ ofK (env.prepCur c)))) I.tuple := by
      apply List.map_congr_left
      intro e he
      simp only [Function.comp_apply]
      rw [eval_ofK env hconst e (hlocal t I rfl e he)]
      have hv : (fun c ↦ ofK (env.cur c)) = fun c ↦ ofK (row c) := funext fun c ↦ by rw [hrow c]
      rw [hv]
    simp only [blockForm, formE, fingerprint]
    congr 2
    funext j
    rw [encodeE_ofK, List.map_map, hl]

end CompStark.Tables.System
