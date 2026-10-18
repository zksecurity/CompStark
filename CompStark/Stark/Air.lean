/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompPoly.Fields.KoalaBear.Fast

/-! # AIRs

An AIR is a width and a list of constraints, polynomial expressions in the current row (`cur`), the
next row, the public values and the row selectors, each asserted to vanish on every row. As in
Plonky3, a constraint under `when_first_row`, `when_last_row` or `when_transition` is the
constraint times that selector, and `assert_eq a b` asserts `a - b`.

`Expr.degree` is Plonky3's `degree_multiple`: columns and selectors have degree 1, constants and
public values 0. `Expr.eval` evaluates in any ring that holds the field's constants.
-/

@[expose] public section
namespace CompStark.Stark

local notation "F" => KoalaBear.Fast.Field

/-- A constraint expression. -/
inductive Expr where
  | cur (col : Nat)
  | next (col : Nat)
  | pub (i : Nat)
  | const (c : F)
  | isFirstRow
  | isLastRow
  | isTransition
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)

namespace Expr

instance : Add Expr := ⟨add⟩
instance : Sub Expr := ⟨sub⟩
instance : Mul Expr := ⟨mul⟩

/-- Plonky3's `degree_multiple`. -/
def degree : Expr → Nat
  | cur _ | next _ | isFirstRow | isLastRow | isTransition => 1
  | pub _ | const _ => 0
  | add a b | sub a b => max a.degree b.degree
  | mul a b => a.degree + b.degree

/-- The value of an expression, with the rows, public values and selectors given. -/
structure Env (K : Type*) where
  cur : Nat → K
  next : Nat → K
  pub : Nat → K
  const : F → K
  isFirstRow : K
  isLastRow : K
  isTransition : K

/-- Evaluate an expression in `env`. -/
def eval {K : Type*} [Add K] [Sub K] [Mul K] (env : Env K) : Expr → K
  | cur c => env.cur c
  | next c => env.next c
  | pub i => env.pub i
  | const c => env.const c
  | isFirstRow => env.isFirstRow
  | isLastRow => env.isLastRow
  | isTransition => env.isTransition
  | add a b => eval env a + eval env b
  | sub a b => eval env a - eval env b
  | mul a b => eval env a * eval env b

end Expr

/-- An AIR. -/
structure Air where
  width : Nat
  constraints : List Expr

namespace Air

/-- The largest constraint degree. -/
def maxDegree (A : Air) : Nat := A.constraints.foldl (fun m c ↦ max m c.degree) 0

/-- Plonky3's `get_log_num_quotient_chunks`: `⌈log₂ (max (d, 2) - 1)⌉`. -/
def logQuotientChunks (A : Air) : Nat :=
  let d := max A.maxDegree 2 - 1
  Nat.log2 d.nextPowerOfTwo

end Air

/-- The Fibonacci AIR of Plonky3's tests, on columns `left, right` with public values `a, b, x`:
the first row is `(a, b)`, each next row is `(right, left + right)`, and the last `right` is `x`. -/
def fibonacci : Air where
  width := 2
  constraints :=
    [.isFirstRow * (.cur 0 - .pub 0),
     .isFirstRow * (.cur 1 - .pub 1),
     .isTransition * (.cur 1 - .next 0),
     .isTransition * ((.cur 0 + .cur 1) - .next 1),
     .isLastRow * (.cur 1 - .pub 2)]

end CompStark.Stark
