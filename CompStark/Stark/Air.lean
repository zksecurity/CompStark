/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Init

/-! # AIRs

An AIR is a width and a list of constraints, polynomial expressions in the current row (`cur`), the
next row, the public values and the row selectors, each asserted to vanish on every row. As in
Plonky3, a constraint under `when_first_row`, `when_last_row` or `when_transition` is the
constraint times that selector, and `assert_eq a b` asserts `a - b`.

`Expr.degree` is Plonky3's `degree_multiple`: columns and the first- and last-row selectors have
degree 1, the transition selector, constants and public values 0. `Expr.eval` evaluates in any
ring that holds the field's constants.
-/

@[expose] public section
namespace CompStark.Stark

/-- A constraint expression over the field `F`. -/
inductive Expr (F : Type) where
  | cur (col : Nat)
  | next (col : Nat)
  | pub (i : Nat)
  | const (c : F)
  | isFirstRow
  | isLastRow
  | isTransition
  | add (a b : Expr F)
  | sub (a b : Expr F)
  | mul (a b : Expr F)

namespace Expr

variable {F : Type}

instance : Add (Expr F) := ⟨add⟩
instance : Sub (Expr F) := ⟨sub⟩
instance : Mul (Expr F) := ⟨mul⟩

/-- Plonky3's `degree_multiple`. -/
def degree : Expr F → Nat
  | cur _ | next _ | isFirstRow | isLastRow => 1
  | isTransition | pub _ | const _ => 0
  | add a b | sub a b => max a.degree b.degree
  | mul a b => a.degree + b.degree

/-- The value of an expression, with the rows, public values and selectors given. -/
structure Env (F : Type) (K : Type*) where
  cur : Nat → K
  next : Nat → K
  pub : Nat → K
  const : F → K
  isFirstRow : K
  isLastRow : K
  isTransition : K

/-- Evaluate an expression in `env`. -/
def eval {K : Type*} [Add K] [Sub K] [Mul K] (env : Env F K) : Expr F → K
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

/-- Every column `e` reads is below `w`. -/
def colsBelow (w : Nat) : Expr F → Bool
  | cur c | next c => c < w
  | pub _ | const _ | isFirstRow | isLastRow | isTransition => true
  | add a b | sub a b | mul a b => colsBelow w a && colsBelow w b

end Expr

/-- An AIR over the field `F`. -/
structure Air (F : Type) where
  width : Nat
  constraints : List (Expr F)

namespace Air

variable {F : Type}

/-- Every constraint reads columns below the width. -/
def ColsInWidth (A : Air F) : Prop := ∀ c ∈ A.constraints, c.colsBelow A.width

/-- The largest constraint degree. -/
def maxDegree (A : Air F) : Nat := A.constraints.foldl (fun m c ↦ max m c.degree) 0

/-- Plonky3's `get_log_num_quotient_chunks`: `⌈log₂ (max (d, 2) - 1)⌉`. -/
def logQuotientChunks (A : Air F) : Nat :=
  let d := max A.maxDegree 2 - 1
  Nat.log2 d.nextPowerOfTwo

end Air

/-- The Fibonacci AIR of Plonky3's tests, on columns `left, right` with public values `a, b, x`:
the first row is `(a, b)`, each next row is `(right, left + right)`, and the last `right` is `x`. -/
def fibonacci {F : Type} : Air F where
  width := 2
  constraints :=
    [.isFirstRow * (.cur 0 - .pub 0),
     .isFirstRow * (.cur 1 - .pub 1),
     .isTransition * (.cur 1 - .next 0),
     .isTransition * ((.cur 0 + .cur 1) - .next 1),
     .isLastRow * (.cur 1 - .pub 2)]

/-- An AIR on columns `x, y` with public values `a, b, c`: the first row is `(a, b)`, each next row
is `(x³ + y, y + 1)`, and the last `x` is `c`. Its transition has degree 3, so its quotient has two
chunks. -/
def cube {F : Type} [One F] : Air F where
  width := 2
  constraints :=
    [.isFirstRow * (.cur 0 - .pub 0),
     .isFirstRow * (.cur 1 - .pub 1),
     .isTransition * ((.cur 0 * .cur 0 * .cur 0 + .cur 1) - .next 0),
     .isTransition * ((.cur 1 + .const 1) - .next 1),
     .isLastRow * (.cur 0 - .pub 2)]

/-- `w` columns, each next row `x'ⱼ = xⱼ³ + xⱼ₊₁` (indices mod `w`), no public values: the
representative wide AIR of the benchmarks, with degree-3 transitions and a two-chunk quotient. -/
def wide {F : Type} (w : Nat) : Air F where
  width := w
  constraints := (List.range w).map fun j ↦
    .isTransition * ((.cur j * .cur j * .cur j + .cur ((j + 1) % w)) - .next j)

end CompStark.Stark
