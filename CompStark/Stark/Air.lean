/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Init

/-! # AIRs

An AIR is a width and a list of constraints, polynomial expressions in the current row (`cur`), the
next row, the current and next rows of a preprocessed trace, the public values and the row
selectors, each asserted to vanish on every row. As in Plonky3, a constraint under
`when_first_row`, `when_last_row` or `when_transition` is the constraint times that selector, and
`assert_eq a b` asserts `a - b`.

The preprocessed trace is part of the AIR (Plonky3's `preprocessed_trace`): fixed columns of the
trace's height that the verifier knows by their commitment. The proof opens them at the next row
only when the AIR declares it reads that row (Plonky3's `preprocessed_next_row_columns`).

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
  | prepCur (col : Nat)
  | prepNext (col : Nat)
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
  | cur _ | next _ | prepCur _ | prepNext _ | isFirstRow | isLastRow => 1
  | isTransition | pub _ | const _ => 0
  | add a b | sub a b => max a.degree b.degree
  | mul a b => a.degree + b.degree

/-- The value of an expression, with the rows, public values and selectors given. -/
structure Env (F : Type) (K : Type*) where
  cur : Nat → K
  next : Nat → K
  prepCur : Nat → K
  prepNext : Nat → K
  pub : Nat → K
  const : F → K
  isFirstRow : K
  isLastRow : K
  isTransition : K

/-- Evaluate an expression in `env`. -/
def eval {K : Type*} [Add K] [Sub K] [Mul K] (env : Env F K) : Expr F → K
  | cur c => env.cur c
  | next c => env.next c
  | prepCur c => env.prepCur c
  | prepNext c => env.prepNext c
  | pub i => env.pub i
  | const c => env.const c
  | isFirstRow => env.isFirstRow
  | isLastRow => env.isLastRow
  | isTransition => env.isTransition
  | add a b => eval env a + eval env b
  | sub a b => eval env a - eval env b
  | mul a b => eval env a * eval env b

/-- Every column `e` reads is below `w`, every current preprocessed column below `pw` and every
next preprocessed column below `pwNext`. -/
def colsBelow (w pw pwNext : Nat) : Expr F → Bool
  | cur c | next c => c < w
  | prepCur c => c < pw
  | prepNext c => c < pwNext
  | pub _ | const _ | isFirstRow | isLastRow | isTransition => true
  | add a b | sub a b | mul a b => colsBelow w pw pwNext a && colsBelow w pw pwNext b

theorem colsBelow_mono {w pw pwNext pw' pwNext' : Nat} (h1 : pw ≤ pw') (h2 : pwNext ≤ pwNext') :
    ∀ e : Expr F, e.colsBelow w pw pwNext = true → e.colsBelow w pw' pwNext' = true
  | cur _, h | next _, h | pub _, h | const _, h | isFirstRow, h | isLastRow, h
  | isTransition, h => h
  | prepCur c, h => by
    simp only [colsBelow, decide_eq_true_eq] at h ⊢
    omega
  | prepNext c, h => by
    simp only [colsBelow, decide_eq_true_eq] at h ⊢
    omega
  | add a b, h | sub a b, h | mul a b, h => by
    simp only [colsBelow, Bool.and_eq_true] at h ⊢
    exact ⟨colsBelow_mono h1 h2 a h.1, colsBelow_mono h1 h2 b h.2⟩

end Expr

/-- An AIR over the field `F`: the trace's width, the number of public values, the constraints,
and the preprocessed trace, row-major, of `preprocessedWidth` columns, opened at the next row if
`preprocessedNextRow`. -/
structure Air (F : Type) where
  width : Nat
  numPublicValues : Nat
  constraints : List (Expr F)
  preprocessedWidth : Nat := 0
  preprocessed : Array F := #[]
  preprocessedNextRow : Bool := true

namespace Air

variable {F : Type}

/-- The proof opens the preprocessed trace at the next row: it has columns and the AIR reads its
next row (Plonky3's `preprocessed_next_row_columns` is not empty). -/
def opensPreprocessedNext (A : Air F) : Bool := 0 < A.preprocessedWidth && A.preprocessedNextRow

/-- The width of the preprocessed trace's next row as opened: `0` unless it is opened. -/
def preprocessedNextWidth (A : Air F) : Nat :=
  if A.opensPreprocessedNext then A.preprocessedWidth else 0

/-- Every constraint reads columns below the widths, and the next preprocessed row only when it
is opened. -/
def ColsInWidth (A : Air F) : Prop :=
  ∀ c ∈ A.constraints, c.colsBelow A.width A.preprocessedWidth A.preprocessedNextWidth

theorem preprocessedNextWidth_le (A : Air F) : A.preprocessedNextWidth ≤ A.preprocessedWidth := by
  unfold preprocessedNextWidth
  split <;> omega

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
  numPublicValues := 3
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
  numPublicValues := 3
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
  numPublicValues := 0
  constraints := (List.range w).map fun j ↦
    .isTransition * ((.cur j * .cur j * .cur j + .cur ((j + 1) % w)) - .next j)

/-- Two columns `a, b` and two preprocessed columns `p = i mod 2`, `s = (i + 1) mod 6` on row `i`
of `2 ^ logN`, with public values `x, y`: the first row is `(x, y)`, each next row is
`(b, p a b + s (a + b))` (Plonky3's `MulFibPAir`, with public values). With `nextRow` the AIR also
reads the next preprocessed row, asserting `p' + p = 1` on transitions; without, it is opened at
`ζ` only. -/
def mulFib {F : Type} [NatCast F] [One F] (logN : Nat) (nextRow : Bool) : Air F where
  width := 2
  numPublicValues := 2
  constraints :=
    [.isFirstRow * (.cur 0 - .pub 0),
     .isFirstRow * (.cur 1 - .pub 1),
     .isTransition * (.cur 1 - .next 0),
     .isTransition * ((.prepCur 0 * .cur 0 * .cur 1 + .prepCur 1 * (.cur 0 + .cur 1)) - .next 1)] ++
    if nextRow then [.isTransition * ((.prepNext 0 + .prepCur 0) - .const 1)] else []
  preprocessedWidth := 2
  preprocessed := Array.ofFn (n := 2 ^ logN * 2) fun k ↦
    if k.val % 2 = 0 then ((k.val / 2 % 2 : Nat) : F) else ((k.val / 2 + 1) % 6 : Nat)
  preprocessedNextRow := nextRow

end CompStark.Stark
