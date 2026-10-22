/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Init
public import Mathlib.Data.List.GetD

/-! # AIRs

An AIR is a width and a list of constraints, polynomial expressions in the current row (`cur`), the
next row, the current and next rows of a preprocessed trace, the periodic columns, the public
values and the row selectors, each asserted to vanish on every row. As in Plonky3, a constraint
under `when_first_row`, `when_last_row` or `when_transition` is the constraint times that
selector, and `assert_eq a b` asserts `a - b`.

The preprocessed trace is part of the AIR (Plonky3's `preprocessed_trace`): fixed columns of the
trace's height that the verifier knows by their commitment. The proof opens them at the next row
only when the AIR declares it reads that row (Plonky3's `preprocessed_next_row_columns`).

A periodic column (Plonky3's `periodic_columns`) is one period of values, of a length `p` that is
a power of two dividing the trace's height `n`: on row `i` it reads value `i mod p`. It is part
of the AIR, neither committed nor opened: as a polynomial it is `f(Xⁿᐟᵖ)`, `f` of degree below `p`
through the period's values on the subgroup of order `p`, of degree `n - n / p`.

An AIR may declare lookups (`Lookup`, Plonky3's LogUp lookups): tuples of expressions with signed
multiplicities, balanced inside the AIR or across the AIRs of a batch on a named bus. Only the
batch STARK proves them (`CompStark/Lookup/`); `uni-stark` ignores them, as Plonky3's does.

`Expr.degree` is Plonky3's `degree_multiple`: columns and the first- and last-row selectors have
degree 1, the transition selector, constants and public values 0. `Expr.degBound` is Plonky3's
`poly_degree`, a constraint's degree as a polynomial on a trace domain of size `n`. Plonky3 sizes
the quotient by `degree` without periodic columns and by `degBound` with them
(`Air.logQuotientChunks`). `Expr.eval` evaluates in any ring that holds the field's constants.
-/

@[expose] public section
namespace CompStark.Stark

/-- A constraint expression over the field `F`. -/
inductive Expr (F : Type) where
  | cur (col : Nat)
  | next (col : Nat)
  | prepCur (col : Nat)
  | prepNext (col : Nat)
  | periodic (i : Nat)
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
  | cur _ | next _ | prepCur _ | prepNext _ | periodic _ | isFirstRow | isLastRow => 1
  | isTransition | pub _ | const _ => 0
  | add a b | sub a b => max a.degree b.degree
  | mul a b => a.degree + b.degree

/-- A bound on the degree of an expression as a polynomial on a trace domain of size `n`, the
periodic column `i` of degree `periodicDegree i` (Plonky3's `poly_degree`): the columns and the
first- and last-row selectors have degree `n - 1`, the transition selector `1`. -/
def degBound (n : Nat) (periodicDegree : Nat → Nat) : Expr F → Nat
  | cur _ | next _ | prepCur _ | prepNext _ | isFirstRow | isLastRow => n - 1
  | periodic i => periodicDegree i
  | isTransition => 1
  | pub _ | const _ => 0
  | add a b | sub a b => max (a.degBound n periodicDegree) (b.degBound n periodicDegree)
  | mul a b => a.degBound n periodicDegree + b.degBound n periodicDegree

/-- The value of an expression, with the rows, public values and selectors given. -/
structure Env (F : Type) (K : Type*) where
  cur : Nat → K
  next : Nat → K
  prepCur : Nat → K
  prepNext : Nat → K
  periodic : Nat → K
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
  | periodic i => env.periodic i
  | pub i => env.pub i
  | const c => env.const c
  | isFirstRow => env.isFirstRow
  | isLastRow => env.isLastRow
  | isTransition => env.isTransition
  | add a b => eval env a + eval env b
  | sub a b => eval env a - eval env b
  | mul a b => eval env a * eval env b

/-- Every current column `e` reads is below `w`, every next column below `wNext`, every current
preprocessed column below `pw` and every next preprocessed column below `pwNext`. -/
def colsBelow (w wNext pw pwNext : Nat) : Expr F → Bool
  | cur c => c < w
  | next c => c < wNext
  | prepCur c => c < pw
  | prepNext c => c < pwNext
  | periodic _ | pub _ | const _ | isFirstRow | isLastRow | isTransition => true
  | add a b | sub a b | mul a b => colsBelow w wNext pw pwNext a && colsBelow w wNext pw pwNext b

theorem colsBelow_mono {w wNext pw pwNext wNext' pw' pwNext' : Nat} (h0 : wNext ≤ wNext')
    (h1 : pw ≤ pw') (h2 : pwNext ≤ pwNext') :
    ∀ e : Expr F, e.colsBelow w wNext pw pwNext = true → e.colsBelow w wNext' pw' pwNext' = true
  | cur _, h | periodic _, h | pub _, h | const _, h | isFirstRow, h | isLastRow, h
  | isTransition, h => h
  | next c, h | prepCur c, h | prepNext c, h => by
    simp only [colsBelow, decide_eq_true_eq] at h ⊢
    omega
  | add a b, h | sub a b, h | mul a b, h => by
    simp only [colsBelow, Bool.and_eq_true] at h ⊢
    exact ⟨colsBelow_mono h0 h1 h2 a h.1, colsBelow_mono h0 h1 h2 b h.2⟩

end Expr

/-- A lookup of an AIR (Plonky3's `Lookup` without exclusive flags): tuples of expressions, each
with a signed multiplicity, positive for a receive and negative for a send. A local lookup
(`bus = none`) balances inside its AIR; a global one balances with every lookup of the batch on
the bus of its name. `countWeight` bounds the magnitude of its multiplicities on a row (Plonky3's
`count_weight`), which the verifier's multiplicity bound trusts the AIR to enforce. -/
structure Lookup (F : Type) where
  bus : Option String
  tuples : List (List (Expr F) × Expr F)
  countWeight : Nat

/-- An AIR over the field `F`: the trace's width, the number of public values, the constraints,
the trace opened at the next row if `mainNextRow`, the preprocessed trace, row-major, of
`preprocessedWidth` columns, opened at the next row if `preprocessedNextRow`, the periodic
columns, one period each, and the lookups in Plonky3's order: the local lookups, then the global
interactions, one tuple each, each in the order the AIR emits them. -/
structure Air (F : Type) where
  width : Nat
  numPublicValues : Nat
  constraints : List (Expr F)
  mainNextRow : Bool := true
  preprocessedWidth : Nat := 0
  preprocessed : Array F := #[]
  preprocessedNextRow : Bool := true
  periodic : List (List F) := []
  lookups : List (Lookup F) := []

namespace Air

variable {F : Type}

/-- The width of the trace's next row as opened: `0` unless the AIR reads it (Plonky3's
`main_next_row_columns` is not empty). -/
def mainNextWidth (A : Air F) : Nat := if A.mainNextRow then A.width else 0

/-- The proof opens the preprocessed trace at the next row: it has columns and the AIR reads its
next row (Plonky3's `preprocessed_next_row_columns` is not empty). -/
def opensPreprocessedNext (A : Air F) : Bool := 0 < A.preprocessedWidth && A.preprocessedNextRow

/-- The width of the preprocessed trace's next row as opened: `0` unless it is opened. -/
def preprocessedNextWidth (A : Air F) : Nat :=
  if A.opensPreprocessedNext then A.preprocessedWidth else 0

/-- Every constraint reads columns below the widths, and the next rows only when they are
opened. -/
def ColsInWidth (A : Air F) : Prop :=
  ∀ c ∈ A.constraints,
    c.colsBelow A.width A.mainNextWidth A.preprocessedWidth A.preprocessedNextWidth

theorem mainNextWidth_le (A : Air F) : A.mainNextWidth ≤ A.width := by
  unfold mainNextWidth
  split <;> omega

theorem preprocessedNextWidth_le (A : Air F) : A.preprocessedNextWidth ≤ A.preprocessedWidth := by
  unfold preprocessedNextWidth
  split <;> omega

/-- Periodic column `i`, empty if there is none. -/
def periodicColumn (A : Air F) (i : Nat) : List F := A.periodic.getD i []

/-- The periodic columns fit a trace of `2 ^ logN` rows: each period is a power of two dividing
the height (Plonky3's `PeriodicColumns::new`). -/
def periodicFits (A : Air F) (logN : Nat) : Bool :=
  A.periodic.all fun c ↦ c.length == 2 ^ Nat.log2 c.length && Nat.log2 c.length ≤ logN

/-- The degree `n - n / p` of periodic column `i` of period `p` as a polynomial on a trace domain
of size `n`. -/
def periodicDegree (A : Air F) (n i : Nat) : Nat := n - n / (A.periodicColumn i).length

/-- The largest constraint degree. -/
def maxDegree (A : Air F) : Nat := A.constraints.foldl (fun m c ↦ max m c.degree) 0

/-- The largest constraint degree as a polynomial on a trace domain of size `n` (`degBound`). -/
def maxDegBound (A : Air F) (n : Nat) : Nat :=
  A.constraints.foldl (fun m c ↦ max m (c.degBound n (A.periodicDegree n))) 0

/-- The constraint degree `d` that sizes the quotient of a trace of `2 ^ logN` rows: the largest
`degree` without periodic columns; with them, the largest polynomial degree `D` in multiples of
`n - 1`, `⌈(D - 1) / (n - 1)⌉`, or `0` for `D = 0` (Plonky3's
`get_max_constraint_degree_extension`). -/
def constraintDegree (A : Air F) (logN : Nat) : Nat :=
  if A.periodic = [] then A.maxDegree else
    let D := A.maxDegBound (2 ^ logN)
    let denom := max (2 ^ logN - 1) 1
    if D = 0 then 0 else (D - 1 + denom - 1) / denom

/-- Plonky3's `get_log_num_quotient_chunks` for a trace of `2 ^ logN` rows:
`⌈log₂ (max (d, 2) - 1)⌉` for the `constraintDegree` `d`. -/
def logQuotientChunks (A : Air F) (logN : Nat) : Nat :=
  let d := max (A.constraintDegree logN) 2 - 1
  Nat.log2 d.nextPowerOfTwo

end Air

/-- A period fits a trace of `2 ^ logN` rows: it is empty or of length a power of two at most
`2 ^ logN`. -/
def PeriodShape {F : Type} (logN : Nat) (col : List F) : Prop :=
  (col = [] ∨ col.length = 2 ^ Nat.log2 col.length) ∧ Nat.log2 col.length ≤ logN

theorem periodShape_of_fits {F : Type} (A : Air F) (logN : Nat) (h : A.periodicFits logN = true)
    (j : Nat) : PeriodShape logN (A.periodicColumn j) := by
  unfold Air.periodicColumn
  rcases Nat.lt_or_ge j A.periodic.length with hj | hj
  · rw [List.getD_eq_getElem _ _ hj]
    have := List.all_eq_true.mp h _ (List.getElem_mem hj)
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact ⟨Or.inr this.1, this.2⟩
  · rw [List.getD_eq_default _ _ hj]
    exact ⟨Or.inl rfl, by simp only [List.length_nil, Nat.log2_zero, Nat.zero_le]⟩

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

/-- The lookup of `wideBus`: on the global bus `wide`, every row receives its columns `0..3` and
sends its columns `4..7`, each tuple with multiplicity `±1`. -/
def wideBusLookup {F : Type} [One F] [Neg F] : Lookup F :=
  ⟨some "wide", [([.cur 0, .cur 1, .cur 2, .cur 3], .const 1),
    ([.cur 4, .cur 5, .cur 6, .cur 7], .const (-1))], 2⟩

/-- `wide w` exchanging tuples of four columns on a global bus (`wideBusLookup`): two interactions
of width `4` per row. -/
def wideBus {F : Type} [One F] [Neg F] (w : Nat) : Air F :=
  { wide w with lookups := [wideBusLookup] }

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

/-- Two columns, each the periodic column of the same index (Plonky3's `PeriodicAir` of
`uni-stark/tests/periodic_air.rs`, with the periods `cols`). -/
def periodicAir {F : Type} (cols : List (List F)) : Air F where
  width := 2
  numPublicValues := 0
  constraints := [.cur 0 - .periodic 0, .cur 1 - .periodic 1]
  periodic := cols

/-- Columns `x, y`, a constant periodic column `k = 3` and a periodic column `s` of period
`1, 2, 3, 4`, with public values `a, c`: the first `x` is `a`, each next row is
`(k x³ + s y, y + s)`, and the last `x` is `c`. Its transition has degree 3 and with periodic
columns Plonky3 sizes its quotient by polynomial degrees, as two chunks, where `degree` would
give four. -/
def periodicCube {F : Type} [NatCast F] : Air F where
  width := 2
  numPublicValues := 2
  constraints :=
    [.isFirstRow * (.cur 0 - .pub 0),
     .isTransition * ((.periodic 0 * .cur 0 * .cur 0 * .cur 0 + .periodic 1 * .cur 1) - .next 0),
     .isTransition * ((.cur 1 + .periodic 1) - .next 1),
     .isLastRow * (.cur 0 - .pub 1)]
  periodic := [[(3 : Nat)], [(1 : Nat), (2 : Nat), (3 : Nat), (4 : Nat)]]

/-- `fibonacci` with a preprocessed column holding the row index on `2 ^ logN` rows, which no
constraint reads (Plonky3's `FibonacciAir` of `batch-stark/tests/simple.rs`). -/
def fibonacciIndexed {F : Type} [NatCast F] (logN : Nat) : Air F :=
  { fibonacci with
    preprocessedWidth := 1
    preprocessed := Array.ofFn (n := 2 ^ logN) fun i ↦ (i.val : F) }

/-- `reps` repetitions of columns `a, b, c` with `a b = c` and next row `(b, a + b)`, and one more
column no constraint reads (Plonky3's `MulAir` of `batch-stark/tests/simple.rs`). -/
def mulAir {F : Type} (reps : Nat) : Air F where
  width := 3 * reps + 1
  numPublicValues := 0
  constraints := (List.range reps).flatMap fun i ↦
    [.cur (3 * i) * .cur (3 * i + 1) - .cur (3 * i + 2),
     .isTransition * (.cur (3 * i + 1) - .next (3 * i)),
     .isTransition * ((.cur (3 * i) + .cur (3 * i + 1)) - .next (3 * i + 1))]

/-- One column, `multiplier` times a preprocessed column holding the row index on `2 ^ logN` rows,
which is not read at the next row (Plonky3's `PreprocessedMulAir` of
`batch-stark/tests/simple.rs`). -/
def preprocessedMul {F : Type} [NatCast F] (logN multiplier : Nat) : Air F where
  width := 1
  numPublicValues := 0
  constraints := [.cur 0 - .prepCur 0 * .const (multiplier : F)]
  preprocessedWidth := 1
  preprocessed := Array.ofFn (n := 2 ^ logN) fun i ↦ (i.val : F)
  preprocessedNextRow := false

/-- `mulAir reps` with lookups (Plonky3's `MulAirLookups` of `batch-stark/tests/simple.rs`): if
`isLocal`, a local lookup of every repetition's `a` against the last column; and sending every
repetition `i`'s `(a, b)` on the bus `global[i]`, if `global` is not empty. -/
def mulAirLookups {F : Type} [One F] [Neg F] (reps : Nat) (isLocal : Bool) (global : List String) :
    Air F :=
  { mulAir reps with
    lookups :=
      (if isLocal then (List.range reps).map fun i ↦
        ⟨none, [([.cur (3 * i)], .const 1), ([.cur (3 * reps)], .const (-1))], 1⟩ else []) ++
      (if global.isEmpty then [] else (List.range reps).map fun i ↦
        ⟨some (global.getD i ""), [([.cur (3 * i), .cur (3 * i + 1)], .const (-1))], 1⟩) }

/-- `fibonacciIndexed logN` receiving its rows `(left, right)` on the bus `bus` with the
multiplicity `count`, bounded by `|count|` (Plonky3's `FibAirLookups` of
`batch-stark/tests/simple.rs`, with a signed multiplicity). -/
def fibonacciLookups {F : Type} [NatCast F] [IntCast F] (logN : Nat) (bus : String) (count : Int) :
    Air F :=
  { fibonacciIndexed logN with
    lookups := [⟨some bus, [([.cur 0, .cur 1], .const (count : F))], count.natAbs⟩] }

/-- Three local lookups of the columns `s₁, s₂, s₃` against the table column `t` on the first row,
on transitions and on the last row, with the multiplicity columns `m₁, m₂, m₃`, the selectors in
the multiplicities (Plonky3's `SingleTableLocalLookupAir` of `batch-stark/tests/simple.rs`). -/
def singleTableLocalLookup {F : Type} [Zero F] : Air F where
  width := 7
  numPublicValues := 0
  constraints := []
  lookups := [(0, Expr.isFirstRow), (1, .isTransition), (2, .isLastRow)].map fun (j, sel) ↦
    ⟨none, [([.cur j], sel), ([.cur 3], .const 0 - sel * .cur (4 + j))], 1⟩

/-- Two columns `a, b` with `a² = b` on every row, never reading the next row (Plonky3's
`SquareAir` of `uni-stark/tests/no_next_row.rs`). -/
def square {F : Type} : Air F where
  width := 2
  numPublicValues := 0
  constraints := [.cur 0 * .cur 0 - .cur 1]
  mainNextRow := false

end CompStark.Stark
