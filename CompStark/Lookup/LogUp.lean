/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Satisfied
public import CompStark.Stark.Challenge

/-! # The LogUp gadget

Plonky3's `LogUpGadget` (`lookup/src/logup.rs`, revision `a4982ec`) for the lookups of one AIR,
over a challenge pair per lookup: `2 c` and `2 c + 1` of the challenges are lookup `c`'s
denominator base `a` and combiner `b`. A tuple `t` with multiplicity `m` contributes the fraction
`m / (a - ∑ⱼ tⱼ bᵏ⁻¹⁻ʲ)` on its row.

The permutation (auxiliary) trace has, over the challenge field, an accumulator in column `0` and
lookup `c`'s fractions on each row in column `c + 1`. Its constraints (`logUpConstraints`), over
the main, preprocessed and permutation traces, the challenges and the AIR's committed terminal
(`ExtExpr`), in Plonky3's order:

* every lookup's fraction pin `U f - V`, `V / U` the sum of the lookup's fractions on the row
  with every denominator cleared;
* the accumulator: `0` on the first row, `acc' = acc + ∑ f` on transitions, and
  `terminal = acc + ∑ f` on the last row.

So the terminal is the sum of every fraction of the trace. `lookupDegree` is the fraction pin's
degree, which Plonky3 packs lookups by. `permutationTrace` is Plonky3's `generate_permutation`:
fractions of zero multiplicity skipped, prefix sums, and the terminal.
-/

@[expose] public section
namespace CompStark.Lookup
open CompStark.Stark

/-- A constraint expression over the base field `F` with values in the challenge field: a base
expression (`base`), the permutation trace's columns at the current and next rows, a challenge,
and the AIR's terminal. -/
inductive ExtExpr (F : Type) where
  | base (e : Expr F)
  | perm (col : Nat)
  | permNext (col : Nat)
  | challenge (i : Nat)
  | terminal
  | add (a b : ExtExpr F)
  | sub (a b : ExtExpr F)
  | mul (a b : ExtExpr F)

namespace ExtExpr

variable {F : Type}

instance : Add (ExtExpr F) := ⟨add⟩
instance : Sub (ExtExpr F) := ⟨sub⟩
instance : Mul (ExtExpr F) := ⟨mul⟩

/-- Plonky3's `degree_multiple`: permutation columns have degree 1, challenges and the terminal
0. -/
def degree : ExtExpr F → Nat
  | base e => e.degree
  | perm _ | permNext _ => 1
  | challenge _ | terminal => 0
  | add a b | sub a b => max a.degree b.degree
  | mul a b => a.degree + b.degree

/-- Plonky3's `poly_degree` on a trace domain of size `n`, the periodic column `i` of degree
`periodicDegree i`: permutation columns have degree `n - 1`. -/
def degBound (n : Nat) (periodicDegree : Nat → Nat) : ExtExpr F → Nat
  | base e => e.degBound n periodicDegree
  | perm _ | permNext _ => n - 1
  | challenge _ | terminal => 0
  | add a b | sub a b => max (a.degBound n periodicDegree) (b.degBound n periodicDegree)
  | mul a b => a.degBound n periodicDegree + b.degBound n periodicDegree

/-- The values of the permutation trace's rows, the challenges and the terminal. -/
structure Env (K : Type*) where
  perm : Nat → K
  permNext : Nat → K
  challenge : Nat → K
  terminal : K

/-- Evaluate an expression, its base expressions in `env` and the rest in `aux`. -/
def eval {K : Type*} [Add K] [Sub K] [Mul K] (env : Expr.Env F K) (aux : Env K) :
    ExtExpr F → K
  | base e => e.eval env
  | perm c => aux.perm c
  | permNext c => aux.permNext c
  | challenge i => aux.challenge i
  | terminal => aux.terminal
  | add a b => eval env aux a + eval env aux b
  | sub a b => eval env aux a - eval env aux b
  | mul a b => eval env aux a * eval env aux b

/-- The constant `c`. -/
abbrev const (c : F) : ExtExpr F := base (.const c)

end ExtExpr

variable {F : Type}

/-! ### The constraints -/

/-- `a - ∑ⱼ tⱼ bᵏ⁻¹⁻ʲ` for the tuple `t` of `k` expressions, by Horner's rule from the first
(Plonky3's `combine_elements`). -/
def denominator [Zero F] (a b : ExtExpr F) (t : List (Expr F)) : ExtExpr F :=
  a - match t with
    | [] => .const 0
    | e :: es => es.foldl (fun acc x ↦ .base x + acc * b) (.base e)

/-- The numerator and the denominator `(V, U)` of `∑ᵢ mᵢ / dᵢ` over the pairs `(dᵢ, mᵢ)`, every
denominator cleared (Plonky3's `fold_rational_terms`). -/
def foldFractions [Zero F] [One F] : List (ExtExpr F × ExtExpr F) → ExtExpr F × ExtExpr F
  | [] => (.const 0, .const 1)
  | (d, m) :: rest => rest.foldl (fun (v, u) (d, m) ↦ (v * d + m * u, u * d)) (m, d)

/-- Lookup `c`'s fraction pin `U f - V`, `f` its fraction column `c + 1`. -/
def fractionPin [Zero F] [One F] (c : Nat) (l : Lookup F) : ExtExpr F :=
  let (v, u) := foldFractions (l.tuples.map fun (t, m) ↦
    (denominator (.challenge (2 * c)) (.challenge (2 * c + 1)) t, .base m))
  u * .perm (c + 1) - v

/-- The sum of the fraction columns of `k` lookups on the current row. -/
def rowSum [Zero F] (k : Nat) : ExtExpr F :=
  (List.range k).foldl (fun s c ↦ s + .perm (c + 1)) (.const 0)

/-- The LogUp constraints of an AIR's lookups, in Plonky3's order: every fraction pin, then the
accumulator's on the first row, on transitions and on the last row. None without lookups. -/
def logUpConstraints [Zero F] [One F] (lookups : List (Lookup F)) : List (ExtExpr F) :=
  if lookups.isEmpty then [] else
    lookups.zipIdx.map (fun (l, c) ↦ fractionPin c l) ++
      [.base .isFirstRow * .perm 0,
        .base .isTransition * (.permNext 0 - .perm 0 - rowSum lookups.length),
        .base .isLastRow * (.terminal - .perm 0 - rowSum lookups.length)]

/-- The degree of a lookup's fraction pin, `max (1 + ∑ᵢ dᵢ) (maxᵢ (deg mᵢ + ∑_{j ≠ i} dⱼ))`,
`dᵢ` the largest degree in tuple `i` (Plonky3's `constraint_degree`). -/
def lookupDegree (l : Lookup F) : Nat :=
  let degs := l.tuples.map fun (t, _) ↦ t.foldl (fun m e ↦ max m e.degree) 0
  let sum := degs.sum
  let num := (l.tuples.zip degs).foldl (fun m ((_, mult), d) ↦ max m (mult.degree + sum - d)) 0
  max (1 + sum) num

/-! ### The permutation trace -/

section Permutation
variable [BaseField F] {EF : Type} [Challenge F EF]

/-- Row `i` of `2 ^ logN` as the permutation trace's generation reads it (Plonky3's
`LookupTraceBuilder`): the traces' rows `i` and `i + 1 mod n`, the public values, and the
selectors as `0` or `1`. It reads no periodic column. -/
def generationRow (A : Air F) (logN : Nat) (trace : Array F) (pis : List F) (i : Nat) :
    Expr.Env F F where
  cur c := trace.getD (i * A.width + c) 0
  next c := trace.getD ((i + 1) % 2 ^ logN * A.width + c) 0
  prepCur c := A.preprocessed.getD (i * A.preprocessedWidth + c) 0
  prepNext c := A.preprocessed.getD ((i + 1) % 2 ^ logN * A.preprocessedWidth + c) 0
  periodic _ := 0
  pub j := pis.getD j 0
  const c := c
  isFirstRow := if i = 0 then 1 else 0
  isLastRow := if i + 1 = 2 ^ logN then 1 else 0
  isTransition := if i + 1 < 2 ^ logN then 1 else 0

/-- `∑ⱼ tⱼ bᵏ⁻¹⁻ʲ` of the tuple's values `t`. -/
def combine (b : EF) (t : List F) : EF :=
  match t with
  | [] => 0
  | x :: xs => xs.foldl (fun acc y ↦ Ext.ofBase y + acc * b) (Ext.ofBase x)

/-- A lookup's fraction on a row: `∑ m / (a - ∑ⱼ tⱼ bᵏ⁻¹⁻ʲ)` over its tuples on the row `env`,
with the challenge pair `(a, b)`, a tuple of multiplicity `0` adding nothing. -/
def fraction (env : Expr.Env F F) (a b : EF) (l : Lookup F) : EF :=
  l.tuples.foldl (fun s (t, m) ↦
    let mv := m.eval env
    if mv = 0 then s else s + Challenge.smul mv (a - combine b (t.map (·.eval env)))⁻¹) 0

/-- The fractions of `A`'s lookups `lookups` on row `i` of its trace of `2 ^ logN` rows with the
public values `pis` and the challenges `chs`, lookup `c` with the pair `2 c`, `2 c + 1`. -/
def rowFractions (A : Air F) (lookups : List (Lookup F)) (logN : Nat) (trace : Array F)
    (pis : List F) (chs : List EF) (i : Nat) : List EF :=
  lookups.zipIdx.map fun (l, c) ↦ fraction (generationRow A logN trace pis i)
    (chs.getD (2 * c) 0) (chs.getD (2 * c + 1) 0) l

/-- The permutation trace of `A`'s lookups `lookups` on its trace of `2 ^ logN` rows with the
public values `pis` and the challenges `chs` (Plonky3's `generate_permutation`): row-major over the
challenge field, on row `i` the accumulator `∑_{r < i}` of the rows' fractions, then the fraction of
every lookup (`rowFractions`); and the terminal, the sum of every row's fractions. -/
def permutationTrace (A : Air F) (lookups : List (Lookup F)) (logN : Nat) (trace : Array F)
    (pis : List F) (chs : List EF) : Array EF × EF :=
  (List.range (2 ^ logN)).foldl (fun (out, acc) i ↦
    let fs := rowFractions A lookups logN trace pis chs i
    ((out.push acc) ++ fs.toArray, fs.foldl (· + ·) acc)) (#[], 0)

/-- A row-major matrix over the challenge field as base coordinates, `d` per element. -/
def flatten (vs : Array EF) : Array F :=
  vs.flatMap fun x ↦ (Ext.coeffs x).toArray

/-- Column `c` of an opened row of base coordinates, `d` per element of the challenge field. -/
def unflattenAt (row : Array EF) (c : Nat) : EF :=
  (List.range (Challenge.d EF)).foldl
    (fun s e ↦ s + Ext.basis e * row.getD (c * Challenge.d EF + e) 0) 0

end Permutation

end CompStark.Lookup
