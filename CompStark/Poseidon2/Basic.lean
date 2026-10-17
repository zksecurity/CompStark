/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.BigOperators.Fin

/-! # The Poseidon2 permutation

Poseidon2 (Grassi, Khovratovich, Schofnegger, <https://eprint.iacr.org/2023/323>) on a state of
`t = 4 k` field elements, with the light external matrix and the S-box `x ↦ x ^ d`. As in Plonky3,
the permutation first applies the external matrix, then runs the initial full rounds, the partial
rounds and the terminal full rounds:

* a full round adds a constant to every coordinate, applies the S-box to every coordinate, then
  the external matrix;
* a partial round adds a constant to coordinate `0` and applies the S-box to it, then the
  internal matrix `1 · 1ᵀ + diag V`.

The definitions use only ring operations and the parameters, so they run unchanged on any
representation of the field.
-/

@[expose] public section
namespace CompStark.Poseidon2

open scoped BigOperators

variable {F : Type*}

/-- The parameters of a Poseidon2 instance of width `t`. -/
structure Params (F : Type*) (t : Nat) where
  /-- The S-box exponent `d`. -/
  degree : Nat
  /-- The round constants of the initial full rounds. -/
  initial : List (Vector F t)
  /-- The round constants of the partial rounds. -/
  internal : List F
  /-- The round constants of the terminal full rounds. -/
  terminal : List (Vector F t)
  /-- The internal matrix is `1 · 1ᵀ + diag diagonal`. -/
  diagonal : Vector F t

section Ring
variable [CommRing F] {t : Nat}

/-- The `4 × 4` MDS matrix `[[2, 3, 1, 1], [1, 2, 3, 1], [1, 1, 2, 3], [3, 1, 1, 2]]`, applied to
coordinates `4 b, …, 4 b + 3`; `i` selects the output row. -/
def mat4 (s : Vector F t) (b i : Nat) : F :=
  let x (j : Nat) : F := s.getD (4 * b + j) 0
  match i with
  | 0 => 2 * x 0 + 3 * x 1 + x 2 + x 3
  | 1 => x 0 + 2 * x 1 + 3 * x 2 + x 3
  | 2 => x 0 + x 1 + 2 * x 2 + 3 * x 3
  | _ => 3 * x 0 + x 1 + x 2 + 2 * x 3

/-- The external matrix: `mat4` on every block of four, plus the sum over all blocks of the
same row. That is the block circulant `circ (2 M₄, M₄, …, M₄)`. -/
def externalLinear (s : Vector F t) : Vector F t :=
  Vector.ofFn fun i : Fin t ↦
    mat4 s (i.val / 4) (i.val % 4) + ∑ b : Fin (t / 4), mat4 s b.val (i.val % 4)

/-- The internal matrix `1 · 1ᵀ + diag V`. -/
def internalLinear (V : Vector F t) (s : Vector F t) : Vector F t :=
  let sum := ∑ j : Fin t, s[j]
  Vector.ofFn fun i : Fin t ↦ V[i] * s[i] + sum

/-- A full round with constants `c`. -/
def fullRound (P : Params F t) (s c : Vector F t) : Vector F t :=
  externalLinear (Vector.ofFn fun i : Fin t ↦ (s[i] + c[i]) ^ P.degree)

/-- A partial round with constant `c`. -/
def partialRound (P : Params F t) (s : Vector F t) (c : F) : Vector F t :=
  internalLinear P.diagonal
    (Vector.ofFn fun i : Fin t ↦ if i.val = 0 then (s[i] + c) ^ P.degree else s[i])

/-- The Poseidon2 permutation. -/
def permute (P : Params F t) (s : Vector F t) : Vector F t :=
  let s := P.initial.foldl (fullRound P) (externalLinear s)
  let s := P.internal.foldl (partialRound P) s
  P.terminal.foldl (fullRound P) s

end Ring

end CompStark.Poseidon2
