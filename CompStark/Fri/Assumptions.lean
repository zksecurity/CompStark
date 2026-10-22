/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Prover

/-! # The shapes the prover works on

The assumptions under which a backend's kernels compute the specification's functions: matrices
the prover commits to have a positive width and `2 ^ k` rows within the two-adic
subgroups of the base field, their values fill them, and they are addressable by machine indices.
`DomainsAddressable` bounds the field's largest domains of extension elements likewise.
-/

@[expose] public section
namespace CompStark.Fri
open CompStark.Stark

variable {F : Type} [BaseField F]

/-- `n` machine words, with room to spare, are addressable by `USize` indices. -/
def Addressable (n : Nat) : Prop := 32 * (n + 1) < USize.size

/-- The shape of every matrix the prover commits to: a positive width, `2 ^ k` rows within the
two-adic subgroups, `width × height` values, addressable. -/
def MatOk (m : Mat F) : Prop :=
  0 < m.width ∧ (∃ k ≤ twoAdicity F, m.height = 2 ^ k) ∧ m.values.size = m.width * m.height ∧
    Addressable (m.width * m.height)

/-- Matrices committed together: at least one, each of the prover's shape and at most `h` rows,
addressable side by side at height `h`. -/
def CommitOk (ms : List (Mat F)) : Prop :=
  ∃ h, ms ≠ [] ∧ (∀ m ∈ ms, MatOk m ∧ m.height ≤ h) ∧
    Addressable (h * ms.foldl (· + ·.width) 0)

/-- The extension's vectors on the largest two-adic subgroup, `d · 2 ^ twoAdicity` words, are
addressable: a bound on the field's shape that every vector the prover builds respects. -/
def DomainsAddressable (F EF : Type) [BaseField F] [Challenge F EF] : Prop :=
  Addressable (Challenge.d EF * 2 ^ twoAdicity F)

/-- The input of a permutation trace's generation and extension by `2 ^ bits`: `A`'s trace and
preprocessed trace of `2 ^ logN` rows, a positive width, the lookups `ls` reading only the AIR's
columns, the extended domain within the two-adic subgroups, and the extensions of the traces and
of the permutation trace addressable side by side. -/
structure PermutationOk (EF : Type) [Challenge F EF] (A : Air F) (ls : List (Lookup F))
    (logN bits : Nat) (trace : Array F) : Prop where
  trace : trace.size = 2 ^ logN * A.width
  preprocessed : A.preprocessed.size = 2 ^ logN * A.preprocessedWidth
  width : 0 < A.width
  lookups : ∀ l ∈ ls, l.ColsBelow A.width A.preprocessedWidth
  twoAdic : logN + bits ≤ twoAdicity F
  mem : Addressable (2 ^ (logN + bits) *
    (A.width + A.preprocessedWidth + (ls.length + 1) * Challenge.d EF))

end CompStark.Fri
