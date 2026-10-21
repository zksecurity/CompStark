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

/-- Matrices committed together: at least one, all of one height, addressable side by side. -/
def CommitOk (ms : List (Mat F)) : Prop :=
  ∃ h, ms ≠ [] ∧ (∀ m ∈ ms, MatOk m ∧ m.height = h) ∧
    Addressable (h * ms.foldl (· + ·.width) 0)

end CompStark.Fri
