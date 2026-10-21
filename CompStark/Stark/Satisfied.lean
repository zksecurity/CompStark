/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Air
public import CompStark.Stark.Field

/-! # Satisfying traces

A trace satisfies an AIR (`Air.Satisfied`) when it is a `2 ^ logN × width` matrix on whose rows
every constraint vanishes, with Plonky3's selector values on the trace domain and the periodic
columns' values on its rows. `Air.DegreeFits` bounds the constraints' degrees by what the
quotient's chunks hold.
-/

@[expose] public section
namespace CompStark.Stark

variable {F : Type} [BaseField F]

/-- Row `i` of the trace domain `⟨ω⟩` of size `n = 2 ^ logN`: the trace's and the preprocessed
trace's rows `i` and `i + 1 mod n`, every periodic column's value `i mod p`, and the selectors at
`ωⁱ`. The first-row selector
`Z_H(X) / (X - 1)` is `n` at `1` and `0` elsewhere on `⟨ω⟩`, the last-row selector
`Z_H(X) / (X - ω⁻¹)` is `n ω` at `ω⁻¹` (row `n - 1`) and `0` elsewhere, the transition selector
is `X - ω⁻¹`. -/
def Air.traceRow (air : Air F) (logN : Nat) (trace : Array F) (publicValues : List F)
    (i : Nat) : Expr.Env F F where
  cur c := trace.getD (i * air.width + c) 0
  next c := trace.getD ((i + 1) % 2 ^ logN * air.width + c) 0
  prepCur c := air.preprocessed.getD (i * air.preprocessedWidth + c) 0
  prepNext c := air.preprocessed.getD ((i + 1) % 2 ^ logN * air.preprocessedWidth + c) 0
  periodic j := (air.periodicColumn j).getD (i % (air.periodicColumn j).length) 0
  pub j := publicValues.getD j 0
  const c := c
  isFirstRow := if i = 0 then ((2 ^ logN : Nat) : F) else 0
  isLastRow := if i + 1 = 2 ^ logN then ((2 ^ logN : Nat) : F) * twoAdicGen logN else 0
  isTransition := twoAdicGen logN ^ i - (twoAdicGen logN)⁻¹

/-- Every constraint vanishes on every row of the trace domain `⟨ω⟩` of size `2 ^ logN`, with
Plonky3's selectors there: `Z_H(x) / (x - 1)`, `Z_H(x) / (x - ω⁻¹)` and `x - ω⁻¹`
(`Air.traceRow`). -/
def Air.ConstraintsVanish (air : Air F) (logN : Nat) (trace : Array F) (publicValues : List F) :
    Prop :=
  ∀ c ∈ air.constraints, ∀ i < 2 ^ logN, c.eval (air.traceRow logN trace publicValues i) = 0

/-- The constraints' degrees fit the quotient's chunks: every constraint, of degree at most
`degBound n`, is below `(k + 1) n` for `k = 2 ^ logQuotientChunks` chunks of size `n = 2 ^ logN`,
so that it divided by `Z_H` has degree below `k n`. Unlike Plonky3's `degree_multiple`, the
transition selector counts as degree `1`. -/
def Air.DegreeFits (air : Air F) (logN : Nat) : Prop :=
  ∀ c ∈ air.constraints, c.degBound (2 ^ logN) (air.periodicDegree (2 ^ logN)) <
    2 ^ (logN + air.logQuotientChunks logN) + 2 ^ logN

/-- The trace is a `2 ^ logN × width` row-major matrix on whose rows every constraint of the AIR
vanishes, with the public values `publicValues`. -/
structure Air.Satisfied (air : Air F) (logN : Nat) (trace : Array F) (publicValues : List F) :
    Prop where
  size : trace.size = 2 ^ logN * air.width
  vanish : air.ConstraintsVanish logN trace publicValues

end CompStark.Stark
