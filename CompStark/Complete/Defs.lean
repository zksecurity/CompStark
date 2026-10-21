/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Prover
public import CompStark.Plonky3.Prover
public import CompStark.Stark.Points
public import CompPoly.Univariate.NTT.CosetBarycentric

/-! # Low-degree vectors and matrices

The predicates the completeness proof passes between the prover's layers, over the base field `F`
and the spec field `Challenge.Spec EF` of the challenge field:

* `Mat.IsLde`: a committed matrix is the low-degree extension of polynomials onto the coset
  `g · ⟨ω⟩`, rows in bit-reversed order.
* `LowDegree`: a vector of extension elements is FRI's view of a codeword, the values on the
  subgroup `⟨ω⟩` in bit-reversed order of a polynomial of bounded degree. FRI ignores the coset
  shift: values on `g · ⟨ω⟩` of `p` are values on `⟨ω⟩` of `p (g X)`, of the same degree.
-/

@[expose] public section
namespace CompStark
open CompStark.Stark CompStark.Fri Polynomial

variable {F : Type} [BaseField F]

/-- The columns of `m`, of height `2 ^ logH`, are the values on the coset `g · ⟨ω⟩`, `ω` of order
`2 ^ logH`, rows in bit-reversed order, of the polynomials `ps` of degree below
`2 ^ (logH - logBlowup)`. -/
def Mat.IsLde (logBlowup logH : Nat) (m : Mat F) (ps : List F[X]) : Prop :=
  m.width = ps.length ∧ m.height = 2 ^ logH ∧ m.values.size = m.width * m.height ∧
    logBlowup ≤ logH ∧ logH ≤ twoAdicity F ∧
    (∀ p ∈ ps, p.degree < ((2 ^ (logH - logBlowup) : Nat) : WithBot Nat)) ∧
    ∀ r < 2 ^ logH, ∀ j < ps.length,
      (m.values.getD (r * m.width + j) 0) =
        (ps.getD j 0).eval (gen *
          (twoAdicGen logH) ^ reverseBits r logH)

/-- `v` holds the values on the subgroup `⟨ω⟩`, `ω` of order `2 ^ logH`, in bit-reversed order, of
a polynomial over the extension of degree below `2 ^ logD`. -/
def LowDegree {EF : Type} [Challenge F EF] (logH logD : Nat) (v : Array EF) : Prop :=
  v.size = 2 ^ logH ∧ logH ≤ twoAdicity F ∧ ∃ p : (Challenge.Spec EF)[X],
    p.degree < ((2 ^ logD : Nat) : WithBot Nat) ∧ ∀ r < 2 ^ logH,
      Challenge.toSpec (v.getD r 0) =
        p.eval (algebraMap F (Challenge.Spec EF)
          ((twoAdicGen logH)) ^ reverseBits r logH)

/-- The shapes the completeness proof works on: a `2 ^ logN × width` trace, constraints that read
only the AIR's columns, an extended domain within the base field's two-adic subgroups, quotient
chunks that fit the blowup, and periodic columns that fit the trace. -/
structure Fits (P : Params) (A : Air F) (logN : Nat) (trace : Array F) : Prop where
  trace : trace.size = 2 ^ logN * A.width
  cols : A.ColsInWidth
  twoAdic : logN + P.logBlowup ≤ twoAdicity F
  chunks : A.logQuotientChunks logN ≤ P.logBlowup
  periodic : A.periodicFits logN = true

end CompStark
