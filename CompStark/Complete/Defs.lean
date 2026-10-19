/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Prover

/-! # Low-degree vectors and matrices

The predicates the completeness proof passes between the prover's layers, over the Mathlib fields
`KoalaBear.Field` and `KoalaBear.Ext4` that the Montgomery elements denote:

* `Mat.IsLde`: a committed matrix is the low-degree extension of polynomials onto the coset
  `g · ⟨ω⟩`, rows in bit-reversed order.
* `LowDegree`: a vector of extension elements is FRI's view of a codeword, the values on the
  subgroup `⟨ω⟩` in bit-reversed order of a polynomial of bounded degree. FRI ignores the coset
  shift: values on `g · ⟨ω⟩` of `p` are values on `⟨ω⟩` of `p (g X)`, of the same degree.
-/

@[expose] public section
namespace CompStark
open CompStark.Stark CompStark.Fri Polynomial Montgomery.Native32

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4

/-- The columns of `m`, of height `2 ^ logH`, are the values on the coset `g · ⟨ω⟩`, `ω` of order
`2 ^ logH`, rows in bit-reversed order, of the polynomials `ps` of degree below
`2 ^ (logH - logBlowup)`. -/
def Mat.IsLde (logBlowup logH : Nat) (m : Mat) (ps : List KoalaBear.Field[X]) : Prop :=
  m.width = ps.length ∧ m.height = 2 ^ logH ∧ m.values.size = m.width * m.height ∧
    logBlowup ≤ logH ∧ logH ≤ 24 ∧
    (∀ p ∈ ps, p.degree < ((2 ^ (logH - logBlowup) : Nat) : WithBot Nat)) ∧
    ∀ r < 2 ^ logH, ∀ j < ps.length,
      FastField.toField (m.values.getD (r * m.width + j) 0) =
        (ps.getD j 0).eval (FastField.toField gen *
          FastField.toField (twoAdicGen logH) ^ reverseBits r logH)

/-- `v` holds the values on the subgroup `⟨ω⟩`, `ω` of order `2 ^ logH`, in bit-reversed order, of
a polynomial over the extension of degree below `2 ^ logD`. -/
def LowDegree (logH logD : Nat) (v : Array EF) : Prop :=
  v.size = 2 ^ logH ∧ logH ≤ 24 ∧ ∃ p : KoalaBear.Ext4[X],
    p.degree < ((2 ^ logD : Nat) : WithBot Nat) ∧ ∀ r < 2 ^ logH,
      KoalaBear.Fast.Ext4.toSpec (v.getD r 0) =
        p.eval (algebraMap KoalaBear.Field KoalaBear.Ext4
          (FastField.toField (twoAdicGen logH)) ^ reverseBits r logH)

/-- The shapes the completeness proof works on: a `2 ^ logN × width` trace, constraints that read
only the AIR's columns, an extended domain within KoalaBear's two-adic subgroups, and quotient
chunks that fit the blowup. -/
structure Fits (P : Params) (A : Air) (logN : Nat) (trace : Array F) : Prop where
  trace : trace.size = 2 ^ logN * A.width
  cols : A.ColsInWidth
  twoAdic : logN + P.logBlowup ≤ 24
  chunks : A.logQuotientChunks ≤ P.logBlowup

end CompStark
