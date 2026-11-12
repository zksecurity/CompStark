/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompPoly.Data.Polynomial.RabinCertificate
import Mathlib.Tactic.ComputeDegree

/-! # Kernel-checked irreducibility of the seven RMFE factors -/

@[expose] public section
namespace CompStark.Keccak.Embedding
open Polynomial CompPoly.RabinCert

/-- The CRT factors in `rmfe.rs` order, with coefficients in increasing degree. -/
def factorCoeffs : Fin 7 → List Nat :=
  ![[0, 1], [1, 1], [1, 1, 0, 1], [1, 0, 1, 1], [1, 0, 1, 0, 0, 1], [1, 0, 0, 1, 0, 1], [1, 1, 1, 1, 0, 1]]

/-- The seven binary CRT factors of degrees 1, 1, 3, 3, 5, 5, 5. -/
noncomputable def factor (i : Fin 7) : (ZMod 2)[X] := toPoly 2 (factorCoeffs i)

/-- The factor degrees in table order. -/
def factorDegree : Fin 7 → Nat := ![1,1,3,3,5,5,5]

/-- The displayed factor degrees agree with their polynomial degrees. -/
theorem factor_natDegree (i : Fin 7) : (factor i).natDegree = factorDegree i := by
  fin_cases i <;> norm_num [factor, factorCoeffs, factorDegree, toPoly_cons, toPoly_nil]
    <;> compute_degree!

/-- Every factor is monic. -/
theorem factor_monic (i : Fin 7) : (factor i).Monic := by
  fin_cases i <;> norm_num [factor, factorCoeffs, toPoly_cons, toPoly_nil]
    <;> monicity!

/-- Every factor is nonzero, since its leading coefficient is one. -/
theorem factor_ne_zero (i : Fin 7) : factor i ≠ 0 := (factor_monic i).ne_zero

/-- Rabin squaring trace for factor 2. -/
def factorTrace2 : List Step := [⟨false, [0], [0, 0, 1]⟩,
    ⟨false, [0, 1], [0, 1, 1]⟩,
    ⟨false, [0, 1], [0, 1]⟩]

/-- Irreducibility of CRT factor 2, checked by structural natural-number certificates. -/
theorem factor_irreducible2 : Irreducible (factor 2) := by
  apply irreducible_of_rabin_prime_degree (ZMod.card 2) (by decide : Nat.Prime 3)
    (factor_natDegree 2)
  · exact dvd_X_pow_sub_X_of_runChain (fL := [1, 1, 0, 1]) rfl (factor_ne_zero 2)
      (steps := factorTrace2) (by decide) (by decide)
  · exact isCoprime_X_pow_sub_X_of_runChain (fL := [1, 1, 0, 1]) rfl (factor_ne_zero 2)
      (steps := [⟨false, [0], [0,0,1]⟩]) (rp := [0,0,1])
      (w := [0, 1, 1]) (u := [1]) (v := [1, 1])
      (by decide) (by decide) (by decide) (by decide)

/-- Rabin squaring trace for factor 3. -/
def factorTrace3 : List Step := [⟨false, [0], [0, 0, 1]⟩,
    ⟨false, [1, 1], [1, 1, 1]⟩,
    ⟨false, [1, 1], [0, 1]⟩]

/-- Irreducibility of CRT factor 3, checked by structural natural-number certificates. -/
theorem factor_irreducible3 : Irreducible (factor 3) := by
  apply irreducible_of_rabin_prime_degree (ZMod.card 2) (by decide : Nat.Prime 3)
    (factor_natDegree 3)
  · exact dvd_X_pow_sub_X_of_runChain (fL := [1, 0, 1, 1]) rfl (factor_ne_zero 3)
      (steps := factorTrace3) (by decide) (by decide)
  · exact isCoprime_X_pow_sub_X_of_runChain (fL := [1, 0, 1, 1]) rfl (factor_ne_zero 3)
      (steps := [⟨false, [0], [0,0,1]⟩]) (rp := [0,0,1])
      (w := [0, 1, 1]) (u := [1]) (v := [0, 1])
      (by decide) (by decide) (by decide) (by decide)

/-- Rabin squaring trace for factor 4. -/
def factorTrace4 : List Step := [⟨false, [0], [0, 0, 1]⟩,
    ⟨false, [0], [0, 0, 0, 0, 1]⟩,
    ⟨false, [1, 0, 0, 1], [1, 0, 1, 1]⟩,
    ⟨false, [0, 1], [1, 1, 0, 1, 1]⟩,
    ⟨false, [1, 1, 0, 1], [0, 1]⟩]

/-- Irreducibility of CRT factor 4, checked by structural natural-number certificates. -/
theorem factor_irreducible4 : Irreducible (factor 4) := by
  apply irreducible_of_rabin_prime_degree (ZMod.card 2) (by decide : Nat.Prime 5)
    (factor_natDegree 4)
  · exact dvd_X_pow_sub_X_of_runChain (fL := [1, 0, 1, 0, 0, 1]) rfl (factor_ne_zero 4)
      (steps := factorTrace4) (by decide) (by decide)
  · exact isCoprime_X_pow_sub_X_of_runChain (fL := [1, 0, 1, 0, 0, 1]) rfl (factor_ne_zero 4)
      (steps := [⟨false, [0], [0,0,1]⟩]) (rp := [0,0,1])
      (w := [0, 1, 1]) (u := [1]) (v := [0, 1, 1, 1])
      (by decide) (by decide) (by decide) (by decide)

/-- Rabin squaring trace for factor 5. -/
def factorTrace5 : List Step := [⟨false, [0], [0, 0, 1]⟩,
    ⟨false, [0], [0, 0, 0, 0, 1]⟩,
    ⟨false, [0, 1, 0, 1], [0, 1, 0, 1, 1]⟩,
    ⟨false, [0, 0, 0, 1], [0, 0, 1, 1]⟩,
    ⟨false, [0, 1], [0, 1]⟩]

/-- Irreducibility of CRT factor 5, checked by structural natural-number certificates. -/
theorem factor_irreducible5 : Irreducible (factor 5) := by
  apply irreducible_of_rabin_prime_degree (ZMod.card 2) (by decide : Nat.Prime 5)
    (factor_natDegree 5)
  · exact dvd_X_pow_sub_X_of_runChain (fL := [1, 0, 0, 1, 0, 1]) rfl (factor_ne_zero 5)
      (steps := factorTrace5) (by decide) (by decide)
  · exact isCoprime_X_pow_sub_X_of_runChain (fL := [1, 0, 0, 1, 0, 1]) rfl (factor_ne_zero 5)
      (steps := [⟨false, [0], [0,0,1]⟩]) (rp := [0,0,1])
      (w := [0, 1, 1]) (u := [1]) (v := [0, 0, 1, 1])
      (by decide) (by decide) (by decide) (by decide)

/-- Rabin squaring trace for factor 6. -/
def factorTrace6 : List Step := [⟨false, [0], [0, 0, 1]⟩,
    ⟨false, [0], [0, 0, 0, 0, 1]⟩,
    ⟨false, [1, 1, 0, 1], [1, 0, 0, 1]⟩,
    ⟨false, [0, 1], [1, 1, 1, 1, 1]⟩,
    ⟨false, [1, 0, 0, 1], [0, 1]⟩]

/-- Irreducibility of CRT factor 6, checked by structural natural-number certificates. -/
theorem factor_irreducible6 : Irreducible (factor 6) := by
  apply irreducible_of_rabin_prime_degree (ZMod.card 2) (by decide : Nat.Prime 5)
    (factor_natDegree 6)
  · exact dvd_X_pow_sub_X_of_runChain (fL := [1, 1, 1, 1, 0, 1]) rfl (factor_ne_zero 6)
      (steps := factorTrace6) (by decide) (by decide)
  · exact isCoprime_X_pow_sub_X_of_runChain (fL := [1, 1, 1, 1, 0, 1]) rfl (factor_ne_zero 6)
      (steps := [⟨false, [0], [0,0,1]⟩]) (rp := [0,0,1])
      (w := [0, 1, 1]) (u := [1]) (v := [1, 0, 1, 1])
      (by decide) (by decide) (by decide) (by decide)

/-- All seven CRT factors are irreducible over the binary field. -/
theorem factor_irreducible (i : Fin 7) : Irreducible (factor i) := by
  fin_cases i
  · apply Polynomial.irreducible_of_degree_eq_one
    norm_num [factor, factorCoeffs, toPoly_cons, toPoly_nil]
  · apply Polynomial.irreducible_of_degree_eq_one
    norm_num [factor, factorCoeffs, toPoly_cons, toPoly_nil]
    compute_degree!
  · exact factor_irreducible2
  · exact factor_irreducible3
  · exact factor_irreducible4
  · exact factor_irreducible5
  · exact factor_irreducible6

/-- Left coefficients in the pairwise Bézout certificates. -/
def factorBezoutLeft : Fin 7 → Fin 7 → List Nat :=
  ![![[0], [1], [1, 0, 1], [0, 1, 1], [0, 1, 0, 0, 1], [0, 0, 1, 0, 1], [1, 1, 1, 0, 1]],
    ![[1], [0], [0, 1, 1], [0, 0, 1], [0, 0, 1, 1, 1], [0, 0, 0, 1, 1], [0, 1, 0, 1, 1]],
    ![[1], [1], [0], [0, 1], [0, 0, 0, 0, 1], [1, 0, 0, 1], [1, 0, 0, 1, 1]],
    ![[1], [1], [1, 1], [0], [1, 1, 1, 1], [0, 0, 1, 1, 1], [0, 1, 1]],
    ![[1], [1], [1, 0, 1], [0, 1], [0], [0, 1, 1], [0, 1, 1, 1, 1]],
    ![[1], [1], [0, 1], [1, 0, 1], [1, 1, 1], [0], [1, 0, 1, 1]],
    ![[1], [1], [0, 1, 1], [1], [1, 0, 0, 1, 1], [0, 0, 1, 1], [0]]]

/-- Right coefficients in the pairwise Bézout certificates. -/
def factorBezoutRight : Fin 7 → Fin 7 → List Nat :=
  ![![[1], [1], [1], [1], [1], [1], [1]],
    ![[1], [1], [1], [1], [1], [1], [1]],
    ![[1, 0, 1], [0, 1, 1], [1], [1, 1], [1, 0, 1], [0, 1], [0, 1, 1]],
    ![[0, 1, 1], [0, 0, 1], [0, 1], [1], [0, 1], [1, 0, 1], [1]],
    ![[0, 1, 0, 0, 1], [0, 0, 1, 1, 1], [0, 0, 0, 0, 1], [1, 1, 1, 1], [1], [1, 1, 1], [1, 0, 0, 1, 1]],
    ![[0, 0, 1, 0, 1], [0, 0, 0, 1, 1], [1, 0, 0, 1], [0, 0, 1, 1, 1], [0, 1, 1], [1], [0, 0, 1, 1]],
    ![[1, 1, 1, 0, 1], [0, 1, 0, 1, 1], [1, 0, 0, 1, 1], [0, 1, 1], [0, 1, 1, 1, 1], [1, 0, 1, 1], [1]]]

/-- Structural natural-number verification of every off-diagonal Bézout identity. -/
theorem factor_coprime_certificate : ∀ i j : Fin 7, i ≠ j →
    eqModP 2 (addNat (mulNat (factorBezoutLeft i j) (factorCoeffs i))
      (mulNat (factorBezoutRight i j) (factorCoeffs j))) [1] = true := by
  decide

/-- The seven irreducibles are pairwise coprime, by kernel-checked Bézout identities. -/
theorem factor_pairwise_coprime : Pairwise (fun i j : Fin 7 => IsCoprime (factor i) (factor j)) := by
  intro i j hij
  refine ⟨toPoly 2 (factorBezoutLeft i j), toPoly 2 (factorBezoutRight i j), ?_⟩
  have h := toPoly_eq_of_eqModP (factor_coprime_certificate i j hij)
  simpa only [toPoly_addNat, toPoly_mulNat, toPoly_one, factor] using h

end CompStark.Keccak.Embedding
