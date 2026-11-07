/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ArkLib.ProofSystem.Whir.Protocol
public import ArkLib.ProofSystem.Whir.Algebra

/-! Honest compressed quadratic messages and complete scalar-round blocks for WHIR. -/

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStark.Pcs
open Interaction Interaction.Oracle

/-- Weighted inner product on a Boolean table. -/
def dot {F : Type} [Semiring F] {n : Nat} (weight table : Whir.Table F n) : F :=
  ∑ u, weight u * table u

/-- Coordinate transport preserves a weighted inner product. -/
theorem dot_cast {F : Type} [Semiring F] {n m : Nat} (h : n = m)
    (weight table : Whir.Table F n) :
    dot (Whir.castTable h weight) (Whir.castTable h table) = dot weight table := by
  subst m
  rfl

/-- The constant and quadratic coefficients of the honest product of affine slices. -/
def honestRound {F : Type} [CommRing F] {lanes vars : Nat}
    (weight table : Whir.Table F ((lanes + 1) + vars)) : Whir.Quadratic F :=
  let w := Whir.castTable (show (lanes + 1) + vars = 1 + (lanes + vars) by omega) weight
  let f := Whir.castTable (show (lanes + 1) + vars = 1 + (lanes + vars) by omega) table
  (∑ u, w (Fin.addCases (fun _ : Fin 1 => false) u) *
      f (Fin.addCases (fun _ : Fin 1 => false) u),
    fun _ => ∑ u,
      (w (Fin.addCases (fun _ : Fin 1 => true) u) -
        w (Fin.addCases (fun _ : Fin 1 => false) u)) *
      (f (Fin.addCases (fun _ : Fin 1 => true) u) -
        f (Fin.addCases (fun _ : Fin 1 => false) u)))

/-- Honest compressed coefficients are linear in the weight table. -/
theorem honestRound_linear {F : Type} [CommRing F] {lanes vars : Nat}
    (a b : F) (left right table : Whir.Table F ((lanes + 1) + vars)) :
    honestRound (fun u => a * left u + b * right u) table =
      (a * (honestRound left table).1 + b * (honestRound right table).1,
        fun i => a * (honestRound left table).2 i + b * (honestRound right table).2 i) := by
  apply Prod.ext
  · simp only [honestRound, Whir.castTable, add_mul, mul_assoc, Finset.sum_add_distrib,
      ← Finset.mul_sum]
  · funext i
    simp only [honestRound, Whir.castTable]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    ring

/-- Reconstructing and evaluating the honest message gives the next weighted inner product. -/
theorem honestRound_eval {F : Type} [CommRing F] {lanes vars : Nat}
    (weight table : Whir.Table F ((lanes + 1) + vars)) (r : F) :
    Whir.evalQuadratic (dot weight table) (honestRound weight table) r =
      dot (Whir.foldMessageOne weight r) (Whir.foldMessageOne table r) := by
  have split := Whir.foldPolynomial_boolean_sum weight table
  rw [Whir.foldPolynomial_eval, Whir.foldPolynomial_eval] at split
  simp only [Whir.foldMessageOne_apply, sub_zero, one_mul, zero_mul, add_zero,
    sub_self, zero_add] at split
  unfold Whir.evalQuadratic
  simp only [Sumcheck.compressedOps, Fin.sum_univ_one, Fin.val_zero, zero_add]
  rw [show dot weight table = _ from split.symm]
  simp only [honestRound, dot, Whir.foldMessageOne_apply,
    Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- Send honest scalar-round messages; the continuation sees only the restricted tables. -/
@[noinline] def honestRounds {F : Type} [CommRing F] (rest : Protocol.{0}) {vars : Nat} :
    (count : Nat) → Whir.Table F (count + vars) → Whir.Table F (count + vars) →
    (Fin count → F) → (Whir.Table F vars → Whir.Table F vars → rest.tree.ExecutionPath) →
      (Whir.scalarRounds F count rest).tree.ExecutionPath
  | 0, weight, table, _, next =>
      next (Whir.castTable (Nat.zero_add vars) weight) (Whir.castTable (Nat.zero_add vars) table)
  | count + 1, weight, table, rs, next =>
      ⟨honestRound weight table, rs 0,
        honestRounds rest count (Whir.foldMessageOne weight (rs 0))
          (Whir.foldMessageOne table (rs 0)) (Fin.tail rs) next⟩

/-- The verifier reads the exact restricted tables' inner product and accepts every honest round. -/
theorem read_honestRounds {F : Type} [CommRing F] [DecidableEq F] (rest : Protocol.{0})
    {vars : Nat} (count : Nat) (weight table : Whir.Table F (count + vars))
    (rs : Fin count → F)
    (next : Whir.Table F vars → Whir.Table F vars → rest.tree.ExecutionPath) :
    Whir.readRounds rest count (dot weight table) (honestRounds rest count weight table rs next) =
      (dot (Whir.restrict weight rs) (Whir.restrict table rs), rs, true,
        next (Whir.restrict weight rs) (Whir.restrict table rs)) := by
  induction count with
  | zero =>
      have hrs : rs = Fin.elim0 := funext fun i => Fin.elim0 i
      subst rs
      simp only [honestRounds, Whir.readRounds, Whir.restrict_zero, dot_cast]
  | succ count ih =>
      simp only [honestRounds, Whir.readRounds, honestRound_eval, ih]
      have hrs : Fin.cons (rs 0) (Fin.tail rs) = rs := Fin.cons_self_tail rs
      simp only [Whir.restrict_foldMessageOne, hrs, Sumcheck.compressedOps,
        Bool.true_and]

/-- Restricting all coordinates leaves the scalar multilinear evaluation. -/
theorem restrict_full {F : Type} [CommRing F] {n : Nat} (table : Whir.Table F (n + 0))
    (point : Fin n → F) (u : Whir.Cube 0) :
    Whir.restrict table point u = Whir.mle table point := by
  simp only [Whir.restrict, Whir.mle, Whir.addCases_empty]
  rfl

/-- Closing honest rounds finish at the product of the two multilinear evaluations. -/
theorem read_honestClosing {F : Type} [CommRing F] [DecidableEq F] {n : Nat}
    (weight table : Whir.Table F n) (rs : Fin n → F) :
    Whir.readRounds .done n (dot weight table)
      (honestRounds .done (vars := 0) n weight table rs (fun _ _ => PUnit.unit)) =
      (Whir.mle weight rs * Whir.mle table rs, rs, true, PUnit.unit) := by
  rw [read_honestRounds (vars := 0)]
  simp only [dot, restrict_full, Fintype.sum_unique]

end CompStark.Pcs
