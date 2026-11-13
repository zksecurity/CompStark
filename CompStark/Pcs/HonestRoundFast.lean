/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.HonestRound
public import CompStark.Pcs.BinaryDomain

/-! The honest quadratic message by one pass over numeric cube indices, both coefficients
computed before the message is returned. -/

@[expose] public section
namespace CompStark.Pcs

/-- A left fold accumulating a sum is the Finset sum over `Fin m`. -/
theorem foldl_finRange_sum {F : Type} [AddCommMonoid F] {m : ℕ} (g : Fin m → F) :
    (List.finRange m).foldl (fun acc i => acc + g i) 0 = ∑ i, g i := by
  rw [Fin.sum_univ_def, List.sum_eq_foldl, List.foldl_map]

/-- `honestRound` with both coefficients summed by index loops. -/
def honestRoundFast {F : Type} [CommRing F] {lanes vars : Nat}
    (weight table : Whir.Table F ((lanes + 1) + vars)) : Whir.Quadratic F :=
  let w := Whir.castTable (show (lanes + 1) + vars = 1 + (lanes + vars) by omega) weight
  let f := Whir.castTable (show (lanes + 1) + vars = 1 + (lanes + vars) by omega) table
  let low := fun i : Fin (2 ^ (lanes + vars)) => Fin.addCases (fun _ : Fin 1 => false) (mask _ i)
  let high := fun i : Fin (2 ^ (lanes + vars)) => Fin.addCases (fun _ : Fin 1 => true) (mask _ i)
  let constant := (List.finRange _).foldl (fun acc i => acc + w (low i) * f (low i)) 0
  let quadratic := (List.finRange _).foldl
    (fun acc i => acc + (w (high i) - w (low i)) * (f (high i) - f (low i))) 0
  (constant, fun _ => quadratic)

/-- The index loops compute the honest message. -/
@[csimp] theorem honestRound_code : @honestRound = @honestRoundFast := by
  funext F _ lanes vars weight table
  simp only [honestRound, honestRoundFast, foldl_finRange_sum]
  congr 1
  · exact ((cubeEquiv (lanes + vars)).sum_comp
      (fun u => Whir.castTable _ weight (Fin.addCases (fun _ : Fin 1 => false) u) *
        Whir.castTable _ table (Fin.addCases (fun _ : Fin 1 => false) u))).symm
  · funext _
    exact ((cubeEquiv (lanes + vars)).sum_comp (fun u =>
      (Whir.castTable _ weight (Fin.addCases (fun _ : Fin 1 => true) u) -
        Whir.castTable _ weight (Fin.addCases (fun _ : Fin 1 => false) u)) *
      (Whir.castTable _ table (Fin.addCases (fun _ : Fin 1 => true) u) -
        Whir.castTable _ table (Fin.addCases (fun _ : Fin 1 => false) u)))).symm

end CompStark.Pcs
