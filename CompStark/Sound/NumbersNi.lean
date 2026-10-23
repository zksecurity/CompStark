/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Numbers
public import CompStark.NonInteractiveError
public import CompStark.Sound.Rbr

/-! # Bounds on the round errors of one random-oracle answer

The terms of `roundError` (`CompStark/NonInteractiveError.lean`) at any FRI arity, with FRI's
radius at most the unique-decoding radius, as in `CompStark/Sound/Numbers.lean`:

* constraint folding, out of domain and batching as for the knowledge error;
* each FRI fold: ArkLib's schedule of Plonky3's arities is the plan of the folds without inputs
  (`plan_eq_arityPlan`, `schedule_mem_plan`), so every fold costs at most the plan's largest level
  bound (`friFoldError_le`);
* FRI's queries: `(1 - δ + #folds · loss + 1/p) ^ numQueries` (`friQueryError_eq`).

`CompStark/Sound/Calculator.lean` collects them at one proximity loss.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop NNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-- The largest level bound of a plan's folds at rate `1/c`, `0` if empty. -/
noncomputable def planMax (c : ℕ) (δ δ_int : ℝ≥0) (loss : ℝ) (plan : List (ℕ × ℕ × Bool)) : ℝ :=
  (plan.map fun f ↦ levelBound c δ δ_int loss (FriGame.Rounds.foldWords f) f.2.1).foldr max 0

theorem le_planMax (c : ℕ) (δ δ_int : ℝ≥0) (loss : ℝ) {f : ℕ × ℕ × Bool} :
    ∀ {plan : List (ℕ × ℕ × Bool)}, f ∈ plan →
      levelBound c δ δ_int loss (FriGame.Rounds.foldWords f) f.2.1 ≤ planMax c δ δ_int loss plan
  | _ :: _, .head _ => le_max_left _ _
  | _ :: _, .tail _ h => (le_planMax c δ δ_int loss h).trans (le_max_right _ _)

theorem planMax_nonneg (c : ℕ) (δ δ_int : ℝ≥0) (loss : ℝ) :
    ∀ plan : List (ℕ × ℕ × Bool), 0 ≤ planMax c δ δ_int loss plan
  | [] => le_rfl
  | _ :: plan => (planMax_nonneg c δ δ_int loss plan).trans (le_max_right _ _)

/-- The plan of folds by the arities `l` from a domain of `2 ^ n` points, injecting nothing. -/
def arityPlan : List ℕ → ℕ → List (ℕ × ℕ × Bool)
  | [], _ => []
  | s :: l, n => (s, n - s, false) :: arityPlan l (n - s)

/-- Without inputs, the plan folds by Plonky3's arities. -/
theorem plan_nil (a logFinal : ℕ) (ha : 0 < a) :
    ∀ fuel n, logFinal ≤ n → n - logFinal ≤ fuel →
      FriGame.Rounds.plan a logFinal fuel n [] =
        arityPlan ((folds a (n - logFinal)).map PNat.val) n
  | 0, n, hn, hfuel => by
    rw [FriGame.Rounds.plan, show n - logFinal = 0 by omega, folds]
    rfl
  | fuel + 1, n, hn, hfuel => by
    by_cases hfin : n ≤ logFinal
    · rw [FriGame.Rounds.plan, ite_eq_left hfin, show n - logFinal = 0 by omega, folds]
      rfl
    obtain ⟨r, hr⟩ : ∃ r, n - logFinal = r + 1 := ⟨n - logFinal - 1, by omega⟩
    have hla : FriGame.Rounds.logArity a logFinal n [] = max 1 (min a (r + 1)) := by
      unfold FriGame.Rounds.logArity
      simp only [List.headD_nil]
      omega
    rw [FriGame.Rounds.plan, ite_eq_right hfin, hr, folds]
    simp only [hla]
    congr 1
    rw [plan_nil a logFinal ha fuel _ (by omega) (by omega)]
    congr 3
    omega

/-- Entry `i` of an arity plan: the arity, and the domain after the first `i + 1` folds. -/
theorem arityPlan_getElem : ∀ (l : List ℕ) (n i : ℕ) (hi : i < l.length),
    (arityPlan l n)[i]'(by
      induction l generalizing n i with
      | nil => exact absurd hi (Nat.not_lt_zero _)
      | cons s l ih =>
        cases i with
        | zero => exact Nat.succ_pos _
        | succ i => exact Nat.succ_lt_succ (ih (n - s) i (Nat.lt_of_succ_lt_succ hi))) =
      (l[i], n - (l.take (i + 1)).sum, false)
  | s :: l, n, 0, _ => by simp only [arityPlan, List.getElem_cons_zero, List.take_succ_cons,
      List.take_zero, List.sum_cons, List.sum_nil, add_zero]
  | s :: l, n, i + 1, hi => by
    simp only [arityPlan, List.getElem_cons_succ, List.take_succ_cons, List.sum_cons]
    rw [arityPlan_getElem l (n - s) i (Nat.lt_of_succ_lt_succ hi), Nat.sub_sub]

theorem length_arityPlan : ∀ (l : List ℕ) (n : ℕ), (arityPlan l n).length = l.length
  | [], _ => rfl
  | _ :: l, _ => congrArg (· + 1) (length_arityPlan l _)

/-- The plan of a setup's FRI without inputs folds by the setup's arities. -/
theorem plan_eq_arityPlan (S : Setup EF) :
    FriGame.Rounds.plan S.params.maxLogArity (S.params.logFinalPolyLen + S.params.logBlowup)
        (S.logN + S.params.logBlowup) (S.logN + S.params.logBlowup) [] =
      arityPlan (S.foldArities.map PNat.val) (S.logN + S.params.logBlowup) := by
  have hf := S.valid.finalPolyFits
  rw [plan_nil _ _ S.valid.folds _ _ (by omega) (Nat.sub_le _ _), Setup.foldArities]
  congr 3
  omega

/-- Fold `i` of a setup's FRI is entry `i` of its plan: its arity and the domain it folds onto. -/
theorem schedule_mem_plan (S : Setup EF) (i : Fin (S.lastFold + 1)) :
    ((S.schedule i : ℕ), S.logN + S.params.logBlowup -
        Fri.Spec.foldingPrefix S.schedule i.castSucc - S.schedule i, false) ∈
      FriGame.Rounds.plan S.params.maxLogArity (S.params.logFinalPolyLen + S.params.logBlowup)
        (S.logN + S.params.logBlowup) (S.logN + S.params.logBlowup) [] := by
  have hne := Setup.foldArities_ne_nil S
  have hlen : S.lastFold + 1 = S.foldArities.length := by
    unfold Setup.lastFold
    have := List.length_pos_iff.mpr hne
    omega
  set l := S.foldArities.map PNat.val with hl
  have hi : (i : ℕ) < l.length := by rw [hl, List.length_map, ← hlen]; exact i.2
  have hs (j : Fin (S.lastFold + 1)) : (S.schedule j : ℕ) = l[(j : ℕ)]'(by
      rw [hl, List.length_map, ← hlen]; exact j.2) := by
    simp only [Setup.schedule, hl, List.getElem_map]
    rw [List.getD_eq_getElem]
  -- the prefix is the sum of the arities before `i`
  have hpre : ∀ j : Fin (S.lastFold + 2), (j : ℕ) ≤ S.lastFold + 1 →
      Fri.Spec.foldingPrefix S.schedule j = (l.take j).sum := by
    intro j hj
    induction j using Fin.induction with
    | zero => rw [Fri.Spec.foldingPrefix_zero, Fin.val_zero, List.take_zero, List.sum_nil]
    | succ j ih =>
      rw [Fri.Spec.foldingPrefix_succ, ih (by simp only [Fin.val_castSucc]; omega), hs j,
        Fin.val_succ, Fin.val_castSucc, List.sum_take_succ]
  rw [plan_eq_arityPlan, List.mem_iff_getElem]
  refine ⟨i, by rw [length_arityPlan]; exact hi, ?_⟩
  rw [arityPlan_getElem l _ i hi, hpre i.castSucc (by simp only [Fin.val_castSucc]; omega), hs i,
    Fin.val_castSucc, List.sum_take_succ, Nat.sub_sub]

/-- The largest error of FRI's folds at any arity, for `δ ≤ (1 - rate) / 2` and a proximity loss
`loss > 0`: the largest level bound of its folds' plan over `|𝕂|`, for any `δ_int > δ`. -/
theorem friFoldError_le (S : Setup EF) (δ δ_int loss : ℝ≥0) (hδ : (δ : ℝ) ≤ (1 - S.rate) / 2)
    (h_pos : 0 < δ) (h_lt : δ < δ_int) (h_loss : 0 < loss) :
    ⨆ i, friFoldError S δ loss i ≤
      ENNReal.ofReal (planMax (2 ^ S.params.logBlowup) δ δ_int loss
        (FriGame.Rounds.plan S.params.maxLogArity (S.params.logFinalPolyLen + S.params.logBlowup)
          (S.logN + S.params.logBlowup) (S.logN + S.params.logBlowup) []) /
        (Fintype.card 𝕂 : ℝ)) := by
  have hK : (0 : ℝ) < Fintype.card 𝕂 := by exact_mod_cast Fintype.card_pos
  have hc : 0 < 2 ^ S.params.logBlowup := Nat.two_pow_pos _
  have hfin := S.valid.finalPolyFits
  have hsum := Setup.sum_schedule S
  have h : 2 ^ S.params.logBlowup * (2 ^ (∑ j, (S.schedule j).val) *
      (finalDegree S.params.logFinalPolyLen).val) = 2 ^ (S.logN + S.params.logBlowup) := by
    change 2 ^ S.params.logBlowup * (2 ^ _ * 2 ^ S.params.logFinalPolyLen) = _
    rw [hsum, ← pow_add, ← pow_add]
    congr 1
    omega
  have hδ' : (δ : ℝ) ≤ (1 - 1 / ((2 ^ S.params.logBlowup : ℕ) : ℝ)) / 2 := by
    rw [rate_eq] at hδ
    push_cast
    exact hδ
  refine iSup_le fun i ↦ ?_
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
    (le_planMax _ δ δ_int loss (schedule_mem_plan S i)) hK.le))
  rw [foldWords_false]
  set m := S.logN + S.params.logBlowup - Fri.Spec.foldingPrefix S.schedule i.castSucc -
    (S.schedule i : ℕ)
  have hudr : (δ : ℝ) * (2 * (2 ^ S.params.logBlowup : ℕ)) ≤ (2 ^ S.params.logBlowup : ℕ) - 1 :=
    mul_le_of_le_udr S δ hδ
  have hmca : (friFoldError S δ loss i : ENNReal) ≤
      ENNReal.ofReal ((2 ^ (S.schedule i : ℕ) - 1 : ℕ) * 2 ^ m / Fintype.card 𝕂) := by
    refine (foldingErrorLossy_le_foldingError _ _ i _ _ loss.coe_nonneg).trans
      ((foldingError_le _ hc _ _ i h δ hudr).trans (le_of_eq ?_))
    rw [ENNReal.ofReal_div_of_pos hK, ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast]
    push_cast
    rfl
  unfold levelBound
  split_ifs with hl
  · have hlossy := foldingErrorLossy_le (ω := S.domain) (2 ^ S.params.logBlowup) S.schedule
      (finalDegree S.params.logFinalPolyLen) i h δ δ_int loss (by push_cast at hl ⊢; exact hl)
      h_pos h_lt h_loss
    have hM : ((2 ^ (S.schedule i : ℕ) - 1 : ℕ) : ℝ) = 2 ^ (S.schedule i : ℕ) - 1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      rfl
    rw [mul_min_of_nonneg _ _ (Nat.cast_nonneg _), ← min_div_div_right hK.le, ENNReal.ofReal_min]
    refine le_min ?_ hmca
    rw [hM]
    exact hlossy
  · exact hmca

/-- FRI's queries at any arity: `(1 - δ + #folds · loss + 1/p) ^ numQueries`, one fold per entry of
the plan. -/
theorem friQueryError_eq (S : Setup EF) (δ loss : ℝ≥0) :
    friQueryError S δ loss =
      ENNReal.ofReal (1 - δ + (FriGame.Rounds.plan S.params.maxLogArity
        (S.params.logFinalPolyLen + S.params.logBlowup) (S.logN + S.params.logBlowup)
        (S.logN + S.params.logBlowup) []).length * loss + 1 / Nat.card F) ^
          S.params.numQueries := by
  have hne := Setup.foldArities_ne_nil S
  have hlen : (S.lastFold : ℝ) + 1 = (FriGame.Rounds.plan S.params.maxLogArity
      (S.params.logFinalPolyLen + S.params.logBlowup) (S.logN + S.params.logBlowup)
      (S.logN + S.params.logBlowup) []).length := by
    rw [plan_eq_arityPlan, length_arityPlan, List.length_map, Setup.lastFold]
    have := List.length_pos_iff.mpr hne
    norm_cast
    omega
  rw [friQueryError, min_eq_right (by nlinarith [loss.coe_nonneg]), ← hlen]
  congr 2
  ring

/-! ### The numbers -/

/-- A radius `x - 2 ^ (-a)`, `2 ^ (-a) ≤ x`, as a real number. -/
theorem coe_sub_two_zpow (x : NNReal) (k : ℤ) (a : ℕ) (hk : k = -a) (h : 1 / 2 ^ a ≤ (x : ℝ)) :
    ((x - 2 ^ k : NNReal) : ℝ) = x - 1 / 2 ^ a := by
  subst hk
  rw [NNReal.coe_sub, zpow_neg, zpow_natCast]
  · push_cast
    ring
  · rw [zpow_neg, zpow_natCast, ← NNReal.coe_le_coe]
    push_cast
    rwa [one_div] at h

end CompStark.Sound
