/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.FriGame

/-! # Plonky3's folding schedule as FRI rounds

`schedule` builds FRI's rounds (`FriGame.Rounds`) as Plonky3's `fold_schedule` (`foldSchedule`)
does for inputs of log heights `m₁ > m₂ > …` below the tallest: from height `n`, fold by
`min (n - mᵢ) (n - logFinal) maxLogArity` towards the next input's height `mᵢ` and the final
height, and inject the input `words mᵢ` when its height is reached.

For heights strictly decreasing, all below `n` and at least `logFinal` (`Fits`), the last one
possibly the final height itself, the rounds reach the final height exactly (`degree_schedule`:
the code before them has degree bound `2 ^ (n - logFinal) d`), and every input is injected:
inputs agreeing in the rounds means each input agrees with its code, on a domain the folds reach
from the first (`agrees_of_inputsAgree`). From the final height, the rounds are `.final`, without
folds. `plan` lists the folds as data, one per fold (`numFolds_schedule`). The rounds' errors
depend on the heights only, not on the words (`foldError_schedule_congr`).
-/

@[expose] public section

namespace CompStark.Sound.FriGame

open Domain FriInject

variable {K : Type}

namespace Rounds

/-- The log arity of the fold from height `n`: towards the next input's height and the final
height, at most `maxLogArity`. -/
def logArity (maxLogArity logFinal n : ℕ) (heights : List ℕ) : ℕ :=
  min (min (n - heights.headD logFinal) (n - logFinal)) maxLogArity

theorem logArity_le (maxLogArity logFinal n : ℕ) (heights : List ℕ) :
    logArity maxLogArity logFinal n heights ≤ n - logFinal :=
  (min_le_left _ _).trans (min_le_right _ _)

/-- The fold towards the next input does not pass it. -/
theorem logArity_le_cons (maxLogArity logFinal n m : ℕ) (rest : List ℕ) :
    logArity maxLogArity logFinal n (m :: rest) ≤ n - m :=
  (min_le_left _ _).trans (min_le_left _ _)

/-- Plonky3's folding schedule from height `n` down to `logFinal`, injecting `words m` at each
height `m` of `heights` (tallest first), with `fuel` rounds at most. -/
def schedule (maxLogArity logFinal : ℕ) (words : (m : ℕ) → Fin (2 ^ m) → K) :
    (fuel n : ℕ) → List ℕ → Rounds K n
  | 0, _, _ => .final
  | fuel + 1, n, heights =>
    if n ≤ logFinal then .final else
      let la := logArity maxLogArity logFinal n heights
      have hla : la ≤ n := (logArity_le _ _ _ _).trans (Nat.sub_le _ _)
      match heights with
      | [] => .fold la hla none (schedule maxLogArity logFinal words fuel (n - la) [])
      | m :: rest =>
        if m = n - la then
          .fold la hla (some (words (n - la)))
            (schedule maxLogArity logFinal words fuel (n - la) rest)
        else .fold la hla none (schedule maxLogArity logFinal words fuel (n - la) (m :: rest))

/-- Heights fit below height `n`: strictly decreasing, all below `n` and at least `logFinal`. -/
def Fits (logFinal n : ℕ) (heights : List ℕ) : Prop :=
  heights.Pairwise (· > ·) ∧ ∀ m ∈ heights, logFinal ≤ m ∧ m < n

theorem fits_nil (logFinal n : ℕ) : Fits logFinal n [] :=
  ⟨List.Pairwise.nil, fun _ h ↦ absurd h List.not_mem_nil⟩

/-- The fold from a height above the final one, with fitting heights, is by at least one bit. -/
theorem one_le_logArity {maxLogArity logFinal n : ℕ} (ha : 0 < maxLogArity) (hn : logFinal < n)
    {heights : List ℕ} (hfit : Fits logFinal n heights) :
    1 ≤ logArity maxLogArity logFinal n heights := by
  unfold logArity
  have hhead : heights.headD logFinal < n := by
    cases heights with
    | nil => exact hn
    | cons m _ => exact (hfit.2 m List.mem_cons_self).2
  omega

/-- After a fold that does not reach the next height, the heights still fit. -/
theorem fits_cons_of_ne {logFinal n la m : ℕ} {rest : List ℕ} (hfit : Fits logFinal n (m :: rest))
    (hla : la ≤ n - m) (hm : ¬ m = n - la) : Fits logFinal (n - la) (m :: rest) := by
  refine ⟨hfit.1, fun m' hm' ↦ ⟨(hfit.2 m' hm').1, ?_⟩⟩
  have hm0 := hfit.2 m List.mem_cons_self
  rcases List.mem_cons.mp hm' with rfl | hm'
  · omega
  · have := List.rel_of_pairwise_cons hfit.1 hm'
    omega

/-- After the fold that reaches the next height, the rest fit. -/
theorem fits_of_eq {logFinal n la m : ℕ} {rest : List ℕ} (hfit : Fits logFinal n (m :: rest))
    (hm : m = n - la) : Fits logFinal (n - la) rest := by
  refine ⟨(List.pairwise_cons.mp hfit.1).2, fun m' hm' ↦
    ⟨(hfit.2 m' (List.mem_cons_of_mem _ hm')).1, ?_⟩⟩
  have := List.rel_of_pairwise_cons hfit.1 hm'
  omega

/-- The rounds reach the final height exactly: the code before them has degree bound
`2 ^ (n - logFinal) d`. -/
theorem degree_schedule {maxLogArity logFinal : ℕ} (ha : 0 < maxLogArity)
    (words : (m : ℕ) → Fin (2 ^ m) → K) (d : ℕ) :
    ∀ (fuel n : ℕ) (heights : List ℕ), logFinal ≤ n → n - logFinal ≤ fuel →
      Fits logFinal n heights →
      (schedule maxLogArity logFinal words fuel n heights).degree d = 2 ^ (n - logFinal) * d
  | 0, n, _, hn, hfuel, _ => by
    rw [schedule, degree, show n - logFinal = 0 by omega, pow_zero, one_mul]
  | fuel + 1, n, heights, hn, hfuel, hfit => by
    by_cases hfin : n ≤ logFinal
    · rw [schedule, ite_eq_left hfin, degree, show n - logFinal = 0 by omega, pow_zero, one_mul]
    have h1 := one_le_logArity ha (by omega) hfit
    have h2 := logArity_le maxLogArity logFinal n heights
    have hpow (la r : ℕ) (hla : 1 ≤ la) (hle : la ≤ n - logFinal)
        (hr : r = 2 ^ (n - la - logFinal) * d) : 2 ^ la * r = 2 ^ (n - logFinal) * d := by
      rw [hr, ← mul_assoc, ← pow_add]
      congr 2
      omega
    rw [schedule, ite_eq_right hfin]
    match heights, hfit, h1, h2 with
    | [], _, h1, h2 =>
      exact hpow _ _ h1 h2 (degree_schedule ha words d fuel _ [] (by omega) (by omega)
        (fits_nil _ _))
    | m :: rest, hfit, h1, h2 =>
      have h3 := logArity_le_cons maxLogArity logFinal n m rest
      by_cases hm : m = n - logArity maxLogArity logFinal n (m :: rest)
      · simp only [ite_eq_left hm, degree]
        exact hpow _ _ h1 h2 (degree_schedule ha words d fuel _ rest (by omega) (by omega)
          (fits_of_eq hfit hm))
      · simp only [ite_eq_right hm, degree]
        exact hpow _ _ h1 h2 (degree_schedule ha words d fuel _ _ (by omega) (by omega)
          (fits_cons_of_ne hfit h3 hm))

/-- The folds of `schedule` as data, in order: each fold's log arity, the log size of the domain
it folds onto, and whether it injects an input there. -/
def plan (maxLogArity logFinal : ℕ) : (fuel n : ℕ) → List ℕ → List (ℕ × ℕ × Bool)
  | 0, _, _ => []
  | fuel + 1, n, heights =>
    if n ≤ logFinal then [] else
      let la := logArity maxLogArity logFinal n heights
      match heights with
      | [] => (la, n - la, false) :: plan maxLogArity logFinal fuel (n - la) []
      | m :: rest =>
        if m = n - la then (la, n - la, true) :: plan maxLogArity logFinal fuel (n - la) rest
        else (la, n - la, false) :: plan maxLogArity logFinal fuel (n - la) (m :: rest)

/-- The words a fold of the plan batches by powers of its challenge besides the first: the other
`2 ^ la - 1` coefficient words of a fold by `2 ^ la`, and the input it injects, if any. -/
def foldWords (f : ℕ × ℕ × Bool) : ℕ := 2 ^ f.1 - 1 + if f.2.2 then 1 else 0

/-- Every fold of the plan from height `n`, for fitting heights, is by `1` to `maxLogArity`
bits onto a height from `logFinal` to below `n`. -/
theorem mem_plan {maxLogArity logFinal : ℕ} (ha : 0 < maxLogArity) :
    ∀ (fuel n : ℕ) (heights : List ℕ), Fits logFinal n heights →
      ∀ f ∈ plan maxLogArity logFinal fuel n heights,
        1 ≤ f.1 ∧ f.1 ≤ maxLogArity ∧ logFinal ≤ f.2.1 ∧ f.2.1 < n
  | 0, _, _, _, f, hf => absurd hf List.not_mem_nil
  | fuel + 1, n, heights, hfit, f, hf => by
    by_cases hfin : n ≤ logFinal
    · rw [plan, ite_eq_left hfin] at hf
      exact absurd hf List.not_mem_nil
    have h1 := one_le_logArity ha (by omega) hfit
    have h2 := logArity_le maxLogArity logFinal n heights
    have h3 : logArity maxLogArity logFinal n heights ≤ maxLogArity := min_le_right _ _
    have hhead : 1 ≤ logArity maxLogArity logFinal n heights ∧
        logArity maxLogArity logFinal n heights ≤ maxLogArity ∧
        logFinal ≤ n - logArity maxLogArity logFinal n heights ∧
        n - logArity maxLogArity logFinal n heights < n := ⟨h1, h3, by omega, by omega⟩
    have hrest : ∀ heights', Fits logFinal (n - logArity maxLogArity logFinal n heights) heights' →
        ∀ f ∈ plan maxLogArity logFinal fuel (n - logArity maxLogArity logFinal n heights)
          heights', 1 ≤ f.1 ∧ f.1 ≤ maxLogArity ∧ logFinal ≤ f.2.1 ∧ f.2.1 < n :=
      fun heights' hfit' f hf ↦ by
        have := mem_plan ha fuel _ heights' hfit' f hf
        omega
    rw [plan, ite_eq_right hfin] at hf
    match heights, hfit, hhead, hrest, hf with
    | [], _, hhead, hrest, hf =>
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hhead
      · exact hrest [] (fits_nil _ _) f hf
    | m :: rest, hfit, hhead, hrest, hf =>
      have h4 := logArity_le_cons maxLogArity logFinal n m rest
      by_cases hm : m = n - logArity maxLogArity logFinal n (m :: rest)
      · dsimp only at hf
        rw [ite_eq_left hm] at hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact hhead
        · exact hrest rest (fits_of_eq hfit hm) f hf
      · dsimp only at hf
        rw [ite_eq_right hm] at hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact hhead
        · exact hrest _ (fits_cons_of_ne hfit h4 hm) f hf

/-- The plan from height `n` has at most `n - logFinal` folds, for fitting heights. -/
theorem length_plan_le {maxLogArity logFinal : ℕ} (ha : 0 < maxLogArity) :
    ∀ (fuel n : ℕ) (heights : List ℕ), Fits logFinal n heights →
      (plan maxLogArity logFinal fuel n heights).length ≤ n - logFinal
  | 0, _, _, _ => Nat.zero_le _
  | fuel + 1, n, heights, hfit => by
    by_cases hfin : n ≤ logFinal
    · rw [plan, ite_eq_left hfin, List.length_nil]
      exact Nat.zero_le _
    have h1 := one_le_logArity ha (by omega) hfit
    have h2 := logArity_le maxLogArity logFinal n heights
    rw [plan, ite_eq_right hfin]
    match heights, hfit, h1, h2 with
    | [], _, h1, h2 =>
      have := length_plan_le (logFinal := logFinal) ha fuel (n - logArity maxLogArity logFinal n [])
        [] (fits_nil _ _)
      simp only [List.length_cons]
      omega
    | m :: rest, hfit, h1, h2 =>
      have h4 := logArity_le_cons maxLogArity logFinal n m rest
      by_cases hm : m = n - logArity maxLogArity logFinal n (m :: rest)
      · have := length_plan_le ha fuel _ rest (fits_of_eq hfit hm)
        simp only [ite_eq_left hm, List.length_cons]
        omega
      · have := length_plan_le ha fuel _ _ (fits_cons_of_ne hfit h4 hm)
        simp only [ite_eq_right hm, List.length_cons]
        omega

/-- The rounds have one fold per entry of the plan. -/
theorem numFolds_schedule (maxLogArity logFinal : ℕ) (words : (m : ℕ) → Fin (2 ^ m) → K) :
    ∀ (fuel n : ℕ) (heights : List ℕ),
      (schedule maxLogArity logFinal words fuel n heights).numFolds =
        (plan maxLogArity logFinal fuel n heights).length
  | 0, _, _ => rfl
  | fuel + 1, n, heights => by
    by_cases hfin : n ≤ logFinal
    · simp only [schedule, plan, ite_eq_left hfin, numFolds, List.length_nil]
    have ih := numFolds_schedule maxLogArity logFinal words fuel
    match heights with
    | [] => simp only [schedule, plan, ite_eq_right hfin, numFolds, List.length_cons, ih]
    | m :: rest =>
      by_cases hm : m = n - logArity maxLogArity logFinal n (m :: rest)
      · simp only [schedule, plan, ite_eq_right hfin, ite_eq_left hm, numFolds,
          List.length_cons, ih]
      · simp only [schedule, plan, ite_eq_right hfin, ite_eq_right hm, numFolds,
          List.length_cons, ih]

/-- Without inputs, the rounds do not read the words. -/
theorem schedule_nil (maxLogArity logFinal : ℕ) (words words' : (m : ℕ) → Fin (2 ^ m) → K) :
    ∀ fuel n, schedule maxLogArity logFinal words fuel n [] =
      schedule maxLogArity logFinal words' fuel n []
  | 0, _ => rfl
  | fuel + 1, n => by
    simp only [schedule, schedule_nil maxLogArity logFinal words words' fuel]

variable [Field K]

/-- The rounds' fold errors, number of folds and degree depend on the heights only, not on the
words. -/
theorem foldError_schedule_congr [Fintype K] [DecidableEq K] [SampleableType K]
    (maxLogArity logFinal d : ℕ) (θ loss : ℝ) (words words' : (m : ℕ) → Fin (2 ^ m) → K) :
    ∀ (fuel n : ℕ) (ω : SmoothCosetFftDomain n K) (heights : List ℕ),
      (schedule maxLogArity logFinal words fuel n heights).foldError d θ loss ω =
          (schedule maxLogArity logFinal words' fuel n heights).foldError d θ loss ω ∧
        (schedule maxLogArity logFinal words fuel n heights).numFolds =
          (schedule maxLogArity logFinal words' fuel n heights).numFolds ∧
        (schedule maxLogArity logFinal words fuel n heights).degree d =
          (schedule maxLogArity logFinal words' fuel n heights).degree d
  | 0, _, _, _ => ⟨rfl, rfl, rfl⟩
  | fuel + 1, n, ω, heights => by
    by_cases hfin : n ≤ logFinal
    · simp only [schedule, ite_eq_left hfin, and_self]
    simp only [schedule, ite_eq_right hfin]
    have ih := foldError_schedule_congr maxLogArity logFinal d θ loss words words' fuel
    match heights with
    | [] =>
      obtain ⟨h1, h2, h3⟩ := ih (n - logArity maxLogArity logFinal n [])
        (ω.subdomain (logArity maxLogArity logFinal n [])) []
      simp only [foldError, numFolds, degree, h1, h2, h3, and_self]
    | m :: rest =>
      by_cases hm : m = n - logArity maxLogArity logFinal n (m :: rest)
      · obtain ⟨h1, h2, h3⟩ := ih (n - logArity maxLogArity logFinal n (m :: rest))
          (ω.subdomain (logArity maxLogArity logFinal n (m :: rest))) rest
        simp only [ite_eq_left hm, foldError, numFolds, degree, h1, h2, h3, and_self]
      · obtain ⟨h1, h2, h3⟩ := ih (n - logArity maxLogArity logFinal n (m :: rest))
          (ω.subdomain (logArity maxLogArity logFinal n (m :: rest))) (m :: rest)
        simp only [ite_eq_right hm, foldError, numFolds, degree, h1, h2, h3, and_self]

/-- Agreement of a word on a domain of an equal height. -/
theorem exists_agrees_cast (P : ∀ {m : ℕ}, SmoothCosetFftDomain m K → Prop)
    (words : (m : ℕ) → Fin (2 ^ m) → K) {m m' : ℕ} (h : m = m')
    (D : SmoothCosetFftDomain m' K) (hD : P D) (deg : ℕ) (ρ : ℝ)
    (hg : Agrees D deg ρ (words m')) :
    ∃ D' : SmoothCosetFftDomain m K, P D' ∧ Agrees D' deg ρ (words m) := by
  subst h
  exact ⟨D, hD, hg⟩

/-- Every input is injected: if the rounds' inputs agree with their codes, each input agrees with
its code, on a domain the folds reach from the first, which keeps any property `P` that
subdomains keep. -/
theorem agrees_of_inputsAgree {maxLogArity logFinal : ℕ} (ha : 0 < maxLogArity)
    (words : (m : ℕ) → Fin (2 ^ m) → K) (d : ℕ) (ρ : ℝ)
    (P : ∀ {m : ℕ}, SmoothCosetFftDomain m K → Prop)
    (hP : ∀ {m : ℕ} (D : SmoothCosetFftDomain m K) (k : ℕ), P D → P (D.subdomain k)) :
    ∀ (fuel n : ℕ) (ω : SmoothCosetFftDomain n K) (heights : List ℕ),
      logFinal ≤ n → n - logFinal ≤ fuel → Fits logFinal n heights → P ω →
      (schedule maxLogArity logFinal words fuel n heights).InputsAgree d ρ ω →
      ∀ m ∈ heights, ∃ D : SmoothCosetFftDomain m K, P D ∧
        Agrees D (2 ^ (m - logFinal) * d) ρ (words m)
  | 0, n, _, heights, hn, hfuel, hfit, _, _, m, hm => by
    have := hfit.2 m hm
    omega
  | fuel + 1, n, ω, heights, hn, hfuel, hfit, hω, hin, m', hm' => by
    have hx := hfit.2 m' hm'
    have hfin : ¬ n ≤ logFinal := by omega
    have h1 := one_le_logArity ha (by omega) hfit
    have h2 := logArity_le maxLogArity logFinal n heights
    rw [schedule, ite_eq_right hfin] at hin
    match heights, hfit, h1, h2, hin, hm' with
    | m :: rest, hfit, h1, h2, hin, hm' =>
      have h3 := logArity_le_cons maxLogArity logFinal n m rest
      by_cases hm : m = n - logArity maxLogArity logFinal n (m :: rest)
      · simp only [ite_eq_left hm, InputsAgree] at hin
        rcases List.mem_cons.mp hm' with rfl | hm'
        · refine exists_agrees_cast P words hm _ (hP ω _ hω) _ ρ ?_
          have hdeg := degree_schedule ha words d fuel _ rest (by omega) (by omega)
            (fits_of_eq hfit hm)
          rw [hdeg, show n - logArity maxLogArity logFinal n (m' :: rest) - logFinal =
            m' - logFinal by omega] at hin
          exact hin.1
        · exact agrees_of_inputsAgree ha words d ρ P hP fuel _ _ rest (by omega) (by omega)
            (fits_of_eq hfit hm) (hP ω _ hω) hin.2 m' hm'
      · simp only [ite_eq_right hm, InputsAgree] at hin
        exact agrees_of_inputsAgree ha words d ρ P hP fuel _ _ _ (by omega) (by omega)
          (fits_cons_of_ne hfit h3 hm) (hP ω _ hω) hin m' hm'

end Rounds

end CompStark.Sound.FriGame
