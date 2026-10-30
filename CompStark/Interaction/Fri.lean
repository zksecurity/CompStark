/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Fri
public import ArkLib.ProofSystem.Fri.Interaction.Soundness

/-! # The STARK's FRI on ArkLib's interaction layer

The STARK runs FRI as Plonky3 does: on the words on `L`, in the coordinate of the subgroup `⟨ω⟩` of
`2 ^ (logN + logBlowup)` points (`Setup.friDomain`), folding
along Plonky3's schedule (`Setup.friSchedule`, ArkLib's `Schedule.plonky3`) down to the final
polynomial's domain of `2 ^ (logFinalPolyLen + logBlowup)` points, injecting the words of the
shorter domains of log sizes `heights` when the folds reach them. ArkLib's FRI on the interaction
layer (`Fri.Interaction.protocol`) is that protocol, and its knowledge certificate bounds its
acceptance by `Fri.Interaction.error`. That error is the STARK's FRI error `friErrorWith`
(`friErrorWith_eq`): the schedules have the same folds and the same injections, and their codes
on `L` and on `⟨ω⟩` are the same words (`foldError_eq_of_isLevel`).
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound Domain

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-- CompStark's FRI rounds along Plonky3's schedule have ArkLib's schedule's fold errors, number
of folds and degree. -/
theorem foldError_schedule_eq {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [SampleableType K] (maxLogArity logFinal d : ℕ) (θ loss : ℝ)
    (words : (m : ℕ) → Fin (2 ^ m) → K) :
    ∀ (fuel n : ℕ) (ω : SmoothCosetFftDomain n K) (heights : List ℕ),
      (FriGame.Rounds.schedule maxLogArity logFinal words fuel n heights).foldError d θ loss ω =
          (Fri.Interaction.Schedule.plonky3 maxLogArity logFinal fuel n heights).foldError d θ
            loss ω ∧
        (FriGame.Rounds.schedule maxLogArity logFinal words fuel n heights).numFolds =
          (Fri.Interaction.Schedule.plonky3 maxLogArity logFinal fuel n heights).numFolds ∧
        (FriGame.Rounds.schedule maxLogArity logFinal words fuel n heights).degree d =
          (Fri.Interaction.Schedule.plonky3 maxLogArity logFinal fuel n heights).degree d
  | 0, _, _, _ => ⟨rfl, rfl, rfl⟩
  | fuel + 1, n, ω, heights => by
    by_cases hfin : n ≤ logFinal
    · simp only [FriGame.Rounds.schedule, Fri.Interaction.Schedule.plonky3, ite_eq_left hfin,
        FriGame.Rounds.foldError, Fri.Interaction.Schedule.foldError,
        FriGame.Rounds.numFolds, Fri.Interaction.Schedule.numFolds, FriGame.Rounds.degree,
        Fri.Interaction.Schedule.degree, and_self]
    simp only [FriGame.Rounds.schedule, Fri.Interaction.Schedule.plonky3, ite_eq_right hfin]
    have ih := foldError_schedule_eq maxLogArity logFinal d θ loss words fuel
    match heights with
    | [] =>
      obtain ⟨h1, h2, h3⟩ := ih (n - FriGame.Rounds.logArity maxLogArity logFinal n [])
        (ω.subdomain (FriGame.Rounds.logArity maxLogArity logFinal n [])) []
      simp only [FriGame.Rounds.foldError, Fri.Interaction.Schedule.foldError,
        Fri.Interaction.Schedule.roundError, FriGame.Rounds.numFolds,
        Fri.Interaction.Schedule.numFolds, FriGame.Rounds.degree, Fri.Interaction.Schedule.degree,
        h1, h2, h3]
      exact ⟨rfl, rfl, rfl⟩
    | m :: rest =>
      by_cases hm : m = n - FriGame.Rounds.logArity maxLogArity logFinal n (m :: rest)
      all_goals have hm' : (m = n - Fri.Interaction.Schedule.logArity maxLogArity logFinal n
        (m :: rest)) = (m = n - FriGame.Rounds.logArity maxLogArity logFinal n (m :: rest)) := rfl
      · obtain ⟨h1, h2, h3⟩ :=
          ih (n - FriGame.Rounds.logArity maxLogArity logFinal n (m :: rest))
            (ω.subdomain (FriGame.Rounds.logArity maxLogArity logFinal n (m :: rest)))
            rest
        simp only [hm', ite_eq_left hm, FriGame.Rounds.foldError,
          Fri.Interaction.Schedule.foldError, Fri.Interaction.Schedule.roundError,
          FriGame.Rounds.numFolds, Fri.Interaction.Schedule.numFolds, FriGame.Rounds.degree,
          Fri.Interaction.Schedule.degree, h1, h2, h3]
        exact ⟨rfl, rfl, rfl⟩
      · obtain ⟨h1, h2, h3⟩ :=
          ih (n - FriGame.Rounds.logArity maxLogArity logFinal n (m :: rest))
            (ω.subdomain (FriGame.Rounds.logArity maxLogArity logFinal n (m :: rest)))
            (m :: rest)
        simp only [hm', ite_eq_right hm, FriGame.Rounds.foldError,
          Fri.Interaction.Schedule.foldError, Fri.Interaction.Schedule.roundError,
          FriGame.Rounds.numFolds, Fri.Interaction.Schedule.numFolds, FriGame.Rounds.degree,
          Fri.Interaction.Schedule.degree, h1, h2, h3]
        exact ⟨rfl, rfl, rfl⟩

namespace Setup
variable {lookups : List (Lookup F)} (S : Setup EF lookups)

/-- FRI's schedule on `L`: Plonky3's, from `L` down to the final polynomial's domain of
`2 ^ (logFinalPolyLen + logBlowup)` points, injecting the words of the log sizes `heights`. -/
def friSchedule (heights : List ℕ) : Fri.Interaction.Schedule (S.logN + S.params.logBlowup) :=
  Fri.Interaction.Schedule.plonky3 S.params.maxLogArity
    (S.params.logFinalPolyLen + S.params.logBlowup) (S.logN + S.params.logBlowup)
    (S.logN + S.params.logBlowup) heights

/-- Each fold of FRI's schedule halves `L` at least once. -/
theorem arityPos_friSchedule (heights : List ℕ)
    (hfit : Fri.Interaction.Schedule.Fits (S.params.logFinalPolyLen + S.params.logBlowup)
      (S.logN + S.params.logBlowup) heights) :
    (S.friSchedule heights).ArityPos :=
  Fri.Interaction.Schedule.arityPos_plonky3 S.valid.folds _ _ heights hfit

/-- FRI's schedule tests the code of the trace's degree bound `n` on `L`. -/
theorem degree_friSchedule (heights : List ℕ)
    (hfit : Fri.Interaction.Schedule.Fits (S.params.logFinalPolyLen + S.params.logBlowup)
      (S.logN + S.params.logBlowup) heights) :
    (S.friSchedule heights).degree (2 ^ S.params.logFinalPolyLen) = S.n := by
  have h := S.valid.finalPolyFits
  rw [friSchedule, Fri.Interaction.Schedule.degree_plonky3 S.valid.folds _ _ _ heights (by omega)
    (Nat.sub_le _ _) hfit, ← pow_add]
  congr 1
  omega

end Setup

/-- Plonky3's schedule without inputs injects none: every input is in its code. -/
theorem inputsInCode_plonky3_nil {K : Type} [Field K] (inputs : (m : ℕ) → Fin (2 ^ m) → K)
    (maxLogArity logFinal d : ℕ) :
    ∀ (fuel n : ℕ) (ω : SmoothCosetFftDomain n K),
      (Fri.Interaction.Schedule.plonky3 maxLogArity logFinal fuel n []).InputsInCode inputs d ω
  | 0, _, _ => trivial
  | fuel + 1, n, ω => by
    by_cases hfin : n ≤ logFinal
    · simp only [Fri.Interaction.Schedule.plonky3, ite_eq_left hfin]
      trivial
    simp only [Fri.Interaction.Schedule.plonky3, ite_eq_right hfin,
      Fri.Interaction.Schedule.InputsInCode]
    exact inputsInCode_plonky3_nil inputs maxLogArity logFinal d fuel _ _

/-- FRI's fold errors depend on its domain only through its codes, which are the same on any two
cosets of one two-adic subgroup. -/
theorem foldError_eq_of_isLevel (d : ℕ) (θ loss : ℝ) :
    ∀ {n : ℕ} (s : Fri.Interaction.Schedule n) {ω ω' : SmoothCosetFftDomain n 𝕂},
      IsLevel ω → IsLevel ω' → s.foldError d θ loss ω = s.foldError d θ loss ω'
  | _, .final, _, _, _, _ => rfl
  | _, .fold k _ inject rest, ω, ω', h, h' => by
    have hc := le_antisymm
      (code_le_of_isLevel (isLevel_subdomain ω k h) (isLevel_subdomain ω' k h') (rest.degree d))
      (code_le_of_isLevel (isLevel_subdomain ω' k h') (isLevel_subdomain ω k h) (rest.degree d))
    have ih := foldError_eq_of_isLevel d θ loss rest (isLevel_subdomain ω k h)
      (isLevel_subdomain ω' k h')
    cases inject <;>
      simp only [Fri.Interaction.Schedule.foldError, Fri.Interaction.Schedule.roundError, hc, ih]

/-- **FRI's error is ArkLib's.** The STARK's FRI error with inputs injected at the log sizes
`heights` is the error of ArkLib's FRI on FRI's domain `⟨ω⟩` along Plonky3's schedule, with a final
polynomial of degree below `2 ^ logFinalPolyLen` and `numQueries` queries. -/
theorem friErrorWith_eq {lookups : List (Lookup F)} (S : Setup EF lookups) (heights : List ℕ)
    (δ : NNReal) :
    friErrorWith S heights δ = Fri.Interaction.error S.friDomain (S.friSchedule heights)
      (2 ^ S.params.logFinalPolyLen) S.params.numQueries δ := by
  unfold friErrorWith FriGame.error Fri.Interaction.error
  refine iInf_congr fun loss ↦ ?_
  obtain ⟨h1, h2, -⟩ := foldError_schedule_eq S.params.maxLogArity
    (S.params.logFinalPolyLen + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen) δ loss
    (fun _ _ ↦ 0) (S.logN + S.params.logBlowup) (S.logN + S.params.logBlowup) S.domain heights
  rw [Setup.friRounds, h1, h2, foldError_eq_of_isLevel _ _ _ _ (ω := S.domain)
    (ω' := S.friDomain) (isLevel_cosetDomain (EF := EF) _ S.valid.twoAdic)
    (isLevel_subgroupDomain (EF := EF) _ S.valid.twoAdic)]
  rfl

/-- FRI's error without injected inputs is ArkLib's along Plonky3's schedule without inputs. -/
theorem friError_eq {lookups : List (Lookup F)} (S : Setup EF lookups) (δ : NNReal) :
    friError S δ = Fri.Interaction.error S.friDomain (S.friSchedule [])
      (2 ^ S.params.logFinalPolyLen) S.params.numQueries δ :=
  friErrorWith_eq S [] δ

end CompStark.Iop
