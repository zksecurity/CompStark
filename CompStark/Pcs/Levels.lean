/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.Multiplicity
public import CompStark.Pcs.Errors

/-! Kernel-checked numerical levels of the WHIR error rows. A schedule's encoded levels are read
as natural-number records; `levelsCheck` decides rational bounds on every row, and
`whirErrorRows_le` turns a successful check into `2^-κ` bounds on the exact real errors. -/

@[expose] public section

namespace CompStark.Pcs

open CompStark.BinaryFields CompStark.Multilinear
open CompStark.Pcs (johnsonLevelSecurity)
open scoped ENNReal

/-- One encoded level: folded variables, remaining variables, inverse-rate exponent, column
queries and Johnson multiplicity. -/
structure Level where
  /-- Variables folded at this level. -/
  lanes : ℕ
  /-- Variables of the level's encoded code. -/
  tail : ℕ
  /-- Inverse-rate exponent. -/
  rate : ℕ
  /-- Column queries. -/
  queries : ℕ
  /-- Johnson multiplicity of the analysis. -/
  m : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- The encoded levels of a schedule with its Johnson multiplicities, in transcript order. -/
def scheduleLevels : {vars : ℕ} → (schedule : Whir.Schedule K vars) →
    Pcs.JohnsonParameters schedule → List Level
  | _, .last lanes tail encoding queries, m => [⟨lanes, tail, encoding.rate, queries, m⟩]
  | _, @Whir.Schedule.more _ tail lanes encoding queries rest, ms =>
      ⟨lanes, tail, encoding.rate, queries, ms.1⟩ :: scheduleLevels rest ms.2

/-- Binary precision of the square-root lower bounds behind `√ρ`. -/
def precision : ℕ := 20

/-- Lower bounds `⌊√((2^n - 1) 2^n) 2^20⌋` for `n = 2, …, 22`. -/
def sqrtLowerTable : List ℕ :=
  [3632373, 7846824, 16244469, 33025982, 66582511, 133692411, 267910654, 536346367, 1073217407,
    2146959295, 4294442975, 8589410287, 17179344887, 34359214075, 68718952445, 137438429182,
    274877382655, 549755289599, 1099511103487, 2199022731263, 4398045986815]

/-- The tabulated lower bound on `√((2^n - 1) 2^n)`, scaled by `2^20`. -/
def sqrtLower (n : ℕ) : ℕ := sqrtLowerTable.getD (n - 2) 0

/-- Rational upper bound `num / den ≥ 2^(r/2)`, using `√2 ≤ 99/70` for odd `r`. -/
def rootUpper (r : ℕ) : ℕ × ℕ := if r % 2 = 0 then (2 ^ (r / 2), 1) else (99 * 2 ^ (r / 2), 70)

namespace Level

/-- Scaled lower bound on `√((2^tail - 1) 2^tail)`. -/
def lo (level : Level) : ℕ := sqrtLower level.tail

/-- Numerator of the level's rational list size. -/
def listNum (level : Level) : ℕ := listNumerator level.tail level.rate level.m

/-- Denominator of the level's rational list size. -/
def listDen (level : Level) : ℕ := listDenominator level.tail

/-- Numerator of the rational lower bound `X / Y ≤ √ρ`. -/
def rootNum (level : Level) : ℕ := level.lo * (rootUpper level.rate).2

/-- Denominator of the rational lower bound `X / Y ≤ √ρ`. -/
def rootDen (level : Level) : ℕ := 2 ^ precision * 2 ^ level.tail * (rootUpper level.rate).1

/-- The level has message variables and an admissible multiplicity. -/
def admissibleCheck (level : Level) : Bool :=
  decide (0 < level.tail) && decide (Admissible level.tail level.rate level.m)

/-- The batching row with `claims` claims is at most `2^-κ`. -/
def batchCheck (κ claims : ℕ) (level : Level) : Bool :=
  decide ((claims - 1) * level.listNum * 2 ^ κ ≤ level.listDen * 2 ^ 192)

/-- Every fold row is at most `2^-κ`. -/
def foldCheck (κ : ℕ) (level : Level) : Bool :=
  decide (0 < level.rootNum) &&
    decide (level.rootNum ^ 2 * 2 ^ (level.tail + level.rate) ≤ (2 ^ level.tail - 1) * level.rootDen ^ 2) &&
    decide ((2 * level.listNum * (48 * level.rootNum ^ 3) * (2 * level.rootNum) +
        ((2 * level.m + 1) ^ 5 + 24 * (2 * level.m + 1)) * level.rootDen ^ 3 *
          2 ^ (level.tail + level.rate) * level.listDen * (2 * level.rootNum) +
        (2 * level.m + 1) * level.rootDen * level.listDen * (48 * level.rootNum ^ 3)) * 2 ^ κ ≤
      level.listDen * (48 * level.rootNum ^ 3) * (2 * level.rootNum) * 2 ^ 192)

/-- The OOD row entering this level is at most `2^-κ`. -/
def oodCheck (κ : ℕ) (level : Level) : Bool :=
  decide (level.listNum ^ 2 * (level.lanes + level.tail) * 2 ^ κ ≤ 2 * level.listDen ^ 2 * 2 ^ 192)

/-- The column-query row is at most `2^-κ`. -/
def queryCheck (κ : ℕ) (level : Level) : Bool :=
  decide (((2 ^ level.tail - 1) * (level.m + 1) ^ 2) ^ level.queries * 4 ^ κ ≤
    (2 ^ (level.tail + level.rate) * level.m ^ 2) ^ level.queries)

/-- The final residual batch and the closing rows after the last level are at most `2^-κ`. -/
def closeCheck (κ : ℕ) (level : Level) : Bool :=
  decide (level.queries * 2 ^ κ ≤ 2 ^ 192) && decide (2 * 2 ^ κ ≤ 2 ^ 192)

/-- An outer row with numerator at most `d`, charged at this level's list bound, is at most `2^-κ`. -/
def outerCheck (κ d : ℕ) (level : Level) : Bool :=
  decide (d * level.listNum * 2 ^ κ ≤ level.listDen * 2 ^ 192)

end Level

/-- Every WHIR row of a level list, with `claims` claims entering the first level, is at most
`2^-κ`, column queries at most `2^-κq`. -/
def levelsCheck (κ κq : ℕ) : List Level → ℕ → Bool
  | [], _ => true
  | [level], claims => level.admissibleCheck && level.batchCheck κ claims && level.foldCheck κ &&
      level.queryCheck κq && level.closeCheck κ
  | level :: next :: rest, claims => level.admissibleCheck && level.batchCheck κ claims &&
      level.foldCheck κ && level.queryCheck κq && next.admissibleCheck && next.oodCheck κ &&
      levelsCheck κ κq (next :: rest) (level.queries + 2)

/-- The certified bound of a row: `2^-κq` for column queries and `2^-κ` otherwise. -/
noncomputable def rowBound (κ κq : ℕ) : Pcs.WhirChallenge → ℝ≥0∞
  | .queries _ => ((2 : ℝ≥0∞) ^ κq)⁻¹
  | _ => ((2 : ℝ≥0∞) ^ κ)⁻¹

section Generic

variable {tail : ℕ} (encoding : Whir.Encoding K tail)

/-- A level's admissibility check yields the hypotheses of the rational error bounds. -/
theorem Level.admissibleCheck_spec {lanes queries m : ℕ}
    (check : (Level.mk lanes tail encoding.rate queries m).admissibleCheck = true) :
    0 < tail ∧ 3 ≤ m := by
  simp only [Level.admissibleCheck, Bool.and_eq_true] at check
  exact ⟨of_decide_eq_true check.1, (of_decide_eq_true check.2).1⟩

/-- Fold rows at a checked level are at most `2^-κ`. -/
theorem foldError_le_of_check {lanes queries m κ : ℕ}
    (list : (Level.mk lanes tail encoding.rate queries m).admissibleCheck = true)
    (check : (Level.mk lanes tail encoding.rate queries m).foldCheck κ = true) :
    Whir.foldError (E := E) encoding (johnsonLevelSecurity tail encoding.rate m) ≤ ((2 : ℝ≥0∞) ^ κ)⁻¹ := by
  obtain ⟨hn, hm⟩ := Level.admissibleCheck_spec encoding list
  simp only [Level.foldCheck, Bool.and_eq_true, decide_eq_true_eq] at check
  exact foldError_le encoding m _ _ κ hm hn check.1.1 check.1.2 check.2

/-- The batching row at a checked level is at most `2^-κ`. -/
theorem batchError_le_of_check {lanes queries m κ claims : ℕ}
    (list : (Level.mk lanes tail encoding.rate queries m).admissibleCheck = true)
    (check : (Level.mk lanes tail encoding.rate queries m).batchCheck κ claims = true) :
    Whir.batchError (E := E) encoding (johnsonLevelSecurity tail encoding.rate m) claims ≤
      ((2 : ℝ≥0∞) ^ κ)⁻¹ := by
  obtain ⟨hn, hm⟩ := Level.admissibleCheck_spec encoding list
  simp only [Level.batchCheck, decide_eq_true_eq] at check
  exact batchError_le encoding m claims κ (by omega) hn check

/-- The OOD row entering a checked level is at most `2^-κ`. -/
theorem oodError_le_of_check {lanes queries m κ : ℕ}
    (list : (Level.mk lanes tail encoding.rate queries m).admissibleCheck = true)
    (check : (Level.mk lanes tail encoding.rate queries m).oodCheck κ = true) :
    Whir.oodError (E := E) encoding (johnsonLevelSecurity tail encoding.rate m) (lanes + tail) ≤
      ((2 : ℝ≥0∞) ^ κ)⁻¹ := by
  obtain ⟨hn, hm⟩ := Level.admissibleCheck_spec encoding list
  simp only [Level.oodCheck, decide_eq_true_eq] at check
  exact oodError_le encoding m (lanes + tail) κ (by omega) hn check

/-- The column-query row at a checked level is at most `2^-κ`. -/
theorem queryError_le_of_check {lanes queries m κ : ℕ}
    (list : (Level.mk lanes tail encoding.rate queries m).admissibleCheck = true)
    (check : (Level.mk lanes tail encoding.rate queries m).queryCheck κ = true) :
    Whir.queryError encoding (johnsonLevelSecurity tail encoding.rate m) queries ≤ ((2 : ℝ≥0∞) ^ κ)⁻¹ := by
  obtain ⟨-, hm⟩ := Level.admissibleCheck_spec encoding list
  simp only [Level.queryCheck, decide_eq_true_eq] at check
  exact queryError_le encoding m queries κ (by omega) check

/-- An outer row with numerator at most `D` at a checked initial level is at most `2^-κ`. -/
theorem outerError_le_of_check {lanes queries m κ d D : ℕ} (hd : d ≤ D)
    (list : (Level.mk lanes tail encoding.rate queries m).admissibleCheck = true)
    (check : (Level.mk lanes tail encoding.rate queries m).outerCheck κ D = true) :
    Pcs.outerError (Whir.listBound encoding (johnsonLevelSecurity tail encoding.rate m)) d ≤
      ((2 : ℝ≥0∞) ^ κ)⁻¹ := by
  obtain ⟨hn, hm⟩ := Level.admissibleCheck_spec encoding list
  simp only [Level.outerCheck, decide_eq_true_eq] at check
  exact outerError_le encoding m d κ (by omega) hn
    ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hd)).trans check)

end Generic

/-- The final batch and closing rows after a checked last level are at most `2^-κ`. -/
theorem close_le_of_check {level : Level} {κ : ℕ} (check : level.closeCheck κ = true) :
    overE level.queries ≤ ((2 : ℝ≥0∞) ^ κ)⁻¹ ∧ overE 2 ≤ ((2 : ℝ≥0∞) ^ κ)⁻¹ := by
  simp only [Level.closeCheck, Bool.and_eq_true, decide_eq_true_eq] at check
  exact ⟨overE_le _ κ check.1, overE_le 2 κ check.2⟩

/-- The OOD row entering a schedule is at most `2^-κ` when its first level is checked. -/
theorem enteringOodError_le {vars : ℕ} (schedule : Whir.Schedule K vars)
    (johnson : Pcs.JohnsonParameters schedule) (next : Level) (rest : List Level) (κ : ℕ)
    (levels : scheduleLevels schedule johnson = next :: rest)
    (list : next.admissibleCheck = true) (check : next.oodCheck κ = true) :
    Whir.enteringOodError (E := E) schedule (Pcs.johnsonSecurity schedule johnson) ≤
      ((2 : ℝ≥0∞) ^ κ)⁻¹ := by
  cases schedule with
  | last lanes tail encoding queries =>
    simp only [scheduleLevels, List.cons.injEq] at levels
    obtain ⟨rfl, -⟩ := levels
    exact oodError_le_of_check encoding list check
  | more lanes encoding queries rest' =>
    simp only [scheduleLevels, List.cons.injEq] at levels
    obtain ⟨rfl, -⟩ := levels
    exact oodError_le_of_check encoding list check

/-- A schedule always has a first encoded level. -/
theorem scheduleLevels_cons {vars : ℕ} (schedule : Whir.Schedule K vars)
    (johnson : Pcs.JohnsonParameters schedule) :
    ∃ next rest, scheduleLevels schedule johnson = next :: rest := by
  cases schedule <;> exact ⟨_, _, rfl⟩

/-- A successful level check bounds every WHIR error row. -/
theorem whirErrorRows_le (κ κq : ℕ) : {vars : ℕ} → (schedule : Whir.Schedule K vars) →
    (johnson : Pcs.JohnsonParameters schedule) → (claims level : ℕ) →
    levelsCheck κ κq (scheduleLevels schedule johnson) claims = true →
    ∀ row ∈ Pcs.whirErrorRows schedule (Pcs.johnsonSecurity schedule johnson) claims level,
      row.error ≤ rowBound κ κq row.challenge
  | _, .last lanes tail encoding queries, m, claims, level, check => by
    simp only [scheduleLevels, levelsCheck, Bool.and_eq_true] at check
    obtain ⟨⟨⟨⟨list, batch⟩, fold⟩, query⟩, close⟩ := check
    have closing := close_le_of_check close
    intro row member
    simp only [Pcs.whirErrorRows, Pcs.johnsonSecurity, List.cons_append,
      List.mem_cons, List.mem_append, List.mem_map, List.mem_range, List.not_mem_nil, false_or, or_false,
      or_assoc] at member
    rcases member with h | ⟨i, -, h⟩ | h | h | ⟨i, -, h⟩ <;> subst h
    · exact batchError_le_of_check encoding list batch
    · exact foldError_le_of_check encoding list fold
    · exact queryError_le_of_check encoding list query
    · exact closing.1
    · exact closing.2
  | _, @Whir.Schedule.more _ tail lanes encoding queries rest, ms, claims, level, check => by
    obtain ⟨next, others, nextEq⟩ := scheduleLevels_cons rest ms.2
    simp only [scheduleLevels, nextEq, levelsCheck, Bool.and_eq_true] at check
    obtain ⟨⟨⟨⟨⟨⟨list, batch⟩, fold⟩, query⟩, nextList⟩, ood⟩, recurse⟩ := check
    rw [← nextEq] at recurse
    intro row member
    simp only [Pcs.whirErrorRows, Pcs.johnsonSecurity, List.cons_append,
      List.mem_cons, List.mem_append, List.mem_map, List.mem_range, List.not_mem_nil, false_or, or_false,
      or_assoc] at member
    rcases member with h | ⟨i, -, h⟩ | h | h | member
    all_goals try subst h
    · exact batchError_le_of_check encoding list batch
    · exact foldError_le_of_check encoding list fold
    · exact enteringOodError_le rest ms.2 next others κ nextEq nextList ood
    · exact queryError_le_of_check encoding list query
    · exact whirErrorRows_le κ κq rest ms.2 (queries + 2) (level + 1) recurse row member

/-- The head level's list bound is the composed initial list bound. -/
theorem initialListBound_eq {vars : ℕ} (schedule : Whir.Schedule K vars)
    (johnson : Pcs.JohnsonParameters schedule) :
    ∃ (tail : ℕ) (encoding : Whir.Encoding K tail) (rest : List Level),
      scheduleLevels schedule johnson =
          ⟨schedule.lanes, tail, encoding.rate, (scheduleLevels schedule johnson).head!.queries,
            (scheduleLevels schedule johnson).head!.m⟩ :: rest ∧
        Pcs.initialListBound schedule (Pcs.johnsonSecurity schedule johnson) =
          Whir.listBound encoding
            (johnsonLevelSecurity tail encoding.rate (scheduleLevels schedule johnson).head!.m) := by
  cases schedule with
  | last lanes tail encoding queries => exact ⟨tail, encoding, [], rfl, rfl⟩
  | more lanes encoding queries rest => exact ⟨_, encoding, _, rfl, rfl⟩

/-- Every outer row at a checked initial level is at most `2^-κ` when its numerator is at most `D`. -/
theorem initialOuterError_le {vars : ℕ} (schedule : Whir.Schedule K vars)
    (johnson : Pcs.JohnsonParameters schedule) (κ d D : ℕ) (hd : d ≤ D)
    (list : ((scheduleLevels schedule johnson).head!).admissibleCheck = true)
    (check : ((scheduleLevels schedule johnson).head!).outerCheck κ D = true) :
    Pcs.outerError (Pcs.initialListBound schedule (Pcs.johnsonSecurity schedule johnson)) d ≤
      ((2 : ℝ≥0∞) ^ κ)⁻¹ := by
  cases schedule with
  | last lanes tail encoding queries => exact outerError_le_of_check encoding hd list check
  | more lanes encoding queries rest => exact outerError_le_of_check encoding hd list check

end CompStark.Pcs
