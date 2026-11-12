/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Composed.Outer
public import CompStark.Pcs.Errors

/-! Uniform budgets of the composed schedules: sequential reductions add their budgets, the initial
list scales the outer budget once, and WHIR spends its level-local errors. -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

@[expose] public section

namespace CompStark.Tables.Composed

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System
open CompStark.Compose
open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.Security OracleComp

noncomputable section

/-- Increasing a budget preserves it. -/
theorem budget_mono {tree : Oracle.TypeTree} (roles : tree.RoleDecoration)
    (schedule : RoundExtractor.ChallengeSchedule tree roles) {small large : ENNReal}
    (budget : Retained.Budget roles schedule small) (bound : small ≤ large) :
    Retained.Budget roles schedule large := by
  induction tree generalizing small large with
  | done => trivial
  | «public» M next ih =>
      rcases roles with ⟨role, roles⟩
      cases role with
      | sender => exact fun move => ih move (roles move) (schedule.2 move) (budget move) bound
      | receiver =>
          obtain ⟨rest, total, children⟩ := budget
          exact ⟨rest, total.trans bound, children⟩
  | «oracle» M next ih => exact fun message => ih (roles.2 PUnit.unit) (schedule message) (budget message) bound

/-- Appended protocols spend the first budget and then the continuation's. -/
theorem budget_append {tree : Oracle.TypeTree} (roles : tree.RoleDecoration)
    (suffix : tree.BranchPath → Oracle.TypeTree)
    (suffixRoles : (path : tree.BranchPath) → (suffix path).RoleDecoration)
    (schedule : RoundExtractor.ChallengeSchedule tree roles)
    (next : (path : tree.ExecutionPath) →
      RoundExtractor.ChallengeSchedule (suffix path.toBranchPath) (suffixRoles path.toBranchPath))
    (first second : ENNReal) (budget : Retained.Budget roles schedule first)
    (children : ∀ path, Retained.Budget (suffixRoles path.toBranchPath) (next path) second) :
    Retained.Budget (PFunctor.FreeM.Displayed.Decoration.append roles suffixRoles)
      (RoundExtractor.appendSchedule suffix roles suffixRoles schedule next) (first + second) := by
  induction tree generalizing first with
  | done => exact budget_mono _ _ (children PUnit.unit) (le_add_self)
  | «public» M rest ih =>
      rcases roles with ⟨role, roles⟩
      cases role with
      | sender =>
          intro move
          exact ih move (roles move) _ _ (schedule.2 move) _ first (budget move)
            (fun path => children ⟨move, path⟩)
      | receiver =>
          obtain ⟨remaining, total, continuations⟩ := budget
          refine ⟨remaining + second, ?_, fun move =>
            ih move (roles move) _ _ (schedule.2 move) _ remaining (continuations move)
              (fun path => children ⟨move, path⟩)⟩
          change schedule.1.2 + (remaining + second) ≤ first + second
          simpa only [add_assoc] using add_le_add total (le_refl second)
  | «oracle» M rest ih =>
      intro message
      exact ih (roles.2 PUnit.unit) _ _ (schedule message) _ first (budget message)
        (fun path => children ⟨message, path⟩)

/-- Sequential reductions add their budgets. -/
theorem reduction_then_budget {P Q : Protocol} {W A B : Type} (first : Reduction P W A)
    (second : A → Reduction Q W B)
    (seam : ∀ claim witness, (second claim).input witness ↔ first.relation claim witness)
    (a b : ENNReal) (left : Retained.Budget P.roles first.challenges a)
    (right : ∀ claim, Retained.Budget Q.roles (second claim).challenges b) :
    Retained.Budget (appendProtocol P Q).roles (first.then second seam).challenges (a + b) := by
  exact budget_append P.roles (fun _ => Q.tree) (fun _ => Q.roles)
    first.challenges (fun path => (second (first.output path)).challenges)
    a b left (fun path => right (first.output path))

/-- The initial list scales every budget once. -/
theorem budget_scale {tree : Oracle.TypeTree} (roles : tree.RoleDecoration)
    (schedule : RoundExtractor.ChallengeSchedule tree roles) (list : ℝ) (error : ENNReal)
    (budget : Retained.Budget roles schedule error) :
    Retained.Budget roles (ListLift.scale roles list schedule) (ENNReal.ofReal list * error) := by
  induction tree generalizing error with
  | done => trivial
  | «public» M next ih =>
      rcases roles with ⟨role, roles⟩
      cases role with
      | sender => exact fun move => ih move (roles move) (schedule.2 move) error (budget move)
      | receiver =>
          obtain ⟨remaining, total, children⟩ := budget
          refine ⟨ENNReal.ofReal list * remaining, ?_, fun move =>
            ih move (roles move) (schedule.2 move) remaining (children move)⟩
          change ENNReal.ofReal list * schedule.1.2 + ENNReal.ofReal list * remaining ≤ _
          simpa only [mul_add] using mul_le_mul (le_refl (ENNReal.ofReal list)) total zero_le zero_le
  | «oracle» M next ih => exact fun message => ih (roles.2 PUnit.unit) (schedule message) error (budget message)

set_option smartUnfolding true in
/-- A block of scalar rounds adds one local error per round. -/
theorem scalar_budget (error : ENNReal) {rest : Protocol}
    (suffix : RoundExtractor.ChallengeSchedule rest.tree rest.roles) (remaining : ENNReal)
    (budget : Retained.Budget rest.roles suffix remaining) (count : ℕ) :
    Retained.Budget (Whir.scalarRounds E count rest).roles
      (Whir.scalarChallenges error suffix count) ((count : ENNReal) * error + remaining) := by
  induction count with
  | zero => simpa only [Whir.scalarRounds, Whir.scalarChallenges, Nat.cast_zero, zero_mul, zero_add] using budget
  | succ count ih =>
      intro polynomial
      refine ⟨(count : ENNReal) * error + remaining, le_of_eq ?_, fun _ => ih⟩
      change error + ((count : ENNReal) * error + remaining) = _
      simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      ac_rfl

/-- WHIR's cumulative budget, each encoded level with its own list bound. -/
def whirBudget : {vars : ℕ} → (schedule : Whir.Schedule K vars) →
    Whir.SecurityParameters schedule → ℕ → ENNReal
  | _, .last lanes tail encoding queries, security, claims =>
      Whir.batchError (E := E) encoding security claims +
        ((lanes : ENNReal) * Whir.foldError (E := E) encoding security +
          (Whir.queryError encoding security queries +
            (overE queries + (tail : ENNReal) * overE 2)))
  | _, .more lanes encoding queries rest, security, claims =>
      Whir.batchError (E := E) encoding security.1 claims +
        ((lanes : ENNReal) * Whir.foldError (E := E) encoding security.1 +
          (Whir.enteringOodError (E := E) rest security.2 +
            (Whir.queryError encoding security.1 queries + whirBudget rest security.2 (queries + 2))))

set_option smartUnfolding true in
/-- WHIR's schedule meets its cumulative budget. -/
theorem whir_budget {vars : ℕ} (schedule : Whir.Schedule K vars)
    (security : Whir.SecurityParameters schedule) (claims : ℕ) :
    Retained.Budget (Whir.opening E schedule).roles (Whir.challenges schedule security claims)
      (whirBudget schedule security claims) := by
  induction schedule generalizing claims with
  | last lanes tail encoding queries =>
      refine ⟨_, le_rfl, fun _ => ?_⟩
      apply scalar_budget
      intro plaintext
      refine ⟨_, le_rfl, fun _ => ⟨_, le_rfl, fun _ => ?_⟩⟩
      simpa only [add_zero, overE, Nat.cast_ofNat] using
        scalar_budget (overE 2) (rest := .done) PUnit.unit 0 trivial tail
  | more lanes encoding queries rest ih =>
      refine ⟨_, le_rfl, fun _ => ?_⟩
      apply scalar_budget
      intro word
      refine ⟨_, le_rfl, fun _ => ?_⟩
      intro opening
      exact ⟨_, le_rfl, fun _ => ih security.2 (queries + 2)⟩

/-- The initial batching error grows with the number of claims. -/
theorem batchError_mono {vars : ℕ} (encoding : Whir.Encoding K vars)
    (security : Whir.LevelSecurity) {small large : ℕ} (bound : small ≤ large) :
    Whir.batchError (E := E) encoding security small ≤ Whir.batchError (E := E) encoding security large := by
  simp only [Whir.batchError, ENNReal.ofReal_div_of_pos
    (show (0 : ℝ) < Fintype.card E by exact_mod_cast Fintype.card_pos),
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  apply ENNReal.div_le_div_right _ _
  apply mul_le_mul _ le_rfl zero_le zero_le
  exact_mod_cast Nat.sub_le_sub_right bound 1

/-- Only WHIR's head batching term depends on the number of claims. -/
theorem whirBudget_mono {vars : ℕ} (schedule : Whir.Schedule K vars)
    (security : Whir.SecurityParameters schedule) {small large : ℕ} (bound : small ≤ large) :
    whirBudget schedule security small ≤ whirBudget schedule security large := by
  cases schedule with
  | last lanes tail encoding queries => exact add_le_add (batchError_mono encoding security bound) le_rfl
  | more lanes encoding queries rest => exact add_le_add (batchError_mono encoding security.1 bound) le_rfl

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ} (setup : Setup S L k M)

/-- The rejected table rounds meet the table rounds' budget. -/
theorem rejectedTable_budget (n : ℕ) :
    Retained.Budget (TableSumcheck.roundsProtocol S L n).roles (rejectedTableRounds n)
      (overE ((TableSumcheck.degree S L + 1) * n)) := by
  induction n with
  | zero => intro values; trivial
  | succ n ih =>
      intro message
      refine ⟨overE ((TableSumcheck.degree S L + 1) * n), le_of_eq ?_, ?_⟩
      · change overE (TableSumcheck.degree S L + 1) + overE ((TableSumcheck.degree S L + 1) * n) = _
        rw [Nat.mul_succ, overE_add ((TableSumcheck.degree S L + 1) * n), add_comm]
      · intro choice
        cases choice with
        | none => trivial
        | some _ => exact ih

/-- Both bus branches meet the table sumcheck's error. -/
theorem table_budget (bus : Option (Bus.Output S L k)) :
    Retained.Budget (TableSumcheck.protocol S L).roles (tableReduction setup bus).challenges
      (TableSumcheck.error S L) := by
  cases bus with
  | none =>
      refine ⟨overE ((TableSumcheck.degree S L + 1) * TableSumcheck.maxHeight S L), le_of_eq ?_,
        fun _ => rejectedTable_budget _⟩
      change overE (TableSumcheck.constraintCount S + 2) +
        overE ((TableSumcheck.degree S L + 1) * TableSumcheck.maxHeight S L) = TableSumcheck.error S L
      simp only [TableSumcheck.error, overE_add]
  | some bus => exact TableSumcheck.challenges_budget S L k bus

/-- The external phase meets the argument's error on both table branches. -/
theorem external_budget (table : Option (TableSumcheck.Output S L k)) :
    Retained.Budget setup.external.protocol.roles (externalReduction setup table).challenges
      setup.external.error := by
  cases table with
  | none => exact setup.external.budget _
  | some o => exact setup.external.budget o

/-- The outer error: the bus, the table sumcheck and the external argument. -/
def outerError : ENNReal := Bus.error S L k + TableSumcheck.error S L + setup.external.error

/-- The outer reductions meet the outer error. -/
theorem outer_budget :
    Retained.Budget (outerProtocol setup).roles (outerReduction setup).challenges (outerError setup) := by
  unfold outerReduction outerError
  apply reduction_then_budget
  · apply reduction_then_budget
    · exact Bus.challenges_budget S L k
    · intro bus
      exact table_budget setup bus
  · intro claim
    exact external_budget setup claim.2

end

end CompStark.Tables.Composed
