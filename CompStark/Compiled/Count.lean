/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compiled.Transcript

/-! The typed presentation has exactly one challenge rank for each authored error row. -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Compiled

open CompStark.BinaryFields CompStark.Multilinear CompStark.Keccak
open Interaction Interaction.Oracle Interaction.Oracle.Security
open StateRestoration CorrelationIntractable

noncomputable section

/-- The number of challenge moves is fixed along all normalized public branches. -/
def Presentation.Counted : {original : Protocol} → Presentation original → ℕ → Prop
  | _, .refine wire _, count => wire.Counted count
  | _, .done, count => count = 0
  | _, @Presentation.sender _ _ _ _ next, count => ∀ move, (next move).Counted count
  | _, @Presentation.reveal _ _ _ _ _ next, count => next.Counted count
  | _, @Presentation.merkle _ _ _ _ _ next, count => next.Counted count
  | _, @Presentation.announce _ _ _ _ _ next, count => ∀ move, (next move).Counted count
  | _, .grind _ next, count => next.Counted count
  | _, @Presentation.challenge _ _ _ _ _ _ _ _ next, count =>
      ∃ rest, count = rest + 1 ∧ next.Counted rest

/-- Counts add under sequential presentation composition. -/
theorem Presentation.Counted.append {first second : Protocol} (presentation : Presentation first)
    (suffix : Presentation second) {before after : ℕ} (head : presentation.Counted before)
    (tail : suffix.Counted after) : (presentation.append suffix).Counted (before + after) := by
  induction presentation generalizing before with
  | refine wire projection ih => exact ih head
  | done =>
      subst before
      change suffix.Counted (0 + after)
      rw [Nat.zero_add]
      exact tail
  | sender encode next ih => exact fun move => ih move (head move)
  | reveal encode next ih => exact ih head
  | merkle layout next ih => exact ih head
  | announce encode valid next ih => exact fun move => ih move (head move)
  | grind bits next ih => exact ih head
  | challenge move shape draw next ih =>
      obtain ⟨rest, rfl, counted⟩ := head
      exact ⟨rest + after, by omega, ih counted⟩

/-- The compiled challenge-key list realizes the structural presentation count. -/
theorem Presentation.Counted.keys {original : Protocol} (presentation : Presentation original)
    {count : ℕ} (counted : presentation.Counted count)
    (path : (StandardBcs.compile Commit.Digest presentation.coin).tree.ExecutionPath) :
    (prefixKeys (StandardBcs.compiledCoin Commit.Digest presentation.coin)
      (erasePath (StandardBcs.compiledCoin Commit.Digest presentation.coin) path)).length = count := by
  induction presentation generalizing count with
  | refine wire projection ih => exact ih counted path
  | done => exact counted.symm
  | sender encode next ih =>
      change (List.map _ (prefixKeys _ (erasePath _ path.2))).length = _
      rw [List.length_map]
      exact ih path.1 (counted path.1) path.2
  | reveal encode next ih =>
      change (List.map _ (prefixKeys _ (erasePath _ path.2))).length = _
      rw [List.length_map]
      exact ih counted path.2
  | merkle layout next ih =>
      change (List.map _ (prefixKeys _ (erasePath _ path.2))).length = _
      rw [List.length_map]
      exact ih counted path.2
  | announce encode valid next ih =>
      change (List.map _ (prefixKeys _ (erasePath _ path.2))).length = _
      rw [List.length_map]
      exact ih path.1 (counted path.1) path.2
  | grind bits next ih =>
      change (List.map _ (prefixKeys _ (erasePath _ path.2))).length = _
      rw [List.length_map]
      exact ih counted path.2
  | challenge move shape draw next ih =>
      obtain ⟨rest, rfl, counted⟩ := counted
      change (_ :: List.map _ (prefixKeys _ (erasePath _ path.2))).length = _
      rw [List.length_cons, List.length_map]
      exact congrArg (· + 1) (ih counted path.2)

/-- Every scalar-round block adds one rank per coordinate. -/
theorem grandRounds_counted {tail : Protocol} (suffix : Presentation tail) {count : ℕ}
    (counted : suffix.Counted count) (degree rounds : ℕ) :
    (grandRounds degree suffix rounds).Counted (count + rounds) := by
  induction rounds with
  | zero => exact counted
  | succ rounds ih => exact ⟨_, rfl, ih⟩

/-- Every interpolation coordinate contributes one rank. -/
theorem interpolation_counted {tail : Protocol} (suffix : Presentation tail) {count : ℕ}
    (counted : suffix.Counted count) (rounds : ℕ) :
    (interpolation suffix rounds).Counted (count + rounds) := by
  induction rounds with
  | zero => exact counted
  | succ rounds ih => exact ⟨_, rfl, ih⟩

/-- The bus contributes one batching draw plus its sumcheck and interpolation coordinates per layer. -/
def busRankCount : List ℕ → ℕ → ℕ
  | [], _ => 0
  | lanes :: rest, used => 1 + used + lanes + busRankCount rest (used + lanes)

/-- Each WHIR level contributes batching, folding, query and boundary draws before its suffix. -/
def whirRankCount : {n : ℕ} → Whir.Schedule K n → ℕ
  | _, .last lanes tail _ _ => 1 + lanes + 2 + tail
  | _, .more lanes _ _ rest => 1 + lanes + 2 + whirRankCount rest
termination_by structural _ schedule => schedule

set_option smartUnfolding true in
/-- A product descent has one rank per batching draw and per sumcheck and interpolation coordinate. -/
theorem grandProduct_counted {tail : Protocol} (suffix : Presentation tail) {count : ℕ}
    (counted : suffix.Counted count) (layers : List ℕ) (used : ℕ) :
    (grandProduct suffix layers used).Counted (count + busRankCount layers used) := by
  induction layers generalizing used with
  | nil => exact counted
  | cons lanes rest ih =>
      have suffixCount := interpolation_counted _ (ih (used + lanes)) lanes
      refine ⟨count + busRankCount rest (used + lanes) + lanes + used, ?_, ?_⟩
      · simp only [busRankCount]
        omega
      · apply grandRounds_counted
        exact fun _ => suffixCount

/-- WHIR scalar rounds have one rank per scalar coordinate. -/
theorem whirRounds_counted {tail : Protocol} (suffix : Presentation tail) {count : ℕ}
    (counted : suffix.Counted count) (rounds : ℕ) :
    (whirRounds suffix rounds).Counted (count + rounds) := by
  induction rounds with
  | zero => exact counted
  | succ rounds ih => exact fun _ => ⟨_, rfl, ih⟩

set_option smartUnfolding true in
/-- WHIR has one rank per draw of its schedule. -/
theorem whirPresentation_counted {n : ℕ} (schedule : Whir.Schedule K n) :
    (whirPresentation schedule).Counted (whirRankCount schedule) := by
  change (whirWirePresentation schedule).Counted _
  induction schedule with
  | last lanes tail encoding queries =>
      have close : (whirRounds .done tail).Counted tail := by
        simpa only [Nat.zero_add] using whirRounds_counted .done rfl tail
      refine ⟨tail + 2 + lanes, ?_, ?_⟩
      · simp only [whirRankCount]
        omega
      · apply whirRounds_counted
        exact fun _ _ => ⟨tail + 1, rfl, ⟨tail, rfl, close⟩⟩
  | more lanes encoding queries rest ih =>
      refine ⟨whirRankCount rest + 2 + lanes, ?_, ?_⟩
      · simp only [whirRankCount]
        omega
      · apply whirRounds_counted
        exact fun _ => ⟨_, rfl, fun _ _ => ⟨_, rfl, ih⟩⟩

/-- The ring-switching draws have one rank each. -/
theorem ringPresentation_counted (count : ℕ) : (ringPresentation count).Counted count := by
  induction count with
  | zero => rfl
  | succ count ih => exact ⟨_, rfl, ih⟩

end

end CompStark.Compiled
