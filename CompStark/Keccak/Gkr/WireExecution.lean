/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.SumcheckExecution

/-! # Typed block executions and the public wire schedule -/

@[expose] public section
open OracleComp
open scoped BigOperators ENNReal
namespace CompStark.Keccak.Gkr

/-- Concatenating schedules executes the first block before its adaptive continuation. -/
theorem runWire_append {E : Type} [Fintype E] [Nonempty E] (prover : Prover E)
    (a b : List WireStep) (history : List (List E)) :
    runWire E prover (a++b) history = (do
      let front ← runWire E prover a history
      let back ← runWire E prover b (history++front)
      pure (front++back)) := by
  induction a generalizing history with
  | nil => simp only [List.nil_append, runWire, pure_bind, List.append_nil, bind_pure]
  | cons step rest ih =>
    cases step <;> simp only [List.cons_append, runWire, ih, bind_assoc, pure_bind,
      List.append_assoc, List.nil_append]

/-- The round-step block starts with one message and its challenge. -/
theorem roundSteps_succ (n d : Nat) (kind : Nat → Challenge) :
    roundSteps (n+1) d kind = [.message (d+1),.challenge (kind 0)] ++
      roundSteps n d (fun i => kind (i+1)) := by
  simp only [roundSteps, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]

/-- Sumcheck trace encoding puts each coefficient vector before its challenge. -/
theorem roundMessages_cons {E : Type} {n d : Nat} (sent : Sumcheck.CompressedMessage E d) (r : E)
    (tail : SumcheckTrace E n d) :
    roundMessages (Fin.cons sent tail.1) (Fin.cons r tail.2) =
      [List.ofFn (messageVector sent),[r]] ++ roundMessages tail.1 tail.2 := by
  simp only [roundMessages, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
    List.flatten_cons, List.cons_append, List.nil_append]

/-- The typed sumcheck sampler is exactly the public wire executor for that block. -/
theorem runSumcheck_encoding {E : Type} [Fintype E] [Nonempty E]
    (prover : Prover E) (d n : Nat) (kind : Nat → Challenge) (history : List (List E)) :
    (fun trace : SumcheckTrace E n d => roundMessages trace.1 trace.2) <$>
      runSumcheck E prover d n history = runWire E prover (roundSteps n d kind) history := by
  induction n generalizing history kind with
  | zero => simp only [runSumcheck, roundSteps, List.range_zero, List.flatMap_nil,
      runWire, map_pure, roundMessages, List.ofFn_zero, List.flatten_nil]
  | succ n ih =>
    rw [roundSteps_succ]
    simp only [List.cons_append, List.nil_append, runWire, runSumcheck, map_eq_bind_pure_comp,
      Function.comp_def, bind_assoc, pure_bind, roundMessages_cons, messageVector_vectorMessage]
    congr 1
    funext r
    have h := ih (fun i => kind (i+1)) (history ++ [List.ofFn (prover history (d+1)),[r]])
    simp only [map_eq_bind_pure_comp, Function.comp_def] at h
    simp only [List.append_assoc, List.singleton_append] at *
    rw [← h]
    simp only [bind_assoc, pure_bind]

/-- Sample a coordinate vector in the same order as a block of public challenges. -/
noncomputable def runCoordinates (E : Type) [Fintype E] [Nonempty E] : (n : Nat) → ProbComp (Fin n → E)
  | 0 => pure Fin.elim0
  | n+1 => do
      let r ← uniformField E
      let tail ← runCoordinates E n
      pure (Fin.cons r tail)

/-- A coordinate vector is encoded as one singleton message for each fresh challenge. -/
def coordinateMessages {E : Type} {n : Nat} (r : Fin n → E) : List (List E) :=
  List.ofFn fun i => [r i]

/-- The coordinate sampler encodes exactly the challenge-only wire block. -/
theorem runCoordinates_encoding {E : Type} [Fintype E] [Nonempty E]
    (prover : Prover E) (n : Nat) (kind : Nat → Challenge) (history : List (List E)) :
    coordinateMessages <$> runCoordinates E n =
      runWire E prover ((List.range n).map fun i => .challenge (kind i)) history := by
  induction n generalizing kind history with
  | zero => simp only [runCoordinates, map_pure, coordinateMessages, List.ofFn_zero,
      List.range_zero, List.map_nil, runWire]
  | succ n ih =>
    simp only [runCoordinates, List.range_succ_eq_map, List.map_cons, List.map_map,
      Function.comp_def, runWire, map_eq_bind_pure_comp, bind_assoc, pure_bind,
      coordinateMessages, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
    congr 1
    funext r
    have h := ih (fun i => kind (i+1)) (history++[[r]])
    simp only [map_eq_bind_pure_comp, Function.comp_def, coordinateMessages] at h
    rw [← h]
    simp only [bind_assoc, pure_bind]

end CompStark.Keccak.Gkr
