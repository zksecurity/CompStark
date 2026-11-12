/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compiled.Count

/-! WHIR's extractor ends at a singleton witness carrier on every path (`level_witness`). -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

@[expose] public section

namespace CompStark.Compiled

open CompStark.BinaryFields
open Interaction Interaction.Oracle Interaction.Oracle.Security

/-- Closing WHIR sumcheck retains the singleton witness carrier. -/
theorem closing_witness (count : ℕ) (candidate : Whir.Table E count)
    (claim : Whir.Claim E count) (active : Bool)
    (path : (Whir.scalarRounds E count .done).tree.ExecutionPath) :
    ((Whir.closingExtractor count candidate claim active).terminalState path).Witness = PUnit := by
  induction count generalizing active with
  | zero => rfl
  | succ count ih => exact ih _ _ _ path.2.2

/-- Folding reaches a singleton suffix without inspecting its proximity predicate. -/
theorem fold_witness {vars : ℕ} (encoding : Whir.Encoding K vars)
    (nearby : (lanes : ℕ) → Whir.MaskedWord E lanes (2 ^ (vars + encoding.rate)) →
      Whir.Table E (lanes + vars) → Prop)
    (decoders : (lanes : ℕ) → Whir.ListDecoder (E := E) encoding lanes)
    {rest : Protocol}
    (finish : (word : Whir.MaskedWord E 0 (2 ^ (vars + encoding.rate))) →
      (claim : Whir.Claim E (0 + vars)) → (active : Bool) →
      RoundExtractor rest.tree (Whir.relationState (nearby 0) word [claim] active))
    (singleton : ∀ word claim active (path : rest.tree.ExecutionPath),
      ((finish word claim active).terminalState path).Witness = PUnit)
    (lanes : ℕ) (word : Whir.MaskedWord E lanes (2 ^ (vars + encoding.rate)))
    (claim : Whir.Claim E (lanes + vars)) (active : Bool)
    (path : (Whir.scalarRounds E lanes rest).tree.ExecutionPath) :
    ((Whir.foldExtractor encoding nearby decoders finish lanes word claim active).terminalState
      path).Witness = PUnit := by
  induction lanes generalizing active with
  | zero => exact singleton word claim active path
  | succ lanes ih => exact ih _ _ _ path.2.2

/-- Every encoded WHIR level ends in the singleton closing carrier. -/
theorem level_witness {n : ℕ} (schedule : Whir.Schedule K n)
    (nearby : Whir.ProximityFamily K E) (decoders : Whir.DecoderFamily (E := E) schedule)
    (word : Whir.oracleMessage E schedule) (claims : List (Whir.Claim E n)) (active : Bool)
    (path : (Whir.opening E schedule).tree.ExecutionPath) :
    ((Whir.levelExtractor (algebraMap K E) schedule nearby decoders word claims active).terminalState
      path).Witness = PUnit := by
  induction schedule generalizing nearby active with
  | last lanes tail encoding queries =>
      change ((Whir.foldExtractor encoding (nearby 0 encoding) decoders
        (Whir.lastExtractor lanes queries encoding (algebraMap K E) (nearby 0 encoding 0)
          (decoders 0)) lanes word (Whir.batch claims path.1) active).terminalState path.2).Witness = _
      apply fold_witness
      intro word claim active path
      exact closing_witness _ _ _ _ path.2.2.2
  | more lanes encoding queries rest ih =>
      change ((Whir.foldExtractor encoding (nearby 0 encoding) decoders.1
        (Whir.boundaryExtractor lanes queries encoding (algebraMap K E) (nearby 0 encoding 0)
          rest (fun level => nearby (level + 1)) (decoders.1 0) decoders.2
          (Whir.levelExtractor (algebraMap K E) rest (fun level => nearby (level + 1)) decoders.2))
        lanes word (Whir.batch claims path.1) active).terminalState path.2).Witness = _
      apply fold_witness
      intro word claim active path
      erw [RoundExtractor.terminalState.eq_3, RoundExtractor.terminalState.eq_2,
        RoundExtractor.terminalState.eq_2, RoundExtractor.terminalState.eq_2]
      exact ih _ _ _ _ _ path.2.2.2.2

end CompStark.Compiled
