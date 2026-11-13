/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compiled.Check
public import CompStark.Compiled.Prover

/-! A driven prover's compiled path passes the verifier's duplex checks: every challenge is the
duplex's draw at its prefix and every grinding nonce passes its test (`Presentation.run_checks`). -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

@[expose] public section

namespace CompStark.Compiled

open CompStark.BinaryFields CompStark.Keccak
open Interaction Interaction.Oracle Interaction.Oracle.Security

/-- A nonce the grinding search returns passes the grinding test. -/
theorem grindSearch_check (state : Transcript.State) (bits : ℕ) :
    (fuel : ℕ) → (nonce : E) → grindSearch state bits fuel = some nonce →
      (Transcript.grindCheck state bits nonce).1 = true
  | 0, _, h => nomatch h
  | fuel + 1, nonce, h => by
      rw [grindSearch] at h
      split at h
      · cases h
        assumption
      · exact grindSearch_check state bits fuel nonce h

/-- A driven prover's path is consistent with the duplex and passes every grinding test. -/
theorem Presentation.run_checks : {original : Protocol} → (presentation : Presentation original) →
    (prover : presentation.Prover) → (state : Transcript.State) →
    (result : (StandardBcs.compile Commit.Digest presentation.coin).tree.ExecutionPath ×
      List (ℕ → List K)) →
    presentation.run prover state = some result →
    WireObserver.check _ presentation.observer state result.1 = true ∧
      presentation.grindingCheck result.1 state = true
  | _, .refine wire _, prover, state, result, h => run_checks wire prover state result h
  | _, .done, _, _, _, _ => ⟨rfl, rfl⟩
  | _, @Presentation.sender _ _ _ encode next, prover, state, result, h => by
      obtain ⟨tail, htail, rfl⟩ := Option.map_eq_some_iff.mp h
      exact run_checks (next (prover state).1) (prover state).2 _ tail htail
  | _, @Presentation.reveal _ _ _ _ encode next, prover, state, result, h => by
      obtain ⟨tail, htail, rfl⟩ := Option.map_eq_some_iff.mp h
      exact run_checks next (prover state).2 _ tail htail
  | _, @Presentation.merkle _ _ _ _ layout next, prover, state, result, h => by
      obtain ⟨tail, htail, rfl⟩ := Option.map_eq_some_iff.mp h
      exact run_checks next (prover state).2.2 _ tail htail
  | _, @Presentation.announce _ _ _ _ _ _, prover, _, _, _ => nomatch prover
  | _, .grind bits next, prover, state, result, h => by
      obtain ⟨nonce, hnonce, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨tail, htail, rfl⟩ := Option.map_eq_some_iff.mp h
      have ih := run_checks next prover _ tail htail
      refine ⟨?_, ?_⟩
      · change WireObserver.check _ next.observer
          (Transcript.replay state (Transcript.grindEvents nonce)) tail.1 = true
        rw [← Transcript.grindCheck_state]
        exact ih.1
      · change ((Transcript.grindCheck state bits nonce).1 &&
          next.grindingCheck tail.1 (Transcript.grindCheck state bits nonce).2) = true
        rw [grindSearch_check state bits grindFuel nonce hnonce, ih.2]
        rfl
  | _, @Presentation.challenge _ _ _ _ _ _ _ draw next, prover, state, result, h => by
      obtain ⟨tail, htail, rfl⟩ := Option.map_eq_some_iff.mp h
      have ih := run_checks next (prover state (draw.run state).1) _ tail htail
      refine ⟨?_, ih.2⟩
      change (@decide ((draw.run state).1 = (draw.run state).1) (draw.equal _ _) &&
        WireObserver.check _ next.observer (draw.run state).2 tail.1) = true
      rw [@decide_eq_true _ (draw.equal _ _) rfl, ih.1]
      rfl

end CompStark.Compiled
