/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compiled.Transcript

/-! Executable checks of a compiled path in one duplex traversal: every challenge equals the
duplex's draw at its prefix (`WireObserver.check_iff`: the path is consistent with the replayed
challenge table), and every grinding nonce passes its test (`Presentation.grindingCheck_iff`). -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

@[expose] public section

namespace CompStark.Compiled

open CompStark.BinaryFields CompStark.Keccak
open Interaction Interaction.Oracle Interaction.Oracle.Security
open StateRestoration

/-- Check every challenge of a path against the duplex's draw at its prefix, threading the duplex
state. -/
def WireObserver.check : {protocol : Protocol} → (coin : PublicCoin protocol) →
    WireObserver coin → Transcript.State → protocol.tree.ExecutionPath → Bool
  | _, .done, _, _, _ => true
  | _, @PublicCoin.sender _ _ _ next, observer, state, path =>
      check (next path.1) (observer.2 path.1) (Transcript.replay state (observer.1 path.1)) path.2
  | _, @PublicCoin.oracle _ _ _ _ next, observer, state, path =>
      check next observer.2 (Transcript.replay state (observer.1 path.1)) path.2
  | _, @PublicCoin.challenge _ _ _ next, observer, state, path =>
      let result := observer.1.run state
      @decide (path.1 = result.1) (observer.1.equal _ _) && check next observer.2 result.2 path.2

/-- The one-traversal check decides consistency with the challenge table replayed from its
state. -/
theorem WireObserver.check_iff : {protocol : Protocol} → (coin : PublicCoin protocol) →
    (observer : WireObserver coin) → (state : Transcript.State) →
    (path : protocol.tree.ExecutionPath) →
    (check coin observer state path = true ↔ CorrelationIntractable.Consistent coin
      (fun pre => decode coin observer pre (Transcript.replay state (encodeFrom coin observer pre))) path)
  | _, .done, _, _, _ => iff_of_true rfl trivial
  | _, @PublicCoin.sender _ _ _ next, observer, state, path => by
      refine (check_iff (next path.1) (observer.2 path.1) (Transcript.replay state (observer.1 path.1))
        path.2).trans ?_
      simp only [CorrelationIntractable.Consistent, decode, encodeFrom, Transcript.replay_append]
  | _, @PublicCoin.oracle _ _ _ _ next, observer, state, path => by
      refine (check_iff next observer.2 (Transcript.replay state (observer.1 path.1)) path.2).trans ?_
      simp only [CorrelationIntractable.Consistent, decode, encodeFrom, Transcript.replay_append]
  | _, @PublicCoin.challenge _ _ _ next, observer, state, path => by
      change (@decide (path.1 = (observer.1.run state).1) (observer.1.equal _ _) &&
        check next observer.2 (observer.1.run state).2 path.2) = true ↔
        path.1 = (observer.1.run state).1 ∧ CorrelationIntractable.Consistent next
          (fun pre => decode next observer.2 pre (Transcript.replay state
            (List.replicate observer.1.width .squeeze ++ encodeFrom next observer.2 pre))) path.2
      rw [Bool.and_eq_true, @decide_eq_true_iff _ (observer.1.equal _ _),
        check_iff next observer.2 (observer.1.run state).2 path.2]
      simp only [Transcript.replay_append, ← squeezeMany_state]
      rfl

/-- Run every grinding test at its actual duplex state. -/
def Presentation.grindingCheck : {original : Protocol} → (presentation : Presentation original) →
    (StandardBcs.compile Commit.Digest presentation.coin).tree.ExecutionPath → Transcript.State → Bool
  | _, .refine wire _, path, state => wire.grindingCheck path state
  | _, .done, _, _ => true
  | _, @Presentation.sender _ _ _ encode next, path, state =>
      (next path.1).grindingCheck path.2 (Transcript.replay state (encode path.1))
  | _, @Presentation.reveal _ _ _ _ encode next, path, state =>
      next.grindingCheck path.2 (Transcript.replay state (encode path.1))
  | _, @Presentation.merkle _ _ _ _ _ next, path, state =>
      next.grindingCheck path.2 (Transcript.replay state (Transcript.digestEvents path.1))
  | _, @Presentation.announce _ _ _ _ _ _, _, _ => false
  | _, .grind bits next, path, state =>
      (Transcript.grindCheck state bits path.1).1 &&
        next.grindingCheck path.2 (Transcript.grindCheck state bits path.1).2
  | _, @Presentation.challenge _ _ _ _ _ _ _ draw next, path, state =>
      next.grindingCheck path.2 (draw.run state).2

/-- A presentation without setup announcements. -/
def Presentation.Unannounced : {original : Protocol} → Presentation original → Prop
  | _, .refine wire _ => wire.Unannounced
  | _, .done => True
  | _, @Presentation.sender _ _ _ _ next => ∀ move, (next move).Unannounced
  | _, @Presentation.reveal _ _ _ _ _ next => next.Unannounced
  | _, @Presentation.merkle _ _ _ _ _ next => next.Unannounced
  | _, @Presentation.announce _ _ _ _ _ _ => False
  | _, .grind _ next => next.Unannounced
  | _, @Presentation.challenge _ _ _ _ _ _ _ _ next => next.Unannounced

/-- Without announcements the grinding check decides the grinding conditions. -/
theorem Presentation.grindingCheck_iff {original : Protocol} (presentation : Presentation original)
    (unannounced : presentation.Unannounced)
    (path : (StandardBcs.compile Commit.Digest presentation.coin).tree.ExecutionPath)
    (state : Transcript.State) :
    presentation.grindingCheck path state = true ↔ presentation.grindingChecks path state := by
  induction presentation generalizing state with
  | refine wire projection ih => exact ih unannounced path state
  | done => exact iff_of_true rfl trivial
  | sender encode next ih => exact ih path.1 (unannounced path.1) path.2 _
  | reveal encode next ih => exact ih unannounced path.2 _
  | merkle layout next ih => exact ih unannounced path.2 _
  | announce encode valid next ih => exact unannounced.elim
  | grind bits next ih =>
      change ((Transcript.grindCheck state bits path.1).1 &&
        next.grindingCheck path.2 (Transcript.grindCheck state bits path.1).2) = true ↔ _ ∧ _
      rw [Bool.and_eq_true]
      exact and_congr Iff.rfl (ih unannounced path.2 _)
  | challenge move shape draw next ih => exact ih unannounced path.2 _

/-- Appending keeps a presentation unannounced. -/
theorem Presentation.Unannounced.append {first second : Protocol} (presentation : Presentation first)
    (suffix : Presentation second) (head : presentation.Unannounced) (tail : suffix.Unannounced) :
    (presentation.append suffix).Unannounced := by
  induction presentation with
  | refine wire projection ih => exact ih head
  | done => exact tail
  | sender encode next ih => exact fun move => ih move (head move)
  | reveal encode next ih => exact ih head
  | merkle layout next ih => exact ih head
  | announce encode valid next ih => exact head.elim
  | grind bits next ih => exact ih head
  | challenge move shape draw next ih => exact ih head

end CompStark.Compiled
