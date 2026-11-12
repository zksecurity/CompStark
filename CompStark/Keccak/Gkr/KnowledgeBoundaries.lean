/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.InitialSampling

/-! # Backward transport across deterministic GKR message boundaries -/

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
@[expose] public section
open Polynomial
open scoped BigOperators
namespace CompStark.Keccak.Gkr

/-- Removing the first round preserves the claim-dependent decoding of every later prefix. -/
theorem runningValue_tail {E M : Type} {n : Nat}
    (ops : Fin (n+1) → Sumcheck.MessageOps E M) (polys : Fin (n+1) → M)
    (point : Fin (n+1) → E) (value : E) (used : Nat) (bound : used ≤ n) :
    runningValue ops polys point value (used+1) =
      runningValue (fun i => ops i.succ) (fun i => polys i.succ) (fun i => point i.succ)
        ((ops 0).evaluate value (polys 0) (point 0)) used := by
  induction used with
  | zero => rfl
  | succ used ih =>
    conv_lhs => rw [runningValue, dite_eq_left (by omega)]
    conv_rhs => rw [runningValue, dite_eq_left (by omega)]
    rw [ih (by omega)]
    rfl

/-- The running target after all rounds is the sumcheck block's final target. -/
theorem runningValue_last {E M : Type} {n : Nat}
    (ops : Fin n → Sumcheck.MessageOps E M) (polys : Fin n → M)
    (point : Fin n → E) (value : E) :
    runningValue ops polys point value n = roundsEnd ops polys point value := by
  induction n generalizing value with
  | zero => rfl
  | succ n ih =>
    rw [runningValue_tail _ _ _ _ n le_rfl, roundsEnd, ih]

/-- The flattened initial point recovers the segment challenge. -/
theorem initialPoint_segment {E : Type} {p : Nat} (t : Transcript E p) :
    initialPoint t ⟨p+4, by omega⟩ = t.segment := by
  simp only [initialPoint, lt_self_iff_false, dite_false, dite_true]

/-- The flattened initial point recovers every lane challenge. -/
theorem initialPoint_lane {E : Type} {p : Nat} (t : Transcript E p) (i : Fin 5) :
    initialPoint t ⟨p+5+i.val, by omega⟩ = t.lanePoint i := by
  simp only [initialPoint, show ¬ p+5+i.val < p+4 by omega, dite_false,
    show ¬ p+5+i.val = p+4 by omega, Nat.add_sub_cancel_left, Fin.eta]

/-- Honest middle and first-layer claims imply the sampled initial identity. -/
theorem middle_message_preserving {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p) (t : Transcript E p)
    (good : cutHolds x output q t (.layer 0)) : cutHolds x output q t (.start (p+10)) := by
  intro r agrees
  have hr : r = initialPoint t := funext fun i => agrees i i.isLt
  subst r
  obtain ⟨middle, claim⟩ := good
  change MiddleHolds x q t at middle
  change ClaimHolds q 0 (firstClaim x output t) at claim
  change t.middleValue = _ at middle
  have hlo (i : Fin 4) : initialPoint t ⟨i.val, by omega⟩ = t.instancePoint ⟨i.val, by omega⟩ := by
    simp only [initialPoint, show i.val < p+4 by omega, dite_true]
  have hpack (i : Fin p) : initialPoint t ⟨i.val+4, by omega⟩ = t.instancePoint ⟨i.val+4, by omega⟩ := by
    simp only [initialPoint, show i.val+4 < p+4 by omega, dite_true]
  dsimp only [initialIdentity]
  simpa only [firstClaim, hlo, hpack, initialPoint_instances, initialPoint_segment, initialPoint_lane,
    middleWord, middle] using claim

/-- Honest shifted evaluations imply the terminal position residual checked by the verifier. -/
theorem evaluations_message_preserving {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p) (t : Transcript E p)
    (d : Fin 12) (checks : Accepts x output t)
    (good : cutHolds x output q t (.batch d)) : cutHolds x output q t (.position d 11) := by
  refine ⟨good.1, ?_⟩
  rw [runningValue_last, residualSum_last]
  have h := (checks.1 d).2.2.2
  rw [good.2 0, good.2 1, good.2 2] at h
  exact h

/-- An honest committed word and initial input residual recover the preceding word residual. -/
theorem word_value_message_preserving {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p) (t : Transcript E p)
    (checks : Accepts x output t)
    (good : cutHolds x output q t (.input 0)) : cutHolds x output q t .wordEnd := by
  constructor
  · apply (input_start_identity q t t.openings.inputPoint).mpr
    exact good.2
  · rw [runningValue_last, residualSum_last]
    have h := checks.2.2.1
    rw [good.1] at h
    exact h

/-- True terminal PCS claims imply the scalar input-opening residual checked by the verifier. -/
theorem slices_message_preserving {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p) (t : Transcript E p)
    (checks : Accepts x output t) (good : TerminalRelation x q t) :
    cutHolds x output q t .inputEnd := by
  have h := terminal_opening_identities x q t good
  refine ⟨h.1, ?_⟩
  rw [runningValue_last, residualSum_last]
  have check := checks.2.2.2.2
  simp_rw [h.2] at check
  exact check

/-- Deterministic changes of semantic claim permitted at a prover message. -/
inductive MessageBoundary (p : Nat) : Cut → Option Cut → Prop where
  /-- A sumcheck message leaves its entering residual unchanged. -/
  | same (c : Cut) : MessageBoundary p c (some c)
  /-- The product coefficients retain the entering layer claim. -/
  | product (d : Fin 12) : MessageBoundary p (.layer d) (some (.product d))
  /-- The middle value splits the sampled identity into its two claims. -/
  | middle : MessageBoundary p (.start (p+10)) (some (.layer 0))
  /-- The shifted evaluations discharge the terminal position equation. -/
  | evaluations (d : Fin 12) : MessageBoundary p (.position d 11) (some (.batch d))
  /-- The word value discharges the middle opening and starts the input opening. -/
  | word : MessageBoundary p .wordEnd (some (.input 0))
  /-- The final slice vector discharges the input opening. -/
  | slices : MessageBoundary p .inputEnd none

/-- A final cut is the PCS opening relation; every earlier cut retains its residual. -/
noncomputable def optionalCutHolds {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p) (t : Transcript E p) :
    Option Cut → Prop
  | none => TerminalRelation x q t
  | some c => cutHolds x output q t c

/-- Every deterministic message boundary transports fixed-table knowledge backwards. -/
theorem messageBoundary_preserving {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p) (t : Transcript E p)
    (checks : Accepts x output t) {before : Cut} {after : Option Cut}
    (boundary : MessageBoundary p before after) :
    optionalCutHolds x output q t after → cutHolds x output q t before := by
  cases boundary with
  | same => exact id
  | product => exact id
  | middle => exact middle_message_preserving x output q t
  | evaluations d => exact evaluations_message_preserving x output q t d checks
  | word => exact word_value_message_preserving x output q t checks
  | slices => exact slices_message_preserving x output q t checks

end CompStark.Keccak.Gkr
