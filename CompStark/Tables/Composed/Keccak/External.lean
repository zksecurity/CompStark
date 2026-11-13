/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Composed.Keccak.Protocol
public import CompStark.Tables.Composed.Budget

/-! The Keccak table's argument as the composed system's external argument: the stack's witness
with its output lanes computed, the rider on the table sumcheck's draws, the GKR's start relation at
the table's point, and the GKR and ring-switching reductions with error
`(36 (p + 4) + 902) / |E| + 6 / 2 ^ 192` (`gkrError_eq`). -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

@[expose] public section

namespace CompStark.Tables.Composed

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System
open CompStark.Compose
open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.Security OracleComp

/-- A GKR step schedule spends its challenges' numerators over `|E|`. -/
theorem wire_budget (steps : List Keccak.Gkr.WireStep) :
    Retained.Budget (Keccak.Gkr.wireRoles E steps) (Keccak.Gkr.wireChallenges E steps)
      ((Keccak.Gkr.numeratorSum steps : ENNReal) / Fintype.card E) := by
  induction steps with
  | nil => trivial
  | cons step rest ih =>
    cases step with
    | message n =>
      intro _
      change Retained.Budget (Keccak.Gkr.wireRoles E rest) (Keccak.Gkr.wireChallenges E rest)
        ((Keccak.Gkr.numeratorSum (.message n :: rest) : ENNReal) / Fintype.card E)
      have same : Keccak.Gkr.numeratorSum (.message n :: rest) = Keccak.Gkr.numeratorSum rest := by
        simp only [Keccak.Gkr.numeratorSum, List.map_cons, List.sum_cons, zero_add]
      rw [same]
      exact ih
    | challenge kind =>
      refine ⟨(Keccak.Gkr.numeratorSum rest : ENNReal) / Fintype.card E, ?_, fun _ ↦ ih⟩
      change (kind.numerator : ENNReal) / Fintype.card E + _ ≤ _
      rw [← ENNReal.add_div]
      simp only [Keccak.Gkr.numeratorSum, List.map_cons, List.sum_cons, Nat.cast_add, le_refl]

/-- The GKR's steps after the instance draws have numerators `36 (p + 4) + 902`. -/
theorem gkrSteps_numerator (p : ℕ) : Keccak.Gkr.numeratorSum (gkrSteps p) = 36 * (p + 4) + 902 := by
  have split : Keccak.Gkr.steps p =
      (List.range (p + 4)).map (fun i => Keccak.Gkr.WireStep.challenge (.initialInstance i)) ++
        gkrSteps p := by
    rw [gkrSteps]
    unfold Keccak.Gkr.steps
    simp only [List.append_assoc]
    rw [List.drop_left' (by simp only [List.length_map, List.length_range])]
  have total := (Keccak.Gkr.totalNumerator_eq p).2
  change Keccak.Gkr.numeratorSum (Keccak.Gkr.steps p) = _ at total
  rw [split, Keccak.Gkr.numeratorSum_append] at total
  have prefixSum : Keccak.Gkr.numeratorSum
      ((List.range (p + 4)).map (fun i => Keccak.Gkr.WireStep.challenge (.initialInstance i))) = p + 4 := by
    simp only [Keccak.Gkr.numeratorSum, List.map_map, Function.comp_def, Keccak.Gkr.Challenge.numerator,
      List.map_const', List.length_range, List.sum_replicate, smul_eq_mul, mul_one]
  omega

/-- Six ring-switching draws spend `6 / 2 ^ 192`. -/
theorem ring_budget : (count : ℕ) →
    Retained.Budget (Pcs.RingSwitch.draws count).roles (Pcs.RingSwitch.challenges count)
      ((count : ENNReal) * (1 / 2 ^ 192))
  | 0 => trivial
  | count + 1 => ⟨(count : ENNReal) * (1 / 2 ^ 192), by
      change (1 : ENNReal) / 2 ^ 192 + _ ≤ _
      push_cast
      rw [add_mul, one_mul, add_comm], fun _ ↦ ring_budget count⟩

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ} (kt : KeccakTable S L M)

namespace KeccakTable

/-- The argument's error: the GKR's steps after the instance draws, then six ring-switching draws. -/
noncomputable def error (p : ℕ) : ENNReal :=
  (Keccak.Gkr.numeratorSum (gkrSteps p) : ENNReal) / Fintype.card E + 6 * (1 / 2 ^ 192)

/-- The argument's error in closed form. -/
theorem error_eq (p : ℕ) :
    error p = ((36 * (p + 4) + 902 : ℕ) : ENNReal) / Fintype.card E + 6 * (1 / 2 ^ 192) := by
  rw [error, gkrSteps_numerator]

/-- The ring-switched claim with a certified evaluator of its weight. -/
def ringEvaluated (t : Keccak.Gkr.Transcript E kt.p) (c : Vector E 6) : Pcs.EvaluatedClaim M :=
  let statement := sliceStatement t
  let point := Vector.ofFn statement.point
  ⟨.combine ((Pcs.RingSwitch.frobTerms (Pcs.RingSwitch.ringStages c)).map fun term =>
      (term.1, .eq (kt.ring.lift (fun i => point[i] ^ 2 ^ term.2)))),
    Pcs.RingSwitch.ringTarget statement c⟩

/-- The argument's claims with certified evaluators of their weights. -/
def evaluated (a : Keccak.Gkr.Transcript E kt.p × Vector E 6) : List (Pcs.EvaluatedClaim M) :=
  [kt.ringEvaluated a.1 a.2,
    ⟨.eq (kt.ring.lift (Keccak.Gkr.appendSlot a.1.instancePoint a.1.openings.outputPoint)),
      a.1.openings.outputValue⟩]

/-- The evaluated claims are the argument's claims. -/
theorem evaluated_claims (a : Keccak.Gkr.Transcript E kt.p × Vector E 6) :
    (kt.evaluated a).map Pcs.EvaluatedClaim.claim = kt.claims a.1 a.2 := by
  simp only [evaluated, claims, List.map_cons, List.map_nil, Pcs.EvaluatedClaim.claim, wordClaim,
    Pcs.EvaluatedWeight.eq_table, List.cons.injEq, and_true]
  refine congrArg (fun weight ↦ (⟨weight, _⟩ : Whir.Claim E M)) ?_
  funext u
  simp only [ringEvaluated, Pcs.EvaluatedWeight.combine, List.map_map, Function.comp_def,
    Pcs.EvaluatedWeight.eq_table, Pcs.RingSwitch.ringWeight, Fin.getElem_fin, Vector.getElem_ofFn]

/-- A witness read off a stack satisfies the external relation exactly when the stack's GKR
witness satisfies the Keccak-f relation with its computed outputs. -/
theorem external_interpret_iff (q : Whir.Table K M) :
    S.external (kt.interpret q) ↔ Keccak.Gkr.InputRelation (ofK g) (kt.outputs q) (kt.bits q) := by
  rw [kt.external_iff]
  unfold KeccakRelation
  rw [witnessBits_interpret]
  rfl

/-- The Keccak table's argument as the composed system's external argument. -/
def external (hM : (S.stackBlocks L).total ≤ 2 ^ M) : External S L k M where
  interpret := kt.interpret
  interpret_shaped := kt.interpret_shaped
  interpret_committed := kt.interpret_committed
  rider := kt.rider
  rider_local q draws remaining := kt.rider_local_le draws q remaining
  external_of_rider q known := (kt.external_interpret_iff q).mpr ((kt.rider_nil_iff q).mp known)
  interpret_stack w shaped holds := kt.interpret_stack hM w shaped holds
  rider_stack w draws shaped holds := by
    have relation := (kt.external_interpret_iff (S.stack L M w)).mp
      (by rw [kt.interpret_stack hM w shaped holds]; exact holds)
    simpa only [List.nil_append] using
      kt.rider_append [] draws _ ((kt.rider_nil_iff _).mpr relation)
  start := kt.start
  start_sound out q length known := kt.start_sound out q length known
  start_complete out q length rider virtual := kt.start_complete out q length rider virtual
  protocol := protocol kt.p
  Output := Keccak.Gkr.Transcript E kt.p × Vector E 6
  output := kt.parse
  stackOutput := kt.stackOutput
  claimBound := 2
  claims_le _ _ := le_rfl
  evaluated _ := kt.evaluated
  evaluated_claims _ a := kt.evaluated_claims a

/-- The Keccak table's argument's reductions. -/
noncomputable def reductions (hM : (S.stackBlocks L).total ≤ 2 ^ M) :
    (kt.external (k := k) hM).Reductions where
  reduction out frame := kt.keccakReduction out frame
  reduction_input out frame q := kt.gkrReduction_input out frame q
  reduction_output _ _ := rfl
  reduction_relation _ _ _ _ := Iff.rfl
  error := error kt.p
  budget _ _ := reduction_then_budget _ _ _ _ _
    (wire_budget (gkrSteps kt.p)) (fun _ ↦ ring_budget 6)
  challenges_frame _ _ _ := rfl

end KeccakTable

end CompStark.Tables.Composed
