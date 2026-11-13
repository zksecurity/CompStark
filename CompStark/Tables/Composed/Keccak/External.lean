/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Composed.Keccak.Protocol
public import CompStark.Tables.Composed.Budget
public import CompStark.Pcs.RingSwitch

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

/-- An equality weight at word coordinates, prepared once. -/
def wordEqWeight {n : ℕ} (point : Fin n → BF64.WordExt3) : Pcs.EvaluatedWeight n :=
  let prepared := Vector.ofFn fun i => (1 : BF64.WordExt3) - point i
  { table := Whir.eqWeight fun i => (point i).toField
    wordEvaluate := fun atPoint => ∏ i, (prepared[i] + atPoint i)
    wordEvaluate_eq := fun atPoint => by
      change BF64.WordExt3.ringEquiv _ = _
      rw [map_prod]
      simp only [prepared, map_add, map_sub, map_one, Fin.getElem_fin, Vector.getElem_ofFn]
      have factors := Pcs.mle_factors (fun i => (1 - (point i).toField, (point i).toField))
        (fun i => (atPoint i).toField)
      change Whir.mle (Whir.eqWeight _) _ = _ at factors
      rw [factors]
      apply Finset.prod_congr rfl
      intro i _
      exact (Pcs.equalityFactor_eq_add _ _).symm }

/-- The Frobenius terms of word stages: `frobTerms` on the word carrier. -/
def frobTermsWord : List (ℕ × BF64.WordExt3) → List (BF64.WordExt3 × ℕ)
  | [] => [(1, 0)]
  | (s, f) :: st => (frobTermsWord st).flatMap fun t ↦
      [(t.1, t.2), (BF64.WordExt3.mul t.1 (f.frobenius t.2), s + t.2)]

/-- Word Frobenius terms are the specification's terms of the converted stages. -/
theorem frobTermsWord_toField (st : List (ℕ × BF64.WordExt3)) :
    (frobTermsWord st).map (fun t => (t.1.toField, t.2)) =
      Pcs.RingSwitch.frobTerms (st.map fun s => (s.1, s.2.toField)) := by
  induction st with
  | nil => rfl
  | cons stage st ih =>
    obtain ⟨s, f⟩ := stage
    rw [frobTermsWord, List.map_cons, Pcs.RingSwitch.frobTerms, ← ih, List.flatMap_map, List.map_flatMap]
    apply List.flatMap_congr
    intro t _
    simp only [List.map_cons, List.map_nil, BF64.WordExt3.toField_mul, BF64.WordExt3.toField_frobenius]

/-- A coordinate bit as a word. -/
def wordBit (i k : ℕ) : BF64.WordExt3 := if i.testBit k then 1 else 0

/-- A word bit is the coordinate bit. -/
theorem wordBit_toField (i k : ℕ) : (wordBit i k).toField = bit i k := by
  unfold wordBit bit
  split
  · exact map_one BF64.WordExt3.ringEquiv
  · exact map_zero BF64.WordExt3.ringEquiv

/-- The two staged Frobenius maps are one map. -/
theorem frobeniusMap_eq_frobMap (st : List (ℕ × E)) (a : E) :
    Pcs.frobeniusMap st a = Pcs.RingSwitch.frobMap st a := by
  induction st generalizing a with
  | nil => rfl
  | cons s st ih => exact ih _

/-- The ring-switching target on the word carrier. -/
def ringTargetWords {n : ℕ} (statement : Pcs.RingSwitch.Statement n) (fs : Vector E 6) : E :=
  let stages := (Pcs.RingSwitch.ringStages fs).map fun s => (s.1, BF64.WordExt3.ofField s.2)
  (((List.finRange 64).map fun i => BF64.WordExt3.ofField (ofK (g ^ i.val)) *
    Pcs.wordMap stages (BF64.WordExt3.ofField (statement.values i))).sum).toField

/-- The word target is the ring-switching target. -/
@[csimp] theorem ringTarget_code : @Pcs.RingSwitch.ringTarget = @ringTargetWords := by
  funext n statement fs
  unfold Pcs.RingSwitch.ringTarget ringTargetWords
  change _ = BF64.WordExt3.ringEquiv _
  rw [map_list_sum, Fin.sum_univ_def, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_def, map_mul]
  change _ = (BF64.WordExt3.ofField _).toField * (Pcs.wordMap _ _).toField
  rw [Pcs.wordMap_refines, BF64.WordExt3.toField_ofField, BF64.WordExt3.toField_ofField,
    frobeniusMap_eq_frobMap]
  simp only [List.map_map, Function.comp_def, BF64.WordExt3.toField_ofField, List.map_id']

/-- The ring-switched claim with a certified evaluator of its weight: the statement's point on the
word carrier, each Frobenius term's coordinates by word squarings and its coefficient by word
Frobenius products. -/
def ringEvaluated (t : Keccak.Gkr.Transcript E kt.p) (c : Vector E 6) : Pcs.EvaluatedClaim M :=
  let statement := sliceStatement t
  let words := Vector.ofFn fun i => BF64.WordExt3.ofField (statement.point i)
  let stages := (Pcs.RingSwitch.ringStages c).map fun s => (s.1, BF64.WordExt3.ofField s.2)
  ⟨.combine ((frobTermsWord stages).map fun term =>
      (term.1.toField, wordEqWeight fun j : Fin M =>
        if h : j.val < kt.p + 10 then words[j.val].frobenius term.2 else wordBit kt.base j.val)),
    Pcs.RingSwitch.ringTarget statement c⟩

/-- The word ring weight's terms are the specification's equality weights at the lifted twists. -/
theorem ringEvaluated_table (t : Keccak.Gkr.Transcript E kt.p) (c : Vector E 6) (u : Whir.Cube M) :
    (kt.ringEvaluated t c).weight.table u = Pcs.RingSwitch.ringWeight kt.ring (sliceStatement t) c u := by
  have stages : ((Pcs.RingSwitch.ringStages c).map fun s => (s.1, BF64.WordExt3.ofField s.2)).map
      (fun s => (s.1, s.2.toField)) = Pcs.RingSwitch.ringStages c := by
    simp only [List.map_map, Function.comp_def, BF64.WordExt3.toField_ofField, List.map_id']
  have terms : Pcs.RingSwitch.frobTerms (Pcs.RingSwitch.ringStages c) =
      (frobTermsWord ((Pcs.RingSwitch.ringStages c).map fun s => (s.1, BF64.WordExt3.ofField s.2))).map
        (fun t => (t.1.toField, t.2)) := by
    rw [frobTermsWord_toField, stages]
  simp only [ringEvaluated, Pcs.EvaluatedWeight.combine, Pcs.RingSwitch.ringWeight]
  rw [terms, List.map_map, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun term _ => ?_)
  refine congrArg (term.1.toField * ·) (congrFun (congrArg Whir.eqWeight (funext fun j => ?_)) u)
  simp only [ring]
  split
  · rename_i h
    simp only [Vector.getElem_ofFn, BF64.WordExt3.toField_frobenius, BF64.WordExt3.toField_ofField]
  · rename_i h
    simp only [wordBit_toField]

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
  exact ringEvaluated_table kt a.1 a.2 u

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
  accepts out a := kt.acceptsWord out a.1
  accepts_eq out a := kt.acceptsWord_eq out a.1

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
