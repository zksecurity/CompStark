/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.ExecutionBounds
public import CompStark.Keccak.Gkr.OpeningBoundaries

/-! # Adaptive committed-word and bit-slice openings -/

set_option maxRecDepth 8192
set_option maxHeartbeats 800000
@[expose] public section
open OracleComp
open scoped BigOperators ENNReal
namespace CompStark.Keccak.Gkr

/-- The input-opening sumcheck has numerator twenty and retains the fixed committed table. -/
theorem slice_opening_phase_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (q : Witness p) (t : Transcript E p) (prover : Prover E) (history : List (List E))
    (wrong : ¬ ClaimHolds q (Fin.last 12) (nextClaim (t.layers (Fin.last 11)))) :
    Pr{let trace ← runSumcheck E prover 1 10 history}[
      roundsValid (fun _ => Sumcheck.compressedOps 1) trace.1 trace.2 (nextClaim (t.layers (Fin.last 11))).value ∧
      roundsEnd (fun _ => Sumcheck.compressedOps 1) trace.1 trace.2 (nextClaim (t.layers (Fin.last 11))).value = inputSummand q t trace.2] ≤
      (20 : ENNReal) / Fintype.card E := by
  classical
  have he : (fun r => MvPolynomial.eval r (inputPolynomial q t)) = inputSummand q t :=
    funext (inputPolynomial_eval q t)
  have hd : CoordinateDegree (inputSummand q t) 2 := by
    simpa only [he] using coordinateDegree_eval (inputPolynomial q t) (inputPolynomial_degree q t)
  have hw : (nextClaim (t.layers (Fin.last 11))).value ≠ booleanSum (inputSummand q t) := by
    rw [booleanSum_eq_residualSum _ (fun _ => 0)]
    exact fun h => wrong ((input_start_identity q t (fun _ => 0)).mpr h)
  simpa only [Nat.cast_ofNat,show (10*2 : ENNReal)=20 by norm_num] using
    runSumcheck_soundness prover 1 10 2 history (fun _ => Sumcheck.compressedOps 1)
      (fun _ => Sumcheck.compressedModel 1) _ _ hd hw

/-- Execute the input-opening sumcheck and send the 64 bit-slice values at its strict prefix. -/
noncomputable def runInputOpening (E : Type) [Fintype E] [Nonempty E]
    (prover : Prover E) (history : List (List E)) (base : OpeningTranscript E) :
    ProbComp (OpeningTranscript E) :=
  (fun trace : SumcheckTrace E 10 1 =>
    {base with inputPolys := trace.1, inputPoint := trace.2, slices := prover (history ++ roundMessages trace.1 trace.2) 64}) <$>
    runSumcheck E prover 1 10 history

/-- Execute both openings, with the committed-word value sent between the two sumchecks. -/
noncomputable def runOpenings (E : Type) [Fintype E] [Nonempty E] [Zero E]
    (prover : Prover E) (history : List (List E)) : ProbComp (OpeningTranscript E) := do
  let trace ← runSumcheck E prover 1 6 history
  let next := history ++ roundMessages trace.1 trace.2
  let value := prover next 1 0
  runInputOpening E prover (next ++ [[value]]) ⟨trace.1,trace.2,value,0,0,0⟩

/-- A terminal PCS relation and the input verifier check imply the honest input residual. -/
theorem input_opening_end {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (q : Witness p) (t : Transcript E p)
    (checks : openingsValid (nextClaim (t.layers (Fin.last 11))) t)
    (terminal : TerminalRelation x q t) :
    roundsValid (fun _ => Sumcheck.compressedOps 1) t.openings.inputPolys t.openings.inputPoint (nextClaim (t.layers (Fin.last 11))).value ∧
      roundsEnd (fun _ => Sumcheck.compressedOps 1) t.openings.inputPolys t.openings.inputPoint (nextClaim (t.layers (Fin.last 11))).value =
        inputSummand q t t.openings.inputPoint := by
  refine ⟨checks.2.2.1,?_⟩
  rw [checks.2.2.2]
  simp_rw [(terminal_opening_identities x q t terminal).2]
  rfl

/-- A terminal PCS relation and the word verifier check imply the honest word residual. -/
theorem word_opening_end {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (q : Witness p) (t : Transcript E p)
    (checks : openingsValid (nextClaim (t.layers (Fin.last 11))) t)
    (terminal : TerminalRelation x q t) :
    roundsValid (fun _ => Sumcheck.compressedOps 1) t.openings.outputPolys t.openings.outputPoint t.middleValue ∧
      roundsEnd (fun _ => Sumcheck.compressedOps 1) t.openings.outputPolys t.openings.outputPoint t.middleValue =
        wordSummand x q t t.openings.outputPoint := by
  refine ⟨checks.1,?_⟩
  rw [checks.2.1,(terminal_opening_identities x q t terminal).1]
  rfl

/-- False final GKR claims survive the adaptive bit-slice opening with numerator twenty. -/
theorem runInputOpening_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (q : Witness p) (t : Transcript E p) (prover : Prover E) (history : List (List E))
    (base : OpeningTranscript E)
    (wrong : ¬ ClaimHolds q (Fin.last 12) (nextClaim (t.layers (Fin.last 11)))) :
    Pr{let o ← runInputOpening E prover history base}[
      openingsValid (nextClaim (t.layers (Fin.last 11))) {t with openings := o} ∧
        TerminalRelation x q {t with openings := o}] ≤ (20 : ENNReal) / Fintype.card E := by
  rw [runInputOpening,prEvent_map]
  refine (prEvent_mono _ _ _ (fun trace h => ?_)).trans
    (slice_opening_phase_bound q t prover history wrong)
  exact input_opening_end x q _ h.1 h.2

/-- The two adaptive opening phases have total numerator thirty-two. -/
theorem runOpenings_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (q : Witness p) (t : Transcript E p) (prover : Prover E) (history : List (List E))
    (wrong : ¬ (MiddleHolds x q t ∧ ClaimHolds q (Fin.last 12) (nextClaim (t.layers (Fin.last 11))))) :
    Pr{let o ← runOpenings E prover history}[
      openingsValid (nextClaim (t.layers (Fin.last 11))) {t with openings := o} ∧
        TerminalRelation x q {t with openings := o}] ≤ (32 : ENNReal) / Fintype.card E := by
  classical
  let event := fun trace : SumcheckTrace E 6 1 => ¬ MiddleHolds x q t ∧
    roundsValid (fun _ => Sumcheck.compressedOps 1) trace.1 trace.2 t.middleValue ∧ roundsEnd (fun _ => Sumcheck.compressedOps 1) trace.1 trace.2 t.middleValue = wordSummand x q t trace.2
  have hfirst : Pr{let trace ← runSumcheck E prover 1 6 history}[event trace] ≤
      (12 : ENNReal) / Fintype.card E := by
    by_cases hm : MiddleHolds x q t
    · simp only [event,hm,not_true_eq_false,false_and,prEvent_false,zero_le]
    · simpa only [event,hm,not_false_eq_true,true_and] using word_opening_phase_bound x q t prover history hm
  have hb := prEvent_bind_le_prEvent_add_of_support (runSumcheck E prover 1 6 history)
    (fun trace =>
      let next := history ++ roundMessages trace.1 trace.2
      runInputOpening E prover (next ++ [[prover next 1 0]]) ⟨trace.1,trace.2,prover next 1 0,0,0,0⟩)
    event
    (fun o => openingsValid (nextClaim (t.layers (Fin.last 11))) {t with openings := o} ∧
      TerminalRelation x q {t with openings := o}) (ε := (20 : ENNReal) / Fintype.card E) (by
      intro trace _ bad
      by_cases hc : ClaimHolds q (Fin.last 12) (nextClaim (t.layers (Fin.last 11)))
      · have hm : ¬ MiddleHolds x q t := fun good => wrong ⟨good,hc⟩
        rw [runInputOpening,prEvent_map]
        refine (prEvent_mono _ _ (fun _ => False) (fun tail h => ?_)).trans ?_
        · have he := word_opening_end x q _ h.1 h.2
          exact bad ⟨hm,he⟩
        · simp only [prEvent_false,zero_le]
      · exact runInputOpening_bound x q t prover _ _ hc)
  change Pr{let o ← _ >>= _}[_] ≤ _
  refine (hb.trans (add_le_add hfirst le_rfl)).trans ?_
  rw [← ENNReal.add_div]
  norm_num

end CompStark.Keccak.Gkr
