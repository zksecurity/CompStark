/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.ExecutionBounds

/-! # Adaptive execution of one Keccak GKR layer -/

set_option maxHeartbeats 800000
@[expose] public section
open Polynomial OracleComp
open scoped BigOperators ENNReal
namespace CompStark.Keccak.Gkr

/-- Send the three shifted evaluations before sampling their batching challenge. -/
noncomputable def runBeta (E : Type) [Fintype E] [Nonempty E] {p : Nat}
    (prover : Prover E) (history : List (List E)) (base : LayerTranscript E p) :
    ProbComp (LayerTranscript E p) :=
  (fun beta => {base with evaluations := prover history 3, beta := beta}) <$> uniformField E

/-- Execute the position sumcheck, then send and batch the three shifted evaluations. -/
noncomputable def runPosition (E : Type) [Fintype E] [Nonempty E] {p : Nat}
    (prover : Prover E) (history : List (List E)) (base : LayerTranscript E p) :
    ProbComp (LayerTranscript E p) := do
  let trace ← runSumcheck E prover 2 11 history
  runBeta E prover (history ++ roundMessages trace.1 trace.2)
    {base with positionPolys := trace.1, positionPoint := trace.2}

/-- Execute the pack/segment sumcheck and its position and batching continuation. -/
noncomputable def runPack (E : Type) [Fintype E] [Nonempty E] {p : Nat}
    (prover : Prover E) (history : List (List E)) (base : LayerTranscript E p) :
    ProbComp (LayerTranscript E p) := do
  let trace ← runSumcheck E prover 1 (p+1) history
  runPosition E prover (history ++ roundMessages trace.1 trace.2)
    {base with packPolys := trace.1, packPoint := trace.2}

/-- Execute a layer with every message selected from its strict wire prefix. -/
noncomputable def runLayer (E : Type) [Fintype E] [Nonempty E] [Zero E] (p : Nat)
    (prover : Prover E) (history : List (List E)) : ProbComp (LayerTranscript E p) := do
  let sent := prover history 47
  let s ← uniformField E
  runPack E prover (history ++ [List.ofFn sent,[s]]) ⟨sent,s,0,0,0,0,0,0⟩

/-- All checks after a position sumcheck concern its terminal scalar and the next layer claim. -/
noncomputable def PositionPasses {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) (target : E) (t : LayerTranscript E p) : Prop :=
  target = eqEval c.point t.packPoint *
    mle (fun j : Fin 2048 => if h : j.val < 1600 then c.weights ⟨j.val,h⟩ else 0) t.positionPoint *
      ((∑ i, muAt t.point i)*t.evaluations 0 +
        ((∑ i, muAt t.point i)+t.evaluations 1)*t.evaluations 2) ∧
    ClaimHolds q d.succ (nextClaim t)

/-- False position residuals pass the adaptive batching continuation with numerator two. -/
theorem runBeta_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) (target : E)
    (prover : Prover E) (history : List (List E)) (base : LayerTranscript E p)
    (wrong : target ≠ positionSummand q d c base base.positionPoint) :
    Pr{let t ← runBeta E prover history base}[PositionPasses q d c target t] ≤
      (2 : ENNReal) / Fintype.card E := by
  let t : LayerTranscript E p := {base with evaluations := prover history 3}
  have hw : target ≠ positionSummand q d c t t.positionPoint := wrong
  by_cases check : target = eqEval c.point t.packPoint *
      mle (fun j : Fin 2048 => if h : j.val < 1600 then c.weights ⟨j.val,h⟩ else 0) t.positionPoint *
      ((∑ i, muAt t.point i)*t.evaluations 0 +
        ((∑ i, muAt t.point i)+t.evaluations 1)*t.evaluations 2)
  · dsimp only [t] at check
    simp only [runBeta, prEvent_map, PositionPasses, check, true_and]
    exact beta_phase_bound q d c t target hw check
  · dsimp only [t] at check
    simp only [runBeta, prEvent_map, PositionPasses, check, false_and, prEvent_false, zero_le]

/-- The position phase and beta batching together lose at most thirty-five roots. -/
theorem runPosition_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) (target : E)
    (prover : Prover E) (history : List (List E)) (base : LayerTranscript E p)
    (wrong : target ≠ packSummand q d c base.point base.packPoint) :
    Pr{let t ← runPosition E prover history base}[
      roundsValid (fun _ => Sumcheck.compressedOps 2) t.positionPolys t.positionPoint target ∧
        PositionPasses q d c (roundsEnd (fun _ => Sumcheck.compressedOps 2) t.positionPolys t.positionPoint target) t] ≤
      (35 : ENNReal) / Fintype.card E := by
  let event := fun trace : SumcheckTrace E 11 2 =>
    roundsValid (fun _ => Sumcheck.compressedOps 2) trace.1 trace.2 target ∧ roundsEnd (fun _ => Sumcheck.compressedOps 2) trace.1 trace.2 target = positionSummand q d c base trace.2
  have hfirst := position_phase_bound q d c base target prover history wrong
  have hb := prEvent_bind_le_prEvent_add_of_support (runSumcheck E prover 2 11 history)
    (fun trace => runBeta E prover (history ++ roundMessages trace.1 trace.2)
      {base with positionPolys := trace.1, positionPoint := trace.2}) event
    (fun t => roundsValid (fun _ => Sumcheck.compressedOps 2) t.positionPolys t.positionPoint target ∧
      PositionPasses q d c (roundsEnd (fun _ => Sumcheck.compressedOps 2) t.positionPolys t.positionPoint target) t)
    (ε := (2 : ENNReal) / Fintype.card E) (by
      intro trace _ bad
      by_cases valid : roundsValid (fun _ => Sumcheck.compressedOps 2) trace.1 trace.2 target
      · have hw : roundsEnd (fun _ => Sumcheck.compressedOps 2) trace.1 trace.2 target ≠ positionSummand q d c base trace.2 :=
          fun h => bad ⟨valid,h⟩
        have h := runBeta_bound q d c (roundsEnd (fun _ => Sumcheck.compressedOps 2) trace.1 trace.2 target) prover
          (history ++ roundMessages trace.1 trace.2)
          {base with positionPolys := trace.1, positionPoint := trace.2} hw
        simpa only [runBeta, prEvent_bind_eq_lintegral_of_discrete, prEvent_map, valid, true_and] using h
      · simp only [runBeta, prEvent_map, valid, false_and, prEvent_false, zero_le])
  change Pr{let t ← _ >>= _}[_] ≤ _
  refine (hb.trans (add_le_add hfirst le_rfl)).trans ?_
  rw [← ENNReal.add_div]
  norm_num

/-- The pack/segment continuation has cubic losses plus the position and batching losses. -/
theorem runPack_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p)
    (prover : Prover E) (history : List (List E)) (base : LayerTranscript E p)
    (wrong : polyEval base.product base.point ≠ (honestProduct q d c).eval base.point) :
    Pr{let t ← runPack E prover history base}[
      roundsValid (packOps c.point) t.packPolys t.packPoint (polyEval t.product t.point) ∧
      roundsValid (fun _ => Sumcheck.compressedOps 2) t.positionPolys t.positionPoint (roundsEnd (packOps c.point) t.packPolys t.packPoint (polyEval t.product t.point)) ∧
      PositionPasses q d c
        (roundsEnd (fun _ => Sumcheck.compressedOps 2) t.positionPolys t.positionPoint (roundsEnd (packOps c.point) t.packPolys t.packPoint (polyEval t.product t.point))) t] ≤
      (3*(p+1)+35 : ENNReal) / Fintype.card E := by
  let : MeasurableSpace (SumcheckTrace E 11 2) := ⊤
  let target := polyEval base.product base.point
  let event := fun trace : SumcheckTrace E (p+1) 1 =>
    roundsValid (packOps c.point) trace.1 trace.2 target ∧ roundsEnd (packOps c.point) trace.1 trace.2 target = packSummand q d c base.point trace.2
  have hfirst := packSegment_phase_bound q d c base.point target prover history wrong
  have hb := prEvent_bind_le_prEvent_add_of_support (runSumcheck E prover 1 (p+1) history)
    (fun trace => runPosition E prover (history ++ roundMessages trace.1 trace.2)
      {base with packPolys := trace.1, packPoint := trace.2}) event
    (fun t => roundsValid (packOps c.point) t.packPolys t.packPoint (polyEval t.product t.point) ∧
      roundsValid (fun _ => Sumcheck.compressedOps 2) t.positionPolys t.positionPoint (roundsEnd (packOps c.point) t.packPolys t.packPoint (polyEval t.product t.point)) ∧
      PositionPasses q d c
        (roundsEnd (fun _ => Sumcheck.compressedOps 2) t.positionPolys t.positionPoint (roundsEnd (packOps c.point) t.packPolys t.packPoint (polyEval t.product t.point))) t)
    (ε := (35 : ENNReal) / Fintype.card E) (by
      intro trace _ bad
      by_cases valid : roundsValid (packOps c.point) trace.1 trace.2 target
      · have hw : roundsEnd (packOps c.point) trace.1 trace.2 target ≠ packSummand q d c base.point trace.2 :=
          fun h => bad ⟨valid,h⟩
        have h := runPosition_bound q d c (roundsEnd (packOps c.point) trace.1 trace.2 target) prover
          (history ++ roundMessages trace.1 trace.2)
          {base with packPolys := trace.1, packPoint := trace.2} hw
        simpa only [runPosition, runBeta, prEvent_bind_eq_lintegral_of_discrete, prEvent_map, valid, target, true_and] using h
      · simp only [runPosition, runBeta, prEvent_bind_eq_lintegral_of_discrete, prEvent_map, valid, target, false_and,
          prEvent_false, MeasureTheory.lintegral_zero, zero_le])
  change Pr{let t ← _ >>= _}[_] ≤ _
  refine (hb.trans (add_le_add hfirst le_rfl)).trans ?_
  rw [← ENNReal.add_div]
  have h : (p+1 : ENNReal)*3+35 = 3*(p+1)+35 := by ring
  rw [h]

/-- A false entering layer claim passes one complete adaptive layer with numerator `3*p+84`. -/
theorem runLayer_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p)
    (prover : Prover E) (history : List (List E)) (wrong : ¬ ClaimHolds q d.castSucc c) :
    Pr{let t ← runLayer E p prover history}[layerValid d c t ∧ ClaimHolds q d.succ (nextClaim t)] ≤
      (3*p+84 : ENNReal) / Fintype.card E := by
  let : MeasurableSpace (SumcheckTrace E (p+1) 1) := ⊤
  let : MeasurableSpace (SumcheckTrace E 11 2) := ⊤
  let sent := prover history 47
  by_cases check : (∑ i, c.mu i * projectMessage sent i) + constantContribution d c = c.value
  · have hfirst := product_evaluation_bound q d c sent wrong check
    have hb := prEvent_bind_le_prEvent_add_of_support (uniformField E)
      (fun s => runPack E prover (history ++ [List.ofFn sent,[s]]) ⟨sent,s,0,0,0,0,0,0⟩)
      (fun s => (honestProduct q d c).eval s = polyEval sent s)
      (fun t => layerValid d c t ∧ ClaimHolds q d.succ (nextClaim t))
      (ε := (3*(p+1)+35 : ENNReal) / Fintype.card E) (by
        intro s _ bad
        have h := runPack_bound q d c prover (history ++ [List.ofFn sent,[s]])
          ⟨sent,s,0,0,0,0,0,0⟩ (Ne.symm bad)
        simpa only [runPack, runPosition, runBeta, prEvent_bind_eq_lintegral_of_discrete,
          prEvent_map, layerValid, PositionPasses, check, true_and, and_assoc] using h)
    change Pr{let t ← _ >>= _}[_] ≤ _
    refine (hb.trans (add_le_add hfirst le_rfl)).trans ?_
    rw [← ENNReal.add_div]
    have h : (46 : ENNReal)+(3*(p+1)+35) = 3*p+84 := by ring
    rw [h]
  · dsimp only [sent] at check
    unfold runLayer
    apply prEvent_bind_le_of_forall_le
    intro s
    simp only [runPack, runPosition, runBeta, prEvent_bind_eq_lintegral_of_discrete,
      prEvent_map, layerValid, check, false_and, prEvent_false, MeasureTheory.lintegral_zero, zero_le]

end CompStark.Keccak.Gkr
