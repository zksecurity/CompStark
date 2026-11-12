/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.ProtocolExecution

/-! # The adaptive union bound for the complete fixed-table reduction -/

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
@[expose] public section
open OracleComp
open scoped BigOperators ENNReal
namespace CompStark.Keccak.Gkr

/-- Every layer boundary in a completed header is the corresponding sequence boundary. -/
theorem claimAt_sequence {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (base : Transcript E p)
    (ts : Fin 12 → LayerTranscript E p) (o : OpeningTranscript E) (d : Fin 13) :
    claimAt x output {base with layers := ts, openings := o} d =
      sequenceClaim (firstClaim x output base) ts d := by
  unfold claimAt sequenceClaim
  split <;> rfl

/-- The final sequence boundary is the claim obtained from the twelfth layer. -/
theorem sequenceClaim_last12 {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (c : Claim E p) (ts : Fin 12 → LayerTranscript E p) :
    sequenceClaim c ts (Fin.last 12) = nextClaim (ts (Fin.last 11)) := rfl

/-- The concrete verifier checks precisely the twelve layer blocks and the two opening blocks. -/
theorem accepts_sequence {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (base : Transcript E p)
    (ts : Fin 12 → LayerTranscript E p) (o : OpeningTranscript E) :
    Accepts x output {base with layers := ts, openings := o} ↔
      SequenceValid 0 (by omega) (firstClaim x output base) ts ∧
        openingsValid (nextClaim (ts (Fin.last 11))) {base with layers := ts, openings := o} := by
  simp only [Accepts,claimAt_sequence,sequenceClaim_last12,SequenceValid,Nat.zero_add]

/-- After the sampled header, the twelve layers and two openings lose their summed numerators. -/
theorem runAfterHeader_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p)
    (prover : Prover E) (history : List (List E)) (base : Transcript E p)
    (wrong : ¬ (MiddleHolds x q base ∧ ClaimHolds q 0 (firstClaim x output base))) :
    Pr{let t ← runAfterHeader E prover history base}[Accepts x output t ∧ TerminalRelation x q t] ≤
      (12*(3*p+84)+32 : ENNReal) / Fintype.card E := by
  classical
  let c := firstClaim x output base
  let event := fun ts : Fin 12 → LayerTranscript E p => MiddleHolds x q base ∧
    SequenceValid 0 (by omega) c ts ∧ ClaimHolds q (Fin.last 12) (nextClaim (ts (Fin.last 11)))
  have hfirst : Pr{let ts ← runLayerSequence E p prover 12 history}[event ts] ≤
      (12*(3*p+84) : ENNReal) / Fintype.card E := by
    by_cases hm : MiddleHolds x q base
    · have hw : ¬ ClaimHolds q 0 c := fun good => wrong ⟨hm,good⟩
      have ht := runLayerSequence_bound q prover 12 0 (by omega) history c hw
      simp only [sequenceClaim_last12] at ht
      simpa only [event,hm,true_and,Nat.cast_ofNat,Nat.zero_add,Fin.last] using ht
    · simp only [event,hm,false_and,prEvent_false,zero_le]
  have hb := prEvent_bind_le_prEvent_add_of_support (runLayerSequence E p prover 12 history)
    (fun ts => (fun o => {base with layers := ts, openings := o}) <$>
      runOpenings E prover (history ++ sequenceMessages ts)) event
    (fun t => Accepts x output t ∧ TerminalRelation x q t)
    (ε := (32 : ENNReal) / Fintype.card E) (by
      intro ts _ bad
      rw [prEvent_map]
      by_cases valid : SequenceValid 0 (by omega) c ts
      · have hw : ¬ (MiddleHolds x q {base with layers := ts} ∧
            ClaimHolds q (Fin.last 12) (nextClaim (ts (Fin.last 11)))) :=
          fun good => bad ⟨good.1,valid,good.2⟩
        have ht := runOpenings_bound x q {base with layers := ts} prover
          (history ++ sequenceMessages ts) hw
        simpa only [accepts_sequence,valid,true_and,c] using ht
      · refine (prEvent_mono _ _ (fun _ => False) (fun o h => ?_)).trans ?_
        · exact valid ((accepts_sequence x output base ts o).mp h.1).1
        · simp only [prEvent_false,zero_le])
  have hrun : runAfterHeader E prover history base =
      (runLayerSequence E p prover 12 history >>= fun ts =>
        (fun o => {base with layers := ts, openings := o}) <$>
          runOpenings E prover (history ++ sequenceMessages ts)) := by
    simp only [runAfterHeader,map_eq_bind_pure_comp,Function.comp_def]
  rw [hrun]
  refine (hb.trans (add_le_add hfirst le_rfl)).trans ?_
  rw [← ENNReal.add_div]

/-- Full typed execution has the unconditional annex C fixed-table soundness bound. -/
theorem runProtocol_soundness {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (hx : IndependentLanePowers x) (output : Fin (2^(p+4)) → Fin 25 → E)
    (q : Witness p) (prover : Prover E) (wrong : ¬ InputRelation x output q) :
    Pr{let t ← runProtocol E p prover}[Accepts x output t ∧ TerminalRelation x q t] ≤
      (37*(p+4)+902 : ENNReal) / Fintype.card E := by
  have hfirst := initial_sampling_bound x hx output q wrong
  have hb := prEvent_bind_le_prEvent_add_of_support (runCoordinates E (p+10))
    (fun r =>
      let middle := prover (coordinateMessages r) 1 0
      runAfterHeader E prover (coordinateMessages r ++ [[middle]]) (header r middle))
    (fun r => mle (initialTable x output q) r = 0)
    (fun t => Accepts x output t ∧ TerminalRelation x q t)
    (ε := (12*(3*p+84)+32 : ENNReal) / Fintype.card E) (by
      intro r _ bad
      apply runAfterHeader_bound
      intro good
      have h := initial_claim_zero x output q (header r (prover (coordinateMessages r) 1 0)) good.1 good.2
      rw [initialPoint_header] at h
      exact bad h)
  change Pr{let t ← _ >>= _}[_] ≤ _
  refine (hb.trans (add_le_add hfirst le_rfl)).trans ?_
  rw [← ENNReal.add_div]
  have he : (p+10 : ENNReal)+(12*(3*p+84)+32) = 37*(p+4)+902 := by ring
  rw [he]

end CompStark.Keccak.Gkr
