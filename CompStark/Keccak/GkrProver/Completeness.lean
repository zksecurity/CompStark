/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.Cofactor
public import CompStark.Keccak.Gkr.InitialBoundary
public import CompStark.Keccak.Gkr.OpeningBoundaries

/-! Honest specification layers and their deterministic acceptance and claim propagation. -/

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr
open scoped BigOperators

/-- The specification layer authors every transmitted message for fixed verifier challenges. -/
noncomputable def honestLayer {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim F p) (s : F)
    (packPoint : Fin (p+1) → F) (positionPoint : Fin 11 → F) (beta : F) : LayerTranscript F p :=
  let t : LayerTranscript F p := {
    product := honestProductMessage q d c
    point := s
    packPolys := honestPackRounds q d c s packPoint
    packPoint := packPoint
    positionPolys := 0
    positionPoint := positionPoint
    evaluations := fun k => shiftedEvaluation q d s packPoint positionPoint k.val
    beta := beta }
  {t with positionPolys := honestPositionRounds q d c t}

/-- An honest layer satisfies the product, cofactor and position checks for every challenge vector. -/
theorem honestLayer_valid {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim F p) (s : F)
    (packPoint : Fin (p+1) → F) (positionPoint : Fin 11 → F) (beta : F)
    (hc : ClaimHolds q d.castSucc c) :
    layerValid d c (honestLayer q d c s packPoint positionPoint beta) := by
  refine ⟨honestProductMessage_valid q d c hc, cofactorRounds_valid _ _ _ _,
    compressedRounds_valid _ _ _, ?_⟩
  change roundsEnd (fun _ => Sumcheck.compressedOps 2)
    (honestPositionRounds q d c (honestLayer q d c s packPoint positionPoint beta)) positionPoint
    (roundsEnd (packOps c.point) (honestPackRounds q d c s packPoint) packPoint
      (polyEval (honestProductMessage q d c) s)) = _
  rw [honestPackRounds_complete]
  exact honestPositionRounds_complete q d c (honestLayer q d c s packPoint positionPoint beta)

/-- Honest shifted evaluations propagate the true weighted claim across beta batching. -/
theorem honestLayer_next {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim F p) (s : F)
    (packPoint : Fin (p+1) → F) (positionPoint : Fin 11 → F) (beta : F) :
    ClaimHolds q d.succ (nextClaim (honestLayer q d c s packPoint positionPoint beta)) := by
  apply (beta_boundary_identity q d _).mpr
  rfl

/-- The specification authors the middle claim, every layer, and both exact terminal openings. -/
structure SpecificationHonest {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (x : F) (output : Fin (2^(p+4)) → Fin 25 → F) (q : Witness p) (t : Transcript F p) : Prop where
  /-- The transmitted middle claim is the actual committed middle-state evaluation. -/
  middle : MiddleHolds x q t
  /-- Every layer follows the honest coefficient strategy at its actual entering claim. -/
  layers : ∀ d, t.layers d = honestLayer q d (claimAt x output t d.castSucc)
    (t.layers d).point (t.layers d).packPoint (t.layers d).positionPoint (t.layers d).beta
  /-- The word block transmits the honest quadratic messages. -/
  word : t.openings.outputPolys = honestWordRounds x q t
  /-- The transmitted word value is the full committed-slot interpolation. -/
  wordValue : t.openings.outputValue = mle (middleWord x q t) t.openings.outputPoint
  /-- The input block transmits the honest quadratic messages. -/
  input : t.openings.inputPolys = honestInputRounds q t
  /-- All sixty-four slices are evaluations of the supplied committed witness. -/
  slices : ∀ z, t.openings.slices z =
    mle (fun slot => mle (fun b => ZMod.castHom (dvd_refl 2) F (q b slot z))
      (inputInstancePoint (nextClaim (t.layers (Fin.last 11))) t.openings.inputPoint))
      (inputSlotPoint t.openings.inputPoint)

/-- The genuine committed middle states and output lanes give the first honest weighted claim. -/
theorem firstClaim_complete {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (x : F) (output : Fin (2^(p+4)) → Fin 25 → F) (q : Witness p) (t : Transcript F p)
    (relation : InputRelation x output q) (middle : MiddleHolds x q t) :
    ClaimHolds q 0 (firstClaim x output t) := by
  have h0 (b : Fin (2^(p+4))) (l : Fin 25) :
      segmentLane x q b 0 l = laneValue x (q b ⟨25+l.val, by omega⟩) := by
    unfold segmentLane
    apply congrArg (laneValue x)
    funext z
    rw [relation.1]
    simp only [startState, Fin.val_one, Nat.mul_one]
    have hd : (64*l.val+z.val)/64 = l.val := by omega
    have hm : (64*l.val+z.val)%64 = z.val := by omega
    simp only [hd, hm, Fin.eta]
  have h1 (b : Fin (2^(p+4))) (l : Fin 25) : segmentLane x q b 1 l = output b l := by
    rw [relation.2]
    unfold segmentLane
    apply congrArg (laneValue x)
    funext z
    apply congrArg (segmentState q b 1 12 (by omega))
    apply Fin.ext
    change 64*l.val+z.val = z.val+64*l.val
    omega
  refine (first_claim_identity x output q t).mpr ?_
  simp only [firstClaim, h0, h1, outputClaimAt]
  dsimp only [MiddleHolds, middleWord] at middle
  rw [middle]

/-- Every entering claim of a specification-honest transcript is true for the committed witness. -/
theorem SpecificationHonest.claims {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    {x : F} {output : Fin (2^(p+4)) → Fin 25 → F} {q : Witness p} {t : Transcript F p}
    (honest : SpecificationHonest x output q t) (relation : InputRelation x output q) (d : Fin 13) :
    ClaimHolds q d (claimAt x output t d) := by
  by_cases hz : d.val = 0
  · have hd : d = 0 := Fin.ext hz
    subst d
    exact firstClaim_complete x output q t relation honest.middle
  · let previous : Fin 12 := ⟨d.val-1, by omega⟩
    have hd : d = previous.succ := Fin.ext (by simp only [previous, Fin.val_succ]; omega)
    rw [claimAt, dite_eq_right hz, honest.layers previous]
    rw [hd]
    exact honestLayer_next q previous _ _ _ _ _

/-- The complete specification strategy satisfies the same acceptance and terminal PCS predicates as the verifier. -/
theorem SpecificationHonest.complete {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    {x : F} {output : Fin (2^(p+4)) → Fin 25 → F} {q : Witness p} {t : Transcript F p}
    (honest : SpecificationHonest x output q t) (relation : InputRelation x output q) :
    Accepts x output t ∧ TerminalRelation x q t := by
  constructor
  · constructor
    · intro d
      rw [honest.layers d]
      exact honestLayer_valid q d _ _ _ _ _ (honest.claims relation d.castSucc)
    · refine ⟨compressedRounds_valid _ _ _, ?_, compressedRounds_valid _ _ _, ?_⟩
      · have start : t.middleValue = residualSum (wordSummand x q t) t.openings.outputPoint 0 :=
          honest.middle.trans (word_start_identity x q t t.openings.outputPoint).symm
        rw [honest.word, start, honestWordRounds_complete, honest.wordValue]
        rfl
      · have last : claimAt x output t (Fin.last 12) = nextClaim (t.layers (Fin.last 11)) := by
          rfl
        have start := (input_start_identity q t t.openings.inputPoint).mp
          (show ClaimHolds q (Fin.last 12) (nextClaim (t.layers (Fin.last 11))) by
            rw [← last]; exact honest.claims relation _)
        rw [last, honest.input, start, honestInputRounds_complete]
        simp_rw [honest.slices]
        rfl
  · constructor
    · exact honest.wordValue.trans (mle_appendSlot
        (fun b slot => laneValue x (q b slot)) t.instancePoint t.openings.outputPoint).symm
    · intro z
      exact (honest.slices z).trans (mle_appendSlot
        (fun b slot => ZMod.castHom (dvd_refl 2) F (q b slot z))
        (inputInstancePoint (nextClaim (t.layers (Fin.last 11))) t.openings.inputPoint)
        (inputSlotPoint t.openings.inputPoint)).symm

/-- Verifier challenges in their protocol dimensions, independent of the authored messages. -/
structure Challenges (F : Type) (p : Nat) where
  /-- Externally drawn instance coordinates. -/
  instancePoint : Fin (p+4) → F
  /-- Segment batching coordinate. -/
  segment : F
  /-- Five lane coordinates. -/
  lanes : Fin 5 → F
  /-- Product evaluation challenge in each backwards layer. -/
  products : Fin 12 → F
  /-- Pack and segment coordinates in each backwards layer. -/
  packs : Fin 12 → Fin (p+1) → F
  /-- Position coordinates in each backwards layer. -/
  positions : Fin 12 → Fin 11 → F
  /-- Quadratic batching challenge in each backwards layer. -/
  betas : Fin 12 → F
  /-- Word-opening slot coordinates. -/
  word : Fin 6 → F
  /-- Input-opening low-instance and slot coordinates. -/
  input : Fin 10 → F

/-- Construct the twelve specification layers in forward transcript order. -/
noncomputable def specificationLayers {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (initial : Claim F p) (r : Challenges F p) (d : Fin 12) : LayerTranscript F p :=
  honestLayer q d
    (if h : d.val = 0 then initial else
      nextClaim (specificationLayers q initial r ⟨d.val-1, by omega⟩))
    (r.products d) (r.packs d) (r.positions d) (r.betas d)
termination_by d.val

/-- Every generated layer retains its prescribed product challenge. -/
@[simp] theorem specificationLayers_point {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (initial : Claim F p) (r : Challenges F p) (d : Fin 12) :
    (specificationLayers q initial r d).point = r.products d := by
  rw [specificationLayers]
  rfl

/-- Every generated layer retains its prescribed pack challenge vector. -/
@[simp] theorem specificationLayers_packPoint {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (initial : Claim F p) (r : Challenges F p) (d : Fin 12) :
    (specificationLayers q initial r d).packPoint = r.packs d := by
  rw [specificationLayers]
  rfl

/-- Every generated layer retains its prescribed position challenge vector. -/
@[simp] theorem specificationLayers_positionPoint {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (initial : Claim F p) (r : Challenges F p) (d : Fin 12) :
    (specificationLayers q initial r d).positionPoint = r.positions d := by
  rw [specificationLayers]
  rfl

/-- Every generated layer retains its prescribed batching challenge. -/
@[simp] theorem specificationLayers_beta {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (initial : Claim F p) (r : Challenges F p) (d : Fin 12) :
    (specificationLayers q initial r d).beta = r.betas d := by
  rw [specificationLayers]
  rfl

/-- Generated layers use exactly the predecessor claim retained by the GKR protocol. -/
theorem specificationLayers_claimAt {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (x : F) (output : Fin (2^(p+4)) → Fin 25 → F) (q : Witness p) (r : Challenges F p)
    (t : Transcript F p) (layers : t.layers = specificationLayers q (firstClaim x output t) r)
    (d : Fin 12) :
    t.layers d = honestLayer q d (claimAt x output t d.castSucc)
      (t.layers d).point (t.layers d).packPoint (t.layers d).positionPoint (t.layers d).beta := by
  rw [layers]
  simp only [specificationLayers_point, specificationLayers_packPoint,
    specificationLayers_positionPoint, specificationLayers_beta]
  conv_lhs => rw [specificationLayers]
  congr 1
  unfold claimAt
  simp only [Fin.val_castSucc]
  split
  · rfl
  · rw [layers]

/-- The honest specification transcript at any fixed sequence of verifier challenges. -/
noncomputable def specificationTranscript {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (x : F) (output : Fin (2^(p+4)) → Fin 25 → F) (q : Witness p) (r : Challenges F p) : Transcript F p :=
  let middle := (1-r.segment) * ∑ l : Fin 25,
    eqWeight r.lanes l.val * mle (fun b => laneValue x (q b ⟨25+l.val, by omega⟩)) r.instancePoint
  let initial : Claim F p := {
    value := middle+r.segment*∑ l, eqWeight r.lanes l.val * mle (fun b => output b l) r.instancePoint
    mu := fun i => eqWeight (fun b : Fin 4 => r.instancePoint ⟨b.val, by omega⟩) i.val
    point := Fin.lastCases r.segment (fun b : Fin p => r.instancePoint ⟨b.val+4, by omega⟩)
    weights := fun j => eqWeight r.lanes (j.val/64)*x^(j.val%64) }
  let t : Transcript F p := {
    instancePoint := r.instancePoint
    segment := r.segment
    lanePoint := r.lanes
    middleValue := middle
    layers := specificationLayers q initial r
    openings := ⟨0,r.word,0,0,r.input,0⟩ }
  {t with openings := {
    outputPolys := honestWordRounds x q t
    outputPoint := r.word
    outputValue := mle (middleWord x q t) r.word
    inputPolys := honestInputRounds q t
    inputPoint := r.input
    slices := fun z =>
      mle (fun slot => mle (fun b => ZMod.castHom (dvd_refl 2) F (q b slot z))
        (inputInstancePoint (nextClaim (t.layers (Fin.last 11))) r.input)) (inputSlotPoint r.input) } }

/-- The constructed specification transcript authors the honest strategy in every phase. -/
theorem specificationTranscript_honest {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (x : F) (output : Fin (2^(p+4)) → Fin 25 → F) (q : Witness p) (r : Challenges F p) :
    SpecificationHonest x output q (specificationTranscript x output q r) := by
  constructor
  · rfl
  · exact specificationLayers_claimAt x output q r _ rfl
  · rfl
  · rfl
  · rfl
  · intro z; rfl

/-- Honest specification proving is complete for every verifier challenge sequence. -/
theorem specificationTranscript_complete {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (x : F) (output : Fin (2^(p+4)) → Fin 25 → F) (q : Witness p) (r : Challenges F p)
    (relation : InputRelation x output q) :
    Accepts x output (specificationTranscript x output q r) ∧
      TerminalRelation x q (specificationTranscript x output q r) :=
  (specificationTranscript_honest x output q r).complete relation

/-- Component equality determines an opening transcript. -/
private theorem opening_ext {F : Type} {a b : OpeningTranscript F}
    (h0 : a.outputPolys=b.outputPolys) (h1 : a.outputPoint=b.outputPoint)
    (h2 : a.outputValue=b.outputValue) (h3 : a.inputPolys=b.inputPolys)
    (h4 : a.inputPoint=b.inputPoint) (h5 : a.slices=b.slices) : a=b := by
  cases a; cases b
  cases h0; cases h1; cases h2; cases h3; cases h4; cases h5
  rfl

/-- Component equality determines a complete transcript. -/
private theorem transcript_ext {F : Type} {p : Nat} {a b : Transcript F p}
    (h0 : a.instancePoint=b.instancePoint) (h1 : a.segment=b.segment)
    (h2 : a.lanePoint=b.lanePoint) (h3 : a.middleValue=b.middleValue)
    (h4 : a.layers=b.layers) (h5 : a.openings=b.openings) : a=b := by
  cases a; cases b
  cases h0; cases h1; cases h2; cases h3; cases h4; cases h5
  rfl

/-- The verifier challenges retained by a complete transcript. -/
def Challenges.ofTranscript {F : Type} {p : Nat} (t : Transcript F p) : Challenges F p := {
  instancePoint := t.instancePoint, segment := t.segment, lanes := t.lanePoint
  products := fun d => (t.layers d).point
  packs := fun d => (t.layers d).packPoint
  positions := fun d => (t.layers d).positionPoint
  betas := fun d => (t.layers d).beta
  word := t.openings.outputPoint, input := t.openings.inputPoint }

/-- Honest messages uniquely determine the complete specification transcript at its retained challenges. -/
theorem SpecificationHonest.eq_specificationTranscript {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    {x : F} {output : Fin (2^(p+4)) → Fin 25 → F} {q : Witness p} {t : Transcript F p}
    (honest : SpecificationHonest x output q t) :
    t = specificationTranscript x output q (Challenges.ofTranscript t) := by
  let spec := specificationTranscript x output q (Challenges.ofTranscript t)
  have hm : spec.middleValue = t.middleValue := honest.middle.symm
  have hf : firstClaim x output spec = firstClaim x output t := by
    unfold firstClaim
    rw [hm]
    rfl
  have hl : ∀ n (hn : n < 12), spec.layers ⟨n,hn⟩ = t.layers ⟨n,hn⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      let d : Fin 12 := ⟨n,hn⟩
      have hc : claimAt x output spec d.castSucc = claimAt x output t d.castSucc := by
        unfold claimAt
        split
        · exact hf
        · rename_i hne
          dsimp only [d,Fin.val_castSucc]
          exact congrArg nextClaim (ih (n-1) (by dsimp only [d,Fin.val_castSucc] at hne; omega) (by omega))
      calc
        spec.layers d = honestLayer q d (claimAt x output spec d.castSucc)
            (t.layers d).point (t.layers d).packPoint (t.layers d).positionPoint (t.layers d).beta :=
          by simpa only [spec,specificationTranscript,specificationLayers_point,
            specificationLayers_packPoint,specificationLayers_positionPoint,specificationLayers_beta,
            Challenges.ofTranscript] using
              specificationLayers_claimAt x output q (Challenges.ofTranscript t) spec rfl d
        _ = honestLayer q d (claimAt x output t d.castSucc)
            (t.layers d).point (t.layers d).packPoint (t.layers d).positionPoint (t.layers d).beta := by rw [hc]
        _ = t.layers d := (honest.layers d).symm
  have hL : spec.layers = t.layers := funext fun d => hl d.val d.isLt
  have hw : honestWordRounds x q spec = honestWordRounds x q t := rfl
  have hi : honestInputRounds q spec = honestInputRounds q t := by
    unfold honestInputRounds
    congr 1
    funext r
    unfold inputSummand
    rw [hL]
  have ho : spec.openings = t.openings := by
    apply opening_ext
    · exact hw.trans honest.word.symm
    · rfl
    · exact honest.wordValue.symm
    · exact hi.trans honest.input.symm
    · rfl
    · funext z
      rw [honest.slices,← hL]
      rfl
  exact (transcript_ext (a := spec) (b := t) rfl rfl rfl hm hL ho).symm

end CompStark.Keccak.GkrProver
