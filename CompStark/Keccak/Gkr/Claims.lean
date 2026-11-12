/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.Protocol

/-! # Fixed-table semantic claims at Keccak GKR prefixes -/

@[expose] public section
open Polynomial
open scoped BigOperators
namespace CompStark.Keccak.Gkr

/-- A sumcheck residual fixes the sampled coordinates and sums the remaining Boolean cube. -/
def residualSum {E : Type*} [CommRing E] {n : Nat}
    (summand : (Fin n → E) → E) (point : Fin n → E) (used : Nat) : E :=
  ∑ b : Fin (2^(n-used)), summand fun i =>
    if i.val < used then point i else if b.val.testBit (i.val-used) then 1 else 0

/-- The running target decodes each authored message against its preceding target. -/
def runningValue {E M : Type} {n : Nat} (ops : Fin n → Sumcheck.MessageOps E M)
    (polys : Fin n → M) (point : Fin n → E) (value : E) : Nat → E
  | 0 => value
  | used+1 => if h : used < n then
      (ops ⟨used,h⟩).evaluate (runningValue ops polys point value used) (polys ⟨used,h⟩) (point ⟨used,h⟩)
    else runningValue ops polys point value used

/-- The pack-and-segment multilinear extension of one packed linear-layer position. -/
noncomputable def linearAtPack {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (s : E) (r : Fin (p+1) → E) (j : Fin 1600) : E :=
  ∑ m : Fin 2, ∑ b : Fin (2^p), eqWeight r (b.val+2^p*m.val) *
    (packedLinear q d m b j).eval s

/-- The cubic pack-and-segment summand after evaluating the product polynomial. -/
noncomputable def packSummand {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) (s : E) (r : Fin (p+1) → E) : E :=
  let one := ∑ i, muAt s i
  let a := linearAtPack q d s r
  eqEval c.point r * ∑ j, c.weights j * (one*a j + (one+a (along j 1))*a (along j 2))

/-- One of the three shifted, zero-padded position evaluations. -/
noncomputable def shiftedEvaluation {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (s : E) (r : Fin (p+1) → E)
    (z : Fin 11 → E) (shift : Nat) : E :=
  mle (fun j : Fin 2048 => if h : j.val < 1600 then
    linearAtPack q d s r (along ⟨j.val,h⟩ shift) else 0) z

/-- The cubic position summand, with the pack-and-segment coordinates fixed. -/
noncomputable def positionSummand {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) (t : LayerTranscript E p)
    (z : Fin 11 → E) : E :=
  let one := ∑ i, muAt t.point i
  let a := shiftedEvaluation q d t.point t.packPoint z
  eqEval c.point t.packPoint *
    mle (fun j : Fin 2048 => if h : j.val < 1600 then c.weights ⟨j.val,h⟩ else 0) z *
      (one*a 0 + (one+a 1)*a 2)

/-- The exact middle-word table at the initial batch point. -/
def middleWord {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (q : Witness p) (t : Transcript E p) (slot : Fin 64) : E :=
  mle (fun b => laneValue x (q b slot)) t.instancePoint

/-- The middle claim is weighted by the segment and lane challenges before the first layer. -/
def MiddleHolds {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (q : Witness p) (t : Transcript E p) : Prop :=
  t.middleValue = (1-t.segment) *
    ∑ l : Fin 25, eqWeight t.lanePoint l.val * middleWord x q t ⟨25+l.val,by omega⟩

/-- The true quadratic summand in the six committed-middle opening rounds. -/
def wordSummand {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (q : Witness p) (t : Transcript E p) (r : Fin 6 → E) : E :=
  mle (fun slot : Fin 64 => if _h : 25 ≤ slot.val ∧ slot.val < 50 then
    (1-t.segment)*eqWeight t.lanePoint (slot.val-25) else 0) r *
      mle (middleWord x q t) r

/-- The true quadratic input-opening summand, for a fixed committed table. -/
noncomputable def inputSummand {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (t : Transcript E p) (r : Fin 10 → E) : E :=
  let c := nextClaim (t.layers (Fin.last 11))
  let low : Fin 4 → E := fun i => r ⟨i.val,by omega⟩
  let slot : Fin 6 → E := fun i => r ⟨i.val+4,by omega⟩
  let inst : Fin (p+4) → E := fun i => if h : i.val < 4 then low ⟨i.val,h⟩
    else c.point ⟨i.val-4,by omega⟩
  mle c.mu low * ∑ z : Fin 64,
    mle (fun s => inputWeight c s z) slot *
      mle (fun s => mle (fun b => ZMod.castHom (dvd_refl 2) E (q b s z)) inst) slot

/-- The scalar identity tested by the initial point, with the middle value fixed honestly. -/
noncomputable def initialIdentity {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p)
    (r : Fin (p+10) → E) : Prop :=
  let t : Transcript E p := {
    instancePoint := fun i => r ⟨i.val,by omega⟩
    segment := r ⟨p+4,by omega⟩
    lanePoint := fun i => r ⟨p+5+i.val,by omega⟩
    middleValue := 0
    layers := fun _ => ⟨0,0,0,0,0,0,0,0⟩
    openings := ⟨0,0,0,0,0,0⟩ }
  let middle := (1-t.segment) *
    ∑ l : Fin 25, eqWeight t.lanePoint l.val * middleWord x q t ⟨25+l.val,by omega⟩
  ClaimHolds q 0 (firstClaim x output { t with middleValue := middle })

/-- Flatten the initial instance, segment, and lane challenges in wire order. -/
def initialPoint {E : Type} {p : Nat} (t : Transcript E p) (i : Fin (p+10)) : E :=
  if h : i.val < p+4 then t.instancePoint ⟨i.val,h⟩
  else if h' : i.val = p+4 then t.segment else t.lanePoint ⟨i.val-(p+5),by omega⟩

/-- Mathematical claim at a cut in the public message schedule. -/
inductive Cut where
  | start (used : Nat)
  | layer (d : Fin 12)
  | product (d : Fin 12)
  | pack (d : Fin 12) (used : Nat)
  | position (d : Fin 12) (used : Nat)
  | batch (d : Fin 12)
  | word (used : Nat)
  | wordEnd
  | input (used : Nat)
  | inputEnd

/-- A message and its challenge have the same pre-challenge semantic sum claim. -/
def roundCuts (count : Nat) (cut : Nat → Cut) : List Cut :=
  (List.range count).flatMap fun i => [cut i, cut i]

/-- Sumcheck wire moves paired with their pre-challenge semantic cuts. -/
def roundNodes (count degree : Nat) (kind : Nat → Challenge) (cut : Nat → Cut) :
    List (WireStep × Cut) :=
  (List.range count).flatMap fun i => [(.message (degree+1), cut i), (.challenge (kind i), cut i)]

/-- A layer's wire moves paired with its semantic cuts. -/
def layerNodes (p : Nat) (d : Fin 12) : List (WireStep × Cut) :=
  [(.message 47, .layer d), (.challenge (.productPoint d.val), .product d)] ++
    roundNodes (p+1) 1 (.packSegment d.val) (.pack d) ++
    roundNodes 11 2 (.position d.val) (.position d) ++
    [(.message 3, .position d 11), (.challenge (.beta d.val), .batch d)]

/-- The concrete wire schedule annotated by its fixed-table semantic claims. -/
def scheduleNodes (p : Nat) : List (WireStep × Cut) :=
  (List.range (p+4)).map (fun i => (.challenge (.initialInstance i), .start i)) ++
  [(.challenge .segment, .start (p+4))] ++
  (List.range 5).map (fun i => (.challenge (.lane i), .start (p+5+i))) ++
  [(.message 1, .start (p+10))] ++
  (List.ofFn fun d : Fin 12 => layerNodes p d).flatten ++
  roundNodes 6 1 .outputSlot .word ++ [(.message 1, .wordEnd)] ++
  roundNodes 4 1 .inputLow .input ++ roundNodes 6 1 .inputSlot (fun i => .input (4+i)) ++
  [(.message 64, .inputEnd)]

/-- Semantic cuts in exactly the order of the wire schedule. -/
def cuts (p : Nat) : List Cut := (scheduleNodes p).map Prod.snd

/-- The honest residual claim at one cut, evaluated only on data already authored there.
Compatible accepting completions supply the deterministic verifier checks. -/
noncomputable def cutHolds {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p)
    (t : Transcript E p) : Cut → Prop
  | .start used => ∀ r : Fin (p+10) → E,
      (∀ i, i.val < used → r i = initialPoint t i) → initialIdentity x output q r
  | .layer d | .product d => MiddleHolds x q t ∧ ClaimHolds q d.castSucc (claimAt x output t d.castSucc)
  | .pack d used => MiddleHolds x q t ∧
      runningValue (packOps (claimAt x output t d.castSucc).point) (t.layers d).packPolys (t.layers d).packPoint
        (polyEval (t.layers d).product (t.layers d).point) used =
      residualSum (packSummand q d (claimAt x output t d.castSucc) (t.layers d).point)
        (t.layers d).packPoint used
  | .position d used => MiddleHolds x q t ∧
      runningValue (fun _ => Sumcheck.compressedOps 2) (t.layers d).positionPolys (t.layers d).positionPoint
        (roundsEnd (packOps (claimAt x output t d.castSucc).point) (t.layers d).packPolys (t.layers d).packPoint
          (polyEval (t.layers d).product (t.layers d).point)) used =
      residualSum (positionSummand q d (claimAt x output t d.castSucc) (t.layers d))
        (t.layers d).positionPoint used
  | .batch d => MiddleHolds x q t ∧ ∀ k : Fin 3,
      (t.layers d).evaluations k = shiftedEvaluation q d (t.layers d).point
        (t.layers d).packPoint (t.layers d).positionPoint k.val
  | .word used => ClaimHolds q (Fin.last 12) (claimAt x output t (Fin.last 12)) ∧
      runningValue (fun _ => Sumcheck.compressedOps 1) t.openings.outputPolys t.openings.outputPoint t.middleValue used =
        residualSum (wordSummand x q t) t.openings.outputPoint used
  | .wordEnd => ClaimHolds q (Fin.last 12) (claimAt x output t (Fin.last 12)) ∧
      runningValue (fun _ => Sumcheck.compressedOps 1) t.openings.outputPolys t.openings.outputPoint t.middleValue 6 =
        residualSum (wordSummand x q t) t.openings.outputPoint 6
  | .input used => t.openings.outputValue = mle (middleWord x q t) t.openings.outputPoint ∧
      runningValue (fun _ => Sumcheck.compressedOps 1) t.openings.inputPolys t.openings.inputPoint
        (claimAt x output t (Fin.last 12)).value used =
        residualSum (inputSummand q t) t.openings.inputPoint used
  | .inputEnd => t.openings.outputValue = mle (middleWord x q t) t.openings.outputPoint ∧
      runningValue (fun _ => Sumcheck.compressedOps 1) t.openings.inputPolys t.openings.inputPoint
        (claimAt x output t (Fin.last 12)).value 10 =
        residualSum (inputSummand q t) t.openings.inputPoint 10

/-- A prefix retains its fixed-table residual claim and can be completed to accepting checks. -/
noncomputable def prefixClaim {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (history : List (List E))
    (q : Witness p) : Prop :=
  ∃ cut, (cuts p)[history.length]? = some cut ∧ ∃ t : Transcript E p,
    history <+: transcriptMessages t ∧ Accepts x output t ∧ cutHolds x output q t cut

/-- The endpoint is exactly acceptance and the two opening relations for the fixed committed table. -/
noncomputable def endpointClaim {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (history : List (List E))
    (q : Witness p) : Prop :=
  ∃ t : Transcript E p, transcriptMessages t = history ∧ Accepts x output t ∧ TerminalRelation x q t

/-- The next prefix retains its honest residual claim or its final opening relation. -/
noncomputable def nextPrefixClaim {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E)
    (rest : List WireStep) (history : List (List E)) (w : Witness p) : Prop :=
  if rest.isEmpty then endpointClaim (p := p) x output history w else prefixClaim x output history w

end CompStark.Keccak.Gkr
