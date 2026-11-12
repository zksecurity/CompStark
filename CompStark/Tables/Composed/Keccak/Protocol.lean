/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Composed.Keccak.Ring
public import CompStark.Tables.Composed.Keccak.Checks
public import CompStark.Tables.Composed.Keccak.Transport
public import CompStark.Tables.Composed.Keccak.Encoding

/-! The Keccak table's argument after the table sumcheck: the Keccak-f GKR without its instance
draws, which the table sumcheck's point supplies, then six ring-switching draws. The GKR reduces
the transmitted output lanes to a word claim and 64 slice claims on the stack's slot region; ring
switching reduces the slice claims to one weighted claim. Each is a reduction on the stack, framed by
an obligation it carries through (`gkrReduction`, `ringReduction`), composed at their seam
(`keccakReduction`). -/

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

/-- The GKR's steps after its instance draws. -/
def gkrSteps (p : ℕ) : List Keccak.Gkr.WireStep :=
  (Keccak.Gkr.steps p).drop (p + 4)

/-- The GKR after its instance draws: public messages and challenges, no oracles. -/
def gkrProtocol (p : ℕ) : Protocol :=
  ⟨Keccak.Gkr.wireTree E (gkrSteps p), Keccak.Gkr.wireRoles E (gkrSteps p), noOracles (gkrSteps p)⟩
where
  /-- The GKR's moves carry no oracle interface. -/
  noOracles (steps : List Keccak.Gkr.WireStep) : (Keccak.Gkr.wireTree E steps).OracleDecoration :=
    (Keccak.Gkr.wireProtocol E steps).oracles

/-- The GKR's empty oracle decorations, move by move. -/
def gkrNoOraclesLazy : (steps : List Keccak.Gkr.WireStep) →
    (Keccak.Gkr.wireTree E steps).OracleDecoration.{0, 0}
  | [] => PUnit.unit
  | .message _ :: rest => ⟨PUnit.unit, fun _ => gkrNoOraclesLazy rest⟩
  | .challenge _ :: rest => ⟨PUnit.unit, fun _ => gkrNoOraclesLazy rest⟩
termination_by structural steps => steps

/-- The GKR's empty oracle decorations are computed move by move. -/
@[csimp] theorem gkrNoOracles_code : gkrProtocol.noOracles = gkrNoOraclesLazy := by
  funext steps
  induction steps with
  | nil => rfl
  | cons step rest ih =>
    cases step with
    | message n =>
      change (PUnit.unit, fun _ : Fin n → E => gkrProtocol.noOracles rest) =
        (PUnit.unit, fun _ : Fin n → E => gkrNoOraclesLazy rest)
      rw [ih]
    | challenge kind =>
      change (PUnit.unit, fun _ : E => gkrProtocol.noOracles rest) =
        (PUnit.unit, fun _ : E => gkrNoOraclesLazy rest)
      rw [ih]

/-- The 64 final slice values at their shared point. -/
def sliceStatement {p : ℕ} (t : Keccak.Gkr.Transcript E p) : Pcs.RingSwitch.Statement (p + 10) :=
  let last := Keccak.Gkr.nextClaim (t.layers (Fin.last 11))
  let instances : Fin (p + 4) → E := fun i =>
    if h : i.val < 4 then t.openings.inputPoint ⟨i.val, h.trans (by decide)⟩
    else last.point ⟨i.val - 4, by omega⟩
  ⟨Keccak.Gkr.appendSlot instances (fun i => t.openings.inputPoint ⟨i.val + 4, by omega⟩),
    t.openings.slices⟩

/-- The ring-switching stage predicates of a layout and statement, after `used` draws. -/
def ringCoreLabels {n M : ℕ} (layout : Pcs.RingSwitch.Layout n M) (statement : Pcs.RingSwitch.Statement n) :
    (count used : ℕ) → Vector E used → Retained.Labels (Whir.Table K M) (Pcs.RingSwitch.draws count).tree
  | 0, used, coefficients => fun q => ∀ k < 2 ^ (6 - used),
      Pcs.RingSwitch.frobPair Finset.univ (fun i : Fin 64 => ofK (g ^ i.val))
        (fun i => Pcs.RingSwitch.frobMap (Pcs.RingSwitch.ringStages coefficients)
          (Pcs.RingSwitch.sliceError layout statement q i)) k = 0
  | count + 1, used, coefficients =>
      ⟨fun q => ∀ k < 2 ^ (6 - used),
        Pcs.RingSwitch.frobPair Finset.univ (fun i : Fin 64 => ofK (g ^ i.val))
          (fun i => Pcs.RingSwitch.frobMap (Pcs.RingSwitch.ringStages coefficients)
            (Pcs.RingSwitch.sliceError layout statement q i)) k = 0,
        fun challenge => ringCoreLabels layout statement count (used + 1) (coefficients.push challenge)⟩

/-- Every ring-switching label's root is its stage's equations. -/
theorem ringCore_input {n M : ℕ} (layout : Pcs.RingSwitch.Layout n M)
    (statement : Pcs.RingSwitch.Statement n) (count used : ℕ) (coefficients : Vector E used) :
    Retained.input (ringCoreLabels layout statement count used coefficients) = fun q =>
      ∀ k < 2 ^ (6 - used), Pcs.RingSwitch.frobPair Finset.univ
        (fun i : Fin 64 => ofK (g ^ i.val))
        (fun i => Pcs.RingSwitch.frobMap (Pcs.RingSwitch.ringStages coefficients)
          (Pcs.RingSwitch.sliceError layout statement q i)) k = 0 := by
  cases count <;> rfl

/-- Ring switching has no prover moves. -/
theorem ringCore_preserving {n M : ℕ} (layout : Pcs.RingSwitch.Layout n M) (fixed : Whir.Table K M)
    (statement : Pcs.RingSwitch.Statement n) (count used : ℕ) (coefficients : Vector E used) :
    (Retained.extractor fixed (ringCoreLabels layout statement count used coefficients)).IsProverPreserving
      (Pcs.RingSwitch.draws count).roles := by
  induction count generalizing used with
  | zero => trivial
  | succ count ih =>
      exact ⟨fun _ impossible => False.elim (by cases impossible),
        fun challenge => ih (used + 1) (coefficients.push challenge)⟩

/-- The ring-switching labels inherit each stage's one-root bound. -/
theorem ringCore_bounded {n M : ℕ} (layout : Pcs.RingSwitch.Layout n M) (fixed : Whir.Table K M)
    (statement : Pcs.RingSwitch.Statement n) (count used : ℕ) (coefficients : Vector E used)
    (within : count + used ≤ 6) :
    (Retained.extractor fixed (ringCoreLabels layout statement count used coefficients)).IsLocallyBounded
      (Pcs.RingSwitch.draws count).roles (Pcs.RingSwitch.challenges count) := by
  induction count generalizing used with
  | zero => trivial
  | succ count ih =>
      refine ⟨?_, fun challenge => ih (used + 1) (coefficients.push challenge) (by omega)⟩
      rw [_root_.RoundByRound.GameFamily.isBounded_iff]
      intro round context
      have source := Pcs.RingSwitch.stageExtractor_bounded layout fixed statement (count + 1) used
        coefficients within
      refine (prEvent_mono _ _
        (RoundExtractor.badChallenge
          (Pcs.RingSwitch.stageExtractor layout fixed statement (count + 1) used coefficients))
        ?_).trans ((_root_.RoundByRound.GameFamily.isBounded_iff _ _).mp source.1 round context)
      rintro challenge ⟨q, bad, good⟩
      change Whir.Table K M at q
      change q = fixed ∧ Retained.input
        (ringCoreLabels layout statement count (used + 1) (coefficients.push challenge)) q at good
      rw [ringCore_input] at good
      exact ⟨q, bad, good⟩

/-- The six-draw labels end at the ring-switched weighted claim. -/
theorem ringCore_terminalPredicate {n M : ℕ} (layout : Pcs.RingSwitch.Layout n M)
    (statement : Pcs.RingSwitch.Statement n) (path : (Pcs.RingSwitch.draws 6).tree.ExecutionPath)
    (q : Whir.Table K M) :
    viewedTerminalPredicate (ringCoreLabels layout statement 6 0 #v[]) path q ↔
      (Pcs.RingSwitch.outputClaim layout statement (Pcs.RingSwitch.coefficients 6 path)).Holds
        (fun u => ofK (q u)) := by
  let fs : Vector E 6 := #v[path.1, path.2.1, path.2.2.1, path.2.2.2.1,
    path.2.2.2.2.1, path.2.2.2.2.2.1]
  have hfs : fs = Pcs.RingSwitch.coefficients 6 path := by
    apply Vector.ext
    intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst i <;> rfl
  have endpoint := Pcs.RingSwitch.stage_six_iff layout q q statement fs
  simp only [Pcs.RingSwitch.stageState, Pcs.RingSwitch.outputState, true_and] at endpoint
  rw [← hfs]
  exact endpoint

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ} (kt : KeccakTable S L M)

namespace KeccakTable

/-- The table sumcheck's instance coordinates as the GKR's first messages. -/
def instanceHistory (out : TableSumcheck.Output S L k) : List (List E) :=
  List.ofFn fun i => [kt.instancePoint out i]

/-- The GKR transcript of the table's instance point and the suffix messages. -/
def gkrTranscript (out : TableSumcheck.Output S L k) (path : (gkrProtocol kt.p).tree.ExecutionPath) :
    Keccak.Gkr.Transcript E kt.p :=
  { decodeTranscript kt.p (kt.instanceHistory out ++ Keccak.Gkr.pathMessages (gkrSteps kt.p) path) with
    instancePoint := kt.instancePoint out }

/-- The parsed transcript's instance point is the decoded one. -/
theorem gkrTranscript_decode (out : TableSumcheck.Output S L k) (path : (gkrProtocol kt.p).tree.ExecutionPath) :
    kt.gkrTranscript out path =
      decodeTranscript kt.p (kt.instanceHistory out ++ Keccak.Gkr.pathMessages (gkrSteps kt.p) path) := by
  apply transcript_ext
  · funext i
    change kt.instancePoint out i = wireValue _ i.val 0
    symm
    apply wireValue_scalar
    rw [List.getElem?_append_left (by rw [instanceHistory, List.length_ofFn]; exact i.isLt)]
    simp only [instanceHistory, List.getElem?_ofFn, i.isLt, dite_true, Fin.eta]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The parsed transcript encodes the instance point and the suffix messages. -/
theorem gkrTranscript_messages (out : TableSumcheck.Output S L k)
    (path : (gkrProtocol kt.p).tree.ExecutionPath) :
    Keccak.Gkr.transcriptMessages (kt.gkrTranscript out path) =
      kt.instanceHistory out ++ Keccak.Gkr.pathMessages (gkrSteps kt.p) path := by
  rw [gkrTranscript_decode]
  exact encode_decodeTranscript _ (instanceSuffix_widths (kt.instancePoint out) path)

/-- The middle-lane word claim on the slot region. -/
def wordClaim (t : Keccak.Gkr.Transcript E kt.p) : Whir.Claim E M :=
  ⟨Whir.eqWeight (kt.ring.lift (Keccak.Gkr.appendSlot t.instancePoint t.openings.outputPoint)),
    t.openings.outputValue⟩

/-- The word claim with its weight's table computed once. -/
@[macro_inline] def wordClaimCached (t : Keccak.Gkr.Transcript E kt.p) : Whir.Claim E M :=
  ⟨Pcs.cachedEqWeight (kt.ring.lift (Keccak.Gkr.appendSlot t.instancePoint t.openings.outputPoint)),
    t.openings.outputValue⟩

/-- Materializing the weight leaves the word claim. -/
@[csimp] theorem wordClaim_code : @wordClaim = @wordClaimCached := by
  funext S L M kt t
  simp only [wordClaim, wordClaimCached, Pcs.cachedEqWeight_eq]

/-- The word claim holds exactly when the transmitted word value is the GKR's lane extension. -/
theorem wordClaim_iff (t : Keccak.Gkr.Transcript E kt.p) (q : Whir.Table K M) :
    (kt.wordClaim t).Holds (fun u => ofK (q u)) ↔
      t.openings.outputValue = Keccak.Gkr.mle (fun b : Fin (2 ^ (kt.p + 10)) =>
        Keccak.Gkr.laneValue (ofK g) (kt.bits q (kt.instanceOf b) (kt.slotOf b)))
        (Keccak.Gkr.appendSlot t.instancePoint t.openings.outputPoint) := by
  change Whir.mle (fun u => ofK (q u))
    (kt.ring.lift (Keccak.Gkr.appendSlot t.instancePoint t.openings.outputPoint)) =
      t.openings.outputValue ↔ _
  rw [← kt.ring.read, kt.packed_correct]
  exact eq_comm

/-- The argument's claims on the stack: the ring-switched claim and the word claim. -/
def claims (t : Keccak.Gkr.Transcript E kt.p) (coefficients : Vector E 6) : List (Whir.Claim E M) :=
  [Pcs.RingSwitch.outputClaim kt.ring (sliceStatement t) coefficients, kt.wordClaim t]

/-- The argument's output on the stack: its claims and the GKR's checks. -/
def stackOutput (out : TableSumcheck.Output S L k) (a : Keccak.Gkr.Transcript E kt.p × Vector E 6) :
    StackOutput M :=
  ⟨kt.claims a.1 a.2, decide (kt.Accepts out a.1)⟩

/-- The GKR's endpoint: the frame, its checks and its terminal word and slice relation. -/
def gkrEndpoint (out : TableSumcheck.Output S L k) (frame : Whir.Table K M → Prop)
    (t : Keccak.Gkr.Transcript E kt.p) (q : Whir.Table K M) : Prop :=
  frame q ∧ Keccak.Gkr.Accepts (ofK g) (kt.outputTable out) t ∧
    Keccak.Gkr.TerminalRelation (ofK g) (kt.bits q) t

/-- The GKR's prefix predicates on the stack, framed. -/
def gkrLabels (out : TableSumcheck.Output S L k) (frame : Whir.Table K M → Prop) :
    ListLift.Labels (Whir.Table K M) (gkrProtocol kt.p).tree :=
  wirePullLabels kt.bits frame (ofK g) (kt.outputTable out) (gkrSteps kt.p) (kt.instanceHistory out)
    (fun q => kt.start out q ∧ frame q)

/-- The GKR's prefix claim at the instance point gives the start relation. -/
theorem start_of_prefix (out : TableSumcheck.Output S L k) (q : Whir.Table K M)
    (known : Keccak.Gkr.nextPrefixClaim (ofK g) (kt.outputTable out) (gkrSteps kt.p)
      (kt.instanceHistory out) (kt.bits q)) : kt.start out q := by
  intro rest
  apply instancePrefix_identity (ofK g) (kt.outputTable out) (kt.bits q) (kt.instancePoint out) known
  intro coordinate
  simp only [initialPoint, coordinate.isLt, dite_true]

/-- The GKR's steps after the instance draws are not empty. -/
theorem gkrSteps_isEmpty : (gkrSteps kt.p).isEmpty = false := by
  obtain ⟨rest, first⟩ := wireSuffix_first kt.p
  rw [gkrSteps, first]
  rfl

/-- The GKR as a reduction on the stack from the start relation, framed. -/
noncomputable def gkrReduction (out : TableSumcheck.Output S L k) (frame : Whir.Table K M → Prop) :
    Reduction (gkrProtocol kt.p) (Whir.Table K M) (Keccak.Gkr.Transcript E kt.p) :=
  componentReduction (gkrProtocol kt.p) (kt.gkrLabels out frame) (kt.gkrTranscript out)
    (kt.gkrEndpoint out frame) (Keccak.Gkr.wireChallenges E (gkrSteps kt.p))
    (fun fixed => Keccak.Gkr.certificate (kt.bits fixed) (ofK g) independentLanePowers (kt.outputTable out))
    (by
      intro fixed _ _
      constructor
      · apply wirePull_preserving kt.bits frame (ofK g) (kt.outputTable out) fixed (gkrSteps kt.p)
          (kt.instanceHistory out)
          (Keccak.Gkr.nextPrefixClaim (ofK g) (kt.outputTable out) (gkrSteps kt.p) (kt.instanceHistory out))
          (fun q => kt.start out q ∧ frame q)
          (fun q hframe known => ⟨kt.start_of_prefix out q known, hframe⟩)
        exact wireSuffix_preserving _ _ _ _ _ List.length_ofFn
      · apply wirePull_bounded kt.bits frame (ofK g) (kt.outputTable out) fixed (gkrSteps kt.p)
          (kt.instanceHistory out)
          (Keccak.Gkr.nextPrefixClaim (ofK g) (kt.outputTable out) (gkrSteps kt.p) (kt.instanceHistory out))
          (fun q => kt.start out q ∧ frame q)
          (fun q hframe known => ⟨kt.start_of_prefix out q known, hframe⟩)
        exact wireSuffix_bounded _ _ _ _ _ List.length_ofFn)
    (endpoint_of_terminalPredicate _ _ _ _ (by
      intro path q
      change ListLift.terminalPredicate (kt.gkrLabels out frame) path q ↔ _
      unfold gkrLabels
      rw [wirePull_terminalPredicate, kt.gkrSteps_isEmpty]
      simp only [Bool.false_eq_true, ↓reduceIte, Keccak.Gkr.finishHistory_eq]
      rw [← gkrTranscript_messages, endpointClaim_transcript]
      exact Iff.rfl))

/-- The GKR reduction starts at the start relation and the frame. -/
theorem gkrReduction_input (out : TableSumcheck.Output S L k) (frame : Whir.Table K M → Prop)
    (q : Whir.Table K M) : (kt.gkrReduction out frame).input q ↔ kt.start out q ∧ frame q := by
  change ListLift.input (kt.gkrLabels out frame) q ↔ _
  unfold gkrLabels
  rw [input_wirePullLabels]

/-- Before ring switching: the GKR's checks, the word claim and the frame. -/
def ringFrame (out : TableSumcheck.Output S L k) (frame : Whir.Table K M → Prop)
    (t : Keccak.Gkr.Transcript E kt.p) (q : Whir.Table K M) : Prop :=
  kt.Accepts out t ∧ (kt.wordClaim t).Holds (fun u => ofK (q u)) ∧ frame q

/-- Ring switching's labels on the stack, framed. -/
def ringLabels (out : TableSumcheck.Output S L k) (frame : Whir.Table K M → Prop)
    (t : Keccak.Gkr.Transcript E kt.p) :
    ListLift.Labels (Whir.Table K M) (Pcs.RingSwitch.draws 6).tree :=
  pullLabels id (kt.ringFrame out frame t) (ringCoreLabels kt.ring (sliceStatement t) 6 0 #v[])

/-- The argument's endpoint: its output holds on the stack, with the frame. -/
def endpoint (out : TableSumcheck.Output S L k) (frame : Whir.Table K M → Prop)
    (a : Keccak.Gkr.Transcript E kt.p × Vector E 6) (q : Whir.Table K M) : Prop :=
  (kt.stackOutput out a).Holds q ∧ frame q

/-- Ring switching ends at the argument's endpoint. -/
theorem ring_endpoint (out : TableSumcheck.Output S L k) (frame : Whir.Table K M → Prop)
    (t : Keccak.Gkr.Transcript E kt.p) :
    EndpointLaw (Pcs.RingSwitch.draws 6) (kt.ringLabels out frame t)
      (Pcs.RingSwitch.coefficients 6) (fun c q => kt.endpoint out frame (t, c) q) :=
  endpoint_of_terminalPredicate (Pcs.RingSwitch.draws 6) (kt.ringLabels out frame t)
    (Pcs.RingSwitch.coefficients 6) _ (by
      intro path q
      rw [ringLabels, terminalPredicate_pullLabels, ringCore_terminalPredicate]
      change _ ∧ (kt.Accepts out t ∧ (kt.wordClaim t).Holds (fun u => ofK (q u)) ∧ frame q) ↔
        (decide (kt.Accepts out t) = true ∧ ∀ claim ∈ kt.claims t (Pcs.RingSwitch.coefficients 6 path),
          claim.Holds (fun u => ofK (q u))) ∧ frame q
      rw [decide_eq_true_iff]
      constructor
      · rintro ⟨switched, accepted, word, framed⟩
        refine ⟨⟨accepted, fun claim member => ?_⟩, framed⟩
        rcases List.mem_cons.mp member with rfl | member
        · exact switched
        · rcases List.mem_cons.mp member with rfl | member
          · exact word
          · exact absurd member List.not_mem_nil
      · rintro ⟨⟨accepted, holds⟩, framed⟩
        exact ⟨holds _ List.mem_cons_self, accepted,
          holds _ (List.mem_cons_of_mem _ List.mem_cons_self), framed⟩)

/-- Ring switching as a reduction on the stack after the GKR. -/
noncomputable def ringReduction (out : TableSumcheck.Output S L k) (frame : Whir.Table K M → Prop)
    (t : Keccak.Gkr.Transcript E kt.p) :
    Reduction (Pcs.RingSwitch.draws 6) (Whir.Table K M) (Vector E 6) :=
  componentReduction (Pcs.RingSwitch.draws 6) (kt.ringLabels out frame t)
    (Pcs.RingSwitch.coefficients 6) (fun c q => kt.endpoint out frame (t, c) q)
    (Pcs.RingSwitch.challenges 6)
    (fun fixed => Pcs.RingSwitch.certificate kt.ring fixed (sliceStatement t))
    (by
      intro fixed _ _
      exact ⟨pull_preserving id (kt.ringFrame out frame t) fixed _ _
          (ringCore_preserving _ _ _ _ _ _),
        pull_bounded id (kt.ringFrame out frame t) fixed _ _ _
          (ringCore_bounded _ _ _ _ _ _ (by decide))⟩)
    (kt.ring_endpoint out frame t)

/-- Ring switching starts where the GKR ends. -/
theorem gkr_ring_seam (out : TableSumcheck.Output S L k) (frame : Whir.Table K M → Prop)
    (t : Keccak.Gkr.Transcript E kt.p) (q : Whir.Table K M) :
    (kt.ringReduction out frame t).input q ↔ (kt.gkrReduction out frame).relation t q := by
  have stages := Pcs.RingSwitch.input_iff_stage_zero kt.ring q q (sliceStatement t)
  simp only [Pcs.RingSwitch.inputState, Pcs.RingSwitch.stageState, true_and] at stages
  change ListLift.input (pullLabels id (kt.ringFrame out frame t)
    (ringCoreLabels kt.ring (sliceStatement t) 6 0 #v[])) q ↔ kt.gkrEndpoint out frame t q
  rw [input_pullLabels, ringCore_input]
  change (∀ k < 2 ^ (6 - 0), Pcs.RingSwitch.frobPair Finset.univ
    (fun i : Fin 64 => ofK (g ^ i.val))
    (fun i => Pcs.RingSwitch.frobMap (Pcs.RingSwitch.ringStages #v[])
      (Pcs.RingSwitch.sliceError kt.ring (sliceStatement t) q i)) k = 0) ∧ _ ↔ _
  rw [← stages]
  simp only [gkrEndpoint, ringFrame, accepts_iff, wordClaim_iff]
  simp only [Keccak.Gkr.TerminalRelation]
  have slices : (∀ z, (sliceStatement t).values z =
      Whir.mle (kt.ring.slices q z) (sliceStatement t).point) ↔
      ∀ z : Fin 64, t.openings.slices z = Keccak.Gkr.mle
        (fun b : Fin (2 ^ (kt.p + 10)) => ZMod.castHom (dvd_refl 2) E
          (kt.bits q (kt.instanceOf b) (kt.slotOf b) z)) (sliceStatement t).point := by
    simp only [kt.slices_correct]
    exact Iff.rfl
  rw [slices]
  constructor
  · rintro ⟨hs, ha, hw, hf⟩
    exact ⟨hf, ha, hw, hs⟩
  · rintro ⟨hf, ha, hw, hs⟩
    exact ⟨hs, ha, hw, hf⟩

/-- The argument's protocol: the GKR's suffix, then six ring-switching draws. -/
def protocol (p : ℕ) : Protocol := appendProtocol (gkrProtocol p) (Pcs.RingSwitch.draws 6)

/-- The argument as a reduction on the stack, framed. -/
noncomputable def keccakReduction (out : TableSumcheck.Output S L k) (frame : Whir.Table K M → Prop) :
    Reduction (protocol kt.p) (Whir.Table K M) (Keccak.Gkr.Transcript E kt.p × Vector E 6) :=
  (kt.gkrReduction out frame).then (kt.ringReduction out frame) (kt.gkr_ring_seam out frame)

/-- The argument's output from a transcript. -/
def parse (out : TableSumcheck.Output S L k) (path : (protocol kt.p).tree.ExecutionPath) :
    Keccak.Gkr.Transcript E kt.p × Vector E 6 :=
  let parts := splitPath (gkrProtocol kt.p) (Pcs.RingSwitch.draws 6) path
  (kt.gkrTranscript out parts.1, Pcs.RingSwitch.coefficients 6 parts.2)

end KeccakTable

end CompStark.Tables.Composed
