/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Composed.Keccak.External
public import CompStark.Keccak.GkrProver.Completeness

/-! The Keccak table's honest argument: the Keccak-f GKR's specification transcript at the table's
instance point, written as the suffix path, then the six ring-switching draws. On a stack whose
witness satisfies the Keccak-f relation, from the start relation, its output holds on the stack
against every coin sequence (`honest`). -/

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

/-- A path of GKR steps read off a message history. -/
def wirePath : (steps : List Keccak.Gkr.WireStep) → List (List E) →
    (Keccak.Gkr.wireTree E steps).ExecutionPath
  | [], _ => PUnit.unit
  | .message _ :: rest, history =>
      ⟨fun i => (history.headD []).getD i.val 0, wirePath rest history.tail⟩
  | .challenge _ :: rest, history => ⟨(history.headD []).getD 0 0, wirePath rest history.tail⟩

/-- A history of the steps' widths is the messages of its path. -/
theorem pathMessages_wirePath (steps : List Keccak.Gkr.WireStep) (history : List (List E))
    (widths : history.map List.length = steps.map wireWidth) :
    Keccak.Gkr.pathMessages steps (wirePath steps history) = history := by
  induction steps generalizing history with
  | nil =>
    cases history with
    | nil => rfl
    | cons _ _ => cases widths
  | cons step rest ih =>
    cases history with
    | nil => cases widths
    | cons head tail =>
      simp only [List.map_cons, List.cons.injEq] at widths
      obtain ⟨width, widths⟩ := widths
      cases step with
      | message n =>
        change List.ofFn (fun i : Fin n => head.getD i.val 0) ::
          Keccak.Gkr.pathMessages rest (wirePath rest tail) = head :: tail
        rw [ih tail widths]
        congr 1
        change head.length = n at width
        subst width
        apply List.ext_getElem (by simp only [List.length_ofFn])
        intro i _ _
        simp only [List.getElem_ofFn, List.getD_eq_getElem _ _ (by assumption)]
      | challenge kind =>
        change [head.getD 0 0] :: Keccak.Gkr.pathMessages rest (wirePath rest tail) = head :: tail
        rw [ih tail widths]
        congr 1
        change head.length = 1 at width
        match head, width with
        | [a], _ => rfl

/-- Round messages have their round widths. -/
theorem roundMessages_widths {n degree : ℕ} (polys : Fin n → Sumcheck.CompressedMessage E degree)
    (point : Fin n → E) :
    (Keccak.Gkr.roundMessages polys point).map List.length = roundWidths n degree := by
  simp only [Keccak.Gkr.roundMessages, roundWidths, List.map_flatten, List.map_ofFn, Function.comp_def,
    List.map_cons, List.map_nil, List.length_ofFn, List.length_singleton, List.ofFn_const]

/-- A layer's messages have the layer widths. -/
theorem layerMessages_widths {p : ℕ} (t : Keccak.Gkr.LayerTranscript E p) :
    (Keccak.Gkr.layerMessages t).map List.length = layerWidths p := by
  simp only [Keccak.Gkr.layerMessages, layerWidths, List.map_append, roundMessages_widths,
    List.map_cons, List.map_nil, List.length_ofFn, List.length_singleton]

/-- A transcript's messages have the transcript widths. -/
theorem transcriptMessages_widths {p : ℕ} (t : Keccak.Gkr.Transcript E p) :
    (Keccak.Gkr.transcriptMessages t).map List.length = (Keccak.Gkr.steps p).map wireWidth := by
  rw [steps_widths]
  simp only [Keccak.Gkr.transcriptMessages, transcriptWidths, List.map_append, List.map_ofFn,
    Function.comp_def, List.map_cons, List.map_nil, List.length_singleton, List.length_ofFn,
    roundMessages_widths, List.map_flatten, layerMessages_widths, List.ofFn_const,
    List.flatten_replicate_singleton]

/-- The six ring-switching draws as a path. -/
def ringPath (c : Vector E 6) : (Pcs.RingSwitch.draws 6).tree.ExecutionPath :=
  ⟨c[0], c[1], c[2], c[3], c[4], c[5], PUnit.unit⟩

/-- The draws of a ring-switching path are its coefficients. -/
theorem coefficients_ringPath (c : Vector E 6) : Pcs.RingSwitch.coefficients 6 (ringPath c) = c := by
  apply Vector.ext
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases cases with h | h | h | h | h | h <;> subst i <;> rfl

/-- Output tables with the same extensions at a transcript's instance point have the same
acceptance. -/
theorem accepts_congr {p : ℕ} (x : E) (left right : Fin (2 ^ (p + 4)) → Fin 25 → E)
    (t : Keccak.Gkr.Transcript E p)
    (equal : ∀ l, Keccak.Gkr.mle (fun b => left b l) t.instancePoint =
      Keccak.Gkr.mle (fun b => right b l) t.instancePoint) :
    Keccak.Gkr.Accepts x left t ↔ Keccak.Gkr.Accepts x right t := by
  have first : Keccak.Gkr.firstClaim x left t = Keccak.Gkr.firstClaim x right t := by
    simp only [Keccak.Gkr.firstClaim, Keccak.Gkr.outputClaimAt, equal]
  have claims : ∀ d, Keccak.Gkr.claimAt x left t d = Keccak.Gkr.claimAt x right t d := by
    intro d
    unfold Keccak.Gkr.claimAt
    rw [first]
  unfold Keccak.Gkr.Accepts
  simp only [claims]

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ} (kt : KeccakTable S L M)

namespace KeccakTable

/-- The GKR's specification transcript at the table's instance point. -/
noncomputable def honestTranscript (out : TableSumcheck.Output S L k) (q : Whir.Table K M)
    (c : Keccak.GkrProver.Challenges E kt.p) : Keccak.Gkr.Transcript E kt.p :=
  Keccak.GkrProver.specificationTranscript (ofK g) (kt.outputs q) (kt.bits q)
    { c with instancePoint := kt.instancePoint out }

/-- The honest transcript's instance point is the table's. -/
theorem honestTranscript_instancePoint (out : TableSumcheck.Output S L k) (q : Whir.Table K M)
    (c : Keccak.GkrProver.Challenges E kt.p) :
    (kt.honestTranscript out q c).instancePoint = kt.instancePoint out := rfl

/-- The honest GKR suffix path. -/
noncomputable def honestGkrPath (out : TableSumcheck.Output S L k) (q : Whir.Table K M)
    (c : Keccak.GkrProver.Challenges E kt.p) : (gkrProtocol kt.p).tree.ExecutionPath :=
  wirePath (gkrSteps kt.p) ((Keccak.Gkr.transcriptMessages (kt.honestTranscript out q c)).drop (kt.p + 4))

/-- The honest suffix path parses to the honest transcript. -/
theorem gkrTranscript_honest (out : TableSumcheck.Output S L k) (q : Whir.Table K M)
    (c : Keccak.GkrProver.Challenges E kt.p) :
    kt.gkrTranscript out (kt.honestGkrPath out q c) = kt.honestTranscript out q c := by
  set t := kt.honestTranscript out q c
  have widths := transcriptMessages_widths t
  have hsplit : Keccak.Gkr.transcriptMessages t =
      kt.instanceHistory out ++ (Keccak.Gkr.transcriptMessages t).drop (kt.p + 4) := by
    conv_lhs => rw [← List.take_append_drop (kt.p + 4) (Keccak.Gkr.transcriptMessages t)]
    congr 1
    unfold Keccak.Gkr.transcriptMessages instanceHistory
    simp only [List.append_assoc]
    rw [List.take_left' (by simp only [List.length_ofFn])]
    rfl
  rw [gkrTranscript_decode, honestGkrPath, pathMessages_wirePath]
  · rw [← hsplit, decodeTranscript_encode]
  · rw [List.map_drop]
    change List.drop _ (List.map List.length (Keccak.Gkr.transcriptMessages t)) = _
    rw [widths, gkrSteps, List.map_drop]

/-- The honest argument: the GKR's specification transcript, then the six ring-switching draws. -/
noncomputable def honest (hM : (S.stackBlocks L).total ≤ 2 ^ M) : (kt.external (k := k) hM).Honest where
  Coins := Keccak.GkrProver.Challenges E kt.p × Vector E 6
  honest out q coins := joinPath _ _ (kt.honestGkrPath out q coins.1) (ringPath coins.2)
  honest_holds out q coins hstart hext := by
    set t := kt.honestTranscript out q coins.1
    have relation := (kt.external_interpret_iff q).mp hext
    obtain ⟨accepted, terminal⟩ := Keccak.GkrProver.specificationTranscript_complete (ofK g) (kt.outputs q)
      (kt.bits q) { coins.1 with instancePoint := kt.instancePoint out } relation
    have hout : (kt.external (k := k) hM).output out (joinPath _ _ (kt.honestGkrPath out q coins.1)
        (ringPath coins.2)) = (t, coins.2) := by
      change kt.parse out _ = _
      unfold parse
      rw [splitPath_joinPath]
      dsimp only
      rw [gkrTranscript_honest, coefficients_ringPath]
    rw [hout]
    have lanes (l : Fin 25) : Keccak.Gkr.mle (fun b => kt.outputs q b l) t.instancePoint =
        Keccak.Gkr.mle (fun b => kt.outputTable out b l) t.instancePoint := by
      rw [honestTranscript_instancePoint, initialSuffix_output (ofK g) _ (kt.bits q) _ hstart l]
      simp only [outputs_eq]
    have haccepts : kt.Accepts out t :=
      (kt.accepts_iff out t).mpr ((accepts_congr (ofK g) _ _ t lanes).mp accepted)
    refine ⟨decide_eq_true haccepts, fun claim member => ?_⟩
    rcases List.mem_cons.mp member with rfl | member
    · change (∑ u, Pcs.RingSwitch.ringWeight kt.ring (sliceStatement t) coins.2 u * ofK (q u)) =
        Pcs.RingSwitch.ringTarget (sliceStatement t) coins.2
      rw [← Pcs.RingSwitch.transformed_slices_eq_weighted]
      unfold Pcs.RingSwitch.ringTarget
      apply Finset.sum_congr rfl
      intro i _
      congr 2
      rw [kt.slices_correct]
      exact (terminal.2 i).symm
    · rcases List.mem_cons.mp member with rfl | member
      · exact (kt.wordClaim_iff t q).mpr terminal.1
      · exact absurd member List.not_mem_nil

end KeccakTable

end CompStark.Tables.Composed
