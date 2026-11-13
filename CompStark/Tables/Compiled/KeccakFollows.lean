/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Compiled.KeccakProver
public import CompStark.Tables.Composed.Keccak.Honest
public import CompStark.Keccak.GkrProver.WriterSchedule
public import CompStark.Compiled.ProverRun
public import CompStark.Keccak.GkrProver.WitnessTrace

/-! The native Keccak-f GKR prover follows the Keccak table's honest argument. A prover that sends
a history's messages runs to the history's path when every challenge of the history is the duplex's
draw at its point (`listProver_idealRun`). The native writer draws every challenge of its transcript
from the duplex (`nativeTranscript_drawn`), and from the start relation and the Keccak-f relation its
transcript is the specification transcript at its own challenges (`nativeTranscript_honest`). -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

@[expose] public section

namespace CompStark.Tables.Compiled

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System
open CompStark.Compiled CompStark.Tables.Composed CompStark.Keccak CompStark.Compose
open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.Security

/-- Every challenge entry of a history is the duplex's draw after the entries before it. -/
def WireDrawn : Transcript.State → List Keccak.Gkr.WireStep → List (List E) → Prop
  | _, [], _ => True
  | s, .message n :: rest, history =>
      WireDrawn (Transcript.replay s (fieldEvents fun i : Fin n => (history.headD []).getD i.val 0)) rest
        history.tail
  | s, .challenge _ :: rest, history =>
      (history.headD []).getD 0 0 = (Transcript.squeeze s).1 ∧
        WireDrawn (Transcript.squeeze s).2 rest history.tail

/-- A scalar draw is one squeeze. -/
theorem scalarDraw_run (s : Transcript.State) : scalarDraw.run s = Transcript.squeeze s := rfl

/-- A prover sending a history's messages runs to the history's path when the history's challenges
are the duplex's draws. -/
theorem listProver_idealRun : (steps : List Keccak.Gkr.WireStep) → (history : List (List E)) →
    (s : Transcript.State) → WireDrawn s steps history →
    ∃ final, (gkrPresentation steps).idealRun (listProver steps history) s =
      some (wirePath steps history, final)
  | [], _, s, _ => ⟨s, rfl⟩
  | .message n :: rest, history, s, drawn => by
    obtain ⟨final, run⟩ := listProver_idealRun rest history.tail _ drawn
    refine ⟨final, ?_⟩
    change ((gkrPresentation rest).idealRun (listProver rest history.tail)
      (Transcript.replay s (fieldEvents fun i : Fin n => (history.headD []).getD i.val 0))).map _ = _
    rw [run]
    rfl
  | .challenge kind :: rest, history, s, drawn => by
    obtain ⟨final, run⟩ := listProver_idealRun rest history.tail _ drawn.2
    refine ⟨final, ?_⟩
    change ((gkrPresentation rest).idealRun (listProver rest history.tail) (Transcript.squeeze s).2).map _ = _
    rw [run]
    have head : (history.headD []).getD 0 0 = (scalarDraw.run s).1 := drawn.1
    change _ = some ((⟨(history.headD []).getD 0 0, wirePath rest history.tail⟩ :
      (Keccak.Gkr.wireTree E (.challenge kind :: rest)).ExecutionPath), final)
    rw [head]
    rfl

/-- A prover chosen from the duplex state runs as the prover chosen at its starting state. -/
theorem statefulProver_idealRun (steps : List Keccak.Gkr.WireStep)
    (prover : Transcript.State → (gkrPresentation steps).Prover) (s : Transcript.State) :
    (gkrPresentation steps).idealRun (statefulProver steps prover) s =
      (gkrPresentation steps).idealRun (prover s) s := by
  cases steps with
  | nil => rfl
  | cons step rest => cases step <;> rfl

/-- A history whose challenges a tracking writer's log samples has the duplex's draws. -/
theorem wireDrawn_of_drawn : (steps : List Keccak.Gkr.WireStep) → (history : List (List E)) →
    (s : Transcript.State) → history.map List.length = steps.map wireWidth →
    Keccak.GkrProver.Drawn s
      (Keccak.GkrProver.historyLog steps (history.map (List.map BF64.WordExt3.ofField))) →
    WireDrawn s steps history
  | [], _, _, _, _ => trivial
  | _ :: _, [], _, widths, _ => by cases widths
  | .message n :: rest, entry :: history, s, widths, drawn => by
    simp only [List.map_cons, List.cons.injEq] at widths
    change Keccak.GkrProver.Drawn s ((entry.map BF64.WordExt3.ofField).map Keccak.GkrProver.WriterEvent.write ++
      Keccak.GkrProver.historyLog rest (history.map (List.map BF64.WordExt3.ofField))) at drawn
    rw [Keccak.GkrProver.drawn_append] at drawn
    have events : ((entry.map BF64.WordExt3.ofField).map Keccak.GkrProver.WriterEvent.write).map
        Keccak.GkrProver.WriterEvent.event = fieldEvents fun i : Fin n => entry.getD i.val 0 := by
      have width : entry.length = n := widths.1
      subst width
      simp only [List.map_map, Function.comp_def, Keccak.GkrProver.WriterEvent.event,
        BF64.WordExt3.toField_ofField, fieldEvents, Transcript.scalarEvents, Vector.toList_ofFn]
      congr 1
      apply List.ext_getElem (by simp only [List.length_ofFn])
      intro i _ _
      simp only [List.getElem_ofFn]
      exact (List.getD_eq_getElem _ _ ‹_›).symm
    rw [events] at drawn
    exact wireDrawn_of_drawn rest history _ widths.2 drawn.2
  | .challenge _ :: rest, entry :: history, s, widths, drawn => by
    simp only [List.map_cons, List.cons.injEq] at widths
    obtain ⟨width, widths⟩ := widths
    match entry, width with
    | [x], _ =>
      change Keccak.GkrProver.Drawn s (Keccak.GkrProver.WriterEvent.sample (BF64.WordExt3.ofField x) ::
        Keccak.GkrProver.historyLog rest (history.map (List.map BF64.WordExt3.ofField))) at drawn
      obtain ⟨value, rest'⟩ := drawn
      rw [BF64.WordExt3.toField_ofField] at value
      exact ⟨value, wireDrawn_of_drawn rest history _ widths rest'⟩

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ} (kt : KeccakTable S L M)

/-- The native transcript draws every challenge after its instance point from the duplex. -/
theorem nativeTranscript_drawn (state : Transcript.State) (o : TableSumcheck.Output S L k)
    (q : Whir.Table K M) :
    WireDrawn state (gkrSteps kt.p)
      ((Keccak.Gkr.transcriptMessages (nativeTranscript kt state o q)).drop (kt.p + 4)) := by
  have drawn := Keccak.GkrProver.prove_drawn { state := TranscriptDuplex.duplexState state }
    (Keccak.GkrProver.buildWitness (kt.p + 4)
      (Array.ofFn fun u : Fin (2 ^ (kt.p + 10)) => UInt64.ofBitVec (kt.word q u).toBitVec))
    (Array.ofFn fun u : Fin (2 ^ (kt.p + 10)) => UInt64.ofBitVec (kt.word q u).toBitVec)
    (Array.ofFn fun i : Fin (kt.p + 4) => BF64.WordExt3.ofField (kt.instancePoint o i))
    (Array.ofFn fun l : Fin 25 =>
      BF64.WordExt3.ofField (o.values ⟨kt.table, kt.active⟩ (kt.outputIndex l)))
    (Keccak.GkrProver.Writer.tracks_fresh state) (Array.size_ofFn ..)
  simp only [Erased.out_mk, List.map_nil] at drawn
  refine wireDrawn_of_drawn _ _ _ ?_ drawn
  rw [List.map_drop, transcriptMessages_widths, gkrSteps, List.map_drop]

/-- The native Keccak-f GKR on a block of at least 256 permutations, small enough for its machine
indices, is the specification transcript at its own challenges for a witness satisfying the
Keccak-f relation and output values that are the outputs' extensions at the batch point. -/
theorem prove_eq_specification {p : ℕ} (hp : 4 ≤ p) (small : 1600 * (2 ^ (p + 4) / 64) ≤ 2 ^ 32)
    (writer : Keccak.GkrProver.Writer) (committed : Array UInt64) (hc : committed.size = 2 ^ (p + 10))
    (batch output : Array BF64.WordExt3) (hb : batch.size = p + 4) (out : Fin (2 ^ (p + 4)) → Fin 25 → E)
    (relation : Keccak.Gkr.InputRelation (ofK g) out (Keccak.GkrProver.committedWitness p committed))
    (ho : ∀ l : Fin 25, output[l.val]!.toField =
      Keccak.Gkr.mle (fun b => out b l) fun i : Fin (p + 4) => batch[i.val]!.toField) :
    let t := (Keccak.GkrProver.prove writer (Keccak.GkrProver.buildWitness (p + 4) committed) committed
      batch output).toProtocol p (Keccak.GkrProver.prove_layers_size ..)
    t = Keccak.GkrProver.specificationTranscript (ofK g) out (Keccak.GkrProver.committedWitness p committed)
      (Keccak.GkrProver.Challenges.ofTranscript t) := by
  obtain ⟨h, rfl⟩ : ∃ h, p = h + 4 := ⟨p - 4, by omega⟩
  exact Keccak.GkrProver.prove_eq_specificationTranscript writer _ committed batch output
    (Keccak.GkrProver.buildWitness_nLog _ _) hb
    (by rw [hc, show h + 4 + 10 = (h + 8) + 6 by omega, pow_add, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]; rfl)
    (Keccak.GkrProver.buildWitness_preChiRefines committed relation.1)
    (by rw [Keccak.GkrProver.buildWitness_nLog]; exact small.trans USize.le_size) out ho

/-- A constant table's extension is its value. -/
theorem mle_const {n : ℕ} (c : E) (r : Fin n → E) : Keccak.Gkr.mle (fun _ => c) r = c := by
  rw [Keccak.Gkr.mle, ← Finset.sum_mul, Keccak.Gkr.eqWeight_sum, one_mul]

/-- The native prover's committed words are the region's words. -/
def regionWords (q : Whir.Table K M) : Array UInt64 :=
  Array.ofFn fun u : Fin (2 ^ (kt.p + 10)) => UInt64.ofBitVec (kt.word q u).toBitVec

/-- The region's words, sliced, are the stack's GKR witness. -/
theorem committedWitness_regionWords (q : Whir.Table K M) :
    Keccak.GkrProver.committedWitness kt.p (regionWords kt q) = kt.bits q := by
  funext b slot z
  have hn : 2 ^ (kt.p + 10) = 64 * 2 ^ (kt.p + 4) := by
    rw [show kt.p + 10 = 6 + (kt.p + 4) by omega, pow_add]; rfl
  have hu : slot.val * 2 ^ (kt.p + 4) + b.val < 2 ^ (kt.p + 10) := by
    have := slot.isLt; have := b.isLt; rw [hn]; nlinarith
  have hi : kt.instanceOf ⟨_, hu⟩ = b := Fin.ext (by
    change (slot.val * 2 ^ (kt.p + 4) + b.val) % 2 ^ (kt.p + 4) = b.val
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt b.isLt])
  have hs : kt.slotOf ⟨_, hu⟩ = slot := Fin.ext (by
    change (slot.val * 2 ^ (kt.p + 4) + b.val) / 2 ^ (kt.p + 4) = slot.val
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt b.isLt, Nat.zero_add])
  simp only [Keccak.GkrProver.committedWitness, regionWords]
  rw [getElem!_pos _ _ (by rw [Array.size_ofFn]; exact hu), Array.getElem_ofFn, kt.word_eq, hi, hs]
  simp only [Keccak.GkrProver.sliceBit, KeccakTable.bits, witnessBits, Pcs.wordBits,
    BitVec.getLsbD_eq_getElem z.isLt]

/-- From the start relation and the Keccak-f relation, the native transcript is the honest
transcript at its own challenges. -/
theorem nativeTranscript_honest (hp : 4 ≤ kt.p) (small : 1600 * (2 ^ (kt.p + 4) / 64) ≤ 2 ^ 32)
    (state : Transcript.State) (o : TableSumcheck.Output S L k) (q : Whir.Table K M)
    (hstart : kt.start o q) (hext : S.external (kt.interpret q)) :
    nativeTranscript kt state o q =
      kt.honestTranscript o q (Keccak.GkrProver.Challenges.ofTranscript (nativeTranscript kt state o q)) := by
  have relation := (kt.external_interpret_iff q).mp hext
  rw [← committedWitness_regionWords kt q] at relation
  have eq := prove_eq_specification hp small { state := TranscriptDuplex.duplexState state }
    (regionWords kt q) (Array.size_ofFn ..)
    (Array.ofFn fun i : Fin (kt.p + 4) => BF64.WordExt3.ofField (kt.instancePoint o i))
    (Array.ofFn fun l : Fin 25 => BF64.WordExt3.ofField (o.values ⟨kt.table, kt.active⟩ (kt.outputIndex l)))
    (Array.size_ofFn ..) (kt.outputs q) relation (by
      intro l
      have batch : (fun i : Fin (kt.p + 4) =>
          (Array.ofFn fun i : Fin (kt.p + 4) => BF64.WordExt3.ofField (kt.instancePoint o i))[i.val]!.toField) =
          kt.instancePoint o := by
        funext i
        rw [getElem!_pos _ _ (by rw [Array.size_ofFn]; exact i.isLt), Array.getElem_ofFn,
          BF64.WordExt3.toField_ofField]
      rw [batch, getElem!_pos _ _ (by rw [Array.size_ofFn]; exact l.isLt), Array.getElem_ofFn,
        BF64.WordExt3.toField_ofField]
      have lane := initialSuffix_output (ofK g) (kt.outputTable o) (kt.bits q) (kt.instancePoint o) hstart l
      simp only [KeccakTable.outputTable, mle_const] at lane
      rw [lane]
      simp only [KeccakTable.outputs_eq])
  rw [committedWitness_regionWords kt q] at eq
  have point : (nativeTranscript kt state o q).instancePoint = kt.instancePoint o := by
    funext i
    change (Array.ofFn fun i : Fin (kt.p + 4) => BF64.WordExt3.ofField (kt.instancePoint o i))[i.val]!.toField = _
    rw [getElem!_pos _ _ (by rw [Array.size_ofFn]; exact i.isLt), Array.getElem_ofFn,
      BF64.WordExt3.toField_ofField]
  unfold KeccakTable.honestTranscript
  rw [← point]
  exact eq

/-- A ring-switching path is the path of its draws. -/
theorem ringPath_coefficients (x : (Pcs.RingSwitch.draws 6).tree.ExecutionPath) :
    ringPath (Pcs.RingSwitch.coefficients 6 x) = x := by
  obtain ⟨a, b, c, d, e, f, ⟨⟩⟩ := x
  rfl

/-- From the start relation and the Keccak-f relation, every ideal run of the native Keccak prover
is the honest argument at some coins: the native transcript's own challenges, then the six
ring-switching draws. -/
theorem keccakProver_honest (hM : (S.stackBlocks L).total ≤ 2 ^ M) (hp : 4 ≤ kt.p)
    (small : 1600 * (2 ^ (kt.p + 4) / 64) ≤ 2 ^ 32) (o : TableSumcheck.Output S L k) (q : Whir.Table K M)
    (hstart : kt.start o q) (hext : S.external (kt.interpret q)) (state : Transcript.State)
    (path : (KeccakTable.protocol kt.p).tree.ExecutionPath) (final : Transcript.State)
    (run : (keccakPresentation kt).idealRun (keccakProver kt o q) state = some (path, final)) :
    ∃ coins, path = (kt.honest (k := k) hM).honest o q coins := by
  unfold keccakPresentation keccakProver at run
  rw [Presentation.idealRun_append, statefulProver_idealRun] at run
  obtain ⟨gkrFinal, gkrRun⟩ := listProver_idealRun (gkrSteps kt.p) _ state (nativeTranscript_drawn kt state o q)
  rw [gkrRun, Option.bind_some] at run
  obtain ⟨tail, _, htail⟩ := Option.map_eq_some_iff.mp run
  refine ⟨(Keccak.GkrProver.Challenges.ofTranscript (nativeTranscript kt state o q),
    Pcs.RingSwitch.coefficients 6 tail.1), ?_⟩
  rw [← (Prod.mk.inj htail).1]
  change _ = joinPath _ _ (kt.honestGkrPath o q _) (ringPath _)
  rw [ringPath_coefficients]
  unfold KeccakTable.honestGkrPath
  rw [← nativeTranscript_honest kt hp small state o q hstart hext]
  rfl

end CompStark.Tables.Compiled
