/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.NativeCompleteness
public import CompStark.Keccak.GkrProver.OpeningTrace
public import CompStark.Keccak.Transcript.Native

/-! The native writer's erased log against the duplex transcript. A writer tracks a starting state
when its duplex state is the replay of its log and every logged sample is the challenge drawn at
that point (`Writer.Tracks`); writes and samples preserve this. Each sumcheck run of the native
prover appends one message and one sample per round to the log (`RunLog`). -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak CompStark.BinaryFields BF64 CompPoly.Extension

/-- The transcript event of a writer event. -/
def WriterEvent.event : WriterEvent → Transcript.Event
  | .write a => .absorb (.scalar a.toField)
  | .sample _ => .squeeze

/-- Every logged sample is the duplex's challenge after the events before it. -/
def Drawn : Transcript.State → List WriterEvent → Prop
  | _, [] => True
  | s, .write a :: rest => Drawn (Transcript.absorb s (.scalar a.toField)) rest
  | s, .sample r :: rest => r.toField = (Transcript.squeeze s).1 ∧ Drawn (Transcript.squeeze s).2 rest

/-- Replay of a concatenated log. -/
theorem replay_events_append (s : Transcript.State) (a b : List WriterEvent) :
    Transcript.replay s ((a ++ b).map WriterEvent.event) =
      Transcript.replay (Transcript.replay s (a.map WriterEvent.event)) (b.map WriterEvent.event) := by
  rw [List.map_append]
  exact List.foldl_append ..

/-- Drawn samples of a concatenated log. -/
theorem drawn_append (s : Transcript.State) (a b : List WriterEvent) :
    Drawn s (a ++ b) ↔ Drawn s a ∧ Drawn (Transcript.replay s (a.map WriterEvent.event)) b := by
  induction a generalizing s with
  | nil => simp only [List.nil_append, Drawn, List.map_nil, true_and]; rfl
  | cons e a ih =>
    cases e with
    | write x => exact ih _
    | sample r =>
      simp only [List.cons_append, Drawn, ih, and_assoc]
      rfl

/-- The writer's duplex state is the replay of its log from `s`, and each logged sample is the
challenge drawn at its point. -/
def Writer.Tracks (s : Transcript.State) (writer : Writer) : Prop :=
  writer.state = TranscriptDuplex.duplexState
      (Transcript.replay s (writer.log.out.map WriterEvent.event)) ∧
    Drawn s writer.log.out

/-- A fresh writer at a duplex state tracks that state. -/
theorem Writer.tracks_fresh (s : Transcript.State) :
    ({ state := TranscriptDuplex.duplexState s } : Writer).Tracks s :=
  ⟨by simp only [Erased.out_mk, List.map_nil]; rfl, by simp only [Erased.out_mk]; trivial⟩

/-- A written scalar's lanes are its transcript item's. -/
theorem write_lanes (a : W) :
    (#[a.c0.val, a.c1.val, a.c2.val, 1] : Array UInt64) =
      (Transcript.Item.scalar a.toField).lanes.toArray := by
  simp only [Transcript.Item.lanes, E.limb, WordExt3.toField, Ext.coeff_ofFn]
  rfl

/-- Three sampled lanes as a word element are the squeezed scalar. -/
theorem sample_toField (u0 u1 u2 : UInt64) :
    (⟨⟨u0⟩, ⟨u1⟩, ⟨u2⟩⟩ : W).toField = E.ofLimbs (Lanes.wordLane u0) (Lanes.wordLane u1)
      (Lanes.wordLane u2) := by
  apply Ext.ext
  intro i
  fin_cases i <;> rfl

/-- Writing appends a write event. -/
theorem Writer.log_write (writer : Writer) (a : W) :
    (writer.write a).log.out = writer.log.out ++ [.write a] := by
  simp only [Writer.write, Erased.map_out]

/-- Sampling appends the sampled value. -/
theorem Writer.log_sample (writer : Writer) :
    writer.sample.2.log.out = writer.log.out ++ [.sample writer.sample.1] := by
  simp only [Writer.sample, Erased.map_out]

/-- Writing preserves tracking. -/
theorem Writer.Tracks.write {s : Transcript.State} {writer : Writer} (h : writer.Tracks s) (a : W) :
    (writer.write a).Tracks s := by
  obtain ⟨state, drawn⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Writer.log_write, replay_events_append]
    simp only [Writer.write]
    rw [state, write_lanes]
    exact TranscriptDuplex.absorb_spec _ _
  · rw [Writer.log_write, drawn_append]
    exact ⟨drawn, trivial⟩

/-- Sampling preserves tracking and draws the duplex's challenge. -/
theorem Writer.Tracks.sample {s : Transcript.State} {writer : Writer} (h : writer.Tracks s) :
    writer.sample.2.Tracks s ∧ writer.sample.1.toField =
      (Transcript.squeeze (Transcript.replay s (writer.log.out.map WriterEvent.event))).1 := by
  obtain ⟨state, drawn⟩ := h
  have spec := TranscriptDuplex.sample_spec (Transcript.replay s (writer.log.out.map WriterEvent.event))
  rw [← state] at spec
  have value : writer.sample.1.toField =
      (Transcript.squeeze (Transcript.replay s (writer.log.out.map WriterEvent.event))).1 := by
    rw [← (Prod.ext_iff.mp spec).1]
    exact sample_toField _ _ _
  refine ⟨⟨?_, ?_⟩, value⟩
  · rw [Writer.log_sample, replay_events_append]
    exact (Prod.ext_iff.mp spec).2
  · rw [Writer.log_sample, drawn_append]
    exact ⟨drawn, value, trivial⟩

/-- Writing a buffer appends its writes. -/
theorem Writer.log_writeAll (writer : Writer) (a : Array W) :
    (writer.writeAll a).log.out = writer.log.out ++ a.toList.map WriterEvent.write := by
  rw [Writer.writeAll, ← Array.foldl_toList]
  generalize a.toList = xs
  induction xs generalizing writer with
  | nil => simp only [List.foldl_nil, List.map_nil, List.append_nil]
  | cons x xs ih => rw [List.foldl_cons, ih, Writer.log_write, List.map_cons, List.append_assoc]; rfl

/-- Writing a buffer preserves tracking. -/
theorem Writer.Tracks.writeAll {s : Transcript.State} {writer : Writer} (h : writer.Tracks s)
    (a : Array W) : (writer.writeAll a).Tracks s := by
  rw [Writer.writeAll, ← Array.foldl_toList]
  generalize a.toList = xs
  induction xs generalizing writer with
  | nil => exact h
  | cons x xs ih => exact ih (h.write x)

/-- The writer events of a sumcheck run: each round's message, then its challenge. -/
def roundLog (messages : List (Array W)) (point : List W) : List WriterEvent :=
  (List.zipWith (fun m r => m.toList.map WriterEvent.write ++ [WriterEvent.sample r]) messages point).flatten

/-- A run's writer has appended its rounds to a starting log, with messages of one width, and
tracks `s`. -/
structure RunLog (s : Transcript.State) (start : List WriterEvent) (width : Nat) (writer : Writer)
    (messages : Array (Array W)) (point : Array W) : Prop where
  log : writer.log.out = start ++ roundLog messages.toList point.toList
  size : messages.size = point.size
  widths : ∀ m ∈ messages.toList, m.size = width
  tracks : writer.Tracks s

/-- A run starts with an empty round log. -/
theorem RunLog.empty {s : Transcript.State} {writer : Writer} (h : writer.Tracks s) (width : Nat) :
    RunLog s writer.log.out width writer #[] #[] :=
  ⟨by simp only [roundLog, List.zipWith_nil_left, List.flatten_nil, List.append_nil],
    rfl, by simp only [List.not_mem_nil, false_implies, implies_true], h⟩

/-- One round writes a message and samples its challenge. -/
theorem RunLog.push {s : Transcript.State} {start : List WriterEvent} {width : Nat} {writer : Writer}
    {messages : Array (Array W)} {point : Array W} (h : RunLog s start width writer messages point)
    (m : Array W) (hm : m.size = width) :
    RunLog s start width ((writer.writeAll m).sample).2 (messages.push m)
      (point.push ((writer.writeAll m).sample).1) where
  log := by
    rw [Writer.log_sample, Writer.log_writeAll, h.log, Array.toList_push, Array.toList_push, roundLog,
      roundLog, List.zipWith_append (by simp only [Array.length_toList, h.size])]
    simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.flatten_append, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.append_assoc]
  size := by simp only [Array.size_push, h.size]
  widths := by
    intro x hx
    rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · exact h.widths x hx
    · rw [hx]; exact hm
  tracks := ((h.tracks.writeAll m).sample).1

/-- A property preserved by every step of a fold holds after it. -/
theorem foldl_preserves {α β : Type} {P : α → Prop} (f : α → β → α) (l : List β) (init : α)
    (h0 : P init) (h : ∀ a x, P a → P (f a x)) : P (l.foldl f init) := by
  induction l generalizing init with
  | nil => exact h0
  | cons x l ih => exact ih _ (h _ _ h0)

/-- Sampling a challenge vector appends one sample per coordinate and preserves tracking. -/
theorem Writer.sampleMany_log {s : Transcript.State} {writer : Writer} (h : writer.Tracks s) (n : Nat) :
    (writer.sampleMany n).2.Tracks s ∧
      (writer.sampleMany n).2.log.out = writer.log.out ++ (writer.sampleMany n).1.toList.map WriterEvent.sample := by
  simp only [Writer.sampleMany, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, pure_bind, Id.run_pure, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  let step (state : Writer × Array W) (_ : Nat) :=
    let sampled := state.1.sample
    (sampled.2, state.2.push sampled.1)
  change ((List.range' 0 n).foldl step _).1.Tracks s ∧
    ((List.range' 0 n).foldl step _).1.log.out = _ ++ ((List.range' 0 n).foldl step _).2.toList.map _
  refine foldl_preserves (P := fun state : Writer × Array W => state.1.Tracks s ∧
    state.1.log.out = writer.log.out ++ state.2.toList.map WriterEvent.sample) step _ _
    ⟨h, by simp only [List.map_nil, List.append_nil]⟩ ?_
  intro state _ hs
  refine ⟨hs.1.sample.1, ?_⟩
  change state.1.sample.2.log.out = _ ++ (state.2.push state.1.sample.1).toList.map _
  rw [Writer.log_sample, hs.2, Array.toList_push, List.map_append, List.append_assoc]
  rfl

/-- The pack run appends its two-scalar rounds. -/
theorem nativePackRun_runLog (w : SlicedWitness) (d : Nat) (claim : Claim) (s0 : W) (early : Array W)
    {s : Transcript.State} {writer : Writer} (h : writer.Tracks s) (value : W) :
    RunLog s writer.log.out 2 (nativePackRun w d claim s0 early writer value).writer
      (nativePackRun w d claim s0 early writer value).messages
      (nativePackRun w d claim s0 early writer value).point := by
  refine foldl_preserves (P := fun state : PackResult =>
    RunLog s writer.log.out 2 state.writer state.messages state.point) _ _ _ (RunLog.empty h 2) ?_
  intro state i hs
  exact hs.push _ rfl

/-- Position rounds keep their three factor tables. -/
theorem positionRun_factors_size (scale kappa : W) (initial : PositionResult) (n : Nat) :
    (positionRun scale kappa initial n).factors.size = initial.factors.size := by
  induction n with
  | zero => rfl
  | succ n ih => exact (Array.size_map ..).trans ih

/-- The position run appends its three-scalar rounds. -/
theorem positionRun_runLog (scale kappa : W) (initial : PositionResult) {s : Transcript.State}
    {start : List WriterEvent}
    (h : RunLog s start 3 initial.writer initial.messages initial.point) (n : Nat) :
    RunLog s start 3 (positionRun scale kappa initial n).writer (positionRun scale kappa initial n).messages
      (positionRun scale kappa initial n).point := by
  induction n with
  | zero => exact h
  | succ n ih =>
    exact ih.push _ (by rw [Array.size_map, positionRound_size])

/-- A quadratic run appends its two-scalar rounds. -/
theorem quadraticRun_runLog (width : Nat) (scale : W) (initial : QuadraticResult) {s : Transcript.State}
    {start : List WriterEvent}
    (h : RunLog s start 2 initial.writer initial.messages initial.point) (n : Nat) :
    RunLog s start 2 (quadraticRun width scale initial n).writer
      (quadraticRun width scale initial n).messages (quadraticRun width scale initial n).point := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.push _ rfl

/-- A quadratic run over `2^n` rows keeps one row. -/
theorem quadraticRun_a_size (width : Nat) (scale : W) (initial : QuadraticResult) (n : Nat)
    (hw : 0 < width) (ha : initial.a.size = 2^n*width) :
    (quadraticRun width scale initial n).a.size = width := by
  induction n generalizing initial with
  | zero => simp only [quadraticRun]; rw [ha, pow_zero, one_mul]
  | succ n ih =>
    rw [quadraticRun_succ_first]
    apply ih
    change (fold initial.a width _).size = _
    rw [fold_rows_size, ha, pow_succ, Nat.mul_assoc, Nat.mul_div_cancel _ (by omega)]

/-- The product message has its 47 coefficients. -/
theorem product_message_size (w : SlicedWitness) (d : Nat) (claim : Claim) (maps : RmfeProducts) :
    (product w d claim maps).message.size = 47 := by
  simp only [product, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Id.run_pure, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    bind_pure_comp, map_pure]
  refine foldl_preserves (P := fun st : Array W × Array PackedE => st.1.size = 47) _ _ _ ?_ ?_
  · exact Array.size_replicate ..
  intro st m hst
  dsimp only
  apply foldl_preserves (P := fun st : Array W × Array PackedE => st.1.size = 47) _ _ _ hst
  intro st b hst
  dsimp only
  apply foldl_preserves (P := fun st : Array W => st.size = 47) _ _ _ hst
  intro st k hst
  simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hst]

/-- The writer events of one layer: the product message and its point, the pack rounds, the
position rounds, then the evaluations and the batching challenge. -/
def layerLog (layer : Layer) : List WriterEvent :=
  roundLog [layer.product] [layer.s] ++ roundLog layer.packMessages.toList layer.packPoint.toList ++
    roundLog layer.positionMessages.toList layer.positionPoint.toList ++
    roundLog [layer.evaluations] [layer.beta]

/-- The message widths and round counts of a layer: 47 product coefficients, `p+1` two-scalar pack
rounds, eleven three-scalar position rounds and three evaluations. -/
structure LayerWidths (p : Nat) (layer : Layer) : Prop where
  product : layer.product.size = 47
  packCount : layer.packPoint.size = p+1
  positionCount : layer.positionPoint.size = 11
  pack : layer.packMessages.size = layer.packPoint.size
  packWidths : ∀ m ∈ layer.packMessages.toList, m.size = 2
  position : layer.positionMessages.size = layer.positionPoint.size
  positionWidths : ∀ m ∈ layer.positionMessages.toList, m.size = 3
  evaluations : layer.evaluations.size = 3

/-- Rounds of two runs, the second starting where the first ends. -/
theorem roundLog_append (m₁ m₂ : List (Array W)) (p₁ p₂ : List W) (h : m₁.length = p₁.length) :
    roundLog (m₁ ++ m₂) (p₁ ++ p₂) = roundLog m₁ p₁ ++ roundLog m₂ p₂ := by
  rw [roundLog, List.zipWith_append h, List.flatten_append]
  rfl

attribute [local irreducible] product Writer.sample Writer.writeAll instanceWeights sum
  evaluate earlyValues binaryValues prepareWeightMaps packedTable eqTable earlyRound packRoundFromClaim
  packConstants foldPacked positionRound fold foldArrayShared transposeWeights

/-- A layer appends its rounds to the log and preserves tracking. -/
theorem layerFromRuns_log (writer : Writer) (w : SlicedWitness) (d : Nat) (claim : Claim)
    (products : RmfeProducts) {s : Transcript.State} (h : writer.Tracks s) {p : Nat}
    (hp : claim.point.size = p+1) :
    let result := layerFromRuns writer w d claim products
    result.2.2.Tracks s ∧ result.2.2.log.out = writer.log.out ++ layerLog result.1 ∧
      LayerWidths p result.1 ∧ result.2.1.point.size = p+1 := by
  dsimp only [layerFromRuns]
  have hprod := product_message_size w d claim products
  generalize product w d claim products = prod at hprod
  have first := (RunLog.empty h prod.message.size).push prod.message rfl
  generalize hsampled : (writer.writeAll prod.message).sample = sampled at first
  obtain ⟨sv, sw⟩ := sampled
  dsimp only at first ⊢
  generalize hearly : earlyValues _ _ _ _ _ _ = early
  have pack := nativePackRun_runLog w d claim sv early first.tracks (evaluate prod.message sv)
  have packLength := (nativePackRun_lengths w d claim sv early sw (evaluate prod.message sv)).1
  generalize nativePackRun w d claim sv early sw (evaluate prod.message sv) = packRun at pack packLength
  have pos := positionRun_runLog packRun.scale (sum (instanceWeights sv))
    ⟨claim.weights ++ Array.replicate 448 0, Array.ofFn fun k : Fin 3 => Array.ofFn fun j : Fin 2048 =>
      if j.val < 1600 then packRun.table.get (shift j.val k.val) else lane 0, #[], #[], packRun.writer⟩
    (RunLog.empty pack.tracks 3) 11
  have factors := positionRun_factors_size packRun.scale (sum (instanceWeights sv))
    ⟨claim.weights ++ Array.replicate 448 0, Array.ofFn fun k : Fin 3 => Array.ofFn fun j : Fin 2048 =>
      if j.val < 1600 then packRun.table.get (shift j.val k.val) else lane 0, #[], #[], packRun.writer⟩ 11
  have posLength := (positionRun_lengths packRun.scale (sum (instanceWeights sv))
    ⟨claim.weights ++ Array.replicate 448 0, Array.ofFn fun k : Fin 3 => Array.ofFn fun j : Fin 2048 =>
      if j.val < 1600 then packRun.table.get (shift j.val k.val) else lane 0, #[], #[], packRun.writer⟩ 11).1
  rw [positionLoop_eq_run]
  generalize positionRun _ _ _ 11 = posRun at pos factors posLength
  have last := (RunLog.empty pos.tracks (posRun.factors.map (·[0]!)).size).push
    (posRun.factors.map (·[0]!)) rfl
  generalize (posRun.writer.writeAll (posRun.factors.map (·[0]!))).sample = final at last
  obtain ⟨beta, fw⟩ := final
  refine ⟨last.tracks, ?_, ⟨hprod, packLength.trans hp, posLength, pack.size, pack.widths, pos.size,
    pos.widths, ?_⟩, packLength.trans hp⟩
  · rw [last.log, pos.log, pack.log, first.log]
    simp only [layerLog, Array.toList_push, List.nil_append, List.append_assoc]
  · rw [Array.size_map, factors, Array.size_ofFn]

/-- The writer events of the openings: the output rounds, the output value, the input rounds, then
the slices. -/
def openingsLog (openings : Openings) : List WriterEvent :=
  roundLog openings.outputMessages.toList openings.outputPoint.toList ++ [.write openings.outputValue] ++
    roundLog openings.inputMessages.toList openings.inputPoint.toList ++
    openings.slices.toList.map WriterEvent.write

/-- The message widths and round counts of the openings: six output and ten input two-scalar rounds
and sixty-four slices. -/
structure OpeningsWidths (openings : Openings) : Prop where
  outputCount : openings.outputPoint.size = 6
  inputCount : openings.inputPoint.size = 10
  output : openings.outputMessages.size = openings.outputPoint.size
  outputWidths : ∀ m ∈ openings.outputMessages.toList, m.size = 2
  input : openings.inputMessages.size = openings.inputPoint.size
  inputWidths : ∀ m ∈ openings.inputMessages.toList, m.size = 2
  slices : openings.slices.size = 64

attribute [local irreducible] inputBits inputWeights openingPerInstance openingAtInstance

/-- The openings append their rounds and slices to the log and preserve tracking. -/
theorem proveOpenings_log (writer : Writer) (committed : Array UInt64) (n : Nat)
    (words wordWeights : Array W) (middle : W) (claim : Claim) {s : Transcript.State}
    (h : writer.Tracks s) :
    let result := proveOpenings writer committed n words wordWeights middle claim
    result.2.Tracks s ∧ result.2.log.out = writer.log.out ++ openingsLog result.1 ∧
      OpeningsWidths result.1 := by
  rw [proveOpenings_eq_runs]
  dsimp only [openingRuns]
  rw [proveQuadratics_eq_run, proveQuadratics_eq_run, proveQuadratics_eq_run]
  have word := quadraticRun_runLog 1 1 ⟨words, wordWeights, #[], #[], middle, writer⟩
    (RunLog.empty h 2) 6
  have wordLength := (quadraticRun_lengths 1 1 ⟨words, wordWeights, #[], #[], middle, writer⟩ 6).1
  generalize quadraticRun 1 1 ⟨words, wordWeights, #[], #[], middle, writer⟩ 6 = wordRun at word wordLength
  have written := word.tracks.write wordRun.a[0]!
  generalize hfolded : inputBits _ _ _ = folded
  have low := quadraticRun_runLog 1 1
    ⟨openingPerInstance folded (inputWeights claim), claim.mu, #[], #[], claim.value,
      wordRun.writer.write wordRun.a[0]!⟩ (RunLog.empty written 2) 4
  have lowLength := (quadraticRun_lengths 1 1 ⟨openingPerInstance folded (inputWeights claim), claim.mu,
    #[], #[], claim.value, wordRun.writer.write wordRun.a[0]!⟩ 4).1
  generalize quadraticRun 1 1 ⟨openingPerInstance folded (inputWeights claim), claim.mu, #[], #[],
    claim.value, wordRun.writer.write wordRun.a[0]!⟩ 4 = lowRun at low lowLength
  have slot := quadraticRun_runLog 64 lowRun.b[0]!
    ⟨openingAtInstance folded lowRun.point, inputWeights claim, #[], #[], lowRun.value, lowRun.writer⟩
    (RunLog.empty low.tracks 2) 6
  have slices := quadraticRun_a_size 64 lowRun.b[0]!
    ⟨openingAtInstance folded lowRun.point, inputWeights claim, #[], #[], lowRun.value, lowRun.writer⟩
    6 (by decide) (openingAtInstance_size ..)
  have slotLength := (quadraticRun_lengths 64 lowRun.b[0]!
    ⟨openingAtInstance folded lowRun.point, inputWeights claim, #[], #[], lowRun.value, lowRun.writer⟩ 6).1
  generalize quadraticRun 64 lowRun.b[0]! ⟨openingAtInstance folded lowRun.point, inputWeights claim, #[], #[],
    lowRun.value, lowRun.writer⟩ 6 = slotRun at slot slices slotLength
  refine ⟨slot.tracks.writeAll _, ?_, ⟨wordLength, ?_, word.size, word.widths, ?_, ?_, slices⟩⟩
  · rw [Writer.log_writeAll, slot.log, low.log, Writer.log_write, word.log]
    rw [openingsLog, Array.toList_append, Array.toList_append, roundLog_append lowRun.messages.toList
      slotRun.messages.toList _ _ (by simp only [Array.length_toList, low.size])]
    simp only [List.append_assoc]
  · simp only [Array.size_append, lowLength, slotLength]; rfl
  · simp only [Array.size_append, low.size, slot.size]
  · intro m hm
    rw [Array.toList_append, List.mem_append] at hm
    exact hm.elim (low.widths m) (slot.widths m)

/-- The writer events of a native reduction after its instance point: the segment and lane
samples, the middle value, each layer's rounds, then the openings. -/
def reductionLog (result : Reduction) : List WriterEvent :=
  WriterEvent.sample result.segment :: result.lanes.toList.map WriterEvent.sample ++
    [.write result.middle] ++ (result.layers.toList.map layerLog).flatten ++ openingsLog result.openings

attribute [local irreducible] proveLayerM proveOpenings Writer.sampleMany outputWords dot prepareRmfeProducts

/-- The native prover appends its reduction's events to the log and preserves tracking. -/
theorem prove_log (writer : Writer) (w : SlicedWitness) (committed : Array UInt64)
    (batch output : Array W) {s : Transcript.State} (h : writer.Tracks s) {p : Nat}
    (hb : batch.size = p+4) :
    let result := prove writer w committed batch output
    result.writer.Tracks s ∧ result.writer.log.out = writer.log.out ++ reductionLog result ∧
      result.lanes.size = 5 ∧ (∀ layer ∈ result.layers.toList, LayerWidths p layer) ∧
      OpeningsWidths result.openings := by
  rw [prove_eq_fold]
  dsimp only [nativeSetup]
  have segment := Writer.sampleMany_log h 1
  have segmentSize := Writer.sampleMany_size writer 1
  generalize writer.sampleMany 1 = seg at segment segmentSize
  have lanes := Writer.sampleMany_log segment.1 5
  have laneSize := Writer.sampleMany_size seg.2 5
  generalize seg.2.sampleMany 5 = laneRun at lanes laneSize
  generalize dot _ _ = middle
  have setup := lanes.1.write middle
  have claimSize : (nativeInitialClaim batch output seg.1[0]! laneRun.1 middle).point.size = p+1 := by
    simp only [nativeInitialClaim, Array.size_push, Array.size_extract, hb]
    omega
  generalize nativeInitialClaim _ _ _ _ _ = claim at claimSize
  have layers := foldl_preserves (P := fun state : NativeLayerState =>
      state.2.1.Tracks s ∧ state.2.1.log.out = (laneRun.2.write middle).log.out ++
        (state.2.2.toList.map layerLog).flatten ∧ (∀ layer ∈ state.2.2.toList, LayerWidths p layer) ∧
        state.1.point.size = p+1)
    (nativeLayerStateStep w prepareRmfeProducts) (List.range 12) (claim, laneRun.2.write middle, #[])
    ⟨setup, by simp only [List.map_nil, List.flatten_nil, List.append_nil],
      by simp only [List.not_mem_nil, false_implies, implies_true], claimSize⟩ (by
      intro state d hs
      have step := layerFromRuns_log state.2.1 w d state.1 prepareRmfeProducts hs.1 hs.2.2.2
      dsimp only [nativeLayerStateStep]
      rw [show proveLayerM (M := Id) (fun _ _ => pure ()) state.2.1 w d state.1 prepareRmfeProducts =
        layerFromRuns state.2.1 w d state.1 prepareRmfeProducts from proveLayerM_eq_runs ..]
      refine ⟨step.1, ?_, ?_, step.2.2.2⟩
      · rw [step.2.1, hs.2.1, Array.toList_push, List.map_append, List.flatten_append,
          List.map_singleton, List.flatten_singleton, List.append_assoc]
      · intro layer hl
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at hl
        rcases hl with hl | hl
        · exact hs.2.2.1 layer hl
        · rw [hl]; exact step.2.2.1)
  generalize (List.range 12).foldl _ _ = final at layers
  have openings := proveOpenings_log final.2.1 committed (2^w.nLog)
    (outputWords committed (2^w.nLog) batch) (wordOpeningWeights seg.1[0]! laneRun.1) middle final.1 layers.1
  refine ⟨openings.1, ?_, laneSize, layers.2.2.1, openings.2.2⟩
  rw [openings.2.1, layers.2.1, Writer.log_write, lanes.2, segment.2]
  have one : seg.1.toList = [seg.1[0]!] := by
    apply List.ext_getElem (by simp only [Array.length_toList, segmentSize, List.length_singleton])
    intro i hi _
    have : i = 0 := by simp only [Array.length_toList, segmentSize] at hi; omega
    subst this
    simp only [Array.getElem_toList, List.getElem_singleton]
    exact (getElem!_pos seg.1 0 (by rw [segmentSize]; decide)).symm
  simp only [reductionLog, one, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
    List.nil_append]

end CompStark.Keccak.GkrProver
