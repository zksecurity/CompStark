/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.WriterLog
public import Mathlib.Data.List.FinRange

/-! The native writer's log along the GKR's wire schedule: each message step writes its entry and
each challenge step samples it (`historyLog`). After the instance point, the native prover's log is
the schedule's log of its transcript's messages (`reductionLog_eq_historyLog`), so a tracking
writer draws every challenge of its transcript from the duplex
(`prove_drawn`). -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak CompStark.Keccak.Gkr CompStark.BinaryFields BF64

/-- The writer events of one wire step's entry: a message's writes, or a challenge's sample. -/
def entryLog : WireStep → List W → List WriterEvent
  | .message _, entry => entry.map WriterEvent.write
  | .challenge _, entry => [WriterEvent.sample (entry.getD 0 0)]

/-- The writer events of a history along a schedule. -/
def historyLog (steps : List WireStep) (history : List (List W)) : List WriterEvent :=
  (List.zipWith entryLog steps history).flatten

/-- A schedule, a history of the same length, and the writer events of the history along it. -/
def Matches (steps : List WireStep) (history : List (List W)) (log : List WriterEvent) : Prop :=
  steps.length = history.length ∧ historyLog steps history = log

/-- Matching schedules concatenate. -/
theorem Matches.append {a b : List WireStep} {ha hb : List (List W)} {la lb : List WriterEvent}
    (h₁ : Matches a ha la) (h₂ : Matches b hb lb) : Matches (a ++ b) (ha ++ hb) (la ++ lb) := by
  refine ⟨by simp only [List.length_append, h₁.1, h₂.1], ?_⟩
  rw [historyLog, List.zipWith_append h₁.1, List.flatten_append]
  exact congrArg₂ (· ++ ·) h₁.2 h₂.2

/-- Matching blocks concatenate along a list. -/
theorem Matches.flatMap {ι : Type} (l : List ι) {g : ι → List WireStep} {h : ι → List (List W)}
    {f : ι → List WriterEvent} (each : ∀ i ∈ l, Matches (g i) (h i) (f i)) :
    Matches (l.flatMap g) (l.flatMap h) (l.flatMap f) := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons i l ih =>
    simp only [List.flatMap_cons]
    exact (each i (List.mem_cons_self ..)).append (ih fun j hj => each j (List.mem_cons_of_mem _ hj))

/-- Matching single steps concatenate along a list. -/
theorem Matches.map {ι : Type} (l : List ι) {g : ι → WireStep} {h : ι → List W} {f : ι → WriterEvent}
    (each : ∀ i ∈ l, Matches [g i] [h i] [f i]) : Matches (l.map g) (l.map h) (l.map f) := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons i l ih =>
    exact (each i (List.mem_cons_self ..)).append (ih fun j hj => each j (List.mem_cons_of_mem _ hj))

/-- A message step writes its entry. -/
theorem Matches.message (n : Nat) (entry : List W) : Matches [.message n] [entry] (entry.map WriterEvent.write) :=
  ⟨rfl, by simp only [historyLog, List.zipWith_cons_cons, List.zipWith_nil_left, List.flatten_cons,
    List.flatten_nil, List.append_nil, entryLog]⟩

/-- A challenge step samples its entry. -/
theorem Matches.challenge (kind : Challenge) (r : W) : Matches [.challenge kind] [[r]] [WriterEvent.sample r] :=
  ⟨rfl, rfl⟩

/-- Natural ranges are the values of their finite ranges. -/
theorem range_eq_map_finRange (n : Nat) : List.range n = (List.finRange n).map Fin.val := by
  apply List.ext_getElem (by simp only [List.length_range, List.length_map, List.length_finRange])
  intro i _ _
  simp only [List.getElem_range, List.getElem_map, List.getElem_finRange, Fin.val_cast]

/-- A total-indexed array of known size is its list. -/
theorem ofFn_getElem! {α : Type} [Inhabited α] (a : Array α) {n : Nat} (h : a.size = n) :
    List.ofFn (fun i : Fin n => a[i.val]!) = a.toList := by
  apply List.ext_getElem (by simp only [List.length_ofFn, Array.length_toList, h])
  intro i hi _
  simp only [List.getElem_ofFn, Array.getElem_toList]
  exact getElem!_pos a i (by rw [h]; simpa only [List.length_ofFn] using hi)

/-- Rounds of a run of `n` rounds, indexed. -/
theorem roundLog_finRange (ms : Array (Array W)) (ps : Array W) {n : Nat} (hm : ms.size = n)
    (hp : ps.size = n) :
    roundLog ms.toList ps.toList = (List.finRange n).flatMap fun i =>
      ms[i.val]!.toList.map WriterEvent.write ++ [WriterEvent.sample ps[i.val]!] := by
  rw [roundLog, List.flatMap_def]
  congr 1
  apply List.ext_getElem (by simp only [List.length_zipWith, Array.length_toList, hm, hp, Nat.min_self,
    List.length_map, List.length_finRange])
  intro i hi _
  simp only [List.length_zipWith, Array.length_toList, hm, hp, Nat.min_self] at hi
  simp only [List.getElem_zipWith, Array.getElem_toList, List.getElem_map, List.getElem_finRange,
    Fin.val_cast]
  rw [getElem!_pos ms i (by omega), getElem!_pos ps i (by omega)]

/-- Sumcheck rounds whose entries are a native run's messages and points write and sample them. -/
theorem Matches.rounds {n d : Nat} (kind : Nat → Challenge) (polys : Fin n → Sumcheck.CompressedMessage E d)
    (point : Fin n → E) (ms : Array (Array W)) (ps : Array W) (hm : ms.size = n) (hp : ps.size = n)
    (messages : ∀ i : Fin n, (List.ofFn (messageVector (polys i))).map WordExt3.ofField = ms[i.val]!.toList)
    (points : ∀ i : Fin n, WordExt3.ofField (point i) = ps[i.val]!) :
    Matches (roundSteps n d kind) ((roundMessages polys point).map (List.map WordExt3.ofField))
      (roundLog ms.toList ps.toList) := by
  rw [roundLog_finRange ms ps hm hp, roundSteps, range_eq_map_finRange, List.flatMap_map, roundMessages,
    List.ofFn_eq_map, ← List.flatMap_def, List.map_flatMap]
  refine Matches.flatMap _ fun i _ => ?_
  simp only [List.map_cons, List.map_nil, messages i, points i]
  exact (Matches.message _ _).append (Matches.challenge _ _)

/-- An array of two elements is its two reads. -/
theorem toList_two (m : Array W) (h : m.size = 2) : m.toList = [m[0]!, m[1]!] := by
  rw [← ofFn_getElem! m h]
  rfl

/-- An array of three elements is its three reads. -/
theorem toList_three (m : Array W) (h : m.size = 3) : m.toList = [m[0]!, m[1]!, m[2]!] := by
  rw [← ofFn_getElem! m h]
  rfl

/-- A member read of an array of arrays of one width has that width. -/
theorem width_get! (ms : Array (Array W)) (width : Nat) (widths : ∀ m ∈ ms.toList, m.size = width)
    (i : Nat) (hi : i < ms.size) : ms[i]!.size = width := by
  rw [getElem!_pos ms i hi]
  exact widths _ (Array.getElem_mem_toList hi)

/-- A two-scalar native message is its specification message's wire entries. -/
theorem linear_entries (m : Array W) (h : m.size = 2) :
    (List.ofFn (messageVector ((m[0]!.toField, fun _ => m[1]!.toField) :
      Sumcheck.CompressedMessage E 1))).map WordExt3.ofField = m.toList := by
  rw [toList_two m h]
  simp only [List.ofFn_succ, List.ofFn_zero, messageVector, Fin.cons_zero, Fin.cons_succ, List.map_cons,
    List.map_nil, WordExt3.ofField_toField]

/-- A three-scalar native message is its specification message's wire entries. -/
theorem quadratic_entries (m : Array W) (h : m.size = 3) :
    (List.ofFn (messageVector ((m[0]!.toField, fun k => m[k.val+1]!.toField) :
      Sumcheck.CompressedMessage E 2))).map WordExt3.ofField = m.toList := by
  rw [toList_three m h]
  simp only [List.ofFn_succ, List.ofFn_zero, messageVector, Fin.cons_zero, Fin.cons_succ, List.map_cons,
    List.map_nil, WordExt3.ofField_toField, Fin.val_zero, Fin.val_succ]

/-- A converted array of known size is its list. -/
theorem ofFn_toField (a : Array W) {n : Nat} (h : a.size = n) :
    (List.ofFn fun i : Fin n => a[i.val]!.toField).map WordExt3.ofField = a.toList := by
  rw [List.map_ofFn]
  simp only [Function.comp_def, WordExt3.ofField_toField]
  exact ofFn_getElem! a h

/-- A native layer's log is its specification layer's wire entries along the layer schedule. -/
theorem layer_matches {p : Nat} (layer : Layer) (widths : LayerWidths p layer) (d : Nat) :
    Matches (layerSteps p d) ((layerMessages (layer.toProtocol p)).map (List.map WordExt3.ofField))
      (layerLog layer) := by
  have product := (Matches.message 47 layer.product.toList).append (Matches.challenge (.productPoint d) layer.s)
  have pack := Matches.rounds (.packSegment d) (layer.toProtocol p).packPolys (layer.toProtocol p).packPoint
    layer.packMessages layer.packPoint (widths.pack.trans widths.packCount) widths.packCount
    (fun i => linear_entries _ (width_get! _ 2 widths.packWidths i (by
      rw [widths.pack, widths.packCount]; exact i.isLt)))
    (fun _ => WordExt3.ofField_toField _)
  have position := Matches.rounds (.position d) (layer.toProtocol p).positionPolys
    (layer.toProtocol p).positionPoint layer.positionMessages layer.positionPoint
    (widths.position.trans widths.positionCount) widths.positionCount
    (fun i => quadratic_entries _ (width_get! _ 3 widths.positionWidths i (by
      rw [widths.position, widths.positionCount]; exact i.isLt)))
    (fun _ => WordExt3.ofField_toField _)
  have last := (Matches.message 3 layer.evaluations.toList).append (Matches.challenge (.beta d) layer.beta)
  have all := ((product.append pack).append position).append last
  have log : layerLog layer = layer.product.toList.map WriterEvent.write ++ [WriterEvent.sample layer.s] ++
      roundLog layer.packMessages.toList layer.packPoint.toList ++
      roundLog layer.positionMessages.toList layer.positionPoint.toList ++
      (layer.evaluations.toList.map WriterEvent.write ++ [WriterEvent.sample layer.beta]) := by
    simp only [layerLog, roundLog, List.zipWith_cons_cons, List.zipWith_nil_left, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.append_assoc]
  have e1 : (List.ofFn (layer.toProtocol p).product).map WordExt3.ofField = layer.product.toList :=
    ofFn_toField _ widths.product
  have e2 : WordExt3.ofField (layer.toProtocol p).point = layer.s := WordExt3.ofField_toField _
  have e3 : (List.ofFn (layer.toProtocol p).evaluations).map WordExt3.ofField = layer.evaluations.toList :=
    ofFn_toField _ widths.evaluations
  have e4 : WordExt3.ofField (layer.toProtocol p).beta = layer.beta := WordExt3.ofField_toField _
  rw [log, layerSteps, layerMessages]
  simp only [List.map_append, List.map_cons, List.map_nil, e1, e2, e3, e4]
  simpa only [List.cons_append, List.nil_append, List.append_assoc] using all

/-- An array of known size, read with in-bounds proofs. -/
theorem toList_ofFn {α : Type} (a : Array α) {n : Nat} (h : a.size = n) :
    a.toList = List.ofFn fun i : Fin n => a[i.val]'(h ▸ i.isLt) := by
  apply List.ext_getElem (by simp only [List.length_ofFn, Array.length_toList, h])
  intro i _ _
  simp only [List.getElem_ofFn, Array.getElem_toList]

/-- A schedule and history of singleton challenges sample their values. -/
theorem Matches.challenges {n : Nat} (kind : Nat → Challenge) (values : Fin n → W) :
    Matches ((List.range n).map fun i => .challenge (kind i)) (List.ofFn fun i => [values i])
      ((List.ofFn values).map WriterEvent.sample) := by
  rw [range_eq_map_finRange, List.map_map, List.ofFn_eq_map, List.ofFn_eq_map, List.map_map]
  exact Matches.map _ fun _ _ => Matches.challenge _ _

/-- The input sumcheck's low-instance and slot rounds form one ten-round schedule. -/
theorem inputSteps : roundSteps 4 1 .inputLow ++ roundSteps 6 1 .inputSlot =
    roundSteps 10 1 (fun i => if i < 4 then .inputLow i else .inputSlot (i - 4)) := rfl

/-- After its instance point, a native reduction's log is its transcript's messages along the GKR
schedule. -/
theorem reduction_matches {p : Nat} (result : Reduction) (height : result.layers.size = 12)
    (lanes : result.lanes.size = 5) (layers : ∀ layer ∈ result.layers.toList, LayerWidths p layer)
    (openings : OpeningsWidths result.openings) :
    Matches ((steps p).drop (p+4))
      (((transcriptMessages (result.toProtocol p height)).drop (p+4)).map (List.map WordExt3.ofField))
      (reductionLog result) := by
  set t := result.toProtocol p height
  have hs : (steps p).drop (p+4) = [.challenge .segment] ++ ((List.range 5).map fun i => .challenge (.lane i)) ++
      [.message 1] ++ (List.range 12).flatMap (layerSteps p) ++ roundSteps 6 1 .outputSlot ++ [.message 1] ++
      (roundSteps 4 1 .inputLow ++ roundSteps 6 1 .inputSlot) ++ [.message 64] := by
    simp only [steps, List.append_assoc]
    rw [List.drop_left' (by simp only [List.length_map, List.length_range])]
  have hm : (transcriptMessages t).drop (p+4) = [[t.segment]] ++ (List.ofFn fun i => [t.lanePoint i]) ++
      [[t.middleValue]] ++ (List.ofFn fun d => layerMessages (t.layers d)).flatten ++
      roundMessages t.openings.outputPolys t.openings.outputPoint ++ [[t.openings.outputValue]] ++
      roundMessages t.openings.inputPolys t.openings.inputPoint ++ [List.ofFn t.openings.slices] := by
    simp only [transcriptMessages, List.append_assoc]
    rw [List.drop_left' (by simp only [List.length_ofFn])]
  rw [hs, hm, inputSteps]
  simp only [List.map_append, List.map_cons, List.map_nil]
  have segment := Matches.challenge .segment result.segment
  have lanePoints := Matches.challenges .lane fun i : Fin 5 => result.lanes[i.val]!
  have middle := Matches.message 1 [result.middle]
  have layerBlock : Matches ((List.range 12).flatMap (layerSteps p))
      ((List.ofFn fun d => layerMessages (t.layers d)).flatten.map (List.map WordExt3.ofField))
      ((List.finRange 12).flatMap fun d => layerLog (result.layers[d.val]'(by rw [height]; exact d.isLt))) := by
    rw [range_eq_map_finRange, List.flatMap_map, List.ofFn_eq_map, ← List.flatMap_def, List.map_flatMap]
    exact Matches.flatMap _ fun d _ => layer_matches _ (layers _ (Array.getElem_mem_toList _)) d.val
  have output := Matches.rounds .outputSlot t.openings.outputPolys t.openings.outputPoint
    result.openings.outputMessages result.openings.outputPoint (openings.output.trans openings.outputCount)
    openings.outputCount
    (fun i => linear_entries _ (width_get! _ 2 openings.outputWidths i (by
      rw [openings.output, openings.outputCount]; exact i.isLt)))
    (fun _ => WordExt3.ofField_toField _)
  have outputValue := Matches.message 1 [result.openings.outputValue]
  have input := Matches.rounds (fun i => if i < 4 then .inputLow i else .inputSlot (i - 4))
    t.openings.inputPolys t.openings.inputPoint
    result.openings.inputMessages result.openings.inputPoint (openings.input.trans openings.inputCount)
    openings.inputCount
    (fun i => linear_entries _ (width_get! _ 2 openings.inputWidths i (by
      rw [openings.input, openings.inputCount]; exact i.isLt)))
    (fun _ => WordExt3.ofField_toField _)
  have slices := Matches.message 64 result.openings.slices.toList
  have all := (((((((segment.append lanePoints).append middle).append layerBlock).append output).append
    outputValue).append input).append slices)
  have e1 : (List.ofFn fun i : Fin 5 => [t.lanePoint i]).map (List.map WordExt3.ofField) =
      List.ofFn fun i : Fin 5 => [result.lanes[i.val]!] := by
    simp only [List.map_ofFn, Function.comp_def, List.map_cons, List.map_nil, t, Reduction.toProtocol,
      WordExt3.ofField_toField]
  have e2 : (List.ofFn t.openings.slices).map WordExt3.ofField = result.openings.slices.toList :=
    ofFn_toField _ openings.slices
  have e3 : WordExt3.ofField t.segment = result.segment := WordExt3.ofField_toField _
  have e4 : WordExt3.ofField t.middleValue = result.middle := WordExt3.ofField_toField _
  have e5 : WordExt3.ofField t.openings.outputValue = result.openings.outputValue := WordExt3.ofField_toField _
  rw [e1, e2, e3, e4, e5]
  have log : reductionLog result = [WriterEvent.sample result.segment] ++
      (List.ofFn fun i : Fin 5 => result.lanes[i.val]!).map WriterEvent.sample ++
      [result.middle].map WriterEvent.write ++
      ((List.finRange 12).flatMap fun d => layerLog (result.layers[d.val]'(by rw [height]; exact d.isLt))) ++
      roundLog result.openings.outputMessages.toList result.openings.outputPoint.toList ++
      [result.openings.outputValue].map WriterEvent.write ++
      roundLog result.openings.inputMessages.toList result.openings.inputPoint.toList ++
      result.openings.slices.toList.map WriterEvent.write := by
    rw [reductionLog, openingsLog, ofFn_getElem! result.lanes lanes, toList_ofFn result.layers height,
      List.ofFn_eq_map, List.map_map, ← List.flatMap_def]
    simp only [List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append,
      Function.comp_def]
  rw [log]
  exact all

/-- A tracking writer draws every challenge of the native prover's transcript from the duplex: the
log the native prover appends is its transcript's messages along the GKR schedule. -/
theorem prove_drawn (writer : Writer) (w : SlicedWitness) (committed : Array UInt64)
    (batch output : Array W) {s : Transcript.State} (h : writer.Tracks s) {p : Nat}
    (hb : batch.size = p+4) :
    let result := prove writer w committed batch output
    Drawn (Transcript.replay s (writer.log.out.map WriterEvent.event))
      (historyLog ((steps p).drop (p+4))
        (((transcriptMessages (result.toProtocol p (prove_layers_size ..))).drop (p+4)).map
          (List.map WordExt3.ofField))) := by
  have log := prove_log writer w committed batch output h hb
  dsimp only at log ⊢
  rw [(reduction_matches _ _ log.2.2.1 log.2.2.2.1 log.2.2.2.2).2]
  have drawn := log.1.2
  rw [log.2.1, drawn_append] at drawn
  exact drawn.2

end CompStark.Keccak.GkrProver
