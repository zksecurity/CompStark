/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Composed.Keccak.Transport


/-! Exact decoding of the fixed-width Keccak wire schedule. -/

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Tables.Composed

open CompStark.Keccak.Gkr

/-- An encoding realizes every history with its prescribed message widths. -/
def CompleteEncoding {F A : Type} (widths : List ℕ) (encode : A → List (List F)) : Prop :=
  ∀ history, history.map List.length = widths → ∃ value, encode value = history

/-- A fixed-width vector realizes every single message of that width. -/
theorem complete_vectorMessage (F : Type) (n : ℕ) :
    CompleteEncoding [n] (fun vector : Fin n → F => [List.ofFn vector]) := by
  intro history shape
  cases history with
  | nil => cases shape
  | cons message tail =>
      have lengths := List.cons.inj shape
      have empty : tail = [] := List.map_eq_nil_iff.mp lengths.2
      subst tail
      have length : message.length = n := lengths.1
      subst n
      exact ⟨fun i => message[i], congrArg (fun m => [m]) (List.ofFn_getElem (xs := message))⟩

/-- A scalar message realizes every singleton wire. -/
theorem complete_scalarMessage (F : Type) :
    CompleteEncoding [1] (fun scalar : F => [[scalar]]) := by
  intro history shape
  obtain ⟨vector, rfl⟩ := complete_vectorMessage F 1 history shape
  exact ⟨vector 0, rfl⟩

/-- Concatenating complete encodings realizes the concatenated message shape. -/
theorem complete_append {F A B : Type} {left right : List ℕ}
    {encodeLeft : A → List (List F)} {encodeRight : B → List (List F)}
    (hl : CompleteEncoding left encodeLeft) (hr : CompleteEncoding right encodeRight) :
    CompleteEncoding (left ++ right) (fun pair : A × B => encodeLeft pair.1 ++ encodeRight pair.2) := by
  intro history shape
  have hleft : (history.take left.length).map List.length = left := by
    rw [List.map_take, shape, List.take_left]
  have hright : (history.drop left.length).map List.length = right := by
    rw [List.map_drop, shape, List.drop_left]
  obtain ⟨a, ha⟩ := hl _ hleft
  obtain ⟨b, hb⟩ := hr _ hright
  exact ⟨(a, b), by change encodeLeft a ++ encodeRight b = history; rw [ha, hb, List.take_append_drop]⟩

/-- Repeating a complete block realizes every history of equally shaped blocks. -/
theorem complete_repeat {F A : Type} {widths : List ℕ} {encode : A → List (List F)}
    (complete : CompleteEncoding widths encode) (n : ℕ) :
    CompleteEncoding (List.replicate n widths).flatten
      (fun values : Fin n → A => (List.ofFn fun i => encode (values i)).flatten) := by
  induction n with
  | zero =>
      intro history shape
      have empty : history = [] := List.map_eq_nil_iff.mp shape
      exact ⟨Fin.elim0, empty.symm⟩
  | succ n ih =>
      intro history shape
      obtain ⟨⟨head, tail⟩, equal⟩ := complete_append complete ih history shape
      refine ⟨Fin.cons head tail, ?_⟩
      simpa only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.flatten_cons] using equal

/-- The wire shape of one transmitted sumcheck block. -/
def roundWidths (n degree : ℕ) : List ℕ := (List.replicate n [degree + 1, 1]).flatten

/-- Transmitted sumcheck messages and challenges realize exactly their fixed wire shape. -/
theorem complete_roundMessages (F : Type) (n degree : ℕ) :
    CompleteEncoding (roundWidths n degree)
      (fun data : (Fin n → Sumcheck.CompressedMessage F degree) × (Fin n → F) =>
        roundMessages data.1 data.2) := by
  intro history shape
  obtain ⟨data, equal⟩ := complete_repeat
    (complete_append (complete_vectorMessage F (degree + 1)) (complete_scalarMessage F)) n history shape
  refine ⟨(fun i => vectorMessage (data i).1, fun i => (data i).2), ?_⟩
  simpa only [roundMessages, messageVector_vectorMessage, List.singleton_append] using equal

/-- The fixed shape of a layer's product, cubic rounds, shifted values and beta. -/
def layerWidths (p : ℕ) : List ℕ :=
  [47, 1] ++ roundWidths (p + 1) 1 ++ roundWidths 11 2 ++ [3, 1]

/-- Every history with a layer's wire shape has a typed layer transcript. -/
theorem complete_layerMessages (F : Type) (p : ℕ) :
    CompleteEncoding (layerWidths p) (@layerMessages F p) := by
  intro history shape
  obtain ⟨⟨⟨⟨⟨product, point⟩, pack⟩, position⟩, ⟨evaluations, beta⟩⟩, equal⟩ :=
    complete_append
      (complete_append
        (complete_append
          (complete_append (complete_vectorMessage F 47) (complete_scalarMessage F))
          (complete_roundMessages F (p + 1) 1))
        (complete_roundMessages F 11 2))
      (complete_append (complete_vectorMessage F 3) (complete_scalarMessage F)) history shape
  exact ⟨⟨product, point, pack.1, pack.2, position.1, position.2, evaluations, beta⟩, equal⟩

/-- Flattening singleton blocks retains their coordinate order. -/
theorem flatten_singleton_ofFn {F : Type} {n : ℕ} (values : Fin n → F) :
    (List.ofFn fun i => [[values i]]).flatten = List.ofFn fun i => [values i] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.ofFn_succ, List.flatten_cons, List.singleton_append, ih]

/-- The complete transcript's fixed sequence of message widths. -/
def transcriptWidths (p : ℕ) : List ℕ :=
  (List.replicate (p + 4) [1]).flatten ++ [1] ++
    (List.replicate 5 [1]).flatten ++ [1] ++
    (List.replicate 12 (layerWidths p)).flatten ++
    roundWidths 6 1 ++ [1] ++ roundWidths 10 1 ++ [64]

/-- Every correctly shaped complete history has a typed transcript with precisely those messages. -/
theorem complete_transcriptMessages (F : Type) (p : ℕ) :
    CompleteEncoding (transcriptWidths p) (@transcriptMessages F p) := by
  intro history shape
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨instances, segment⟩, lanes⟩, middle⟩, layers⟩, output⟩, value⟩, input⟩, slices⟩, equal⟩ :=
    complete_append
      (complete_append
        (complete_append
          (complete_append
            (complete_append
              (complete_append
                (complete_append
                  (complete_append (complete_repeat (complete_scalarMessage F) (p + 4))
                    (complete_scalarMessage F))
                  (complete_repeat (complete_scalarMessage F) 5))
                (complete_scalarMessage F))
              (complete_repeat (complete_layerMessages F p) 12))
            (complete_roundMessages F 6 1))
          (complete_scalarMessage F))
        (complete_roundMessages F 10 1))
      (complete_vectorMessage F 64) history shape
  refine ⟨⟨instances, segment, lanes, middle, layers,
    ⟨output.1, output.2, value, input.1, input.2, slices⟩⟩, ?_⟩
  simpa only [transcriptMessages, flatten_singleton_ofFn] using equal

/-- Number of field elements in a public wire move. -/
def wireWidth : WireStep → ℕ
  | .message n => n
  | .challenge _ => 1

/-- Sumcheck tags leave the coefficient/challenge message widths unchanged. -/
theorem roundSteps_widths (n degree : ℕ) (kind : ℕ → Challenge) :
    (roundSteps n degree kind).map wireWidth = roundWidths n degree := by
  simp only [roundSteps, roundWidths, List.map_cons, List.map_nil, wireWidth,
    List.flatMap_def, List.map_flatten, List.map_map, Function.comp_def, List.map_const', List.length_range]

/-- Every layer's wire moves have the same typed transcript shape. -/
theorem layerSteps_widths (p d : ℕ) : (layerSteps p d).map wireWidth = layerWidths p := by
  simp only [layerSteps, layerWidths, List.map_append, List.map_cons, List.map_nil,
    wireWidth, roundSteps_widths]

/-- The complete Keccak schedule has precisely the typed transcript's message widths. -/
theorem steps_widths (p : ℕ) : (steps p).map wireWidth = transcriptWidths p := by
  simp only [steps, transcriptWidths, List.map_append, List.map_map, Function.comp_def,
    List.map_cons, List.map_nil, wireWidth, List.map_const', List.length_range,
    layerSteps_widths, List.flatMap_def, List.map_flatten, List.map_map, Function.comp_def, roundSteps_widths, layerSteps_widths, List.map_const', List.length_range]
  simp only [roundWidths, show 10 = 4 + 6 from rfl, List.replicate_add, List.flatten_append, List.flatten_replicate_singleton,
    List.append_assoc]

/-- A typed execution path always has its schedule's exact field-message widths. -/
theorem pathMessages_widths {F : Type} (steps : List WireStep)
    (path : (wireTree F steps).ExecutionPath) :
    (pathMessages steps path).map List.length = steps.map wireWidth := by
  induction steps with
  | nil => rfl
  | cons step rest ih =>
      cases step with
      | message n =>
          change (List.ofFn (show Fin n → F from path.1)).length :: _ = n :: _
          rw [List.length_ofFn]
          exact congrArg (List.cons n) (ih path.2)
      | challenge kind => exact congrArg (List.cons 1) (ih path.2)

/-- Read an actual coefficient/scalar position in a fixed-width GKR wire encoding. Shape and round-trip laws identify these total reads on typed paths. -/
def wireValue {E : Type} [Zero E] (history : List (List E)) (message coordinate : ℕ) : E :=
  (history.getD message []).getD coordinate 0

/-- Decode the scalar coordinates of a complete fixed-width wire history. -/
def decodeTranscript {E : Type} [Zero E] (packs : ℕ) (history : List (List E)) :
    Transcript E packs :=
  let get := wireValue history
  let opening := packs + 11 + 12 * (2 * packs + 28)
  { instancePoint := fun i => get i.val 0
    segment := get (packs + 4) 0
    lanePoint := fun i => get (packs + 5 + i.val) 0
    middleValue := get (packs + 10) 0
    layers := fun d =>
      let offset := packs + 11 + (2 * packs + 28) * d.val
      { product := fun i => get offset i.val
        point := get (offset + 1) 0
        packPolys := fun i => vectorMessage fun j => get (offset + 2 + 2 * i.val) j.val
        packPoint := fun i => get (offset + 3 + 2 * i.val) 0
        positionPolys := fun i => vectorMessage fun j => get (offset + 2 * packs + 4 + 2 * i.val) j.val
        positionPoint := fun i => get (offset + 2 * packs + 5 + 2 * i.val) 0
        evaluations := fun i => get (offset + 2 * packs + 26) i.val
        beta := get (offset + 2 * packs + 27) 0 }
    openings := {
      outputPolys := fun i => vectorMessage fun j => get (opening + 2 * i.val) j.val
      outputPoint := fun i => get (opening + 2 * i.val + 1) 0
      outputValue := get (opening + 12) 0
      inputPolys := fun i => vectorMessage fun j => get (opening + 13 + 2 * i.val) j.val
      inputPoint := fun i => get (opening + 14 + 2 * i.val) 0
      slices := fun i => get (opening + 33) i.val } }

/-- Share indexed wire history across every scalar projection of a GKR transcript. -/
@[macro_inline] def cachedWireValues {E : Type} [Zero E] (history : List (List E)) : Nat → Nat → E :=
  let messages := history.toArray.map List.toArray
  fun message coordinate => ((messages[message]?).getD #[])[coordinate]?.getD 0

/-- Array-backed scalar reads preserve total list reads, including both zero defaults. -/
theorem cachedWireValues_eq {E : Type} [Zero E] (history : List (List E)) :
    cachedWireValues history = wireValue history := by
  funext message coordinate
  simp only [cachedWireValues, wireValue, Array.getElem?_map, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]
  cases history[message]? with
  | none => simp only [Option.map_none, Option.getD_none,
      Array.getElem?_empty, List.getElem?_nil]
  | some words => simp only [Option.map_some, Option.getD_some, List.getElem?_toArray]

/-- Decode with one array index shared by all points, polynomials and layer projections. -/
def decodeTranscriptFast {E : Type} [Zero E] (packs : ℕ) (history : List (List E)) :
    Transcript E packs :=
  let get := cachedWireValues history
  let opening := packs + 11 + 12 * (2 * packs + 28)
  { instancePoint := fun i => get i.val 0
    segment := get (packs + 4) 0
    lanePoint := fun i => get (packs + 5 + i.val) 0
    middleValue := get (packs + 10) 0
    layers := fun d =>
      let offset := packs + 11 + (2 * packs + 28) * d.val
      { product := fun i => get offset i.val
        point := get (offset + 1) 0
        packPolys := fun i => vectorMessage fun j => get (offset + 2 + 2 * i.val) j.val
        packPoint := fun i => get (offset + 3 + 2 * i.val) 0
        positionPolys := fun i => vectorMessage fun j => get (offset + 2 * packs + 4 + 2 * i.val) j.val
        positionPoint := fun i => get (offset + 2 * packs + 5 + 2 * i.val) 0
        evaluations := fun i => get (offset + 2 * packs + 26) i.val
        beta := get (offset + 2 * packs + 27) 0 }
    openings := {
      outputPolys := fun i => vectorMessage fun j => get (opening + 2 * i.val) j.val
      outputPoint := fun i => get (opening + 2 * i.val + 1) 0
      outputValue := get (opening + 12) 0
      inputPolys := fun i => vectorMessage fun j => get (opening + 13 + 2 * i.val) j.val
      inputPoint := fun i => get (opening + 14 + 2 * i.val) 0
      slices := fun i => get (opening + 33) i.val } }

/-- Cached transcript projections agree at every scalar and every layer. -/
@[csimp] theorem decodeTranscript_code : @decodeTranscript = @decodeTranscriptFast := by
  funext E inst packs history
  unfold decodeTranscriptFast
  rw [cachedWireValues_eq]
  rfl

/-- Reading an encoded vector returns its actual coordinate. -/
theorem wireValue_vector {F : Type} [Zero F] {history : List (List F)} {n message : ℕ}
    (vector : Fin n → F) (encoded : history[message]? = some (List.ofFn vector)) (i : Fin n) :
    wireValue history message i.val = vector i := by
  simp only [wireValue, List.getD_eq_getElem?_getD, encoded, Option.getD_some,
    List.getElem?_ofFn, i.isLt, dite_true, Fin.eta]

/-- Reading an encoded scalar returns that scalar. -/
theorem wireValue_scalar {F : Type} [Zero F] {history : List (List F)} {message : ℕ}
    (scalar : F) (encoded : history[message]? = some [scalar]) :
    wireValue history message 0 = scalar := by
  simp only [wireValue, List.getD_eq_getElem?_getD, encoded, Option.getD_some,
    List.getElem?_cons_zero]

/-- The final slice vector occupies the last wire after both opening sumchecks. -/
theorem transcriptMessages_get_slices {F : Type} [CommRing F] {p : ℕ}
    (t : Transcript F p) :
    (transcriptMessages t)[wordOffset p + 33]? = some (List.ofFn t.openings.slices) := by
  obtain ⟨pre, hp, equal⟩ := transcriptMessages_opening_blocks t
  rw [equal]
  have read := getElem?_middle_block
    (pre ++ roundMessages t.openings.outputPolys t.openings.outputPoint ++
      [[t.openings.outputValue]] ++ roundMessages t.openings.inputPolys t.openings.inputPoint)
    [List.ofFn t.openings.slices] [] (wordOffset p + 33) 0
    (by simp only [List.length_append, hp, roundMessages_length, List.length_cons, List.length_nil]) (by exact Nat.zero_lt_succ _)
  simpa only [List.append_nil, Nat.add_zero, List.getElem?_cons_zero] using read

/-- The three shifted layer values immediately precede beta. -/
theorem layerMessages_get_evaluations {F : Type} {p : ℕ} (t : LayerTranscript F p) :
    (layerMessages t)[2 * p + 26]? = some (List.ofFn t.evaluations) := by
  have read := getElem?_middle_block
    ([List.ofFn t.product, [t.point]] ++ roundMessages t.packPolys t.packPoint ++
      roundMessages t.positionPolys t.positionPoint)
    [List.ofFn t.evaluations] [[t.beta]] (2 * p + 26) 0
    (by simp only [List.length_append, roundMessages_length, List.length_cons, List.length_nil]; omega) (by exact Nat.zero_lt_succ _)
  simpa only [layerMessages, List.append_assoc, List.singleton_append, Nat.add_zero,
    List.getElem?_cons_zero] using read

/-- Equality of all wire fields determines a layer transcript. -/
theorem layerTranscript_ext {F : Type} {p : ℕ} {a b : LayerTranscript F p}
    (product : a.product = b.product) (point : a.point = b.point)
    (packPolys : a.packPolys = b.packPolys) (packPoint : a.packPoint = b.packPoint)
    (positionPolys : a.positionPolys = b.positionPolys) (positionPoint : a.positionPoint = b.positionPoint)
    (evaluations : a.evaluations = b.evaluations) (beta : a.beta = b.beta) : a = b := by
  cases a; cases b
  cases product; cases point; cases packPolys; cases packPoint
  cases positionPolys; cases positionPoint; cases evaluations; cases beta
  rfl

/-- Equality of the opening wire fields determines its transcript. -/
theorem openingTranscript_ext {F : Type} {a b : OpeningTranscript F}
    (outputPolys : a.outputPolys = b.outputPolys) (outputPoint : a.outputPoint = b.outputPoint)
    (outputValue : a.outputValue = b.outputValue) (inputPolys : a.inputPolys = b.inputPolys)
    (inputPoint : a.inputPoint = b.inputPoint) (slices : a.slices = b.slices) : a = b := by
  cases a; cases b
  cases outputPolys; cases outputPoint; cases outputValue; cases inputPolys; cases inputPoint; cases slices
  rfl

/-- Equality of the header, layers and openings determines the complete transcript. -/
theorem transcript_ext {F : Type} {p : ℕ} {a b : Transcript F p}
    (instances : a.instancePoint = b.instancePoint) (segment : a.segment = b.segment)
    (lanes : a.lanePoint = b.lanePoint) (middle : a.middleValue = b.middleValue)
    (layers : a.layers = b.layers) (openings : a.openings = b.openings) : a = b := by
  cases a; cases b
  cases instances; cases segment; cases lanes; cases middle; cases layers; cases openings
  rfl

/-- Each layer field is recovered from its exact arithmetic wire offset. -/
theorem decodeTranscript_layer {F : Type} [CommRing F] {p : ℕ}
    (t : Transcript F p) (d : Fin 12) :
    (decodeTranscript p (transcriptMessages t)).layers d = t.layers d := by
  have read (j : ℕ) (bounded : j < 2 * p + 28) := transcriptMessages_get_layer t d j bounded
  apply layerTranscript_ext
  · funext i
    apply wireValue_vector (t.layers d).product
    simpa only [layerOffset, Nat.add_zero] using
      (read 0 (by omega)).trans (layerMessages_get_product (t.layers d))
  · apply wireValue_scalar (t.layers d).point
    exact (read 1 (by omega)).trans (layerMessages_get_point (t.layers d))
  · funext i
    apply messageVector_injective
    funext j
    dsimp only [decodeTranscript]
    rw [messageVector_vectorMessage]
    apply wireValue_vector (messageVector ((t.layers d).packPolys i))
    simpa only [layerOffset, Nat.add_assoc] using
      (read (2 + 2 * i.val) (by omega)).trans
        ((layerMessages_get_pack (t.layers d) (2 * i.val) (by omega)).trans
          (roundMessages_get_polynomial _ _ i))
  · funext i
    apply wireValue_scalar ((t.layers d).packPoint i)
    convert (read (2 + (2 * i.val + 1)) (by omega)).trans
      ((layerMessages_get_pack (t.layers d) (2 * i.val + 1) (by omega)).trans
        (roundMessages_get_challenge _ _ i)) using 1
    congr 1
    dsimp only [layerOffset]
    omega
  · funext i
    apply messageVector_injective
    funext j
    dsimp only [decodeTranscript]
    rw [messageVector_vectorMessage]
    apply wireValue_vector (messageVector ((t.layers d).positionPolys i))
    simpa only [layerOffset, Nat.add_assoc] using
      (read ((2 * p + 4) + 2 * i.val) (by omega)).trans
        ((layerMessages_get_position (t.layers d) (2 * i.val) (by omega)).trans
          (roundMessages_get_polynomial _ _ i))
  · funext i
    apply wireValue_scalar ((t.layers d).positionPoint i)
    convert (read ((2 * p + 4) + (2 * i.val + 1)) (by omega)).trans
      ((layerMessages_get_position (t.layers d) (2 * i.val + 1) (by omega)).trans
        (roundMessages_get_challenge _ _ i)) using 1
    congr 1
    dsimp only [layerOffset]
    omega
  · funext i
    apply wireValue_vector (t.layers d).evaluations
    simpa only [layerOffset, Nat.add_assoc] using
      (read (2 * p + 26) (by omega)).trans (layerMessages_get_evaluations (t.layers d))
  · apply wireValue_scalar (t.layers d).beta
    simpa only [layerOffset, Nat.add_assoc] using
      (read (2 * p + 27) (by omega)).trans (layerMessages_get_beta (t.layers d))

/-- The two opening blocks and final slices decode to the exact sent fields. -/
theorem decodeTranscript_openings {F : Type} [CommRing F] {p : ℕ} (t : Transcript F p) :
    (decodeTranscript p (transcriptMessages t)).openings = t.openings := by
  apply openingTranscript_ext
  · funext i
    apply messageVector_injective
    funext j
    dsimp only [decodeTranscript]
    rw [messageVector_vectorMessage]
    apply wireValue_vector (messageVector (t.openings.outputPolys i))
    exact (transcriptMessages_get_word t (2 * i.val) (by omega)).trans
      (roundMessages_get_polynomial _ _ i)
  · funext i
    apply wireValue_scalar (t.openings.outputPoint i)
    simpa only [wordOffset, Nat.add_assoc] using
      (transcriptMessages_get_word t (2 * i.val + 1) (by omega)).trans
        (roundMessages_get_challenge _ _ i)
  · exact wireValue_scalar _ (transcriptMessages_get_wordValue t)
  · funext i
    apply messageVector_injective
    funext j
    dsimp only [decodeTranscript]
    rw [messageVector_vectorMessage]
    apply wireValue_vector (messageVector (t.openings.inputPolys i))
    simpa only [inputOffset, wordOffset, Nat.add_assoc] using
      (transcriptMessages_get_input t (2 * i.val) (by omega)).trans
        (roundMessages_get_polynomial _ _ i)
  · funext i
    apply wireValue_scalar (t.openings.inputPoint i)
    convert (transcriptMessages_get_input t (2 * i.val + 1) (by omega)).trans
      (roundMessages_get_challenge _ _ i) using 1
    congr 1
    dsimp only [inputOffset, wordOffset]
    omega
  · funext i
    exact wireValue_vector _ (transcriptMessages_get_slices t) i

/-- Decoding the wire encoding recovers every field of the typed transcript. -/
theorem decodeTranscript_encode {F : Type} [CommRing F] {p : ℕ} (t : Transcript F p) :
    decodeTranscript p (transcriptMessages t) = t := by
  apply transcript_ext
  · funext i
    change wireValue (transcriptMessages t) i.val 0 = t.instancePoint i
    simpa only [initialPoint, i.isLt, dite_true, Fin.eta] using wireValue_scalar _
      (transcriptMessages_get_initial t ⟨i.val, by omega⟩)
  · change wireValue (transcriptMessages t) (p + 4) 0 = t.segment
    simpa only [initialPoint_segment] using wireValue_scalar _
      (transcriptMessages_get_initial t ⟨p + 4, by omega⟩)
  · funext i
    change wireValue (transcriptMessages t) (p + 5 + i.val) 0 = t.lanePoint i
    simpa only [initialPoint_lane] using wireValue_scalar _
      (transcriptMessages_get_initial t ⟨p + 5 + i.val, by omega⟩)
  · exact wireValue_scalar _ (transcriptMessages_get_middle t)
  · exact funext (decodeTranscript_layer t)
  · exact decodeTranscript_openings t

/-- A correctly shaped history is recovered exactly by decoding and encoding. -/
theorem encode_decodeTranscript {F : Type} [CommRing F] {p : ℕ} (history : List (List F))
    (shape : history.map List.length = transcriptWidths p) :
    transcriptMessages (decodeTranscript p history) = history := by
  obtain ⟨t, rfl⟩ := complete_transcriptMessages F p history shape
  rw [decodeTranscript_encode]

/-- The supplied instance-coordinate prefix and remaining wire path have the complete transcript shape. -/
theorem instanceSuffix_widths {F : Type} {p : ℕ} (point : Fin (p + 4) → F)
    (path : (wireTree F ((steps p).drop (p + 4))).ExecutionPath) :
    ((List.ofFn fun i => [point i]) ++ pathMessages ((steps p).drop (p + 4)) path).map List.length =
      transcriptWidths p := by
  have initial : ((steps p).take (p + 4)).map wireWidth = List.replicate (p + 4) 1 := by
    unfold steps
    simp only [List.append_assoc]
    rw [List.take_left' (by simp only [List.length_map, List.length_range])]
    simp only [List.map_map, Function.comp_def, wireWidth, List.map_const', List.length_range]
  rw [List.map_append]
  have header : (List.ofFn fun i => [point i]).map List.length = List.replicate (p + 4) 1 := by
    simp only [List.map_ofFn, Function.comp_def, List.length_cons, List.length_nil, List.ofFn_const]
  rw [header, pathMessages_widths, ← initial, ← List.map_append, List.take_append_drop, steps_widths]

/-- An endpoint on an encoded transcript is exactly its verifier checks and final opening relation. -/
theorem endpointClaim_transcript {F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (x : F) (output : Fin (2 ^ (p + 4)) → Fin 25 → F) (q : Witness p) (t : Transcript F p) :
    endpointClaim x output (transcriptMessages t) q ↔ Accepts x output t ∧ TerminalRelation x q t := by
  constructor
  · rintro ⟨other, equal, accepted, terminal⟩
    have same := transcriptMessages_injective equal
    subst other
    exact ⟨accepted, terminal⟩
  · rintro ⟨accepted, terminal⟩
    exact ⟨t, rfl, accepted, terminal⟩

end CompStark.Tables.Composed
