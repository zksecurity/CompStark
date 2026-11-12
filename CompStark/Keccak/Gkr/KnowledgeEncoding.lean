/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.KnowledgePrefix
public import CompStark.Keccak.Gkr.ProtocolExecution

/-! # Transcript data fixed by an authored wire prefix -/

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
@[expose] public section
namespace CompStark.Keccak.Gkr

/-- Two completions of an authored prefix have identical messages at every authored index. -/
theorem authored_getElem_eq {α : Type} (history left right : List α)
    (hl : history <+: left) (hr : history <+: right) (i : Nat) (hi : i < history.length) :
    left[i]? = right[i]? := by
  obtain ⟨ls, hls⟩ := hl
  obtain ⟨rs, hrs⟩ := hr
  rw [← hls, ← hrs, List.getElem?_append_left hi, List.getElem?_append_left hi]

/-- An element of a known-length middle block retains its offset in a concatenated encoding. -/
theorem getElem?_middle_block {α : Type} (a b c : List α) (offset i : Nat)
    (ha : a.length = offset) (hi : i < b.length) :
    (a ++ b ++ c)[offset+i]? = b[i]? := by
  rw [List.append_assoc, List.getElem?_append_right (by omega), ha, Nat.add_sub_cancel_left,
    List.getElem?_append_left hi]

/-- Uniformly sized blocks can be read at their arithmetic wire offsets. -/
theorem getElem?_flatten_ofFn {α : Type} {n : Nat} (blocks : Fin n → List α)
    (width : Nat) (lengths : ∀ i, (blocks i).length = width) (i : Fin n)
    (j : Nat) (hj : j < width) :
    (List.ofFn blocks).flatten[width*i.val+j]? = (blocks i)[j]? := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa only [Fin.val_zero, Nat.mul_zero, Nat.zero_add] using
        (List.getElem?_append_left (l₂ := (List.ofFn fun i => blocks i.succ).flatten)
          (by rw [lengths]; exact hj))
    · rw [List.getElem?_append_right (by rw [lengths]; simp only [Fin.val_succ, Nat.mul_add, Nat.mul_one]; omega)]
      rw [lengths]
      have he : width*(k.val+1)+j-width = width*k.val+j := by simp only [Nat.mul_add, Nat.mul_one]; omega
      simp only [Fin.val_succ, he]
      exact ih (fun i => blocks i.succ) (fun i => lengths i.succ) k

/-- The coefficient message at a sumcheck round is fixed before its challenge. -/
theorem roundMessages_get_polynomial {E : Type} {n degree : Nat}
    (polys : Fin n → Sumcheck.CompressedMessage E degree) (point : Fin n → E) (i : Fin n) :
    (roundMessages polys point)[2*i.val]? = some (List.ofFn (messageVector (polys i))) := by
  simpa only [roundMessages, Nat.add_zero, List.getElem?_cons_zero] using
    getElem?_flatten_ofFn (fun j => [List.ofFn (messageVector (polys j)), [point j]]) 2 (fun _ => rfl) i 0 (by decide)

/-- The scalar at a sumcheck round occupies the wire immediately after its polynomial. -/
theorem roundMessages_get_challenge {E : Type} {n degree : Nat}
    (polys : Fin n → Sumcheck.CompressedMessage E degree) (point : Fin n → E) (i : Fin n) :
    (roundMessages polys point)[2*i.val+1]? = some [point i] := by
  exact getElem?_flatten_ofFn (fun j => [List.ofFn (messageVector (polys j)), [point j]]) 2 (fun _ => rfl) i 1 (by decide)

/-- A common sumcheck prefix fixes every coefficient vector that has already been sent. -/
theorem roundMessages_polynomial_fixed {E : Type} {n degree : Nat}
    (a b : Fin n → Sumcheck.CompressedMessage E degree) (r s : Fin n → E) (history : List (List E))
    (ha : history <+: roundMessages a r) (hb : history <+: roundMessages b s)
    (i : Fin n) (hi : 2*i.val < history.length) : a i = b i := by
  have h := authored_getElem_eq history _ _ ha hb (2*i.val) hi
  rw [roundMessages_get_polynomial, roundMessages_get_polynomial] at h
  exact messageVector_injective (List.ofFn_injective (Option.some.inj h))

/-- A common sumcheck prefix fixes every challenge that has already been sampled. -/
theorem roundMessages_challenge_fixed {E : Type} {n degree : Nat}
    (a b : Fin n → Sumcheck.CompressedMessage E degree) (r s : Fin n → E) (history : List (List E))
    (ha : history <+: roundMessages a r) (hb : history <+: roundMessages b s)
    (i : Fin n) (hi : 2*i.val+1 < history.length) : r i = s i := by
  have h := authored_getElem_eq history _ _ ha hb (2*i.val+1) hi
  rw [roundMessages_get_challenge, roundMessages_get_challenge] at h
  exact List.singleton_inj.mp (Option.some.inj h)

/-- The layer block begins after the initial coordinates, middle claim, and previous layers. -/
def layerOffset (p : Nat) (d : Fin 12) : Nat := p+11+(2*p+28)*d.val

/-- A transcript consists of its initial coordinates, middle value, layers, and openings. -/
theorem transcriptMessages_blocks {E : Type} [CommRing E] {p : Nat} (t : Transcript E p) :
    transcriptMessages t = coordinateMessages (initialPoint t) ++ [[t.middleValue]] ++
      sequenceMessages t.layers ++ openingMessages t.openings := by
  have h := completed_header_messages (initialPoint t) t.middleValue t.layers t.openings
  simpa only [header, initialPoint_instances, initialPoint_segment, initialPoint_lane] using h

/-- The initial coordinate at an authored index is the corresponding transcript scalar. -/
theorem transcriptMessages_get_initial {E : Type} [CommRing E] {p : Nat}
    (t : Transcript E p) (i : Fin (p+10)) :
    (transcriptMessages t)[i.val]? = some [initialPoint t i] := by
  rw [transcriptMessages_blocks, List.append_assoc, List.append_assoc,
    List.getElem?_append_left (by simp only [coordinateMessages, List.length_ofFn]; exact i.isLt)]
  simp only [coordinateMessages, List.getElem?_ofFn, i.isLt, dite_true, Fin.eta]

/-- The middle value is fixed before the first layer starts. -/
theorem transcriptMessages_get_middle {E : Type} [CommRing E] {p : Nat}
    (t : Transcript E p) : (transcriptMessages t)[p+10]? = some [t.middleValue] := by
  rw [transcriptMessages_blocks, List.append_assoc, List.append_assoc,
    List.getElem?_append_right (by simp only [coordinateMessages, List.length_ofFn]; exact le_rfl)]
  simp only [coordinateMessages, List.length_ofFn, Nat.sub_self, List.cons_append,
    List.getElem?_cons_zero]

/-- A layer's complete wire block has its fixed arithmetic offset in the transcript. -/
theorem transcriptMessages_get_layer {E : Type} [CommRing E] {p : Nat}
    (t : Transcript E p) (d : Fin 12) (j : Nat) (hj : j < 2*p+28) :
    (transcriptMessages t)[layerOffset p d+j]? = (layerMessages (t.layers d))[j]? := by
  have hlen : (sequenceMessages t.layers).length = 12*(2*p+28) := by
    simp only [sequenceMessages, List.length_flatten, List.map_ofFn, Function.comp_def,
      layerMessages_length, List.ofFn_const, List.sum_replicate, smul_eq_mul]
  have hp : (coordinateMessages (initialPoint t) ++ [[t.middleValue]]).length = p+11 := by
    simp only [List.length_append, coordinateMessages, List.length_ofFn, List.length_cons, List.length_nil]
  have hi : (2*p+28)*d.val+j < (sequenceMessages t.layers).length := by
    rw [hlen]
    nlinarith [d.isLt]
  have h := getElem?_middle_block (coordinateMessages (initialPoint t) ++ [[t.middleValue]])
    (sequenceMessages t.layers) (openingMessages t.openings) (p+11) ((2*p+28)*d.val+j) hp hi
  rw [← transcriptMessages_blocks] at h
  simp only [layerOffset, Nat.add_assoc] at h ⊢
  rw [h]
  exact getElem?_flatten_ofFn (fun d => layerMessages (t.layers d)) (2*p+28)
    (fun d => layerMessages_length (t.layers d)) d j hj

/-- The layer product coefficients are sent before the product evaluation challenge. -/
theorem layerMessages_get_product {E : Type} {p : Nat} (t : LayerTranscript E p) :
    (layerMessages t)[0]? = some (List.ofFn t.product) := by
  simp only [layerMessages, List.append_assoc, List.cons_append, List.getElem?_cons_zero]

/-- The layer product point follows its coefficient message. -/
theorem layerMessages_get_point {E : Type} {p : Nat} (t : LayerTranscript E p) :
    (layerMessages t)[1]? = some [t.point] := by
  simp only [layerMessages, List.append_assoc, List.cons_append, List.getElem?_cons_succ,
    List.getElem?_cons_zero]

/-- Every authored initial challenge is fixed across all compatible completions. -/
theorem prefix_initial_fixed {E : Type} [CommRing E] {p : Nat} (t u : Transcript E p)
    (history : List (List E)) (ht : history <+: transcriptMessages t)
    (hu : history <+: transcriptMessages u) (i : Fin (p+10)) (hi : i.val < history.length) :
    initialPoint t i = initialPoint u i := by
  have h := authored_getElem_eq history _ _ ht hu i.val hi
  rw [transcriptMessages_get_initial, transcriptMessages_get_initial] at h
  exact List.singleton_inj.mp (Option.some.inj h)

/-- The authored middle claim is fixed across all compatible completions. -/
theorem prefix_middle_fixed {E : Type} [CommRing E] {p : Nat} (t u : Transcript E p)
    (history : List (List E)) (ht : history <+: transcriptMessages t)
    (hu : history <+: transcriptMessages u) (hi : p+10 < history.length) : t.middleValue = u.middleValue := by
  have h := authored_getElem_eq history _ _ ht hu (p+10) hi
  rw [transcriptMessages_get_middle, transcriptMessages_get_middle] at h
  exact List.singleton_inj.mp (Option.some.inj h)

/-- A complete authored layer is fixed across all compatible completions. -/
theorem prefix_layer_fixed {E : Type} [CommRing E] {p : Nat} (t u : Transcript E p)
    (history : List (List E)) (ht : history <+: transcriptMessages t)
    (hu : history <+: transcriptMessages u) (d : Fin 12)
    (hi : layerOffset p d+(2*p+28) ≤ history.length) : t.layers d = u.layers d := by
  apply layerMessages_injective
  apply List.ext_getElem?
  intro j
  by_cases hj : j < 2*p+28
  · have h := authored_getElem_eq history _ _ ht hu (layerOffset p d+j) (by omega)
    simpa only [transcriptMessages_get_layer _ d j hj] using h
  · rw [List.getElem?_eq_none (by rw [layerMessages_length]; omega),
      List.getElem?_eq_none (by rw [layerMessages_length]; omega)]

/-- A complete authored header fixes its instance, segment, lane, and middle data. -/
theorem prefix_header_fixed {E : Type} [CommRing E] {p : Nat} (t u : Transcript E p)
    (history : List (List E)) (ht : history <+: transcriptMessages t)
    (hu : history <+: transcriptMessages u) (hi : p+11 ≤ history.length) :
    t.instancePoint = u.instancePoint ∧ t.segment = u.segment ∧
      t.lanePoint = u.lanePoint ∧ t.middleValue = u.middleValue := by
  have hp : initialPoint t = initialPoint u := by
    funext i
    exact prefix_initial_fixed t u history ht hu i (by omega)
  refine ⟨?_, ?_, ?_, prefix_middle_fixed t u history ht hu (by omega)⟩
  · have h := congrArg (fun r : Fin (p+10) → E => fun i : Fin (p+4) => r ⟨i.val, by omega⟩) hp
    simpa only [initialPoint_instances] using h
  · simpa only [initialPoint_segment] using congrFun hp ⟨p+4, by omega⟩
  · funext i
    simpa only [initialPoint_lane] using congrFun hp ⟨p+5+i.val, by omega⟩

/-- A complete authored header fixes the retained middle-state invariant. -/
theorem prefix_MiddleHolds_fixed {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (q : Witness p) (t u : Transcript E p)
    (history : List (List E)) (ht : history <+: transcriptMessages t)
    (hu : history <+: transcriptMessages u) (hi : p+11 ≤ history.length) :
    MiddleHolds x q t ↔ MiddleHolds x q u := by
  obtain ⟨hinst, hseg, hlane, hmid⟩ := prefix_header_fixed t u history ht hu hi
  simp only [MiddleHolds, middleWord, hinst, hseg, hlane, hmid]

/-- The header and complete previous layers fix the claim entering a layer. -/
theorem prefix_claimAt_fixed {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (t u : Transcript E p)
    (history : List (List E)) (ht : history <+: transcriptMessages t)
    (hu : history <+: transcriptMessages u) (d : Fin 12)
    (hi : layerOffset p d ≤ history.length) :
    claimAt x output t d.castSucc = claimAt x output u d.castSucc := by
  by_cases hd : d.val = 0
  · have hb : p+11 ≤ history.length := by dsimp only [layerOffset] at hi; omega
    obtain ⟨hinst, hseg, hlane, hmid⟩ := prefix_header_fixed t u history ht hu hb
    simp only [claimAt, Fin.val_castSucc, hd, dite_true, firstClaim, hinst, hseg, hlane, hmid]
  · let prev : Fin 12 := ⟨d.val-1, by omega⟩
    have he : (2*p+28)*(d.val-1)+(2*p+28) = (2*p+28)*d.val := by
      rw [← Nat.mul_succ]
      congr 1
      omega
    have hb : layerOffset p prev+(2*p+28) ≤ history.length := by
      dsimp only [layerOffset, prev] at *
      omega
    have hl := prefix_layer_fixed t u history ht hu prev hb
    simp only [claimAt, Fin.val_castSucc, hd, dite_false]
    exact congrArg nextClaim hl

/-- An authored product polynomial is fixed across all compatible completions. -/
theorem prefix_product_fixed {E : Type} [CommRing E] {p : Nat} (t u : Transcript E p)
    (history : List (List E)) (ht : history <+: transcriptMessages t)
    (hu : history <+: transcriptMessages u) (d : Fin 12)
    (hi : layerOffset p d < history.length) : (t.layers d).product = (u.layers d).product := by
  have h := authored_getElem_eq history _ _ ht hu (layerOffset p d+0) (by omega)
  rw [transcriptMessages_get_layer _ d 0 (by omega),
    transcriptMessages_get_layer _ d 0 (by omega), layerMessages_get_product, layerMessages_get_product] at h
  exact List.ofFn_injective (Option.some.inj h)

/-- The next scalar wire message is the freshly appended challenge in every completion. -/
theorem authored_next_scalar {E : Type} {p : Nat} (history : List (List E)) (r : E)
    (t : Transcript E p) (ht : history ++ [[r]] <+: transcriptMessages t) :
    (transcriptMessages t)[history.length]? = some [r] := by
  obtain ⟨tail, he⟩ := ht
  rw [← he, List.append_assoc, List.getElem?_append_right (by omega), Nat.sub_self]
  rfl

/-- All layer messages authored before the final beta challenge. -/
def layerBody {E : Type} {p : Nat} (t : LayerTranscript E p) : List (List E) :=
  [List.ofFn t.product, [t.point]] ++ roundMessages t.packPolys t.packPoint ++
    roundMessages t.positionPolys t.positionPoint ++ [List.ofFn t.evaluations]

/-- Beta is the only wire message following a layer's body. -/
theorem layerMessages_body {E : Type} {p : Nat} (t : LayerTranscript E p) :
    layerMessages t = layerBody t ++ [[t.beta]] := by
  simp only [layerMessages, layerBody, List.append_assoc, List.singleton_append]

/-- A layer body has one fewer wire message than its complete layer. -/
theorem layerBody_length {E : Type} {p : Nat} (t : LayerTranscript E p) :
    (layerBody t).length = 2*p+27 := by
  have h := layerMessages_length t
  rw [layerMessages_body, List.length_append] at h
  simp only [List.length_cons, List.length_nil] at h
  omega

/-- A common prefix through the shifted evaluations fixes every layer field except beta. -/
theorem prefix_layer_beta_fixed {E : Type} [CommRing E] {p : Nat} (t u : Transcript E p)
    (history : List (List E)) (ht : history <+: transcriptMessages t)
    (hu : history <+: transcriptMessages u) (d : Fin 12) (beta : E)
    (hi : layerOffset p d+(2*p+27) ≤ history.length) :
    {t.layers d with beta := beta} = {u.layers d with beta := beta} := by
  have bodies : layerBody (t.layers d) = layerBody (u.layers d) := by
    apply List.ext_getElem?
    intro j
    by_cases hj : j < 2*p+27
    · have h := authored_getElem_eq history _ _ ht hu (layerOffset p d+j) (by omega)
      rw [transcriptMessages_get_layer _ d j (by omega),
        transcriptMessages_get_layer _ d j (by omega), layerMessages_body, layerMessages_body,
        List.getElem?_append_left (by rw [layerBody_length]; exact hj),
        List.getElem?_append_left (by rw [layerBody_length]; exact hj)] at h
      exact h
    · rw [List.getElem?_eq_none (by rw [layerBody_length]; omega),
        List.getElem?_eq_none (by rw [layerBody_length]; omega)]
  apply layerMessages_injective
  rw [layerMessages_body, layerMessages_body]
  change layerBody (t.layers d) ++ [[beta]] = layerBody (u.layers d) ++ [[beta]]
  rw [bodies]

/-- The beta scalar occupies the last wire in a layer. -/
theorem layerMessages_get_beta {E : Type} {p : Nat} (t : LayerTranscript E p) :
    (layerMessages t)[2*p+27]? = some [t.beta] := by
  rw [layerMessages_body, List.getElem?_append_right (by rw [layerBody_length]), layerBody_length,
    Nat.sub_self]
  rfl

/-- A layer's pack sumcheck starts after its product polynomial and evaluation point. -/
theorem layerMessages_get_pack {E : Type} {p : Nat} (t : LayerTranscript E p)
    (j : Nat) (hj : j < 2*(p+1)) :
    (layerMessages t)[2+j]? = (roundMessages t.packPolys t.packPoint)[j]? := by
  simpa only [layerMessages, List.append_assoc] using getElem?_middle_block [List.ofFn t.product, [t.point]]
    (roundMessages t.packPolys t.packPoint)
    (roundMessages t.positionPolys t.positionPoint ++ [List.ofFn t.evaluations, [t.beta]])
    2 j rfl (by rw [roundMessages_length]; exact hj)

/-- A layer's position sumcheck follows its complete pack sumcheck. -/
theorem layerMessages_get_position {E : Type} {p : Nat} (t : LayerTranscript E p)
    (j : Nat) (hj : j < 22) :
    (layerMessages t)[(2*p+4)+j]? = (roundMessages t.positionPolys t.positionPoint)[j]? := by
  apply getElem?_middle_block
    ([List.ofFn t.product, [t.point]] ++ roundMessages t.packPolys t.packPoint)
    (roundMessages t.positionPolys t.positionPoint) [List.ofFn t.evaluations, [t.beta]]
    (2*p+4) j
  · simp only [List.length_append, List.length_cons, List.length_nil, roundMessages_length]
    omega
  · simpa only [roundMessages_length] using hj

/-- The middle-opening block starts after all twelve complete layers. -/
def wordOffset (p : Nat) : Nat := p+11+12*(2*p+28)

/-- The input-opening block follows the middle sumcheck and its scalar value. -/
def inputOffset (p : Nat) : Nat := wordOffset p+13

/-- The transcript's complete header and layers have the offset of the middle opening. -/
theorem transcriptMessages_opening_blocks {E : Type} [CommRing E] {p : Nat}
    (t : Transcript E p) :
    ∃ pre : List (List E), pre.length = wordOffset p ∧ transcriptMessages t =
      pre ++ roundMessages t.openings.outputPolys t.openings.outputPoint ++
        [[t.openings.outputValue]] ++ roundMessages t.openings.inputPolys t.openings.inputPoint ++
        [List.ofFn t.openings.slices] := by
  refine ⟨coordinateMessages (initialPoint t) ++ [[t.middleValue]] ++ sequenceMessages t.layers, ?_, ?_⟩
  · simp only [List.length_append, coordinateMessages, List.length_ofFn, List.length_cons,
      List.length_nil, sequenceMessages, List.length_flatten, List.map_ofFn, Function.comp_def,
      layerMessages_length, List.ofFn_const, List.sum_replicate, smul_eq_mul, wordOffset]
  · rw [transcriptMessages_blocks]
    simp only [openingMessages, inputOpeningMessages, List.append_assoc]

/-- Middle-opening round messages have their fixed wire offsets in every transcript. -/
theorem transcriptMessages_get_word {E : Type} [CommRing E] {p : Nat}
    (t : Transcript E p) (j : Nat) (hj : j < 12) :
    (transcriptMessages t)[wordOffset p+j]? =
      (roundMessages t.openings.outputPolys t.openings.outputPoint)[j]? := by
  obtain ⟨pre, hp, he⟩ := transcriptMessages_opening_blocks t
  rw [he]
  simpa only [List.append_assoc] using getElem?_middle_block pre
    (roundMessages t.openings.outputPolys t.openings.outputPoint)
    ([[t.openings.outputValue]] ++ roundMessages t.openings.inputPolys t.openings.inputPoint ++
      [List.ofFn t.openings.slices]) (wordOffset p) j hp (by rw [roundMessages_length]; exact hj)

/-- Input-opening round messages have their fixed wire offsets in every transcript. -/
theorem transcriptMessages_get_input {E : Type} [CommRing E] {p : Nat}
    (t : Transcript E p) (j : Nat) (hj : j < 20) :
    (transcriptMessages t)[inputOffset p+j]? =
      (roundMessages t.openings.inputPolys t.openings.inputPoint)[j]? := by
  obtain ⟨pre, hp, he⟩ := transcriptMessages_opening_blocks t
  rw [he]
  apply getElem?_middle_block
    (pre ++ roundMessages t.openings.outputPolys t.openings.outputPoint ++ [[t.openings.outputValue]])
    (roundMessages t.openings.inputPolys t.openings.inputPoint) [List.ofFn t.openings.slices]
    (inputOffset p) j
  · simp only [List.length_append, hp, roundMessages_length, List.length_cons, List.length_nil,
      inputOffset]
  · simpa only [roundMessages_length] using hj

/-- The middle-opening value occupies the scalar wire between the two opening blocks. -/
theorem transcriptMessages_get_wordValue {E : Type} [CommRing E] {p : Nat}
    (t : Transcript E p) :
    (transcriptMessages t)[wordOffset p+12]? = some [t.openings.outputValue] := by
  obtain ⟨pre, hp, he⟩ := transcriptMessages_opening_blocks t
  rw [he]
  have h := getElem?_middle_block pre
    (roundMessages t.openings.outputPolys t.openings.outputPoint ++ [[t.openings.outputValue]])
    (roundMessages t.openings.inputPolys t.openings.inputPoint ++ [List.ofFn t.openings.slices])
    (wordOffset p) 12 hp (by simp only [List.length_append, roundMessages_length,
      List.length_cons, List.length_nil]; omega)
  have hread : (roundMessages t.openings.outputPolys t.openings.outputPoint ++
      [[t.openings.outputValue]])[12]? = some [t.openings.outputValue] := by
    rw [List.getElem?_append_right (by rw [roundMessages_length]), roundMessages_length, Nat.sub_self]
    rfl
  rw [hread] at h
  simpa only [List.append_assoc] using h

/-- The layer's evaluation point is fixed before its pack sumcheck. -/
theorem prefix_layer_point_fixed {E : Type} [CommRing E] {p : Nat} (t u : Transcript E p)
    (history : List (List E)) (ht : history <+: transcriptMessages t)
    (hu : history <+: transcriptMessages u) (d : Fin 12)
    (hi : layerOffset p d+1 < history.length) : (t.layers d).point = (u.layers d).point := by
  have h := authored_getElem_eq history _ _ ht hu (layerOffset p d+1) hi
  rw [transcriptMessages_get_layer _ d 1 (by omega), transcriptMessages_get_layer _ d 1 (by omega),
    layerMessages_get_point, layerMessages_get_point] at h
  exact List.singleton_inj.mp (Option.some.inj h)

end CompStark.Keccak.Gkr
