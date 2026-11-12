/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Transcript.Duplex
public import CompStark.Keccak.Prepared

/-! The lane-level duplex writer on the transcript's sixteen-lane rate, proved equal to the item-level transcript at every absorb, squeeze and grind. -/

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStark.Keccak.TranscriptDuplex
open CompStark.BinaryFields CompStark.Keccak.Lanes CompStark.Keccak.Duplex

/-- A squeeze on the native permutation, sharing one permutation array. -/
def squeezeNative (s : Transcript.State) : E × Transcript.State :=
  let lanes := CompStark.Keccak.f1600 (Array.ofFn fun i : Fin 25 =>
    if h : i.val < 16 then (Transcript.rateBlock s.pending)[i.val]!
    else s.capacity ⟨i.val - 16, by omega⟩)
  (E.ofLimbs (wordLane lanes[0]!) (wordLane lanes[1]!) (wordLane lanes[2]!),
    ⟨fun i => lanes[16 + i.val]!, [], by decide⟩)

/-- The native squeeze gives the specification's challenge and capacity. -/
theorem squeezeNative_eq (s : Transcript.State) : squeezeNative s = Transcript.squeeze s := by
  rw [Transcript.squeeze_code]
  simp only [squeezeNative, Transcript.squeezeExec, CompStark.Keccak.f1600_eq]

/-- Absorption flushing a full rate through the native squeeze. -/
def absorbNative (s : Transcript.State) (item : Transcript.Item) : Transcript.State :=
  let flushed := if s.pending.length = 4 then (squeezeNative s).2 else s
  ⟨flushed.capacity, flushed.pending ++ [item], by
    dsimp [flushed]; split
    · simp only [squeezeNative, List.nil_append, List.length_singleton]; omega
    · have := s.bounded
      simp only [List.length_append, List.length_singleton]; omega⟩

/-- Native absorption has the specification's complete state transition. -/
theorem absorbNative_eq (s : Transcript.State) (item : Transcript.Item) :
    absorbNative s item = Transcript.absorb s item := by
  simp only [absorbNative, squeezeNative_eq, Transcript.absorb]

/-- Production overwrite-duplex rate: sixteen lanes with nine capacity lanes. -/
def rate : CompStark.Keccak.Duplex.Rate := ⟨16, by decide, by decide⟩

/-- Materialize exactly the pending production frames and carried capacity. -/
def duplexState (state : Transcript.State) : CompStark.Keccak.Duplex.State rate Unit :=
  ⟨Array.ofFn (fun i : Fin 25 => if h : i.val < 16 then
    (Transcript.rateBlock state.pending)[i.val]! else state.capacity ⟨i.val - 16, by omega⟩),
    Array.size_ofFn, 4 * state.pending.length, by have := state.bounded; dsimp [rate]; omega, ()⟩

/-- Full output lanes of a native production squeeze. -/
def squeezeLanes (state : Transcript.State) : Array UInt64 :=
  CompStark.Keccak.f1600 (duplexState state).lanes

/-- The materialized squeeze has precisely the scalar and capacity of the native writer. -/
theorem squeezeLanes_eq (state : Transcript.State) :
    (E.ofLimbs (wordLane (squeezeLanes state)[0]!)
      (wordLane (squeezeLanes state)[1]!)
      (wordLane (squeezeLanes state)[2]!),
      (⟨fun i => (squeezeLanes state)[16 + i.val]!, [], by decide⟩ : Transcript.State)) =
      squeezeNative state := rfl

/-- Unit-observed duplex states are determined by their lane array and pending cursor. -/
theorem state_ext (a b : Duplex.State rate Unit) (lanes : a.lanes = b.lanes)
    (pending : a.pending = b.pending) : a = b := by
  cases a with
  | mk av aw ap ab ao =>
    cases b with
    | mk bv bw bp bb bo =>
      dsimp only at lanes pending
      cases lanes
      cases pending
      cases ao
      cases bo
      rfl

/-- Squeezing a materialized production state carries exactly the native writer's capacity. -/
theorem flush_transport (s : Transcript.State) :
    (flushWith CompStark.Keccak.f1600 fast_width rate (fun _ _ _ => ()) (duplexState s)).2 =
      duplexState (squeezeNative s).2 := by
  apply state_ext
  · apply Array.ext
    · simp only [flushWith, Array.size_mapIdx, fast_width, duplexState, Array.size_ofFn]
    · intro i hi hj
      have bound : i < 25 := by simpa only [flushWith, Array.size_mapIdx, fast_width] using hi
      simp only [flushWith, Array.getElem_mapIdx, duplexState, Array.getElem_ofFn,
        squeezeNative, rate]
      by_cases h : i < 16
      · simp only [h, ↓reduceIte, ↓reduceDIte]
        have hz : ∀ j : Fin 16, (Transcript.rateBlock [])[j.val]! = 0 := by decide
        exact (hz ⟨i, h⟩).symm
      · simp only [h, ↓reduceIte, ↓reduceDIte]
        have index : 16 + (i-16) = i := by omega
        let output := CompStark.Keccak.f1600 (duplexState s).lanes
        change output[i] = output[16+(i-16)]!
        rw [index]
        exact (getElem!_pos output i (by rw [fast_width]; exact bound)).symm
  · rfl

/-- Reading a three-lane sample preserves each selected output word. -/
theorem extract_three (output : Array UInt64) (width : output.size = 25) (i : Fin 3) :
    (output.extract 0 3)[i.val]! = output[i.val]! := by
  have size : (output.extract 0 3).size = 3 := by
    simp only [Array.size_extract, width]; decide
  have hi : i.val < output.size := by rw [width]; omega
  rw [getElem!_pos (output.extract 0 3) i.val (by rw [size]; exact i.isLt),
    getElem!_pos output i.val hi, Array.getElem_extract]
  simp only [Nat.zero_add]

/-- Sampling the native duplex returns the production scalar and materialized successor state. -/
theorem sample_transport (s : Transcript.State) :
    let result := Duplex.sample rate (fun _ _ _ => ()) (duplexState s) 3 (by decide)
    (E.ofLimbs (wordLane result.1[0]!)
      (wordLane result.1[1]!) (wordLane result.1[2]!), result.2) =
      ((squeezeNative s).1, duplexState (squeezeNative s).2) := by
  apply Prod.ext
  · let output := CompStark.Keccak.f1600 (duplexState s).lanes
    change E.ofLimbs (wordLane (output.extract 0 3)[0]!)
      (wordLane (output.extract 0 3)[1]!) (wordLane (output.extract 0 3)[2]!) =
      E.ofLimbs (wordLane output[0]!)
        (wordLane output[1]!) (wordLane output[2]!)
    have h0 := extract_three output (fast_width _) ⟨0, by decide⟩
    have h1 := extract_three output (fast_width _) ⟨1, by decide⟩
    have h2 := extract_three output (fast_width _) ⟨2, by decide⟩
    change (output.extract 0 3)[0]! = output[0]! at h0
    change (output.extract 0 3)[1]! = output[1]! at h1
    change (output.extract 0 3)[2]! = output[2]! at h2
    rw [h0, h1, h2]
  · exact flush_transport s

/-- A complete item fits in an available production slot without a permutation. -/
theorem absorb_four_ready (state : Duplex.State rate Unit) (a b c d : UInt64)
    (h : state.pending + 4 ≤ 16) :
    let next := Duplex.absorb rate (fun _ _ _ => ()) state #[a,b,c,d]
    next.lanes = (((state.lanes.set! state.pending a).set! (state.pending+1) b).set!
      (state.pending+2) c).set! (state.pending+3) d ∧ next.pending = state.pending+4 := by
  have h0 : state.pending ≠ 16 := by omega
  have h1 : state.pending+1 ≠ 16 := by omega
  have h2 : state.pending+1+1 ≠ 16 := by omega
  have h3 : state.pending+1+1+1 ≠ 16 := by omega
  simp only [Duplex.absorb, absorbWith, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, absorbLaneWith,
    rate, h0, h1, h2, h3, ↓reduceIte]
  constructor <;> trivial

/-- Appending a bounded frame overwrites its four previously padded rate lanes. -/
theorem rateBlock_append (pending : List Transcript.Item) (item : Transcript.Item)
    (h : pending.length < 4) :
    Transcript.rateBlock (pending ++ [item]) =
      ((((Transcript.rateBlock pending).set (4*pending.length) item.lanes[0]!).set
        (4*pending.length+1) item.lanes[1]!).set
        (4*pending.length+2) item.lanes[2]!).set
        (4*pending.length+3) item.lanes[3]! := by
  rcases pending with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, tail⟩⟩⟩⟩
  all_goals try { simp only [List.length_cons] at h; omega }
  all_goals cases item
  all_goals try cases x
  all_goals try cases y
  all_goals try cases z
  all_goals rfl

/-- Bounded item lists materialize exactly sixteen rate lanes. -/
theorem rateBlock_width (pending : List Transcript.Item) (h : pending.length ≤ 4) :
    (Transcript.rateBlock pending).length = 16 := by
  have width : (pending.flatMap Transcript.Item.lanes).length = 4*pending.length := by
    clear h
    induction pending with
    | nil => rfl
    | cons item pending ih =>
      simp only [List.flatMap_cons, List.length_append, Transcript.Item.lanes_length,
        List.length_cons, ih]
      omega
  simp only [Transcript.rateBlock, List.length_append, List.length_replicate, width]
  omega

/-- Checked list reads commute with a single bounded overwrite. -/
theorem list_get_set (xs : List UInt64) (i j : Nat) (value : UInt64) (hj : j < xs.length) :
    (xs.set i value)[j]! = if i = j then value else xs[j]! := by
  rw [getElem!_pos (xs.set i value) j (by simpa only [List.length_set] using hj),
    getElem!_pos xs j hj, List.getElem_set]

/-- A materialized four-lane overwrite is exactly a bounded production frame append. -/
theorem materialized_append (s : Transcript.State) (item : Transcript.Item)
    (h : s.pending.length < 4) :
    (duplexState ⟨s.capacity, s.pending ++ [item], by
      simp only [List.length_append, List.length_singleton]; omega⟩).lanes =
      ((((duplexState s).lanes.set! (4*s.pending.length) item.lanes[0]!).set!
        (4*s.pending.length+1) item.lanes[1]!).set!
        (4*s.pending.length+2) item.lanes[2]!).set!
        (4*s.pending.length+3) item.lanes[3]! := by
  apply Array.ext
  · simp only [Array.size_set!, duplexState, Array.size_ofFn]
  · intro i hi hj
    have small : i < 25 := by simpa only [duplexState, Array.size_ofFn] using hi
    simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds,
      duplexState, Array.getElem_ofFn, Array.size_setIfInBounds, Array.size_ofFn, small]
    by_cases hr : i < 16
    · simp only [hr, ↓reduceDIte, rateBlock_append s.pending item h]
      have width := rateBlock_width s.pending s.bounded
      simp only [list_get_set, List.length_set, width, hr]
    · have h0 : 4*s.pending.length ≠ i := by omega
      have h1 : 4*s.pending.length+1 ≠ i := by omega
      have h2 : 4*s.pending.length+2 ≠ i := by omega
      have h3 : 4*s.pending.length+3 ≠ i := by omega
      simp only [hr, h0, h1, h2, h3, ↓reduceIte, ↓reduceDIte]

/-- Appending a frame in an available slot preserves the materialized production state. -/
theorem absorb_ready (s : Transcript.State) (item : Transcript.Item)
    (h : s.pending.length < 4) :
    Duplex.absorb rate (fun _ _ _ => ()) (duplexState s) item.lanes.toArray =
      duplexState ⟨s.capacity, s.pending ++ [item], by
        simp only [List.length_append, List.length_singleton]; omega⟩ := by
  have available : (duplexState s).pending + 4 ≤ 16 := by
    change 4*s.pending.length+4 ≤ 16
    omega
  have ready :
      (Duplex.absorb rate (fun _ _ _ => ()) (duplexState s) item.lanes.toArray).lanes =
        ((((duplexState s).lanes.set! (4*s.pending.length) item.lanes[0]!).set!
          (4*s.pending.length+1) item.lanes[1]!).set!
          (4*s.pending.length+2) item.lanes[2]!).set!
          (4*s.pending.length+3) item.lanes[3]! ∧
      (Duplex.absorb rate (fun _ _ _ => ()) (duplexState s) item.lanes.toArray).pending =
        4*s.pending.length+4 := by
    cases item <;> exact absorb_four_ready (duplexState s) _ _ _ _ available
  apply state_ext
  · exact ready.1.trans (materialized_append s item h).symm
  · rw [ready.2]
    simp only [duplexState, List.length_append, List.length_singleton, Nat.mul_add, Nat.mul_one]

/-- A full rate flushes exactly once before the first lane of the next frame. -/
theorem absorb_four_full (state : Duplex.State rate Unit) (a b c d : UInt64)
    (h : state.pending = 16) :
    Duplex.absorb rate (fun _ _ _ => ()) state #[a,b,c,d] =
      Duplex.absorb rate (fun _ _ _ => ())
        (flushWith CompStark.Keccak.f1600 fast_width rate (fun _ _ _ => ()) state).2 #[a,b,c,d] := by
  have first : absorbLaneWith CompStark.Keccak.f1600 fast_width rate (fun _ _ _ => ()) state a =
      absorbLaneWith CompStark.Keccak.f1600 fast_width rate (fun _ _ _ => ())
        (flushWith CompStark.Keccak.f1600 fast_width rate (fun _ _ _ => ()) state).2 a := by
    simp only [absorbLaneWith, h, rate, ↓reduceIte, flushWith, Nat.reduceEqDiff]
  simp only [Duplex.absorb, absorbWith, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, first]

/-- Every framed absorb, including the full-rate boundary, preserves the production state. -/
theorem absorb_transport (s : Transcript.State) (item : Transcript.Item) :
    Duplex.absorb rate (fun _ _ _ => ()) (duplexState s) item.lanes.toArray =
      duplexState (absorbNative s item) := by
  by_cases full : s.pending.length = 4
  · have boundary : (duplexState s).pending = 16 := by
      simp only [duplexState, full]
    have flush : Duplex.absorb rate (fun _ _ _ => ()) (duplexState s) item.lanes.toArray =
        Duplex.absorb rate (fun _ _ _ => ())
          (flushWith CompStark.Keccak.f1600 fast_width rate (fun _ _ _ => ()) (duplexState s)).2
          item.lanes.toArray := by
      cases item <;> exact absorb_four_full (duplexState s) _ _ _ _ boundary
    rw [flush, flush_transport, absorb_ready (squeezeNative s).2 item (by
      change 0 < 4; decide)]
    simp only [absorbNative, full, ↓reduceIte]
  · have available : s.pending.length < 4 := by have := s.bounded; omega
    rw [absorb_ready s item available]
    simp only [absorbNative, full, ↓reduceIte]

/-- A concatenated stream of production frames preserves every intervening flush. -/
theorem absorbAll_transport (s : Transcript.State) (items : List Transcript.Item) :
    Duplex.absorb rate (fun _ _ _ => ()) (duplexState s)
      (items.flatMap Transcript.Item.lanes).toArray =
      duplexState (items.foldl absorbNative s) := by
  induction items generalizing s with
  | nil => rfl
  | cons item items ih =>
    have append (a b : Array UInt64) (state : Duplex.State rate Unit) :
        Duplex.absorb rate (fun _ _ _ => ()) state (a ++ b) =
          Duplex.absorb rate (fun _ _ _ => ()) (Duplex.absorb rate (fun _ _ _ => ()) state a) b := by
      exact Array.foldl_append
    simp only [List.flatMap_cons, ← List.append_toArray, List.foldl_cons,
      append, absorb_transport, ih]

/-- Honest nonce frames use only the low word and domain four. -/
def nonceFrame (nonce : Nat) : Array UInt64 := #[nonce.toUInt64, 0, 0, 4]

/-- Test the production contiguous low-bit grinding window. -/
def acceptNonce (bits : Nat) (output : Array UInt64) : Bool :=
  decide (output[0]!.toNat % 2 ^ (min bits 64) = 0)

/-- Search all representable honest nonces in increasing order using CompStark's grinder. -/
def grind (bits : Nat) (state : CompStark.Keccak.Duplex.State rate Unit) :
    Option (Nat × CompStark.Keccak.Duplex.State rate Unit) :=
  CompStark.Keccak.Duplex.grind rate (fun _ _ _ => ()) state nonceFrame (acceptNonce bits) (2 ^ 64)

/-- Production nonce search with a prepared frame and deterministic parallel chunks. -/
def grindPrepared (bits : Nat) (state : CompStark.Keccak.Duplex.State rate Unit) :
    Option (Nat × CompStark.Keccak.Duplex.State rate Unit) :=
  CompStark.Keccak.Duplex.grindNonce rate (fun _ _ _ => ()) state bits (2 ^ 64)

/-- Prepared probing retains the exact smallest nonce, carried state and transcript framing. -/
@[csimp] theorem grind_prepared_code : grind = grindPrepared := by
  funext bits state
  rw [grindPrepared, CompStark.Keccak.Duplex.grindNonce_eq]
  rfl

/-- The complete native grind, including its carried capacity, refines the VCVio permutation. -/
theorem grind_refines (bits : Nat) (state : CompStark.Keccak.Duplex.State rate Unit) :
    grind bits state =
      CompStark.Keccak.Duplex.grindWith VCVio.Algorithms.Keccak.f1600
        CompStark.Keccak.Duplex.spec_width rate (fun _ _ _ => ()) state nonceFrame
        (acceptNonce bits) (2 ^ 64) := by
  exact CompStark.Keccak.Duplex.grind_eq ..

/-- Every successful grind chooses the smallest acceptable honest nonce. -/
theorem grind_min (bits : Nat) (state : CompStark.Keccak.Duplex.State rate Unit)
    (nonce : Nat) (next : CompStark.Keccak.Duplex.State rate Unit)
    (h : grind bits state = some (nonce, next)) :
    let probe := fun n => (CompStark.Keccak.Duplex.flushWith CompStark.Keccak.f1600
      CompStark.Keccak.Duplex.fast_width rate (fun o _ _ => o)
      (CompStark.Keccak.Duplex.absorbWith CompStark.Keccak.f1600
        CompStark.Keccak.Duplex.fast_width rate (fun o _ _ => o) state (nonceFrame n))).1
    nonce < 2 ^ 64 ∧ acceptNonce bits (probe nonce) = true ∧
      ∀ m, m < nonce → acceptNonce bits (probe m) = false :=
  CompStark.Keccak.Duplex.grind_min rate (fun _ _ _ => ()) state nonceFrame
    (acceptNonce bits) (2 ^ 64) nonce next h


/-- Sampling the lane writer returns the specification's challenge and successor state. -/
theorem sample_spec (s : Transcript.State) :
    let result := Duplex.sample rate (fun _ _ _ => ()) (duplexState s) 3 (by decide)
    (E.ofLimbs (wordLane result.1[0]!) (wordLane result.1[1]!) (wordLane result.1[2]!),
      result.2) = ((Transcript.squeeze s).1, duplexState (Transcript.squeeze s).2) := by
  rw [← squeezeNative_eq]
  exact sample_transport s

/-- Absorbing an item's lanes is the specification's absorption. -/
theorem absorb_spec (s : Transcript.State) (item : Transcript.Item) :
    Duplex.absorb rate (fun _ _ _ => ()) (duplexState s) item.lanes.toArray =
      duplexState (Transcript.absorb s item) := by
  rw [← absorbNative_eq]
  exact absorb_transport s item

/-- Absorbing a stream of item lanes is the specification's absorption of the stream. -/
theorem absorbAll_spec (s : Transcript.State) (items : List Transcript.Item) :
    Duplex.absorb rate (fun _ _ _ => ()) (duplexState s)
      (items.flatMap Transcript.Item.lanes).toArray =
      duplexState (Transcript.absorbAll s items) := by
  have native : items.foldl absorbNative s = Transcript.absorbAll s items := by
    simp only [Transcript.absorbAll, show absorbNative = Transcript.absorb from
      funext fun a => funext fun b => absorbNative_eq a b]
  rw [← native]
  exact absorbAll_transport s items

end CompStark.Keccak.TranscriptDuplex
