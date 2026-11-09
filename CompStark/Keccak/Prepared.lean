/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Duplex

/-! Prepared low-word nonce probes and deterministic parallel search. -/

@[expose] public section
namespace CompStark.Keccak.Duplex

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- The production nonce occupies one tagged scalar frame. -/
def nonceFrame (nonce : Nat) : Array UInt64 := #[nonce.toUInt64, 0, 0, 4]

/-- Absorbing one lane inside the rate does not permute. -/
theorem absorbLane_inside (rate : Rate) (state : State rate O) (lane : UInt64)
    (h : state.pending < rate.lanes) :
    absorbLaneWith f1600 fast_width rate (fun o _ _ => o) state lane =
      ⟨state.lanes.set! state.pending lane, by simp only [Array.size_set!, state.width],
        state.pending + 1, by omega, state.observed⟩ := by
  simp only [absorbLaneWith, Nat.ne_of_lt h, ↓reduceIte]

/-- A fitting nonce frame writes four lanes without any intermediate permutation. -/
theorem nonce_lanes (rate : Rate) (state : State rate O)
    (fit : state.pending + 4 ≤ rate.lanes) (nonce : Nat) :
    (absorbWith f1600 fast_width rate (fun o _ _ => o) state (nonceFrame nonce)).lanes =
      (((state.lanes.set! state.pending nonce.toUInt64).set! (state.pending + 1) 0).set!
        (state.pending + 2) 0).set! (state.pending + 3) 4 := by
  have h0 : state.pending ≠ rate.lanes := by omega
  have h1 : state.pending + 1 ≠ rate.lanes := by omega
  have h2 : state.pending + 2 ≠ rate.lanes := by omega
  have h3 : state.pending + 3 ≠ rate.lanes := by omega
  simp only [absorbWith, nonceFrame, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil,
    absorbLaneWith, h0, h1, h2, h3, ↓reduceIte, Nat.add_assoc]

/-- Replacing the nonce in the prepared input reproduces absorption of that nonce. -/
theorem nonce_prepared (rate : Rate) (state : State rate O)
    (fit : state.pending + 4 ≤ rate.lanes) (nonce : Nat) :
    ((absorbWith f1600 fast_width rate (fun o _ _ => o) state (nonceFrame 0)).lanes.set!
      state.pending nonce.toUInt64) =
      (absorbWith f1600 fast_width rate (fun o _ _ => o) state (nonceFrame nonce)).lanes := by
  rw [nonce_lanes _ _ fit, nonce_lanes _ _ fit]
  simp only [Array.set!_eq_setIfInBounds]
  rw [Array.setIfInBounds_comm (i := state.pending + 3) (j := state.pending) _ _ (by omega),
    Array.setIfInBounds_comm (i := state.pending + 2) (j := state.pending) _ _ (by omega),
    Array.setIfInBounds_comm (i := state.pending + 1) (j := state.pending) _ _ (by omega),
    Array.setIfInBounds_setIfInBounds]

/-- Consecutive searches compose without changing their first accepted candidate. -/
theorem findNonce_add (accept : Nat → Bool) (left right first : Nat) :
    findNonce accept (left + right) first =
      (findNonce accept left first).or (findNonce accept right (first + left)) := by
  induction left generalizing first with
  | zero => simp only [Nat.zero_add, findNonce, Nat.add_zero, Option.none_or]
  | succ left ih =>
    rw [Nat.succ_add, findNonce, findNonce]
    split
    · rfl
    · rw [ih]
      congr 2
      omega

/-- Searching consecutive chunks in order returns the first match of their union. -/
theorem findNonce_chunks (accept : Nat → Bool) (size first chunks : Nat) :
    ((List.range chunks).map fun k => findNonce accept size (first + size * k)).findSome? id =
      findNonce accept (size * chunks) first := by
  induction chunks with
  | zero => rfl
  | succ chunks ih =>
    rw [List.range_succ, List.map_append, List.findSome?_append, ih, Nat.mul_succ,
      findNonce_add]
    simp only [List.map_cons, List.map_nil, List.findSome?_cons, List.findSome?_nil, id]
    cases findNonce accept (size * chunks) first <;> cases findNonce accept size (first + size * chunks) <;> rfl

/-- Search parallel waves of sixteen consecutive 512-candidate chunks in nonce order. -/
def findNonceParallel (accept : Nat → Bool) (fuel first : Nat) : Option Nat :=
  if fuel < 8192 then findNonce accept fuel first
  else
    let tasks := (Array.range 16).map fun k =>
      Task.spawn fun _ => findNonce accept 512 (first + 512 * k)
    match (tasks.map Task.get).findSome? id with
    | some nonce => some nonce
    | none => findNonceParallel accept (fuel - 8192) (first + 8192)
termination_by fuel
decreasing_by omega

/-- Parallel scheduling preserves the sequential search's exact smallest nonce. -/
theorem findNonceParallel_eq (accept : Nat → Bool) (fuel first : Nat) :
    findNonceParallel accept fuel first = findNonce accept fuel first := by
  induction fuel using Nat.strong_induction_on generalizing first with
  | h fuel ih =>
      rw [findNonceParallel]
      split
      · rfl
      · rename_i h
        have tasks : (((Array.range 16).map fun k =>
            Task.spawn fun _ => findNonce accept 512 (first + 512 * k)).map Task.get).findSome? id =
            findNonce accept 8192 first := by
          rw [Array.map_map]
          change (((Array.range 16).map fun k => findNonce accept 512 (first + 512 * k)).findSome? id) = _
          have equal := findNonce_chunks accept 512 first 16
          simpa only [Array.toList_map, Array.toList_range, ← Array.findSome?_toList] using equal
        dsimp only
        have splitFuel : findNonce accept fuel first =
            (findNonce accept 8192 first).or (findNonce accept (fuel - 8192) (first + 8192)) := by
          conv_lhs => rw [show fuel = 8192 + (fuel - 8192) by omega]
          exact findNonce_add accept 8192 (fuel - 8192) first
        rw [tasks, splitFuel]
        cases findNonce accept 8192 first with
        | some nonce => rfl
        | none =>
            simp only [Option.none_or]
            exact ih (fuel - 8192) (by omega) (first + 8192)

/-- Flush a full rate once before preparing a nonce frame. -/
def nonceReady (rate : Rate) (state : State rate O) : State rate O :=
  if state.pending = rate.lanes then
    (flushWith f1600 fast_width rate (fun o _ _ => o) state).2 else state

/-- A full-rate preparation does not change absorption of the next lane. -/
theorem absorbLane_ready (rate : Rate) (state : State rate O) (lane : UInt64) :
    absorbLaneWith f1600 fast_width rate (fun o _ _ => o) (nonceReady rate state) lane =
      absorbLaneWith f1600 fast_width rate (fun o _ _ => o) state lane := by
  by_cases h : state.pending = rate.lanes
  · have hz : (0 : Nat) ≠ rate.lanes := Nat.ne_of_lt rate.positive
    simp only [nonceReady, h, ↓reduceIte, absorbLaneWith, flushWith, hz]
  · simp only [nonceReady, h, ↓reduceIte]

/-- Preparing a full rate preserves the input of every subsequent nonce probe. -/
theorem nonceReady_lanes (rate : Rate) (state : State rate O) (nonce : Nat) :
    (absorbWith f1600 fast_width rate (fun o _ _ => o) (nonceReady rate state)
      (nonceFrame nonce)).lanes =
    (absorbWith f1600 fast_width rate (fun o _ _ => o) state (nonceFrame nonce)).lanes := by
  simp only [absorbWith, nonceFrame, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil]
  rw [absorbLane_ready]

/-- Test the contiguous low-bit nonce window on one unboxed output lane. -/
def nonceAccept (bits : Nat) (word : UInt64) : Bool :=
  decide (word.toNat % 2 ^ (min bits 64) = 0)

/-- Prepare the absorbed frame once, then probe only the first output lane; large searches
use ordered parallel chunks. Successful binding observes the original frame exactly once. -/
def grindNonce (rate : Rate) (observer : Observer O) (state : State rate O)
    (bits limit : Nat) : Option (Nat × State rate O) :=
  let ready := nonceReady rate state
  if ready.pending + 4 ≤ rate.lanes then
    let base := (absorbWith f1600 fast_width rate (fun o _ _ => o) ready (nonceFrame 0)).lanes
    let probe := fun n => nonceAccept bits (f1600FirstOverwrite base ready.pending n.toUInt64)
    let found := if bits < 13 then findNonce probe limit 0 else findNonceParallel probe limit 0
    found.map fun nonce =>
      (nonce, (flushWith f1600 fast_width rate observer
        (absorbWith f1600 fast_width rate observer state (nonceFrame nonce))).2)
  else grind rate observer state nonceFrame (fun output => nonceAccept bits output[0]!) limit

/-- Prepared parallel grinding preserves the entire sequential result, including observations. -/
theorem grindNonce_eq (rate : Rate) (observer : Observer O) (state : State rate O)
    (bits limit : Nat) :
    grindNonce rate observer state bits limit =
      grind rate observer state nonceFrame (fun output => nonceAccept bits output[0]!) limit := by
  unfold grindNonce
  dsimp only
  split
  · rename_i fit
    have probe : (fun n => nonceAccept bits
        (f1600FirstOverwrite
          (absorbWith f1600 fast_width rate (fun o _ _ => o)
            (nonceReady rate state) (nonceFrame 0)).lanes
          (nonceReady rate state).pending n.toUInt64)) =
        (fun n => nonceAccept bits
          (flushWith f1600 fast_width rate (fun o _ _ => o)
            (absorbWith f1600 fast_width rate (fun o _ _ => o) state (nonceFrame n))).1[0]!) := by
      funext n
      rw [f1600FirstOverwrite_eq _ (State.width _) _, nonce_prepared _ _ fit, nonceReady_lanes]
      rfl
    simp only [findNonceParallel_eq, ite_self, probe]
    rfl
  · rfl

end CompStark.Keccak.Duplex
