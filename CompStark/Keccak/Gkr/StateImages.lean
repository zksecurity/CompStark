/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.Refinement
public import CompStark.Keccak.Gkr.InitialSampling

/-! Materialized machine-word state images for the algebraic Keccak checker. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
set_option smartUnfolding false
@[expose] public section
namespace CompStark.Keccak.Gkr
open CompStark.Keccak.GkrProver

/-- Embed one Boolean field element in the low bit of a machine word. -/
def bitWord (bit : ZMod 2) : UInt64 := if bit = 0 then 0 else 1

/-- Reading the low bit recovers the Boolean field element. -/
theorem bitWord_slice (bit : ZMod 2) : sliceBit (bitWord bit) 0 = bit := by
  fin_cases bit <;> decide

/-- Execute one committed twelve-round segment in machine-word state arrays. -/
def segmentSlices {p : Nat} (q : Witness p) (b : Fin (2 ^ (p + 4)))
    (m : Fin 2) : (e : Nat) → e ≤ 12 → Array UInt64
  | 0, _ => Array.ofFn fun j : Fin 1600 => bitWord (startState q b m j)
  | e + 1, he =>
      chiSlices (linearSlices (segmentSlices q b m e (by omega)) 1) 1 (12 * m.val + e)

/-- A single machine-word round agrees with its low-bit GKR state. -/
theorem oneRound_bit (state : Array UInt64) (r : Fin 24) (j : Fin 1600) :
    sliceBit (chiSlices (linearSlices state 1) 1 r.val)[j.val]! 0 =
      round r (fun k => sliceBit state[k.val]! 0) j := by
  simpa only [Nat.mul_one, Nat.add_zero] using
    (roundSlices_eq state (groups := 1) (g := 0) (by decide) r j 0)

/-- The bit-level segment advances by its numbered round. -/
theorem segmentState_step {p : Nat} (q : Witness p) (b : Fin (2 ^ (p + 4)))
    (m : Fin 2) (e : Nat) (he : e + 1 ≤ 12) :
    segmentState q b m (e + 1) he =
      round ⟨12 * m.val + e, by have := m.isLt; omega⟩ (segmentState q b m e (by omega)) := rfl

/-- The machine-word segment advances by its numbered round. -/
theorem segmentSlices_step {p : Nat} (q : Witness p) (b : Fin (2 ^ (p + 4)))
    (m : Fin 2) (e : Nat) (he : e + 1 ≤ 12) :
    segmentSlices q b m (e + 1) he =
      chiSlices (linearSlices (segmentSlices q b m e (by omega)) 1) 1 (12 * m.val + e) := rfl

/-- A valid array lookup recovers the generating function. -/
theorem arrayOfFn_get {A : Type} [Inhabited A] {n : Nat} (a : Fin n → A) (j : Fin n) :
    (Array.ofFn a)[j.val]! = a j := by
  simp only [getElem!_pos, Array.size_ofFn, j.isLt, Array.getElem_ofFn]

/-- The machine-word segment starts at the committed bit state. -/
theorem segmentSlices_zero {p : Nat} (q : Witness p) (b : Fin (2 ^ (p + 4)))
    (m : Fin 2) (he : 0 ≤ 12) (j : Fin 1600) :
    sliceBit (segmentSlices q b m 0 he)[j.val]! 0 = segmentState q b m 0 he j := by
  exact (congrArg (fun word => sliceBit word 0)
    (arrayOfFn_get (fun k => bitWord (startState q b m k)) j)).trans
    (bitWord_slice (startState q b m j))

/-- A correct machine-word segment prefix preserves its next round. -/
theorem segmentSlices_next {p : Nat} (q : Witness p) (b : Fin (2 ^ (p + 4)))
    (m : Fin 2) (e : Nat) (he : e + 1 ≤ 12)
    (states : (fun k : Fin 1600 => sliceBit (segmentSlices q b m e (by omega))[k.val]! 0) =
      segmentState q b m e (by omega)) (j : Fin 1600) :
    sliceBit (segmentSlices q b m (e + 1) he)[j.val]! 0 = segmentState q b m (e + 1) he j := by
  let r : Fin 24 := ⟨12 * m.val + e, by have := m.isLt; omega⟩
  calc
    _ = sliceBit (chiSlices (linearSlices (segmentSlices q b m e (by omega)) 1) 1 r.val)[j.val]! 0 :=
      congrArg (fun state : Array UInt64 => sliceBit state[j.val]! 0) (segmentSlices_step q b m e he)
    _ = round r (fun k => sliceBit (segmentSlices q b m e (by omega))[k.val]! 0) j :=
      oneRound_bit _ r j
    _ = round r (segmentState q b m e (by omega)) j :=
      congrArg (fun state => round r state j) states
    _ = segmentState q b m (e + 1) he j := congrFun (segmentState_step q b m e he).symm j

/-- Every materialized segment bit equals the authored GKR segment state. -/
theorem segmentSlices_bit {p : Nat} (q : Witness p) (b : Fin (2 ^ (p + 4)))
    (m : Fin 2) (e : Nat) (he : e ≤ 12) (j : Fin 1600) :
    sliceBit (segmentSlices q b m e he)[j.val]! 0 = segmentState q b m e he j := by
  induction e generalizing j with
  | zero => exact segmentSlices_zero q b m he j
  | succ e ih => exact segmentSlices_next q b m e he (funext fun k => ih (by omega) k) j

/-- The two segments retain every packed linear-layer bit at one GKR depth. -/
abbrev LinearImages (p : Nat) := Vector (Vector (Vector (Vector (ZMod 2) 1600) 16) (2 ^ p)) 2

/-- Materialize the fixed candidate linear layer before scalar interpolation. -/
@[noinline, nospecialize] def linearImages {p : Nat} (q : Witness p) (d : Fin 12) : LinearImages p :=
  Vector.ofFn fun m => Vector.ofFn fun b => Vector.ofFn fun i =>
    let state := linearSlices (segmentSlices q (packInstance i b) m (11 - d.val) (by omega)) 1
    Vector.ofFn fun j : Fin 1600 => sliceBit state[j.val]! 0

/-- The machine-word linear layer agrees with its low-bit GKR state. -/
theorem oneLinear_bit (state : Array UInt64) (j : Fin 1600) :
    sliceBit (linearSlices state 1)[j.val]! 0 =
      linear (fun k => sliceBit state[k.val]! 0) j := by
  simpa only [Nat.mul_one, Nat.add_zero] using
    (linearSlices_eq state (groups := 1) (g := 0) (by decide) j 0)

/-- Every cached linear-layer bit has its exact protocol value. -/
theorem linearImages_get {p : Nat} (q : Witness p) (d : Fin 12)
    (m : Fin 2) (b : Fin (2 ^ p)) (i : Fin 16) (j : Fin 1600) :
    ((((linearImages q d)[m.val])[b.val])[i.val])[j.val] =
      linear (segmentState q (packInstance i b) m (11 - d.val) (by omega)) j := by
  simp only [linearImages, Vector.getElem_ofFn]
  exact (oneLinear_bit _ j).trans (congrArg (fun state => linear state j)
    (funext fun k => segmentSlices_bit q (packInstance i b) m _ (by omega) k))

open CompStark.BinaryFields

/-- Materialize all output lanes from one shared machine-word segment. -/
@[noinline, nospecialize] def segmentLanes {p : Nat} (x : E) (q : Witness p)
    (b : Fin (2 ^ (p + 4))) (m : Fin 2) : Vector E 25 :=
  let state := segmentSlices q b m 12 (by omega)
  Vector.ofFn fun l => laneValue x (fun z : Fin 64 => sliceBit state[64 * l.val + z.val]! 0)

/-- Every cached segment lane equals its bit-level specification. -/
theorem segmentLanes_get {p : Nat} (x : E) (q : Witness p)
    (b : Fin (2 ^ (p + 4))) (m : Fin 2) (l : Fin 25) :
    (segmentLanes x q b m)[l.val] = segmentLane x q b m l := by
  simp only [segmentLanes, Vector.getElem_ofFn]
  exact congrArg (laneValue x) (funext fun z : Fin 64 =>
    segmentSlices_bit q b m 12 (by omega) (⟨64 * l.val + z.val, by omega⟩ : Fin 1600))

/-- Compute each initial discrepancy from explicit segment output lanes. -/
def initialErrorWith {p : Nat} (x : E) (output : Fin (2 ^ (p + 4)) → Fin 25 → E)
    (q : Witness p) (lanes : Fin (2 ^ (p + 4)) → Fin 2 → Fin 25 → E)
    (b : Fin (2 ^ (p + 4))) (slot : Fin 64) : E :=
  if h : slot.val / 2 < 25 then
    if slot.val % 2 = 0 then laneValue x (q b ⟨25 + slot.val / 2, by omega⟩) - lanes b 0 ⟨slot.val / 2, h⟩
    else output b ⟨slot.val / 2, h⟩ - lanes b 1 ⟨slot.val / 2, h⟩
  else 0

/-- Index instance and slot coordinates in the initial discrepancy cube. -/
def initialCube {p : Nat} (error : Fin (2 ^ (p + 4)) → Fin 64 → E)
    (w : Fin (2 ^ (p + 10))) : E :=
  error ⟨w.val % 2 ^ (p + 4), Nat.mod_lt _ (Nat.two_pow_pos _)⟩
    ⟨w.val / 2 ^ (p + 4), by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
      simpa only [show p + 10 = p + 4 + 6 by omega, pow_add,
        show (2 ^ 6 : Nat) = 64 by decide, Nat.mul_comm] using w.isLt⟩

/-- The indexed lane discrepancy is the authored initial table. -/
theorem initialCube_error {p : Nat} (x : E) (output : Fin (2 ^ (p + 4)) → Fin 25 → E)
    (q : Witness p) (w : Fin (2 ^ (p + 10))) :
    initialCube (initialErrorWith x output q (segmentLane x q)) w = initialTable x output q w := rfl

/-- Materialize the initial discrepancy cube from shared segment lane images. -/
@[noinline, nospecialize] def initialImage {p : Nat} (x : E)
    (output : Fin (2 ^ (p + 4)) → Fin 25 → E) (q : Witness p) : Vector E (2 ^ (p + 10)) :=
  let lanes := Vector.ofFn fun b : Fin (2 ^ (p + 4)) => Vector.ofFn fun m : Fin 2 => segmentLanes x q b m
  Vector.ofFn (initialCube (initialErrorWith x output q (fun b m l => ((lanes[b.val])[m.val])[l.val])))

/-- The materialized initial discrepancy preserves every authored table entry. -/
theorem initialImage_get {p : Nat} (x : E)
    (output : Fin (2 ^ (p + 4)) → Fin 25 → E) (q : Witness p)
    (w : Fin (2 ^ (p + 10))) :
    (initialImage x output q)[w.val] = initialTable x output q w := by
  let lanes := Vector.ofFn fun b : Fin (2 ^ (p + 4)) => Vector.ofFn fun m : Fin 2 => segmentLanes x q b m
  have same : (fun b m l => ((lanes[b.val])[m.val])[l.val]) = segmentLane x q := by
    funext b m l
    simpa only [lanes, Vector.getElem_ofFn] using segmentLanes_get x q b m l
  change (Vector.ofFn (initialCube (initialErrorWith x output q
    (fun b m l => ((lanes[b.val])[m.val])[l.val]))))[w.val] = _
  rw [Vector.getElem_ofFn, same]
  exact initialCube_error x output q w
end CompStark.Keccak.Gkr
