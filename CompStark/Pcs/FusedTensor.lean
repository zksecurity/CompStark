/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Copyright (c) 2026 leanEthereum.
Adapted from leanEthereum/leanMultisig, crates/pcs/src/stack_open/basis.rs and whir.rs.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.FusedPairs
public import CompStark.Pcs.WindowScatter

/-! Shared high-pattern coefficients with on-demand block reconstruction. -/
@[expose] public section
namespace CompStark.Pcs
open BF64
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxHeartbeats 1000000
attribute [local irreducible] Word.toField WordExt3.toField

/-- Shared low windows, high coefficients and ring byte map for a final tensor lift. -/
structure TensorLiftPlan (low high : Nat) where
  /-- Number of distinct low patterns. -/
  patterns : Nat
  /-- Occupied low patterns. -/
  windows : Vector (BasisWindow low) patterns
  /-- Aggregated point coefficients for each high block. -/
  coefficients : Vector (Vector WordExt3 patterns) high
  /-- Prepared ring-coordinate map. -/
  binary : Vector (Vector WordExt3 256) 24
  /-- Nonzero point-pattern indices retained once per high block. -/
  live : Vector (Array (Fin patterns)) high
  /-- Every nonzero coefficient occurs once in its high block's live list. -/
  live_eq : ∀ h : Fin high, live[h.val] =
    ((List.finRange patterns).filter fun p => decide (coefficients[h.val][p.val] ≠ 0)).toArray

/-- Filter a materialized coefficient row without rebuilding its parent matrix in the predicate. -/
@[noinline] def liveTensorPatterns {patterns : Nat} (coefficients : Vector WordExt3 patterns) :
    Array (Fin patterns) :=
  ((List.finRange patterns).filter fun p =>
    decide (coefficients[p.val] ≠ (⟨⟨0⟩,⟨0⟩,⟨0⟩⟩ : WordExt3))).toArray

/-- Group scalar contributions by their retained low-pattern key. -/
def patternCoefficients (patterns count : Nat) (keys : Vector (Fin patterns) count)
    (f : Fin count → WordExt3) : Vector WordExt3 patterns :=
  Vector.ofFn fun p => sumExt count fun t => if keys[t.val] = p then f t else 0

/-- Scatter each contribution once into its shared pattern accumulator. -/
@[specialize] def patternScatter (patterns count : Nat) (keys : Vector (Fin patterns) count)
    (f : Fin count → WordExt3) (left : Nat) (bound : left ≤ count)
    (out : Vector WordExt3 patterns) : Vector WordExt3 patterns :=
  match left with
  | 0 => out
  | left+1 =>
    let key := keys[left]
    patternScatter patterns count keys f left (by omega)
      (out.set key (WordExt3.add out[key] (f ⟨left,by omega⟩)))
termination_by structural left

/-- Scattering retains the complete sum for every pattern, including duplicate keys. -/
theorem patternScatter_refines (patterns count : Nat) (keys : Vector (Fin patterns) count)
    (f : Fin count → WordExt3) (left : Nat) (bound : left ≤ count)
    (out : Vector WordExt3 patterns) (p : Fin patterns) :
    (patternScatter patterns count keys f left bound out)[p].toField = out[p].toField +
      ∑ t : Fin left, if keys[t.val] = p then (f ⟨t.val,by omega⟩).toField else 0 := by
  induction left generalizing out with
  | zero =>
    rw [patternScatter]
    simp only [Fin.sum_univ_zero, add_zero]
  | succ left ih =>
    rw [patternScatter, ih, Fin.sum_univ_castSucc]
    simp only [Fin.getElem_fin, Vector.getElem_set, Fin.val_castSucc, Fin.val_last]
    by_cases same : keys[left].val = p.val
    · have equal : keys[left] = p := Fin.ext same
      simp only [equal, ite_true, WordExt3.toField_add]
      ac_rfl
    · have different : keys[left] ≠ p := fun e => same (congrArg Fin.val e)
      simp only [same, different, ite_false, add_zero]

/-- Aggregate pattern coefficients in one pass through the point terms. -/
def patternCoefficientsScatter (patterns count : Nat) (keys : Vector (Fin patterns) count)
    (f : Fin count → WordExt3) : Vector WordExt3 patterns :=
  patternScatter patterns count keys f count (Nat.le_refl _) (Vector.replicate patterns 0)

/-- Keyed accumulation equals the complete filtered finite sums. -/
@[csimp] theorem patternCoefficients_code : patternCoefficients = patternCoefficientsScatter := by
  funext patterns count keys f
  apply Vector.ext
  intro p hp
  apply WordExt3.toField_injective
  rw [show (patternCoefficientsScatter patterns count keys f)[p].toField = _ from
    patternScatter_refines patterns count keys f count (Nat.le_refl _) (Vector.replicate patterns 0) ⟨p,hp⟩]
  have z : (0 : WordExt3).toField = 0 := map_zero WordExt3.ringEquiv
  simp only [patternCoefficients, Vector.getElem_ofFn, sumExt_toField, Fin.getElem_fin,
    Vector.getElem_replicate, z, zero_add, apply_ite]

/-- Retain one coefficient for each distinct low pattern and high block. -/
def prepareTensorLift (low high count : Nat) (windows : Vector (BasisWindow low) count)
    (gamma : Vector (Vector WordExt3 high) count) (a : Vector WordExt3 (count+192)) :
    TensorLiftPlan low high :=
  let unique := windows.toList.dedup
  let keys := tensorPatternKeys windows
  let coefficients := Vector.ofFn (fun h : Fin high =>
    patternCoefficients unique.length count keys (fun t => roundProduct a[t.val] gamma[t.val][h.val]))
  let live := coefficients.map liveTensorPatterns
  { patterns := unique.length
    windows := unique.toArray.toVector
    coefficients := coefficients
    binary := prepareCoordinates (Vector.ofFn fun bit : Fin 192 => a[count+bit.val])
    live := live
    live_eq := by intro h; simp only [live, Vector.getElem_map, liveTensorPatterns]; rfl }

private theorem sum_array_indices {α A : Type} [AddCommMonoid A] (a : Array α) (f : α → A) :
    (∑ i : Fin a.size, f a[i.val]) = (a.toList.map f).sum := by
  conv_rhs => rw [← Array.ofFn_getElem (xs := a)]
  simp only [Array.toList_ofFn, List.map_ofFn, Function.comp_apply, List.sum_ofFn]

private theorem live_pattern_sum {low patterns : Nat} (ws : Vector (BasisWindow low) patterns)
    (coefficients : Vector WordExt3 patterns) (xs : List (Fin patterns)) (x : Fin low) :
    (((xs.filter fun p => decide (coefficients[p.val] ≠ 0)).map fun p =>
      coefficients[p.val].toField * ws[p.val].expand[x.val].toField).sum) =
      (xs.map fun p => coefficients[p.val].toField * ws[p.val].expand[x.val].toField).sum := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    by_cases zero : coefficients[p.val] = 0
    · have z : (0 : WordExt3).toField = 0 := map_zero WordExt3.ringEquiv
      simp only [List.filter_cons, zero, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, ite_false, List.map_cons, List.sum_cons, z, zero_mul, zero_add, ih]
    · simp only [List.filter_cons, zero, ne_eq, not_false_eq_true, decide_true,
        ite_true, List.map_cons, List.sum_cons, ih]

/-- Reconstruct one point-weight coordinate, reducing only after all live patterns. -/
@[inline] def TensorLiftPlan.pointAt {low high : Nat} (plan : TensorLiftPlan low high)
    (h : Fin high) (x : Fin low) : WordExt3 :=
  mixedWideLoop plan.live[h.val].size (fun q =>
    let p := plan.live[h.val][q.val]
    let w := plan.windows[p.val]
    if inside : w.start ≤ x.val ∧ x.val < w.start+w.count then
      MixedWide.mul plan.coefficients[h.val][p.val] w.values[x.val-w.start]
    else ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩)
    plan.live[h.val].size (Nat.le_refl _) 0 0 0 0 0 0

/-- Deferred live-pattern reconstruction retains the complete low-coordinate sum. -/
theorem TensorLiftPlan.pointAt_refines {low high : Nat} (plan : TensorLiftPlan low high)
    (h : Fin high) (x : Fin low) :
    (plan.pointAt h x).toField = ∑ p : Fin plan.patterns,
      plan.coefficients[h.val][p.val].toField * plan.windows[p.val].expand[x.val].toField := by
  rw [TensorLiftPlan.pointAt, mixedWideLoop_refines, MixedWide.reduce_zero]
  have z : (0 : WordExt3).toField = 0 := map_zero WordExt3.ringEquiv
  rw [z, zero_add]
  calc
    _ = ∑ q : Fin plan.live[h.val].size,
        plan.coefficients[h.val][plan.live[h.val][q.val].val].toField *
          plan.windows[plan.live[h.val][q.val].val].expand[x.val].toField := by
      apply Finset.sum_congr rfl
      intro q _
      simp only [BasisWindow.expand, Vector.getElem_ofFn]
      split
      · simp only [MixedWide.reduce_mul, WordExt3.toField_mul]
      · have zz : (⟨⟨0⟩,⟨0⟩,⟨0⟩⟩ : WordExt3).toField = 0 := z
        simp only [MixedWide.reduce_zero, z, zz, mul_zero]
    _ = _ := by
      rw [sum_array_indices (plan.live[h.val]) (fun p : Fin plan.patterns =>
        plan.coefficients[h.val][p.val].toField * plan.windows[p.val].expand[x.val].toField), plan.live_eq]
      rw [live_pattern_sum, ← List.ofFn_eq_map, List.sum_ofFn]

/-- Evaluate the point and ring weight while its survivor block is resident. -/
@[inline] def TensorLiftPlan.weightAt {cols low high : Nat} (plan : TensorLiftPlan low high)
    (shape : cols = high*low) (ring : Vector WordExt3 cols) (i : Fin cols) : WordExt3 :=
  WordExt3.add (plan.pointAt (i.cast shape).divNat (i.cast shape).modNat)
    (applyCoordinateBytes plan.binary ring[i.val])

/-- Fuse a materialized tensor plan with witness contraction at a retained physical stride. -/
@[noinline] def materializeTensorPairs (lanes cols rows low high : Nat)
    (shape : cols = high*low) (size : 2*rows = cols)
    (words : Vector Word (lanes*cols)) (mixed : MixedDotPlan lanes)
    (lifted : TensorLiftPlan low high) (ring : Vector WordExt3 cols) : PairSurvivors rows :=
  materializePairs rows
    (fun i => dotMixedPlan mixed fun lane => words[basisAddress lane (i.cast size)])
    (fun i => lifted.weightAt shape ring (i.cast size))

/-- On-demand weight reconstruction equals the complete tensor lift at every coordinate. -/
theorem prepareTensorLift_weightAt (cols low high count : Nat) (shape : cols = high*low)
    (windows : Vector (BasisWindow low) count) (gamma : Vector (Vector WordExt3 high) count)
    (ring : Vector WordExt3 cols) (a : Vector WordExt3 (count+192)) (i : Fin cols) :
    (prepareTensorLift low high count windows gamma a).weightAt shape ring i =
      (liftTensorPointBinary cols low high count shape windows gamma ring a)[i.val] := by
  apply WordExt3.toField_injective
  simp only [TensorLiftPlan.weightAt, WordExt3.toField_add, TensorLiftPlan.pointAt_refines,
    prepareTensorLift, patternCoefficients, liftTensorPointBinary, tensorWeightedWindows_code, tensorWeightedWindowsShared, Vector.getElem_ofFn,
    sumExt_toField, scaleTensorWindow_refines, Fin.getElem_fin]
  rfl

end CompStark.Pcs
