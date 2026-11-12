/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.TensorSuffix

/-! Exact native chi evaluations authored by the four early pack cofactor rounds. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 100000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak BF64
open scoped BigOperators

/-- The equality-weighted native chi summand after binding the four low pack coordinates. -/
noncomputable def nativeTensorValue (w : SlicedWitness) (d : Nat) (claim : Claim) (s : W)
    (point : Array W) : W :=
  ∑ m ∈ Finset.range 2, ∑ b ∈ Finset.range (2^(w.nLog-4)/16),
    (eqTable (claim.point.extract 4 claim.point.size))[m*(2^(w.nLog-4)/16)+b]! *
      ∑ j : Fin 1600, claim.weights[j.val]! *
        ((sum (instanceWeights s))*binaryInterpolate point.toList
            (tensorFactor s w.layers[12*(m+1)-d]! (2^w.nLog/64) (16*b) j) 0 +
          ((sum (instanceWeights s))+binaryInterpolate point.toList
            (tensorFactor s w.layers[12*(m+1)-d]! (2^w.nLog/64) (16*b) (Gkr.along j 1)) 0)*
              binaryInterpolate point.toList
                (tensorFactor s w.layers[12*(m+1)-d]! (2^w.nLog/64) (16*b) (Gkr.along j 2)) 0)

attribute [local irreducible] earlyValues prepareWeightMaps prepareRmfeProducts product binaryValues

/-- Interpolation of the actual complete tensor is the exact weighted native chi summand. -/
theorem earlyValues_interpolate (w : SlicedWitness) (hn : 8 ≤ w.nLog) (d : Nat) (claim : Claim)
    (s : W) (point : Array W) (hp : point.size = 4) :
    tensorInterpolate point.toList
      (fun i => (earlyValues w d claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
        prepareRmfeProducts (binaryValues (product w d claim prepareRmfeProducts).packs claim.point
          (CompStark.Sumcheck.prepare s)))[i]!) 0 = nativeTensorValue w d claim s point := by
  have hs : (earlyValues w d claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
      prepareRmfeProducts (binaryValues (product w d claim prepareRmfeProducts).packs claim.point
        (CompStark.Sumcheck.prepare s))).size = 81 := by
    rw [earlyValues_eq_nativeTensor w hn,Array.size_ofFn]
  rw [← bindEarly_get _ point 1 (by rw [hs,hp]; decide) 0 (by decide)]
  exact bindEarly_nativeTensor w hn d claim s point hp

/-- A bound prefix, a fresh coordinate and a Boolean suffix occupy exactly four pack coordinates. -/
def earlyFullPoint (bound : Array W) (r : W) (row : Nat) : Array W :=
  (bound.toList++[r]++booleanSuffix row (3-bound.size)).toArray

/-- Every early-round complete point has the exact four-coordinate tensor dimension. -/
theorem earlyFullPoint_size (bound : Array W) (hb : bound.size ≤ 3) (r : W) (row : Nat) :
    (earlyFullPoint bound r row).size = 4 := by
  simp only [earlyFullPoint,List.size_toArray,List.length_append,Array.length_toList,
    List.length_singleton,booleanSuffix_length]
  omega

/-- All four early production pack rounds evaluate the complete equality-weighted native chi expression. -/
theorem earlyRound_native_evaluate (w : SlicedWitness) (hn : 8 ≤ w.nLog) (d : Nat) (claim : Claim)
    (s : W) (bound : Array W) (hb : bound.size ≤ 3) (r : W) :
    let values := earlyValues w d claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
      prepareRmfeProducts (binaryValues (product w d claim prepareRmfeProducts).packs claim.point
        (CompStark.Sumcheck.prepare s))
    (earlyRound values claim.point bound)[0]!+
      r*((earlyRound values claim.point bound)[1]!+r*(earlyRound values claim.point bound)[2]!) =
        ∑ row ∈ Finset.range (eqTable (claim.point.extract (bound.size+1) 4)).size,
          (eqTable (claim.point.extract (bound.size+1) 4))[row]! *
            nativeTensorValue w d claim s (earlyFullPoint bound r row) := by
  dsimp only
  rw [earlyRound_evaluate_suffix _ _ _ (by rw [earlyValues_eq_nativeTensor w hn,Array.size_ofFn]) hb]
  apply Finset.sum_congr rfl
  intro row _
  apply congrArg (fun value : W => (eqTable (claim.point.extract (bound.size+1) 4))[row]!*value)
  have heq := earlyValues_interpolate w hn d claim s (earlyFullPoint bound r row)
    (earlyFullPoint_size bound hb r row)
  simpa only [earlyFullPoint,List.toList_toArray] using heq

end CompStark.Keccak.GkrProver
