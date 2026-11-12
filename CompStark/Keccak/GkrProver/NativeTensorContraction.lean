/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.NativeTensor

/-! Interpolation semantics of all equality-weighted production tensor endpoints. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak BF64
open scoped BigOperators

/-- Endpoint interpolation commutes with every finite sum of endpoint tables. -/
theorem tensorInterpolate_finset_sum {A : Type} (indices : Finset A) (f : A → Nat → W)
    (point : List W) (row : Nat) :
    tensorInterpolate point (fun i => ∑ a ∈ indices,f a i) row =
      ∑ a ∈ indices,tensorInterpolate point (f a) row := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,tensorInterpolate_zero]
  | @insert a indices ha ih =>
    simp only [Finset.sum_insert ha,tensorInterpolate_add,ih]

/-- Interpolating a complete compact native chi tensor gives its lifted Boolean-factor expression. -/
theorem tensorInterpolate_mixedTensor (s : W) (state : Array UInt64) (groups base : Nat)
    (a b c : Fin 1600) (kappa : W) (point : Array W) (hp : point.size = 4) :
    tensorInterpolate point.toList
      (fun i => mixedTensorEntry s state groups base a b c kappa ⟨i%81,Nat.mod_lt _ (by decide)⟩) 0 =
      kappa*binaryInterpolate point.toList (tensorFactor s state groups base a) 0 +
        (kappa+binaryInterpolate point.toList (tensorFactor s state groups base b) 0)*
          binaryInterpolate point.toList (tensorFactor s state groups base c) 0 := by
  rw [← tensorInterpolate_chi]
  apply tensorInterpolate_congr
  intro i _ hi
  have hi81 : i < 81 := by simpa only [Array.length_toList,hp,Nat.zero_add,Nat.mul_one,Nat.reducePow] using hi
  rw [mixedTensorEntry_eq]
  simp only [Array.length_toList,hp,Nat.mod_eq_of_lt hi81]

/-- The actual production tensor contracts to the complete equality-weighted native pack chi expression. -/
theorem bindEarly_nativeTensor (w : SlicedWitness) (hn : 8 ≤ w.nLog) (d : Nat) (claim : Claim)
    (s : W) (point : Array W) (hp : point.size = 4) :
    (bindEarly
      (earlyValues w d claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
        prepareRmfeProducts (binaryValues (product w d claim prepareRmfeProducts).packs claim.point
          (CompStark.Sumcheck.prepare s))) point)[0]! =
      ∑ m ∈ Finset.range 2, ∑ b ∈ Finset.range (2^(w.nLog-4)/16),
        (eqTable (claim.point.extract 4 claim.point.size))[m*(2^(w.nLog-4)/16)+b]! *
          ∑ j : Fin 1600, claim.weights[j.val]! *
            ((sum (instanceWeights s))*binaryInterpolate point.toList
                (tensorFactor s w.layers[12*(m+1)-d]! (2^w.nLog/64) (16*b) j) 0 +
              ((sum (instanceWeights s))+binaryInterpolate point.toList
                (tensorFactor s w.layers[12*(m+1)-d]! (2^w.nLog/64) (16*b) (Gkr.along j 1)) 0)*
                binaryInterpolate point.toList
                  (tensorFactor s w.layers[12*(m+1)-d]! (2^w.nLog/64) (16*b) (Gkr.along j 2)) 0) := by
  rw [earlyValues_eq_nativeTensor w hn,bindEarly_get _ point 1
    (by rw [Array.size_ofFn,hp]; decide) 0 (by decide)]
  trans tensorInterpolate point.toList
    (fun i => nativeTensorEntry w d claim s ⟨i%81,Nat.mod_lt _ (by decide)⟩) 0
  · apply tensorInterpolate_congr
    intro i _ hi
    have hi81 : i < 81 := by simpa only [Array.length_toList,hp,Nat.zero_add,Nat.mul_one,Nat.reducePow] using hi
    rw [getElem!_pos _ _ (by rw [Array.size_ofFn]; exact hi81),Array.getElem_ofFn]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt hi81).symm
  · unfold nativeTensorEntry
    simp only [tensorInterpolate_finset_sum,tensorInterpolate_scale,
      tensorInterpolate_mixedTensor s _ _ _ _ _ _ _ point hp]

end CompStark.Keccak.GkrProver
