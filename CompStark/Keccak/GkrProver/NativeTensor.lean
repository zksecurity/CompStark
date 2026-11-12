/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.BinaryTensor

/-! Complete production tensor semantics, including retained finite endpoints. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 100000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak BF64
open scoped BigOperators

/-- The pack domain splits into complete sixteen-pack tensor blocks. -/
theorem packs_eq_blocks (nLog : Nat) (hn : 8 ≤ nLog) :
    2^(nLog-4) = 16*(2^(nLog-4)/16) := by
  have hd : 16 ∣ 2^(nLog-4) := Nat.pow_dvd_pow 2 (show 4 ≤ nLog-4 by omega)
  exact (Nat.div_mul_cancel hd).symm.trans (Nat.mul_comm _ _)

/-- One complete equality-weighted chi endpoint of the early-pack tensor. -/
noncomputable def nativeTensorEntry (w : SlicedWitness) (d : Nat) (claim : Claim) (s : W) (q : Fin 81) : W :=
  ∑ m ∈ Finset.range 2, ∑ b ∈ Finset.range (2^(w.nLog-4)/16),
    (eqTable (claim.point.extract 4 claim.point.size))[m*(2^(w.nLog-4)/16)+b]! *
      ∑ j : Fin 1600, claim.weights[j.val]! *
        mixedTensorEntry s w.layers[12*(m+1)-d]! (2^w.nLog/64) (16*b)
          j (Gkr.along j 1) (Gkr.along j 2) (sum (instanceWeights s)) q

attribute [local irreducible] earlyValues prepareWeightMaps prepareRmfeProducts product binaryValues ternaryPlan

/-- Every production early-pack endpoint is its full equality-weighted native chi tensor. -/
theorem earlyValues_complete (w : SlicedWitness) (hn : 8 ≤ w.nLog) (d : Nat) (claim : Claim)
    (s : W) (q : Fin 81) :
    (earlyValues w d claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
      prepareRmfeProducts (binaryValues (product w d claim prepareRmfeProducts).packs claim.point
        (CompStark.Sumcheck.prepare s)))[q.val]! = nativeTensorEntry w d claim s q := by
  rw [earlyValues_get]
  unfold nativeTensorEntry
  by_cases hq : (ternaryPlan[q.val]!).2 = 81
  · rw [ite_eq_left hq]
    change (binaryValues (product w d claim prepareRmfeProducts).packs claim.point
      (CompStark.Sumcheck.prepare s))[(ternaryVertex q hq).val]! = _
    rw [binaryValues_product_rows w d claim s _ (packs_eq_blocks w.nLog hn)]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro b _
    rw [productRow_eval_finiteTensor w d claim s m (16*b) q hq]
  · rw [ite_eq_right hq]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro b _
    apply congrArg (fun v : W =>
      (eqTable (claim.point.extract 4 claim.point.size))[m*(2^(w.nLog-4)/16)+b]!*v)
    apply Finset.sum_congr rfl
    intro j _
    exact tensorColumnProduct_infinity claim.weights s _ _ _ j _ q hq

/-- The complete production tensor array equals the mathematical endpoint table of native chi. -/
theorem earlyValues_eq_nativeTensor (w : SlicedWitness) (hn : 8 ≤ w.nLog) (d : Nat) (claim : Claim)
    (s : W) :
    earlyValues w d claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
      prepareRmfeProducts (binaryValues (product w d claim prepareRmfeProducts).packs claim.point
        (CompStark.Sumcheck.prepare s)) = Array.ofFn (nativeTensorEntry w d claim s) := by
  have hs := (earlyValues_blocks_get w d claim
    (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s)) prepareRmfeProducts
    (binaryValues (product w d claim prepareRmfeProducts).packs claim.point
      (CompStark.Sumcheck.prepare s)) (0 : Fin 81)).1
  apply Array.ext (hs.trans Array.size_ofFn.symm)
  intro i hi hj
  rw [← getElem!_pos _ i hi,Array.getElem_ofFn]
  exact earlyValues_complete w hn d claim s ⟨i,by simpa only [Array.size_ofFn] using hj⟩

end CompStark.Keccak.GkrProver
