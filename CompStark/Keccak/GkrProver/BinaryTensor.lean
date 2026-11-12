/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.TensorEndpoints
public import CompStark.Keccak.GkrProver.RetainedProducts

/-! Equality batching of the retained finite tensor endpoints. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak BF64
open scoped BigOperators

/-- The retained production polynomials supply exactly the equality-weighted finite pack endpoints. -/
theorem binaryValues_product_rows (w : SlicedWitness) (d : Nat) (claim : Claim) (s : W)
    (blocks : Nat) (hp : 2^(w.nLog-4) = 16*blocks) (i : Fin 16) :
    (binaryValues (product w d claim prepareRmfeProducts).packs claim.point
      (CompStark.Sumcheck.prepare s))[i.val]! =
      ∑ m ∈ Finset.range 2, ∑ b ∈ Finset.range blocks,
        (eqTable (claim.point.extract 4 claim.point.size))[m*blocks+b]! *
          evaluatePackedLoop (productRow w d claim prepareRmfeProducts m (16*b+i.val))
            (CompStark.Sumcheck.prepare s) (productRow w d claim prepareRmfeProducts m (16*b+i.val)).size 0 := by
  rw [binaryValues_rows _ _ _ (2*blocks) (by rw [product_packs_size,hp]; omega),range_sum_blocks]
  apply Finset.sum_congr rfl
  intro m hm
  have hm : m < 2 := Finset.mem_range.mp hm
  apply Finset.sum_congr rfl
  intro b hb
  have hb : b < blocks := Finset.mem_range.mp hb
  have hi := i.isLt
  have hindex : 16*(blocks*m+b)+i.val = m*2^(w.nLog-4)+(16*b+i.val) := by rw [hp]; ring
  rw [hindex,product_packs_get w d claim prepareRmfeProducts ⟨m,hm⟩ (16*b+i.val) (by rw [hp]; omega)]
  rw [Nat.mul_comm blocks m]

end CompStark.Keccak.GkrProver
