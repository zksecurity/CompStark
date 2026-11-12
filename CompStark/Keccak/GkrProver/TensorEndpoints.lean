/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.ProductVertices

/-! Common finite and infinity endpoint semantics of the native early-pack tensor. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak BF64
open scoped BigOperators

/-- The Boolean pack selected by a finite compact tensor assignment. -/
def ternaryVertex (q : Fin 81) (hq : (ternaryPlan[q.val]!).2 = 81) : Fin 16 :=
  ⟨(ternaryPlan[q.val]!).1,by
    have h := ternaryPlan_semantics q
    rw [ite_eq_left hq] at h
    exact h.1⟩

/-- A finite native tensor endpoint is the chi expression on its selected Boolean pack. -/
theorem mixedTensorEntry_finite (s : W) (state : Array UInt64) (groups base : Nat)
    (a b c : Fin 1600) (kappa : W) (q : Fin 81) (hq : (ternaryPlan[q.val]!).2 = 81) :
    mixedTensorEntry s state groups base a b c kappa q =
      kappa*rmfeValue s (tensorVertices state groups base a (ternaryVertex q hq)) +
        (kappa+rmfeValue s (tensorVertices state groups base b (ternaryVertex q hq)))*
          rmfeValue s (tensorVertices state groups base c (ternaryVertex q hq)) := by
  unfold mixedTensorEntry
  rw [ite_eq_left hq]
  have hvalue (j : Fin 1600) : rmfeValue s (lane (readUDWord (mixedEmbeddings state groups base)
      (1600*q.val+j.val).toUSize).toUInt64) =
      rmfeValue s (tensorVertices state groups base j (ternaryVertex q hq)) := by
    rw [mixedEmbeddings_value,ternaryValue_binary _ q hq]
    rfl
  dsimp only
  rw [hvalue a,hvalue b,hvalue c]

/-- A retained product row evaluates to the exact finite endpoint of the production compact tensor. -/
theorem productRow_eval_finiteTensor (w : SlicedWitness) (d : Nat) (claim : Claim) (s : W)
    (m base : Nat) (q : Fin 81) (hq : (ternaryPlan[q.val]!).2 = 81) :
    evaluatePackedLoop (productRow w d claim prepareRmfeProducts m (base+(ternaryVertex q hq).val))
      (CompStark.Sumcheck.prepare s)
      (productRow w d claim prepareRmfeProducts m (base+(ternaryVertex q hq).val)).size 0 =
      ∑ j : Fin 1600, claim.weights[j.val]! *
        mixedTensorEntry s w.layers[12*(m+1)-d]! (2^w.nLog/64) base
          j (Gkr.along j 1) (Gkr.along j 2) (sum (instanceWeights s)) q := by
  rw [productRow_eval_vertices]
  simp only [mixedTensorEntry_finite s _ _ _ _ _ _ _ q hq,kappa_eq_rmfeValue]

/-- A nonfinite native tensor endpoint contains exactly its quadratic product contribution. -/
theorem tensorColumnProduct_infinity (weights : Array W) (s : W) (state : Array UInt64)
    (groups base : Nat) (j : Fin 1600) (kappa : W) (q : Fin 81)
    (hq : (ternaryPlan[q.val]!).2 ≠ 81) :
    tensorColumnProduct weights s state groups base j q = weights[j.val]! *
      mixedTensorEntry s state groups base j (Gkr.along j 1) (Gkr.along j 2) kappa q := by
  unfold tensorColumnProduct mixedTensorEntry
  rw [ite_eq_right hq]
  simp only [mixedEmbeddings_rmfeValue]
  unfold tensorFactor
  ring

end CompStark.Keccak.GkrProver
