/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.RingSwitch.Protocol
public import CompStark.Pcs.Verifier
public import CompStark.Pcs.Tensor

/-! Honest ring-switch preparation, word targets, factored stack weights and shared claim batching. -/

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStark.Pcs.RingSwitch.Prover
open CompStark.BinaryFields

/-- The generic ordered Frobenius composition is the protocol's exact staged map. -/
theorem frobeniusMap_eq (stages : List (Nat × E)) (a : E) :
    CompStark.Pcs.frobeniusMap stages a = Pcs.RingSwitch.frobMap stages a := by
  induction stages generalizing a with
  | nil => rfl
  | cons stage stages ih => exact ih _

/-- Apply the six public maps while retaining the word carrier between stages. -/
def mapWord (fs : Vector E 6) (a : E) : BF64.WordExt3 :=
  CompStark.Pcs.binary64Map (fs.map BF64.WordExt3.ofField) (BF64.WordExt3.ofField a)

/-- Word execution agrees with all six protocol maps and their descending shifts. -/
theorem mapWord_eq (fs : Vector E 6) (a : E) :
    (mapWord fs a).toField = Pcs.RingSwitch.frobMap (Pcs.RingSwitch.ringStages fs) a := by
  rw [mapWord, CompStark.Pcs.binary64Map, CompStark.Pcs.wordMap_refines,
    BF64.WordExt3.toField_ofField, frobeniusMap_eq]
  congr 1
  simp only [CompStark.Pcs.binary64Stages, List.map_ofFn, Pcs.RingSwitch.ringStages]
  congr 1
  funext i
  simp only [Function.comp_apply, Fin.getElem_fin, Vector.getElem_map,
    BF64.WordExt3.toField_ofField]

/-- Compute the weighted target with word maps, mixed products and XOR accumulation. -/
def target {n : Nat} (statement : Pcs.RingSwitch.Statement n) (fs : Vector E 6) : E :=
  (CompStark.Pcs.sumWords ((List.finRange 64).map fun i =>
    BF64.WordExt3.mulScalar (mapWord fs (statement.values i))
      (BF64.Word.ofField (g ^ i.val)))).toField

/-- The executable target equals the protocol's target, without changing the packing basis. -/
theorem target_eq {n : Nat} (statement : Pcs.RingSwitch.Statement n) (fs : Vector E 6) :
    target statement fs = Pcs.RingSwitch.ringTarget statement fs := by
  simp only [target, CompStark.Pcs.sumWords_refines, List.map_map, Function.comp_def,
    BF64.WordExt3.toField_mulScalar, BF64.Word.toField_ofField, mapWord_eq, Algebra.smul_def]
  rw [← List.ofFn_eq_map, Fin.sum_ofFn]
  rfl

/-- Share the suffix equality tensor across all sixty-four honest slice evaluations. -/
@[macro_inline] def prepare {n m : Nat} (layout : Pcs.RingSwitch.Layout n m)
    (stack : Whir.Table K m) (point : Fin n → E) : Pcs.RingSwitch.Statement n :=
  let weights := Pcs.cachedEqWeight point
  ⟨point, fun bit => Pcs.innerProduct weights (layout.slices stack bit)⟩

/-- Preparation gives precisely the model's bit-slice multilinear evaluations. -/
theorem prepare_values {n m : Nat} (layout : Pcs.RingSwitch.Layout n m)
    (stack : Whir.Table K m) (point : Fin n → E) (bit : Fin 64) :
    (prepare layout stack point).values bit = Whir.mle (layout.slices stack bit) point := by
  simp only [prepare, Pcs.innerProduct_eq, Pcs.cachedEqWeight_eq, Whir.mle]

/-- Retain cached low/high factors for each lifted Frobenius term instead of a dense stack table. -/
@[macro_inline] def factoredWeight {n lo hi : Nat} (lift : (Fin n → E) → Fin (lo + hi) → E)
    (statement : Pcs.RingSwitch.Statement n) (fs : Vector E 6) : Whir.Table E (lo + hi) :=
  let terms := (Pcs.RingSwitch.frobTerms (Pcs.RingSwitch.ringStages fs)).map fun term =>
    (term.1, CompStark.Pcs.wordFactoredEq (lo := lo) (hi := hi)
      (lift (fun i => (BF64.WordExt3.frobenius (BF64.WordExt3.ofField (statement.point i)) term.2).toField)))
  fun u => Pcs.sparseSum (terms.map fun term => Pcs.sparseMul term.1 (term.2.eval u).toField)

/-- Every factored term equals the protocol's lifted equality weight. -/
theorem factoredWeight_eq {n lo hi : Nat} (lift : (Fin n → E) → Fin (lo + hi) → E)
    (statement : Pcs.RingSwitch.Statement n) (fs : Vector E 6) (u : Whir.Cube (lo + hi)) :
    factoredWeight lift statement fs u =
      ((Pcs.RingSwitch.frobTerms (Pcs.RingSwitch.ringStages fs)).map fun term =>
        term.1 * Whir.eqWeight (lift (fun i => statement.point i ^ 2 ^ term.2)) u).sum := by
  simp only [factoredWeight, Pcs.sparseSum_eq, List.map_map, Function.comp_def,
    Pcs.sparseMul_eq, CompStark.Pcs.wordFactoredEq_eval, BF64.WordExt3.toField_frobenius,
    BF64.WordExt3.toField_ofField]

/-- The honest opening retains its physical layout and targets the same committed stack. -/
def opening {n lo hi : Nat} (layout : Pcs.RingSwitch.Layout n (lo + hi))
    (statement : Pcs.RingSwitch.Statement n) (fs : Vector E 6) : Whir.Claim E (lo + hi) :=
  ⟨factoredWeight layout.lift statement fs, target statement fs⟩

/-- Word targets and factored weights refine the exact ring-switch protocol endpoint. -/
theorem opening_eq {n lo hi : Nat} (layout : Pcs.RingSwitch.Layout n (lo + hi))
    (statement : Pcs.RingSwitch.Statement n) (fs : Vector E 6) :
    opening layout statement fs = Pcs.RingSwitch.outputClaim layout statement fs := by
  unfold opening Pcs.RingSwitch.outputClaim
  rw [target_eq]
  congr 1
  funext u
  exact factoredWeight_eq layout.lift statement fs u

/-- An honest preparation satisfies the opening claim for every six-challenge map. -/
theorem opening_holds {n lo hi : Nat} (layout : Pcs.RingSwitch.Layout n (lo + hi))
    (stack : Whir.Table K (lo + hi)) (point : Fin n → E) (fs : Vector E 6) :
    (opening layout (prepare layout stack point) fs).Holds (fun u => ofK (stack u)) := by
  rw [opening_eq]
  change (∑ u, Pcs.RingSwitch.ringWeight layout (prepare layout stack point) fs u * ofK (stack u)) = _
  rw [← Pcs.RingSwitch.transformed_slices_eq_weighted]
  simp only [Pcs.RingSwitch.outputClaim, Pcs.RingSwitch.ringTarget, prepare_values]
  rfl

/-- Ring claims and point claims occupy disjoint consecutive powers of one batching challenge. -/
def batch {n : Nat} (rings points : List (Whir.Claim E n)) (lambda : E) : Whir.Claim E n :=
  Pcs.batchCached (rings ++ points) lambda

/-- Shared claim batching has exactly ArkLib's power order over the concatenated families. -/
theorem batch_eq {n : Nat} (rings points : List (Whir.Claim E n)) (lambda : E) :
    batch rings points lambda = Whir.batch (rings ++ points) lambda :=
  Pcs.batchCached_eq _ _

/-- True ring and point claims yield the single weighted opening used by WHIR. -/
theorem batch_holds {n : Nat} (rings points : List (Whir.Claim E n)) (lambda : E)
    (table : Whir.Table E n) (hr : ∀ c ∈ rings, c.Holds table) (hp : ∀ c ∈ points, c.Holds table) :
    (batch rings points lambda).Holds table := by
  rw [batch_eq]
  apply Whir.batch_holds
  intro c hc
  exact (List.mem_append.mp hc).elim (hr c) (hp c)

end CompStark.Pcs.RingSwitch.Prover
