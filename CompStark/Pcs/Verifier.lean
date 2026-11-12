/-
Copyright (c) 2026 zkSecurity.
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompStark.Pcs.Weights
public import CompStark.Pcs.AdditiveEncoding
public import ArkLib.ProofSystem.Whir.Protocol

/-! The WHIR verifier with shared batching powers and materialized prefix folds. -/

set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

@[expose] public section
namespace CompStark.Pcs
open CompStark.BinaryFields

/-- Numeric inner product with zero products and summands omitted. -/
def innerProduct {n : Nat} (first second : Whir.Table E n) : E :=
  sparseSum ((List.finRange (2 ^ n)).map fun i => sparseMul (first (mask n i)) (second (mask n i)))

/-- Numeric sparse accumulation equals the Boolean-function inner product. -/
theorem innerProduct_eq {n : Nat} (first second : Whir.Table E n) :
    innerProduct first second = ∑ u, first u * second u := by
  simp only [innerProduct, sparseSum_eq, sparseMul_eq]
  rw [← List.ofFn_eq_map, Fin.sum_ofFn]
  simpa only [cubeEquiv_apply] using (cubeEquiv n).sum_comp (fun u => first u * second u)

/-- MLE evaluation with its equality tensor shared across all entries. -/
def mleCached {n : Nat} (table : Whir.Table E n) (point : Fin n → E) : E :=
  innerProduct (cachedEqWeight point) table

/-- The cached evaluator agrees with the WHIR multilinear extension. -/
theorem mleCached_eq {n : Nat} (table : Whir.Table E n) (point : Fin n → E) :
    mleCached table point = Whir.mle table point := by
  simp only [mleCached, innerProduct_eq, cachedEqWeight_eq, Whir.mle]

/-- Prefix folding materializes its result once, sharing the prefix equality tensor. -/
@[macro_inline] def restrictCached {count tail : Nat} (table : Whir.Table E (count + tail))
    (point : Fin count → E) : Whir.Table E tail :=
  let weights := cachedEqWeight point
  let image := Vector.ofFn fun i : Fin (2 ^ tail) =>
    innerProduct weights (fun u => table (Fin.addCases u (mask tail i)))
  fun u => image[(cubeEquiv tail).symm u]

/-- Materialized prefix folding is the original restriction operation. -/
theorem restrictCached_eq {count tail : Nat} (table : Whir.Table E (count + tail))
    (point : Fin count → E) : restrictCached table point = Whir.restrict table point := by
  funext u
  have same : mask tail ((cubeEquiv tail).symm u) = u := (cubeEquiv tail).apply_symm_apply u
  simp only [restrictCached, Fin.getElem_fin, Vector.getElem_ofFn]
  rw [same, innerProduct_eq, cachedEqWeight_eq]
  rfl

/-- Compute all scalar batching powers once before the repeated weight lookups. -/
@[macro_inline] def batchCached {n : Nat} (claims : List (Whir.Claim E n)) (r : E) : Whir.Claim E n :=
  let terms := claims.zipIdx.map fun (claim, index) => (r ^ index, claim)
  ⟨fun u => sparseSum (terms.map fun term => sparseMul term.1 (term.2.weight u)),
    sparseSum (terms.map fun term => sparseMul term.1 term.2.value)⟩

/-- Shared powers and sparse arithmetic preserve the exact batching claim. -/
theorem batchCached_eq {n : Nat} (claims : List (Whir.Claim E n)) (r : E) :
    batchCached claims r = Whir.batch claims r := by
  simp only [batchCached, Whir.batch, sparseSum_eq, List.map_map, Function.comp_def, sparseMul_eq]

/-- Verify the exact WHIR transcript with cached batches and prefix folds. -/
def acceptsCached (ι : K →+* E) : {n : Nat} → (schedule : Whir.Schedule K n) →
    Whir.oracleMessage E schedule → List (Whir.Claim E n) →
    (Whir.opening E schedule).tree.ExecutionPath → Bool
  | _, .last lanes tail enc queries, word, claims, path =>
      let batched := batchCached claims path.1
      let round := Whir.readRounds (Whir.transition E (.last lanes tail enc queries))
        lanes batched.value path.2
      let residual : Whir.Claim E tail := ⟨restrictCached batched.weight round.2.1, round.1⟩
      let finalTable := round.2.2.2.1
      let xs := round.2.2.2.2.1
      let finalClaims := residual :: List.ofFn (fun q : Fin queries =>
        (⟨queryWeightCached enc ι (xs q), (Whir.foldMaskedWord word round.2.1 (xs q)).getD 0⟩ : Whir.Claim E tail))
      let finalBatch := batchCached finalClaims round.2.2.2.2.2.1
      let closing := Whir.readRounds .done tail finalBatch.value round.2.2.2.2.2.2
      round.2.2.1 && Whir.queriesKnown word xs && closing.2.2.1 &&
        decide (mleCached finalBatch.weight closing.2.1 * mleCached finalTable closing.2.1 = closing.1)
  | _, .more lanes enc queries rest, word, claims, path =>
      let batched := batchCached claims path.1
      let round := Whir.readRounds (Whir.transition E (.more lanes enc queries rest))
        lanes batched.value path.2
      let residual := ⟨restrictCached batched.weight round.2.1, round.1⟩
      let after := round.2.2.2
      let claims' := Whir.nextClaimsPrepared enc ι residual after.2.1 after.2.2.1 after.2.2.2.1
        (fun x => (Whir.foldMaskedWord word round.2.1 x).getD 0)
      round.2.2.1 && Whir.queriesKnown word after.2.2.2.1 && acceptsCached ι rest after.1 claims' after.2.2.2.2

/-- Cached verification agrees with every original WHIR acceptance decision. -/
theorem acceptsCached_eq (ι : K →+* E) {n : Nat} (schedule : Whir.Schedule K n)
    (word : Whir.oracleMessage E schedule) (claims : List (Whir.Claim E n))
    (path : (Whir.opening E schedule).tree.ExecutionPath) :
    acceptsCached ι schedule word claims path = Whir.accepts ι schedule word claims path := by
  induction schedule with
  | last lanes tail enc queries =>
    rw [acceptsCached, Whir.accepts]
    simp only [batchCached_eq, restrictCached_eq, mleCached_eq, queryWeightCached_eq]
  | more lanes enc queries rest ih =>
    rw [acceptsCached, Whir.accepts]
    simp only [batchCached_eq, restrictCached_eq, ← Whir.nextClaims_code, ih]

end CompStark.Pcs
