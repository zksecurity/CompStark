/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.ExtractorCache

/-! Independent retained-claim checks over one shared sparse candidate. -/

set_option autoImplicit false
@[expose] public section
namespace CompStark.Pcs
open CompStark.BinaryFields
/-- Add a nonzero weighted product without allocating a field-valued intermediate. -/
@[inline] def accumulateWordProduct (acc : BF64.WordExt3) (a b : E) : BF64.WordExt3 :=
  let word := BF64.WordExt3.ofField a
  if word = (⟨⟨0⟩, ⟨0⟩, ⟨0⟩⟩ : BF64.WordExt3) then acc else acc + word * BF64.WordExt3.ofField b

/-- The streaming word step is exactly ordinary multiply-add over the specification field. -/
theorem accumulateWordProduct_eq (acc : BF64.WordExt3) (a b : E) :
    (accumulateWordProduct acc a b).toField = acc.toField + a*b := by
  have projection (x : BF64.WordExt3) : BF64.WordExt3.ringEquiv x = x.toField := rfl
  have literal : (⟨⟨0⟩, ⟨0⟩, ⟨0⟩⟩ : BF64.WordExt3) = 0 := rfl
  dsimp only [accumulateWordProduct]
  split_ifs with zero
  · have a_zero : a = 0 := by
      calc
        a = (BF64.WordExt3.ofField a).toField := (BF64.WordExt3.toField_ofField a).symm
        _ = (0 : BF64.WordExt3).toField := congrArg BF64.WordExt3.toField (zero.trans literal)
        _ = 0 := map_zero BF64.WordExt3.ringEquiv
    simp only [a_zero, zero_mul, add_zero]
  · change BF64.WordExt3.ringEquiv (_ + _ * _) = _
    rw [map_add, map_mul]
    simp only [projection, BF64.WordExt3.toField_ofField]

/-- Sum retained products in a streaming machine-word accumulator. -/
def entriesInnerProductWords {n : Nat} (weight : Whir.Table E n) (entries : List (Fin (2^n) × E)) : E :=
  BF64.WordExt3.toField (entries.foldl (fun acc entry =>
    accumulateWordProduct acc (weight (mask n entry.1)) entry.2) 0)
/-- Streaming word products preserve the sparse field inner product. -/
theorem entriesInnerProductWords_eq {n : Nat} (weight : Whir.Table E n) (entries : List (Fin (2^n) × E)) :
    entriesInnerProductWords weight entries = entriesInnerProduct weight entries := by
  have projection (x : BF64.WordExt3) : BF64.WordExt3.ringEquiv x = x.toField := rfl
  have loop (ys : List (Fin (2^n) × E)) (acc : BF64.WordExt3) :
      BF64.WordExt3.ringEquiv (ys.foldl (fun acc entry =>
        accumulateWordProduct acc (weight (mask n entry.1)) entry.2) acc) =
      acc.toField + entriesInnerProduct weight ys := by
    induction ys generalizing acc with
    | nil =>
      simp only [List.foldl_nil, entriesInnerProduct, List.map_nil, sparseSum,
        List.foldr_nil, add_zero, projection]
    | cons entry ys ih =>
      rw [List.foldl_cons, ih]
      simp only [accumulateWordProduct_eq,
        entriesInnerProduct, List.map_cons, sparseSum, List.foldr_cons,
        sparseAdd_eq, sparseMul_eq]
      exact add_assoc _ _ _
  have zero : (0 : BF64.WordExt3).toField = 0 := map_zero BF64.WordExt3.ringEquiv
  simpa only [entriesInnerProductWords, projection, zero, zero_add] using loop entries 0
/-- Check retained claims over one shared sparse candidate without product lists. -/
@[noinline, nospecialize] def entriesClaimsCheckParallel {n : Nat}
    (claims : List (Whir.Claim E n)) (entries : List (Fin (2^n) × E)) : Bool :=
  let checks := claims.map fun claim => Task.spawn fun _ =>
    decide (entriesInnerProductWords claim.weight entries = claim.value)
  checks.all Task.get

/-- Validate independent retained claims in tasks over one shared sparse candidate image. -/
def imageClaimsCheckParallel {n : Nat} (claims : List (Whir.Claim E n))
    (image : Vector E (2 ^ n)) : Bool :=
  entriesClaimsCheckParallel claims (nonzeroEntries image (List.finRange (2 ^ n)))
/-- Parallel retained checks preserve the complete original conjunction. -/
theorem imageClaimsCheckParallel_eq {n : Nat} (claims : List (Whir.Claim E n))
    (image : Vector E (2 ^ n)) :
    imageClaimsCheckParallel claims image = imageClaimsCheck claims image := by
  simp only [imageClaimsCheckParallel, entriesClaimsCheckParallel, List.all_map, Task.spawn, entriesInnerProductWords_eq,
    entriesInnerProduct_nonzeroEntries, imageClaimsCheck, imageInnerProduct]
  rfl
end CompStark.Pcs
