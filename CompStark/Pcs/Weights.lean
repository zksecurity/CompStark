/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import CompStark.Pcs.BinaryDomain
public import CompStark.BinaryFields.WordProduct
public import CompPoly.Fields.Binary.BF64.WordField
public import CompStark.Keccak.Gkr.Executable

/-! Shared sparse tensor weights for physical opening claims. -/

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStark.Pcs
open CompStark.BinaryFields

/-- Multiply an extension weight by a base-field word with three word products. -/
def mulBaseLimbs (a : E) (b : K) : E :=
  BF64.WordExt3.toField (BF64.WordExt3.mulScalar (BF64.WordExt3.ofField a) (BF64.Word.ofField b))

/-- The mixed three-product kernel preserves scalar extension. -/
theorem mulBaseLimbs_eq (a : E) (b : K) : mulBaseLimbs a b = a * ofK b := by
  rw [mulBaseLimbs, BF64.WordExt3.toField_mulScalar, BF64.WordExt3.toField_ofField,
    BF64.Word.toField_ofField, Algebra.smul_def, mul_comm]
  rfl

/-- Use the mixed kernel for base-field right operands and six products otherwise. -/
def mulLimbs (a b : E) : E :=
  if b.limb 1 = 0 ∧ b.limb 2 = 0 then mulBaseLimbs a (b.limb 0)
  else mulExtensionNative a b

/-- Mixed and full word products both agree with extension-field multiplication. -/
theorem mulLimbs_eq (a b : E) : mulLimbs a b = a * b := by
  unfold mulLimbs
  split_ifs with base
  · have hb := (ofLimbs_limb b).symm
    rw [base.1, base.2] at hb
    rw [mulBaseLimbs_eq]
    rw [show ofK (b.limb 0) = b from (ofK_eq_ofLimbs _).trans hb.symm]
  · exact mulExtensionNative_eq a b

/-- Multiply scalar weights while retaining shared zero and unit values. -/
def sparseMul (a b : E) : E :=
  if a = 0 then 0 else if b = 0 then 0 else if a = 1 then b else if b = 1 then a else mulLimbs a b

/-- The sparse branches preserve field multiplication. -/
theorem sparseMul_eq (a b : E) : sparseMul a b = a * b := by
  unfold sparseMul
  rw [mulLimbs_eq]
  split_ifs <;> simp_all only [zero_mul, mul_zero, one_mul, mul_one]

/-- Expand one tensor coordinate, sharing the inactive half for Boolean selectors. -/
def sparseCubeLayer {size : Nat} (previous : Vector E size) (right : E) : Vector E (size + size) :=
  if right = 0 then previous ++ Vector.replicate size (0 : E)
  else if right = 1 then Vector.replicate size (0 : E) ++ previous
  else previous.map (fun a => sparseMul a (1 - right)) ++ previous.map (fun a => sparseMul a right)

/-- Tensor expansion agrees entrywise with multiplication by the two coordinate weights. -/
theorem sparseCubeLayer_get {size : Nat} (previous : Vector E size) (right : E)
    (i : Nat) (hi : i < size + size) :
    (sparseCubeLayer previous right)[i] =
      if h : i < size then previous[i] * (1 - right)
      else previous[i - size]'(by omega) * right := by
  simp only [sparseCubeLayer]
  split_ifs <;>
    simp_all only [Vector.getElem_append, Vector.getElem_replicate, Vector.getElem_map,
      sparseMul_eq, sub_zero, mul_one, mul_zero, sub_self]

/-- Expand a tensor with zero and unit selectors without multiplying those entries. -/
def sparseCubeWeights : {n : Nat} → (Fin n → E) → Vector E (2 ^ n)
  | 0, _ => #v[1]
  | n + 1, point =>
    let previous := sparseCubeWeights (fun i : Fin n => point i.castSucc)
    (sparseCubeLayer previous (point (Fin.last n))).cast (by simp only [pow_succ]; omega)

/-- Sparse tensor expansion agrees with the generic equality-weight tensor. -/
theorem sparseCubeWeights_eq {n : Nat} (point : Fin n → E) :
    sparseCubeWeights point = Keccak.Gkr.cubeWeights point := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Vector.ext
    intro i hi
    simp only [sparseCubeWeights, Vector.getElem_cast, sparseCubeLayer_get,
      Keccak.Gkr.cubeWeights, Vector.getElem_ofFn, ih]

/-- Materialize a tensor once before repeated Boolean-coordinate lookups. -/
def cachedEqWeight {n : Nat} (point : Fin n → E) : Whir.Table E n :=
  let image := sparseCubeWeights point
  fun u => image[(cubeEquiv n).symm u]

/-- Read a shared equality tensor through its direct numeric coordinate index. -/
@[macro_inline] def cachedEqWeightDirect {n : Nat} (point : Fin n → E) : Whir.Table E n :=
  let image := sparseCubeWeights point
  fun u => image[cubeIndex n u]

/-- Numeric tensor reads preserve every Boolean-coordinate lookup. -/
@[csimp] theorem cachedEqWeight_direct : @cachedEqWeight = @cachedEqWeightDirect := rfl

/-- Shared tensor lookup is exactly the WHIR equality weight. -/
theorem cachedEqWeight_eq {n : Nat} (point : Fin n → E) :
    cachedEqWeight point = Whir.eqWeight point := by
  funext u
  simp only [cachedEqWeight, sparseCubeWeights_eq, Keccak.Gkr.cubeWeights_get,
    Keccak.Gkr.eqWeight, Whir.eqWeight]
  apply Finset.prod_congr rfl
  intro i _
  have bits := congrFun ((cubeEquiv n).apply_symm_apply u) i
  change (((cubeEquiv n).symm u).val.testBit i.val) = u i at bits
  rw [bits]

/-- Add sparse contributions while retaining shared zero values. -/
def sparseAdd (a b : E) : E := if a = 0 then b else if b = 0 then a else a + b

/-- Skipping zero contributions preserves field addition. -/
theorem sparseAdd_eq (a b : E) : sparseAdd a b = a + b := by
  unfold sparseAdd
  split_ifs <;> simp_all only [zero_add, add_zero]

/-- Sum contributions without allocating new field values for zero summands. -/
def sparseSum (values : List E) : E := values.foldr sparseAdd 0

/-- Sparse summation has exactly the ordinary list sum. -/
theorem sparseSum_eq (values : List E) : sparseSum values = values.sum := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [sparseSum, List.foldr_cons, sparseAdd_eq, List.sum_cons] at *
    rw [ih]

/-- Accumulate tensor images while retaining only the current term and the running image. -/
def tensorCombinationImage {n : Nat} (terms : List (E × (Fin n → E))) : Vector E (2 ^ n) :=
  terms.foldr (fun term accumulated =>
    let weights := sparseCubeWeights term.2
    Vector.ofFn fun i => sparseAdd (sparseMul term.1 weights[i]) accumulated[i])
    (Vector.replicate (2 ^ n) 0)

/-- The accumulated image equals the specified pointwise linear combination. -/
theorem tensorCombinationImage_get {n : Nat} (terms : List (E × (Fin n → E)))
    (i : Fin (2 ^ n)) :
    (tensorCombinationImage terms)[i] =
      (terms.map fun term => term.1 * Whir.eqWeight term.2 (mask n i)).sum := by
  have lookup (point : Fin n → E) : (sparseCubeWeights point)[i] = Whir.eqWeight point (mask n i) := by
    simpa only [cachedEqWeight, Equiv.symm_apply_apply, ← cubeEquiv_apply] using
      congrFun (cachedEqWeight_eq point) (cubeEquiv n i)
  induction terms with
  | nil => simp only [tensorCombinationImage, List.foldr_nil, Fin.getElem_fin, Vector.getElem_replicate, List.map_nil, List.sum_nil]
  | cons term terms ih =>
    simp only [tensorCombinationImage, List.foldr_cons, Fin.getElem_fin, Vector.getElem_ofFn,
      sparseAdd_eq, sparseMul_eq, List.map_cons, List.sum_cons]
    simpa only [tensorCombinationImage, Fin.getElem_fin, sparseAdd_eq, sparseMul_eq] using
      congrArg₂ (fun x y : E => term.1 * x + y) (lookup term.2) ih

/-- The word isomorphism has the same executable field projection. -/
theorem wordEquiv_apply (a : BF64.WordExt3) : BF64.WordExt3.ringEquiv a = a.toField := rfl
/-- Numeric tensor weights transported through the cubic machine-word field. -/
theorem wordCubeWeights_get {n : Nat} (point : Fin n → E) (i : Fin (2^n)) :
    BF64.WordExt3.toField ((Keccak.Gkr.cubeWeights (fun j => BF64.WordExt3.ofField (point j)))[i]) =
      (sparseCubeWeights point)[i] := by
  rw [sparseCubeWeights_eq, Keccak.Gkr.cubeWeights_get, Keccak.Gkr.cubeWeights_get]
  change BF64.WordExt3.ringEquiv (∏ j : Fin n, _) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  split_ifs <;> simp only [map_sub, map_one, wordEquiv_apply, BF64.WordExt3.toField_ofField]
/-- Accumulate tensor terms entirely in the machine-word field. -/
def tensorWords {n : Nat} (terms : List (E × (Fin n → E))) : Vector BF64.WordExt3 (2^n) :=
  terms.foldr (fun term accumulated =>
    let weights := Keccak.Gkr.cubeWeights (fun j => BF64.WordExt3.ofField (term.2 j))
    let scalar := BF64.WordExt3.ofField term.1
    accumulated.mapFinIdx fun i a hi => scalar * weights[i] + a)
    (Vector.replicate (2^n) 0)
/-- Word accumulation agrees with every entry of the tensor specification. -/
theorem tensorWords_get {n : Nat} (terms : List (E × (Fin n → E))) (i : Fin (2^n)) :
    BF64.WordExt3.toField (tensorWords terms)[i] = (tensorCombinationImage terms)[i] := by
  induction terms with
  | nil =>
    simp only [tensorWords, tensorCombinationImage, List.foldr_nil, Fin.getElem_fin,
      Vector.getElem_replicate]
    exact map_zero BF64.WordExt3.ringEquiv
  | cons term terms ih =>
    simp only [tensorWords, List.foldr_cons, Fin.getElem_fin, Vector.getElem_mapFinIdx,
      tensorCombinationImage, Vector.getElem_ofFn, sparseAdd_eq, sparseMul_eq]
    change BF64.WordExt3.ringEquiv (_ * _ + _) = _
    rw [map_add, map_mul]
    change _ * BF64.WordExt3.toField ((Keccak.Gkr.cubeWeights _)[i]) + _ = _
    rw [wordCubeWeights_get]
    simp only [wordEquiv_apply, BF64.WordExt3.toField_ofField]
    simpa only [tensorWords, tensorCombinationImage, sparseAdd_eq, sparseMul_eq, Fin.getElem_fin] using
      congrArg (fun a => term.1 * (sparseCubeWeights term.2)[i] + a) ih

/-- Convert a word tensor to the specification carrier after all accumulation. -/
def tensorCombinationWord {n : Nat} (terms : List (E × (Fin n → E))) : Vector E (2^n) :=
  (tensorWords terms).map BF64.WordExt3.toField

/-- Word-field accumulation preserves the complete tensor specification. -/
theorem tensorCombinationWord_eq {n : Nat} (terms : List (E × (Fin n → E))) :
    tensorCombinationWord terms = tensorCombinationImage terms := by
  apply Vector.ext
  intro i hi
  simp only [tensorCombinationWord, Vector.getElem_map]
  exact tensorWords_get terms ⟨i, hi⟩

/-- Accumulate disjoint term halves in bounded tasks over the same numeric coordinates. -/
def tensorCombinationTasks {n : Nat} : Nat → List (E × (Fin n → E)) → Vector E (2 ^ n)
  | 0, terms => tensorCombinationWord terms
  | depth+1, terms =>
    if terms.length ≤ 1 then tensorCombinationWord terms
    else
      let middle := terms.length / 2
      let first := Task.spawn fun _ => tensorCombinationTasks depth (terms.take middle)
      let second := tensorCombinationTasks depth (terms.drop middle)
      let first := first.get
      Vector.ofFn fun i => sparseAdd first[i] second[i]

/-- Balanced accumulation preserves every coefficient of the specified tensor combination. -/
theorem tensorCombinationTasks_get {n : Nat} (depth : Nat) (terms : List (E × (Fin n → E)))
    (i : Fin (2 ^ n)) :
    (tensorCombinationTasks depth terms)[i] =
      (terms.map fun term => term.1 * Whir.eqWeight term.2 (mask n i)).sum := by
  induction depth generalizing terms with
  | zero => simpa only [tensorCombinationTasks, tensorCombinationWord_eq] using tensorCombinationImage_get terms i
  | succ depth ih =>
    rw [tensorCombinationTasks.eq_2]
    split
    · simpa only [tensorCombinationWord_eq] using tensorCombinationImage_get terms i
    · simp only [Fin.getElem_fin, Vector.getElem_ofFn, Task.spawn, sparseAdd_eq]
      rw [show (tensorCombinationTasks depth (terms.take (terms.length / 2)))[i.val] = _ from
        ih (terms.take (terms.length / 2)),
        show (tensorCombinationTasks depth (terms.drop (terms.length / 2)))[i.val] = _ from
        ih (terms.drop (terms.length / 2)),
        ← List.sum_append, ← List.map_append, List.take_append_drop]

/-- One Boolean coordinate shared by every tensor term. -/
structure FixedCoordinate {n : Nat} (terms : List (E × (Fin n → E))) where
  /-- Coordinate to remove before accumulating the tensors. -/
  index : Fin n
  /-- Its common Boolean value. -/
  bit : Bool
  /-- Every point has exactly that Boolean coordinate. -/
  fixed : ∀ term ∈ terms, term.2 index = if bit then 1 else 0

/-- Find a shared zero or unit coordinate in numeric coordinate order. -/
def fixedCoordinate {n : Nat} (terms : List (E × (Fin n → E))) :
    List (Fin n) → Option (FixedCoordinate terms)
  | [] => none
  | i :: rest =>
    if zero : terms.all (fun term => decide (term.2 i = 0)) = true then
      some ⟨i, false, by simpa only [List.all_eq_true, decide_eq_true_eq, Bool.false_eq_true, ite_false] using zero⟩
    else if one : terms.all (fun term => decide (term.2 i = 1)) = true then
      some ⟨i, true, by simpa only [List.all_eq_true, decide_eq_true_eq, ite_true] using one⟩
    else fixedCoordinate terms rest

/-- Equality tensors split into one selected factor and all remaining coordinates. -/
theorem eqWeight_succAbove {n : Nat} (point : Fin (n+1) → E) (u : Whir.Cube (n+1))
    (index : Fin (n+1)) :
    Whir.eqWeight point u = (if u index then point index else 1 - point index) *
      Whir.eqWeight (point ∘ index.succAbove) (u ∘ index.succAbove) := by
  exact Fin.prod_univ_succAbove (fun i => if u i then point i else 1 - point i) index

/-- Numeric deletion of a Boolean coordinate. -/
def eraseIndex (x index : Nat) : Nat :=
  x % 2^index + 2^index * (x / 2^(index+1))
/-- Numeric deletion retains exactly the unselected bits. -/
theorem eraseIndex_bit (x index j : Nat) :
    (eraseIndex x index).testBit j = x.testBit (if j < index then j else j+1) := by
  rw [eraseIndex, Nat.add_comm, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _))]
  by_cases h : j < index
  · simp only [h, decide_true, ite_true, Nat.testBit_mod_two_pow, Bool.true_and]
  · simp only [h, ite_false, Nat.testBit_div_two_pow]
    congr 1
    omega
/-- Bounded numeric deletion is the Boolean-coordinate inverse. -/
theorem eraseIndex_cube {n : Nat} (x : Fin (2^(n+1))) (index : Fin (n+1)) :
    eraseIndex x.val index.val = (cubeIndex n (mask (n+1) x ∘ index.succAbove)).val := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [eraseIndex_bit]
  by_cases hj : j < n
  · have bits := congrFun (mask_cubeIndex n (mask (n+1) x ∘ index.succAbove)) ⟨j,hj⟩
    change (cubeIndex n (mask (n+1) x ∘ index.succAbove)).val.testBit j =
      x.val.testBit (index.succAbove ⟨j,hj⟩).val at bits
    rw [bits]
    congr 1
    by_cases h : j < index.val <;> simp only [Fin.succAbove, Fin.lt_def, h,
      ite_true, ite_false, Fin.val_castSucc, Fin.val_succ]
  · rw [Nat.testBit_eq_false_of_lt (by
      apply x.isLt.trans_le
      apply Nat.pow_le_pow_right (by decide)
      split <;> omega), Nat.testBit_eq_false_of_lt (by
        apply (cubeIndex n (mask (n+1) x ∘ index.succAbove)).isLt.trans_le
        exact Nat.pow_le_pow_right (by decide) (by omega))]
/-- Restore one fixed selector with direct numeric bit deletion. -/
def expandCoordinate {n : Nat} (reduced : Vector E (2^n))
    (index : Fin (n+1)) (bit : Bool) : Vector E (2^(n+1)) :=
  let stride := 2^index.val
  Vector.ofFn fun i =>
    if i.val.testBit index.val = bit then
      reduced[i.val % stride + stride * (i.val / (stride * 2))]'(by
        have h := (cubeIndex n (mask (n+1) i ∘ index.succAbove)).isLt
        rw [← eraseIndex_cube] at h
        simpa only [eraseIndex, Nat.pow_succ] using h)
    else 0
/-- Numeric selector expansion equals the complete Boolean-coordinate lookup. -/
theorem expandCoordinate_get {n : Nat} (reduced : Vector E (2^n))
    (index : Fin (n+1)) (bit : Bool) (i : Fin (2^(n+1))) :
    (expandCoordinate reduced index bit)[i] =
      if mask (n+1) i index = bit then
        reduced[(cubeIndex n (mask (n+1) i ∘ index.succAbove)).val] else 0 := by
  simp only [expandCoordinate, Fin.getElem_fin, Vector.getElem_ofFn]
  have h := eraseIndex_cube i index
  simp only [eraseIndex, Nat.pow_succ] at h
  simp only [h]
  rfl

/-- Combine tensors on their shared support before expanding their fixed coordinates. -/
def tensorCombinationCompressed : {n : Nat} → List (E × (Fin n → E)) → Vector E (2 ^ n)
  | 0, terms => tensorCombinationImage terms
  | n+1, terms =>
    match fixedCoordinate terms (List.finRange (n+1)) with
    | none => tensorCombinationTasks 3 terms
    | some fixed =>
      let reduced := tensorCombinationCompressed
        (terms.map fun term => (term.1, term.2 ∘ fixed.index.succAbove))
      expandCoordinate reduced fixed.index fixed.bit

/-- Compressed accumulation has exactly the original weighted value at every coordinate. -/
theorem tensorCombinationCompressed_get {n : Nat} (terms : List (E × (Fin n → E)))
    (i : Fin (2 ^ n)) :
    (tensorCombinationCompressed terms)[i] =
      (terms.map fun term => term.1 * Whir.eqWeight term.2 (mask n i)).sum := by
  induction n with
  | zero => exact tensorCombinationImage_get terms i
  | succ n ih =>
    rw [tensorCombinationCompressed]
    split
    · exact tensorCombinationTasks_get 3 terms i
    · rename_i fixed found
      rw [expandCoordinate_get]
      have factor (term : E × (Fin (n+1) → E)) (member : term ∈ terms) :
          Whir.eqWeight term.2 (mask (n+1) i) =
            if (mask (n+1) i) fixed.index = fixed.bit then
              Whir.eqWeight (term.2 ∘ fixed.index.succAbove)
                ((mask (n+1) i) ∘ fixed.index.succAbove)
            else 0 := by
        rw [eqWeight_succAbove _ _ fixed.index, fixed.fixed term member]
        cases fixed.bit <;> cases (mask (n+1) i) fixed.index <;>
          simp only [Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false,
            sub_zero, sub_self, zero_mul, one_mul]
      split_ifs with same
      · have reduced := ih (terms.map fun term => (term.1, term.2 ∘ fixed.index.succAbove))
          (cubeIndex n ((mask (n+1) i) ∘ fixed.index.succAbove))
        simp only [Fin.getElem_fin, mask_cubeIndex, List.map_map, Function.comp_def] at reduced
        simp only [Function.comp_def]
        rw [reduced]
        apply congrArg List.sum
        apply List.map_congr_left
        intro term member
        rw [factor term member, ite_eq_left same]
        rfl
      · have zero : terms.map (fun term => term.1 * Whir.eqWeight term.2 (mask (n+1) i)) =
            terms.map (fun _ => (0 : E)) := by
          apply List.map_congr_left
          intro term member
          rw [factor term member, ite_eq_right same, mul_zero]
        rw [zero, List.sum_map_zero]

/-- Removing shared Boolean coordinates preserves the complete dense tensor image. -/
@[csimp] theorem tensorCombinationImage_code : @tensorCombinationImage = @tensorCombinationCompressed := by
  funext n terms
  apply Vector.ext
  intro i hi
  exact (tensorCombinationImage_get terms ⟨i,hi⟩).trans
    (tensorCombinationCompressed_get terms ⟨i,hi⟩).symm


/-- Materialize the combined tensor once before repeated Boolean-coordinate lookups. -/
def tensorCombination {n : Nat} (terms : List (E × (Fin n → E))) : Whir.Table E n :=
  let image := tensorCombinationImage terms
  fun u => image[(cubeEquiv n).symm u]

/-- Read the accumulated tensor through its direct numeric coordinate index. -/
@[macro_inline] def tensorCombinationDirect {n : Nat} (terms : List (E × (Fin n → E))) : Whir.Table E n :=
  let image := tensorCombinationImage terms
  fun u => image[cubeIndex n u]

/-- Direct numeric reads preserve the complete combined tensor. -/
@[csimp] theorem tensorCombination_direct : @tensorCombination = @tensorCombinationDirect := rfl

/-- Shared sparse combinations preserve the specified linear combination. -/
theorem tensorCombination_eq {n : Nat} (terms : List (E × (Fin n → E))) (u : Whir.Cube n) :
    tensorCombination terms u = (terms.map fun term => term.1 * Whir.eqWeight term.2 u).sum := by
  simp only [tensorCombination, tensorCombinationImage_get, ← cubeEquiv_apply,
    Equiv.apply_symm_apply]

end CompStark.Pcs
