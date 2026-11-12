/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.Verifier
public import ArkLib.ProofSystem.Whir.Extractor

/-! Shared claim restrictions and exact candidate validation for WHIR backward maps. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

@[expose] public section
namespace CompStark.Pcs
open CompStark.BinaryFields Whir
open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec

/-- Numeric inner product with a complete scalar image shared across retained claims. -/
def imageInnerProduct {n : Nat} (weight : Table E n) (image : Vector E (2 ^ n)) : E :=
  sparseSum ((List.finRange (2 ^ n)).map fun i => sparseMul (weight (mask n i)) image[i])

/-- Materializing the scalar table preserves its exact weighted sum. -/
theorem imageInnerProduct_ofFn {n : Nat} (weight f : Table E n) :
    imageInnerProduct weight (Vector.ofFn fun i : Fin (2 ^ n) => f (mask n i)) =
      innerProduct weight f := by
  simp only [imageInnerProduct, innerProduct, Fin.getElem_fin, Vector.getElem_ofFn]

/-- Check every claim against one shared numeric table image. -/
def imageClaimsCheck {n : Nat} (claims : List (Claim E n))
    (image : Vector E (2 ^ n)) : Bool :=
  claims.all fun claim => decide (imageInnerProduct claim.weight image = claim.value)

/-- Retain nonzero coordinates in their original numeric order. -/
def nonzeroEntries {n : Nat} (image : Vector E (2 ^ n)) (indices : List (Fin (2 ^ n))) :
    List (Fin (2 ^ n) × E) :=
  indices.filterMap fun i => if image[i] = 0 then none else some (i, image[i])

/-- Evaluate a weight only at the retained nonzero table entries. -/
def entriesInnerProduct {n : Nat} (weight : Table E n) (entries : List (Fin (2 ^ n) × E)) : E :=
  sparseSum (entries.map fun entry => sparseMul (weight (mask n entry.1)) entry.2)

/-- Removing zero entries preserves every ordered weighted sum. -/
theorem entriesInnerProduct_nonzeroEntries {n : Nat} (weight : Table E n)
    (image : Vector E (2 ^ n)) (indices : List (Fin (2 ^ n))) :
    entriesInnerProduct weight (nonzeroEntries image indices) =
      sparseSum (indices.map fun i => sparseMul (weight (mask n i)) image[i]) := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
    by_cases zero : image[i] = 0
    · simpa only [entriesInnerProduct, nonzeroEntries, List.filterMap_cons, zero,
        ↓reduceIte, List.map_cons, sparseSum, List.foldr_cons, sparseMul_eq,
        mul_zero, sparseAdd_eq, zero_add] using ih
    · simpa only [entriesInnerProduct, nonzeroEntries, List.filterMap_cons, zero,
        ↓reduceIte, List.map_cons, sparseSum, List.foldr_cons] using
        congrArg (sparseAdd (sparseMul (weight (mask n i)) image[i])) ih

/-- Validate all claims against one shared sparse image of the decoded table. -/
def imageClaimsCheckPrepared {n : Nat} (claims : List (Claim E n))
    (image : Vector E (2 ^ n)) : Bool :=
  let entries := nonzeroEntries image (List.finRange (2 ^ n))
  claims.all fun claim => decide (entriesInnerProduct claim.weight entries = claim.value)

/-- Shared sparse validation is exactly the original complete-image validation. -/
@[csimp] theorem imageClaimsCheck_code : @imageClaimsCheck = @imageClaimsCheckPrepared := by
  funext n claims image
  simp only [imageClaimsCheck, imageClaimsCheckPrepared, entriesInnerProduct_nonzeroEntries,
    imageInnerProduct]

/-- Shared-image validation agrees with the original finite retained-claim checks. -/
theorem imageClaimsCheck_ofFn {n : Nat} (claims : List (Claim E n)) (f : Table E n) :
    imageClaimsCheck claims (Vector.ofFn fun i : Fin (2 ^ n) => f (mask n i)) =
      (claims.all fun claim => decide (innerProduct claim.weight f = claim.value)) := by
  simp only [imageClaimsCheck, imageInnerProduct_ofFn]

/-- Check a retained claim using the certified numeric inner product. -/
def claimCheck {n : Nat} (claim : Claim E n) (f : Table E n) : Bool :=
  decide (innerProduct claim.weight f = claim.value)

/-- Numeric claim validation decides exactly the retained predicate. -/
theorem claimCheck_eq {n : Nat} (claim : Claim E n) (f : Table E n) :
    claimCheck claim f = decide (claim.Holds f) := by
  simp only [claimCheck, innerProduct_eq, Claim.Holds]

/-- Validate every retained claim in its supplied order. -/
def claimsCheck {n : Nat} (claims : List (Claim E n)) (f : Table E n) : Bool :=
  claims.all fun claim => claimCheck claim f

/-- Ordered claim validation decides the exact finite conjunction. -/
theorem claimsCheck_eq {n : Nat} (claims : List (Claim E n)) (f : Table E n) :
    claimsCheck claims f = decide (∀ c ∈ claims, c.Holds f) := by
  apply Bool.eq_iff_iff.mpr
  simp only [claimsCheck, List.all_eq_true, claimCheck_eq, decide_eq_true_eq]

/-- Select an ordered preimage while keeping the result carrier opaque to specialization. -/
@[noinline, nospecialize] def selectPrepared {A B C : Type}
    (candidates : List A) (view : A → B) (check : A → Bool)
    (equal : B → B → Bool) (project : A → C) (default : C) (successor : B) : C :=
  match candidates.find? (fun a => equal (view a) successor && check a) with
  | some a => project a
  | none => ((candidates.find? (fun a => equal (view a) successor)).map project).getD default

/-- Select a checked value without extending the search over its function-valued coordinates. -/
@[noinline, nospecialize] def firstChecked {A : Type}
    (candidates : List A) (check : A → Bool) (default : A) : A :=
  (candidates.find? check).getD default

/-- Select the same preimage with an explicitly supplied reflected validity check. -/
@[macro_inline] def checkedLift {n m : Nat} (candidates : List (Table E n))
    (view : Table E n → Table E m) (valid : Table E n → Prop) [DecidablePred valid]
    (check : Table E n → Bool) (_correct : ∀ f, check f = decide (valid f)) :
    Table E m → Table E n :=
  selectPrepared candidates view check (fun a b => decide (a = b)) id 0

/-- Reflected validation preserves both ordered searches and the zero default. -/
theorem checkedLift_eq {n m : Nat} (candidates : List (Table E n))
    (view : Table E n → Table E m) (valid : Table E n → Prop) [DecidablePred valid]
    (check : Table E n → Bool) (correct : ∀ f, check f = decide (valid f))
    : checkedLift candidates view valid check correct = listLift candidates view valid := by
  funext successor
  simp only [checkedLift, selectPrepared, listLift, correct, Bool.decide_and, id_eq]
  cases candidates.find? (fun f => decide (view f = successor) && decide (valid f)) with
  | some f => rfl
  | none =>
    cases candidates.find? (fun f => decide (view f = successor)) <;> rfl

/-- Materialize one affine message restriction before repeated coordinate reads. -/
@[macro_inline] def foldMessageCached {lanes vars : Nat}
    (f : Table E ((lanes + 1) + vars)) (r : E) : Table E (lanes + vars) :=
  restrictCached (Whir.castTable (by omega) f) (fun _ : Fin 1 => r)

/-- The shared affine message is the exact WHIR restriction. -/
theorem foldMessageCached_eq {lanes vars : Nat}
    (f : Table E ((lanes + 1) + vars)) (r : E) :
    foldMessageCached f r = foldMessageOne f r := by
  simp only [foldMessageCached, restrictCached_eq, foldMessageOne]

/-- Materialize known folded columns with the certified cubic-field kernel while preserving the mask. -/
@[macro_inline] def foldRowsCached {lanes columns : Nat}
    (word : MaskedWord E (lanes + 1) columns) (r : E) : MaskedWord E lanes columns :=
  let image := Vector.ofFn fun x : Fin columns =>
    (word x).map fun column => Vector.ofFn fun i : Fin (2 ^ lanes) =>
      sparseAdd (sparseMul (1 - r) (column (Fin.cons false (mask lanes i))))
        (sparseMul r (column (Fin.cons true (mask lanes i))))
  fun x => (image[x]).map fun column u => column[(cubeEquiv lanes).symm u]

/-- Shared word folding preserves every known column and every hidden column. -/
theorem foldRowsCached_eq {lanes columns : Nat}
    (word : MaskedWord E (lanes + 1) columns) (r : E) :
    foldRowsCached word r = foldMaskedRowsOne word r := by
  funext x
  simp only [foldRowsCached, Fin.getElem_fin, Vector.getElem_ofFn,
    Option.map_map, foldMaskedRowsOne]
  congr 1
  funext column u
  simp only [Function.comp_apply, Vector.getElem_ofFn, ← cubeEquiv_apply,
    Fin.eta, Equiv.apply_symm_apply, sparseAdd_eq, sparseMul_eq]

/-- Boundary preimage selection with the same collision search and reflected validity. -/
@[macro_inline] def boundaryLiftChecked {n m : Nat} (oldList : List (Table E m))
    (view : Table E m → Table E n) (valid : Table E m → Prop) [DecidablePred valid]
    (check : Table E m → Bool) (correct : ∀ f, check f = decide (valid f))
    (newList : List (Table E n)) (z : Fin n → E) (successor : Table E n) :
    Sum (Table E n) (Table E n × Table E n) :=
  if oldList.any (fun f => decide (view f = successor)) then
    .inl (view (checkedLift oldList view valid check correct successor))
  else match oodCollisionPair newList z with
    | some pair => .inr pair
    | none => .inl (view 0)

/-- Reflected boundary validation preserves the entire boundary backward map. -/
theorem boundaryLiftChecked_eq {n m : Nat} (oldList : List (Table E m))
    (view : Table E m → Table E n) (valid : Table E m → Prop) [DecidablePred valid]
    (check : Table E m → Bool) (correct : ∀ f, check f = decide (valid f))
    (newList : List (Table E n)) (z : Fin n → E) :
    boundaryLiftChecked oldList view valid check correct newList z =
      boundaryLift oldList view valid newList z := by
  funext successor
  simp only [boundaryLiftChecked, checkedLift_eq, boundaryLift]
  split_ifs
  · rfl
  · cases oodCollisionPair newList z <;> rfl


/-- The complete shared message-fold function equals the original fold. -/
theorem foldMessageCached_fun_eq : @foldMessageCached = @Whir.foldMessageOne E _ := by
  funext lanes vars f r
  exact foldMessageCached_eq f r

/-- The complete shared word-fold function equals the original fold. -/
theorem foldRowsCached_fun_eq : @foldRowsCached = @Whir.foldMaskedRowsOne E _ := by
  funext lanes columns word r
  exact foldRowsCached_eq word r

/-- The complete shared batch function equals the original batching function. -/
theorem batchCached_fun_eq : @batchCached = @Whir.batch E _ := by
  funext n claims r
  exact batchCached_eq claims r

/-- Store a candidate's affine image as data before function-valued comparison. -/
@[macro_inline] def foldImage {lanes vars : Nat}
    (f : Table E ((lanes + 1) + vars)) (r : E) : Vector E (2 ^ (lanes + vars)) :=
  let weights := cachedEqWeight (fun _ : Fin 1 => r)
  Vector.ofFn fun i : Fin (2 ^ (lanes + vars)) =>
    innerProduct weights (fun u => (Whir.castTable (by omega) f)
      (Fin.addCases u (mask (lanes + vars) i)))

/-- Reading the stored candidate image gives the exact affine restriction. -/
theorem foldImage_eq {lanes vars : Nat}
    (f : Table E ((lanes + 1) + vars)) (r : E) :
    (fun u => (foldImage f r)[(cubeEquiv (lanes + vars)).symm u]) =
      foldMessageOne f r := by
  rw [← foldMessageCached_eq]
  rfl

/-- Prefer a valid fold preimage using materialized candidate-image records. -/
@[macro_inline] def foldLiftCached {lanes vars : Nat} (candidates : List (Table E ((lanes + 1) + vars)))
    (r : E) (claim : Claim E ((lanes + 1) + vars)) :
    Table E (lanes + vars) → Table E ((lanes + 1) + vars) :=
  let images := candidates.map fun f => (f, foldImage f r)
  selectPrepared images (fun entry u => entry.2[(cubeEquiv (lanes + vars)).symm u])
    (fun entry => claimCheck claim entry.1) (fun a b => decide (a = b)) Prod.fst 0

/-- Materialized preimages retain validity preference, ordered fallback and zero. -/
theorem foldLiftCached_eq {lanes vars : Nat} (candidates : List (Table E ((lanes + 1) + vars)))
    (r : E) (claim : Claim E ((lanes + 1) + vars)) :
    foldLiftCached candidates r claim =
      listLift candidates (fun f => foldMessageOne f r) claim.Holds := by
  funext successor
  simp only [foldLiftCached, selectPrepared, List.find?_map, Function.comp_def, foldImage_eq,
    claimCheck_eq, listLift, Bool.decide_and, Option.map_map]
  cases candidates.find? (fun f => decide (foldMessageOne f r = successor) && decide (claim.Holds f)) with
  | some f => rfl
  | none =>
    simp only [Option.map_none]
    cases candidates.find? (fun f => decide (foldMessageOne f r = successor)) <;> rfl

/-- Fold extraction with shared virtual words, claim restrictions and validity checks. -/
def foldExtractorCached
    {vars : ℕ} (enc : Encoding K vars) (nearby : (lanes : ℕ) →
      MaskedWord E lanes (2 ^ (vars + enc.rate)) → Table E (lanes + vars) → Prop)
    (decoders : (lanes : ℕ) → ListDecoder (E := E) enc lanes)
    {rest : Protocol}
    (finish : (word : MaskedWord E 0 (2 ^ (vars + enc.rate))) →
      (claim : Claim E (0 + vars)) → (active : Bool) →
      RoundExtractor rest.tree (relationState (nearby 0) word [claim] active)) :
    (lanes : ℕ) → (word : MaskedWord E lanes (2 ^ (vars + enc.rate))) →
      (claim : Claim E (lanes + vars)) → (active : Bool) →
      RoundExtractor (scalarRounds E lanes rest).tree
        (relationState (nearby _) word [claim] active)
  | 0, word, claim, active => finish word claim active
  | lanes + 1, word, claim, active =>
    let candidates := (decoders (lanes + 1)).decode word
    fun q =>
      let checked := active && (Sumcheck.compressedOps 1).accept claim.value q
      ⟨relationState (nearby _) word [claim] checked, id, fun r =>
        let word' := foldRowsCached word r
        let claim' : Claim E (lanes + vars) :=
          ⟨foldMessageCached claim.weight r, evalQuadratic claim.value q r⟩
        ⟨relationState (nearby _) word' [claim'] checked,
          foldLiftCached candidates r claim,
          foldExtractorCached enc nearby decoders finish lanes word' claim' checked⟩⟩

/-- Final-level extraction with reflected retained-claim validation. -/
def lastExtractorCached
    {tail : ℕ} (lanes queries : ℕ) (enc : Encoding K tail) (ι : K →+* E)
    (nearby : MaskedWord E 0 (2 ^ (tail + enc.rate)) → Table E (0 + tail) → Prop)
    (decoder : ListDecoder (E := E) enc 0) (word : MaskedWord E 0 (2 ^ (tail + enc.rate)))
    (claim : Claim E (0 + tail)) (active : Bool) :
    RoundExtractor (transition E (.last lanes tail enc queries)).tree
      (relationState nearby word [claim] active) :=
  let candidates := decoder.decode word
  fun candidate =>
    ⟨plaintextProximityState enc nearby word claim candidate active,
      (fun _ => checkedLift candidates
        (castTable (Nat.zero_add tail)) claim.Holds (claimCheck claim) (claimCheck_eq claim) candidate), fun xs =>
      let claims : List (Claim E tail) :=
        ⟨castTable (Nat.zero_add tail) claim.weight, claim.value⟩ ::
          List.ofFn (fun q : Fin queries =>
            ⟨queryWeightCached enc ι (xs q), zeroFill word (xs q) Fin.elim0⟩)
      ⟨plaintextState candidate claims (active && queriesKnown word xs), (fun _ => PUnit.unit),
        finalBatchExtractor candidate claims (active && queriesKnown word xs)⟩⟩

/-- Boundary extraction preserving the old-list and collision branches. -/
def boundaryExtractorCached {tail : ℕ} (lanes queries : ℕ) (enc : Encoding K tail)
    (ι : K →+* E)
    (nearby : MaskedWord E 0 (2 ^ (tail + enc.rate)) → Table E (0 + tail) → Prop)
    (rest : Schedule K tail) (nextNearby : ProximityFamily K E)
    (decoder : ListDecoder (E := E) enc 0) (decoders : DecoderFamily (E := E) rest)
    (suffixExtractor : (word : oracleMessage E rest) → (claims : List (Claim E tail)) →
      (active : Bool) → RoundExtractor (opening E rest).tree
        (relationLevelState rest nextNearby word claims active))
    (word : MaskedWord E 0 (2 ^ (tail + enc.rate))) (claim : Claim E (0 + tail))
    (active : Bool) :
    RoundExtractor (transition E (.more lanes enc queries rest)).tree
      (relationState nearby word [claim] active) :=
  let oldList := decoder.decode word
  fun nextWord =>
    let oldState := relationState nearby word [claim] active
    let old := fun f : Table E tail => oldState.holds (castTable (Nat.zero_add tail).symm f)
    let newList := levelList rest decoders nextWord
    ⟨oldState, id, fun z =>
      let separatedState := oodState old newList z active
      ⟨separatedState, (fun w => match w with
        | .inl f => castTable (Nat.zero_add tail).symm f
        | .inr _ => (0 : Table E (0 + tail))), fun answer =>
        ⟨separatedState, id, fun xs =>
          let residual : Claim E tail :=
            ⟨castTable (Nat.zero_add tail) claim.weight, claim.value⟩
          let claims := Whir.nextClaimsPrepared enc ι residual z answer xs (fun x => zeroFill word x Fin.elim0)
          ⟨relationLevelState rest nextNearby nextWord claims (active && queriesKnown word xs),
            boundaryLiftChecked oldList
              (castTable (Nat.zero_add tail)) claim.Holds (claimCheck claim) (claimCheck_eq claim) newList z,
            suffixExtractor nextWord claims (active && queriesKnown word xs)⟩⟩⟩⟩

/-- Complete schedule extraction with shared folding and reflected validity checks. -/
def levelExtractorCached (ι : K →+* E) :
    {n : ℕ} → (s : Schedule K n) → (nearby : ProximityFamily K E) →
      (decoders : DecoderFamily (E := E) s) →
      (word : oracleMessage E s) → (claims : List (Claim E n)) → (active : Bool) →
      RoundExtractor (opening E s).tree (relationLevelState s nearby word claims active)
  | _, .last lanes tail enc queries, nearby, decoders, word, claims, active =>
    let candidates := (decoders lanes).decode word
    fun r =>
      ⟨relationState (nearby 0 enc lanes) word [batchCached claims r] active,
        checkedLift candidates id
          (fun f => ∀ c ∈ claims, c.Holds f) (claimsCheck claims) (claimsCheck_eq claims),
        foldExtractorCached enc (nearby 0 enc) decoders
          (lastExtractorCached lanes queries enc ι (nearby 0 enc 0) (decoders 0))
          lanes word (batchCached claims r) active⟩
  | _, .more lanes enc queries rest, nearby, decoders, word, claims, active =>
    let candidates := (decoders.1 lanes).decode word
    fun r =>
      ⟨relationState (nearby 0 enc lanes) word [batchCached claims r] active,
        checkedLift candidates id
          (fun f => ∀ c ∈ claims, c.Holds f) (claimsCheck claims) (claimsCheck_eq claims),
        foldExtractorCached enc (nearby 0 enc) decoders.1
          (boundaryExtractorCached lanes queries enc ι (nearby 0 enc 0)
            rest (fun level => nearby (level + 1)) (decoders.1 0) decoders.2
            (levelExtractorCached ι rest (fun level => nearby (level + 1)) decoders.2))
          lanes word (batchCached claims r) active⟩

/-- Cached folds preserve every state and backward map of the original extractor. -/
theorem foldExtractorCached_eq : @foldExtractorCached = @Whir.foldExtractor K E _ _ := by
  funext vars enc nearby decoders rest finish lanes
  induction lanes with
  | zero => rfl
  | succ lanes ih =>
    funext word claim active
    simp only [foldExtractorCached, Whir.foldExtractor]
    rw [foldRowsCached_fun_eq, foldMessageCached_fun_eq]
    simp only [foldLiftCached_eq, ih]

/-- Cached final preimage checks preserve the original last-level extractor. -/
theorem lastExtractorCached_eq : @lastExtractorCached = @Whir.lastExtractor K E _ _ _ := by
  funext tail lanes queries enc ι nearby decoder word claim active
  simp only [lastExtractorCached, Whir.lastExtractor, Whir.Encoding.queryWeights,
    checkedLift_eq, queryWeightCached_eq]

/-- Cached boundary checks preserve old-list, collision and zero-default behavior. -/
theorem boundaryExtractorCached_eq :
    @boundaryExtractorCached = @Whir.boundaryExtractor K E _ _ _ := by
  funext tail lanes queries enc ι nearby rest nextNearby decoder decoders suffix word claim active
  simp only [boundaryExtractorCached, Whir.boundaryExtractor, boundaryLiftChecked_eq]
  funext nextWord
  refine Sigma.ext ?_ ?_
  · rfl
  apply heq_of_eq
  refine Prod.ext ?_ ?_
  · rfl
  funext z
  refine Sigma.ext ?_ ?_
  · rfl
  apply heq_of_eq
  apply Prod.ext
  · funext w
    cases w <;> rfl
  · rfl

/-- Every cached schedule map equals the corresponding complete WHIR extractor. -/
theorem levelExtractorCached_eq : @levelExtractorCached = @Whir.levelExtractor K E _ _ _ := by
  funext ι n schedule
  induction schedule with
  | last lanes tail enc queries =>
    funext nearby decoders word claims active
    simp only [levelExtractorCached, Whir.levelExtractor]
    rw [batchCached_fun_eq]
    simp only [checkedLift_eq, foldExtractorCached_eq, lastExtractorCached_eq]
  | more lanes enc queries rest ih =>
    funext nearby decoders word claims active
    simp only [levelExtractorCached, Whir.levelExtractor]
    rw [batchCached_fun_eq]
    simp only [checkedLift_eq, foldExtractorCached_eq, boundaryExtractorCached_eq, ih]

end CompStark.Pcs
