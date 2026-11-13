/-
Copyright (c) 2026 zkSecurity.
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompStark.Pcs.Verifier
public import CompStark.BinaryFields.WordProduct
public import ArkLib.ProofSystem.Whir.Algebra

/-! Multilinear weight evaluators carry their specification without materializing its table. -/

set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 30000

@[expose] public section
namespace CompStark.Pcs
open CompStark.BinaryFields BF64

/-- Binary exponentiation through the certified extension-word carrier. -/
def powerNative (a : E) (n : Nat) : E :=
  BF64.WordExt3.toField (BF64.WordExt3.powWord (BF64.WordExt3.ofField a) n)

/-- Word powers agree with the specification at every natural exponent. -/
theorem powerNative_eq (a : E) (n : Nat) : powerNative a n = a ^ n := by
  rw [powerNative, BF64.WordExt3.toField_powWord, BF64.WordExt3.toField_ofField]

/-- Use three base products when the right word has no extension coefficients. -/
def wordProduct (a b : WordExt3) : WordExt3 :=
  if b.c1 = 0 ∧ b.c2 = 0 then WordExt3.mulScalar a b.c0 else a*b
/-- The mixed word product equals full extension multiplication. -/
theorem wordProduct_eq (a b : WordExt3) : wordProduct a b = a*b := by
  unfold wordProduct
  split_ifs with base
  · apply WordExt3.toField_injective
    rw [WordExt3.toField_mulScalar]
    change b.c0.toField • a.toField = WordExt3.ringEquiv (a*b)
    rw [map_mul]
    change _ = a.toField * b.toField
    have scalar : b.toField = ofK b.c0.toField := by
      change E.ofLimbs b.c0.toField b.c1.toField b.c2.toField = _
      rw [base.1, base.2]
      have wordZero : Word.toField (0 : Word) = 0 := rfl
      rw [wordZero, ← ofK_eq_ofLimbs]
    rw [scalar, Algebra.smul_def, mul_comm]
    rfl
  · rfl
/-- Multiply word values while omitting zero and unit operands. -/
def sparseProduct (a b : WordExt3) : WordExt3 :=
  if a = 0 then 0 else if b = 0 then 0 else if a = 1 then b else if b = 1 then a else wordProduct a b
/-- Sparse word multiplication equals the carrier's field multiplication. -/
theorem sparseProduct_eq (a b : WordExt3) : sparseProduct a b = a*b := by
  unfold sparseProduct
  rw [wordProduct_eq]
  split_ifs <;> simp_all only [zero_mul, mul_zero, one_mul, mul_one]
/-- A table and a certified evaluator of its multilinear extension. -/
structure EvaluatedWeight (n : Nat) where
  /-- Boolean values used by the protocol specification. -/
  table : Whir.Table E n
  /-- Evaluation retains word coordinates and a word result. -/
  wordEvaluate : (Fin n → WordExt3) → WordExt3
  /-- Word evaluation represents the protocol's exact equality-kernel sum. -/
  wordEvaluate_eq : ∀ point, WordExt3.toField (wordEvaluate point) =
    Whir.mle table (fun i => WordExt3.toField (point i))

/-- Word evaluation at converted coordinates equals the specification MLE. -/
theorem EvaluatedWeight.wordEvaluate_ofField {n : Nat} (weight : EvaluatedWeight n)
    (point : Fin n → E) : WordExt3.toField
      (weight.wordEvaluate (fun i => WordExt3.ofField (point i))) = Whir.mle weight.table point := by
  simpa only [WordExt3.toField_ofField] using
    weight.wordEvaluate_eq (fun i => WordExt3.ofField (point i))

/-- Prepare each closing coordinate once before evaluating the complete weight expression. -/
def EvaluatedWeight.evaluatePoint {n : Nat} (weight : EvaluatedWeight n) (point : Fin n → E) : WordExt3 :=
  let coordinates := Vector.ofFn fun i => WordExt3.ofField (point i)
  weight.wordEvaluate (fun i => coordinates[i])
/-- Prepared word coordinates retain the exact multilinear weight value. -/
theorem EvaluatedWeight.evaluatePoint_eq {n : Nat} (weight : EvaluatedWeight n) (point : Fin n → E) :
    (weight.evaluatePoint point).toField = Whir.mle weight.table point := by
  simpa only [EvaluatedWeight.evaluatePoint, Fin.getElem_fin, Vector.getElem_ofFn] using
    weight.wordEvaluate_ofField point

/-- A protocol claim with a certified weight evaluator. -/
structure EvaluatedClaim (n : Nat) where
  /-- Weight and its multilinear evaluator. -/
  weight : EvaluatedWeight n
  /-- Transmitted value of the weighted opening. -/
  value : E

/-- Forget the evaluator, retaining the exact WHIR claim. -/
def EvaluatedClaim.claim {n : Nat} (c : EvaluatedClaim n) : Whir.Claim E n :=
  ⟨c.weight.table, c.value⟩

/-- Dimension transport commutes with erasing an evaluator. -/
theorem EvaluatedClaim.cast_claim {n m : Nat} (h : n = m) (claim : EvaluatedClaim n) :
    (h ▸ claim).claim = h ▸ claim.claim := by
  cases h
  rfl

/-- Erasing a transported family commutes with applying it to an input. -/
theorem EvaluatedClaim.cast_apply_claim {A : Type} {n m : Nat} (h : n = m)
    (claims : A → EvaluatedClaim n) (a : A) :
    ((h ▸ claims) a).claim = (h ▸ (fun x => (claims x).claim)) a := by
  cases h
  rfl

/-- Multilinear evaluation of a factored tensor is a product of scalar evaluations. -/
theorem mle_factors {n : Nat} (factors : Fin n → E × E) (point : Fin n → E) :
    Whir.mle (fun u => ∏ i, if u i then (factors i).2 else (factors i).1) point =
      ∏ i, ((1 - point i) * (factors i).1 + point i * (factors i).2) := by
  have expansion := Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
    (if b then point i else 1 - point i) *
      (if b then (factors i).2 else (factors i).1))
  simpa only [Whir.mle, Whir.eqWeight, ← Finset.prod_mul_distrib,
    Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true, add_comm] using expansion.symm

/-- Factor tensors prepare word coordinates once and retain them for evaluation. -/
def EvaluatedWeight.factors {n : Nat} (factors : Fin n → E × E) : EvaluatedWeight n :=
  let prepared := Vector.ofFn fun i => (WordExt3.ofField (factors i).1, WordExt3.ofField (factors i).2)
  { table := fun u => ∏ i, if u i then (factors i).2 else (factors i).1
    wordEvaluate := fun point => ∏ i, (prepared[i].1 + sparseProduct (point i) (prepared[i].2 - prepared[i].1))
    wordEvaluate_eq := fun point => by
      change WordExt3.ringEquiv _ = _
      simp only [prepared, map_prod, map_add, sparseProduct_eq, map_mul, map_sub,
        Fin.getElem_fin, Vector.getElem_ofFn,
        show ∀ a, WordExt3.ringEquiv (WordExt3.ofField a) = a from WordExt3.toField_ofField]
      simp only [show ∀ w, WordExt3.ringEquiv w = WordExt3.toField w from fun _ => rfl]
      rw [mle_factors]
      apply Finset.prod_congr rfl
      intro i _
      ring }
/-- Characteristic-two equality factors require only coordinate additions. -/
theorem equalityFactor_eq_add (r x : E) : (1 - x) * (1 - r) + x * r = 1 - r + x := by
  simp only [CharTwo.sub_eq_add]
  calc
    (1 + x) * (1 + r) + x * r = (1 + r) + x + (x * r + x * r) := by ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]
/-- Equality tensors retain only one prepared word per coordinate. -/
def EvaluatedWeight.eq {n : Nat} (point : Fin n → E) : EvaluatedWeight n :=
  let prepared := Vector.ofFn fun i => (1 : WordExt3) - WordExt3.ofField (point i)
  { table := Whir.eqWeight point
    wordEvaluate := fun atPoint => ∏ i, (prepared[i] + atPoint i)
    wordEvaluate_eq := fun atPoint => by
      change WordExt3.ringEquiv _ = _
      rw [map_prod]
      simp only [prepared, map_add, map_sub, map_one, Fin.getElem_fin, Vector.getElem_ofFn,
        show ∀ a, WordExt3.ringEquiv (WordExt3.ofField a) = a from WordExt3.toField_ofField]
      have factors := mle_factors (fun i => (1 - point i, point i))
        (fun i => (atPoint i).toField)
      change Whir.mle (Whir.eqWeight point) _ = _ at factors
      rw [factors]
      apply Finset.prod_congr rfl
      intro i _
      exact (equalityFactor_eq_add _ _).symm }

/-- The factored equality evaluator specifies the exact WHIR equality table. -/
@[simp] theorem EvaluatedWeight.eq_table {n : Nat} (point : Fin n → E) :
    (EvaluatedWeight.eq point).table = Whir.eqWeight point := rfl

/-- Multilinear evaluation commutes with finite scalar combinations. -/
theorem mle_combination {R : Type} [CommRing R] {n : Nat}
    (terms : List (R × Whir.Table R n)) (point : Fin n → R) :
    Whir.mle (fun u => (terms.map fun t => t.1 * t.2 u).sum) point =
      (terms.map fun t => t.1 * Whir.mle t.2 point).sum := by
  induction terms with
  | nil => simp only [List.map_nil, List.sum_nil, Whir.mle, mul_zero, Finset.sum_const_zero]
  | cons term terms ih =>
    simp only [List.map_cons, List.sum_cons, Whir.mle, mul_add, Finset.sum_add_distrib] at *
    rw [← ih, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    ac_rfl

/-- Multilinear evaluation of a restriction concatenates the two evaluation points. -/
theorem mle_restriction {R : Type} [CommRing R] {count tail : Nat}
    (table : Whir.Table R (count + tail)) (front : Fin count → R) (point : Fin tail → R) :
    Whir.mle (Whir.restrict table front) point = Whir.mle table (Fin.addCases front point) := by
  unfold Whir.mle Whir.restrict
  rw [Whir.sum_cube_add (n := count) (m := tail)]
  simp only [Whir.eqWeight_add, Fin.addCases_left, Fin.addCases_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ac_rfl

/-- Word evaluator combinations prepare their scalar coefficients once. -/
def EvaluatedWeight.combine {n : Nat} (terms : List (E × EvaluatedWeight n)) : EvaluatedWeight n :=
  let prepared := terms.map fun term => (WordExt3.ofField term.1, term.2)
  { table := fun u => (terms.map fun term => term.1 * term.2.table u).sum
    wordEvaluate := fun point => (prepared.map fun term => sparseProduct term.1 (term.2.wordEvaluate point)).sum
    wordEvaluate_eq := fun point => by
      change WordExt3.ringEquiv _ = _
      rw [map_list_sum]
      dsimp only [prepared]
      simp only [List.map_map, Function.comp_def, sparseProduct_eq]
      simp only [map_mul]
      simp only [show ∀ a, WordExt3.ringEquiv (WordExt3.ofField a) = a from WordExt3.toField_ofField]
      simp only [show ∀ w, WordExt3.ringEquiv w = WordExt3.toField w from fun _ => rfl, EvaluatedWeight.wordEvaluate_eq]
      simpa only [List.map_map, Function.comp_def] using
        (mle_combination (terms.map fun term => (term.1, term.2.table)) _).symm }

/-- Carrier conversion commutes with concatenating low and high coordinates. -/
theorem toField_addCases {count tail : Nat} (front : Fin count → WordExt3)
    (point : Fin tail → WordExt3) :
    (fun i => WordExt3.toField (Fin.addCases front point i)) =
      Fin.addCases (fun i => WordExt3.toField (front i)) (fun i => WordExt3.toField (point i)) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp only [Fin.addCases_left]
  · intro j; simp only [Fin.addCases_right]
/-- Restrictions prepend prepared word coordinates without materializing a table. -/
def EvaluatedWeight.restrict {count tail : Nat} (weight : EvaluatedWeight (count+tail))
    (front : Fin count → E) : EvaluatedWeight tail :=
  let prepared : Vector WordExt3 count := Vector.ofFn fun i => WordExt3.ofField (front i)
  let frontWords : Fin count → WordExt3 := fun i => prepared[i]
  { table := Whir.restrict (count := count) (tail := tail) weight.table front
    wordEvaluate := fun (point : Fin tail → WordExt3) => weight.wordEvaluate (Fin.addCases frontWords point)
    wordEvaluate_eq := fun (point : Fin tail → WordExt3) => by
      have coordinates : (fun i => WordExt3.toField
          (Fin.addCases frontWords point i)) =
          Fin.addCases front (fun i => WordExt3.toField (point i)) := by
        rw [toField_addCases]
        simp only [frontWords, prepared, Fin.getElem_fin, Vector.getElem_ofFn, WordExt3.toField_ofField]
      calc
        _ = Whir.mle weight.table (fun i => WordExt3.toField
          (Fin.addCases frontWords point i)) :=
          by
            have law := weight.wordEvaluate_eq (Fin.addCases frontWords point)
            exact law
        _ = Whir.mle weight.table (Fin.addCases front (fun i => WordExt3.toField (point i))) :=
          congrArg (Whir.mle weight.table) coordinates
        _ = _ := (mle_restriction (count := count) (tail := tail) weight.table front
          (fun i => WordExt3.toField (point i))).symm }
/-- Batch opening values and evaluators in the protocol's exact power order. -/
def batchEvaluated {n : Nat} (claims : List (EvaluatedClaim n)) (r : E) : EvaluatedClaim n :=
  let terms := claims.zipIdx.map fun (claim, index) => (powerNative r index, claim)
  ⟨.combine (terms.map fun term => (term.1, term.2.weight)),
    sparseSum (terms.map fun term => sparseMul term.1 term.2.value)⟩

/-- Factored batching retains the exact protocol weight and value. -/
theorem batchEvaluated_claim {n : Nat} (claims : List (EvaluatedClaim n)) (r : E) :
    (batchEvaluated claims r).claim = Whir.batch (claims.map EvaluatedClaim.claim) r := by
  simp only [batchEvaluated, EvaluatedClaim.claim, EvaluatedWeight.combine, sparseSum_eq,
    sparseMul_eq, powerNative_eq, Whir.batch, List.map_map, Function.comp_def, List.zipIdx_map, Prod.map, EvaluatedClaim.claim, id_eq]

end CompStark.Pcs

namespace CompStark.Pcs
open CompStark.BinaryFields BF64

/-- An additive encoder with certified multilinear evaluations of its query weights. -/
structure EvaluatedEncoding (n : Nat) where
  /-- The exact protocol encoder and domain. -/
  encoding : Whir.Encoding K n
  /-- Factored query weights on the extension field. -/
  query : encoding.Columns → EvaluatedWeight n
  /-- Each query evaluator represents the scalar-extended protocol weight. -/
  query_table : ∀ x, (query x).table = fun u => ofK (encoding.weight x u)
  /-- An executable encoding of every base-field row, as data. -/
  encodeRowsBase : {lanes : Nat} → Whir.Table K (lanes + n) → Vector (Array K) (2 ^ lanes)
  /-- Each row's entries are the protocol's encoding of that row. -/
  encodeRowsBase_eq : ∀ {lanes : Nat} (f : Whir.Table K (lanes + n)) (row : Fin (2 ^ lanes))
    (x : encoding.Columns), (encodeRowsBase f)[row].getD x.val 0 =
      encoding.encode (RingHom.id K) (fun v => f (Fin.addCases (mask lanes row) v)) x
  /-- An executable encoding of every extension-field row, as data. -/
  encodeRowsExtension : {lanes : Nat} → Whir.Table E (lanes + n) → Vector (Array E) (2 ^ lanes)
  /-- Each row's entries are the protocol's encoding of that row. -/
  encodeRowsExtension_eq : ∀ {lanes : Nat} (f : Whir.Table E (lanes + n)) (row : Fin (2 ^ lanes))
    (x : encoding.Columns), (encodeRowsExtension f)[row].getD x.val 0 =
      encoding.encode (algebraMap K E) (fun v => f (Fin.addCases (mask lanes row) v)) x

/-- Shared recurrence constants and denominator inverse for one normalized basis factor. -/
def normalizedFactorPlan (i : Fin 64) : Array K × K :=
  let constants := AdditiveNTT.subspacePolynomialConstantsArray (β := basis) (ℓ := 0) (R_rate := 0) i
  (constants, (AdditiveNTT.evalWAtCachedConstants constants (basis i))⁻¹)

/-- A production folding ladder retaining the query-weight evaluators at every level. -/
inductive EvaluatedSchedule : Nat → Type
  /-- The final encoded level folds into the transmitted plaintext table. -/
  | last (lanes tail : Nat) (encoding : EvaluatedEncoding tail) (queries : Nat) :
      EvaluatedSchedule (lanes + tail)
  /-- A boundary introduces the next encoded word, its OOD answer and sampled queries. -/
  | more {tail : Nat} (lanes : Nat) (encoding : EvaluatedEncoding tail) (queries : Nat)
      (rest : EvaluatedSchedule tail) : EvaluatedSchedule (lanes + tail)

/-- Erase evaluators without changing any protocol shape or query count. -/
def EvaluatedSchedule.schedule : {n : Nat} → (schedule : EvaluatedSchedule n) → Whir.Schedule K n
  | _, .last lanes tail enc queries => .last lanes tail enc.encoding queries
  | _, .more lanes enc queries rest => .more lanes enc.encoding queries (EvaluatedSchedule.schedule rest)
termination_by structural _ schedule => schedule


/-- A word equality tensor represents the exact Boolean-coordinate weight. -/
theorem wordCubeWeight {n : Nat} (point : Fin n → E) (i : Fin (2^n)) :
    WordExt3.toField ((Keccak.Gkr.cubeWeights (fun j => WordExt3.ofField (point j)))[i]) =
      Whir.eqWeight point (mask n i) := by
  rw [Keccak.Gkr.cubeWeights_get]
  change WordExt3.ringEquiv _ = _
  simp only [Keccak.Gkr.eqWeight, Whir.eqWeight, mask, map_prod, apply_ite, map_sub, map_one,
    show ∀ a, WordExt3.ringEquiv (WordExt3.ofField a) = a from WordExt3.toField_ofField]
/-- Accumulate extension values through three unboxed polynomial-basis words. -/
def sumWordLoop {size : Nat} (values : Fin size → WordExt3) :
    (count start : Nat) → start+count ≤ size → UInt64 → UInt64 → UInt64 → WordExt3
  | 0, _, _, a0,a1,a2 => ⟨⟨a0⟩,⟨a1⟩,⟨a2⟩⟩
  | count+1,start,h,a0,a1,a2 =>
    let value := values ⟨start,by omega⟩
    sumWordLoop values count (start+1) (by omega)
      (a0 ^^^ value.c0.val) (a1 ^^^ value.c1.val) (a2 ^^^ value.c2.val)
/-- Unboxed accumulation preserves the exact finite interval sum. -/
theorem sumWordLoop_eq {size : Nat} (values : Fin size → WordExt3)
    (count start : Nat) (h : start+count ≤ size) (acc : WordExt3) :
    sumWordLoop values count start h acc.c0.val acc.c1.val acc.c2.val =
      acc + ∑ i : Fin count, values ⟨start+i.val,by omega⟩ := by
  induction count generalizing start acc with
  | zero =>
    simp only [sumWordLoop.eq_1, Fin.sum_univ_zero, add_zero]
  | succ count ih =>
    change sumWordLoop values count (start+1) _ (acc+values ⟨start,by omega⟩).c0.val
      (acc+values ⟨start,by omega⟩).c1.val (acc+values ⟨start,by omega⟩).c2.val = _
    rw [ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ, add_assoc]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Fin.ext
    change start+(1+i.val) = start+(i.val+1)
    omega
/-- Sum a finite word family without allocating a list or boxed running accumulator. -/
def sumWordFamily {size : Nat} (values : Fin size → WordExt3) : WordExt3 :=
  sumWordLoop values size 0 (by omega) 0 0 0
/-- Every word sum equals its mathematical finite sum. -/
theorem sumWordFamily_eq {size : Nat} (values : Fin size → WordExt3) : sumWordFamily values = ∑ i, values i := by
  change sumWordLoop values size 0 (by omega) (0:WordExt3).c0.val (0:WordExt3).c1.val (0:WordExt3).c2.val = _
  rw [sumWordLoop_eq]
  simp only [zero_add]

/-- Fold sampled columns with shared word weights and word accumulators. -/
@[macro_inline] def foldWordEvaluated {lanes columns : Nat} (word : Whir.Word E lanes columns)
    (point : Fin lanes → E) : Fin columns → E :=
  let coordinates := Vector.ofFn fun i : Fin lanes => WordExt3.ofField (point i)
  let weights := Keccak.Gkr.cubeWeights (fun i : Fin lanes => coordinates[i])
  fun column => WordExt3.toField (sumWordFamily fun i : Fin (2^lanes) =>
    sparseProduct weights[i] (WordExt3.ofField (word column (mask lanes i))))
/-- Word accumulation checks exactly the sampled-column multilinear extension. -/
theorem foldWordEvaluated_eq {lanes columns : Nat} (word : Whir.Word E lanes columns)
    (point : Fin lanes → E) : foldWordEvaluated word point = Whir.foldWord word point := by
  funext column
  unfold foldWordEvaluated Whir.foldWord Whir.mle
  rw [sumWordFamily_eq]
  change WordExt3.ringEquiv _ = _
  rw [map_sum]
  trans ∑ i : Fin (2^lanes), Whir.eqWeight point (mask lanes i) * word column (mask lanes i)
  · apply Finset.sum_congr rfl
    intro i _
    rw [sparseProduct_eq, map_mul]
    change WordExt3.toField _ * WordExt3.toField (WordExt3.ofField _) = _
    have weight := wordCubeWeight point i
    simp only [Fin.getElem_fin, Vector.getElem_ofFn] at weight ⊢
    rw [weight, WordExt3.toField_ofField]
  · simpa only [cubeEquiv_apply] using
      (cubeEquiv lanes).sum_comp (fun u => Whir.eqWeight point u * word column u)


/-- Resolve a sampled column's mask once before folding its extension-field rows. -/
@[macro_inline] def foldMaskedWordEvaluated {lanes columns : Nat}
    (word : Whir.MaskedWord E lanes columns) (point : Fin lanes → E) : Fin columns → E :=
  let coordinates := Vector.ofFn fun i : Fin lanes => WordExt3.ofField (point i)
  let weights := Keccak.Gkr.cubeWeights (fun i : Fin lanes => coordinates[i])
  fun column => match word column with
    | none => 0
    | some values => WordExt3.toField (sumWordFamily fun i : Fin (2^lanes) =>
        sparseProduct weights[i] (WordExt3.ofField (values (mask lanes i))))

/-- Resolving the mask before the row loop preserves zero-filled folding exactly. -/
theorem foldMaskedWordEvaluated_eq {lanes columns : Nat}
    (word : Whir.MaskedWord E lanes columns) (point : Fin lanes → E) :
    foldMaskedWordEvaluated word point = foldWordEvaluated (Whir.zeroFill word) point := by
  funext column
  cases known : word column with
  | none =>
      rw [foldWordEvaluated_eq]
      simp only [foldMaskedWordEvaluated, known, Whir.foldWord, Whir.mle, Whir.zeroFill,
        Option.getD_none, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  | some values =>
      simp only [foldMaskedWordEvaluated, foldWordEvaluated, Whir.zeroFill, known, Option.getD_some]


/-- Verify WHIR using multilinear evaluators and point concatenation for residuals. -/
def acceptsEvaluated : {n : Nat} → (schedule : EvaluatedSchedule n) →
    Whir.oracleMessage E schedule.schedule → List (EvaluatedClaim n) →
    (Whir.opening E schedule.schedule).tree.ExecutionPath → Bool
  | _, .last lanes tail enc queries, word, claims, path =>
      let batched := batchEvaluated claims path.1
      let round := Whir.readRounds (Whir.transition E (.last lanes tail enc.encoding queries))
        lanes batched.value path.2
      let residual : EvaluatedClaim tail := ⟨batched.weight.restrict round.2.1, round.1⟩
      let finalTable := round.2.2.2.1
      let xs := round.2.2.2.2.1
      let folded := foldMaskedWordEvaluated word round.2.1
      let finalClaims := residual :: List.ofFn (fun q : Fin queries =>
        (⟨enc.query (xs q), folded (xs q)⟩ : EvaluatedClaim tail))
      let finalBatch := batchEvaluated finalClaims round.2.2.2.2.2.1
      let closing := Whir.readRounds .done tail finalBatch.value round.2.2.2.2.2.2
      round.2.2.1 && Whir.queriesKnown word xs && closing.2.2.1 &&
        decide (sparseMul (WordExt3.toField (finalBatch.weight.evaluatePoint closing.2.1))
          (mleCached finalTable closing.2.1) = closing.1)
  | _, .more lanes enc queries rest, word, claims, path =>
      let batched := batchEvaluated claims path.1
      let round := Whir.readRounds (Whir.transition E (.more lanes enc.encoding queries rest.schedule))
        lanes batched.value path.2
      let residual := ⟨batched.weight.restrict round.2.1, round.1⟩
      let after := round.2.2.2
      let folded := foldMaskedWordEvaluated word round.2.1
      let claims' := residual :: (⟨.eq after.2.1, after.2.2.1⟩ : EvaluatedClaim _) ::
        List.ofFn (fun q : Fin queries =>
          (⟨enc.query (after.2.2.2.1 q), folded (after.2.2.2.1 q)⟩ : EvaluatedClaim _))
      round.2.2.1 && Whir.queriesKnown word after.2.2.2.1 && acceptsEvaluated rest after.1 claims' after.2.2.2.2

/-- Erasing a batch commutes with taking its weight. -/
theorem batchEvaluated_weight {n : Nat} (claims : List (EvaluatedClaim n)) (r : E) :
    (batchEvaluated claims r).weight.table = (Whir.batch (claims.map EvaluatedClaim.claim) r).weight :=
  congrArg Whir.Claim.weight (batchEvaluated_claim claims r)

/-- Erasing a batch commutes with taking its value. -/
theorem batchEvaluated_value {n : Nat} (claims : List (EvaluatedClaim n)) (r : E) :
    (batchEvaluated claims r).value = (Whir.batch (claims.map EvaluatedClaim.claim) r).value :=
  congrArg Whir.Claim.value (batchEvaluated_claim claims r)

/-- Every factored WHIR decision is equal to the original verifier's decision. -/
theorem acceptsEvaluated_eq {n : Nat} (schedule : EvaluatedSchedule n)
    (word : Whir.oracleMessage E schedule.schedule) (claims : List (EvaluatedClaim n))
    (path : (Whir.opening E schedule.schedule).tree.ExecutionPath) :
    acceptsEvaluated schedule word claims path =
      Whir.accepts (algebraMap K E) schedule.schedule word (claims.map EvaluatedClaim.claim) path := by
  induction schedule with
  | last lanes tail enc queries =>
    change acceptsEvaluated (.last lanes tail enc queries) word claims path =
      Whir.accepts (algebraMap K E) (.last lanes tail enc.encoding queries) word
        (claims.map EvaluatedClaim.claim) path
    rw [acceptsEvaluated, Whir.accepts]
    simp only [foldMaskedWordEvaluated_eq, foldWordEvaluated_eq, ← Whir.foldMaskedWord_getD, batchEvaluated_value, sparseMul_eq, mleCached_eq, EvaluatedWeight.evaluatePoint_eq,
      batchEvaluated_weight, List.map_cons, List.map_ofFn, Function.comp_def,
      EvaluatedClaim.claim, EvaluatedWeight.restrict, enc.query_table]
    rfl
  | more lanes enc queries rest ih =>
    change acceptsEvaluated (.more lanes enc queries rest) word claims path =
      Whir.accepts (algebraMap K E) (.more lanes enc.encoding queries rest.schedule) word
        (claims.map EvaluatedClaim.claim) path
    rw [acceptsEvaluated, ih, Whir.accepts]
    simp only [foldMaskedWordEvaluated_eq, foldWordEvaluated_eq, ← Whir.foldMaskedWord_getD, batchEvaluated_value, Whir.nextClaims, List.map_cons, List.map_ofFn, Function.comp_def,
      EvaluatedClaim.claim, EvaluatedWeight.restrict, EvaluatedWeight.eq_table,
      batchEvaluated_weight, enc.query_table]
    rfl

/-- Multiply an extension word by a base word while retaining zero and unit operands. -/
def baseProduct (a : WordExt3) (b : Word) : WordExt3 :=
  if b = 0 then 0 else if b = 1 then a else WordExt3.mulScalar a b
/-- Sparse base-word products equal the full mixed scalar product. -/
theorem baseProduct_eq (a : WordExt3) (b : Word) : baseProduct a b = WordExt3.mulScalar a b := by
  unfold baseProduct
  split_ifs with zero unit
  · subst b
    apply WordExt3.toField_injective
    rw [WordExt3.toField_mulScalar]
    change WordExt3.ringEquiv 0 = (0 : K) • a.toField
    rw [map_zero, zero_smul]
  · subst b
    apply WordExt3.toField_injective
    rw [WordExt3.toField_mulScalar]
    change a.toField = (1 : K) • a.toField
    rw [one_smul]
  · rfl
/-- Fold authenticated base words directly into extension-word accumulators. -/
@[macro_inline] def foldBaseWordEvaluated {lanes columns : Nat} (word : Whir.Word K lanes columns)
    (point : Fin lanes → E) : Fin columns → E :=
  let coordinates := Vector.ofFn fun i : Fin lanes => WordExt3.ofField (point i)
  let weights := CompStark.Keccak.Gkr.cubeWeights (fun i : Fin lanes => coordinates[i])
  fun column => WordExt3.toField (sumWordFamily fun i : Fin (2^lanes) =>
    baseProduct weights[i] (Word.ofField (word column (mask lanes i))))
/-- Direct base folding equals scalar extension followed by the protocol fold. -/
theorem foldBaseWordEvaluated_eq {lanes columns : Nat} (word : Whir.Word K lanes columns)
    (point : Fin lanes → E) :
    foldBaseWordEvaluated word point = Whir.foldWord (fun column row => ofK (word column row)) point := by
  funext column
  unfold foldBaseWordEvaluated Whir.foldWord Whir.mle
  rw [sumWordFamily_eq]
  change WordExt3.ringEquiv _ = _
  rw [map_sum]
  trans ∑ i : Fin (2^lanes), Whir.eqWeight point (mask lanes i) * ofK (word column (mask lanes i))
  · apply Finset.sum_congr rfl
    intro i _
    rw [baseProduct_eq]
    change WordExt3.toField (WordExt3.mulScalar _ _) = _
    rw [WordExt3.toField_mulScalar, Word.toField_ofField]
    have weight := wordCubeWeight point i
    simp only [Fin.getElem_fin, Vector.getElem_ofFn] at weight ⊢
    rw [weight, Algebra.smul_def]
    exact mul_comm _ _
  · simpa only [cubeEquiv_apply] using
      (cubeEquiv lanes).sum_comp (fun u => Whir.eqWeight point u * ofK (word column u))
/-- Resolve a sampled column's mask once before folding its base-field rows. -/
@[macro_inline] def foldMaskedBaseWordEvaluated {lanes columns : Nat}
    (word : Whir.MaskedWord K lanes columns) (point : Fin lanes → E) : Fin columns → E :=
  let coordinates := Vector.ofFn fun i : Fin lanes => WordExt3.ofField (point i)
  let weights := CompStark.Keccak.Gkr.cubeWeights (fun i : Fin lanes => coordinates[i])
  fun column => match word column with
    | none => 0
    | some values => WordExt3.toField (sumWordFamily fun i : Fin (2^lanes) =>
        baseProduct weights[i] (Word.ofField (values (mask lanes i))))

/-- Resolving the base mask before the row loop preserves scalar-extended folding exactly. -/
theorem foldMaskedBaseWordEvaluated_eq {lanes columns : Nat}
    (word : Whir.MaskedWord K lanes columns) (point : Fin lanes → E) :
    foldMaskedBaseWordEvaluated word point = foldBaseWordEvaluated (Whir.zeroFill word) point := by
  funext column
  cases known : word column with
  | none =>
      rw [foldBaseWordEvaluated_eq]
      simp only [foldMaskedBaseWordEvaluated, known, Whir.foldWord, Whir.mle, Whir.zeroFill,
        Option.getD_none, Pi.zero_apply, show ofK (0 : K) = (0 : E) from rfl, mul_zero, Finset.sum_const_zero]
  | some values =>
      simp only [foldMaskedBaseWordEvaluated, foldBaseWordEvaluated, Whir.zeroFill, known, Option.getD_some]

/-- Verify the initial base-field oracle without constructing extension elements per cell. -/
def acceptsBaseEvaluated : {n : Nat} → (schedule : EvaluatedSchedule n) →
    Whir.oracleMessage K schedule.schedule → List (EvaluatedClaim n) →
    (Whir.opening E schedule.schedule).tree.ExecutionPath → Bool
  | _, .last lanes tail enc queries, word, claims, path =>
      let batched := batchEvaluated claims path.1
      let round := Whir.readRounds (Whir.transition E (.last lanes tail enc.encoding queries))
        lanes batched.value path.2
      let residual : EvaluatedClaim tail := ⟨batched.weight.restrict round.2.1, round.1⟩
      let finalTable := round.2.2.2.1
      let xs := round.2.2.2.2.1
      let folded := foldMaskedBaseWordEvaluated word round.2.1
      let finalClaims := residual :: List.ofFn (fun q : Fin queries =>
        (⟨enc.query (xs q), folded (xs q)⟩ : EvaluatedClaim tail))
      let finalBatch := batchEvaluated finalClaims round.2.2.2.2.2.1
      let closing := Whir.readRounds .done tail finalBatch.value round.2.2.2.2.2.2
      round.2.2.1 && Whir.queriesKnown word xs && closing.2.2.1 &&
        decide (sparseMul (WordExt3.toField (finalBatch.weight.evaluatePoint closing.2.1))
          (mleCached finalTable closing.2.1) = closing.1)
  | _, .more lanes enc queries rest, word, claims, path =>
      let batched := batchEvaluated claims path.1
      let round := Whir.readRounds (Whir.transition E (.more lanes enc.encoding queries rest.schedule))
        lanes batched.value path.2
      let residual := ⟨batched.weight.restrict round.2.1, round.1⟩
      let after := round.2.2.2
      let folded := foldMaskedBaseWordEvaluated word round.2.1
      let claims' := residual :: (⟨.eq after.2.1, after.2.2.1⟩ : EvaluatedClaim _) ::
        List.ofFn (fun q : Fin queries =>
          (⟨enc.query (after.2.2.2.1 q), folded (after.2.2.2.1 q)⟩ : EvaluatedClaim _))
      round.2.2.1 && Whir.queriesKnown word after.2.2.2.1 && acceptsEvaluated rest after.1 claims' after.2.2.2.2

/-- Direct initial base-word checking preserves every WHIR branch and equation. -/
theorem acceptsBaseEvaluated_eq {n : Nat} (schedule : EvaluatedSchedule n)
    (word : Whir.oracleMessage K schedule.schedule) (claims : List (EvaluatedClaim n))
    (path : (Whir.opening E schedule.schedule).tree.ExecutionPath) :
    acceptsBaseEvaluated schedule word claims path =
      acceptsEvaluated schedule (Whir.mapMasked ofK word) claims path := by
  cases schedule with
  | last lanes tail enc queries =>
    rw [acceptsBaseEvaluated, acceptsEvaluated]
    have mapped : Whir.zeroFill (Whir.mapMasked ofK word) =
        (fun column row => ofK (Whir.zeroFill word column row)) :=
      Whir.zeroFill_mapMasked (algebraMap K E) word
    simp only [foldMaskedBaseWordEvaluated_eq, foldMaskedWordEvaluated_eq, foldBaseWordEvaluated_eq, foldWordEvaluated_eq, Whir.queriesKnown_mapMasked]
    rw [mapped]
  | more lanes enc queries rest =>
    rw [acceptsBaseEvaluated, acceptsEvaluated]
    have mapped : Whir.zeroFill (Whir.mapMasked ofK word) =
        (fun column row => ofK (Whir.zeroFill word column row)) :=
      Whir.zeroFill_mapMasked (algebraMap K E) word
    simp only [foldMaskedBaseWordEvaluated_eq, foldMaskedWordEvaluated_eq, foldBaseWordEvaluated_eq, foldWordEvaluated_eq, Whir.queriesKnown_mapMasked]
    rw [mapped]

end CompStark.Pcs
