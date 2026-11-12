/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.Radius
public import CompStark.Pcs.PackedEncoding
public import CompStark.Pcs.Conversion
public import CompPoly.Bivariate.GuruswamiSudan.Executable
public import CompPoly.Fields.Binary.BF64.GuruswamiSudan
public import CompPoly.Bivariate.GuruswamiSudan.Parameters.Production
public import CompPoly.Fields.Binary.AdditiveNTT.BasisConversion
public import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots
public import CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Correctness
public import CompPoly.Univariate.ToPoly.Degree
public import ArkLib.ProofSystem.Whir.Coding
public import Mathlib.Data.List.Pi
import all Init.Util

/-!
# Guruswami–Sudan input and interleaving adapter

CompPoly decodes scalar received words. Each WHIR row is passed through that backend,
converted from monomial polynomials to novel coefficients, and combined by Cartesian
product. A final simultaneous-column filter and deduplication give the required list
semantics. Certified scalar parameter selection and exact integer agreement cutoffs
connect the executable list to WHIR's analytical Johnson radius.
-/

set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

@[expose] public section

open CompStark.BinaryFields CompPoly CompPoly.GuruswamiSudan Polynomial Module
namespace CompStark.Pcs

/-- Executable scalar decoding with exact coverage at certified finite parameters. -/
structure GsScalarDecoder (S : Type) [Field S] [BEq S] [LawfulBEq S] where
  /-- Decode the packed received row at the exact integer mismatch radius. -/
  decode : Nat → Nat → GSReceivedWord S → Array (CPolynomial S)
  /-- Every returned polynomial and every nearby degree-bounded polynomial coincide. -/
  mem_iff : ∀ {k radius : Nat} (word : GSReceivedWord S) {params : GSExecParams},
    finiteGSParamSelector.choose k word.length radius = some params →
    DistinctXCoordinates word.points → ∀ p : CPolynomial S,
      p ∈ (decode k radius word).toList ↔
        degreeLt p k ∧ candidateMismatchCount word.points p ≤ radius
  /-- Convert returned monomial polynomials on the same certified executable carrier. -/
  convert : {r : Nat} → (Fin r → S) → (vars : Nat) → vars ≤ r → CPolynomial S → Array S
  /-- Executable carrier conversion preserves the original novel coefficient array. -/
  convert_eq : ∀ {r : Nat} (basis : Fin r → S) (vars : Nat) (h : vars ≤ r) (p : CPolynomial S),
    convert basis vars h p = AdditiveNTT.monomialToNovelArray basis vars h p

  /-- Encode every decoded candidate lane with one shared executable plan. -/
  encodeRows : (K →+* S) → (vars rate lanes : Nat) → vars + rate < 64 →
    Whir.Table S (lanes + vars) → Vector (Array S) (2 ^ lanes)
  /-- Encoded carrier rows agree in every valid column with the exact additive code. -/
  encodeRows_correct : ∀ [Fintype S] [Algebra (ZMod 2) S] (phi : K →+* S)
    (vars rate lanes : Nat) (h : vars + rate < 64) (f : Whir.Table S (lanes + vars))
    (row : Fin (2 ^ lanes)) (x : Fin (2 ^ (vars + rate))),
    ((encodeRows phi vars rate lanes h f)[row.val]).getD x.val 0 =
      (encoding vars rate h.le).encode phi (fun u => f (Fin.addCases (mask lanes row) u)) x

/-- Certified scalar decoding and coefficient conversion through the base word carrier. -/
def baseGsContext : GsScalarDecoder K :=
  ⟨BF64.decodeScalar, BF64.mem_decodeScalar_iff,
    mappedNovel BF64.Word.ringEquiv.symm, mappedNovel_eq BF64.Word.ringEquiv.symm,
    packedEncodingRows,
    by intro _ _; exact packedEncodingRows_correct⟩

/-- Certified decoding and coefficient conversion through the cubic word carrier. -/
def extensionGsContext : GsScalarDecoder E :=
  ⟨BF64.decodeExt3Scalar, BF64.mem_decodeExt3Scalar_iff,
    mappedNovel BF64.WordExt3.ringEquiv.symm, mappedNovel_eq BF64.WordExt3.ringEquiv.symm,
    scalarEncodingRows BF64.WordExt3.ringEquiv.symm,
    by intro _ _; exact scalarEncodingRows_correct BF64.WordExt3.ringEquiv.symm⟩

variable {S : Type} [Field S] [BEq S] [LawfulBEq S] [DecidableEq S]

/-- A scalar row on the embedded additive domain, in numeric column order. -/
def gsReceivedWord (phi : K →+* S) {vars lanes : ℕ} (enc : Whir.Encoding K vars)
    (word : Whir.Word S lanes (2 ^ (vars + enc.rate))) (row : Whir.Cube lanes) :
    GSReceivedWord S :=
  ⟨Array.ofFn fun x : enc.Columns => (phi (enc.domain x), word x row)⟩

/-- Recover novel coefficients from canonical monomial coefficients after scalar extension. -/
@[macro_inline] def polynomialMessage (phi : K →+* S) (vars : ℕ) (h : vars ≤ 64)
    (p : CPolynomial S) : Whir.Table S vars :=
  let coefficients := AdditiveNTT.monomialToNovelArray (fun j => phi (basis j)) vars h p
  fun u => coefficients.getD ((cubeEquiv vars).symm u).val 0

/-- The executable coefficient conversion reconstructs every degree-bounded polynomial. -/
theorem coefficientPolynomial_polynomialMessage [Fintype S] [Algebra (ZMod 2) S]
    (phi : K →+* S) (vars : ℕ) (h : vars ≤ 64)
    (p : CPolynomial S) (hp : p.toPoly.degree < ((2 ^ vars : ℕ) : WithBot ℕ)) :
    coefficientPolynomial phi vars h (polynomialMessage phi vars h p) =
      ⟨p.toPoly, mem_degreeLT.mpr hp⟩ := by
  unfold coefficientPolynomial polynomialMessage
  have convert := AdditiveNTT.monomialToNovelArray_eq_equivFun
    (ZMod 2) (fun j => phi (basis j)) vars h p hp
  simp only [← cubeEquiv_apply, Equiv.symm_apply_apply]
  change (novelBasis phi vars h).equivFun.symm _ = _
  rw [convert]
  exact LinearEquiv.symm_apply_apply _ _

/-- A row message materialized by the scalar context's certified carrier conversion. -/
@[macro_inline] def scalarMessage (phi : K →+* S) (vars : Nat) (h : vars ≤ 64)
    (ctx : GsScalarDecoder S) (p : CPolynomial S) : Whir.Table S vars :=
  let coefficients := ctx.convert (fun j => phi (basis j)) vars h p
  fun u => coefficients.getD ((cubeEquiv vars).symm u).val 0

omit [DecidableEq S] in
/-- The carrier implementation returns the exact specification row message. -/
theorem scalarMessage_eq (phi : K →+* S) (vars : Nat) (h : vars ≤ 64)
    (ctx : GsScalarDecoder S) (p : CPolynomial S) :
    scalarMessage phi vars h ctx p = polynomialMessage phi vars h p := by
  simp only [scalarMessage, polynomialMessage, ctx.convert_eq]

/-- Scalar GS outputs converted to novel coefficients with an executable degree check. -/
def gsRowCandidates (phi : K →+* S) (vars rate : ℕ) (h : vars + rate ≤ 64)
    (ctx : GsScalarDecoder S) (cutoff : ℕ) {lanes : ℕ}
    (word : Whir.Word S lanes (2 ^ (vars + rate))) (row : Whir.Cube lanes) :
    List (Whir.Table S vars) :=
  let decoded := ctx.decode (2 ^ vars) (2 ^ (vars + rate) - cutoff)
    (gsReceivedWord phi (encoding vars rate h) word row)
  decoded.toList.filterMap fun p =>
    if degreeLtBool p (2 ^ vars) then some (scalarMessage phi vars (by omega) ctx p) else none

/-- The novel coefficient message in one fixed interleaved row. -/
def rowMessage {vars lanes : ℕ} (f : Whir.Table S (lanes + vars))
    (row : Whir.Cube lanes) : Whir.Table S vars :=
  fun v => f (Fin.addCases row v)

/-- Reassemble an interleaved message from a candidate for every numeric row index. -/
def joinRows {vars lanes : ℕ} (rows : Fin (2 ^ lanes) → Whir.Table S vars) :
    Whir.Table S (lanes + vars) := fun u =>
  rows ((cubeEquiv lanes).symm (fun i => u (Fin.castAdd vars i)))
    (fun i => u (Fin.natAdd lanes i))

/-- Cartesian products combine the supplied scalar candidate lists without witness choice. -/
def rowProduct {vars lanes : ℕ}
    (rows : Whir.Cube lanes → List (Whir.Table S vars)) :
    List (Whir.Table S (lanes + vars)) :=
  (List.pi (List.finRange (2 ^ lanes)) (fun i => rows (mask lanes i))).map fun tuple =>
    joinRows (fun i => tuple i (List.mem_finRange i))

/-- Decode disjoint rows as Lean tasks and retain their numeric order in the product. -/
@[macro_inline] def rowProductParallel {vars lanes : Nat}
    (rows : Whir.Cube lanes → List (Whir.Table S vars)) :
    List (Whir.Table S (lanes + vars)) :=
  let jobs := Array.ofFn fun i : Fin (2 ^ lanes) => Task.spawn fun _ => rows (mask lanes i)
  let lists := jobs.map Task.get
  (List.pi (List.finRange (2 ^ lanes)) (fun i => lists[i.val]'(by
    simp only [lists, jobs, Array.size_map, Array.size_ofFn]
    exact i.isLt))).map fun tuple =>
    joinRows (fun i => tuple i (List.mem_finRange i))

/-- Parallel row evaluation preserves the exact ordered Cartesian product. -/
@[csimp] theorem rowProduct_code : @rowProduct = @rowProductParallel := by
  funext S vars lanes rows
  simp only [rowProduct, rowProductParallel, Array.getElem_map, Array.getElem_ofFn]
  rfl

/-- Number of columns agreeing in every interleaved row. -/
def agreementCount {vars lanes : ℕ} (enc : Whir.Encoding K vars) (phi : K →+* S)
    (word : Whir.Word S lanes (2 ^ (vars + enc.rate))) (f : Whir.Table S (lanes + vars)) : ℕ :=
  (Finset.univ.filter fun x => word x = enc.interleave phi f x).card

/-- Materialize the carrier-encoded rows once before simultaneous column comparison. -/
@[macro_inline] def interleaveDecoded (phi : K →+* S) (vars rate lanes : Nat)
    (h : vars + rate < 64) (ctx : GsScalarDecoder S) (f : Whir.Table S (lanes + vars)) :
    Whir.Word S lanes (2 ^ (vars + rate)) :=
  let rows := ctx.encodeRows phi vars rate lanes h f
  fun x row => rows[((cubeEquiv lanes).symm row).val].getD x.val 0

omit [DecidableEq S] in
/-- Carrier-encoded row images preserve the original interleaved encoding. -/
theorem interleaveDecoded_correct [Fintype S] [Algebra (ZMod 2) S]
    (phi : K →+* S) (vars rate lanes : Nat) (h : vars + rate < 64)
    (ctx : GsScalarDecoder S) (f : Whir.Table S (lanes + vars)) :
    interleaveDecoded phi vars rate lanes h ctx f =
      (encoding vars rate (Nat.le_of_lt h)).interleave phi f := by
  funext x row
  simp only [interleaveDecoded, ctx.encodeRows_correct,
    ← cubeEquiv_apply, Equiv.apply_symm_apply, Whir.Encoding.interleave]

omit [Field S] [BEq S] [LawfulBEq S] [DecidableEq S] in
/-- Numeric Boolean rows determine equality of interleaved columns. -/
theorem column_eq_iff_numeric {lanes : Nat} (left right : Whir.Cube lanes → S) :
    left = right ↔ ∀ row : Fin (2 ^ lanes), left (mask lanes row) = right (mask lanes row) := by
  constructor
  · intro same row
    exact congrFun same (mask lanes row)
  · intro same
    funext row
    simpa only [← cubeEquiv_apply, Equiv.apply_symm_apply] using same ((cubeEquiv lanes).symm row)

/-- Count simultaneous agreements using whole encoded rows within the butterfly domain. -/
def candidateAgreementCount (phi : K →+* S) (vars rate lanes : ℕ) (h : vars + rate ≤ 64)
    (ctx : GsScalarDecoder S) (word : Whir.Word S lanes (2 ^ (vars + rate)))
    (f : Whir.Table S (lanes + vars)) : ℕ :=
  if fast : vars + rate < 64 then
    let encoded := interleaveDecoded phi vars rate lanes fast ctx f
    (Finset.univ.filter fun x => ∀ row : Fin (2 ^ lanes),
      word x (mask lanes row) = encoded x (mask lanes row)).card
  else agreementCount (encoding vars rate h) phi word f

/-- Whole-row comparison counts exactly the specification's agreeing columns. -/
theorem candidateAgreementCount_eq [Fintype S] [Algebra (ZMod 2) S]
    (phi : K →+* S) (vars rate lanes : ℕ) (h : vars + rate ≤ 64)
    (ctx : GsScalarDecoder S) (word : Whir.Word S lanes (2 ^ (vars + rate))) (f : Whir.Table S (lanes + vars)) :
    candidateAgreementCount phi vars rate lanes h ctx word f =
      agreementCount (encoding vars rate h) phi word f := by
  unfold candidateAgreementCount
  split_ifs <;> simp only [← column_eq_iff_numeric, interleaveDecoded_correct, agreementCount]

/-- The certified scalar product, filtered at the exact simultaneous-column cutoff. -/
def gsDecode (phi : K →+* S) (vars rate lanes : ℕ) (h : vars + rate ≤ 64)
    (ctx : GsScalarDecoder S) (cutoff : ℕ) :
    Whir.Word S lanes (2 ^ (vars + rate)) → List (Whir.Table S (lanes + vars)) :=
  fun word =>
    (rowProduct (gsRowCandidates phi vars rate h ctx cutoff word)).filter
      (fun f => decide (cutoff ≤ candidateAgreementCount phi vars rate lanes h ctx word f)) |>.dedup

omit [Field S] [BEq S] [LawfulBEq S] [DecidableEq S] in
/-- Every full message whose rows occur in their candidate lists occurs in the product. -/
theorem mem_rowProduct_of_rows {vars lanes : ℕ}
    (rows : Whir.Cube lanes → List (Whir.Table S vars)) (f : Whir.Table S (lanes + vars))
    (hf : ∀ u, (rowMessage (vars := vars) (lanes := lanes) f u) ∈ rows u) : f ∈ rowProduct rows := by
  classical
  let tuple (i : Fin (2 ^ lanes)) (_hi : i ∈ List.finRange (2 ^ lanes)) : Whir.Table S vars :=
    fun v => f (Fin.addCases (mask lanes i) v)
  have htuple : tuple ∈ List.pi (List.finRange (2 ^ lanes)) (fun i => rows (mask lanes i)) :=
    (List.mem_pi _ tuple).mpr (fun i _ => hf (mask lanes i))
  apply List.mem_map.mpr
  refine ⟨tuple, htuple, ?_⟩
  funext u
  change f (Fin.addCases
    (mask lanes ((cubeEquiv lanes).symm (fun i => u (Fin.castAdd vars i))))
    (fun i => u (Fin.natAdd lanes i))) = f u
  have hmask : mask lanes ((cubeEquiv lanes).symm (fun i => u (Fin.castAdd vars i))) =
      (fun i => u (Fin.castAdd vars i)) := (cubeEquiv lanes).apply_symm_apply _
  rw [hmask]
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [Fin.addCases_left, Fin.addCases_right]


omit [BEq S] [LawfulBEq S] [DecidableEq S] in
/-- The full scalar domain has exactly the encoded word length. -/
theorem gsReceivedWord_length (phi : K →+* S) {vars lanes : ℕ} (enc : Whir.Encoding K vars)
    (word : Whir.Word S lanes (2 ^ (vars + enc.rate))) (row : Whir.Cube lanes) :
    (gsReceivedWord phi enc word row).length = 2 ^ (vars + enc.rate) := by
  simp only [gsReceivedWord, GSReceivedWord.length, Array.size_ofFn]

omit [BEq S] [LawfulBEq S] [DecidableEq S] in
/-- Injectivity of the embedded additive domain discharges scalar coordinate distinctness. -/
theorem gsReceivedWord_distinct (phi : K →+* S) {vars lanes : ℕ} (enc : Whir.Encoding K vars)
    (word : Whir.Word S lanes (2 ^ (vars + enc.rate))) (row : Whir.Cube lanes) :
    DistinctXCoordinates (gsReceivedWord phi enc word row).points := by
  simp only [DistinctXCoordinates, gsReceivedWord, Array.toList_ofFn, List.map_ofFn]
  exact List.nodup_ofFn.mpr (phi.injective.comp enc.domain.injective)

omit [DecidableEq S] in
/-- The canonical array degree predicate is exactly the mathematical message degree. -/
theorem degreeLtBool_iff (p : CPolynomial S) (k : ℕ) :
    degreeLtBool p k = true ↔ p.toPoly.degree < (k : WithBot ℕ) := by
  simp only [degreeLtBool, decide_eq_true_eq, ← CPolynomial.mem_degreeLT_iff_size_le,
    CPolynomial.mem_degreeLT, ← CPolynomial.degree_toPoly]

/-- The simultaneous integer filter makes every returned message close at its cutoff. -/
theorem gsDecode_sound [Fintype S] [Algebra (ZMod 2) S] (phi : K →+* S) (vars rate lanes : ℕ) (h : vars + rate ≤ 64)
    (ctx : GsScalarDecoder S) (cutoff : ℕ)
    (word : Whir.Word S lanes (2 ^ (vars + rate))) (f : Whir.Table S (lanes + vars))
    (hf : f ∈ (gsDecode phi vars rate lanes h ctx cutoff) word) :
    cutoff ≤ agreementCount (encoding vars rate h) phi word f := by
  have check := of_decide_eq_true ((List.mem_filter.mp (List.mem_dedup.mp hf)).2)
  simpa only [candidateAgreementCount_eq] using check

/-- Finite-table equality removes duplicates constructively. -/
theorem gsDecode_nodup (phi : K →+* S) (vars rate lanes : ℕ) (h : vars + rate ≤ 64)
    (ctx : GsScalarDecoder S) (cutoff : ℕ)
    (word : Whir.Word S lanes (2 ^ (vars + rate))) :
    ((gsDecode phi vars rate lanes h ctx cutoff) word).Nodup :=
  List.nodup_dedup _

/-- Number of agreements in one scalar received row. -/
def rowAgreementCount (phi : K →+* S) {vars lanes : ℕ} (enc : Whir.Encoding K vars)
    (word : Whir.Word S lanes (2 ^ (vars + enc.rate))) (row : Whir.Cube lanes)
    (f : Whir.Table S vars) : ℕ :=
  (Finset.univ.filter fun x => word x row = enc.encode phi f x).card

/-- The backend's packed agreement counter is the additive-domain agreement count. -/
theorem matchingPointCount_eq_card (phi : K →+* S) {vars lanes : ℕ}
    (enc : Whir.Encoding K vars) (word : Whir.Word S lanes (2 ^ (vars + enc.rate)))
    (row : Whir.Cube lanes) (p : CPolynomial S) :
    matchingPointCount (gsReceivedWord phi enc word row).points p =
      (Finset.univ.filter fun x : enc.Columns =>
        word x row = CPolynomial.eval (phi (enc.domain x)) p).card := by
  unfold matchingPointCount gsReceivedWord
  rw [← Array.foldl_toList, Array.toList_ofFn]
  have fold (xs : List (S × S)) (n : ℕ) :
      xs.foldl (fun count point => if CPolynomial.eval point.1 p == point.2
        then count + 1 else count) n =
      n + (xs.map fun point => if CPolynomial.eval point.1 p == point.2 then 1 else 0).sum := by
    induction xs generalizing n with
    | nil => simp only [List.foldl_nil, List.map_nil, List.sum_nil, Nat.add_zero]
    | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      split_ifs <;> rw [ih] <;> omega
  rw [fold, Nat.zero_add, List.map_ofFn, List.sum_ofFn, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Function.comp_apply, beq_iff_eq]
  congr 1
  exact propext eq_comm

/-- Scalar coverage at a natural agreement cutoff on the actual additive encoding. -/
def GsRowCoverage (phi : K →+* S) (vars rate lanes : ℕ) (h : vars + rate ≤ 64)
    (ctx : GsScalarDecoder S) (cutoff : ℕ) : Prop :=
  ∀ (word : Whir.Word S lanes (2 ^ (vars + rate))) (row : Whir.Cube lanes) f,
    cutoff ≤ rowAgreementCount phi (encoding vars rate h) word row f →
      f ∈ gsRowCandidates phi vars rate h ctx cutoff word row

/-- Certified parameter selection supplies scalar coverage without a per-word assumption. -/
theorem gsRowCoverage_of_selection [Fintype S] [Algebra (ZMod 2) S]
    (phi : K →+* S) (vars rate lanes : ℕ) (h : vars + rate ≤ 64)
    (ctx : GsScalarDecoder S) (cutoff : ℕ) (hcutoff : cutoff ≤ 2 ^ (vars + rate))
    (params : GSExecParams)
    (selected : finiteGSParamSelector.choose (2 ^ vars) (2 ^ (vars + rate))
      (2 ^ (vars + rate) - cutoff) = some params) :
    GsRowCoverage phi vars rate lanes h ctx cutoff := by
  classical
  intro word row f close
  let spec := coefficientPolynomial phi vars (by omega) f
  let p : CPolynomial S := CPolynomial.toPolyLinearEquiv.symm spec.val
  have hp : p.toPoly = spec.val := by
    simpa only [CPolynomial.toPolyLinearEquiv_apply] using
      (CPolynomial.toPolyLinearEquiv.apply_symm_apply spec.val)
  have degree : p.toPoly.degree < ((2 ^ vars : ℕ) : WithBot ℕ) := by
    rw [hp]
    exact mem_degreeLT.mp spec.property
  have represents : polynomialMessage phi vars (by omega) p = f := by
    apply (coefficientPolynomial_bijective phi vars (by omega)).injective
    rw [coefficientPolynomial_polynomialMessage phi vars (by omega) p degree]
    exact Subtype.ext hp
  have hmatches : matchingPointCount (gsReceivedWord phi (encoding vars rate h) word row).points p =
      rowAgreementCount phi (encoding vars rate h) word row f := by
    rw [matchingPointCount_eq_card]
    unfold rowAgreementCount
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change Fin (2 ^ (vars + rate)) at x
    rw [CPolynomial.eval_toPoly, hp]
    change word x row = spec.val.eval (phi (domain h x)) ↔ _
    rw [← encode_eq_eval phi vars rate h f x]
  have counts := matchingPointCount_add_candidateMismatchCount
    (gsReceivedWord phi (encoding vars rate h) word row).points p
  have length : (gsReceivedWord phi (encoding vars rate h) word row).points.size =
      2 ^ (vars + rate) := Array.size_ofFn
  have decoded : p ∈ (ctx.decode (2 ^ vars)
      (2 ^ (vars + rate) - cutoff)
      (gsReceivedWord phi (encoding vars rate h) word row)).toList := by
    apply (ctx.mem_iff
      (gsReceivedWord phi (encoding vars rate h) word row)
      (by rw [gsReceivedWord_length]; exact selected)
      (gsReceivedWord_distinct phi (encoding vars rate h) word row) p).mpr
    constructor
    · simpa only [degreeLt, CPolynomial.degree_toPoly] using degree
    · rw [hmatches, length] at counts
      omega
  apply List.mem_filterMap.mpr
  refine ⟨p, decoded, ?_⟩
  simp only [(degreeLtBool_iff p _).mpr degree, ↓reduceIte, scalarMessage_eq, represents]

omit [BEq S] [LawfulBEq S] in
/-- Every simultaneous agreeing column agrees in each scalar row. -/
theorem agreementCount_le_rowAgreementCount (phi : K →+* S) {vars lanes : ℕ}
    (enc : Whir.Encoding K vars) (word : Whir.Word S lanes (2 ^ (vars + enc.rate)))
    (f : Whir.Table S (lanes + vars)) (row : Whir.Cube lanes) :
    agreementCount enc phi word f ≤ rowAgreementCount phi enc word row (rowMessage f row) := by
  apply Finset.card_le_card
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrFun (Finset.mem_filter.mp hx).2 row⟩

/-- Scalar coverage and the simultaneous filter give exact interleaved membership. -/
theorem gsDecode_mem_iff [Fintype S] [Algebra (ZMod 2) S] (phi : K →+* S) (vars rate lanes : ℕ) (h : vars + rate ≤ 64)
    (ctx : GsScalarDecoder S) (cutoff : ℕ)
    (coverage : GsRowCoverage phi vars rate lanes h ctx cutoff)
    (word : Whir.Word S lanes (2 ^ (vars + rate))) (f : Whir.Table S (lanes + vars)) :
    f ∈ (gsDecode phi vars rate lanes h ctx cutoff) word ↔
      cutoff ≤ agreementCount (encoding vars rate h) phi word f := by
  constructor
  · exact gsDecode_sound phi vars rate lanes h ctx cutoff word f
  · intro close
    have rows : ∀ row : Whir.Cube lanes,
        rowMessage (vars := vars) (lanes := lanes) f row ∈
          gsRowCandidates phi vars rate h ctx cutoff word row := by
      intro row
      exact coverage word row (rowMessage (vars := vars) (lanes := lanes) f row)
        (close.trans (agreementCount_le_rowAgreementCount phi (encoding vars rate h) word f row))
    exact List.mem_dedup.mpr (List.mem_filter.mpr
      ⟨mem_rowProduct_of_rows (vars := vars) (lanes := lanes)
        (gsRowCandidates phi vars rate h ctx cutoff word) f rows, decide_eq_true (by simpa only [candidateAgreementCount_eq] using close)⟩)

/-- Exact agreement cutoff at an analytical radius; the real parameter is proof-only. -/
def CutoffCorrect (vars rate cutoff : ℕ) (gamma : ℝ) : Prop :=
  ∀ a : ℕ, a ≤ 2 ^ (vars + rate) →
    (cutoff ≤ a ↔ (1 - gamma) * (2 ^ (vars + rate) : ℕ) ≤ (a : ℝ))

omit [Field S] [BEq S] [LawfulBEq S] [DecidableEq S] in
/-- Integer Johnson search realizes the reduced-rate square-root radius exactly. -/
theorem johnsonCutoff_correct (vars rate m : ℕ) (hm : 0 < m)
    (hfull : johnsonAgreement (2 ^ vars) (2 ^ (vars + rate)) m (2 ^ (vars + rate))) :
    CutoffCorrect vars rate (agreementCutoff (2 ^ vars) (2 ^ (vars + rate)) m)
      (1 - (1 + 1 / (m : ℝ)) *
        Real.sqrt (((2 ^ vars - 1 : ℕ) : ℝ) / 2 ^ (vars + rate))) := by
  intro a ha
  rw [agreementCutoff_le_iff _ _ _ hfull a ha, johnsonAgreement_iff_real _ _ _ _ hm
    (Nat.two_pow_pos _)]
  simp only [sub_sub_cancel, Nat.cast_pow, Nat.cast_ofNat]

omit [BEq S] [LawfulBEq S] in
/-- A certified discrete cutoff is WHIR's exact simultaneous-column proximity predicate. -/
theorem cutoff_iff_close (phi : K →+* S) (vars rate lanes : ℕ) (h : vars + rate ≤ 64)
    (cutoff : ℕ) (gamma : ℝ) (correct : CutoffCorrect vars rate cutoff gamma)
    (word : Whir.Word S lanes (2 ^ (vars + rate))) (f : Whir.Table S (lanes + vars)) :
    cutoff ≤ agreementCount (encoding vars rate h) phi word f ↔
      Whir.Close gamma (Whir.fullWord word) ((encoding vars rate h).interleave phi f) := by
  have bound : agreementCount (encoding vars rate h) phi word f ≤ 2 ^ (vars + rate) :=
    (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin _)
  rw [correct _ bound]
  unfold Whir.Close Whir.agreement Whir.fullWord agreementCount
  simp only [Function.comp_apply, Option.some.injEq]

/-- Count revealed-column agreements after encoding each candidate row once. -/
def maskedCandidateAgreementCount (phi : K →+* S) (vars rate lanes : ℕ)
    (h : vars + rate ≤ 64) (ctx : GsScalarDecoder S)
    (word : Whir.MaskedWord S lanes (2 ^ (vars + rate)))
    (candidate : Whir.Table S (lanes + vars)) : ℕ :=
  if fast : vars + rate < 64 then
    let encoded := interleaveDecoded phi vars rate lanes fast ctx candidate
    (Finset.univ.filter fun x => (match word x with
      | none => false
      | some column => decide (∀ row : Fin (2 ^ lanes), column (mask lanes row) = encoded x (mask lanes row))) = true).card
  else (Whir.agreement word ((encoding vars rate h).interleave phi candidate)).card

/-- Materialized row encoding counts exactly the absolute masked agreement set. -/
theorem maskedCandidateAgreementCount_eq [Fintype S] [Algebra (ZMod 2) S]
    (phi : K →+* S) (vars rate lanes : ℕ) (h : vars + rate ≤ 64) (ctx : GsScalarDecoder S)
    (word : Whir.MaskedWord S lanes (2 ^ (vars + rate)))
    (candidate : Whir.Table S (lanes + vars)) :
    maskedCandidateAgreementCount phi vars rate lanes h ctx word candidate =
      (Whir.agreement word ((encoding vars rate h).interleave phi candidate)).card := by
  unfold maskedCandidateAgreementCount
  split_ifs with fast
  · simp only [interleaveDecoded_correct, Whir.agreement]
    congr 1
    apply Finset.filter_congr
    intro x _
    cases word x <;> simp only [Bool.false_eq_true, reduceCtorEq, Option.some.injEq,
      decide_eq_true_eq, ← column_eq_iff_numeric]
  · rfl

/-- Materialize encoded columns from the certified row encoder. -/
def candidateColumns (phi : K →+* S) (vars rate lanes : ℕ) (h : vars + rate ≤ 64)
    (ctx : GsScalarDecoder S) (candidate : Whir.Table S (lanes + vars)) :
    Vector (Whir.Cube lanes → S) (2 ^ (vars + rate)) :=
  if fast : vars + rate < 64 then
    let rows := ctx.encodeRows phi vars rate lanes fast candidate
    Vector.ofFn fun x row => rows[((cubeEquiv lanes).symm row).val].getD x.val 0
  else Vector.ofFn ((encoding vars rate h).interleave phi candidate)

omit [DecidableEq S] in
/-- Materialized candidate columns agree with the exact interleaved encoding. -/
theorem candidateColumns_eq [Fintype S] [Algebra (ZMod 2) S]
    (phi : K →+* S) (vars rate lanes : ℕ) (h : vars + rate ≤ 64)
    (ctx : GsScalarDecoder S) (candidate : Whir.Table S (lanes + vars))
    (x : Fin (2 ^ (vars + rate))) :
    (candidateColumns phi vars rate lanes h ctx candidate)[x.val] =
      (encoding vars rate h).interleave phi candidate x := by
  unfold candidateColumns
  split_ifs with fast
  · funext row
    simp only [Vector.getElem_ofFn, ctx.encodeRows_correct,
      ← cubeEquiv_apply, Equiv.apply_symm_apply, Whir.Encoding.interleave]
  · simp only [Vector.getElem_ofFn]

/-- Zero-fill candidate generation with a materialized masked agreement filter. -/
def maskedListDecoder (phi : K →+* S) (vars rate lanes : ℕ) (h : vars + rate ≤ 64)
    (ctx : GsScalarDecoder S) (cutoff : ℕ)
    (decode : Whir.Word S lanes (2 ^ (vars + rate)) → List (Whir.Table S (lanes + vars))) :
    Whir.ListDecoder (E := S) (encoding vars rate h) lanes where
  encodeColumns := candidateColumns phi vars rate lanes h ctx
  decode word := (decode (Whir.zeroFill word)).filter fun candidate =>
    decide (cutoff ≤ maskedCandidateAgreementCount phi vars rate lanes h ctx word candidate)

/-- The executable masked filter is precisely the generic zero-fill decoder. -/
theorem maskedListDecoder_decode_eq [Fintype S] [Algebra (ZMod 2) S]
    (phi : K →+* S) (vars rate lanes : ℕ) (h : vars + rate ≤ 64)
    (ctx : GsScalarDecoder S) (cutoff : ℕ)
    (decode : Whir.Word S lanes (2 ^ (vars + rate)) → List (Whir.Table S (lanes + vars))) :
    (maskedListDecoder phi vars rate lanes h ctx cutoff decode).decode =
      (Whir.ListDecoder.ofZeroFill phi cutoff decode).decode := by
  unfold maskedListDecoder Whir.ListDecoder.ofZeroFill
  funext word
  simp only [maskedCandidateAgreementCount_eq]

/-- Masked decoding uses zero fill for candidate generation and filters the actual revealed columns. -/
def gsListDecoder (phi : K →+* S) (vars rate lanes : ℕ) (h : vars + rate ≤ 64)
    (ctx : GsScalarDecoder S) (cutoff : ℕ) :
    Whir.ListDecoder (E := S) (encoding vars rate h) lanes :=
  maskedListDecoder phi vars rate lanes h ctx cutoff (gsDecode phi vars rate lanes h ctx cutoff)

/-- Certified scalar coverage supplies exact WHIR membership and its Johnson list bound. -/
theorem gsListDecoder_correct [Fintype S] [Algebra (ZMod 2) S]
    (phi : K →+* S) (vars rate lanes : ℕ) (h : vars + rate ≤ 64)
    (ctx : GsScalarDecoder S) (cutoff : ℕ) (hcutoff : cutoff ≤ 2 ^ (vars + rate))
    (params : GSExecParams)
    (selected : finiteGSParamSelector.choose (2 ^ vars) (2 ^ (vars + rate))
      (2 ^ (vars + rate) - cutoff) = some params)
    (sec : Whir.LevelSecurity) (valid : sec.Valid (encoding vars rate h))
    (correct : CutoffCorrect vars rate cutoff (Whir.radius (encoding vars rate h) sec)) :
    (gsListDecoder phi vars rate lanes h ctx cutoff).Correct phi
      (Whir.radius (encoding vars rate h) sec) (Whir.listBound (encoding vars rate h) sec) := by
  classical
  change (maskedListDecoder phi vars rate lanes h ctx cutoff
    (gsDecode phi vars rate lanes h ctx cutoff)).Correct phi _ _
  have membership (word : Whir.Word S lanes (2 ^ (vars + rate))) (f : Whir.Table S (lanes + vars)) :
      f ∈ gsDecode phi vars rate lanes h ctx cutoff word ↔
        Whir.Close (Whir.radius (encoding vars rate h) sec) (Whir.fullWord word)
          ((encoding vars rate h).interleave phi f) :=
    (gsDecode_mem_iff phi vars rate lanes h ctx cutoff
      (gsRowCoverage_of_selection phi vars rate lanes h ctx cutoff hcutoff params selected) word f).trans
      (cutoff_iff_close phi vars rate lanes h cutoff _ correct word f)
  have reference := Whir.nearbyDecoder_correct (encoding vars rate h) phi
    (encodingContract phi vars rate h valid.2.1) sec valid lanes
  refine ⟨fun word => (gsDecode_nodup phi vars rate lanes h ctx cutoff _).filter _, ?_, ?_, ?_⟩
  · intro word f
    have bound : (Whir.agreement word ((encoding vars rate h).interleave phi f)).card ≤
        2 ^ (vars + rate) := (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin _)
    have close : cutoff ≤ (Whir.agreement word ((encoding vars rate h).interleave phi f)).card ↔
        Whir.Close (Whir.radius (encoding vars rate h) sec) word
          ((encoding vars rate h).interleave phi f) := correct _ bound
    simp only [maskedListDecoder_decode_eq, Whir.ListDecoder.ofZeroFill, List.mem_filter, decide_eq_true_eq,
      membership, close]
    exact ⟨fun hf => hf.2, fun hf => ⟨hf.zeroFill, hf⟩⟩
  · intro word
    have perm : (gsDecode phi vars rate lanes h ctx cutoff (Whir.zeroFill word)).Perm
        ((Whir.nearbyDecoder (encoding vars rate h) phi
          (Whir.radius (encoding vars rate h) sec) lanes).decode (Whir.fullWord (Whir.zeroFill word))) := by
      apply (List.perm_ext_iff_of_nodup
        (gsDecode_nodup phi vars rate lanes h ctx cutoff _) (reference.nodup _)).mpr
      intro f
      exact (membership _ f).trans (reference.mem_iff _ f).symm
    rw [maskedListDecoder_decode_eq]
    exact (Nat.cast_le.mpr (List.length_filter_le _ _)).trans
      ((Nat.cast_le.mpr perm.length_eq.le).trans (reference.length_le _))
  · exact candidateColumns_eq phi vars rate lanes h ctx

/-- Unconditional scalar GS coverage at the initial production parameters. -/
theorem gsRowCoverage_initial [Fintype S] [Algebra (ZMod 2) S]
    (phi : K →+* S) (ctx : GsScalarDecoder S) (lanes : ℕ) :
    GsRowCoverage phi 13 1 lanes (by decide) ctx 15447 :=
  gsRowCoverage_of_selection phi 13 1 lanes (by decide) ctx 15447 (by decide) _
    finiteGSParamSelector_initial

/-- Unconditional scalar GS coverage at the middle production parameters. -/
theorem gsRowCoverage_middle [Fintype S] [Algebra (ZMod 2) S]
    (phi : K →+* S) (ctx : GsScalarDecoder S) (lanes : ℕ) :
    GsRowCoverage phi 9 4 lanes (by decide) ctx 2728 :=
  gsRowCoverage_of_selection phi 9 4 lanes (by decide) ctx 2728 (by decide) _
    finiteGSParamSelector_middle

/-- Unconditional scalar GS coverage at the final production parameters. -/
theorem gsRowCoverage_final [Fintype S] [Algebra (ZMod 2) S]
    (phi : K →+* S) (ctx : GsScalarDecoder S) (lanes : ℕ) :
    GsRowCoverage phi 5 7 lanes (by decide) ctx 476 :=
  gsRowCoverage_of_selection phi 5 7 lanes (by decide) ctx 476 (by decide) _
    finiteGSParamSelector_final

end CompStark.Pcs
