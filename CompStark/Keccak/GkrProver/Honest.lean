/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.Kernels
public import CompStark.Keccak.Gkr.SumcheckExecution
public import CompStark.Keccak.Gkr.BetaBoundary
public import CompStark.Keccak.Gkr.OpeningAlgebra

/-! Honest coefficient messages and the compressed sumcheck completeness contract. -/

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr Polynomial
open scoped BigOperators

/-- The honest degree-46 message selects the actual RMFE product coefficients. -/
noncomputable def honestProductMessage {F : Type*} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : CompStark.Keccak.Gkr.Claim F p) : Fin 47 → F :=
  fun i => (honestProduct q d c).coeff i.val

/-- The 47 coefficients retain the complete honest polynomial. -/
theorem honestProductMessage_polynomial {F : Type*} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : CompStark.Keccak.Gkr.Claim F p) :
    messagePolynomial (honestProductMessage q d c) = honestProduct q d c := by
  unfold messagePolynomial honestProductMessage
  rw [show (∑ i : Fin 47, (monomial i.val) ((honestProduct q d c).coeff i.val)) =
    ∑ k ∈ Finset.range 47, (monomial k) ((honestProduct q d c).coeff k) from
      Fin.sum_univ_eq_sum_range (fun k => (monomial k) ((honestProduct q d c).coeff k)) 47]
  exact ((honestProduct q d c).as_sum_range' 47 (by
    exact Nat.lt_succ_of_le (natDegree_le_of_degree_le (honestProduct_degree q d c)))).symm

/-- Product evaluation in transmitted coefficient form is the protocol's honest product. -/
theorem honestProductMessage_eval {F : Type*} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : CompStark.Keccak.Gkr.Claim F p) (r : F) :
    polyEval (honestProductMessage q d c) r = (honestProduct q d c).eval r := by
  rw [← messagePolynomial_eval, honestProductMessage_polynomial]

/-- Honest product messages satisfy the verifier projection check on every valid entering claim. -/
theorem honestProductMessage_valid {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : CompStark.Keccak.Gkr.Claim F p)
    (hc : ClaimHolds q d.castSucc c) :
    (∑ i, c.mu i * projectMessage (honestProductMessage q d c) i) +
      constantContribution d c = c.value := by
  have h := (layer_projection_identity q d c).mp hc
  simpa only [← project_messagePolynomial, honestProductMessage_polynomial] using h

/-- The first honest sumcheck polynomial, restricted before the fresh coordinate. -/
noncomputable def firstHonestPolynomial {F : Type} [CommRing F] {n degree : Nat}
    (f : (Fin (n+1) → F) → F) (hf : CoordinateDegree f degree) : F⦃≤ degree⦄[X] :=
  ⟨Classical.choose (first_projection_exists f hf),
    Polynomial.mem_degreeLE.mpr (Classical.choose_spec (first_projection_exists f hf)).1⟩

/-- The polynomial's evaluation is the honest remaining Boolean sum. -/
theorem firstHonestPolynomial_eval {F : Type} [CommRing F] {n degree : Nat}
    (f : (Fin (n+1) → F) → F) (hf : CoordinateDegree f degree) (r : F) :
    (firstHonestPolynomial f hf).val.eval r = booleanSum (fun point => f (Fin.cons r point)) :=
  (Classical.choose_spec (first_projection_exists f hf)).2 r

/-- Boolean endpoints of the honest polynomial give the entering claim. -/
theorem firstHonestPolynomial_sum {F : Type} [CommRing F] {n degree : Nat}
    (f : (Fin (n+1) → F) → F) (hf : CoordinateDegree f degree) :
    (firstHonestPolynomial f hf).val.eval 0 + (firstHonestPolynomial f hf).val.eval 1 = booleanSum f := by
  rw [firstHonestPolynomial_eval, firstHonestPolynomial_eval, booleanSum_succ]

/-- Honest compressed messages choose a polynomial before binding each successive coordinate. -/
noncomputable def honestCompressedRounds {F : Type} [CommRing F] {degree : Nat} :
    {n : Nat} → (f : (Fin n → F) → F) → CoordinateDegree f (degree+1) →
      (Fin n → F) → Fin n → Sumcheck.CompressedMessage F degree
  | 0, _, _, _ => Fin.elim0
  | _+1, f, hf, point => Fin.cons (Sumcheck.compress (firstHonestPolynomial f hf))
      (honestCompressedRounds (fun r => f (Fin.cons (point 0) r)) (hf.tail (point 0)) (fun i => point i.succ))

/-- Full compressed decoding recovers the honest first-round polynomial, including its omitted coefficient. -/
theorem honestCompressed_first {F : Type} [CommRing F] {n degree : Nat}
    (f : (Fin (n+1) → F) → F) (hf : CoordinateDegree f (degree+1)) (r : F) :
    (Sumcheck.compressedOps degree).evaluate (booleanSum f)
      (Sumcheck.compress (firstHonestPolynomial f hf)) r =
      booleanSum (fun point => f (Fin.cons r point)) := by
  rw [Sumcheck.compressed_evaluate_eq,
    Sumcheck.compressed_compress _ _ (firstHonestPolynomial_sum f hf), firstHonestPolynomial_eval]

/-- Every compressed round satisfies the deterministic Boolean-sum acceptance predicate. -/
theorem compressedRounds_valid {F : Type} [CommRing F] {n degree : Nat}
    (messages : Fin n → Sumcheck.CompressedMessage F degree) (point : Fin n → F) (value : F) :
    roundsValid (fun _ => Sumcheck.compressedOps degree) messages point value := by
  induction n generalizing value with
  | zero => trivial
  | succ n ih => exact ⟨rfl, ih _ _ _⟩

/-- Honest compressed sumchecks are complete for every sequence of verifier challenges. -/
theorem honestCompressedRounds_complete {F : Type} [CommRing F] {n degree : Nat}
    (f : (Fin n → F) → F) (hf : CoordinateDegree f (degree+1)) (point : Fin n → F) :
    roundsEnd (fun _ => Sumcheck.compressedOps degree) (honestCompressedRounds f hf point)
      point (booleanSum f) = f point := by
  induction n with
  | zero =>
    simp only [roundsEnd, booleanSum, Finset.univ_unique, Finset.sum_singleton]
    congr 1
    funext i
    exact i.elim0
  | succ n ih =>
    simp only [honestCompressedRounds, roundsEnd, Fin.cons_zero, Fin.cons_succ]
    rw [honestCompressed_first]
    rw [ih]
    congr 1
    exact Fin.cons_self_tail point

/-- The exact two-to-one table used to bind the least significant cube variable. -/
def foldCube {F : Type*} [CommRing F] {n : Nat}
    (table : Fin (2^(n+1)) → F) (r : F) (i : Fin (2^n)) : F :=
  line (table ⟨2*i.val, by rw [pow_succ]; omega⟩)
    (table ⟨2*i.val+1, by rw [pow_succ]; omega⟩) r

/-- Binding a table variable preserves its multilinear evaluation at every suffix point. -/
theorem foldCube_mle {F : Type*} [CommRing F] [CharP F 2] {n : Nat}
    (table : Fin (2^(n+1)) → F) (r : F) (point : Fin n → F) :
    mle (foldCube table r) point = mle table (Fin.cons r point) := by
  let f (low : Fin 2) (high : Fin (2^n)) : F := table ⟨low.val+2*high.val, by
    rw [pow_succ]; omega⟩
  have split := mle_blocks (n := n+1) (a := 1) (b := n) (by omega) f (Fin.cons r point)
  have recover : (fun w : Fin (2^(n+1)) =>
      f ⟨w.val%2,Nat.mod_lt _ (by decide)⟩ ⟨w.val/2,by
        apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
        simpa only [pow_succ, Nat.mul_comm] using w.isLt⟩) = table := by
    funext w
    dsimp only [f]
    congr 1
    apply Fin.ext
    change w.val%2+2*(w.val/2) = w.val
    omega
  change mle _ (Fin.cons r point) = _ at split
  simp only [pow_one] at split
  rw [recover] at split
  rw [split]
  unfold mle
  apply Finset.sum_congr rfl
  intro i _
  have pointEq : (fun j : Fin n => (Fin.cons r point : Fin (n+1) → F) (⟨1+j.val, by omega⟩ : Fin (n+1))) = point := by
    funext j
    have hj : (⟨1+j.val, by omega⟩ : Fin (n+1)) = j.succ :=
      Fin.ext (Nat.add_comm 1 j.val)
    rw [hj]
    rfl
  rw [pointEq]
  congr 1
  simp only [eqWeight, Fin.prod_univ_one]
  change line (table ⟨2*i.val, _⟩) (table ⟨2*i.val+1, _⟩) r =
    ∑ x : Fin 2, (if x.val.testBit 0 then r else 1-r) * f x i
  rw [Fin.sum_univ_two, line_eq]
  change (1-r)*table ⟨2*i.val, _⟩+r*table ⟨2*i.val+1, _⟩ =
    (1-r)*table ⟨0+2*i.val, _⟩+r*table ⟨1+2*i.val, _⟩
  simp only [Nat.zero_add, Nat.add_comm 1]

/-- Claim-aware quadratic cofactor decoding equals the honest equality-factored cubic. -/
theorem cofactor_decode {F : Type} [CommRing F] [CharP F 2] (a b c r s : F) :
    (cofactorOps r).evaluate (a+r*(b+c)) (b, fun _ => c) s =
      (1+r+s)*(a+b*s+c*s^2) := by
  simp only [cofactorOps]
  have h := CharTwo.add_self_eq_zero (r*(b+c))
  congr 1
  linear_combination h

/-- Function-indexed and integer-indexed Boolean sums enumerate the same protocol cube. -/
theorem booleanSum_eq_residual {F : Type*} [CommRing F] {n : Nat}
    (f : (Fin n → F) → F) (point : Fin n → F) :
    booleanSum f = residualSum f point 0 := by
  rw [residualSum_zero]
  unfold booleanSum
  rw [← finFunctionFinEquiv.symm.sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  funext i
  exact (cube_bit_cast b i).symm

/-- Honest compressed messages end at the concrete residual's terminal evaluation. -/
theorem honestCompressedRounds_residual {F : Type} [CommRing F] {n degree : Nat}
    (f : (Fin n → F) → F) (hf : CoordinateDegree f (degree+1)) (point : Fin n → F) :
    roundsEnd (fun _ => Sumcheck.compressedOps degree) (honestCompressedRounds f hf point)
      point (residualSum f point 0) = f point := by
  rw [← booleanSum_eq_residual]
  exact honestCompressedRounds_complete f hf point

/-- The actual position summand admits the honest compressed cubic strategy. -/
theorem positionCoordinateDegree {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : CompStark.Keccak.Gkr.Claim F p)
    (t : LayerTranscript F p) : CoordinateDegree (positionSummand q d c t) 3 := by
  simpa only [positionPolynomial_eval] using
    coordinateDegree_eval (positionPolynomial q d c t) (positionPolynomial_degree q d c t)

/-- Honest transmitted position messages use the protocol's zero-padded shifted tables. -/
noncomputable def honestPositionRounds {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : CompStark.Keccak.Gkr.Claim F p)
    (t : LayerTranscript F p) : Fin 11 → Sumcheck.CompressedMessage F 2 :=
  honestCompressedRounds (positionSummand q d c t) (positionCoordinateDegree q d c t) t.positionPoint

/-- The honest position block connects the true pack endpoint to the true shifted evaluations. -/
theorem honestPositionRounds_complete {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : CompStark.Keccak.Gkr.Claim F p)
    (t : LayerTranscript F p) :
    roundsEnd (fun _ => Sumcheck.compressedOps 2) (honestPositionRounds q d c t)
      t.positionPoint (packSummand q d c t.point t.packPoint) =
        positionSummand q d c t t.positionPoint := by
  rw [← position_start_identity q d c t t.positionPoint]
  exact honestCompressedRounds_residual _ _ _

/-- The committed-word opening has the honest quadratic coordinate bound. -/
theorem wordCoordinateDegree {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (x : F) (q : Witness p) (t : Transcript F p) : CoordinateDegree (wordSummand x q t) 2 := by
  simpa only [wordPolynomial_eval] using
    coordinateDegree_eval (wordPolynomial x q t) (wordPolynomial_degree x q t)

/-- Honest word-opening messages include all sixty-four committed slots. -/
noncomputable def honestWordRounds {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (x : F) (q : Witness p) (t : Transcript F p) : Fin 6 → Sumcheck.CompressedMessage F 1 :=
  honestCompressedRounds (wordSummand x q t) (wordCoordinateDegree x q t) t.openings.outputPoint

/-- The honest word-opening block ends at the product of its two multilinear factors. -/
theorem honestWordRounds_complete {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (x : F) (q : Witness p) (t : Transcript F p) :
    roundsEnd (fun _ => Sumcheck.compressedOps 1) (honestWordRounds x q t)
      t.openings.outputPoint (residualSum (wordSummand x q t) t.openings.outputPoint 0) =
        wordSummand x q t t.openings.outputPoint :=
  honestCompressedRounds_residual _ _ _

/-- The actual input-opening summand has the honest quadratic coordinate bound. -/
theorem inputCoordinateDegree {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (t : Transcript F p) : CoordinateDegree (inputSummand q t) 2 := by
  simpa only [inputPolynomial_eval] using
    coordinateDegree_eval (inputPolynomial q t) (inputPolynomial_degree q t)

/-- Honest input messages bind the four low instance bits before the six slot bits. -/
noncomputable def honestInputRounds {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (t : Transcript F p) : Fin 10 → Sumcheck.CompressedMessage F 1 :=
  honestCompressedRounds (inputSummand q t) (inputCoordinateDegree q t) t.openings.inputPoint

/-- The honest input-opening block ends at the exact committed-slice summand. -/
theorem honestInputRounds_complete {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (t : Transcript F p) :
    roundsEnd (fun _ => Sumcheck.compressedOps 1) (honestInputRounds q t)
      t.openings.inputPoint (residualSum (inputSummand q t) t.openings.inputPoint 0) =
        inputSummand q t t.openings.inputPoint :=
  honestCompressedRounds_residual _ _ _

/-- Evaluation identifies bounded-degree honest compressed-round polynomials over a sufficiently large field. -/
theorem firstHonestPolynomial_eq {F : Type} [CommRing F] [IsDomain F] [Fintype F]
    {n degree : Nat} (f : (Fin (n+1) → F) → F) (hf : CoordinateDegree f degree)
    (hcard : degree < Fintype.card F) (P : F⦃≤ degree⦄[X])
    (heval : ∀ r, P.val.eval r = booleanSum (fun rest => f (Fin.cons r rest))) :
    firstHonestPolynomial f hf = P := by
  apply Subtype.ext
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ Function.injective_id
  · intro r
    exact (firstHonestPolynomial_eval f hf r).trans (heval r).symm
  · apply lt_of_le_of_lt _ hcard
    apply max_le
    · exact natDegree_le_of_degree_le (mem_degreeLE.mp (firstHonestPolynomial f hf).property)
    · exact natDegree_le_of_degree_le (mem_degreeLE.mp P.property)

end CompStark.Keccak.GkrProver
