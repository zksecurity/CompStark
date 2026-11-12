/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.Honest

/-! Honest equality-factored quadratic tails for the pack-and-segment sumcheck. -/

set_option maxRecDepth 2048

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr Polynomial
open scoped BigOperators

/-- Fixing one coordinate and scaling the summand preserves its coordinate degree cap. -/
theorem coordinateDegree_scale_tail {F : Type} [CommRing F] {n degree : Nat}
    (f : (Fin (n+1) → F) → F) (hf : CoordinateDegree f degree) (a r : F) :
    CoordinateDegree (fun point => a*f (Fin.cons r point)) degree := by
  intro i point
  obtain ⟨P, hP, heval⟩ := hf.tail r i point
  refine ⟨C a*P, (degree_mul_le _ _).trans ?_, ?_⟩
  · exact (add_le_add degree_C_le hP).trans (by simp only [zero_add]; exact le_rfl)
  · intro s
    rw [eval_mul, eval_C, heval]

/-- Equality kernels split into their first coordinate and their suffix kernel. -/
theorem eqEval_cons {F : Type} [CommRing F] [CharP F 2] {n : Nat}
    (a b : F) (r s : Fin n → F) :
    eqEval (Fin.cons a r) (Fin.cons b s) = (1+a+b)*eqEval r s := by
  simp only [eqEval, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  congr 1
  rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add]
  have h := CharTwo.add_self_eq_zero (a*b)
  linear_combination h

/-- A weighted Boolean projection of a quadratic summand is a quadratic polynomial. -/
theorem weighted_projection_exists {F : Type} [CommRing F] {n : Nat}
    (f : (Fin (n+1) → F) → F) (hf : CoordinateDegree f 2)
    (weight : (Fin n → F) → F) :
    ∃ P : F[X], P.degree ≤ 2 ∧ ∀ r,
      P.eval r = booleanSum (fun point => weight point*f (Fin.cons r point)) := by
  classical
  choose P hdeg heval using fun b : Fin n → Fin 2 => hf 0 (Fin.cons 0 (fun i => (b i : Nat)))
  refine ⟨∑ b, C (weight (fun i => (b i : Nat)))*P b,
    (degree_sum_le _ _).trans (Finset.sup_le fun b _ => ?_), ?_⟩
  · exact (degree_mul_le _ _).trans
      ((add_le_add degree_C_le (hdeg b)).trans (by simp only [zero_add]; exact le_rfl))
  · intro r
    simp only [eval_finsetSum, eval_mul, eval_C, heval, Fin.update_cons_zero, booleanSum]

/-- The honest cofactor polynomial fixes its equality suffix before the fresh coordinate. -/
noncomputable def honestCofactorPolynomial {F : Type} [CommRing F] {n : Nat}
    (f : (Fin (n+1) → F) → F) (hf : CoordinateDegree f 2) (point : Fin n → F) : F⦃≤ 2⦄[X] :=
  ⟨Classical.choose (weighted_projection_exists f hf (eqEval point)),
    mem_degreeLE.mpr (Classical.choose_spec (weighted_projection_exists f hf (eqEval point))).1⟩

/-- Honest cofactor evaluation is the remaining equality-weighted Boolean sum. -/
theorem honestCofactorPolynomial_eval {F : Type} [CommRing F] {n : Nat}
    (f : (Fin (n+1) → F) → F) (hf : CoordinateDegree f 2) (point : Fin n → F) (r : F) :
    (honestCofactorPolynomial f hf point).val.eval r =
      booleanSum (fun rest => eqEval point rest*f (Fin.cons r rest)) :=
  (Classical.choose_spec (weighted_projection_exists f hf (eqEval point))).2 r

/-- A quadratic is exactly its three coefficient polynomial. -/
theorem quadratic_polynomial_eval {F : Type} [CommRing F] (P : F⦃≤ 2⦄[X]) (r : F) :
    P.val.eval r = P.val.coeff 0+P.val.coeff 1*r+P.val.coeff 2*r^2 := by
  have hd : P.val.natDegree < 3 := Nat.lt_succ_of_le
    (natDegree_le_of_degree_le (mem_degreeLE.mp P.property))
  rw [eval_eq_sum_range' hd, ← Fin.sum_univ_eq_sum_range]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num
  ring

/-- The entering weighted sum determines the omitted cofactor constant coefficient. -/
theorem honestCofactorPolynomial_sum {F : Type} [CommRing F] [CharP F 2] {n : Nat}
    (f : (Fin (n+1) → F) → F) (hf : CoordinateDegree f 2) (point : Fin (n+1) → F) :
    booleanSum (fun r => eqEval point r*f r) =
      (honestCofactorPolynomial f hf (fun i => point i.succ)).val.coeff 0 +
        point 0*((honestCofactorPolynomial f hf (fun i => point i.succ)).val.coeff 1+
          (honestCofactorPolynomial f hf (fun i => point i.succ)).val.coeff 2) := by
  have hp : point = Fin.cons (point 0) (fun i => point i.succ) := (Fin.cons_self_tail point).symm
  rw [booleanSum_succ]
  conv_lhs => rw [hp]
  simp only [eqEval_cons, add_zero, mul_assoc, ← Finset.mul_sum, booleanSum]
  change (1+point 0)*(booleanSum fun r => eqEval (fun i => point i.succ) r*f (Fin.cons 0 r)) +
    (1+point 0+1)*(booleanSum fun r => eqEval (fun i => point i.succ) r*f (Fin.cons 1 r)) = _
  rw [← honestCofactorPolynomial_eval f hf _ 0, ← honestCofactorPolynomial_eval f hf _ 1,
    quadratic_polynomial_eval, quadratic_polynomial_eval]
  simp only [zero_pow (by decide : 2 ≠ 0), one_pow, mul_zero, mul_one, add_zero]
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hthree : (3 : F) = 1 := by
    calc
      _ = (2 : F)+1 := by norm_num
      _ = 1 := by rw [htwo, zero_add]
  ring_nf
  simp only [htwo, hthree, mul_zero, mul_one, add_zero, zero_add]

/-- Honest pack messages send only the linear and quadratic cofactor coefficients. -/
noncomputable def honestCofactorRounds {F : Type} [CommRing F] [CharP F 2] :
    {n : Nat} → (f : (Fin n → F) → F) → CoordinateDegree f 2 →
      (Fin n → F) → (Fin n → F) → Fin n → CofactorMessage F
  | 0, _, _, _, _ => Fin.elim0
  | _+1, f, hf, point, sampled =>
    let P := honestCofactorPolynomial f hf (fun i => point i.succ)
    Fin.cons (P.val.coeff 1, fun _ => P.val.coeff 2)
      (honestCofactorRounds (fun rest => (1+point 0+sampled 0)*f (Fin.cons (sampled 0) rest))
        (coordinateDegree_scale_tail f hf _ _) (fun i => point i.succ) (fun i => sampled i.succ))

/-- Every honest cofactor tail passes the protocol's deterministic acceptance checks. -/
theorem cofactorRounds_valid {F : Type} [CommRing F] {n : Nat}
    (messages : Fin n → CofactorMessage F) (point sampled : Fin n → F) (value : F) :
    roundsValid (packOps point) messages sampled value := by
  induction n generalizing value with
  | zero => trivial
  | succ n ih => exact ⟨rfl, ih _ _ _ _⟩

/-- Honest cofactor tails preserve the entire equality-weighted sum through every challenge. -/
theorem honestCofactorRounds_complete {F : Type} [CommRing F] [CharP F 2] {n : Nat}
    (f : (Fin n → F) → F) (hf : CoordinateDegree f 2) (point sampled : Fin n → F) :
    roundsEnd (packOps point) (honestCofactorRounds f hf point sampled) sampled
      (booleanSum (fun r => eqEval point r*f r)) = eqEval point sampled*f sampled := by
  induction n with
  | zero =>
    simp only [roundsEnd, booleanSum, Finset.univ_unique, Finset.sum_singleton]
    congr 1
    congr 1; funext i; exact i.elim0
  | succ n ih =>
    simp only [honestCofactorRounds, roundsEnd, packOps, Fin.cons_zero, Fin.cons_succ]
    rw [honestCofactorPolynomial_sum f hf point, cofactor_decode, ← quadratic_polynomial_eval,
      honestCofactorPolynomial_eval]
    have hs : (1+point 0+sampled 0)*
        booleanSum (fun r => eqEval (fun i => point i.succ) r*f (Fin.cons (sampled 0) r)) =
        booleanSum (fun r => eqEval (fun i => point i.succ) r*
          ((1+point 0+sampled 0)*f (Fin.cons (sampled 0) r))) := by
      simp only [booleanSum, Finset.mul_sum]; congr 1; funext r; ring
    have hi := ih (fun rest => (1+point 0+sampled 0)*f (Fin.cons (sampled 0) rest))
      (coordinateDegree_scale_tail f hf _ _) (fun i => point i.succ) (fun i => sampled i.succ)
    rw [hs]
    refine hi.trans ?_
    have hsample : Fin.cons (sampled 0) (fun i => sampled i.succ) = sampled := Fin.cons_self_tail sampled
    have he : eqEval point sampled =
        (1+point 0+sampled 0)*eqEval (fun i => point i.succ) (fun i => sampled i.succ) := by
      calc
        _ = eqEval (Fin.cons (point 0) (fun i => point i.succ))
            (Fin.cons (sampled 0) (fun i => sampled i.succ)) :=
          congrArg₂ eqEval (Fin.cons_self_tail point).symm (Fin.cons_self_tail sampled).symm
        _ = _ := eqEval_cons _ _ _ _
    rw [hsample, he]
    ring

/-- The pack summand with its equality factor removed has coordinate degree two. -/
noncomputable def packCofactorPolynomial {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim F p) (s : F) : MvPolynomial (Fin (p+1)) F :=
  ∑ j : Fin 1600, MvPolynomial.C (c.weights j) *
    chiPolynomial (∑ i, muAt s i) (fun k => MvPolynomial.MLE' (packTable q d s (along j k.val)))

/-- The cofactor polynomial retains the full pack summand under its exact equality kernel. -/
theorem packCofactorPolynomial_eval {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim F p) (s : F) (r : Fin (p+1) → F) :
    eqEval c.point r * MvPolynomial.eval r (packCofactorPolynomial q d c s) = packSummand q d c s r := by
  simpa only [packPolynomial, packCofactorPolynomial, map_mul, equalityPolynomial_eval] using
    packPolynomial_eval q d c s r

/-- The equality-free pack cofactor is a sum of weighted quadratic chi expressions. -/
theorem packCofactorPolynomial_degree {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim F p) (s : F) (i : Fin (p+1)) :
    (packCofactorPolynomial q d c s).degreeOf i ≤ 2 := by
  apply coordinate_sum_degree
  intro j
  simpa only [zero_add] using coordinate_mul_degree _ _ i
    (show (MvPolynomial.C (c.weights j) : MvPolynomial (Fin (p+1)) F).degreeOf i ≤ 0 by
      simp only [MvPolynomial.degreeOf_C, le_refl])
    (chiPolynomial_degree _ _ i (fun _ => tablePolynomial_degree _ i))

/-- Honest transmitted pack tails for the actual RMFE product at its sampled evaluation point. -/
noncomputable def honestPackRounds {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim F p) (s : F) (point : Fin (p+1) → F) :
    Fin (p+1) → CofactorMessage F :=
  honestCofactorRounds (fun r => MvPolynomial.eval r (packCofactorPolynomial q d c s))
    (coordinateDegree_eval _ (packCofactorPolynomial_degree q d c s)) c.point point

/-- Honest cofactor messages connect the product evaluation to the true terminal pack summand. -/
theorem honestPackRounds_complete {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim F p) (s : F) (point : Fin (p+1) → F) :
    roundsEnd (packOps c.point) (honestPackRounds q d c s point) point
      (polyEval (honestProductMessage q d c) s) = packSummand q d c s point := by
  rw [honestProductMessage_eval, ← pack_start_identity q d c s point, ← booleanSum_eq_residual]
  have hsum : booleanSum (packSummand q d c s) =
      booleanSum (fun r => eqEval c.point r * MvPolynomial.eval r (packCofactorPolynomial q d c s)) :=
    congrArg booleanSum (funext fun r => (packCofactorPolynomial_eval q d c s r).symm)
  rw [hsum, ← packCofactorPolynomial_eval q d c s point]
  exact honestCofactorRounds_complete
    (fun r => MvPolynomial.eval r (packCofactorPolynomial q d c s))
    (coordinateDegree_eval _ (packCofactorPolynomial_degree q d c s)) c.point point

/-- Evaluation identifies bounded-degree honest cofactor messages over a sufficiently large field. -/
theorem honestCofactorPolynomial_eq {F : Type} [CommRing F] [IsDomain F] [Fintype F]
    {n : Nat} (f : (Fin (n+1) → F) → F) (hf : CoordinateDegree f 2) (point : Fin n → F)
    (hcard : 2 < Fintype.card F) (P : F⦃≤ 2⦄[X])
    (heval : ∀ r, P.val.eval r = booleanSum (fun rest => eqEval point rest*f (Fin.cons r rest))) :
    honestCofactorPolynomial f hf point = P := by
  apply Subtype.ext
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ Function.injective_id
  · intro r
    exact (honestCofactorPolynomial_eval f hf point r).trans (heval r).symm
  · apply lt_of_le_of_lt _ hcard
    apply max_le
    · exact natDegree_le_of_degree_le (mem_degreeLE.mp (honestCofactorPolynomial f hf point).property)
    · exact natDegree_le_of_degree_le (mem_degreeLE.mp P.property)

end CompStark.Keccak.GkrProver
