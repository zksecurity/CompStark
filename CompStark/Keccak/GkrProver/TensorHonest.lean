/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.NativeLayerSemantics

/-! Coordinate degree and Boolean projection of the native early pack tensor. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr BF64 Polynomial
open scoped BigOperators

/-- Boolean suffix digits are the little-endian cube coordinates of their integer row. -/
theorem booleanSuffix_ofFn (row n : Nat) :
    booleanSuffix row n=List.ofFn (fun i : Fin n => if row.testBit i.val then (1 : W) else 0) := by
  induction n generalizing row with
  | zero => rfl
  | succ n ih =>
    rw [booleanSuffix,List.ofFn_succ,ih]
    congr 1
    · rw [Nat.testBit_eq_decide_div_mod_eq]
      simp only [Fin.val_zero,pow_zero,Nat.div_one,decide_eq_true_eq]
      have := Nat.mod_lt row (by decide : 0<2)
      split <;> split <;> first | rfl | omega
    · simp only [Fin.val_succ,Nat.testBit_succ]

/-- The quadratic endpoint rule has a kernel-checked univariate degree certificate. -/
theorem interpolateQuadratic_exists (a b c : W) :
    ∃ P : W[X],P.degree≤2 ∧ ∀ r,P.eval r=interpolateQuadratic a b c r := by
  let values : Fin 3 → W := ![a,a+b+c,c]
  let P : W⦃≤2⦄[X] := ⟨messagePolynomial values,mem_degreeLE.mpr (messagePolynomial_degree values)⟩
  refine ⟨P.val,mem_degreeLE.mp P.property,?_⟩
  intro r
  rw [quadratic_polynomial_eval P r]
  change (messagePolynomial values).coeff 0+(messagePolynomial values).coeff 1*r+
    (messagePolynomial values).coeff 2*r^2= _
  have hc (k : Nat) (hk : k<3) : (messagePolynomial values).coeff k=values ⟨k,hk⟩ :=
    messagePolynomial_coeff values ⟨k,hk⟩
  rw [hc 0 (by decide),hc 1 (by decide),hc 2 (by decide)]
  change a+(a+b+c)*r+c*r^2=interpolateQuadratic a b c r
  unfold interpolateQuadratic
  ring

/-- Interpolation of a complete ternary tensor has degree at most two in every coordinate. -/
theorem tensorInterpolate_coordinateDegree (n : Nat) (values : Nat → W) :
    CoordinateDegree (fun point : Fin n → W => tensorInterpolate (List.ofFn point) values 0) 2 := by
  induction n generalizing values with
  | zero => intro i; exact i.elim0
  | succ n ih =>
    intro i point
    rw [← Fin.cons_self_tail point]
    refine Fin.cases ?_ (fun i => ?_) i
    · obtain ⟨P,hdeg,heval⟩ := interpolateQuadratic_exists
        (tensorInterpolate (List.ofFn (fun j => point j.succ)) (fun row => values (3*row)) 0)
        (tensorInterpolate (List.ofFn (fun j => point j.succ)) (fun row => values (3*row+1)) 0)
        (tensorInterpolate (List.ofFn (fun j => point j.succ)) (fun row => values (3*row+2)) 0)
      refine ⟨P,hdeg,?_⟩
      intro r
      rw [heval]
      simp only [Fin.update_cons_zero,List.ofFn_cons,tensorInterpolate]
      rfl
    · obtain ⟨P,hdeg,heval⟩ := ih
        (fun row => interpolateQuadratic (values (3*row)) (values (3*row+1)) (values (3*row+2)) (point 0))
        i (fun j => point j.succ)
      refine ⟨P,hdeg,?_⟩
      intro r
      rw [heval]
      simp only [← Fin.cons_update,List.ofFn_cons]
      exact tensorInterpolate_contract _ values (point 0) 0

/-- Tensor interpolation after a fixed low prefix preserves the quadratic coordinate cap on the remaining block. -/
theorem tensorInterpolate_prefix_degree (bound : Array W) (n : Nat) (values : Nat → W) (scale : W) :
    CoordinateDegree (fun point : Fin n → W =>
      scale*tensorInterpolate (bound.toList++List.ofFn point) values 0) 2 := by
  intro i point
  have hh := tensorInterpolate_coordinateDegree n (fun row => tensorInterpolate bound.toList values row) i point
  obtain ⟨P,hdeg,heval⟩ := hh
  refine ⟨C scale*P,(degree_mul_le _ _).trans
    ((add_le_add degree_C_le hdeg).trans (by simp only [zero_add]; exact le_rfl)),?_⟩
  intro r
  rw [Polynomial.eval_mul,Polynomial.eval_C,heval]
  dsimp only
  rw [tensorInterpolate_append]

/-- Early native cofactor evaluation is the exact remaining equality-weighted Boolean projection. -/
theorem earlyRound_boolean_projection (values entering bound : Array W) (hv : values.size=81)
    (he : 4≤entering.size) (hb : bound.size≤3) (r : W) :
    (earlyRound values entering bound)[0]!+r*((earlyRound values entering bound)[1]!+
      r*(earlyRound values entering bound)[2]!) =
      booleanSum (fun rest : Fin (3-bound.size) → W =>
        eqEval (fun i : Fin (3-bound.size) => entering[bound.size+1+i.val]!) rest *
          tensorInterpolate (bound.toList++[r]++List.ofFn rest) (fun i => values[i]!) 0) := by
  rw [earlyRound_evaluate_suffix values entering bound hv hb r]
  rw [booleanSum_eq_residual _ (fun _ => 0),residualSum_zero]
  simp only [eqEval_cubePoint]
  have hs : (entering.extract (bound.size+1) 4).size=3-bound.size := by
    rw [Array.size_extract,Nat.min_eq_left he]
    omega
  rw [eqTable_size,hs]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro row _
  have hw := eqTable_get_dimension (entering.extract (bound.size+1) 4) (3-bound.size) hs row
  have hpoint : (fun i : Fin (3-bound.size) => (entering.extract (bound.size+1) 4)[i.val]!) =
      (fun i : Fin (3-bound.size) => entering[bound.size+1+i.val]!) := by
    funext i
    rw [getElem!_pos _ _ (by rw [hs]; exact i.isLt),Array.getElem_extract,
      ← getElem!_pos entering _ (by have := i.isLt; omega)]
  rw [hw,hpoint]
  congr 1
  rw [booleanSuffix_ofFn]
  rfl

/-- The complete scaled quadratic polynomial authored by an early native pack round. -/
noncomputable def earlyPolynomial (values entering bound : Array W) (scale : W) : W⦃≤2⦄[X] :=
  ⟨messagePolynomial (fun k : Fin 3 => scale*(earlyRound values entering bound)[k.val]!),
    mem_degreeLE.mpr (messagePolynomial_degree _)⟩

/-- Each coefficient of the early-round polynomial is the scaled native coefficient. -/
theorem earlyPolynomial_coeff (values entering bound : Array W) (scale : W) (k : Fin 3) :
    (earlyPolynomial values entering bound scale).val.coeff k.val =
      scale*(earlyRound values entering bound)[k.val]! :=
  messagePolynomial_coeff _ k

/-- The early native polynomial evaluates with exactly the production loop's scaled Horner expression. -/
theorem earlyPolynomial_horner (values entering bound : Array W) (scale r : W) :
    (earlyPolynomial values entering bound scale).val.eval r =
      scale*((earlyRound values entering bound)[0]!+r*((earlyRound values entering bound)[1]!+
        r*(earlyRound values entering bound)[2]!)) := by
  rw [quadratic_polynomial_eval]
  have hc (k : Nat) (hk : k<3) :
      (earlyPolynomial values entering bound scale).val.coeff k=scale*(earlyRound values entering bound)[k]! :=
    earlyPolynomial_coeff values entering bound scale ⟨k,hk⟩
  rw [hc 0 (by decide),hc 1 (by decide),hc 2 (by decide)]
  ring

/-- The early polynomial is the exact scaled remaining Boolean projection in any identified suffix dimension. -/
theorem earlyPolynomial_first (values entering bound : Array W) (scale : W) (n : Nat)
    (hv : values.size=81) (he : 4≤entering.size) (hb : bound.size+n=3) (r : W) :
    (earlyPolynomial values entering bound scale).val.eval r =
      booleanSum (fun rest : Fin n → W =>
        eqEval (fun i : Fin n => entering[bound.size+1+i.val]!) rest *
          (scale*tensorInterpolate (bound.toList++[r]++List.ofFn rest) (fun i => values[i]!) 0)) := by
  have hn : n=3-bound.size := by omega
  subst n
  rw [earlyPolynomial_horner,earlyRound_boolean_projection values entering bound hv he (by omega) r]
  simp only [booleanSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rest _
  ring

/-- The native early polynomial is the specification's honest cofactor polynomial on its remaining tensor. -/
theorem earlyPolynomial_honest (values entering bound : Array W) (scale : W) (n : Nat)
    (hv : values.size=81) (he : 4≤entering.size) (hb : bound.size+n=3) :
    honestCofactorPolynomial
      (fun point : Fin (n+1) → W => scale*tensorInterpolate (bound.toList++List.ofFn point) (fun i => values[i]!) 0)
      (tensorInterpolate_prefix_degree bound (n+1) (fun i => values[i]!) scale)
      (fun i : Fin n => entering[bound.size+1+i.val]!) = earlyPolynomial values entering bound scale := by
  let : Fintype Ext3 := Fintype.ofFinite Ext3
  let : Fintype W := Fintype.ofEquiv Ext3 WordExt3.ringEquiv.toEquiv.symm
  have hcard : 2<Fintype.card W := by
    rw [Fintype.card_congr WordExt3.ringEquiv.toEquiv,BF64.card_ext3]
    decide
  apply honestCofactorPolynomial_eq _ _ _ hcard
  intro r
  simpa only [List.ofFn_cons,List.append_assoc,List.singleton_append] using
    earlyPolynomial_first values entering bound scale n hv he hb r

end CompStark.Keccak.GkrProver
