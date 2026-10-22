/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Lookup.Poly
public import CompStark.Complete.Quotient
public import CompStark.Batch.Refines

/-! # The honest quotient of the LogUp constraints

The LogUp constraints as polynomials (`CompStark/Lookup/Poly.lean`) over the honest traces'
polynomials vanish on the trace domain, so they are `Z_H` times a polynomial over the spec field
(`eq_zHE_mul`), whose values on the quotient domain the batch prover computes.
-/

@[expose] public section
namespace CompStark.Lookup
open CompStark.Stark CompStark.Fri Polynomial

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]
local notation "K" => F
local notation "E" => Challenge.Spec EF

/-! ### Divisibility over the extension -/

/-- `Z_H = Xⁿ - 1` over the spec field `𝕂`. -/
noncomputable abbrev zHE (n : Nat) : E[X] := X ^ n - C 1

theorem zHE_monic (logN : Nat) : (zHE (EF := EF) (2 ^ logN)).Monic :=
  monic_X_pow_sub_C 1 (Nat.two_pow_pos logN).ne'

/-- A polynomial over `𝕂` vanishing on `⟨ω⟩` is `Z_H` times its quotient. -/
theorem eq_zHE_mul (logN : Nat) (h : logN ≤ twoAdicity F) (p : E[X])
    (hp : ∀ i < 2 ^ logN, p.eval (algebraMap K E (twoAdicGen logN ^ i)) = 0) :
    p = zHE (2 ^ logN) * (p /ₘ zHE (2 ^ logN)) := by
  have hr : p %ₘ zHE (2 ^ logN) = 0 := by
    have hpr := BaseField.isPrimitiveRoot_twoAdicGen (F := F) logN h
    refine eq_zero_of_degree_lt_of_eval_index_eq_zero (Finset.range (2 ^ logN))
      (v := fun i ↦ algebraMap K E (twoAdicGen logN ^ i)) (fun i hi j hj hij ↦ ?_) ?_
      (fun i hi ↦ ?_)
    · exact hpr.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
        ((algebraMap K E).injective hij)
    · rw [Finset.card_range]
      have := degree_modByMonic_lt p (zHE_monic logN)
      rwa [degree_X_pow_sub_C (Nat.two_pow_pos logN)] at this
    · have e := congrArg (eval (algebraMap K E (twoAdicGen logN ^ i)))
        (modByMonic_add_div p (zHE (2 ^ logN)))
      rw [eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_C, ← map_pow, ← pow_mul,
        Nat.mul_comm, pow_mul, hpr.pow_eq_one, one_pow, map_one, sub_self, zero_mul, add_zero,
        hp i (Finset.mem_range.mp hi)] at e
      exact e
  have := modByMonic_add_div p (zHE (2 ^ logN))
  rw [hr, zero_add] at this
  exact this.symm

/-! ### The permutation trace's polynomials -/

/-- Coordinate `e` of the base coordinates of element `k`. -/
theorem getD_flatten (vs : Array EF) (k e : Nat) (hk : k < vs.size) (he : e < Challenge.d EF) :
    (flatten vs).getD (k * Challenge.d EF + e) 0 = coordOf e (vs.getD k 0) := by
  have hl : (flatten vs).toList = vs.toList.flatMap fun x ↦ Ext.coeffs x := by
    rw [flatten, Array.toList_flatMap]
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hl, ← List.getD_eq_getElem?_getD,
    getD_flatMap_uniform (fun x : EF ↦ Ext.coeffs x) (Challenge.d EF)
      (fun x ↦ Challenge.length_coeffs x) 0 0 _ k e (by rw [Array.length_toList]; exact hk) he,
    Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, ← List.getD_eq_getElem?_getD]

/-- The polynomial over `𝕂` of column `c` of a matrix over the challenge field in base
coordinates, `rps` the polynomials of its base columns. -/
noncomputable def auxPoly (rps : List F[X]) (c : Nat) : E[X] :=
  chunkPoly EF ((List.range (Challenge.d EF)).map fun e ↦ rps.getD (c * Challenge.d EF + e) 0)

theorem eval_auxPoly (rps : List F[X]) (c : Nat) (y : E) : (auxPoly rps c).eval y =
    ∑ e ∈ Finset.range (Challenge.d EF),
      Challenge.toSpec (Ext.basis e : EF) * aeval y (rps.getD (c * Challenge.d EF + e) 0) := by
  rw [auxPoly, eval_chunkPoly]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  rw [getD_map_range _ _ _ _ (Finset.mem_range.mp he)]

/-- On `⟨ω⟩`, the column polynomials of a matrix over the challenge field take its columns'
values. -/
theorem eval_auxPoly_root (logN W : Nat) (vs : Array EF) (rps : List F[X])
    (hT : TraceOn logN (W * Challenge.d EF) (flatten vs) (rps.getD · 0))
    (hs : vs.size = 2 ^ logN * W) (c : Nat) (hc : c < W) (i : Nat) (hi : i < 2 ^ logN) :
    (auxPoly rps c).eval (algebraMap K E (twoAdicGen logN ^ i)) =
      Challenge.toSpec (vs.getD (i * W + c) 0) := by
  rw [eval_auxPoly, toSpec_eq_basis]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  have he := Finset.mem_range.mp he
  rw [aeval_algebraMap_apply_eq_algebraMap_eval, hT _ (by nlinarith) i hi,
    show i * (W * Challenge.d EF) + (c * Challenge.d EF + e) =
      (i * W + c) * Challenge.d EF + e by ring,
    getD_flatten vs _ e (by rw [hs]; nlinarith) he]

theorem getD_map_toSpec (chs : List EF) (j : Nat) :
    (chs.map Challenge.toSpec).getD j 0 = Challenge.toSpec (chs.getD j 0) := by
  rcases Nat.lt_or_ge j chs.length with hj | hj
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj), List.getElem_map,
      List.getD_eq_getElem _ _ hj]
  · rw [List.getD_eq_default _ _ (by rw [List.length_map]; exact hj), List.getD_eq_default _ _ hj,
      Challenge.toSpec_zero]

/-- **On the honest permutation trace, every LogUp constraint polynomial is `Z_H` times its
quotient**, for row-local lookups reading the AIR's columns and challenges without poles on the
trace domain. -/
theorem extPoly_eq (A : Air F) (ls : List (Lookup F)) (logN : Nat) (h : logN ≤ twoAdicity F)
    (trace : Array F) (pis : List F) (chs : List EF) (T Tp P : Nat → F[X])
    (hT : TraceOn logN A.width trace T)
    (hTp : TraceOn logN A.preprocessedWidth A.preprocessed Tp) (hP : PeriodicOn A logN P)
    (rps : List F[X]) (hR : TraceOn logN ((ls.length + 1) * Challenge.d EF)
      (flatten (permutationTrace A ls logN trace pis chs).1) (rps.getD · 0))
    (hls : ∀ l ∈ ls, l.Fits A.width A.mainNextWidth A.preprocessedWidth A.preprocessedNextWidth)
    (hpole : ∀ i < 2 ^ logN, NoPoleAt A ls logN trace pis chs i) :
    ∀ g ∈ logUpConstraints ls,
      extPoly (2 ^ logN) (twoAdicGen logN) T Tp P pis (auxPoly rps) (chs.map Challenge.toSpec)
        (Challenge.toSpec (permutationTrace A ls logN trace pis chs).2) g =
      zHE (2 ^ logN) * (extPoly (2 ^ logN) (twoAdicGen logN) T Tp P pis (auxPoly rps)
        (chs.map Challenge.toSpec)
        (Challenge.toSpec (permutationTrace A ls logN trace pis chs).2) g /ₘ zHE (2 ^ logN)) := by
  intro g hg
  have hcols := colsBelow_logUpConstraints ls (fun l hl x hx ↦
    ⟨fun e he ↦ ((hls l hl x hx).1 e he).2, (hls l hl x hx).2.2⟩) g hg
  have hsz := Batch.size_permutationTrace A ls logN trace pis chs
  have hw := BaseField.isPrimitiveRoot_twoAdicGen (F := F) logN h
  refine eq_zHE_mul logN h _ fun i hi ↦ ?_
  rw [eval_extPoly_root A logN h trace pis T Tp P hT hTp hP _ _ _ (ls.length + 1) g hcols i hi]
  have key := ExtExpr.eval_hom id (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) A.width
    A.mainNextWidth A.preprocessedWidth A.preprocessedNextWidth (ls.length + 1)
    ((A.traceRow logN trace pis i).map (algebraMap K E))
    ((A.traceRow logN trace pis i).map (algebraMap K E))
    ⟨fun c ↦ (auxPoly rps c).eval (algebraMap K E (twoAdicGen logN ^ i)),
      fun c ↦ (auxPoly rps c).eval (algebraMap K E (twoAdicGen logN ^ (i + 1))),
      ((chs.map Challenge.toSpec).getD · 0),
      Challenge.toSpec (permutationTrace A ls logN trace pis chs).2⟩
    (honestAux A ls logN trace pis chs i) (fun _ _ ↦ rfl) (fun c hc ↦ ?_) (fun c hc ↦ ?_)
    (fun j ↦ getD_map_toSpec chs j) rfl g hcols
  · rw [show g.eval _ _ = _ from key]
    exact logUpConstraints_honest A ls logN h trace pis chs (fun l hl x hx ↦
      ⟨fun e he ↦ ((hls l hl x hx).1 e he).1, (hls l hl x hx).2.1⟩) i hi (hpole i hi) g hg
  · exact eval_auxPoly_root logN (ls.length + 1) _ rps hR hsz c hc i hi
  · have hm : (i + 1) % 2 ^ logN < 2 ^ logN := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hsucc : twoAdicGen (F := F) logN ^ (i + 1) = twoAdicGen logN ^ ((i + 1) % 2 ^ logN) := by
      conv_lhs => rw [← Nat.mod_add_div (i + 1) (2 ^ logN)]
      rw [pow_add, pow_mul, hw.pow_eq_one, one_pow, mul_one]
    show (auxPoly rps c).eval (algebraMap K E (twoAdicGen logN ^ (i + 1))) = _
    rw [hsucc]
    exact eval_auxPoly_root logN (ls.length + 1) _ rps hR hsz c hc _ hm

/-! ### The folded LogUp quotient -/

/-- An expression over base values lifted to the challenge field is the lift of its value. -/
theorem toSpec_eval_ofBase (X : Expr.Env F F) : ∀ e : Expr F,
    Challenge.toSpec (e.eval (X.map (Ext.ofBase (EF := EF)))) = algebraMap K E (e.eval X)
  | .cur _ | .next _ | .prepCur _ | .prepNext _ | .periodic _ | .pub _ | .const _ | .isFirstRow
  | .isLastRow | .isTransition => Challenge.toSpec_ofBase' _
  | .add a b => by
    simp only [Expr.eval]
    rw [Challenge.toSpec_add, toSpec_eval_ofBase X a, toSpec_eval_ofBase X b, map_add]
  | .sub a b => by
    simp only [Expr.eval]
    rw [Challenge.toSpec_sub, toSpec_eval_ofBase X a, toSpec_eval_ofBase X b, map_sub]
  | .mul a b => by
    simp only [Expr.eval]
    rw [Challenge.toSpec_mul, toSpec_eval_ofBase X a, toSpec_eval_ofBase X b, map_mul]

theorem toSpec_foldl_sum (f : Nat → EF) : ∀ (l : List Nat) (x : EF),
    Challenge.toSpec (l.foldl (fun s e ↦ s + f e) x) =
      Challenge.toSpec x + (l.map fun e ↦ Challenge.toSpec (f e)).sum
  | [], x => by simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | e :: l, x => by
    rw [List.foldl_cons, toSpec_foldl_sum f l, Challenge.toSpec_add, List.map_cons,
      List.sum_cons, add_assoc]

/-- `toSpec` of a Horner fold from an accumulator. -/
theorem toSpec_foldl_horner {α : Type*} (l : List α) (f : α → EF) (a x : EF) :
    Challenge.toSpec (l.foldl (fun acc c ↦ acc * a + f c) x) =
      (l.map fun c ↦ Challenge.toSpec (f c)).foldl (fun acc v ↦ acc * Challenge.toSpec a + v)
        (Challenge.toSpec x) := by
  induction l generalizing x with
  | nil => rfl
  | cons c l ih => rw [List.foldl_cons, ih, Challenge.toSpec_add, Challenge.toSpec_mul]; rfl

/-- The selectors of `lookupQuotientValues` are the quotient's. -/
theorem quotientSelectors_eq (d l : Nat) :
    quotientSelectors (F := F) d l = (qFirst d l, qLast d l, qTrans d l, batchInv (qZh d l)) :=
  rfl

/-- **The prover's LogUp quotient values** on the quotient domain: `1 / Z_H` times the LogUp
constraint polynomials folded by `α`, from the traces and the permutation trace on the quotient
domain. -/
theorem toSpec_lookupQuotientValues (A : Air F) (ext : List (ExtExpr F)) (pis : List F)
    (d l : Nat) (h : d + l ≤ twoAdicity F) (tq pq rq : Mat F) (per : List (Array F))
    (T Tp P : Nat → F[X]) (rps : List F[X]) (pmw : Nat)
    (hq : ∀ j < A.width, ∀ r < 2 ^ (d + l),
      tq.values.getD (r * tq.width + j) 0 = (T j).eval (qpt (d + l) r))
    (hpq : ∀ j < A.preprocessedWidth, ∀ r < 2 ^ (d + l),
      pq.values.getD (r * pq.width + j) 0 = (Tp j).eval (qpt (d + l) r))
    (hper : ∀ j r, periodicRow (per.getD j #[]) r = (P j).eval (qpt (d + l) r))
    (hrq : ∀ j < pmw * Challenge.d EF, ∀ r < 2 ^ (d + l),
      rq.values.getD (r * rq.width + j) 0 = (rps.getD j 0).eval (qpt (d + l) r))
    (chs : List EF) (terminal alpha : EF)
    (hcols : ∀ g ∈ ext,
      g.colsBelow A.width A.mainNextWidth A.preprocessedWidth A.preprocessedNextWidth pmw)
    (r : Nat) (hr : r < 2 ^ (d + l)) :
    Challenge.toSpec ((lookupQuotientValues ext pis d l tq pq rq per chs terminal alpha).getD r 0) =
      algebraMap K E ((qpt (d + l) r ^ 2 ^ d - 1)⁻¹) * horner (ext.map fun g ↦
        (extPoly (2 ^ d) (twoAdicGen d) T Tp P pis (auxPoly rps) (chs.map Challenge.toSpec)
          (Challenge.toSpec terminal) g).eval (algebraMap K E (qpt (d + l) r)))
        (Challenge.toSpec alpha) := by
  set y := algebraMap K E (qpt (d + l) r) with hy
  have hdom := Array.size_ofFn (n := 2 ^ (d + l)) (f := fun _ ↦ (0 : EF))
  unfold lookupQuotientValues
  rw [quotientSelectors_eq]
  dsimp only
  rw [getD_lt _ _ (by rw [Array.size_ofFn]; exact hr), Array.getElem_ofFn]
  dsimp only
  rw [Challenge.toSpec_smul, Algebra.smul_def, getD_invZh d l r h, toSpec_foldl_horner,
    Challenge.toSpec_zero, foldl_horner, zero_mul, zero_add]
  congr 2
  refine List.map_congr_left fun g hg ↦ ?_
  set envP := (polyEnv (2 ^ d) (twoAdicGen d) T Tp P pis).map (Polynomial.map (algebraMap K E))
  set auxP := polyAux (twoAdicGen d) (auxPoly rps) (chs.map Challenge.toSpec)
    (Challenge.toSpec terminal)
  have hP : (extPoly (2 ^ d) (twoAdicGen d) T Tp P pis (auxPoly rps) (chs.map Challenge.toSpec)
      (Challenge.toSpec terminal) g).eval y = g.eval (envP.map (eval y))
        ⟨fun c ↦ (auxP.perm c).eval y, fun c ↦ (auxP.permNext c).eval y,
          fun j ↦ (auxP.challenge j).eval y, auxP.terminal.eval y⟩ :=
    ExtExpr.eval_hom (eval y) (fun _ _ ↦ eval_add) (fun a b ↦ eval_sub a b _)
      (fun _ _ ↦ eval_mul) A.width A.mainNextWidth A.preprocessedWidth A.preprocessedNextWidth
      pmw _ _ _ _ (fun e _ ↦ (Expr.eval_map (evalRingHom y) envP e).symm) (fun _ _ ↦ rfl)
      (fun _ _ ↦ rfl) (fun _ ↦ rfl) rfl g (hcols g hg)
  rw [hP]
  have hpermAt : ∀ c < pmw, ∀ r' < 2 ^ (d + l), Challenge.toSpec (Challenge.ofCoeffs
      ((List.range (Challenge.d EF)).map fun e ↦
        rq.values.getD (r' * rq.width + (c * Challenge.d EF + e)) 0) : EF) =
      (auxPoly rps c).eval (algebraMap K E (qpt (d + l) r')) := by
    intro c hc r' hr'
    rw [toSpec_ofCoeffs_sum, eval_auxPoly]
    refine Finset.sum_congr rfl fun e he ↦ ?_
    have he := Finset.mem_range.mp he
    rw [getD_map_range _ _ _ _ he, Ext.toSpec_basis he,
      aeval_algebraMap_apply_eq_algebraMap_eval, hrq _ (by nlinarith) r' hr']
  refine ExtExpr.eval_hom Challenge.toSpec Challenge.toSpec_add Challenge.toSpec_sub
    Challenge.toSpec_mul A.width A.mainNextWidth A.preprocessedWidth A.preprocessedNextWidth pmw
    _ _ _ _ (fun e he ↦ ?_) (fun c hc ↦ ?_) (fun c hc ↦ ?_) (fun j ↦ ?_) ?_ g (hcols g hg)
  · -- a base expression: its value on the quotient domain's row
    have h1 : Challenge.toSpec (e.eval ((rowEnv tq pq per (2 ^ (d + l)) (2 ^ l) pis (qFirst d l)
        (qLast d l) (qTrans d l) r).map Ext.ofBase)) =
        algebraMap K E (e.eval (rowEnv tq pq per (2 ^ (d + l)) (2 ^ l) pis (qFirst d l)
          (qLast d l) (qTrans d l) r)) := toSpec_eval_ofBase _ e
    refine (Eq.trans ?_ h1).trans ?_
    · rfl
    rw [eval_rowEnv A d l h tq pq per pis T Tp P hq hpq hper e he r hr, ← eval_map_apply]
    have := Expr.eval_map (mapRingHom (algebraMap K E)) (polyEnv (2 ^ d) (twoAdicGen d) T Tp P pis)
      e
    rw [coe_mapRingHom] at this
    have h2 := Expr.eval_map (evalRingHom y) envP e
    rw [coe_evalRingHom] at h2
    rw [h2, this]
    rfl
  · exact hpermAt c hc r hr
  · have hr' : (r + 2 ^ l) % 2 ^ (d + l) < 2 ^ (d + l) := Nat.mod_lt _ (Nat.two_pow_pos _)
    show Challenge.toSpec (Challenge.ofCoeffs ((List.range (Challenge.d EF)).map fun e ↦
      rq.values.getD ((r + 2 ^ l) % 2 ^ (d + l) * rq.width + (c * Challenge.d EF + e)) 0)) =
        ((auxPoly rps c).comp (C (algebraMap K E (twoAdicGen d)) * X)).eval y
    rw [toSpec_ofCoeffs_sum, eval_comp, eval_mul, eval_C, eval_X, eval_auxPoly]
    refine Finset.sum_congr rfl fun e he ↦ ?_
    have he := Finset.mem_range.mp he
    rw [getD_map_range _ _ _ _ he, Ext.toSpec_basis he, ← eval_next_qpt d l h rq _ _
      (hrq _ (by nlinarith)) r, hy, ← map_mul, aeval_algebraMap_apply_eq_algebraMap_eval,
      eval_comp, eval_mul, eval_C, eval_X]
  · show Challenge.toSpec (chs.getD j 0) = (C ((chs.map Challenge.toSpec).getD j 0)).eval y
    rw [eval_C, getD_map_toSpec]
  · show Challenge.toSpec terminal = (C (Challenge.toSpec terminal)).eval y
    rw [eval_C]

/-- The LogUp constraints' quotients folded by `α`. -/
noncomputable def qExt (logN : Nat) (T Tp P : Nat → F[X]) (pis : List F) (R : Nat → E[X])
    (chs : List E) (terminal : E) (ext : List (ExtExpr F)) (a : E) : E[X] :=
  horner (ext.map fun g ↦ extPoly (2 ^ logN) (twoAdicGen logN) T Tp P pis R chs terminal g /ₘ
    zHE (2 ^ logN)) (C a)

/-- The folded LogUp quotient has degree below `k n` when every constraint fits. -/
theorem natDegree_qExt (logN lc : Nat) (T Tp P : Nat → F[X]) (pd : Nat → Nat) (pis : List F)
    (R : Nat → E[X]) (chs : List E) (terminal : E) (ext : List (ExtExpr F)) (a : E)
    (hT : TraceDeg logN T) (hTp : TraceDeg logN Tp) (hP : ∀ j, (P j).natDegree ≤ pd j)
    (hR : ∀ c, (R c).natDegree ≤ 2 ^ logN - 1)
    (hdeg : ∀ g ∈ ext, g.degBound (2 ^ logN) pd < 2 ^ (logN + lc) + 2 ^ logN) :
    (qExt logN T Tp P pis R chs terminal ext a).natDegree < 2 ^ (logN + lc) := by
  refine natDegree_horner _ a _ 0 (by rw [natDegree_zero]; exact Nat.two_pow_pos _)
    (fun p hp ↦ ?_)
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hp
  rw [natDegree_divByMonic _ (zHE_monic logN), natDegree_X_pow_sub_C]
  have h1 := natDegree_extPoly (2 ^ logN) (twoAdicGen logN) T Tp P pd pis R chs terminal g hT hTp
    hP hR
  have h2 := hdeg g hg
  have h3 := Nat.two_pow_pos (logN + lc)
  omega

/-- The folded LogUp quotient at a point is Horner's rule over the quotients there. -/
theorem eval_qExt (logN : Nat) (T Tp P : Nat → F[X]) (pis : List F) (R : Nat → E[X])
    (chs : List E) (terminal : E) (ext : List (ExtExpr F)) (a y : E) :
    (qExt logN T Tp P pis R chs terminal ext a).eval y = horner (ext.map fun g ↦
      (extPoly (2 ^ logN) (twoAdicGen logN) T Tp P pis R chs terminal g /ₘ
        zHE (2 ^ logN)).eval y) a := by
  rw [qExt, ← coe_evalRingHom, horner_map, coe_evalRingHom, eval_C, List.map_map]
  rfl

/-- Horner's rule over polynomials that are `Z_H` times quotients, at a point, is `Z_H` there
times Horner's rule over the quotients. -/
theorem horner_extPoly (logN : Nat) (T Tp P : Nat → F[X]) (pis : List F) (R : Nat → E[X])
    (chs : List E) (terminal : E) (ext : List (ExtExpr F)) (a y : E)
    (heq : ∀ g ∈ ext, extPoly (2 ^ logN) (twoAdicGen logN) T Tp P pis R chs terminal g =
      zHE (2 ^ logN) * (extPoly (2 ^ logN) (twoAdicGen logN) T Tp P pis R chs terminal g /ₘ
        zHE (2 ^ logN))) :
    horner (ext.map fun g ↦
      (extPoly (2 ^ logN) (twoAdicGen logN) T Tp P pis R chs terminal g).eval y) a =
      (qExt logN T Tp P pis R chs terminal ext a).eval y * (y ^ 2 ^ logN - 1) := by
  rw [eval_qExt, ← horner_mul, List.map_map]
  congr 1
  refine List.map_congr_left fun g hg ↦ ?_
  conv_lhs => rw [heq g hg]
  simp only [Function.comp_apply, eval_mul, zHE, eval_sub, eval_pow, eval_X, eval_C]
  ring

/-! ### The verifier's LogUp constraints at `ζ` -/

/-- A recombined opened column of a matrix over the challenge field in base coordinates is its
column polynomial at the point. -/
theorem toSpec_unflattenAt_openedAt (b h : Nat) (m : Stark.Mat F) (rps : List F[X]) (z : EF)
    (hm : CompStark.Mat.IsLde b h m rps) (hz : Ext.OutsideBase z) (W c : Nat) (hc : c < W)
    (hw : rps.length = W * Challenge.d EF) :
    Challenge.toSpec (unflattenAt (Fri.openedAt b m z) c) =
      (auxPoly rps c).eval (Challenge.toSpec z) := by
  have hO := (openedAt_isLde b h m rps z hm hz).2
  rw [unflattenAt, toSpec_foldl_sum, Challenge.toSpec_zero, zero_add, list_sum_range,
    eval_auxPoly]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  have he := Finset.mem_range.mp he
  rw [Challenge.toSpec_mul, hO _ (by rw [hw]; nlinarith)]

/-- At `ζ`, a LogUp constraint reading the AIR's and the permutation trace's columns has, on the
honest openings, its polynomial's value. -/
theorem toSpec_extEval_honest (P : Params) (A : Air F) (logN : Nat) (trace : Array F)
    (pis : List F) (zeta : EF) (hper : A.periodicFits logN = true) (hz : Ext.OutsideBase zeta)
    (ps pps rps : List K[X])
    (hlde : CompStark.Mat.IsLde P.logBlowup (logN + P.logBlowup)
      (ldeRef logN P.logBlowup gen A.width trace) ps)
    (hplde : CompStark.Mat.IsLde P.logBlowup (logN + P.logBlowup)
      (ldeRef logN P.logBlowup gen A.preprocessedWidth A.preprocessed) pps)
    (pm : Mat F) (hrlde : CompStark.Mat.IsLde P.logBlowup (logN + P.logBlowup) pm rps) (W : Nat)
    (hw : rps.length = W * Challenge.d EF) (chunks : List (Mat F)) (chs : List EF)
    (terminal : EF) (g : ExtExpr F)
    (hg : g.colsBelow A.width A.mainNextWidth A.preprocessedWidth A.preprocessedNextWidth W) :
    Challenge.toSpec (g.eval (outOfDomainEnv A pis
      (honestOpened P.logBlowup A logN (ldeRef logN P.logBlowup gen A.width trace) chunks zeta)
      logN zeta) ⟨unflattenAt (Fri.openedAt P.logBlowup pm zeta),
        unflattenAt (Fri.openedAt P.logBlowup pm (zeta * Ext.ofBase (twoAdicGen logN))),
        (chs.getD · 0), terminal⟩) =
      (extPoly (2 ^ logN) (twoAdicGen logN) (ps.getD · 0) (pps.getD · 0) (A.periodicPolys logN)
        pis (auxPoly rps) (chs.map Challenge.toSpec) (Challenge.toSpec terminal) g).eval
        (Challenge.toSpec zeta) := by
  have h24 : logN ≤ twoAdicity F := by have := hlde.2.2.2.2.1; omega
  have hw0 : (twoAdicGen logN : F) ≠ 0 := BaseField.twoAdicGen_ne_zero logN h24
  have hz' := Ext.outsideBase_mul_ofBase hz hw0
  set y := Challenge.toSpec zeta
  set envP := (polyEnv (2 ^ logN) (twoAdicGen logN) (ps.getD · 0) (pps.getD · 0)
    (A.periodicPolys logN) pis).map (Polynomial.map (algebraMap K E))
  set auxP := polyAux (twoAdicGen logN) (auxPoly rps) (chs.map Challenge.toSpec)
    (Challenge.toSpec terminal)
  have hP : (extPoly (2 ^ logN) (twoAdicGen logN) (ps.getD · 0) (pps.getD · 0)
      (A.periodicPolys logN) pis (auxPoly rps) (chs.map Challenge.toSpec)
      (Challenge.toSpec terminal) g).eval y = g.eval (envP.map (eval y))
        ⟨fun c ↦ (auxP.perm c).eval y, fun c ↦ (auxP.permNext c).eval y,
          fun j ↦ (auxP.challenge j).eval y, auxP.terminal.eval y⟩ :=
    ExtExpr.eval_hom (eval y) (fun _ _ ↦ eval_add) (fun a b ↦ eval_sub a b _)
      (fun _ _ ↦ eval_mul) A.width A.mainNextWidth A.preprocessedWidth A.preprocessedNextWidth
      W _ _ _ _ (fun e _ ↦ (Expr.eval_map (evalRingHom y) envP e).symm) (fun _ _ ↦ rfl)
      (fun _ _ ↦ rfl) (fun _ ↦ rfl) rfl g hg
  rw [hP]
  refine ExtExpr.eval_hom Challenge.toSpec Challenge.toSpec_add Challenge.toSpec_sub
    Challenge.toSpec_mul A.width A.mainNextWidth A.preprocessedWidth A.preprocessedNextWidth W
    _ _ _ _ (fun e he ↦ ?_) (fun c hc ↦ ?_) (fun c hc ↦ ?_) (fun j ↦ ?_) ?_ g hg
  · rw [toSpec_eval_honest P A logN trace pis zeta hper hz ps pps hlde hplde chunks e he,
      aeval_def, eval₂_eq_eval_map]
    have h2 := Expr.eval_map (evalRingHom y) envP e
    rw [coe_evalRingHom] at h2
    rw [h2]
    have := Expr.eval_map (mapRingHom (algebraMap K E)) (polyEnv (2 ^ logN) (twoAdicGen logN)
      (ps.getD · 0) (pps.getD · 0) (A.periodicPolys logN) pis) e
    rw [coe_mapRingHom] at this
    rw [this]
    rfl
  · exact toSpec_unflattenAt_openedAt _ _ pm rps zeta hrlde hz W c hc hw
  · show _ = ((auxPoly rps c).comp (C (algebraMap K E (twoAdicGen logN)) * X)).eval y
    rw [toSpec_unflattenAt_openedAt _ _ pm rps _ hrlde hz' W c hc hw, eval_comp, eval_mul,
      eval_C, eval_X, Challenge.toSpec_mul, Challenge.toSpec_ofBase', mul_comm]
  · show Challenge.toSpec (chs.getD j 0) = (C ((chs.map Challenge.toSpec).getD j 0)).eval y
    rw [eval_C, getD_map_toSpec]
  · show Challenge.toSpec terminal = (C (Challenge.toSpec terminal)).eval y
    rw [eval_C]

end CompStark.Lookup

/-! ### The batch verifier's per-instance check -/

namespace CompStark.Batch
open CompStark.Stark CompStark.Fri CompStark.Lookup Polynomial

variable {F : Type} [BaseField F] [Poseidon2Field F] {EF : Type} [Challenge F EF]
local notation "K" => F
local notation "E" => Challenge.Spec EF

/-- The extension of an instance's honest permutation trace in base coordinates, if it has
lookups. -/
def permLde (b : Nat) (I : Instance F) (trace : Array F) (pis : List F) (chs : List EF) :
    Option (Mat F) :=
  if I.lookups.isEmpty then none else some (ldeRef I.logN b gen
    ((I.lookups.length + 1) * Challenge.d EF)
    (flatten (permutationTrace I.air I.lookups I.logN trace pis chs).1))

/-- An instance's honest quotient chunks. -/
def honestChunks (P : Params) (I : Instance F) (trace : Array F) (pis : List F) (chs : List EF)
    (alpha : EF) : List (Mat F) :=
  batchQuotientChunks (specBackend EF) P I (ldeRef I.logN P.logBlowup gen I.air.width trace)
    (prepLde P.logBlowup I.air I.logN) (permLde P.logBlowup I trace pis chs) pis chs
    (permutationTrace I.air I.lookups I.logN trace pis chs).2 alpha

/-- **The prover's quotient values of an instance with lookups** are its constraints' folded
quotient times `α ^ L` plus its LogUp constraints' folded quotient on the quotient domain. -/
theorem toSpec_batchQuotientValues (P : Params) (I : Instance F) (trace : Array F)
    (pis : List F) (chs : List EF) (alpha : EF) (hfit : Fits P I.air I.logN trace)
    (hlc : I.logQuotientChunks ≤ P.logBlowup) (hsat : I.air.ConstraintsVanish I.logN trace pis)
    (hls : ∀ l ∈ I.lookups,
      l.Fits I.air.width I.air.mainNextWidth I.air.preprocessedWidth I.air.preprocessedNextWidth)
    (hpole : ∀ i < 2 ^ I.logN, NoPoleAt I.air I.lookups I.logN trace pis chs i)
    (ps pps rps : List K[X])
    (hlde : CompStark.Mat.IsLde P.logBlowup (I.logN + P.logBlowup)
      (ldeRef I.logN P.logBlowup gen I.air.width trace) ps)
    (hT : TraceOn I.logN I.air.width trace (ps.getD · 0))
    (hplde : CompStark.Mat.IsLde P.logBlowup (I.logN + P.logBlowup)
      (ldeRef I.logN P.logBlowup gen I.air.preprocessedWidth I.air.preprocessed) pps)
    (hTp : TraceOn I.logN I.air.preprocessedWidth I.air.preprocessed (pps.getD · 0))
    (hrlde : CompStark.Mat.IsLde P.logBlowup (I.logN + P.logBlowup) (ldeRef I.logN P.logBlowup gen
      ((I.lookups.length + 1) * Challenge.d EF)
      (flatten (permutationTrace I.air I.lookups I.logN trace pis chs).1)) rps)
    (hR : TraceOn I.logN ((I.lookups.length + 1) * Challenge.d EF)
      (flatten (permutationTrace I.air I.lookups I.logN trace pis chs).1) (rps.getD · 0))
    (r : Nat) (hr : r < 2 ^ (I.logN + I.logQuotientChunks)) :
    Challenge.toSpec ((batchQuotientValues (specBackend EF) I
      (ldeRef I.logN P.logBlowup gen I.air.width trace) (prepLde P.logBlowup I.air I.logN)
      (permLde P.logBlowup I trace pis chs) pis chs
      (permutationTrace I.air I.lookups I.logN trace pis chs).2 alpha).getD r 0) =
      (qFold I.air I.logN (ps.getD · 0) (pps.getD · 0) (I.air.periodicPolys I.logN) pis
          (Challenge.toSpec alpha) *
          C (Challenge.toSpec alpha ^ (I.air.lookupConstraints I.logN).length) +
        qExt I.logN (ps.getD · 0) (pps.getD · 0) (I.air.periodicPolys I.logN) pis (auxPoly rps)
          (chs.map Challenge.toSpec)
          (Challenge.toSpec (permutationTrace I.air I.lookups I.logN trace pis chs).2)
          (I.air.lookupConstraints I.logN) (Challenge.toSpec alpha)).eval
        (algebraMap K E (qpt (I.logN + I.logQuotientChunks) r)) := by
  set A := I.air
  set logN := I.logN
  set lc := I.logQuotientChunks
  set b := P.logBlowup
  set pt := permutationTrace A I.lookups logN trace pis chs
  have h24 := hfit.twoAdic
  have hlc24 : logN + lc ≤ twoAdicity F := by omega
  have hqb := toSpec_quotientOfLde A pis logN b lc trace alpha hlc h24 hsat hfit.cols
    hfit.periodic ps pps hlde hT hplde hTp r hr
  unfold batchQuotientValues permLde
  by_cases he : I.lookups.isEmpty = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true he)]
    dsimp only
    rw [lookupConstraints_of_isEmpty I he]
    simp only [List.length_nil, pow_zero, C_1, mul_one, qExt, List.map_nil, horner,
      List.foldl_nil, add_zero]
    exact hqb
  rw [ite_eq_right_of_eq_false _ _ (eq_false he)]
  dsimp only
  set ext' := A.lookupConstraints logN
  have hsize : (quotientOfLde A pis logN lc (ldeRef logN b gen A.width trace)
      (prepLde b A logN) alpha).size = 2 ^ (logN + lc) := by
    rw [quotientOfLde, quotientValues_eq, Array.size_ofFn]
  have hsize' : (lookupQuotientOfLde A ext' pis logN lc (ldeRef logN b gen A.width trace)
      (prepLde b A logN) (ldeRef logN b gen ((I.lookups.length + 1) * Challenge.d EF)
        (flatten pt.1)) chs pt.2 alpha).size = 2 ^ (logN + lc) := by
    rw [lookupQuotientOfLde, lookupQuotientValues, Array.size_ofFn]
  show Challenge.toSpec ((Array.zipWith _ _ _).getD r 0) = _
  rw [getD_lt _ _ (by rw [Array.size_zipWith, hsize, hsize', Nat.min_self]; exact hr),
    Array.getElem_zipWith]
  rw [Challenge.toSpec_add, Challenge.toSpec_mul, toSpec_extPow, ← getD_lt _ _ (by
    rw [hsize]; exact hr), hqb, ← getD_lt _ _ (by rw [hsize']; exact hr), eval_add, eval_mul,
    eval_C]
  congr 1
  -- the LogUp part
  have hps' : CompStark.Mat.IsLde b ((logN + lc) + (b - lc))
      (ldeRef logN b gen A.width trace) ps := by
    rw [show logN + lc + (b - lc) = logN + b by omega]; exact hlde
  have hrps' : CompStark.Mat.IsLde b ((logN + lc) + (b - lc))
      (ldeRef logN b gen ((I.lookups.length + 1) * Challenge.d EF) (flatten pt.1)) rps := by
    rw [show logN + lc + (b - lc) = logN + b by omega]; exact hrlde
  have hlen : ps.length = A.width := hlde.1.symm
  have hrlen : rps.length = (I.lookups.length + 1) * Challenge.d EF := hrlde.1.symm
  unfold lookupQuotientOfLde
  dsimp only
  rw [toSpec_lookupQuotientValues A ext' pis logN lc hlc24 _ _ _ _ (ps.getD · 0) (pps.getD · 0)
    (A.periodicPolys logN) rps (I.lookups.length + 1)
    (fun j hj r hr ↦ permuteRows_lde _ ps b (logN + lc) (b - lc) hps' r hr j (by omega))
    (prepLde_onQuotient A logN b lc hlc pps hplde)
    (periodicRow_periodicPolys A logN lc hfit.periodic hlc24)
    (fun j hj r hr ↦ permuteRows_lde _ rps b (logN + lc) (b - lc) hrps' r hr j (by omega))
    chs pt.2 alpha (colsBelow_logUpConstraints I.lookups (fun l hl x hx ↦
      ⟨fun e he ↦ ((hls l hl x hx).1 e he).2, (hls l hl x hx).2.2⟩)) r hr]
  rw [horner_extPoly logN _ _ _ pis _ _ _ ext' _ _ (extPoly_eq A I.lookups logN (by omega) trace pis
    chs _ _ _ hT hTp (periodicOn_periodicPolys A logN hfit.periodic (by omega)) rps hR hls hpole),
    ← mul_assoc, mul_comm (algebraMap K E _), mul_assoc, ← map_pow, ← map_one (algebraMap K E),
    ← map_sub, ← map_mul, inv_mul_cancel₀ (sub_ne_zero.mpr (genPoint_pow_ne _ r hlc24 logN
      (by omega))), map_one, mul_one]

/-- **An instance's out-of-domain check passes on its honest openings**, its LogUp constraints
included, for row-local lookups without poles on the trace domain whose constraints fit the
quotient. -/
theorem instanceCheck_honest (P : Params) (I : Instance F) (trace : Array F) (pis : List F)
    (chs : List EF) (alpha zeta : EF) (hfit : Fits P I.air I.logN trace)
    (hlc : I.logQuotientChunks ≤ P.logBlowup) (hsat : I.air.ConstraintsVanish I.logN trace pis)
    (hdeg : I.air.DegreeFitsAt I.logN I.logQuotientChunks)
    (hdegL : ∀ g ∈ I.air.lookupConstraints I.logN,
      g.degBound (2 ^ I.logN) (I.air.periodicDegree (2 ^ I.logN)) <
        2 ^ (I.logN + I.logQuotientChunks) + 2 ^ I.logN)
    (hls : ∀ l ∈ I.lookups,
      l.Fits I.air.width I.air.mainNextWidth I.air.preprocessedWidth I.air.preprocessedNextWidth)
    (hpole : ∀ i < 2 ^ I.logN, NoPoleAt I.air I.lookups I.logN trace pis chs i)
    (hz : Ext.OutsideBase zeta) (permLocal permNext : Array EF) (terminal : EF)
    (hperm : ∀ m ∈ permLde P.logBlowup I trace pis chs,
      permLocal = Fri.openedAt P.logBlowup m zeta ∧
        permNext = Fri.openedAt P.logBlowup m (zeta * Ext.ofBase (twoAdicGen I.logN)) ∧
        terminal = (permutationTrace I.air I.lookups I.logN trace pis chs).2) :
    instanceCheck I (honestOpened P.logBlowup I.air I.logN
      (ldeRef I.logN P.logBlowup gen I.air.width trace) (honestChunks P I trace pis chs alpha) zeta)
      pis permLocal permNext chs terminal zeta alpha = true := by
  set A := I.air
  set logN := I.logN
  set lc := I.logQuotientChunks
  set b := P.logBlowup
  set pt := permutationTrace A I.lookups logN trace pis chs
  set ext' := A.lookupConstraints logN
  have h24 := hfit.twoAdic
  have hlc24 : logN + lc ≤ twoAdicity F := by omega
  obtain ⟨ps, hlde, hT, hTd⟩ := trace_lde P A logN trace hfit
  obtain ⟨pps, hplde, hTp, hTpd⟩ := prep_lde P A logN trace hfit
  obtain ⟨rps, hrlde, hR, hRd⟩ := matrix_lde b logN ((I.lookups.length + 1) * Challenge.d EF)
    (flatten pt.1) h24
  have hRdeg : ∀ c, (auxPoly (EF := EF) rps c).natDegree ≤ 2 ^ logN - 1 := fun c ↦ by
    have := natDegree_chunkPoly (EF := EF) ((List.range (Challenge.d EF)).map fun e ↦
      rps.getD (c * Challenge.d EF + e) 0) (2 ^ logN) (Nat.two_pow_pos _) fun e he ↦ by
        rw [getD_map_range _ _ _ _ he]
        have h1 := hRd (c * Challenge.d EF + e)
        dsimp only at h1
        have := Nat.two_pow_pos logN
        omega
    rw [auxPoly]
    omega
  set Q := qFold A logN (ps.getD · 0) (pps.getD · 0) (A.periodicPolys logN) pis
      (Challenge.toSpec alpha) * C (Challenge.toSpec alpha ^ ext'.length) +
    qExt logN (ps.getD · 0) (pps.getD · 0) (A.periodicPolys logN) pis (auxPoly rps)
      (chs.map Challenge.toSpec) (Challenge.toSpec pt.2) ext' (Challenge.toSpec alpha) with hQdef
  have hQ : Q.natDegree < 2 ^ (logN + lc) := by
    refine (natDegree_add_le _ _).trans_lt (max_lt ?_ ?_)
    · exact (natDegree_mul_C_le _ _).trans_lt (natDegree_qFold A logN lc pis _ _ _ hTd hTpd
        (natDegree_periodicPolys A logN hfit.periodic (by omega)) hdeg _)
    · exact natDegree_qExt logN lc _ _ _ _ pis _ _ _ ext' _ hTd hTpd
        (natDegree_periodicPolys A logN hfit.periodic (by omega)) hRdeg hdegL
  have hqs := toSpec_batchQuotientValues P I trace pis chs alpha hfit hlc hsat hls hpole ps pps rps
    hlde hT hplde hTp hrlde hR
  have hrec := recompose_honest P logN lc h24 hlc _ Q hQ hqs zeta hz
  have hzh : Challenge.toSpec zeta ^ 2 ^ logN - 1 ≠ 0 := by
    have := pow_ne_of_outsideBase hz (specDomain logN (by omega)) one_ne_zero
    rw [map_one, one_pow] at this
    exact sub_ne_zero.mpr this
  set o := honestOpened b A logN (ldeRef logN b gen A.width trace)
    (honestChunks P I trace pis chs alpha) zeta
  have hl : o.quotientChunks.toList = (List.range (2 ^ lc)).map fun c ↦
      Fri.openedAt b (ldeRef logN b
        (gen * (gen * powF (twoAdicGen (logN + lc)) c)⁻¹) (Challenge.d EF)
        (chunkValues (batchQuotientValues (specBackend EF) I (ldeRef logN b gen A.width trace)
          (prepLde b A logN) (permLde b I trace pis chs) pis chs pt.2 alpha) (2 ^ lc) c
          (2 ^ logN))) zeta := by
    simp only [o, honestOpened, honestChunks, batchQuotientChunks, chunksOf, List.toList_toArray,
      List.map_map]
    rfl
  -- the LogUp constraints at `ζ`
  have hext : horner (ext'.map fun g ↦ Challenge.toSpec (g.eval (outOfDomainEnv A pis o logN zeta)
      ⟨unflattenAt permLocal, unflattenAt permNext, (chs.getD · 0), terminal⟩))
      (Challenge.toSpec alpha) =
      (qExt logN (ps.getD · 0) (pps.getD · 0) (A.periodicPolys logN) pis (auxPoly rps)
        (chs.map Challenge.toSpec) (Challenge.toSpec pt.2) ext' (Challenge.toSpec alpha)).eval
        (Challenge.toSpec zeta) * (Challenge.toSpec zeta ^ 2 ^ logN - 1) := by
    by_cases he : I.lookups.isEmpty = true
    · have h0 : ext' = [] := lookupConstraints_of_isEmpty I he
      simp only [h0, List.map_nil, horner, List.foldl_nil, qExt, eval_zero, zero_mul]
    · have hm : ldeRef logN b gen ((I.lookups.length + 1) * Challenge.d EF) (flatten pt.1) ∈
          permLde b I trace pis chs := by
        simp only [permLde, he, Bool.false_eq_true, ↓reduceIte, Option.mem_def]
        rfl
      obtain ⟨h1, h2, h3⟩ := hperm _ hm
      rw [h1, h2, h3, ← horner_extPoly logN _ _ _ pis _ _ _ ext' _ _
        (extPoly_eq A I.lookups logN (by omega) trace pis chs _ _ _ hT hTp
          (periodicOn_periodicPolys A logN hfit.periodic (by omega)) rps hR hls hpole)]
      congr 1
      refine List.map_congr_left fun g hg ↦ ?_
      exact toSpec_extEval_honest P A logN trace pis zeta hfit.periodic hz ps pps rps hlde hplde _
        hrlde (I.lookups.length + 1) hrlde.1.symm _ chs pt.2 g
        (colsBelow_logUpConstraints I.lookups (fun l hl x hx ↦
          ⟨fun e he ↦ ((hls l hl x hx).1 e he).2, (hls l hl x hx).2.2⟩) g hg)
  unfold instanceCheck
  dsimp only
  refine beq_iff_eq.mpr (Challenge.toSpec_injective ?_)
  rw [hl, hrec, Challenge.toSpec_mul, toSpec_foldl_horner, foldl_horner, List.length_map,
    foldedConstraints_honest P A logN trace pis alpha zeta h24 hfit.cols hfit.periodic hsat hz ps
      pps hlde hT hplde hTp _, hext, Challenge.toSpec_inv, Challenge.toSpec_sub, toSpec_extPowTwo,
    Challenge.toSpec_one, hQdef, eval_add, eval_mul, eval_C]
  field_simp
  exact mul_div_cancel_left₀ _ hzh

end CompStark.Batch
