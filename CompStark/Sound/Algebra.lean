/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Steps
public import CompStark.Stark.Constraints

/-! # The algebra step

`algebraStep`: if trace polynomials `T_j` of degree at most `n` fail the AIR on the trace domain
`H = ⟨ω⟩`, then for all but `#constraints - 1` values of `α`, the constraint check at `ζ` on the
true openings passes for at most `identityDegree` points `ζ` off `H`.

Over `𝕂[X]`, let `C_α = ∑_k α^(K-1-k) C_k` be the constraints over the `T_j` with the selector
polynomials (`foldedPoly`, from `constraintPoly`), and `R = ∑_c L_c ∑_e genᵉ q_{c,e}` the
recomposed quotient (`recomposedPoly`, `L_c` the recomposition selector `selPoly`). The identity
`Φ = C_α - Z_H R` (`identityPoly`) has degree at most `identityDegree`.

* For `ζ ∉ H`, `Z_H(ζ)`, `ζ - 1` and `ζ - ω⁻¹` are nonzero (`1` and `ω⁻¹` lie in `H`), so the
  verifier's selectors are the selector polynomials at `ζ` and the check says `Φ(ζ) = 0` (`eval_identityPoly_eq_zero`).
* At a row `ωⁱ`, `Z_H` vanishes and each `C_k` takes the constraint's value on row `i`
  (`eval_constraintPoly_root`), so `Φ(ωⁱ) = P_i(α)` for `P_i = ∑_k c_k(i) Y^(K-1-k)`
  (`eval_identityPoly_root`).
* The trace fails some constraint on some row `i`, so `P_i ≠ 0` has at most `K - 1` roots: these
  are the bad `α`. For any other `α`, `Φ(ωⁱ) ≠ 0`, so `Φ ≠ 0` has at most `deg Φ` roots `ζ`.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop Polynomial


variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### Horner's rule over constants -/

/-- Horner's rule peels off its first term. -/
theorem horner_cons {R : Type*} [CommRing R] (v : R) (l : List R) (a : R) :
    horner (v :: l) a = v * a ^ l.length + horner l a := by
  rw [horner, List.foldl_cons, foldl_horner, zero_mul, zero_add]

/-- `∑_k l_k Y^(K-1-k)` has degree below `K`. -/
theorem degree_horner_C_X {R : Type*} [CommRing R] :
    ∀ l : List R, (horner (l.map C) Polynomial.X).degree < l.length
  | [] => by
    rw [List.map_nil, horner, List.foldl_nil, degree_zero]
    exact WithBot.bot_lt_coe _
  | v :: l => by
    rw [List.map_cons, horner_cons, List.length_map, List.length_cons]
    refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
    · exact (degree_C_mul_X_pow_le _ _).trans_lt (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self _))
    · exact (degree_horner_C_X l).trans (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self _))

/-- `∑_k l_k Y^(K-1-k)` is nonzero if some `l_k` is. -/
theorem horner_C_X_ne_zero {R : Type*} [CommRing R] :
    ∀ l : List R, (∃ v ∈ l, v ≠ 0) → horner (l.map C) Polynomial.X ≠ 0
  | [], ⟨_, hv, _⟩ => absurd hv List.not_mem_nil
  | v :: l, ⟨w, hw, hw0⟩ => fun h ↦ by
    rw [List.map_cons, horner_cons, List.length_map] at h
    have hc : (C v * Polynomial.X ^ l.length + horner (l.map C) Polynomial.X).coeff l.length =
        (0 : R[X]).coeff l.length := by rw [h]
    rw [coeff_add, coeff_C_mul_X_pow, ite_eq_left rfl,
      coeff_eq_zero_of_degree_lt (degree_horner_C_X l), add_zero, coeff_zero] at hc
    rw [hc, C_0, zero_mul, zero_add] at h
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hw0 hc
    · exact horner_C_X_ne_zero l ⟨w, hw, hw0⟩ h

/-- `∑_k l_k Y^(K-1-k)` at `a` is Horner's rule in `a`. -/
theorem eval_horner_C_X {R : Type*} [CommRing R] (l : List R) (a : R) :
    (horner (l.map C) Polynomial.X).eval a = horner l a := by
  rw [← coe_evalRingHom, horner_map, coe_evalRingHom, eval_X, List.map_map]
  congr 1
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun v _ ↦ eval_C (R := R)

/-! ### Folding maxima -/

/-- A running maximum is at least its start. -/
theorem le_foldl_max {ι : Type*} (f : ι → Nat) :
    ∀ (l : List ι) (a : Nat), a ≤ l.foldl (fun m c ↦ max m (f c)) a
  | [], _ => le_rfl
  | c :: l, a => (le_max_left a (f c)).trans (le_foldl_max f l _)

/-- A running maximum bounds every value it folds. -/
theorem le_foldl_max_of_mem {ι : Type*} (f : ι → Nat) :
    ∀ (l : List ι) (a : Nat), ∀ c ∈ l, f c ≤ l.foldl (fun m c ↦ max m (f c)) a
  | [], _, _, h => absurd h List.not_mem_nil
  | d :: l, a, c, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact (le_max_right a (f c)).trans (le_foldl_max f l _)
    · exact le_foldl_max_of_mem f l _ c h

/-! ### The polynomials -/

/-- Column `j` of `trace`, `0` beyond the width. -/
noncomputable def traceCol (S : Setup EF) (trace : Fin S.air.width → F[X]) (j : Nat) : F[X] :=
  if h : j < S.air.width then trace ⟨j, h⟩ else 0

/-- `C_α`: the constraints over the trace polynomials, folded by `α`, over `𝕂`. -/
noncomputable def foldedPoly (S : Setup EF) (publicValues : List F)
    (trace : Fin S.air.width → F[X]) (α : 𝕂) : 𝕂[X] :=
  horner (S.air.constraints.map fun c ↦
    (constraintPoly S.n (twoAdicGen S.logN) (traceCol S trace) publicValues c).map (algebraMap F 𝕂))
    (C α)

/-- The recomposition selector of chunk `c`: `∏_{d ≠ c} Z_{D_d}(X) / Z_{D_d}(s_c)`. -/
noncomputable def selPoly (S : Setup EF) (c : Fin S.chunks) : 𝕂[X] :=
  ∏ d : Fin S.chunks with d ≠ c, C (vanishing (chunkShift S d) S.n (chunkShift S c))⁻¹ *
    ((Polynomial.X * C (chunkShift S d)⁻¹) ^ S.n - 1)

/-- The quotient recomposed from its chunks' coordinate polynomials. -/
noncomputable def recomposedPoly (S : Setup EF)
    (quotient : Fin S.chunks → Fin (Challenge.d EF) → F[X]) : 𝕂[X] :=
  ∑ c, selPoly S c * ∑ e : Fin (Challenge.d EF),
    C (CompPoly.Extension.Ext.gen ^ (e : Nat)) * (quotient c e).map (algebraMap F 𝕂)

/-- The constraint identity `Φ = C_α - Z_H R`. -/
noncomputable def identityPoly (S : Setup EF) (publicValues : List F)
    (trace : Fin S.air.width → F[X]) (quotient : Fin S.chunks → Fin (Challenge.d EF) → F[X]) (α : 𝕂)
    : 𝕂[X] :=
  foldedPoly S publicValues trace α - (Polynomial.X ^ S.n - 1) * recomposedPoly S quotient

/-! ### Degrees -/

/-- The columns have degree at most `n`. -/
theorem natDegree_traceCol (S : Setup EF) (trace : Fin S.air.width → F[X])
    (hdeg : ∀ j, (trace j).natDegree ≤ S.n) (j : Nat) : (traceCol S trace j).natDegree ≤ S.n := by
  rw [traceCol]
  split
  · exact hdeg _
  · rw [natDegree_zero]; exact Nat.zero_le _

/-- On columns of degree at most `n`, a constraint has degree at most `degBound (n + 1)`. -/
theorem natDegree_constraintPoly_succ (S : Setup EF) (publicValues : List F)
    (trace : Fin S.air.width → F[X]) (hdeg : ∀ j, (trace j).natDegree ≤ S.n) (c : Expr F) :
    (constraintPoly S.n (twoAdicGen S.logN) (traceCol S trace) publicValues c).natDegree ≤
      c.degBound (S.n + 1) :=
  Expr.natDegree_eval (S.n + 1) _ (natDegree_traceCol S trace hdeg)
    (fun j ↦ (natDegree_comp_shift _ _).trans (natDegree_traceCol S trace hdeg j))
    (fun _ ↦ natDegree_C _) (fun _ ↦ natDegree_C _) ((natDegree_firstSel _).trans (by omega))
    ((natDegree_lastSel _ _).trans (by omega))
    (natDegree_sub_le_of_le natDegree_X_le (natDegree_C _).le) c

/-- `C_α` has degree at most the largest constraint degree. -/
theorem natDegree_foldedPoly (S : Setup EF) (publicValues : List F)
    (trace : Fin S.air.width → F[X]) (hdeg : ∀ j, (trace j).natDegree ≤ S.n) (α : 𝕂) :
    (foldedPoly S publicValues trace α).natDegree ≤
      S.air.constraints.foldl (fun m c ↦ max m (c.degBound (S.n + 1))) 0 := by
  rw [foldedPoly, horner]
  refine Nat.lt_succ_iff.mp (natDegree_horner _ α _ 0 ?_ fun p hp ↦ ?_)
  · rw [natDegree_zero]; exact Nat.succ_pos _
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
  exact Nat.lt_succ_of_le (natDegree_map_le.trans ((natDegree_constraintPoly_succ S publicValues
    trace hdeg c).trans (le_foldl_max_of_mem (fun c ↦ c.degBound (S.n + 1)) _ 0 c hc)))

/-- The recomposition selector has degree at most `(chunks - 1) n`. -/
theorem natDegree_selPoly (S : Setup EF) (c : Fin S.chunks) :
    (selPoly S c).natDegree ≤ (S.chunks - 1) * S.n := by
  refine (natDegree_prod_le _ _).trans ?_
  have hcard : (Finset.univ.filter fun d : Fin S.chunks ↦ d ≠ c).card = S.chunks - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ,
      Fintype.card_fin]
  rw [← hcard, ← smul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun d _ ↦ ?_
  refine (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans ?_)
  rw [natDegree_one, Nat.max_zero]
  refine natDegree_pow_le.trans ?_
  have : (Polynomial.X * C (chunkShift S d)⁻¹).natDegree ≤ 1 :=
    (natDegree_mul_C_le _ _).trans natDegree_X_le
  exact (Nat.mul_le_mul_left _ this).trans (Nat.mul_one _).le

/-- The recomposed quotient has degree at most `chunks · n`. -/
theorem natDegree_recomposedPoly (S : Setup EF)
    (quotient : Fin S.chunks → Fin (Challenge.d EF) → F[X])
    (hq : ∀ c e, (quotient c e).natDegree ≤ S.n) :
    (recomposedPoly S quotient).natDegree ≤ S.chunks * S.n := by
  refine natDegree_sum_le_of_forall_le _ _ fun c _ ↦ natDegree_mul_le.trans ?_
  have h1 := natDegree_selPoly S c
  have h2 : (∑ e : Fin (Challenge.d EF), C (CompPoly.Extension.Ext.gen ^ (e : Nat)) *
      (quotient c e).map (algebraMap F 𝕂)).natDegree ≤ S.n :=
    natDegree_sum_le_of_forall_le _ _ fun e _ ↦
      (natDegree_C_mul_le _ _).trans (natDegree_map_le.trans (hq c e))
  have h3 : (S.chunks - 1) * S.n + S.n = S.chunks * S.n := by
    have := Nat.two_pow_pos S.air.logQuotientChunks
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ this)]
  omega

/-- `Φ` has degree at most `identityDegree`. -/
theorem natDegree_identityPoly (S : Setup EF) (publicValues : List F)
    (trace : Fin S.air.width → F[X]) (hdeg : ∀ j, (trace j).natDegree ≤ S.n)
    (quotient : Fin S.chunks → Fin (Challenge.d EF) → F[X])
    (hq : ∀ c e, (quotient c e).natDegree ≤ S.n)
    (α : 𝕂) : (identityPoly S publicValues trace quotient α).natDegree ≤ S.identityDegree := by
  refine (natDegree_sub_le _ _).trans (max_le
    ((natDegree_foldedPoly S publicValues trace hdeg α).trans (le_max_left _ _))
    (natDegree_mul_le.trans (le_trans ?_ (le_max_right _ _))))
  have hz : (Polynomial.X ^ S.n - 1 : 𝕂[X]).natDegree ≤ S.n :=
    (natDegree_sub_le _ _).trans (by rw [natDegree_one, Nat.max_zero]; exact natDegree_X_pow_le _)
  have hr := natDegree_recomposedPoly S quotient hq
  have : S.n * (S.chunks + 1) = S.n + S.chunks * S.n := by
    rw [Nat.mul_succ, Nat.mul_comm, Nat.add_comm]
  omega

/-! ### The check at `ζ` -/

/-- The verifier's environment at `ζ` (`ConstraintsHoldAt`). -/
noncomputable def envAt (S : Setup EF) (publicValues : List F) (ζ : 𝕂) (o : Openings S) :
    Expr.Env F 𝕂 :=
  { cur := fun j ↦ if h : j < S.air.width then o.traceAt ⟨j, h⟩ else 0
    next := fun j ↦ if h : j < S.air.width then o.traceNext ⟨j, h⟩ else 0
    pub := fun i ↦ lift (publicValues.getD i 0)
    const := lift
    isFirstRow := vanishing 1 S.n ζ / (ζ - 1)
    isLastRow := vanishing 1 S.n ζ / (ζ - (rootOfUnity S.logN)⁻¹)
    isTransition := ζ - (rootOfUnity S.logN)⁻¹ }

/-- The verifier's recomposition selector of chunk `c` at `ζ` (`ConstraintsHoldAt`). -/
noncomputable def selectorAt (S : Setup EF) (ζ : 𝕂) (c : Fin S.chunks) : 𝕂 :=
  ∏ d : Fin S.chunks with d ≠ c,
    vanishing (chunkShift S d) S.n ζ / vanishing (chunkShift S d) S.n (chunkShift S c)

/-- Chunk `c`'s claimed value (`ConstraintsHoldAt`). -/
noncomputable def chunkAt {S : Setup EF} (o : Openings S) (c : Fin S.chunks) : 𝕂 :=
  ∑ e : Fin (Challenge.d EF), CompPoly.Extension.Ext.gen ^ (e : Nat) * o.quotientAt c e

/-- `ConstraintsHoldAt` in terms of `envAt`, `selectorAt` and `chunkAt`. -/
theorem constraintsHoldAt_iff (S : Setup EF) (publicValues : List F) (α ζ : 𝕂) (o : Openings S) :
    ConstraintsHoldAt S publicValues α ζ o ↔
      S.air.constraints.foldl (fun acc c ↦ acc * α + c.eval (envAt S publicValues ζ o)) 0 /
        vanishing 1 S.n ζ = ∑ c, selectorAt S ζ c * chunkAt o c :=
  Iff.rfl

/-- The trace domain is a two-adic subgroup of the base field. -/
theorem logN_le (S : Setup EF) : S.logN ≤ twoAdicity F := (Nat.le_add_right _ _).trans S.valid.twoAdic

/-- `ω_n` lies in the base field. -/
theorem rootOfUnity_eq (S : Setup EF) : rootOfUnity S.logN = algebraMap F 𝕂 (twoAdicGen S.logN) :=
  rfl

/-- The selector polynomial at `ζ` is the verifier's selector. -/
theorem eval_selPoly (S : Setup EF) (c : Fin S.chunks) (ζ : 𝕂) :
    (selPoly S c).eval ζ = selectorAt S ζ c := by
  rw [selPoly, eval_prod, selectorAt]
  refine Finset.prod_congr rfl fun d _ ↦ ?_
  rw [eval_mul, eval_C, eval_sub, eval_pow, eval_mul, eval_X, eval_C, eval_one]
  simp only [vanishing, div_eq_mul_inv]
  ring

/-- The recomposed quotient at `ζ` is the verifier's recomposition of the true openings. -/
theorem eval_recomposedPoly (S : Setup EF) (trace : Fin S.air.width → F[X])
    (quotient : Fin S.chunks → Fin (Challenge.d EF) → F[X]) (ζ : 𝕂) :
    (recomposedPoly S quotient).eval ζ =
      ∑ c, selectorAt S ζ c * chunkAt (trueOpenings S trace quotient ζ) c := by
  rw [recomposedPoly, eval_finsetSum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [eval_mul, eval_selPoly, eval_finsetSum, chunkAt]
  congr 1
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [eval_mul, eval_C, eval_map_algebraMap]
  rfl

/-- `C_α` at a point is Horner's rule over the constraint polynomials there. -/
theorem eval_foldedPoly (S : Setup EF) (publicValues : List F) (trace : Fin S.air.width → F[X])
    (α y : 𝕂) : (foldedPoly S publicValues trace α).eval y = horner (S.air.constraints.map
      fun c ↦ aeval y (constraintPoly S.n (twoAdicGen S.logN) (traceCol S trace) publicValues c)) α := by
  rw [foldedPoly, ← coe_evalRingHom, horner_map, coe_evalRingHom, eval_C, List.map_map]
  congr 1
  refine List.map_congr_left fun c _ ↦ ?_
  simp only [Function.comp_apply, eval_map_algebraMap]

/-- The verifier's constraint at `ζ` is the constraint polynomial at `ζ`. -/
theorem eval_envAt (S : Setup EF) (publicValues : List F) (trace : Fin S.air.width → F[X])
    (quotient : Fin S.chunks → Fin (Challenge.d EF) → F[X]) (ζ : 𝕂) (h1 : ζ - 1 ≠ 0)
    (hω : ζ - (rootOfUnity S.logN)⁻¹ ≠ 0) (c : Expr F) (hc : c.colsBelow S.air.width = true) :
    c.eval (envAt S publicValues ζ (trueOpenings S trace quotient ζ)) =
      aeval ζ (constraintPoly S.n (twoAdicGen S.logN) (traceCol S trace) publicValues c) := by
  have hl := logN_le S
  have hinv : (rootOfUnity S.logN)⁻¹ = algebraMap F 𝕂 (twoAdicGen S.logN)⁻¹ := by
    rw [rootOfUnity_eq, map_inv₀]
  refine (Expr.eval_hom (fun p : F[X] ↦ aeval ζ p) (fun a b ↦ map_add _ a b)
    (fun a b ↦ map_sub _ a b) (fun a b ↦ map_mul _ a b) S.air.width _ _ (fun j hj ↦ ?_)
    (fun j hj ↦ ?_) (fun _ ↦ aeval_C _ _) (fun _ ↦ aeval_C _ _) ?_ ?_ ?_ c hc).symm
  · simp only [polyEnv, envAt, traceCol, trueOpenings, dite_eq_left hj]
  · simp only [polyEnv, envAt, traceCol, trueOpenings, dite_eq_left hj]
    rw [aeval_comp, map_mul, aeval_C, aeval_X, mul_comm, rootOfUnity_eq]
  · change aeval ζ (firstSel S.n) = vanishing 1 S.n ζ / (ζ - 1)
    rw [eq_div_iff h1, aeval_firstSel, vanishing, div_one]
  · change aeval ζ (lastSel S.n (twoAdicGen S.logN)) = vanishing 1 S.n ζ / (ζ - (rootOfUnity S.logN)⁻¹)
    rw [eq_div_iff hω, hinv, aeval_lastSel _ _ (BaseField.twoAdicGen_ne_zero _ hl) (twoAdicGen_pow_self _ hl), vanishing, div_one]
  · change aeval ζ (Polynomial.X - C (twoAdicGen S.logN)⁻¹) = ζ - (rootOfUnity S.logN)⁻¹
    rw [map_sub, aeval_X, aeval_C, hinv]

/-- **The check at `ζ` off the trace domain** makes `ζ` a root of `Φ`. -/
theorem eval_identityPoly_eq_zero (S : Setup EF) (publicValues : List F)
    (trace : Fin S.air.width → F[X]) (quotient : Fin S.chunks → Fin (Challenge.d EF) → F[X])
    (α ζ : 𝕂)
    (hζ : ζ ^ S.n ≠ 1)
    (h : ConstraintsHoldAt S publicValues α ζ (trueOpenings S trace quotient ζ)) :
    (identityPoly S publicValues trace quotient α).eval ζ = 0 := by
  have hz : ζ ^ S.n - 1 ≠ 0 := sub_ne_zero.mpr hζ
  have h1 : ζ - 1 ≠ 0 := sub_ne_zero.mpr fun e ↦ hζ (by rw [e, one_pow])
  have hω : ζ - (rootOfUnity S.logN)⁻¹ ≠ 0 := sub_ne_zero.mpr fun e ↦ hζ (by
    rw [e, inv_pow, rootOfUnity_eq, ← map_pow, twoAdicGen_pow_self _ (logN_le S), map_one, inv_one])
  rw [constraintsHoldAt_iff, ← List.foldl_map (g := fun acc v ↦ acc * α + v), ← horner,
    vanishing, div_one, ← eval_recomposedPoly, div_eq_iff hz] at h
  rw [List.map_congr_left fun c hc ↦ eval_envAt S publicValues trace quotient ζ h1 hω c
    (S.valid.colsInWidth c hc), ← eval_foldedPoly] at h
  rw [identityPoly, eval_sub, eval_mul, eval_sub, eval_pow, eval_X, eval_one, h, mul_comm,
    sub_self]

/-! ### The identity on the trace domain -/

/-- The trace polynomials take `traceOf`'s values on the trace domain. -/
theorem traceOn_traceOf (S : Setup EF) (trace : Fin S.air.width → F[X]) :
    TraceOn S.logN S.air.width (traceOf S trace) (traceCol S trace) := by
  intro j hj i hi
  have hr : i * S.air.width + j < S.n * S.air.width :=
    calc i * S.air.width + j < i * S.air.width + S.air.width := Nat.add_lt_add_left hj _
      _ = (i + 1) * S.air.width := (Nat.succ_mul _ _).symm
      _ ≤ S.n * S.air.width := Nat.mul_le_mul_right _ hi
  have hd : (i * S.air.width + j) / S.air.width = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hm : (i * S.air.width + j) % S.air.width = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  rw [traceOf, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dite_eq_left hr, Option.getD_some,
    finProdFinEquiv_symm_apply]
  rw [traceCol, dite_eq_left hj]
  simp only [Fin.divNat, Fin.modNat, hd, hm]

/-- On a row `ωⁱ`, `Φ` is Horner's rule over the constraints' values on row `i`. -/
theorem eval_identityPoly_root (S : Setup EF) (publicValues : List F)
    (trace : Fin S.air.width → F[X]) (quotient : Fin S.chunks → Fin (Challenge.d EF) → F[X]) (α : 𝕂)
    (i : Nat)
    (hi : i < S.n) :
    (identityPoly S publicValues trace quotient α).eval (algebraMap F 𝕂 (twoAdicGen S.logN ^ i)) =
      horner (S.air.constraints.map fun c ↦ algebraMap F 𝕂
        (c.eval (S.air.traceRow S.logN (traceOf S trace) publicValues i))) α := by
  have hl := logN_le S
  have hz : (algebraMap F 𝕂 (twoAdicGen S.logN ^ i)) ^ S.n - 1 = 0 := by
    rw [← map_pow, ← pow_mul, Nat.mul_comm, pow_mul, twoAdicGen_pow_self _ hl, one_pow, map_one, sub_self]
  rw [identityPoly, eval_sub, eval_mul, eval_sub, eval_pow, eval_X, eval_one, hz, zero_mul,
    sub_zero, eval_foldedPoly]
  congr 1
  refine List.map_congr_left fun c hc ↦ ?_
  rw [aeval_algebraMap_apply_eq_algebraMap_eval, eval_constraintPoly_root S.air S.logN hl _ _ _
    (traceOn_traceOf S trace) c (S.valid.colsInWidth c hc) i hi]

/-! ### The algebra step -/

/-- The points of `s` on which a nonzero polynomial vanishes number at most its degree. -/
theorem card_filter_le_of_roots {R : Type*} [CommRing R] [IsDomain R] (s : Finset R)
    (p : R → Prop) [DecidablePred p] {Φ : R[X]} (hΦ : Φ ≠ 0) (h : ∀ x, p x → Φ.eval x = 0) :
    (s.filter p).card ≤ Φ.natDegree := by
  classical
  refine (Finset.card_le_card fun x hx ↦ ?_).trans
    ((Multiset.toFinset_card_le _).trans (card_roots' Φ))
  exact Multiset.mem_toFinset.mpr ((mem_roots hΦ).mpr (h x (Finset.mem_filter.mp hx).2))

/-- The trace fails some constraint on some row. -/
theorem exists_failing_row (S : Setup EF) (publicValues : List F) (trace : Fin S.air.width → F[X])
    (hsat : ¬ S.air.Satisfied S.logN (traceOf S trace) publicValues) :
    ∃ c ∈ S.air.constraints, ∃ i < S.n,
      c.eval (S.air.traceRow S.logN (traceOf S trace) publicValues i) ≠ 0 := by
  by_contra hne
  refine hsat ⟨Array.size_ofFn, fun c hc i hi ↦ ?_⟩
  by_contra h
  exact hne ⟨c, hc, i, hi, h⟩

/-- **The algebra step.** -/
theorem algebraStep (S : Setup EF) : AlgebraStep S := by
  classical
  intro publicValues trace hdeg hsat
  obtain ⟨c₀, hc₀, i, hi, hne⟩ := exists_failing_row S publicValues trace hsat
  set vs : List 𝕂 := S.air.constraints.map fun c ↦ algebraMap F 𝕂
    (c.eval (S.air.traceRow S.logN (traceOf S trace) publicValues i)) with hvs
  set P : 𝕂[X] := horner (vs.map C) Polynomial.X
  have hP : P ≠ 0 := horner_C_X_ne_zero vs ⟨_, List.mem_map_of_mem hc₀, fun h ↦ hne
    ((algebraMap F 𝕂).injective (h.trans (map_zero _).symm))⟩
  refine ⟨P.roots.toFinset, ?_, fun α hα quotient hq ↦ ?_⟩
  · have hd := (natDegree_lt_iff_degree_lt hP).mpr (degree_horner_C_X vs)
    rw [hvs, List.length_map] at hd
    exact (Multiset.toFinset_card_le _).trans ((card_roots' P).trans (by omega))
  · have hΦ : identityPoly S publicValues trace quotient α ≠ 0 := fun h0 ↦ by
      have := congrArg (eval (algebraMap F 𝕂 (twoAdicGen S.logN ^ i))) h0
      rw [eval_identityPoly_root S publicValues trace quotient α i hi, eval_zero, ← hvs,
        ← eval_horner_C_X] at this
      exact hα (Multiset.mem_toFinset.mpr ((mem_roots hP).mpr this))
    exact (card_filter_le_of_roots _ _ hΦ fun ζ h ↦ eval_identityPoly_eq_zero S publicValues
      trace quotient α ζ h.1 h.2).trans
      (natDegree_identityPoly S publicValues trace hdeg quotient hq α)

end CompStark.Sound
