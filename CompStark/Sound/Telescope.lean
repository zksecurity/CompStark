/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Steps

/-! # The terminal is the sum of the fractions

If a trace and a permutation trace satisfy an instance's LogUp constraints on every row (`Holds`)
and no tuple of a lookup has a zero denominator on any row, the terminal is the sum, over the rows
and the lookups' tuples, of each tuple's multiplicity over its denominator (`terminal_eq_sum`):

* lookup `c`'s fraction pin `U f - V` vanishes with `U = ∏ d ≠ 0`, so its fraction column holds
  `f = V / U = ∑ m / d` (`foldValues_mul_sum`);
* the first-row selector `n` at row `0` makes the accumulator vanish there;
* the transition selector `ωʳ - ω⁻¹`, nonzero on every row but the last, makes the accumulator
  add the row's fractions from row to row;
* the last-row selector `n ω` at row `n - 1` makes the terminal the accumulator plus the last
  row's fractions.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop CompStark.Lookup Polynomial

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### Cleared denominators -/

section Fractions
variable {R : Type*} [Field R]

theorem snd_foldl_fracStep (ts : List (R × R)) (v u : R) :
    (ts.foldl fracStep (v, u)).2 = u * (ts.map (·.1)).prod := by
  induction ts generalizing v u with
  | nil => simp only [List.foldl_nil, List.map_nil, List.prod_nil, mul_one]
  | cons y ts ih =>
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    exact ih _ _

/-- The cleared denominator is the product of the denominators. -/
theorem snd_foldValues (ts : List (R × R)) : (foldValues ts).2 = (ts.map (·.1)).prod := by
  cases ts with
  | nil => simp only [foldValues, List.map_nil, List.prod_nil]
  | cons y ts =>
    obtain ⟨d, m⟩ := y
    rw [foldValues, snd_foldl_fracStep, List.map_cons, List.prod_cons]

/-- Without a zero denominator, the fraction column pinned by `U f - V = 0` is `∑ m / d`. -/
theorem eq_sum_of_pin (ts : List (R × R)) (hts : ∀ x ∈ ts, x.1 ≠ 0) (f : R)
    (h : (foldValues ts).2 * f - (foldValues ts).1 = 0) :
    f = (ts.map fun x ↦ x.2 / x.1).sum := by
  have hU : (foldValues ts).2 ≠ 0 := by
    rw [snd_foldValues]
    exact List.prod_ne_zero fun h0 ↦ by
      obtain ⟨x, hx, hx0⟩ := List.mem_map.mp h0
      exact hts x hx hx0
  have hs := foldValues_mul_sum ts fun x hx _ ↦ hts x hx
  refine mul_left_cancel₀ hU ?_
  rw [sub_eq_zero.mp h, ← hs]
  congr 2
  exact List.map_congr_left fun x _ ↦ (div_eq_mul_inv _ _).symm

end Fractions

/-! ### The rows of the LogUp constraints -/

variable {lookups : List (Lookup F)}

/-- Row `r` of the trace domain with the trace's values mapped to `𝕂`. -/
noncomputable abbrev rowEnv (S : Setup EF lookups) (publicValues : List F) (trace : Array F)
    (r : Nat) : Expr.Env F 𝕂 :=
  (S.air.traceRow S.logN trace publicValues r).map (algebraMap F 𝕂)

/-- The denominator of a tuple `t` of lookup `c` on a row `env`, with the challenges `chs`:
`chs₂꜀ - ∑ⱼ tⱼ chs₂꜀₊₁ᵏ⁻¹⁻ʲ`. -/
noncomputable def tupleDenominator (env : Expr.Env F 𝕂) (chs : List 𝕂) (c : Nat)
    (t : List (Expr F)) : 𝕂 :=
  chs.getD (2 * c) 0 - hornerFirst (chs.getD (2 * c + 1) 0) (t.map (·.eval env))

/-- The fractions of lookup `l`, number `c`, on a row `env`: each tuple's multiplicity over its
denominator. -/
noncomputable def lookupFractions (env : Expr.Env F 𝕂) (chs : List 𝕂) (l : Lookup F) (c : Nat) :
    List 𝕂 :=
  l.tuples.map fun x ↦ x.2.eval env / tupleDenominator env chs c x.1

theorem mem_logUpConstraints_pin (hne : lookups ≠ []) (l : Lookup F) (c : Nat)
    (h : (l, c) ∈ lookups.zipIdx) : fractionPin c l ∈ logUpConstraints lookups := by
  have : lookups.isEmpty = false := by
    cases lookups with
    | nil => exact absurd rfl hne
    | cons => rfl
  rw [logUpConstraints, ite_eq_right (by rw [this]; exact Bool.false_ne_true)]
  exact List.mem_append_left _ (List.mem_map.mpr ⟨(l, c), h, rfl⟩)

theorem mem_logUpConstraints_acc (hne : lookups ≠ []) :
    (ExtExpr.base .isFirstRow * .perm 0 : ExtExpr F) ∈ logUpConstraints lookups ∧
    (ExtExpr.base .isTransition * (.permNext 0 - .perm 0 - rowSum lookups.length) :
      ExtExpr F) ∈ logUpConstraints lookups ∧
    (ExtExpr.base .isLastRow * (.terminal - .perm 0 - rowSum lookups.length) : ExtExpr F) ∈
      logUpConstraints lookups := by
  have : lookups.isEmpty = false := by
    cases lookups with
    | nil => exact absurd rfl hne
    | cons => rfl
  rw [logUpConstraints, ite_eq_right (by rw [this]; exact Bool.false_ne_true)]
  refine ⟨List.mem_append_right _ ?_, List.mem_append_right _ ?_, List.mem_append_right _ ?_⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]

/-- **The terminal is the sum of the fractions.** -/
theorem terminal_eq_sum (S : Setup EF lookups) (hne : lookups ≠ []) (publicValues : List F)
    (chs : List 𝕂) (terminal : 𝕂) (trace : Array F)
    (R : Fin S.permWidth → Fin (Challenge.d EF) → F[X])
    (h : Holds S publicValues chs terminal trace R)
    (hpole : ∀ r < S.n, ∀ x ∈ lookups.zipIdx, ∀ t ∈ x.1.tuples,
      tupleDenominator (rowEnv S publicValues trace r) chs x.2 t.1 ≠ 0) :
    terminal = ((List.range S.n).flatMap fun r ↦ lookups.zipIdx.flatMap fun x ↦
      lookupFractions (rowEnv S publicValues trace r) chs x.1 x.2).sum := by
  set n := S.n
  set L := lookups.length
  set acc : Nat → 𝕂 := fun r ↦ permRow S R r 0
  set fr : Nat → Nat → 𝕂 := fun r c ↦ permRow S R r (c + 1)
  set aux : Nat → ExtExpr.Env 𝕂 := fun r ↦
    ⟨permRow S R r, permRow S R (r + 1), (chs.getD · 0), terminal⟩
  have hl : S.logN ≤ twoAdicity F := (Nat.le_add_right _ _).trans S.valid.twoAdic
  have hnpos : 0 < n := Nat.two_pow_pos S.logN
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hω := BaseField.isPrimitiveRoot_twoAdicGen (F := F) S.logN hl
  have hn0 : ((n : Nat) : F) ≠ 0 := by
    simp only [n, Setup.n, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_ne_zero _ BaseField.two_ne_zero
  have hconst (r : Nat) : (rowEnv S publicValues trace r).const 0 = 0 ∧
      (rowEnv S publicValues trace r).const 1 = 1 := ⟨map_zero _, map_one _⟩
  -- The fraction columns.
  have hfr : ∀ r < n, ∀ x ∈ lookups.zipIdx,
      fr r x.2 = (lookupFractions (rowEnv S publicValues trace r) chs x.1 x.2).sum := by
    intro r hr x hx
    have h0 := h.lookups _ (mem_logUpConstraints_pin hne x.1 x.2 hx) r hr
    rw [eval_fractionPin _ _ _ _ (hconst r).1 (hconst r).2] at h0
    refine (eq_sum_of_pin _ (fun y hy ↦ ?_) _ h0).trans ?_
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
      exact hpole r hr x hx t ht
    · rw [lookupFractions, List.map_map]
      rfl
  -- The accumulator.
  obtain ⟨hfirst, htrans, hlast⟩ := mem_logUpConstraints_acc (lookups := lookups) hne
  have hrowSum (r : Nat) : (rowSum L).eval (rowEnv S publicValues trace r) (aux r) =
      ((List.range L).map fun c ↦ fr r c).sum :=
    eval_rowSum _ _ L (hconst r).1
  have hacc0 : acc 0 = 0 := by
    have h0 := h.lookups _ hfirst 0 (Nat.two_pow_pos _)
    have e : (ExtExpr.base .isFirstRow * .perm 0 : ExtExpr F).eval (rowEnv S publicValues trace 0)
        (aux 0) = algebraMap F 𝕂 (S.air.traceRow S.logN trace publicValues 0).isFirstRow *
          acc 0 := rfl
    have e' : (S.air.traceRow S.logN trace publicValues 0).isFirstRow =
        ((2 ^ S.logN : Nat) : F) := by simp only [Air.traceRow, ↓reduceIte]
    rw [e, e'] at h0
    exact (mul_eq_zero.mp h0).resolve_left
      ((map_ne_zero_iff _ (algebraMap F 𝕂).injective).mpr hn0)
  have hstep : ∀ r, r + 1 < n → acc (r + 1) = acc r + ((List.range L).map fun c ↦ fr r c).sum := by
    intro r hr
    have h0 := h.lookups _ htrans r (by omega)
    have e : (ExtExpr.base .isTransition * (.permNext 0 - .perm 0 - rowSum L) : ExtExpr F).eval
        (rowEnv S publicValues trace r) (aux r) =
        algebraMap F 𝕂 (twoAdicGen S.logN ^ r - (twoAdicGen S.logN)⁻¹) *
          (acc (r + 1) - acc r - (rowSum L).eval (rowEnv S publicValues trace r) (aux r)) := rfl
    rw [e, hrowSum] at h0
    have hne0 : twoAdicGen (F := F) S.logN ^ r - (twoAdicGen S.logN)⁻¹ ≠ 0 := by
      intro he
      have h1 : twoAdicGen (F := F) S.logN ^ (r + 1) = 1 := by
        rw [pow_succ, sub_eq_zero.mp he, inv_mul_cancel₀ (hω.ne_zero (Nat.two_pow_pos _).ne')]
      have := hω.pow_eq_one_iff_dvd (r + 1) |>.mp h1
      have hr' : r + 1 < 2 ^ S.logN := hr
      exact absurd (Nat.le_of_dvd (Nat.succ_pos _) this) (by omega)
    have := (mul_eq_zero.mp h0).resolve_left
      ((map_ne_zero_iff _ (algebraMap F 𝕂).injective).mpr hne0)
    linear_combination this
  have hend : terminal = acc m + ((List.range L).map fun c ↦ fr m c).sum := by
    have h0 := h.lookups _ hlast m (by omega)
    have e : (ExtExpr.base .isLastRow * (.terminal - .perm 0 - rowSum L) : ExtExpr F).eval
        (rowEnv S publicValues trace m) (aux m) =
        algebraMap F 𝕂 (S.air.traceRow S.logN trace publicValues m).isLastRow *
          (terminal - acc m - (rowSum L).eval (rowEnv S publicValues trace m) (aux m)) := rfl
    have e' : (S.air.traceRow S.logN trace publicValues m).isLastRow =
        ((2 ^ S.logN : Nat) : F) * twoAdicGen S.logN :=
      ite_eq_left (by change m + 1 = n; omega)
    rw [e, e', hrowSum] at h0
    have hne0 : ((2 ^ S.logN : Nat) : F) * twoAdicGen S.logN ≠ 0 :=
      mul_ne_zero hn0 (hω.ne_zero (Nat.two_pow_pos _).ne')
    have := (mul_eq_zero.mp h0).resolve_left
      ((map_ne_zero_iff _ (algebraMap F 𝕂).injective).mpr hne0)
    linear_combination this
  -- The accumulator before row `r` sums the earlier rows' fractions.
  have hsum : ∀ r, r < n → acc r =
      ((List.range r).map fun r' ↦ ((List.range L).map fun c ↦ fr r' c).sum).sum := by
    intro r
    induction r with
    | zero => intro _; rw [hacc0]; rfl
    | succ r ih =>
      intro hr
      rw [hstep r hr, ih (by omega), List.range_succ, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton]
  -- The row sums are the fractions.
  have hrow : ∀ r < n, ((List.range L).map fun c ↦ fr r c).sum =
      (lookups.zipIdx.flatMap fun x ↦
        lookupFractions (rowEnv S publicValues trace r) chs x.1 x.2).sum := by
    intro r hr
    rw [Lookup.sum_flatMap]
    have hz : lookups.zipIdx.map (fun x ↦ fr r x.2) = (List.range L).map fun c ↦ fr r c := by
      rw [show (fun x : Lookup F × ℕ ↦ fr r x.2) = (fun c ↦ fr r c) ∘ Prod.snd from rfl,
        ← List.map_map, List.zipIdx_map_snd, List.range_eq_range']
    rw [← hz]
    congr 1
    exact List.map_congr_left fun x hx ↦ hfr r hr x hx
  have htot : terminal = ((List.range n).map fun r ↦ ((List.range L).map fun c ↦ fr r c).sum).sum :=
    by rw [hend, hsum m (by omega), hm, List.range_succ, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton]
  rw [htot, Lookup.sum_flatMap]
  congr 1
  exact List.map_congr_left fun r hr ↦ hrow r (List.mem_range.mp hr)

end CompStark.Sound
