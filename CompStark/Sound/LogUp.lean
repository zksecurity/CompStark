/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FieldSimp
public import CompStark.Complete.LogUp

/-! # LogUp's challenge pair

LogUp checks a sum of fractions `∑ₖ Mₖ / (α - cₖ(β))` at a uniform pair `(α, β)`, one fraction per
key `k` with its net multiplicity `Mₖ`, the denominator a polynomial of degree at most `W` in `β`
per key, distinct keys giving distinct polynomials `cₖ`. If some `Mₖ` is nonzero, the pair is bad
(a denominator vanishes, or the sum does) for at most `(D + (D - 1) W) |K|` of the `|K|²` pairs, `D`
the number of keys (`card_bad_le`):

* a denominator `α - cₖ(β)` vanishes for one `α` per `β`: `D |K|` pairs;
* otherwise the sum vanishes where the cleared numerator `P = ∑ₖ Mₖ ∏_{j ≠ k} (α - cⱼ(β))`, of total
  degree at most `(D - 1) W` in `(α, β)`, does. `P` is nonzero: substituting `α = cₖ(β)` for a key
  of nonzero `Mₖ` leaves `Mₖ ∏_{j ≠ k} (cₖ - cⱼ)`, a product of nonzero polynomials. The
  Schwartz–Zippel lemma bounds its zeros by `(D - 1) W |K|`.
-/

@[expose] public section
namespace CompStark.Sound.LogUp
open Polynomial Finset

variable {K : Type} [Field K]

/-- `α - c(β)` as a polynomial in `α = X 0` and `β = X 1`. -/
noncomputable def denomPoly (c : K[X]) : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 - Polynomial.aeval (MvPolynomial.X 1) c

theorem eval_denomPoly (c : K[X]) (f : Fin 2 → K) :
    MvPolynomial.eval f (denomPoly c) = f 0 - c.eval (f 1) := by
  rw [denomPoly, map_sub, MvPolynomial.eval_X, Polynomial.aeval_def, Polynomial.hom_eval₂,
    MvPolynomial.eval_X]
  have : (MvPolynomial.eval f).comp (algebraMap K (MvPolynomial (Fin 2) K)) = RingHom.id K :=
    RingHom.ext fun a ↦ by
      rw [RingHom.comp_apply, MvPolynomial.algebraMap_eq, MvPolynomial.eval_C, RingHom.id_apply]
  rw [this, Polynomial.eval₂_id]

theorem totalDegree_aeval_X_le (c : K[X]) :
    (Polynomial.aeval (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) c).totalDegree ≤
      c.natDegree := by
  conv_lhs => rw [c.as_sum_range_C_mul_X_pow]
  rw [map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le fun i hi ↦ ?_
  rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, MvPolynomial.algebraMap_eq]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  rw [MvPolynomial.totalDegree_X, mul_one]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)

theorem totalDegree_denomPoly_le (c : K[X]) (W : ℕ) (hW : 1 ≤ W) (hc : c.natDegree ≤ W) :
    (denomPoly c).totalDegree ≤ W := by
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ((totalDegree_aeval_X_le c).trans hc))
  rw [MvPolynomial.totalDegree_X]
  exact hW

variable {ι : Type} [DecidableEq ι]

/-- The cleared numerator `∑ₖ Mₖ ∏_{j ≠ k} (α - cⱼ(β))`. -/
noncomputable def numerator (keys : Finset ι) (c : ι → K[X]) (M : ι → K) :
    MvPolynomial (Fin 2) K :=
  ∑ k ∈ keys, MvPolynomial.C (M k) * ∏ j ∈ keys.erase k, denomPoly (c j)

theorem totalDegree_numerator_le (keys : Finset ι) (c : ι → K[X]) (M : ι → K) (W : ℕ)
    (hW : 1 ≤ W) (hc : ∀ k ∈ keys, (c k).natDegree ≤ W) :
    (numerator keys c M).totalDegree ≤ (keys.card - 1) * W := by
  refine MvPolynomial.totalDegree_finsetSum_le fun k hk ↦ ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine (Finset.sum_le_sum fun j hj ↦
    totalDegree_denomPoly_le (c j) W hW (hc j (Finset.mem_of_mem_erase hj))).trans ?_
  rw [Finset.sum_const, Finset.card_erase_of_mem hk, smul_eq_mul]

/-- Substituting `α = cₖ(β)`: `α - cⱼ(β)` becomes `cₖ - cⱼ`. -/
noncomputable def substitute (ck : K[X]) : MvPolynomial (Fin 2) K →ₐ[K] K[X] :=
  MvPolynomial.aeval ![ck, Polynomial.X]

theorem substitute_denomPoly (ck c : K[X]) : substitute ck (denomPoly c) = ck - c := by
  rw [denomPoly, map_sub, substitute, MvPolynomial.aeval_X, ← Polynomial.aeval_algHom_apply,
    MvPolynomial.aeval_X]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Polynomial.aeval_X_left_apply]

theorem substitute_C (ck : K[X]) (a : K) : substitute ck (MvPolynomial.C a) = Polynomial.C a := by
  rw [substitute, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]

/-- **The cleared numerator is nonzero** if the polynomials are distinct and some multiplicity is
nonzero. -/
theorem numerator_ne_zero (keys : Finset ι) (c : ι → K[X]) (M : ι → K)
    (hinj : Set.InjOn c keys) (k : ι) (hk : k ∈ keys) (hM : M k ≠ 0) :
    numerator keys c M ≠ 0 := by
  intro h
  have h' := congrArg (substitute (c k)) h
  rw [map_zero, numerator, map_sum, Finset.sum_eq_single k] at h'
  · rw [map_mul, substitute_C, map_prod] at h'
    simp only [substitute_denomPoly] at h'
    refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.mpr fun j hj ↦ ?_) h'
    · rw [ne_eq, Polynomial.C_eq_zero]
      exact hM
    · refine sub_ne_zero.mpr fun he ↦ (Finset.ne_of_mem_erase hj) ?_
      exact hinj (Finset.mem_of_mem_erase hj) hk he.symm
  · intro j hj hjk
    rw [map_mul, map_prod, Finset.prod_eq_zero (i := k) (Finset.mem_erase.mpr ⟨Ne.symm hjk, hk⟩)
      (by rw [substitute_denomPoly, sub_self]), mul_zero]
  · intro hk'
    exact absurd hk hk'

/-- Off the poles, the sum of fractions vanishes only where the cleared numerator does. -/
theorem eval_numerator_eq_zero (keys : Finset ι) (c : ι → K[X]) (M : ι → K) (f : Fin 2 → K)
    (hpole : ∀ k ∈ keys, f 0 - (c k).eval (f 1) ≠ 0)
    (hsum : ∑ k ∈ keys, M k / (f 0 - (c k).eval (f 1)) = 0) :
    MvPolynomial.eval f (numerator keys c M) = 0 := by
  have hprod : ∏ j ∈ keys, (f 0 - (c j).eval (f 1)) ≠ 0 := Finset.prod_ne_zero_iff.mpr hpole
  have key : MvPolynomial.eval f (numerator keys c M) =
      (∑ k ∈ keys, M k / (f 0 - (c k).eval (f 1))) * ∏ j ∈ keys, (f 0 - (c j).eval (f 1)) := by
    rw [numerator, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [map_mul, MvPolynomial.eval_C, map_prod, ← Finset.mul_prod_erase keys _ hk]
    simp only [eval_denomPoly]
    field_simp [hpole k hk]
  rw [key, hsum, zero_mul]

section Count
variable [Fintype K] [DecidableEq K]

/-- The zeros of a nonzero polynomial in two variables number at most its total degree times
`|K|` (Schwartz–Zippel). -/
theorem card_zeros_le {P : MvPolynomial (Fin 2) K} (hP : P ≠ 0) :
    (univ.filter fun z : K × K ↦ MvPolynomial.eval ![z.1, z.2] P = 0).card ≤
      P.totalDegree * Fintype.card K := by
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hP (Finset.univ : Finset K)
  set Z := (Fintype.piFinset fun _ : Fin 2 ↦ (univ : Finset K)).filter
    fun f ↦ MvPolynomial.eval f P = 0
  have hcard : (univ.filter fun z : K × K ↦ MvPolynomial.eval ![z.1, z.2] P = 0).card =
      Z.card := by
    refine Finset.card_bij (fun z _ ↦ ![z.1, z.2]) (fun z hz ↦ ?_) (fun a _ b _ h ↦ ?_)
      (fun f hf ↦ ⟨(f 0, f 1), ?_, ?_⟩)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simp only [Z, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_univ, implies_true,
        true_and]
      exact hz
    · have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      exact Prod.ext h0 h1
    · simp only [Z, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_univ, implies_true,
        true_and] at hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have : ![f 0, f 1] = f := funext fun i ↦ by fin_cases i <;> rfl
      rw [this]
      exact hf
    · funext i
      fin_cases i <;> rfl
  rw [hcard]
  have hK : (0 : NNRat) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  rw [Finset.card_univ, div_le_div_iff₀ (by positivity) hK] at hsz
  have : (Z.card : NNRat) * Fintype.card K ≤ P.totalDegree * Fintype.card K * Fintype.card K := by
    calc (Z.card : NNRat) * Fintype.card K ≤ P.totalDegree * Fintype.card K ^ 2 := hsz
      _ = _ := by ring
  have := le_of_mul_le_mul_right this hK
  exact_mod_cast this

/-- **LogUp's Schwartz–Zippel bound.** For keys with distinct denominator polynomials `cₖ` of
degree at most `W ≥ 1` and a nonzero multiplicity, at most `(D + (D - 1) W) |K|` pairs `(α, β)`
make a denominator `α - cₖ(β)` vanish or the sum `∑ₖ Mₖ / (α - cₖ(β))` vanish, `D` the number of
keys. -/
theorem card_bad_le (keys : Finset ι) (c : ι → K[X]) (M : ι → K) (W : ℕ) (hW : 1 ≤ W)
    (hc : ∀ k ∈ keys, (c k).natDegree ≤ W) (hinj : Set.InjOn c keys) (k : ι) (hk : k ∈ keys)
    (hM : M k ≠ 0) :
    (univ.filter fun z : K × K ↦ (∃ k ∈ keys, z.1 - (c k).eval z.2 = 0) ∨
        ∑ k ∈ keys, M k / (z.1 - (c k).eval z.2) = 0).card ≤
      (keys.card + (keys.card - 1) * W) * Fintype.card K := by
  set P := numerator keys c M
  have hsub : (univ.filter fun z : K × K ↦ (∃ k ∈ keys, z.1 - (c k).eval z.2 = 0) ∨
        ∑ k ∈ keys, M k / (z.1 - (c k).eval z.2) = 0) ⊆
      keys.biUnion (fun j ↦ univ.image fun β : K ↦ ((c j).eval β, β)) ∪
        univ.filter fun z : K × K ↦ MvPolynomial.eval ![z.1, z.2] P = 0 := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_filter]
    by_cases hp : ∃ k ∈ keys, z.1 - (c k).eval z.2 = 0
    · obtain ⟨j, hj, h0⟩ := hp
      exact Or.inl ⟨j, hj, z.2, Prod.ext (sub_eq_zero.mp h0).symm rfl⟩
    · right
      push Not at hp
      exact eval_numerator_eq_zero keys c M ![z.1, z.2] hp (hz.resolve_left (by push Not; exact hp))
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  rw [add_mul]
  refine Nat.add_le_add (Finset.card_biUnion_le.trans ?_) ((card_zeros_le
    (numerator_ne_zero keys c M hinj k hk hM)).trans (Nat.mul_le_mul_right _
      (totalDegree_numerator_le keys c M W hW hc)))
  refine (Finset.sum_le_sum fun j _ ↦ Finset.card_image_le).trans ?_
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

end Count

end CompStark.Sound.LogUp

/-! ### Horner's rule as a polynomial -/

namespace CompStark.Sound.LogUp
open Polynomial Finset CompStark.Lookup

section Horner
variable {K : Type*} [CommRing K]

theorem hornerFirst_append_singleton (b : K) (l : List K) (y : K) :
    hornerFirst b (l ++ [y]) = y + hornerFirst b l * b := by
  cases l with
  | nil => simp only [List.nil_append, hornerFirst, List.foldl_nil, zero_mul, add_zero]
  | cons x xs => simp only [List.cons_append, hornerFirst, List.foldl_append, List.foldl_cons,
      List.foldl_nil]

theorem map_hornerFirst {L : Type*} [CommRing L] (f : K →+* L) (b : K) (l : List K) :
    f (hornerFirst b l) = hornerFirst (f b) (l.map f) := by
  induction l using List.reverseRecOn with
  | nil => simp only [hornerFirst, map_zero, List.map_nil]
  | append_singleton l y ih =>
    rw [hornerFirst_append_singleton, List.map_append, List.map_singleton,
      hornerFirst_append_singleton, map_add, map_mul, ih]

/-- `∑ⱼ tⱼ Xᵏ⁻¹⁻ʲ`, Horner's rule over the constants `t` at `X`. -/
noncomputable abbrev hornerPoly (t : List K) : K[X] := hornerFirst X (t.map C)

theorem eval_hornerPoly (t : List K) (β : K) : (hornerPoly t).eval β = hornerFirst β t := by
  rw [hornerPoly, ← coe_evalRingHom, map_hornerFirst, coe_evalRingHom, eval_X, List.map_map]
  congr 1
  conv_rhs => rw [← List.map_id t]
  exact List.map_congr_left fun v _ ↦ eval_C

theorem degree_hornerPoly_lt [Nontrivial K] (t : List K) : (hornerPoly t).degree < t.length := by
  induction t using List.reverseRecOn with
  | nil =>
    simp only [hornerPoly, List.map_nil, hornerFirst, degree_zero, List.length_nil, Nat.cast_zero]
    exact WithBot.bot_lt_coe _
  | append_singleton l y ih =>
    rw [hornerPoly, List.map_append, List.map_singleton, hornerFirst_append_singleton,
      List.length_append, List.length_singleton]
    refine (degree_add_le _ _).trans_lt (max_lt ((degree_C_le).trans_lt ?_) ?_)
    · exact_mod_cast Nat.succ_pos _
    · refine (degree_mul_le _ _).trans_lt ?_
      refine (add_le_add le_rfl degree_X_le).trans_lt ?_
      have : (hornerPoly l).degree + 1 < (l.length : WithBot ℕ) + 1 :=
        WithBot.add_lt_add_right WithBot.one_ne_bot ih
      exact_mod_cast this

theorem hornerPoly_injective [IsDomain K] :
    ∀ (t t' : List K), t.length = t'.length → hornerPoly t = hornerPoly t' → t = t' := by
  intro t
  induction t using List.reverseRecOn with
  | nil => intro t' h _; exact (List.length_eq_zero_iff.mp h.symm).symm
  | append_singleton l y ih =>
    intro t' hlen h
    obtain ⟨l', y', rfl⟩ : ∃ l' y', t' = l' ++ [y'] := by
      rcases List.eq_nil_or_concat t' with h0 | ⟨l', y', rfl⟩
      · rw [h0, List.length_nil, List.length_append, List.length_singleton] at hlen
        omega
      · exact ⟨l', y', List.concat_eq_append⟩
    simp only [hornerPoly, List.map_append, List.map_singleton, hornerFirst_append_singleton]
      at h
    have h0 := congrArg (coeff · 0) h
    simp only [coeff_add, coeff_C_zero, coeff_mul_X_zero, add_zero] at h0
    subst h0
    have hm := add_left_cancel h
    have hl : hornerPoly l = hornerPoly l' := mul_right_cancel₀ X_ne_zero hm
    simp only [List.length_append, List.length_singleton] at hlen
    rw [ih l' (by omega) hl]

end Horner

/-! ### The keys of LogUp's messages -/

section Messages
variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-- The denominator `α + (b + 1) βᵂ - ∑ⱼ tⱼ βᵏ⁻¹⁻ʲ` of the key `(b, t)`, bus `b` and tuple `t`. -/
noncomputable def denominator (W : ℕ) (key : ℕ × List F) (α β : 𝕂) : 𝕂 :=
  α + algebraMap F 𝕂 ((key.1 + 1 : ℕ) : F) * β ^ W - hornerFirst β (key.2.map (algebraMap F 𝕂))

/-- LogUp's sum of fractions over the messages `(key, m)`: `∑ m / denominator`. -/
noncomputable def fractionSum (W : ℕ) (msgs : List ((ℕ × List F) × F)) (α β : 𝕂) : 𝕂 :=
  (msgs.map fun x ↦ algebraMap F 𝕂 x.2 / denominator W x.1 α β).sum

/-- The lookup challenges `(α, β)` are bad for the messages: a denominator vanishes, or the sum
of fractions does. -/
def PairBad (W : ℕ) (msgs : List ((ℕ × List F) × F)) (α β : 𝕂) : Prop :=
  (∃ x ∈ msgs, denominator W x.1 α β = 0) ∨ fractionSum W msgs α β = 0

/-- The key's denominator is `α - c(β)` for the polynomial `c = ∑ⱼ tⱼ Xᵏ⁻¹⁻ʲ - (b + 1) Xᵂ`. -/
noncomputable def keyPoly (W : ℕ) (key : ℕ × List F) : 𝕂[X] :=
  hornerPoly (key.2.map (algebraMap F 𝕂)) - C (algebraMap F 𝕂 ((key.1 + 1 : ℕ) : F)) * X ^ W

theorem denominator_eq (W : ℕ) (key : ℕ × List F) (α β : 𝕂) :
    denominator W key α β = α - (keyPoly W key).eval β := by
  rw [denominator, keyPoly, eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_hornerPoly]
  ring

theorem natDegree_keyPoly_le (W : ℕ) (key : ℕ × List F) (h : key.2.length ≤ W) :
    (keyPoly (EF := EF) W key).natDegree ≤ W := by
  refine (natDegree_sub_le _ _).trans (max_le ?_ ((natDegree_C_mul_le _ _).trans
    (natDegree_X_pow_le _)))
  rcases eq_or_ne (hornerPoly (key.2.map (algebraMap F 𝕂))) 0 with h0 | h0
  · rw [h0, natDegree_zero]; exact Nat.zero_le _
  · have := degree_hornerPoly_lt (key.2.map (algebraMap F 𝕂))
    rw [List.length_map] at this
    exact ((natDegree_lt_iff_degree_lt h0).mpr this).le.trans (by omega)

/-- Keys of one width per bus, at most `W`, and buses giving distinct base elements have distinct
key polynomials. -/
theorem keyPoly_inj (W : ℕ) (k k' : ℕ × List F) (hk : k.2.length ≤ W) (hk' : k'.2.length ≤ W)
    (hbus : k.1 = k'.1 → k.2.length = k'.2.length)
    (hdistinct : ((k.1 + 1 : ℕ) : F) = ((k'.1 + 1 : ℕ) : F) → k.1 = k'.1)
    (h : keyPoly (EF := EF) W k = keyPoly W k') : k = k' := by
  have hcW (key : ℕ × List F) (hkey : key.2.length ≤ W) : (keyPoly (EF := EF) W key).coeff W =
      -algebraMap F 𝕂 ((key.1 + 1 : ℕ) : F) := by
    rw [keyPoly, coeff_sub, coeff_C_mul_X_pow, ite_eq_left rfl,
      coeff_eq_zero_of_degree_lt ((degree_hornerPoly_lt _).trans_le (by
        rw [List.length_map]; exact_mod_cast hkey)), zero_sub]
  have hb : k.1 = k'.1 := by
    have := congrArg (coeff · W) h
    simp only [hcW k hk, hcW k' hk', neg_inj] at this
    exact hdistinct ((algebraMap F 𝕂).injective this)
  have hH : hornerPoly (k.2.map (algebraMap F 𝕂)) = hornerPoly (k'.2.map (algebraMap F 𝕂)) := by
    have := h
    rw [keyPoly, keyPoly, hb] at this
    exact sub_left_injective this
  have ht := hornerPoly_injective _ _ (by rw [List.length_map, List.length_map, hbus hb]) hH
  exact Prod.ext hb (List.map_injective_iff.mpr (algebraMap F 𝕂).injective ht)

/-- A sum over a list of keyed values, weighted by a function of the keys, sums each key's
values. -/
theorem sum_map_eq_sum_keys {κ R : Type*} [DecidableEq κ] [CommSemiring R] (D : κ → R) :
    ∀ L : List (κ × R), (L.map fun x ↦ D x.1 * x.2).sum =
      ∑ k ∈ (L.map (·.1)).toFinset, D k * ((L.filter (·.1 = k)).map (·.2)).sum
  | [] => by simp only [List.map_nil, List.sum_nil, List.toFinset_nil, Finset.sum_empty]
  | x :: L => by
    rw [List.map_cons, List.sum_cons, sum_map_eq_sum_keys D L, List.map_cons,
      List.toFinset_cons]
    have hsplit (k : κ) : (((x :: L).filter (·.1 = k)).map (·.2)).sum =
        (if x.1 = k then x.2 else 0) + ((L.filter (·.1 = k)).map (·.2)).sum := by
      rw [List.filter_cons]
      split_ifs with h1 h2 h2
      · rw [List.map_cons, List.sum_cons]
      · exact absurd (of_decide_eq_true h1) h2
      · exact absurd h2 (by simpa only [decide_eq_true_eq] using h1)
      · rw [zero_add]
    simp only [hsplit, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_insert_self _ _)]
    congr 1
    by_cases hx : x.1 ∈ (L.map (·.1)).toFinset
    · rw [Finset.insert_eq_of_mem hx]
    · rw [Finset.sum_insert hx]
      have h0 : ((L.filter (·.1 = x.1)).map (·.2)).sum = 0 := by
        rw [List.filter_eq_nil_iff.mpr fun y hy ↦ by
          simp only [decide_eq_true_eq]
          intro he
          exact hx (List.mem_toFinset.mpr (List.mem_map.mpr ⟨y, hy, he⟩))]
        rfl
      rw [h0, mul_zero, zero_add]

open Classical in
/-- **LogUp's Schwartz–Zippel bound on messages.** If some key's multiplicities do not sum to
zero, with tuples of one width per bus, at most `W ≥ 1`, and buses giving distinct base elements,
at most `(T + (T - 1) W) |𝕂|` pairs `(α, β)` are bad, `T` the number of messages. -/
theorem card_pairBad_le (W : ℕ) (hW : 1 ≤ W) (msgs : List ((ℕ × List F) × F))
    (hwidth : ∀ x ∈ msgs, x.1.2.length ≤ W)
    (hbus : ∀ x ∈ msgs, ∀ y ∈ msgs, x.1.1 = y.1.1 → x.1.2.length = y.1.2.length)
    (hdistinct : ∀ x ∈ msgs, ∀ y ∈ msgs,
      ((x.1.1 + 1 : ℕ) : F) = ((y.1.1 + 1 : ℕ) : F) → x.1.1 = y.1.1)
    (key : ℕ × List F) (hunbal : ((msgs.filter (·.1 = key)).map (·.2)).sum ≠ 0) :
    (univ.filter fun z : 𝕂 × 𝕂 ↦ PairBad W msgs z.1 z.2).card ≤
      (msgs.length + (msgs.length - 1) * W) * Fintype.card 𝕂 := by
  classical
  set keys := (msgs.map (·.1)).toFinset
  set M : ℕ × List F → 𝕂 := fun k ↦ algebraMap F 𝕂 ((msgs.filter (·.1 = k)).map (·.2)).sum
  have hmemkeys (k : ℕ × List F) (hk : k ∈ keys) : ∃ x ∈ msgs, x.1 = k := by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    exact ⟨x, hx, rfl⟩
  have hkey : key ∈ keys := by
    by_contra hk
    refine hunbal ?_
    rw [List.filter_eq_nil_iff.mpr fun y hy ↦ by
      simp only [decide_eq_true_eq]
      intro he
      exact hk (List.mem_toFinset.mpr (List.mem_map.mpr ⟨y, hy, he⟩))]
    rfl
  have hD : keys.card ≤ msgs.length :=
    (List.toFinset_card_le _).trans (by rw [List.length_map])
  have hsum (α β : 𝕂) : fractionSum W msgs α β =
      ∑ k ∈ keys, M k / (α - (keyPoly W k).eval β) := by
    rw [fractionSum]
    have := sum_map_eq_sum_keys (fun k ↦ (denominator (EF := EF) W k α β)⁻¹)
      (msgs.map fun x ↦ (x.1, algebraMap F 𝕂 x.2))
    simp only [List.map_map, Function.comp_def] at this
    rw [show (msgs.map fun x ↦ algebraMap F 𝕂 x.2 / denominator W x.1 α β) =
      msgs.map fun x ↦ (denominator W x.1 α β)⁻¹ * algebraMap F 𝕂 x.2 from
        List.map_congr_left fun x _ ↦ by rw [div_eq_inv_mul], this]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [denominator_eq, div_eq_inv_mul]
    congr 1
    simp only [M, map_list_sum, List.map_map]
    rw [List.filter_map, List.map_map]
    rfl
  have hsub : (univ.filter fun z : 𝕂 × 𝕂 ↦ PairBad W msgs z.1 z.2) ⊆
      univ.filter fun z : 𝕂 × 𝕂 ↦ (∃ k ∈ keys, z.1 - (keyPoly W k).eval z.2 = 0) ∨
        ∑ k ∈ keys, M k / (z.1 - (keyPoly W k).eval z.2) = 0 := by
    intro z hz
    replace hz := (Finset.mem_filter.mp hz).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases hz with ⟨x, hx, h0⟩ | h0
    · exact Or.inl ⟨x.1, List.mem_toFinset.mpr (List.mem_map_of_mem hx),
        (denominator_eq W x.1 z.1 z.2) ▸ h0⟩
    · exact Or.inr ((hsum z.1 z.2) ▸ h0)
  refine (Finset.card_le_card hsub).trans ((card_bad_le keys (keyPoly W) M W hW
    (fun k hk ↦ by
      obtain ⟨x, hx, rfl⟩ := hmemkeys k hk
      exact natDegree_keyPoly_le W x.1 (hwidth x hx))
    (fun k hk k' hk' h ↦ by
      obtain ⟨x, hx, rfl⟩ := hmemkeys k (Finset.mem_coe.mp hk)
      obtain ⟨y, hy, rfl⟩ := hmemkeys k' (Finset.mem_coe.mp hk')
      exact keyPoly_inj W x.1 y.1 (hwidth x hx) (hwidth y hy) (hbus x hx y hy)
        (hdistinct x hx y hy) h)
    key hkey (fun h ↦ hunbal ((algebraMap F 𝕂).injective (h.trans (map_zero _).symm)))).trans ?_)
  refine Nat.mul_le_mul_right _ (Nat.add_le_add hD (Nat.mul_le_mul_right _ (by omega)))

end Messages

end CompStark.Sound.LogUp
