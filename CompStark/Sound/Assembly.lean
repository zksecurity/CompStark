/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Steps

/-! # Knowledge soundness from its steps

The acceptance probability averages, over `α`, `ζ` and `a`, the constraint check at `ζ` times
FRI's acceptance of the batched DEEP word. For each `(α, ζ)`:

* if the DEEP components are not `(δ' - 2/N)`-near the code on a common set, the batched word is
  `δ`-near for few `a` (`BatchingStep`), and FRI rejects `δ`-far words (`FriStep`):
  `batchingError + friError`;
* otherwise, for `ζ` off the trace domain, the claimed values are those of a candidate trace
  and quotient at `δ'` (`DecodingStep`), polynomials close to the committed words, of which there
  are at most `listSize` each; every candidate trace fails the AIR, so the check holds for few
  `ζ` per pair of candidates unless `α` is one of few bad values per candidate trace
  (`AlgebraStep`).
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop Polynomial

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### The batched DEEP word -/

/-- A sum over a list with its indices from `i`, as a sum over the positions. -/
theorem sum_zipIdx_map {β M : Type} [AddCommMonoid M] (g : β → Nat → M) :
    ∀ (l : List β) (i : Nat),
      ((l.zipIdx i).map fun p ↦ g p.1 p.2).sum = ∑ k : Fin l.length, g l[k] (i + k)
  | [], _ => rfl
  | b :: l, i => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, sum_zipIdx_map g l (i + 1)]
    erw [Fin.sum_univ_succ (n := l.length)]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]
    rfl

theorem length_openedWords {S : Setup EF} (p : Prover S) (α ζ : 𝕂) :
    (openedWords p α ζ).length = S.numOpened := by
  simp only [openedWords, List.length_append, List.length_map, List.length_finRange,
    List.length_flatMap, List.map_const', List.sum_replicate, smul_eq_mul, Setup.numOpened]
  ring

/-- The batched DEEP word is the combination of the components by the powers of `a`. -/
theorem deepWord_eq {S : Setup EF} (p : Prover S) (α ζ a : 𝕂) :
    deepWord p α ζ a = fun i ↦ ∑ k : Fin S.numOpened, a ^ (k : Nat) * components p α ζ k i := by
  funext i
  rw [deepWord]
  have hmap : (fun x : ((S.Point → F) × 𝕂 × 𝕂) × Nat ↦ match x with
      | ((f, z, y), k) => a ^ k * (y - algebraMap F 𝕂 (f i)) / (z - S.domain i)) =
      fun x ↦ a ^ x.2 * (x.1.2.2 - algebraMap F 𝕂 (x.1.1 i)) / (x.1.2.1 - S.domain i) := by
    funext x
    rcases x with ⟨⟨f, z, y⟩, k⟩
    rfl
  rw [hmap, sum_zipIdx_map (fun (w : (S.Point → F) × 𝕂 × 𝕂) k ↦
    a ^ k * (w.2.2 - algebraMap F 𝕂 (w.1 i)) / (w.2.1 - S.domain i)) _ 0]
  refine Fintype.sum_equiv (finCongr (length_openedWords p α ζ)) _ _ fun k ↦ ?_
  simp only [Nat.zero_add, components, deepComponent, finCongr_apply, Fin.val_cast, mul_div_assoc]
  rfl

/-! ### Far components -/

/-- `|𝕂|` as an extended real. -/
noncomputable abbrev card𝕂 (EF : Type) [Challenge F EF] : ENNReal := Fintype.card
    (Challenge.Spec EF)

theorem card𝕂_ne_zero : card𝕂 EF ≠ 0 := by
  simp only [card𝕂, ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true]

theorem card𝕂_ne_top : card𝕂 EF ≠ ⊤ := ENNReal.natCast_ne_top _

open Classical in
/-- If the DEEP components are not `δ'`-near on a common set, FRI's acceptance at `δ` summed over
`a` is at most `|𝕂| (batchingError + friError)`. -/
theorem sum_fri_of_far {S : Setup EF} (hF : FriStep S) (hF1 : FriAtMostOne S)
    (hB : BatchingStep S) (δ : NNReal) (δ' : ℝ) (p : Prover S) (α ζ : 𝕂)
    (hfar : ¬ NearTogether S δ' (components p α ζ)) :
    ∑ a : 𝕂, friAcceptance S (deepWord p α ζ a) ≤
      card𝕂 EF * (batchingError S δ δ' + friError S δ) := by
  have hb := hB δ δ' (components p α ζ) hfar
  set P : 𝕂 → Prop := fun a ↦
    Near S δ fun i ↦ ∑ k : Fin S.numOpened, a ^ (k : Nat) * components p α ζ k i
  have hnear : ((Finset.univ.filter P).card : ENNReal) ≤ card𝕂 EF * batchingError S δ δ' := by
    have h := (ENNReal.div_le_iff_le_mul (Or.inl (card𝕂_ne_zero (EF := EF)))
      (Or.inl (card𝕂_ne_top (EF := EF)))).mp hb
    rwa [mul_comm] at h
  calc ∑ a : 𝕂, friAcceptance S (deepWord p α ζ a)
      ≤ ∑ a : 𝕂, ((if P a then 1 else 0) + friError S δ) := by
        refine Finset.sum_le_sum fun a _ ↦ ?_
        split_ifs with ha
        · exact (hF1 _).trans le_self_add
        · rw [zero_add, deepWord_eq]
          exact hF δ _ ha
    _ = (Finset.univ.filter P).card + card𝕂 EF * friError S δ := by
        rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
    _ ≤ card𝕂 EF * (batchingError S δ δ' + friError S δ) := by
        rw [mul_add]; gcongr

/-! ### The candidates -/

/-- The candidate polynomials of words `words` at proximity `δ`: degree at most `n`, agreeing with
the words on a common set of `(1 - δ) N` points. -/
def candidates (S : Setup EF) {ι : Type} (δ : ℝ) (words : ι → S.Point → F) : Set (ι → F[X]) :=
  {polys | (∀ k, (polys k).natDegree ≤ S.n) ∧ Agree S δ words polys}

theorem candidates_finite (S : Setup EF) {ι : Type} [Fintype ι] (δ : ℝ)
    (words : ι → S.Point → F) : (candidates S δ words).Finite := by
  classical
  refine Set.Finite.of_finite_image (f := fun polys k (i : Fin (S.n + 1)) ↦ (polys k).coeff i)
    (Set.toFinite _) fun P hP Q hQ h ↦ funext fun k ↦ Polynomial.ext fun m ↦ ?_
  by_cases hm : m ≤ S.n
  · exact congrFun (congrFun h k) ⟨m, Nat.lt_succ_of_le hm⟩
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hP.1 k) (Nat.lt_of_not_le hm)),
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hQ.1 k) (Nat.lt_of_not_le hm))]

theorem card_candidates_le (S : Setup EF) {ι : Type} [Fintype ι] [DecidableEq ι] (δ : ℝ)
    (words : ι → S.Point → F) :
    (candidates_finite S δ words).toFinset.card ≤ S.listSize ι δ := by
  rw [← Set.ncard_eq_toFinset_card _ (candidates_finite S δ words)]
  exact Finset.le_sup (f := fun words : ι → S.Point → F ↦
    {polys : ι → F[X] | (∀ k, (polys k).natDegree ≤ S.n) ∧ Agree S δ words polys}.ncard)
    (Finset.mem_univ words)

/-! ### Summing over the challenges -/

section Sums
variable {S : Setup EF} (hF : FriStep S) (hF1 : FriAtMostOne S) (hB : BatchingStep S)
  (hD : DecodingStep S) (hA : AlgebraStep S) (publicValues : List F) (p : Prover S)

open Classical

include hF hF1 hB in
/-- For one `(α, ζ)`: `|𝕂| (batchingError + friError)` if a component is far, and `|𝕂|` if the
check passes with near components. -/
theorem sum_a_le (δ : NNReal) (δ' : ℝ) (α ζ : 𝕂) :
    ∑ a : 𝕂, (if ConstraintsHoldAt S publicValues α ζ (p.openings α ζ)
      then friAcceptance S (deepWord p α ζ a) else 0) ≤
    card𝕂 EF * (batchingError S δ δ' + friError S δ) +
      if NearTogether S δ' (components p α ζ) ∧
        ConstraintsHoldAt S publicValues α ζ (p.openings α ζ) then card𝕂 EF else 0 := by
  by_cases hH : ConstraintsHoldAt S publicValues α ζ (p.openings α ζ)
  · simp only [hH, ↓reduceIte, and_true]
    by_cases hG : NearTogether S δ' (components p α ζ)
    · simp only [hG, ↓reduceIte]
      refine le_add_left ((Finset.sum_le_sum fun a _ ↦ hF1 _).trans ?_)
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    · simp only [hG, ↓reduceIte, add_zero]
      exact sum_fri_of_far hF hF1 hB δ δ' p α ζ hG
  · simp only [hH, ↓reduceIte, Finset.sum_const_zero, zero_le]

-- The constructor-name linter exhausts its recursion budget on this proof's locals.
set_option linter.constructorNameAsVariable false in
/-- The points on the trace domain number at most `n`. -/
theorem card_not_offTraceDomain (S : Setup EF) :
    (Finset.univ.filter fun ζ : 𝕂 ↦ ¬ OffTraceDomain S ζ).card ≤ S.n := by
  classical
  have hsub : (Finset.univ.filter fun ζ : 𝕂 ↦ ¬ OffTraceDomain S ζ) ⊆
      (nthRoots S.n (1 : 𝕂)).toFinset := by
    intro ζ hζ
    simp only [OffTraceDomain, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hζ
    rw [Multiset.mem_toFinset, mem_nthRoots (Nat.two_pow_pos S.logN)]
    exact hζ
  exact (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans (card_nthRoots _ _))

-- The constructor-name linter exhausts its recursion budget on this proof's locals.
set_option linter.constructorNameAsVariable false in
include hD in
/-- The `ζ` where the components are near on a common set at `δ - 2/N` and the check passes: on
the trace domain, or the check passes with the true values of a candidate trace and quotient at
`δ`. -/
theorem card_near_check_le (δ : NNReal) (hδ : (δ : ℝ) < 1 - S.rate) (α : 𝕂) :
    (Finset.univ.filter fun ζ : 𝕂 ↦ NearTogether S ((δ : ℝ) - 2 / S.size) (components p α ζ) ∧
        ConstraintsHoldAt S publicValues α ζ (p.openings α ζ)).card ≤
      S.n + ∑ P ∈ (candidates_finite S δ p.trace).toFinset,
        ∑ Q ∈ (candidates_finite S δ fun ce : Fin S.chunks × Fin (Challenge.d EF) ↦
          p.quotient α ce.1 ce.2).toFinset,
        (Finset.univ.filter fun ζ : 𝕂 ↦ OffTraceDomain S ζ ∧
          ConstraintsHoldAt S publicValues α ζ
            (trueOpenings S P (fun c e ↦ Q (c, e)) ζ)).card := by
  set C1 := (candidates_finite S δ p.trace).toFinset
  set C2 := (candidates_finite S δ fun ce : Fin S.chunks × Fin (Challenge.d EF) ↦
    p.quotient α ce.1 ce.2).toFinset
  set check : (Fin S.air.width → F[X]) → (Fin S.chunks × Fin (Challenge.d EF) → F[X]) → Finset 𝕂 :=
    fun P Q ↦ Finset.univ.filter fun ζ : 𝕂 ↦ OffTraceDomain S ζ ∧
      ConstraintsHoldAt S publicValues α ζ (trueOpenings S P (fun c e ↦ Q (c, e)) ζ)
  have hsub : (Finset.univ.filter fun ζ : 𝕂 ↦
        NearTogether S ((δ : ℝ) - 2 / S.size) (components p α ζ) ∧
        ConstraintsHoldAt S publicValues α ζ (p.openings α ζ)) ⊆
      (Finset.univ.filter fun ζ : 𝕂 ↦ ¬ OffTraceDomain S ζ) ∪
        C1.biUnion fun P ↦ C2.biUnion fun Q ↦ check P Q := by
    intro ζ hζ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion]
    by_cases hb : OffTraceDomain S ζ
    · right
      obtain ⟨tr, qu, htd, hta, hqd, hqa, ho⟩ := hD δ hδ p α ζ hb hζ.1
      refine ⟨tr, (Set.Finite.mem_toFinset _).mpr ⟨htd, hta⟩, fun ce ↦ qu ce.1 ce.2,
        (Set.Finite.mem_toFinset _).mpr ⟨fun ce ↦ hqd ce.1 ce.2, hqa⟩, ?_⟩
      simp only [check, Finset.mem_filter, Finset.mem_univ, true_and]
      have h := hζ.2
      rw [ho] at h
      exact ⟨hb, h⟩
    · exact Or.inl hb
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  exact Nat.add_le_add (card_not_offTraceDomain S) (Finset.card_biUnion_le.trans
    (Finset.sum_le_sum fun P _ ↦ Finset.card_biUnion_le))

end Sums

/-- `|𝕂|⁻³ (|𝕂|³ u + |𝕂|² v) = u + v / |𝕂|`. -/
theorem inv_cube_mul (u v : ENNReal) :
    (card𝕂 EF)⁻¹ ^ 3 * (card𝕂 EF ^ 3 * u + card𝕂 EF ^ 2 * v) = u + v / card𝕂 EF := by
  have h0 := card𝕂_ne_zero (EF := EF)
  have ht := card𝕂_ne_top (EF := EF)
  have h2 : (card𝕂 EF)⁻¹ ^ 2 * card𝕂 EF ^ 2 = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel h0 ht, one_pow]
  have h3 : (card𝕂 EF)⁻¹ ^ 3 * card𝕂 EF ^ 3 = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel h0 ht, one_pow]
  rw [mul_add, ← mul_assoc, h3, one_mul, div_eq_mul_inv]
  congr 1
  calc (card𝕂 EF)⁻¹ ^ 3 * (card𝕂 EF ^ 2 * v)
        = ((card𝕂 EF)⁻¹ ^ 2 * card𝕂 EF ^ 2) * (v * (card𝕂 EF)⁻¹) := by ring
    _ = v * (card𝕂 EF)⁻¹ := by rw [h2, one_mul]

open Classical in
/-- Knowledge soundness from the four steps. -/
theorem knowledgeSoundness_of {S : Setup EF} (hF : FriStep S) (hF1 : FriAtMostOne S)
    (hB : BatchingStep S) (hD : DecodingStep S) (hA : AlgebraStep S) (publicValues : List F)
    (p : Prover S) (δ δ' : NNReal) (hδ' : (δ' : ℝ) < 1 - S.rate)
    (hfail : ∀ trace ∈ closeTraces S δ' p.trace, ¬ S.air.Satisfied S.logN trace publicValues) :
    acceptance publicValues p ≤ knowledgeError S δ δ' := by
  set C1 := (candidates_finite S δ' p.trace).toFinset
  set ℓT := S.listSize (Fin S.air.width) δ'
  set ℓQ := S.listSize (Fin S.chunks × Fin (Challenge.d EF)) δ'
  set E := batchingError S δ ((δ' : ℝ) - 2 / S.size) + friError S δ
  set D := S.identityDegree
  set M := S.n
  -- Every candidate trace fails the AIR, so it has few bad `α`.
  have hbadP : ∀ P ∈ C1, ∃ bad : Finset 𝕂, bad.card ≤ S.air.constraints.length - 1 ∧
      ∀ α ∉ bad, ∀ quotient : Fin S.chunks → Fin (Challenge.d EF) → F[X],
        (∀ c e, (quotient c e).natDegree ≤ S.n) →
        (Finset.univ.filter fun ζ : 𝕂 ↦ OffTraceDomain S ζ ∧
          ConstraintsHoldAt S publicValues α ζ (trueOpenings S P quotient ζ)).card ≤ D := by
    intro P hP
    rw [Set.Finite.mem_toFinset] at hP
    exact hA publicValues P hP.1 (hfail _ ⟨P, hP.1, hP.2, rfl⟩)
  choose! badOf hbadOf hgoodOf using hbadP
  set bad := C1.biUnion badOf
  have hbad : bad.card ≤ ℓT * (S.air.constraints.length - 1) :=
    Finset.card_biUnion_le.trans ((Finset.sum_le_sum fun P hP ↦ hbadOf P hP).trans (by
      rw [Finset.sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (card_candidates_le S δ' p.trace)))
  -- The `ζ` with near components and a passing check, for one `α`.
  have hcount : ∀ α : 𝕂, ((Finset.univ.filter fun ζ : 𝕂 ↦
      NearTogether S ((δ' : ℝ) - 2 / S.size) (components p α ζ) ∧
        ConstraintsHoldAt S publicValues α ζ (p.openings α ζ)).card : ENNReal) ≤
      M + ((if α ∈ bad then card𝕂 EF else 0) + (ℓT * ℓQ * D : Nat)) := by
    intro α
    by_cases hα : α ∈ bad
    · simp only [hα, ↓reduceIte]
      refine le_trans ?_ (le_add_left le_self_add)
      exact Nat.cast_le.mpr (Finset.card_le_univ _)
    simp only [hα, ↓reduceIte, zero_add]
    refine (Nat.cast_le.mpr (card_near_check_le hD publicValues p δ' hδ' α)).trans ?_
    rw [Nat.cast_add]
    refine add_le_add le_rfl (Nat.cast_le.mpr ?_)
    set C2 := (candidates_finite S δ' fun ce : Fin S.chunks × Fin (Challenge.d EF) ↦
      p.quotient α ce.1 ce.2).toFinset
    calc ∑ P ∈ C1, ∑ Q ∈ C2, (Finset.univ.filter fun ζ : 𝕂 ↦ OffTraceDomain S ζ ∧
          ConstraintsHoldAt S publicValues α ζ (trueOpenings S P (fun c e ↦ Q (c, e)) ζ)).card
        ≤ ∑ P ∈ C1, ∑ Q ∈ C2, D := by
          refine Finset.sum_le_sum fun P hP ↦ Finset.sum_le_sum fun Q hQ ↦ ?_
          have hαP : α ∉ badOf P := fun h ↦ hα (Finset.mem_biUnion.mpr ⟨P, hP, h⟩)
          rw [Set.Finite.mem_toFinset] at hQ
          exact hgoodOf P hP α hαP _ fun c e ↦ hQ.1 (c, e)
      _ = C1.card * C2.card * D := by
          rw [Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_assoc]
      _ ≤ ℓT * ℓQ * D := Nat.mul_le_mul_right _ (Nat.mul_le_mul (card_candidates_le S δ' _)
          (card_candidates_le S δ' _))
  -- Summing over `a` and `ζ`, for one `α`.
  have hα : ∀ α : 𝕂, ∑ ζ : 𝕂, ∑ a : 𝕂,
      (if ConstraintsHoldAt S publicValues α ζ (p.openings α ζ)
        then friAcceptance S (deepWord p α ζ a) else 0) ≤
      card𝕂 EF ^ 2 * E + card𝕂 EF * (M + ((if α ∈ bad then card𝕂 EF else 0) +
        (ℓT * ℓQ * D : Nat))) := by
    intro α
    refine (Finset.sum_le_sum fun ζ _ ↦
      sum_a_le hF hF1 hB publicValues p δ ((δ' : ℝ) - 2 / S.size) α ζ).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      ← mul_assoc, ← pow_two, mul_comm _ (card𝕂 EF)]
    exact add_le_add le_rfl (mul_le_mul_right (hcount α) _)
  -- Summing over `α`.
  have hsum : ∑ α : 𝕂, ∑ ζ : 𝕂, ∑ a : 𝕂,
      (if ConstraintsHoldAt S publicValues α ζ (p.openings α ζ)
        then friAcceptance S (deepWord p α ζ a) else 0) ≤
      card𝕂 EF ^ 3 * E + card𝕂 EF ^ 2 * (M + bad.card + (ℓT * ℓQ * D : Nat)) := by
    refine (Finset.sum_le_sum fun α _ ↦ hα α).trans_eq ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.sum_const, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
    ring
  calc acceptance publicValues p
      ≤ (card𝕂 EF)⁻¹ ^ 3 * (card𝕂 EF ^ 3 * E +
          card𝕂 EF ^ 2 * (M + bad.card + (ℓT * ℓQ * D : Nat))) :=
        mul_le_mul_right hsum _
    _ = E + (M + bad.card + (ℓT * ℓQ * D : Nat)) / card𝕂 EF := inv_cube_mul _ _
    _ ≤ knowledgeError S δ δ' := by
        have key : (M + bad.card + (ℓT * ℓQ * D : Nat) : ENNReal) ≤
            ((ℓT * (S.air.constraints.length - 1) : Nat) : ENNReal) +
              ((ℓT * ℓQ * D + S.n : Nat) : ENNReal) := by
          have hk : M + bad.card + ℓT * ℓQ * D ≤
              ℓT * (S.air.constraints.length - 1) + (ℓT * ℓQ * D + S.n) := by
            simp only [M]
            omega
          exact_mod_cast hk
        have h := ENNReal.div_le_div_right key (card𝕂 EF)
        rw [← ENNReal.div_add_div_same (a := ((ℓT * (S.air.constraints.length - 1) : Nat) :
          ENNReal))] at h
        rw [knowledgeError, foldingError, outOfDomainError, add_comm E]
        calc (M + bad.card + (ℓT * ℓQ * D : Nat) : ENNReal) / card𝕂 EF + E
            ≤ ((ℓT * (S.air.constraints.length - 1) : Nat) : ENNReal) / card𝕂 EF +
                ((ℓT * ℓQ * D + S.n : Nat) : ENNReal) / card𝕂 EF + E :=
              add_le_add h le_rfl
          _ = _ := by simp only [E, ← add_assoc]; rfl

end CompStark.Sound
