/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Steps

/-! # Knowledge soundness from its steps

The acceptance probability averages, over `α`, `ζ` and `a`, the constraint check at `ζ` times
FRI's acceptance of the batched DEEP word. For each `(α, ζ)`:

* if some DEEP component is far from the code, the batched word is near for few `a`
  (`BatchingStep`), and FRI rejects far words (`FriStep`): `batchingError + friError`;
* otherwise, for `ζ` outside the base field, the claimed values are the decoded polynomials'
  (`DecodingStep`), so the check holds for few `ζ` unless `α` is one of few bad values
  (`AlgebraStep`): `(identityDegree + |𝔽|) / |𝕂| + foldingError`.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop Polynomial

local notation "𝔽" => KoalaBear.Field
local notation "𝕂" => KoalaBear.Ext4
local notation "F" => KoalaBear.Fast.Field

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

theorem length_openedWords {S : Setup} (p : Prover S) (α ζ : 𝕂) :
    (openedWords p α ζ).length = S.numOpened := by
  simp only [openedWords, List.length_append, List.length_map, List.length_finRange,
    List.length_flatMap, List.map_const', List.sum_replicate, smul_eq_mul, Setup.numOpened]
  ring

/-- The DEEP components of the opened words, by position. -/
noncomputable def components {S : Setup} (p : Prover S) (α ζ : 𝕂) :
    Fin S.numOpened → S.Point → 𝕂 := fun k ↦
  let w := (openedWords p α ζ)[k.val]'(by rw [length_openedWords]; exact k.isLt)
  deepComponent S w.1 w.2.1 w.2.2

/-- The batched DEEP word is the combination of the components by the powers of `a`. -/
theorem deepWord_eq {S : Setup} (p : Prover S) (α ζ a : 𝕂) :
    deepWord p α ζ a = fun i ↦ ∑ k : Fin S.numOpened, a ^ (k : Nat) * components p α ζ k i := by
  funext i
  rw [deepWord]
  have hmap : (fun x : ((S.Point → 𝔽) × 𝕂 × 𝕂) × Nat ↦ match x with
      | ((f, z, y), k) => a ^ k * (y - algebraMap 𝔽 𝕂 (f i)) / (z - S.domain i)) =
      fun x ↦ a ^ x.2 * (x.1.2.2 - algebraMap 𝔽 𝕂 (x.1.1 i)) / (x.1.2.1 - S.domain i) := by
    funext x
    rcases x with ⟨⟨f, z, y⟩, k⟩
    rfl
  rw [hmap, sum_zipIdx_map (fun (w : (S.Point → 𝔽) × 𝕂 × 𝕂) k ↦
    a ^ k * (w.2.2 - algebraMap 𝔽 𝕂 (w.1 i)) / (w.2.1 - S.domain i)) _ 0]
  refine Fintype.sum_equiv (finCongr (length_openedWords p α ζ)) _ _ fun k ↦ ?_
  simp only [Nat.zero_add, components, deepComponent, finCongr_apply, Fin.val_cast, mul_div_assoc]
  rfl

/-! ### Far components -/

/-- `|𝕂|` as an extended real. -/
noncomputable abbrev card𝕂 : ENNReal := Fintype.card 𝕂

theorem card𝕂_ne_zero : card𝕂 ≠ 0 := by
  simp only [card𝕂, ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true]

theorem card𝕂_ne_top : card𝕂 ≠ ⊤ := ENNReal.natCast_ne_top _

open Classical in
/-- If some DEEP component is far, FRI's acceptance summed over `a` is at most
`|𝕂| (batchingError + friError)`. -/
theorem sum_fri_of_far {S : Setup} (hF : FriStep S) (hF1 : FriAtMostOne S)
    (hB : BatchingStep S) (δ : NNReal) (p : Prover S) (α ζ : 𝕂)
    (hfar : ∃ k, ¬ Near S δ (components p α ζ k)) :
    ∑ a : 𝕂, friAcceptance S (deepWord p α ζ a) ≤
      card𝕂 * (batchingError S δ + friError S δ) := by
  have hb := hB δ (components p α ζ) hfar
  set P : 𝕂 → Prop := fun a ↦
    Near S δ fun i ↦ ∑ k : Fin S.numOpened, a ^ (k : Nat) * components p α ζ k i
  have hnear : ((Finset.univ.filter P).card : ENNReal) ≤ card𝕂 * batchingError S δ := by
    have h := (ENNReal.div_le_iff_le_mul (Or.inl card𝕂_ne_zero) (Or.inl card𝕂_ne_top)).mp hb
    rwa [mul_comm] at h
  calc ∑ a : 𝕂, friAcceptance S (deepWord p α ζ a)
      ≤ ∑ a : 𝕂, ((if P a then 1 else 0) + friError S δ) := by
        refine Finset.sum_le_sum fun a _ ↦ ?_
        split_ifs with ha
        · exact (hF1 _).trans le_self_add
        · rw [zero_add, deepWord_eq]
          exact hF δ _ ha
    _ = (Finset.univ.filter P).card + card𝕂 * friError S δ := by
        rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
    _ ≤ card𝕂 * (batchingError S δ + friError S δ) := by
        rw [mul_add]; gcongr

/-! ### Near components -/

theorem forall_mem_openedWords {S : Setup} {δ : NNReal} (p : Prover S) (α ζ : 𝕂)
    (h : ∀ k, Near S δ (components p α ζ k)) :
    ∀ w ∈ openedWords p α ζ, Near S δ (deepComponent S w.1 w.2.1 w.2.2) := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
  exact h ⟨i, by rw [← length_openedWords p α ζ]; exact hi⟩

/-- With near components and `ζ` outside the base field, the prover's openings are the decoded
polynomials' values. -/
theorem openings_eq_true {S : Setup} (hD : DecodingStep S) {δ : NNReal}
    (hδ : δ ≤ S.uniqueDecodingRadius) (p : Prover S) (α ζ : 𝕂) (hζ : OutsideBase ζ)
    (h : ∀ k, Near S δ (components p α ζ k)) :
    p.openings α ζ = trueOpenings S (fun j ↦ decoded S (p.trace j))
      (fun c e ↦ decoded S (p.quotient α c e)) ζ := by
  obtain ⟨h1, h2, h3⟩ := hD δ hδ p α ζ hζ (forall_mem_openedWords p α ζ h)
  rcases hp : p.openings α ζ with ⟨a, b, c⟩
  rw [hp] at h1 h2 h3
  simp only [trueOpenings, Openings.mk.injEq]
  exact ⟨funext h1, funext h2, funext fun c ↦ funext (h3 c)⟩

/-! ### Summing over the challenges -/

section Sums
variable {S : Setup} (hF : FriStep S) (hF1 : FriAtMostOne S) (hB : BatchingStep S)
  (hD : DecodingStep S) (hA : AlgebraStep S) (publicValues : List F) (p : Prover S)
  (δ : NNReal)

open Classical

include hF hF1 hB in
/-- For one `(α, ζ)`: `|𝕂| (batchingError + friError)` if a component is far, and `|𝕂|` if the
check passes with near components. -/
theorem sum_a_le (α ζ : 𝕂) :
    ∑ a : 𝕂, (if ConstraintsHoldAt S publicValues α ζ (p.openings α ζ)
      then friAcceptance S (deepWord p α ζ a) else 0) ≤
    card𝕂 * (batchingError S δ + friError S δ) +
      if (∀ k, Near S δ (components p α ζ k)) ∧
        ConstraintsHoldAt S publicValues α ζ (p.openings α ζ) then card𝕂 else 0 := by
  by_cases hH : ConstraintsHoldAt S publicValues α ζ (p.openings α ζ)
  · simp only [hH, ↓reduceIte, and_true]
    by_cases hG : ∀ k, Near S δ (components p α ζ k)
    · simp only [hG, implies_true, ↓reduceIte]
      refine le_add_left ((Finset.sum_le_sum fun a _ ↦ hF1 _).trans ?_)
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    · simp only [hG, ↓reduceIte, add_zero]
      push Not at hG
      exact sum_fri_of_far hF hF1 hB δ p α ζ hG
  · simp only [hH, ↓reduceIte, Finset.sum_const_zero, zero_le]

/-- The points outside the base field number `|𝔽|`... in `𝕂` the base field's image. -/
theorem card_not_outsideBase :
    (Finset.univ.filter fun ζ : 𝕂 ↦ ¬ OutsideBase ζ).card = Fintype.card 𝔽 := by
  have : (Finset.univ.filter fun ζ : 𝕂 ↦ ¬ OutsideBase ζ) =
      Finset.univ.map ⟨algebraMap 𝔽 𝕂, (algebraMap 𝔽 𝕂).injective⟩ := by
    ext ζ
    simp only [OutsideBase, not_not, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_map, Function.Embedding.coeFn_mk, Set.mem_range]
  rw [this, Finset.card_map, Finset.card_univ]

-- The constructor-name linter exhausts its recursion budget on this proof's locals.
set_option linter.constructorNameAsVariable false in
include hD in
/-- The `ζ` where the components are near and the check passes: in the base field, or the check
passes with the decoded polynomials' true values. -/
theorem card_near_check_le (hδ : δ ≤ S.uniqueDecodingRadius) (α : 𝕂) :
    (Finset.univ.filter fun ζ : 𝕂 ↦ (∀ k, Near S δ (components p α ζ k)) ∧
        ConstraintsHoldAt S publicValues α ζ (p.openings α ζ)).card ≤
      Fintype.card 𝔽 + (Finset.univ.filter fun ζ : 𝕂 ↦ OutsideBase ζ ∧
        ConstraintsHoldAt S publicValues α ζ (trueOpenings S (fun j ↦ decoded S (p.trace j))
          (fun c e ↦ decoded S (p.quotient α c e)) ζ)).card := by
  have hsub : (Finset.univ.filter fun ζ : 𝕂 ↦ (∀ k, Near S δ (components p α ζ k)) ∧
        ConstraintsHoldAt S publicValues α ζ (p.openings α ζ)) ⊆
      (Finset.univ.filter fun ζ : 𝕂 ↦ ¬ OutsideBase ζ) ∪
      (Finset.univ.filter fun ζ : 𝕂 ↦ OutsideBase ζ ∧
        ConstraintsHoldAt S publicValues α ζ (trueOpenings S (fun j ↦ decoded S (p.trace j))
          (fun c e ↦ decoded S (p.quotient α c e)) ζ)) := by
    intro ζ hζ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hζ ⊢
    by_cases hb : OutsideBase ζ
    · right
      have h := hζ.2
      rw [openings_eq_true hD hδ p α ζ hb hζ.1] at h
      exact ⟨hb, h⟩
    · exact Or.inl hb
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rwa [card_not_outsideBase] at h

end Sums

/-! ### The bound -/

theorem natDegree_decoded (S : Setup) (f : S.Point → 𝔽) : (decoded S f).natDegree ≤ S.n := by
  have h := ((degreeLTEquiv 𝔽 (S.n + 1)).symm
    (Classical.choose (Finset.univ.exists_min_image (fun c ↦ hammingDist f fun i ↦
      ((degreeLTEquiv 𝔽 (S.n + 1)).symm c : 𝔽[X]).eval
        (basePoint (S.logN + S.params.logBlowup) i)) Finset.univ_nonempty))).2
  rw [mem_degreeLT] at h
  by_cases hp : decoded S f = 0
  · rw [hp, natDegree_zero]; exact Nat.zero_le _
  · exact Nat.lt_succ_iff.mp ((natDegree_lt_iff_degree_lt hp).mpr h)

/-- `|𝕂|⁻³ (|𝕂|³ u + |𝕂|² v) = u + v / |𝕂|`. -/
theorem inv_cube_mul (u v : ENNReal) :
    card𝕂⁻¹ ^ 3 * (card𝕂 ^ 3 * u + card𝕂 ^ 2 * v) = u + v / card𝕂 := by
  have h0 := card𝕂_ne_zero
  have ht := card𝕂_ne_top
  have h2 : card𝕂⁻¹ ^ 2 * card𝕂 ^ 2 = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel h0 ht, one_pow]
  have h3 : card𝕂⁻¹ ^ 3 * card𝕂 ^ 3 = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel h0 ht, one_pow]
  rw [mul_add, ← mul_assoc, h3, one_mul, div_eq_mul_inv]
  congr 1
  calc card𝕂⁻¹ ^ 3 * (card𝕂 ^ 2 * v) = (card𝕂⁻¹ ^ 2 * card𝕂 ^ 2) * (v * card𝕂⁻¹) := by ring
    _ = v * card𝕂⁻¹ := by rw [h2, one_mul]

open Classical in
/-- Knowledge soundness from the four steps. -/
theorem knowledgeSoundness_of {S : Setup} (hF : FriStep S) (hF1 : FriAtMostOne S)
    (hB : BatchingStep S) (hD : DecodingStep S) (hA : AlgebraStep S) (publicValues : List F)
    (p : Prover S) (δ : NNReal) (hδ : δ ≤ S.uniqueDecodingRadius)
    (hsat : ¬ S.air.Satisfied S.logN (extract p) publicValues) :
    acceptance publicValues p ≤ knowledgeError S δ := by
  obtain ⟨bad, hbad, hgood⟩ := hA publicValues (fun j ↦ decoded S (p.trace j))
    (fun j ↦ natDegree_decoded S _) hsat
  set E := batchingError S δ + friError S δ
  set D := S.identityDegree
  -- The `ζ` with near components and a passing check, for one `α`.
  have hcount : ∀ α : 𝕂, ((Finset.univ.filter fun ζ : 𝕂 ↦
      (∀ k, Near S δ (components p α ζ k)) ∧
        ConstraintsHoldAt S publicValues α ζ (p.openings α ζ)).card : ENNReal) ≤
      Fintype.card 𝔽 + ((if α ∈ bad then card𝕂 else 0) + D) := by
    intro α
    refine (Nat.cast_le.mpr (card_near_check_le hD publicValues p δ hδ α)).trans ?_
    rw [Nat.cast_add]
    gcongr
    by_cases hα : α ∈ bad
    · simp only [hα, ↓reduceIte]
      exact (Nat.cast_le.mpr (Finset.card_le_univ _)).trans_eq rfl |>.trans le_self_add
    · simp only [hα, ↓reduceIte, zero_add]
      exact Nat.cast_le.mpr (hgood α hα _ fun c e ↦ natDegree_decoded S _)
  -- Summing over `a` and `ζ`, for one `α`.
  have hα : ∀ α : 𝕂, ∑ ζ : 𝕂, ∑ a : 𝕂,
      (if ConstraintsHoldAt S publicValues α ζ (p.openings α ζ)
        then friAcceptance S (deepWord p α ζ a) else 0) ≤
      card𝕂 ^ 2 * E + card𝕂 * (Fintype.card 𝔽 + ((if α ∈ bad then card𝕂 else 0) + D)) := by
    intro α
    refine (Finset.sum_le_sum fun ζ _ ↦ sum_a_le hF hF1 hB publicValues p δ α ζ).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      ← mul_assoc, ← pow_two, mul_comm _ card𝕂]
    exact add_le_add le_rfl (mul_le_mul_right (hcount α) _)
  -- Summing over `α`.
  have hsum : ∑ α : 𝕂, ∑ ζ : 𝕂, ∑ a : 𝕂,
      (if ConstraintsHoldAt S publicValues α ζ (p.openings α ζ)
        then friAcceptance S (deepWord p α ζ a) else 0) ≤
      card𝕂 ^ 3 * E + card𝕂 ^ 2 * (Fintype.card 𝔽 + bad.card + D) := by
    refine (Finset.sum_le_sum fun α _ ↦ hα α).trans_eq ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.sum_const, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
    ring
  calc acceptance publicValues p
      ≤ card𝕂⁻¹ ^ 3 * (card𝕂 ^ 3 * E + card𝕂 ^ 2 * (Fintype.card 𝔽 + bad.card + D)) :=
        mul_le_mul_right hsum _
    _ = E + (Fintype.card 𝔽 + bad.card + D) / card𝕂 := inv_cube_mul _ _
    _ ≤ knowledgeError S δ := by
        have key : (Fintype.card 𝔽 + bad.card + D : ENNReal) ≤
            ((S.air.constraints.length - 1 : Nat) : ENNReal) + ((D + Fintype.card 𝔽 : Nat) :
              ENNReal) := by
          rw [Nat.cast_add, add_comm ((D : Nat) : ENNReal), ← add_assoc,
            add_comm _ ((Fintype.card 𝔽 : Nat) : ENNReal), add_assoc, add_assoc]
          exact add_le_add le_rfl (add_le_add (Nat.cast_le.mpr hbad) le_rfl)
        have h := ENNReal.div_le_div_right key card𝕂
        rw [← ENNReal.div_add_div_same (a := ((S.air.constraints.length - 1 : Nat) : ENNReal))]
          at h
        rw [knowledgeError, foldingError, outOfDomainError, add_comm E]
        calc (Fintype.card 𝔽 + bad.card + D : ENNReal) / card𝕂 + E
            ≤ ((S.air.constraints.length - 1 : Nat) : ENNReal) / card𝕂 +
                ((D + Fintype.card 𝔽 : Nat) : ENNReal) / card𝕂 + E := add_le_add h le_rfl
          _ = _ := by simp only [E, ← add_assoc]; rfl

end CompStark.Sound
