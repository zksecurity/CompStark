/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Fri
public import CompStark.Sound.Batching
public import CompStark.Sound.Decoding
public import CompStark.Sound.Algebra

/-! # The single-instance pieces of knowledge soundness

The knowledge-soundness proof (`Sound/BatchAssembly.lean`) averages, over `α`, `ζ` and `a`, the
constraint checks at `ζ` times FRI's acceptance of the batched DEEP word. Its single-instance
pieces are here:

* the batched DEEP word over a list of opened words is the combination of their DEEP components
  by the powers of `a` (`sum_zipIdx_deep`);
* list decoding has at most `listSize` candidates (`card_candidates_le`);
* for a STARK whose candidate traces and permutation traces all fail some constraint, all but few
  `α` leave few `ζ` at which the DEEP components are `(δ' - 2/N)`-near the code on a common set
  and the check passes (`exists_bad_alphas`): for `ζ` off the trace domain, the claimed values
  are those of a candidate trace, permutation trace and quotient at `δ'` (`decodingStep`),
  polynomials close to the committed words, and the check holds for few `ζ` per triple of
  candidates unless `α` is one of few bad values per candidate pair (`algebraStep`).
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop Polynomial

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

variable {lookups : List (Lookup F)}

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

/-- The batched DEEP word over a list of `m` opened words is the combination of their DEEP
components by the powers of `a`, by position. -/
theorem sum_zipIdx_deep (S : Setup EF lookups) (l : List ((S.Point → F) × 𝕂 × 𝕂)) {m : Nat}
    (hl : l.length = m) (a : 𝕂) (i : S.Point) :
    (l.zipIdx.map fun ((f, z, y), k) ↦ a ^ k * (y - algebraMap F 𝕂 (f i)) / (z - S.domain i)).sum =
      ∑ k : Fin m, a ^ (k : Nat) * (let w := l[k.val]'(hl ▸ k.isLt)
        deepComponent S w.1 w.2.1 w.2.2 i) := by
  have hmap : (fun x : ((S.Point → F) × 𝕂 × 𝕂) × Nat ↦ match x with
      | ((f, z, y), k) => a ^ k * (y - algebraMap F 𝕂 (f i)) / (z - S.domain i)) =
      fun x ↦ a ^ x.2 * (x.1.2.2 - algebraMap F 𝕂 (x.1.1 i)) / (x.1.2.1 - S.domain i) := by
    funext x
    rcases x with ⟨⟨f, z, y⟩, k⟩
    rfl
  rw [hmap, sum_zipIdx_map (fun (w : (S.Point → F) × 𝕂 × 𝕂) k ↦
    a ^ k * (w.2.2 - algebraMap F 𝕂 (w.1 i)) / (w.2.1 - S.domain i)) _ 0]
  refine Fintype.sum_equiv (finCongr hl) _ _ fun k ↦ ?_
  simp only [Nat.zero_add, deepComponent, finCongr_apply, Fin.val_cast, mul_div_assoc]
  rfl

/-- The batched DEEP word is the combination of the components by the powers of `a`. -/
theorem deepWord_eq {S : Setup EF lookups} (p : Prover S) (α ζ a : 𝕂) :
    deepWord p α ζ a = fun i ↦ ∑ k : Fin S.numOpened, a ^ (k : Nat) * components p α ζ k i :=
  funext fun i ↦ sum_zipIdx_deep S _ (length_openedWords p α ζ) a i

/-! ### `|𝕂|` -/

/-- `|𝕂|` as an extended real. -/
noncomputable abbrev card𝕂 (EF : Type) [Challenge F EF] : ENNReal := Fintype.card
    (Challenge.Spec EF)

theorem card𝕂_ne_zero : card𝕂 EF ≠ 0 := by
  simp only [card𝕂, ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true]

theorem card𝕂_ne_top : card𝕂 EF ≠ ⊤ := ENNReal.natCast_ne_top _

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

/-! ### The candidates -/

/-- The candidate polynomials of words `words` at proximity `δ`: degree at most `n`, agreeing with
the words on a common set of `(1 - δ) N` points. -/
def candidates (S : Setup EF lookups) {ι : Type} (δ : ℝ) (words : ι → S.Point → F) :
    Set (ι → F[X]) :=
  {polys | (∀ k, (polys k).natDegree ≤ S.n) ∧ Agree S δ words polys}

theorem candidates_finite (S : Setup EF lookups) {ι : Type} [Fintype ι] (δ : ℝ)
    (words : ι → S.Point → F) : (candidates S δ words).Finite := by
  classical
  refine Set.Finite.of_finite_image (f := fun polys k (i : Fin (S.n + 1)) ↦ (polys k).coeff i)
    (Set.toFinite _) fun P hP Q hQ h ↦ funext fun k ↦ Polynomial.ext fun m ↦ ?_
  by_cases hm : m ≤ S.n
  · exact congrFun (congrFun h k) ⟨m, Nat.lt_succ_of_le hm⟩
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hP.1 k) (Nat.lt_of_not_le hm)),
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hQ.1 k) (Nat.lt_of_not_le hm))]

theorem card_candidates_le (S : Setup EF lookups) {ι : Type} [Fintype ι] [DecidableEq ι] (δ : ℝ)
    (words : ι → S.Point → F) :
    (candidates_finite S δ words).toFinset.card ≤ S.listSize ι δ := by
  rw [← Set.ncard_eq_toFinset_card _ (candidates_finite S δ words)]
  exact Finset.le_sup (f := fun words : ι → S.Point → F ↦
    {polys : ι → F[X] | (∀ k, (polys k).natDegree ≤ S.n) ∧ Agree S δ words polys}.ncard)
    (Finset.mem_univ words)

/-- The candidate permutation traces number at most `permListSize`: without lookups, the one
empty tuple. -/
theorem card_permCandidates_le (S : Setup EF lookups) (δ : ℝ)
    (words : Fin S.permWidth × Fin (Challenge.d EF) → S.Point → F) :
    (candidates_finite S δ words).toFinset.card ≤ S.permListSize δ := by
  cases lookups with
  | nil =>
    refine Finset.card_le_one.mpr fun P _ Q _ ↦ funext fun ce ↦ ?_
    exact absurd ce.1.isLt (Nat.not_lt_zero _)
  | cons l ls => exact card_candidates_le S δ words

/-! ### Few `ζ` pass with near components -/

section Counting
variable {S : Setup EF lookups} (publicValues : List F) (challenges : List (Challenge.Spec EF))
  (terminal : Challenge.Spec EF)
  (p : Prover S)

open Classical

-- The constructor-name linter exhausts its recursion budget on this proof's locals.
set_option linter.constructorNameAsVariable false in
/-- The points on the trace domain number at most `n`. -/
theorem card_not_offTraceDomain (S : Setup EF lookups) :
    (Finset.univ.filter fun ζ : 𝕂 ↦ ¬ OffTraceDomain S ζ).card ≤ S.n := by
  classical
  have hsub : (Finset.univ.filter fun ζ : 𝕂 ↦ ¬ OffTraceDomain S ζ) ⊆
      (nthRoots S.n (1 : 𝕂)).toFinset := by
    intro ζ hζ
    simp only [OffTraceDomain, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hζ
    rw [Multiset.mem_toFinset, mem_nthRoots (Nat.two_pow_pos S.logN)]
    exact hζ
  exact (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans (card_nthRoots _ _))

/-- The candidate triples of trace, permutation trace and quotient polynomials of the prover's
words at `δ` after `α`. -/
noncomputable def candidateTriples (δ : ℝ) (α : 𝕂) :
    Finset ((Fin S.air.width → F[X]) × (Fin S.permWidth × Fin (Challenge.d EF) → F[X]) ×
      (Fin S.chunks × Fin (Challenge.d EF) → F[X])) :=
  (candidates_finite S δ p.trace).toFinset ×ˢ
    ((candidates_finite S δ fun ce : Fin S.permWidth × Fin (Challenge.d EF) ↦
      p.perm ce.1 ce.2).toFinset ×ˢ
    (candidates_finite S δ fun ce : Fin S.chunks × Fin (Challenge.d EF) ↦
      p.quotient α ce.1 ce.2).toFinset)

-- The constructor-name linter exhausts its recursion budget on this proof's locals.
set_option linter.constructorNameAsVariable false in
/-- The `ζ` where the components are near on a common set at `δ - 2/N` and the check passes: on
the trace domain, or the check passes with the true values of a candidate trace, permutation
trace and quotient at `δ`. -/
theorem card_near_check_le (δ : NNReal) (hδ : (δ : ℝ) < 1 - S.rate) (α : 𝕂) :
    (Finset.univ.filter fun ζ : 𝕂 ↦ NearTogether S ((δ : ℝ) - 2 / S.size) (components p α ζ) ∧
        ConstraintsHoldAt S publicValues α ζ (p.openings α ζ) challenges terminal).card ≤
      S.n + ∑ PRQ ∈ candidateTriples p δ α,
        (Finset.univ.filter fun ζ : 𝕂 ↦ OffTraceDomain S ζ ∧
          ConstraintsHoldAt S publicValues α ζ
            (trueOpenings S PRQ.1 (fun c e ↦ PRQ.2.2 (c, e)) ζ (fun c e ↦ PRQ.2.1 (c, e)))
            challenges terminal).card := by
  set check : (Fin S.air.width → F[X]) × (Fin S.permWidth × Fin (Challenge.d EF) → F[X]) ×
      (Fin S.chunks × Fin (Challenge.d EF) → F[X]) → Finset 𝕂 :=
    fun PRQ ↦ Finset.univ.filter fun ζ : 𝕂 ↦ OffTraceDomain S ζ ∧
      ConstraintsHoldAt S publicValues α ζ
        (trueOpenings S PRQ.1 (fun c e ↦ PRQ.2.2 (c, e)) ζ (fun c e ↦ PRQ.2.1 (c, e)))
        challenges terminal
  have hsub : (Finset.univ.filter fun ζ : 𝕂 ↦
        NearTogether S ((δ : ℝ) - 2 / S.size) (components p α ζ) ∧
        ConstraintsHoldAt S publicValues α ζ (p.openings α ζ) challenges terminal) ⊆
      (Finset.univ.filter fun ζ : 𝕂 ↦ ¬ OffTraceDomain S ζ) ∪
        (candidateTriples p δ α).biUnion check := by
    intro ζ hζ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion]
    by_cases hb : OffTraceDomain S ζ
    · right
      obtain ⟨tr, qu, pm, htd, hta, hqd, hqa, hpd, hpa, ho⟩ := decodingStep S δ hδ p α ζ hb hζ.1
      refine ⟨(tr, fun ce ↦ pm ce.1 ce.2, fun ce ↦ qu ce.1 ce.2), ?_, ?_⟩
      · simp only [candidateTriples, Finset.mem_product, Set.Finite.mem_toFinset]
        exact ⟨⟨htd, hta⟩, ⟨fun ce ↦ hpd ce.1 ce.2, hpa⟩, ⟨fun ce ↦ hqd ce.1 ce.2, hqa⟩⟩
      · simp only [check, Finset.mem_filter, Finset.mem_univ, true_and]
        have h := hζ.2
        rw [ho] at h
        exact ⟨hb, h⟩
    · exact Or.inl hb
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  exact Nat.add_le_add (card_not_offTraceDomain S) Finset.card_biUnion_le

-- The constructor-name linter exhausts its recursion budget on this proof's locals.
set_option linter.constructorNameAsVariable false in
/-- If every candidate trace and permutation trace at `δ'` fail some constraint (`Holds`), then
for all but `ℓT ℓP (#constraints - 1)` values of `α`, the components are near on a common set at
`δ' - 2/N` and the check passes for at most `n + ℓT ℓP ℓQ identityDegree` values of `ζ`. -/
theorem exists_bad_alphas (δ' : NNReal) (hδ' : (δ' : ℝ) < 1 - S.rate)
    (hfail : ∀ P ∈ candidates S δ' p.trace, ∀ R ∈ candidates S δ'
      (fun ce : Fin S.permWidth × Fin (Challenge.d EF) ↦ p.perm ce.1 ce.2),
      ¬ Holds S publicValues challenges terminal (traceOf S P) fun c e ↦ R (c, e)) :
    ∃ bad : Finset 𝕂,
      bad.card ≤ S.listSize (Fin S.air.width) δ' * S.permListSize δ' * (S.numConstraints - 1) ∧
      ∀ α ∉ bad, (Finset.univ.filter fun ζ : 𝕂 ↦
        NearTogether S ((δ' : ℝ) - 2 / S.size) (components p α ζ) ∧
          ConstraintsHoldAt S publicValues α ζ (p.openings α ζ) challenges terminal).card ≤
        S.n + S.listSize (Fin S.air.width) δ' * S.permListSize δ' *
          S.listSize (Fin S.chunks × Fin (Challenge.d EF)) δ' * S.identityDegree := by
  set C1 := (candidates_finite S δ' p.trace).toFinset
  set C2 := (candidates_finite S δ' fun ce : Fin S.permWidth × Fin (Challenge.d EF) ↦
    p.perm ce.1 ce.2).toFinset
  set D := S.identityDegree
  -- Every candidate pair fails a constraint, so it has few bad `α`.
  have hbadP : ∀ PR ∈ C1 ×ˢ C2, ∃ bad : Finset 𝕂, bad.card ≤ S.numConstraints - 1 ∧
      ∀ α ∉ bad, ∀ quotient : Fin S.chunks → Fin (Challenge.d EF) → F[X],
        (∀ c e, (quotient c e).natDegree ≤ S.n) →
        (Finset.univ.filter fun ζ : 𝕂 ↦ OffTraceDomain S ζ ∧
          ConstraintsHoldAt S publicValues α ζ (trueOpenings S PR.1 quotient ζ
            fun c e ↦ PR.2 (c, e)) challenges terminal).card ≤ D := by
    intro PR hPR
    rw [Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hPR
    exact algebraStep S publicValues challenges terminal PR.1 (fun c e ↦ PR.2 (c, e)) hPR.1.1
      (fun c e ↦ hPR.2.1 (c, e)) (hfail PR.1 hPR.1 PR.2 hPR.2)
  choose! badOf hbadOf hgoodOf using hbadP
  refine ⟨(C1 ×ˢ C2).biUnion badOf, Finset.card_biUnion_le.trans ((Finset.sum_le_sum fun PR hPR ↦
    hbadOf PR hPR).trans ?_), fun α hα ↦ (card_near_check_le publicValues challenges terminal p δ'
      hδ' α).trans (Nat.add_le_add_left ?_ _)⟩
  · rw [Finset.sum_const, smul_eq_mul, Finset.card_product]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (card_candidates_le S δ' p.trace)
      (card_permCandidates_le S δ' _))
  set C3 := (candidates_finite S δ' fun ce : Fin S.chunks × Fin (Challenge.d EF) ↦
    p.quotient α ce.1 ce.2).toFinset
  calc ∑ PRQ ∈ candidateTriples p δ' α, (Finset.univ.filter fun ζ : 𝕂 ↦ OffTraceDomain S ζ ∧
        ConstraintsHoldAt S publicValues α ζ
          (trueOpenings S PRQ.1 (fun c e ↦ PRQ.2.2 (c, e)) ζ (fun c e ↦ PRQ.2.1 (c, e)))
          challenges terminal).card
      ≤ ∑ PRQ ∈ candidateTriples p δ' α, D := by
        refine Finset.sum_le_sum fun PRQ hPRQ ↦ ?_
        simp only [candidateTriples, Finset.mem_product] at hPRQ
        have hαP : α ∉ badOf (PRQ.1, PRQ.2.1) := fun h ↦ hα (Finset.mem_biUnion.mpr
          ⟨(PRQ.1, PRQ.2.1), Finset.mem_product.mpr ⟨hPRQ.1, hPRQ.2.1⟩, h⟩)
        have hQ := hPRQ.2.2
        rw [Set.Finite.mem_toFinset] at hQ
        exact hgoodOf (PRQ.1, PRQ.2.1) (Finset.mem_product.mpr ⟨hPRQ.1, hPRQ.2.1⟩) α hαP _
          fun c e ↦ hQ.1 (c, e)
    _ = C1.card * C2.card * C3.card * D := by
        rw [Finset.sum_const, smul_eq_mul, candidateTriples, Finset.card_product,
          Finset.card_product]
        ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul
        (card_candidates_le S δ' _) (card_permCandidates_le S δ' _)) (card_candidates_le S δ' _))

end Counting

end CompStark.Sound
