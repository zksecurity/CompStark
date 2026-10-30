/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Fri
public import CompStark.Sound.Batching
public import CompStark.Sound.Decoding
public import CompStark.Sound.Algebra

/-! # The single-instance pieces of the round arguments

The STARK's round arguments (`Sound/Rbr.lean`) count bad challenges with these pieces:

* the batched DEEP word over a list of opened words is the combination of their DEEP components
  by the powers of `a` (`sum_zipIdx_deep`, `deepWord_eq`);
* list decoding has at most `listSize` candidates (`card_candidates_le`), and a candidate of the
  committed words as one family (`Setup.Committed`) restricts to candidates of each part
  (`committedTrace_mem_candidates`, …);
* at most `n` points lie on the trace domain and `N` on `L` (`card_not_offTraceDomain`,
  `card_not_offDomain`).
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

/-- Polynomials that agree with words on a common set agree with every subfamily on it. -/
theorem agree_comp {S : Setup EF lookups} {ι ι' : Type} {δ : ℝ} {words : ι → S.Point → F}
    {polys : ι → F[X]} (h : Agree S δ words polys) (f : ι' → ι) :
    Agree S δ (words ∘ f) (polys ∘ f) := by
  obtain ⟨T, hT, hagree⟩ := h
  exact ⟨T, hT, fun i hi k ↦ hagree i hi (f k)⟩

/-- A candidate of a family of words restricts to a candidate of every subfamily. -/
theorem comp_mem_candidates {S : Setup EF lookups} {ι ι' : Type} {δ : ℝ}
    {words : ι → S.Point → F} {polys : ι → F[X]} (h : polys ∈ candidates S δ words)
    (f : ι' → ι) : polys ∘ f ∈ candidates S δ (words ∘ f) :=
  ⟨fun k ↦ h.1 (f k), agree_comp h.2 f⟩

section Committed
variable {S : Setup EF lookups} {δ : ℝ} {trace : Fin S.air.width → S.Point → F}
  {perm : Fin S.permWidth → Fin (Challenge.d EF) → S.Point → F}
  {quotient : Fin S.chunks → Fin (Challenge.d EF) → S.Point → F} {J : S.Committed → F[X]}

/-- The trace of a candidate of the committed words is a candidate trace. -/
theorem committedTrace_mem_candidates (h : J ∈ candidates S δ (S.committed trace perm quotient)) :
    S.committedTrace J ∈ candidates S δ trace :=
  comp_mem_candidates h Sum.inl

/-- The permutation trace of a candidate of the committed words is a candidate permutation
trace. -/
theorem committedPerm_mem_candidates (h : J ∈ candidates S δ (S.committed trace perm quotient)) :
    (fun ce : Fin S.permWidth × Fin (Challenge.d EF) ↦ S.committedPerm J ce.1 ce.2) ∈
      candidates S δ fun ce ↦ perm ce.1 ce.2 :=
  comp_mem_candidates h (Sum.inr ∘ Sum.inl)

/-- Polynomials of degree at most `n` that agree with the committed words on a common set are a
candidate of them. -/
theorem committed_mem_candidates {P : Fin S.air.width → F[X]}
    {R : Fin S.permWidth → Fin (Challenge.d EF) → F[X]}
    {Q : Fin S.chunks → Fin (Challenge.d EF) → F[X]} (hP : ∀ j, (P j).natDegree ≤ S.n)
    (hR : ∀ c e, (R c e).natDegree ≤ S.n) (hQ : ∀ c e, (Q c e).natDegree ≤ S.n)
    (h : Agree S δ (S.committed trace perm quotient) (S.committed P R Q)) :
    S.committed P R Q ∈ candidates S δ (S.committed trace perm quotient) := by
  refine ⟨?_, h⟩
  rintro (j | ⟨c, e⟩ | ⟨c, e⟩)
  · exact hP j
  · exact hR c e
  · exact hQ c e

end Committed

/-! ### The points on the domains -/

section Counting

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

/-- The points on `L` number `N`. -/
theorem card_not_offDomain (S : Setup EF lookups) :
    (Finset.univ.filter fun ζ : 𝕂 ↦ ¬ OffDomain S ζ).card ≤ S.size := by
  classical
  have hsub : (Finset.univ.filter fun ζ : 𝕂 ↦ ¬ OffDomain S ζ) ⊆
      Finset.univ.image fun i : S.Point ↦ S.domain i := by
    intro ζ hζ
    simp only [OffDomain, Finset.mem_filter, Finset.mem_univ, true_and, not_forall,
      not_not] at hζ
    obtain ⟨i, hi⟩ := hζ
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  rw [Finset.card_univ, Fintype.card_fin]

end Counting

end CompStark.Sound
