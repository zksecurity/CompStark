/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Assembly
public import CompStark.Sound.Fri
public import CompStark.Sound.Batching
public import CompStark.Sound.Decoding
public import CompStark.Sound.Algebra
public import CompStark.Sound.Sampling
public import CompStark.Sound.ConsistentQueries

/-! # Round-by-round soundness of the STARK

The interactive knowledge-soundness proof (`Sound/Assembly.lean`) averages over the challenges;
its ingredients are per round. Here they are bad events on transcript prefixes, each bounded for
every prefix by its error in `CompStark/NonInteractiveError.lean`, for the non-interactive proof,
where every round is one random-oracle answer:

* `α` (`AlphaBad`): a candidate trace failing the AIR has a quotient passing the check at more
  than `identityDegree` points; `foldingError`.
* `ζ` (`ZetaBad`): `α` is safe, and `ζ` lies on the trace domain or passes the check for a
  failing candidate trace and a candidate quotient; `outOfDomainError`.
* `a` (`BatchBad`): the DEEP components are not near the code together, the batched word is;
  `batchingError`.
* FRI fold `i` (`FoldBad`): ArkLib's lossy folding failure of committed word `i` at `β_i`;
  `friFoldError`.
* The queries (`QueryBad`): the DEEP word is far, the folds are safe, and every query lands where
  the checks pass and the recommitted word `f₀'` agrees with the DEEP word
  (`Transcript.consistentQueries`); `friQueryError`.

The grinding samples of the FRI rounds come in the same answer as their challenges and multiply
the bounds by `powFraction` (`prob_foldRound_le`, `prob_queryBad_le`); so do those of `ζ` and `a`
(`Ni/RoundBounds.lean`).

The terminal lemma `exists_satisfied_of_safe` is deterministic: if the verifier's checks pass on a
transcript whose rounds are all safe, some candidate trace satisfies the AIR. Safe `α` and `ζ`
put `ζ` off the trace domain and leave no failing candidate pair passing the check, so the DEEP
components are not near together (`DecodingStep`); safe `a` makes the DEEP word far; safe folds
are ArkLib's `SafeHistory`; and then not every query can pass.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop Polynomial OracleComp Fri.Spec

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### FRI's schedule -/

namespace Setup
variable (S : Iop.Setup EF)

theorem foldArities_ne_nil : S.foldArities ≠ [] := by
  obtain ⟨f, fs, h⟩ := folds_cons S.params.maxLogArity (S.logN - S.params.logFinalPolyLen)
    (by have := S.folds; omega)
  rw [Iop.Setup.foldArities, h]
  exact List.cons_ne_nil _ _

/-- The schedule's arities sum to the halvings, `logN - logFinalPolyLen`. -/
theorem sum_schedule :
    ∑ j, (S.schedule j).val = S.logN - S.params.logFinalPolyLen := by
  have hsum := sum_folds S.params.maxLogArity (S.logN - S.params.logFinalPolyLen)
  rw [← Iop.Setup.foldArities] at hsum
  rw [← hsum]
  have hne := foldArities_ne_nil S
  unfold Iop.Setup.schedule Iop.Setup.lastFold
  generalize S.foldArities = l at *
  match l with
  | [] => exact absurd rfl hne
  | f :: fs =>
    rw [← Fin.sum_univ_fun_getElem (f :: fs) PNat.val]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [List.getD_eq_getElem]

end Setup

/-- FRI's final degree bound: the final polynomial has degree below `2 ^ logFinalPolyLen`. -/
abbrev finalDegreeOf (S : Iop.Setup EF) : ℕ+ := finalDegree S.params.logFinalPolyLen

theorem schedule_le (S : Iop.Setup EF) :
    ∑ j, (S.schedule j).val ≤ S.logN + S.params.logBlowup := by
  rw [Setup.sum_schedule]
  omega

/-- ArkLib's code of the folding schedule is `S.code`: degree below `n`. -/
theorem schedule_degree (S : Iop.Setup EF) :
    2 ^ (∑ j, (S.schedule j).val) * (finalDegreeOf S).val = S.n := by
  have hlt := S.folds
  rw [Setup.sum_schedule, finalDegreeOf, finalDegree, PNat.mk_coe, ← pow_add,
    Nat.sub_add_cancel hlt.le]

/-- A word not `δ`-near `S.code` is at relative distance at least `δ` from ArkLib's code. -/
theorem le_relHammingDist_of_not_near (S : Iop.Setup EF) (δ : ℝ) (w : S.Point → 𝕂)
    (hw : ¬ Near S δ w) :
    ∀ u ∈ ReedSolomon.code S.domain (2 ^ (∑ j, (S.schedule j).val) * (finalDegreeOf S).val),
      δ ≤ (Code.relHammingDist w u : ℝ) := by
  intro u hu
  rw [schedule_degree] at hu
  exact le_of_not_gt fun h ↦ hw (near_of_relHammingDist_lt S δ w u hu h)

/-! ### The transcript -/

/-- The prover with fixed words and messages. -/
def fixedProver {S : Iop.Setup EF} (trace : Fin S.air.width → S.Point → F)
    (quotient : Fin S.chunks → Fin (Challenge.d EF) → S.Point → F) (openings : Openings S)
    : Prover S :=
  ⟨trace, fun _ ↦ quotient, fun _ _ ↦ openings⟩

/-- The transcript of the interactive oracle proof, as the extractor reads it off a
non-interactive proof: the prover's words and messages, and the challenges. -/
structure Transcript (S : Iop.Setup EF) where
  trace : Fin S.air.width → S.Point → F
  alpha : 𝕂
  quotient : Fin S.chunks → Fin (Challenge.d EF) → S.Point → F
  zeta : 𝕂
  openings : Openings S
  batch : 𝕂
  /-- FRI's committed words, the recommitted batched word `f₀'` first, and its final polynomial,
  as ArkLib's oracles. -/
  fri : ∀ j, FinalOracleStatement S.schedule S.domain j
  /-- The folding challenges `β_i`. -/
  betas : FinalStatement 𝕂 S.lastFold

namespace Transcript
variable {S : Iop.Setup EF} (t : Transcript S)

/-- The transcript's prover. -/
def prover : Prover S := fixedProver t.trace t.quotient t.openings

/-- The batched DEEP word of the transcript. -/
noncomputable def deepWord : S.Point → 𝕂 := Iop.deepWord t.prover t.alpha t.zeta t.batch

/-- The points where FRI's query checks pass and `f₀'` agrees with the DEEP word. -/
noncomputable def consistentQueries : Finset S.Point :=
  Fri.Spec.consistentQueries S.schedule (schedule_le S) t.fri t.betas t.deepWord

end Transcript

/-! ### The bad events -/

section Events
variable (S : Iop.Setup EF) (publicValues : List F)

open Classical

/-- `α` is bad for a candidate trace `P`: with some quotient of degree at most `n`, the check
passes with the true values at more than `identityDegree` points `ζ` off the trace domain. -/
def AlphaBadFor (P : Fin S.air.width → F[X]) (α : 𝕂) : Prop :=
  ∃ quotient : Fin S.chunks → Fin (Challenge.d EF) → F[X], (∀ c e, (quotient c e).natDegree ≤ S.n) ∧
    S.identityDegree < (Finset.univ.filter fun ζ : 𝕂 ↦ OffTraceDomain S ζ ∧
      ConstraintsHoldAt S publicValues α ζ (trueOpenings S P quotient ζ)).card

/-- Round `α`: `α` is bad for a candidate trace that fails the AIR. -/
def AlphaBad (δ' : ℝ) (trace : Fin S.air.width → S.Point → F) (α : 𝕂) : Prop :=
  ∃ P ∈ candidates S δ' trace, ¬ S.air.Satisfied S.logN (traceOf S P) publicValues ∧
    AlphaBadFor S publicValues P α

/-- Round `ζ`: `α` is safe, and `ζ` lies on the trace domain or the check passes at `ζ` with the
true values of a candidate trace failing the AIR and a candidate quotient. -/
def ZetaBad (δ' : ℝ) (trace : Fin S.air.width → S.Point → F) (α : 𝕂)
    (quotient : Fin S.chunks → Fin (Challenge.d EF) → S.Point → F) (ζ : 𝕂) : Prop :=
  ¬ AlphaBad S publicValues δ' trace α ∧ (¬ OffTraceDomain S ζ ∨
    ∃ P ∈ candidates S δ' trace, ¬ S.air.Satisfied S.logN (traceOf S P) publicValues ∧
      ∃ Q ∈ candidates S δ' (fun ce : Fin S.chunks × Fin (Challenge.d EF) ↦ quotient ce.1 ce.2),
        ConstraintsHoldAt S publicValues α ζ (trueOpenings S P (fun c e ↦ Q (c, e)) ζ))

/-- Round `a`: the DEEP components are not near the code together at `δ' - 2/N`, but their
batched word is `δ`-near. -/
def BatchBad (δ : NNReal) (δ' : ℝ) (trace : Fin S.air.width → S.Point → F) (α : 𝕂)
    (quotient : Fin S.chunks → Fin (Challenge.d EF) → S.Point → F) (ζ : 𝕂) (openings : Openings S)
    (a : 𝕂) :
    Prop :=
  ¬ NearTogether S (δ' - 2 / S.size) (components (fixedProver trace quotient openings) α ζ) ∧
    Near S δ (Iop.deepWord (fixedProver trace quotient openings) α ζ a)

/-- FRI fold `i`: ArkLib's lossy folding failure of committed word `i` at `β`. The safe history
of ArkLib's query analysis (`SafeHistory`) is that no fold is bad. -/
def FoldBad (δ loss : NNReal) (i : Fin (S.lastFold + 1))
    (fri : ∀ j, FinalOracleStatement S.schedule S.domain j) (β : 𝕂) : Prop :=
  Fri.LossyFoldingAgreementFailure (S.domain.subdomain (foldingPrefix S.schedule i.castSucc))
    (fun z ↦ committedFunction S.schedule fri i.castSucc
      (S.domain.subdomain (foldingPrefix S.schedule i.castSucc) z))
    (S.schedule i).val (foldingDegree S.schedule (finalDegreeOf S) i.succ) δ loss β

/-- The point of `L` that a query sample selects: the low `log N` bits of its canonical value, the
index into `L` in bit-reversed order. -/
def queryPoint (x : F) : S.Point :=
  ⟨reverseBits (CompPoly.CanonicalNat.toNat x % 2 ^ (S.logN + S.params.logBlowup))
      (S.logN + S.params.logBlowup),
    reverseBits_lt _ _⟩

/-- Before the queries: the DEEP word is `δ`-far, no fold is bad and the final polynomial has
degree below `2 ^ logFinalPolyLen`. -/
def QueryReady (δ loss : NNReal) (t : Transcript S) : Prop :=
  ¬ Near S δ t.deepWord ∧ SafeHistory S.schedule (finalDegreeOf S) t.fri t.betas δ loss ∧
    (finalPolynomial S.schedule t.fri).natDegree < (finalDegreeOf S).val

/-- The query round: ready, the grinding sample `pow` has `queryPowBits` vanishing low bits, and
every query sample selects a point where the checks pass and `f₀'` agrees with the DEEP word. -/
def QueryBad (δ loss : NNReal) (t : Transcript S) (pow : F)
    (queries : Fin S.params.numQueries → F) : Prop :=
  QueryReady S δ loss t ∧ CompPoly.CanonicalNat.toNat pow % 2 ^ S.params.queryPowBits = 0 ∧
    ∀ j, queryPoint S (queries j) ∈ t.consistentQueries

/-- The folds of a transcript are safe in ArkLib's sense when none is bad. -/
theorem safeHistory_iff (δ loss : NNReal) (t : Transcript S) :
    SafeHistory S.schedule (finalDegreeOf S) t.fri t.betas δ loss ↔
      ∀ i, ¬ FoldBad S δ loss i t.fri (t.betas i) := Iff.rfl

/-- Fold `i`'s bad event reads only committed word `i`. -/
theorem foldBad_congr (δ loss : NNReal) (i : Fin (S.lastFold + 1))
    {fri fri' : ∀ j, FinalOracleStatement S.schedule S.domain j}
    (h : committedWord S.schedule fri i = committedWord S.schedule fri' i) (β : 𝕂) :
    FoldBad S δ loss i fri β ↔ FoldBad S δ loss i fri' β := by
  have hf : ∀ x, committedFunction S.schedule fri i.castSucc x =
      committedFunction S.schedule fri' i.castSucc x := by
    intro x
    simp only [committedFunction, Fin.val_castSucc, i.isLt, ↓reduceDIte, Fin.eta, h]
  simp only [FoldBad, hf]

end Events

/-! ### The bounds -/

section Bounds
variable (S : Iop.Setup EF) (publicValues : List F)

open Classical

-- The constructor-name linter exhausts its recursion budget on this proof's locals.
set_option linter.constructorNameAsVariable false in
/-- The `α` bad for a failing candidate trace number at most `#constraints - 1`. -/
theorem card_alphaBadFor_le (P : Fin S.air.width → F[X]) (hP : ∀ j, (P j).natDegree ≤ S.n)
    (hfail : ¬ S.air.Satisfied S.logN (traceOf S P) publicValues) :
    (Finset.univ.filter fun α : 𝕂 ↦ AlphaBadFor S publicValues P α).card ≤
      S.air.constraints.length - 1 := by
  obtain ⟨bad, hcard, hgood⟩ := algebraStep S publicValues P hP hfail
  refine (Finset.card_le_card fun α hα ↦ ?_).trans hcard
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα
  by_contra hb
  obtain ⟨Q, hQ, hlt⟩ := hα
  exact absurd (hgood α hb Q hQ) (not_le.mpr hlt)

-- The constructor-name linter exhausts its recursion budget on this proof's locals.
set_option linter.constructorNameAsVariable false in
/-- Round `α`: at most `ℓT (#constraints - 1)` bad values. -/
theorem card_alphaBad_le (δ' : NNReal) (trace : Fin S.air.width → S.Point → F) :
    (Finset.univ.filter fun α : 𝕂 ↦ AlphaBad S publicValues δ' trace α).card ≤
      S.listSize (Fin S.air.width) δ' * (S.air.constraints.length - 1) := by
  set C := (candidates_finite S δ' trace).toFinset
  have hsub : (Finset.univ.filter fun α : 𝕂 ↦ AlphaBad S publicValues δ' trace α) ⊆
      (C.filter fun P ↦ ¬ S.air.Satisfied S.logN (traceOf S P) publicValues).biUnion
        fun P ↦ Finset.univ.filter fun α : 𝕂 ↦ AlphaBadFor S publicValues P α := by
    intro α hα
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα
    obtain ⟨P, hP, hfail, hbad⟩ := hα
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, C,
      Set.Finite.mem_toFinset]
    exact ⟨P, ⟨hP, hfail⟩, hbad⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  refine (Finset.sum_le_sum (g := fun _ ↦ S.air.constraints.length - 1) fun P hP ↦ ?_).trans ?_
  · simp only [Finset.mem_filter, C, Set.Finite.mem_toFinset] at hP
    exact card_alphaBadFor_le S publicValues P hP.1.1 hP.2
  · rw [Finset.sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans (card_candidates_le S δ' _))

/-- Round `α`: a uniform `α` is bad with probability at most `foldingError`. -/
theorem prob_alphaBad_le (δ' : NNReal) (trace : Fin S.air.width → S.Point → F) :
    Pr{let α ← $ᵗ 𝕂}[AlphaBad S publicValues δ' trace α] ≤ foldingError S δ' := by
  rw [SampleableType.prEvent_uniformSample, Iop.foldingError]
  gcongr
  exact_mod_cast card_alphaBad_le S publicValues δ' trace

-- The constructor-name linter exhausts its recursion budget on this proof's locals.
set_option linter.constructorNameAsVariable false in
/-- Round `ζ`: at most `ℓT ℓQ identityDegree + n` bad values. -/
theorem card_zetaBad_le (δ' : NNReal) (trace : Fin S.air.width → S.Point → F) (α : 𝕂)
    (quotient : Fin S.chunks → Fin (Challenge.d EF) → S.Point → F) :
    (Finset.univ.filter fun ζ : 𝕂 ↦ ZetaBad S publicValues δ' trace α quotient ζ).card ≤
      S.listSize (Fin S.air.width) δ' * S.listSize (Fin S.chunks × Fin (Challenge.d EF)) δ' *
        S.identityDegree + S.n := by
  by_cases hα : AlphaBad S publicValues δ' trace α
  · have h : (Finset.univ.filter fun ζ : 𝕂 ↦ ZetaBad S publicValues δ' trace α quotient ζ) = ∅ :=
      Finset.filter_false_of_mem fun ζ _ hζ ↦ hζ.1 hα
    rw [h, Finset.card_empty]
    exact Nat.zero_le _
  set C1 := ((candidates_finite S δ' trace).toFinset.filter
    fun P ↦ ¬ S.air.Satisfied S.logN (traceOf S P) publicValues)
  set C2 := (candidates_finite S δ' fun ce : Fin S.chunks × Fin (Challenge.d EF) ↦
    quotient ce.1 ce.2).toFinset
  set check : (Fin S.air.width → F[X]) → (Fin S.chunks × Fin (Challenge.d EF) → F[X]) → Finset 𝕂 :=
    fun P Q ↦ Finset.univ.filter fun ζ : 𝕂 ↦ OffTraceDomain S ζ ∧
      ConstraintsHoldAt S publicValues α ζ (trueOpenings S P (fun c e ↦ Q (c, e)) ζ)
  have hsub : (Finset.univ.filter fun ζ : 𝕂 ↦ ZetaBad S publicValues δ' trace α quotient ζ) ⊆
      (C1.biUnion fun P ↦ C2.biUnion fun Q ↦ check P Q) ∪
        Finset.univ.filter fun ζ : 𝕂 ↦ ¬ OffTraceDomain S ζ := by
    intro ζ hζ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ
    obtain ⟨-, hζ'⟩ := hζ
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
      true_and, check, C1, C2, Set.Finite.mem_toFinset]
    by_cases hoff : OffTraceDomain S ζ
    · left
      rcases hζ' with h | ⟨P, hP, hfail, Q, hQ, hcheck⟩
      · exact absurd hoff h
      · exact ⟨P, ⟨hP, hfail⟩, Q, hQ, hoff, hcheck⟩
    · exact Or.inr hoff
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add ?_ (card_not_offTraceDomain S)))
  refine Finset.card_biUnion_le.trans ((Finset.sum_le_sum fun P hP ↦
    Finset.card_biUnion_le.trans (Finset.sum_le_sum (g := fun _ ↦ S.identityDegree)
      fun Q hQ ↦ ?_)).trans ?_)
  · simp only [C1, Finset.mem_filter, Set.Finite.mem_toFinset] at hP
    simp only [C2, Set.Finite.mem_toFinset] at hQ
    by_contra hlt
    exact hα ⟨P, hP.1, hP.2, fun c e ↦ Q (c, e), fun c e ↦ hQ.1 (c, e), not_le.mp hlt⟩
  · rw [Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, ← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul
      ((Finset.card_filter_le _ _).trans (card_candidates_le S δ' _))
      (card_candidates_le S δ' _))

/-- Round `ζ`: a uniform `ζ` is bad with probability at most `outOfDomainError`. -/
theorem prob_zetaBad_le (δ' : NNReal) (trace : Fin S.air.width → S.Point → F) (α : 𝕂)
    (quotient : Fin S.chunks → Fin (Challenge.d EF) → S.Point → F) :
    Pr{let ζ ← $ᵗ 𝕂}[ZetaBad S publicValues δ' trace α quotient ζ] ≤ outOfDomainError S δ' := by
  rw [SampleableType.prEvent_uniformSample, outOfDomainError]
  gcongr
  exact_mod_cast card_zetaBad_le S publicValues δ' trace α quotient

/-- Round `a`: a uniform `a` is bad with probability at most `batchingError`. -/
theorem prob_batchBad_le (δ : NNReal) (δ' : ℝ) (trace : Fin S.air.width → S.Point → F)
    (α : 𝕂) (quotient : Fin S.chunks → Fin (Challenge.d EF) → S.Point → F) (ζ : 𝕂)
    (openings : Openings S) :
    Pr{let a ← $ᵗ 𝕂}[BatchBad S δ δ' trace α quotient ζ openings a] ≤
      batchingError S δ (δ' - 2 / S.size) := by
  rw [SampleableType.prEvent_uniformSample]
  set p := fixedProver trace quotient openings
  by_cases hfar : NearTogether S (δ' - 2 / S.size) (components p α ζ)
  · have h : (Finset.univ.filter fun a : 𝕂 ↦ BatchBad S δ δ' trace α quotient ζ openings a) = ∅ :=
      Finset.filter_false_of_mem fun a _ ha ↦ ha.1 hfar
    rw [h, Finset.card_empty, Nat.cast_zero, ENNReal.zero_div]
    exact bot_le
  have hset : (Finset.univ.filter fun a : 𝕂 ↦ BatchBad S δ δ' trace α quotient ζ openings a) =
      Finset.univ.filter fun a : 𝕂 ↦
        Near S δ fun i ↦ ∑ k : Fin S.numOpened, a ^ (k : Nat) * components p α ζ k i :=
    Finset.filter_congr fun a _ ↦ by
      rw [BatchBad, ← deepWord_eq]
      exact and_iff_right hfar
  rw [hset]
  exact batchingStep S S.numOpened δ _ _ hfar

/-- FRI fold `i`: a uniform `β` is bad with probability at most `friFoldError`, for every
committed word. -/
theorem prob_foldBad_le (δ loss : NNReal) (i : Fin (S.lastFold + 1))
    (fri : ∀ j, FinalOracleStatement S.schedule S.domain j) :
    Pr{let β ← $ᵗ 𝕂}[FoldBad S δ loss i fri β] ≤ friFoldError S δ loss i := by
  unfold FoldBad friFoldError foldingErrorLossy
  rw [ENNReal.coe_toNNReal (CoreDefinitions.lossyMcaError_ne_top _ _ _ _)]
  exact Fri.lossyFoldingAgreementFailure_prob_le_powers _ _
    (foldingDegree_pos S.schedule (finalDegreeOf S) i.succ) _ _

/-- FRI fold `i` with its grinding sample, drawn in the same answer: at most
`powFraction commitPowBits · friFoldError`. -/
theorem prob_foldRound_le (δ loss : NNReal) (i : Fin (S.lastFold + 1))
    (fri : ∀ j, FinalOracleStatement S.schedule S.domain j) :
    Pr{let z ← $ᵗ (F × 𝕂)}[CompPoly.CanonicalNat.toNat z.1 % 2 ^ S.params.commitPowBits = 0 ∧
      FoldBad S δ loss i fri z.2] ≤
      powFraction F S.params.commitPowBits * friFoldError S δ loss i := by
  exact (prob_pow_and_le _ _).trans (mul_le_mul_right (prob_foldBad_le S δ loss i fri) _)

/-- The query samples that select a point of `G` are those whose residues lie in the
bit-reversed `G`, a set of the same size. -/
theorem queryPoint_mem_iff (G : Finset S.Point) (x : F) :
    queryPoint S x ∈ G ↔ CompPoly.CanonicalNat.toNat x % 2 ^ (S.logN + S.params.logBlowup) ∈
      G.image fun z ↦ reverseBits z.val (S.logN + S.params.logBlowup) := by
  set m := S.logN + S.params.logBlowup
  have hlt : CompPoly.CanonicalNat.toNat x % 2 ^ m < 2 ^ m := Nat.mod_lt _ (Nat.two_pow_pos m)
  simp only [Finset.mem_image]
  constructor
  · intro h
    exact ⟨_, h, reverseBits_reverseBits hlt⟩
  · rintro ⟨z, hz, hzx⟩
    have hz' : queryPoint S x = z := by
      apply Fin.ext
      simp only [queryPoint, ← hzx, reverseBits_reverseBits z.isLt]
    rw [hz']
    exact hz

/-- The query round: at most `powFraction queryPowBits · friQueryError`. -/
theorem prob_queryBad_le (δ loss : NNReal) (t : Transcript S) :
    Pr{let z ← $ᵗ (F × (Fin S.params.numQueries → F))}[QueryBad S δ loss t z.1 z.2] ≤
      powFraction F S.params.queryPowBits * friQueryError S δ loss := by
  by_cases hready : QueryReady S δ loss t
  · set m := S.logN + S.params.logBlowup
    set G := t.consistentQueries.image fun z ↦ reverseBits z.val m
    have hdens := consistentQueries_density_le S.schedule (finalDegreeOf S) (schedule_le S)
      t.fri t.betas t.deepWord δ δ loss loss.coe_nonneg hready.2.1 hready.2.2
      (le_relHammingDist_of_not_near S δ t.deepWord hready.1)
    have hG : (G.card : ℝ) ≤ 2 ^ m *
        (1 - min ((δ : ℝ) - S.lastFold * loss) ((δ : ℝ) - (S.lastFold + 1) * loss)) := by
      have hpos : (0 : ℝ) < 2 ^ m := by positivity
      rw [div_le_iff₀ hpos] at hdens
      have hcard : (G.card : ℝ) ≤ (Fri.Spec.consistentQueries S.schedule (schedule_le S) t.fri
          t.betas t.deepWord).card := by
        exact_mod_cast Finset.card_image_le
      change (G.card : ℝ) ≤ _
      linarith
    have h := prob_queryRound_le S.params.queryPowBits m S.params.numQueries
      (BaseField.two_pow_dvd_card_sub_one_of_le S.valid.twoAdic) G _ hG
    refine le_trans (le_of_eq ?_) h
    congr 1
    funext z
    simp only [QueryBad, hready, true_and, queryPoint_mem_iff, G, m, Transcript.consistentQueries]
  · rw [SampleableType.prEvent_uniformSample]
    have h : (Finset.univ.filter fun z : F × (Fin S.params.numQueries → F) ↦
        QueryBad S δ loss t z.1 z.2) = ∅ :=
      Finset.filter_false_of_mem fun z _ hz ↦ hready hz.1
    rw [h, Finset.card_empty, Nat.cast_zero, ENNReal.zero_div]
    exact bot_le

end Bounds

/-! ### The terminal lemma -/

section Terminal
variable (S : Iop.Setup EF) (publicValues : List F)

/-- If every candidate trace fails the AIR, the check passes at `ζ` and the rounds `α`, `ζ`, `a`
are safe, the DEEP word is `δ`-far from the code. -/
theorem not_near_deepWord (δ δ' : NNReal) (hδ' : (δ' : ℝ) < 1 - S.rate) (t : Transcript S)
    (hfail : ∀ P ∈ candidates S δ' t.trace,
      ¬ S.air.Satisfied S.logN (traceOf S P) publicValues)
    (hcheck : ConstraintsHoldAt S publicValues t.alpha t.zeta t.openings)
    (hα : ¬ AlphaBad S publicValues δ' t.trace t.alpha)
    (hζ : ¬ ZetaBad S publicValues δ' t.trace t.alpha t.quotient t.zeta)
    (ha : ¬ BatchBad S δ δ' t.trace t.alpha t.quotient t.zeta t.openings t.batch) :
    ¬ Near S δ t.deepWord := by
  intro hnear
  have htogether : NearTogether S ((δ' : ℝ) - 2 / S.size) (components t.prover t.alpha t.zeta) :=
    not_not.mp fun h ↦ ha ⟨h, hnear⟩
  have hoff : OffTraceDomain S t.zeta := not_not.mp fun h ↦ hζ ⟨hα, Or.inl h⟩
  obtain ⟨P, Q, hPd, hPa, hQd, hQa, ho⟩ :=
    decodingStep S δ' hδ' t.prover t.alpha t.zeta hoff htogether
  refine hζ ⟨hα, Or.inr ⟨P, ⟨hPd, hPa⟩, hfail P ⟨hPd, hPa⟩, fun ce ↦ Q ce.1 ce.2,
    ⟨fun ce ↦ hQd ce.1 ce.2, hQa⟩, ?_⟩⟩
  have h : t.openings = trueOpenings S P Q t.zeta := ho
  rw [← h]
  exact hcheck

/-- **The terminal lemma.** If the verifier's checks pass on a transcript whose rounds are all
safe, some candidate trace satisfies the AIR: the check at `ζ`, a final polynomial of degree
below `2 ^ logFinalPolyLen`, a grinding sample with `queryPowBits` vanishing low bits, and every
query sample selecting a point where the checks pass and `f₀'` agrees with the DEEP word. -/
theorem exists_satisfied_of_safe (δ δ' loss : NNReal) (hδ' : (δ' : ℝ) < 1 - S.rate)
    (t : Transcript S) (pow : F) (queries : Fin S.params.numQueries → F)
    (hcheck : ConstraintsHoldAt S publicValues t.alpha t.zeta t.openings)
    (hdegree : (finalPolynomial S.schedule t.fri).natDegree < (finalDegreeOf S).val)
    (hpow : CompPoly.CanonicalNat.toNat pow % 2 ^ S.params.queryPowBits = 0)
    (hqueries : ∀ j, queryPoint S (queries j) ∈ t.consistentQueries)
    (hα : ¬ AlphaBad S publicValues δ' t.trace t.alpha)
    (hζ : ¬ ZetaBad S publicValues δ' t.trace t.alpha t.quotient t.zeta)
    (ha : ¬ BatchBad S δ δ' t.trace t.alpha t.quotient t.zeta t.openings t.batch)
    (hfolds : ∀ i, ¬ FoldBad S δ loss i t.fri (t.betas i))
    (hq : ¬ QueryBad S δ loss t pow queries) :
    ∃ P ∈ candidates S δ' t.trace, S.air.Satisfied S.logN (traceOf S P) publicValues := by
  by_contra hno
  have hfail : ∀ P ∈ candidates S δ' t.trace,
      ¬ S.air.Satisfied S.logN (traceOf S P) publicValues := fun P hP h ↦ hno ⟨P, hP, h⟩
  exact hq ⟨⟨not_near_deepWord S publicValues δ δ' hδ' t hfail hcheck hα hζ ha, hfolds,
    hdegree⟩, hpow, hqueries⟩

end Terminal

end CompStark.Sound
