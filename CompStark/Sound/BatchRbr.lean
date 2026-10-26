/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.BatchAssembly
public import CompStark.Sound.Rbr
public import CompStark.BatchNonInteractiveError

/-! # Round-by-round soundness of the batch STARK

The batch STARK's rounds as bad events on transcript prefixes, each bounded for every prefix by
its error in `CompStark/BatchNonInteractiveError.lean`, for the non-interactive proof, where every
round is one random-oracle answer. The transcript (`Batch.Transcript`) holds every instance's
words, terminals and claimed values, the challenges, and FRI's committed words and final
polynomial, which FRI folds by Plonky3's schedule from the tallest domain, injecting the batched
DEEP words of the shorter domains (`Transcript.rounds`, `Transcript.fri`).

* The lookup challenges `(α_L, β_L)` (`LookupBad`, `Sound/BatchLogUp.lean`): for some tuple of
  candidate traces satisfying every AIR but unbalanced, a message's denominator or the messages'
  sum of fractions vanishes.

The rounds of `α`, `ζ` and `a` are those of the instance that the traces, permutation traces and
terminals make fail (`Batch.failing`): one whose candidate traces and permutation traces all fail
some constraint, if there is one.

* `α` (`AlphaBad`) and `ζ` (`ZetaBad`): the STARK's events for that instance, its permutation
  trace, lookup challenges and terminal included.
* `a` (`BatchBad`): the DEEP components of the opened words of that instance's domain size are
  not near the code together, the batched word of that size is.
* FRI fold `j` (`FoldBad`): the fold of committed word `j`, with its injected word, fails
  (`FriGame.Rounds.FoldFails`).
* The queries (`QueryBad`): the tallest batched word or an injected one is far, the folds are
  safe, and every query lands where the checks pass and FRI's first word agrees with the tallest
  batched word.

The terminal lemma `exists_satisfied_of_safe` is deterministic: if the verifier's checks pass on a
transcript whose rounds are all safe, some tuple of candidate traces satisfies the batch.
Otherwise, with safe lookup challenges and terminals summing to zero, an instance fails
(`exists_failing_instance`), and as for the STARK its safe `α`, `ζ` and `a` make the batched word
of its domain size far (`not_near_deepWords`); FRI starts with that word or injects it, so with
safe folds not every query passes.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop Polynomial OracleComp FriGame FriInject

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

namespace Batch

/-! ### FRI's injected words -/

section Injected
variable {withLookups : Bool} (S : Iop.Batch.Setup EF withLookups)

/-- The shift of the domain of `2 ^ m` points that FRI's folds reach from the tallest domain
`g ⟨ω⟩`: `g ^ 2 ^ (logTop - m)`. -/
noncomputable def foldShift (m : ℕ) : 𝕂 := lift gen ^ 2 ^ (S.logTop - m)

theorem foldShift_ne_zero (m : ℕ) : foldShift S m ≠ 0 := by
  refine pow_ne_zero _ ?_
  rw [lift, ne_eq, map_eq_zero_iff _ (algebraMap F 𝕂).injective]
  exact BaseField.gen_ne_zero

/-- FRI's injected words: Plonky3 adds the batched DEEP word of the domain of `2 ^ m` points times
`β ^ 2 ^ k` to a fold by `2 ^ k` at `β`, which is ArkLib's fold at `s β`, `s` the shift of the
folded domain's square root: so ArkLib's fold injects the word divided by the folded domain's
shift. -/
noncomputable def injected (words : (m : ℕ) → Fin (2 ^ m) → 𝕂) (m : ℕ) (x : Fin (2 ^ m)) : 𝕂 :=
  (foldShift S m)⁻¹ * words m x

end Injected

/-- A word agreeing with a code after scaling by a nonzero constant agrees with it before. -/
theorem agrees_of_agrees_mul {m : ℕ} {D : Fin (2 ^ m) ↪ 𝕂} {deg : ℕ} {ρ : ℝ} {c : 𝕂}
    (hc : c ≠ 0) {w : Fin (2 ^ m) → 𝕂} (h : Agrees D deg ρ fun x ↦ c * w x) : Agrees D deg ρ w := by
  obtain ⟨T, hT, v, hv, hvT⟩ := h
  refine ⟨T, hT, c⁻¹ • v, Submodule.smul_mem _ _ hv, fun x hx ↦ ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, hvT x hx, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-! ### The transcript -/

/-- The transcript of the batch STARK, as the extractor reads it off a non-interactive proof:
every instance's words, terminals and claimed values, the challenges, and FRI's committed words,
final polynomial and folding challenges. -/
structure Transcript {withLookups : Bool} (S : Iop.Batch.Setup EF withLookups) where
  trace : (i : Fin S.k) → Fin (S.air i).width → (S.instanceSetup i).Point → F
  lookupAlpha : 𝕂
  lookupBeta : 𝕂
  perm : (i : Fin S.k) → Fin (S.instanceSetup i).permWidth → Fin (Challenge.d EF) →
    (S.instanceSetup i).Point → F
  terminal : Fin S.k → 𝕂
  alpha : 𝕂
  quotient : (i : Fin S.k) → Fin (S.instanceSetup i).chunks → Fin (Challenge.d EF) →
    (S.instanceSetup i).Point → F
  zeta : 𝕂
  openings : (i : Fin S.k) → Openings (S.instanceSetup i)
  batch : 𝕂
  /-- FRI's committed words, the batched word of the tallest domain again first: word `j`, read
  on `2 ^ m` points. -/
  words : ℕ → (m : ℕ) → Fin (2 ^ m) → 𝕂
  /-- FRI's final polynomial, in the final domain's coordinate. -/
  finalPoly : 𝕂[X]
  /-- The folding challenges, in ArkLib's coordinate. -/
  betas : ℕ → 𝕂

namespace Transcript
variable {withLookups : Bool} {S : Iop.Batch.Setup EF withLookups} (t : Transcript S)

/-- The transcript's prover. -/
def prover : Iop.Batch.Prover S :=
  ⟨t.trace, fun _ _ ↦ t.perm, fun _ _ ↦ t.terminal, fun _ _ _ ↦ t.quotient,
    fun _ _ _ _ ↦ t.openings⟩

/-- The batched DEEP words of the transcript, one per domain size. -/
noncomputable def deepWords (m : ℕ) : Fin (2 ^ m) → 𝕂 :=
  Iop.Batch.groupDeepWord t.prover t.lookupAlpha t.lookupBeta t.alpha t.zeta t.batch m

/-- FRI's rounds: Plonky3's schedule from the tallest domain, injecting the shorter domains'
batched words. -/
noncomputable def rounds : Rounds 𝕂 S.logTop :=
  S.domainSetup.friRounds (injected S t.deepWords) S.friHeights

/-- FRI's run on the committed words. -/
noncomputable def fri : InjectTrace S.domainSetup.domain
    (t.rounds.degree (2 ^ S.params.logFinalPolyLen)) :=
  Rounds.run _ (Nat.two_pow_pos _) t.words t.finalPoly t.betas S.domainSetup.domain t.rounds

open Classical in
/-- The points where FRI's query checks pass and its first word agrees with the tallest batched
word. -/
noncomputable def consistentQueries : Finset S.domainSetup.Point :=
  t.fri.accepting.filter fun x ↦ t.fri.initial x = t.deepWords S.logTop x

end Transcript

/-! ### The bad events -/

section Events
variable {withLookups : Bool} (S : Iop.Batch.Setup EF withLookups)
  (publicValues : Fin S.k → List F)

open Classical in
/-- The instance the traces, permutation traces and terminals make fail at the lookup challenges,
if one fails (`Failing`). -/
noncomputable def failing (δ' : NNReal)
    (traces : (i : Fin S.k) → Fin (S.air i).width → (S.instanceSetup i).Point → F)
    (perms : (i : Fin S.k) → Fin (S.instanceSetup i).permWidth → Fin (Challenge.d EF) →
      (S.instanceSetup i).Point → F)
    (terminals : Fin S.k → 𝕂) (lα lβ : 𝕂) : Fin S.k :=
  if h : ∃ i, Failing S publicValues δ' traces perms terminals lα lβ i then Classical.choose h
  else ⟨0, S.nonempty⟩

theorem failing_spec (δ' : NNReal)
    (traces : (i : Fin S.k) → Fin (S.air i).width → (S.instanceSetup i).Point → F)
    (perms : (i : Fin S.k) → Fin (S.instanceSetup i).permWidth → Fin (Challenge.d EF) →
      (S.instanceSetup i).Point → F)
    (terminals : Fin S.k → 𝕂) (lα lβ : 𝕂)
    (h : ∃ i, Failing S publicValues δ' traces perms terminals lα lβ i) :
    Failing S publicValues δ' traces perms terminals lα lβ
      (failing S publicValues δ' traces perms terminals lα lβ) := by
  simp only [failing, h, ↓reduceDIte]
  exact Classical.choose_spec h

variable (δ δ' loss : NNReal)
  (traces : (i : Fin S.k) → Fin (S.air i).width → (S.instanceSetup i).Point → F)
  (perms : (i : Fin S.k) → Fin (S.instanceSetup i).permWidth → Fin (Challenge.d EF) →
    (S.instanceSetup i).Point → F)
  (terminals : Fin S.k → Challenge.Spec EF) (lα lβ : Challenge.Spec EF)

/-- Round `α`: `α` is bad for the failing instance (`Sound.AlphaBad`). -/
def AlphaBad (α : 𝕂) : Prop :=
  let i := failing S publicValues δ' traces perms terminals lα lβ
  Sound.AlphaBad (S.instanceSetup i) (publicValues i) δ' (traces i) α (perms i)
    (S.challenges lα lβ i) (terminals i)

/-- Round `ζ`: `ζ` is bad for the failing instance (`Sound.ZetaBad`). -/
def ZetaBad (α : 𝕂)
    (quotients : (i : Fin S.k) → Fin (S.instanceSetup i).chunks → Fin (Challenge.d EF) →
      (S.instanceSetup i).Point → F) (ζ : 𝕂) : Prop :=
  let i := failing S publicValues δ' traces perms terminals lα lβ
  Sound.ZetaBad (S.instanceSetup i) (publicValues i) δ' (traces i) α (quotients i) ζ (perms i)
    (S.challenges lα lβ i) (terminals i)

/-- Round `a`: the DEEP components of the opened words of the failing instance's domain size are
not near the code on a common set at `δ' - 2/N`, but their batched word is `δ`-near. -/
def BatchBad (α : 𝕂)
    (quotients : (i : Fin S.k) → Fin (S.instanceSetup i).chunks → Fin (Challenge.d EF) →
      (S.instanceSetup i).Point → F) (ζ : 𝕂)
    (openings : (i : Fin S.k) → Openings (S.instanceSetup i)) (a : 𝕂) : Prop :=
  let i := failing S publicValues δ' traces perms terminals lα lβ
  let p : Iop.Batch.Prover S := ⟨traces, fun _ _ ↦ perms, fun _ _ ↦ terminals,
    fun _ _ _ ↦ quotients, fun _ _ _ _ ↦ openings⟩
  ¬ NearTogether (S.instanceSetup i) ((δ' : ℝ) - 2 / (S.instanceSetup i).size)
      (groupComponents p lα lβ α ζ i) ∧
    Near (S.instanceSetup i) δ
      (Iop.Batch.groupDeepWord p lα lβ α ζ a (S.logN i + S.params.logBlowup))

/-- FRI fold `j`: the fold of committed word `j` at `β` fails, on FRI's rounds `rounds`. -/
def FoldBad (rounds : Rounds 𝕂 S.logTop) (words : ℕ → (m : ℕ) → Fin (2 ^ m) → 𝕂) (j : ℕ)
    (β : 𝕂) : Prop :=
  Rounds.FoldFails (2 ^ S.params.logFinalPolyLen) δ loss β words j S.domainSetup.domain rounds

/-- Before the queries: the tallest batched word or an injected word is `δ`-far from its code, no
fold fails and the final polynomial has degree below `2 ^ logFinalPolyLen`. -/
def QueryReady (t : Transcript S) : Prop :=
  ¬ (Agrees S.domainSetup.domain (t.rounds.degree (2 ^ S.params.logFinalPolyLen)) (1 - δ)
      (t.deepWords S.logTop) ∧
    t.rounds.InputsAgree (2 ^ S.params.logFinalPolyLen) (1 - δ) S.domainSetup.domain) ∧
  t.fri.SafeLossy δ loss ∧ t.finalPoly.natDegree < 2 ^ S.params.logFinalPolyLen

/-- The query round: ready, the grinding sample `pow` has `queryPowBits` vanishing low bits, and
every query sample selects a point where the checks pass and FRI's first word agrees with the
tallest batched word. -/
def QueryBad (t : Transcript S) (pow : F) (queries : Fin S.params.numQueries → F) : Prop :=
  QueryReady S δ loss t ∧ CompPoly.CanonicalNat.toNat pow % 2 ^ S.params.queryPowBits = 0 ∧
    ∀ j, queryPoint S.domainSetup (queries j) ∈ t.consistentQueries

end Events

/-! ### The bounds -/

section Bounds
open Classical
variable {withLookups : Bool} (S : Iop.Batch.Setup EF withLookups)
  (publicValues : Fin S.k → List F) (δ δ' loss : NNReal)
  (traces : (i : Fin S.k) → Fin (S.air i).width → (S.instanceSetup i).Point → F)
  (perms : (i : Fin S.k) → Fin (S.instanceSetup i).permWidth → Fin (Challenge.d EF) →
    (S.instanceSetup i).Point → F)
  (terminals : Fin S.k → Challenge.Spec EF) (lα lβ : Challenge.Spec EF)

/-- The lookup round: a uniform pair `(α_L, β_L)` is bad with probability at most
`lookupError`. -/
theorem prob_lookupBad_le :
    Pr{let z ← $ᵗ (𝕂 × 𝕂)}[LookupBad S publicValues δ' traces z.1 z.2] ≤ S.lookupError δ' := by
  rw [SampleableType.prEvent_uniformSample, Iop.Batch.Setup.lookupError, Fintype.card_prod]
  have h := card_lookupBad_le S publicValues δ' traces
  have hK := card𝕂_ne_zero (EF := EF)
  have hT := card𝕂_ne_top (EF := EF)
  calc ((Finset.univ.filter fun z : 𝕂 × 𝕂 ↦ LookupBad S publicValues δ' traces z.1 z.2).card :
        ENNReal) / ((Fintype.card 𝕂 * Fintype.card 𝕂 : ℕ) : ENNReal)
      ≤ ((S.traceListSize δ' * (S.numInteractions + (S.numInteractions - 1) * S.lookupWidth) *
          Fintype.card 𝕂 : ℕ) : ENNReal) / ((Fintype.card 𝕂 * Fintype.card 𝕂 : ℕ) : ENNReal) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr h) _
    _ = _ := by
        simp only [Nat.cast_mul]
        rw [ENNReal.mul_div_mul_right _ _ hK hT]

/-- The lookup round with its grinding sample, drawn in the same answer: at most
`powFraction lookupPowBits · lookupError`. -/
theorem prob_lookupRound_le :
    Pr{let z ← $ᵗ (F × (𝕂 × 𝕂))}[CompPoly.CanonicalNat.toNat z.1 % 2 ^ S.params.lookupPowBits = 0 ∧
      LookupBad S publicValues δ' traces z.2.1 z.2.2] ≤
      powFraction F S.params.lookupPowBits * S.lookupError δ' :=
  (prob_pow_and_le _ _).trans (mul_le_mul_right (prob_lookupBad_le S publicValues δ' traces) _)

/-- Round `α`: a uniform `α` is bad with probability at most the worst instance's
`foldingError`. -/
theorem prob_alphaBad_le :
    Pr{let α ← $ᵗ 𝕂}[AlphaBad S publicValues δ' traces perms terminals lα lβ α] ≤
      ⨆ i, foldingError (S.instanceSetup i) δ' :=
  (Sound.prob_alphaBad_le _ _ _ _ δ' _ _).trans
    (le_iSup (fun i ↦ foldingError (S.instanceSetup i) δ') _)

/-- Round `ζ`: a uniform `ζ` is bad with probability at most the worst instance's
`outOfDomainError`. -/
theorem prob_zetaBad_le (α : 𝕂)
    (quotients : (i : Fin S.k) → Fin (S.instanceSetup i).chunks → Fin (Challenge.d EF) →
      (S.instanceSetup i).Point → F) :
    Pr{let ζ ← $ᵗ 𝕂}[ZetaBad S publicValues δ' traces perms terminals lα lβ α quotients ζ] ≤
      ⨆ i, outOfDomainError (S.instanceSetup i) δ' :=
  (Sound.prob_zetaBad_le _ _ _ _ δ' _ _ _ _).trans
    (le_iSup (fun i ↦ outOfDomainError (S.instanceSetup i) δ') _)

/-- Round `a`: a uniform `a` is bad with probability at most the worst instance's batching
error over the opened words of its domain size. -/
theorem prob_batchBad_le (α : 𝕂)
    (quotients : (i : Fin S.k) → Fin (S.instanceSetup i).chunks → Fin (Challenge.d EF) →
      (S.instanceSetup i).Point → F) (ζ : 𝕂)
    (openings : (i : Fin S.k) → Openings (S.instanceSetup i)) :
    Pr{let a ← $ᵗ 𝕂}[BatchBad S publicValues δ δ' traces perms terminals lα lβ α quotients ζ
      openings a] ≤
      ⨆ i, batchingErrorOf (S.instanceSetup i)
        (S.groupNumOpened (S.logN i + S.params.logBlowup)) δ
        ((δ' : ℝ) - 2 / (S.instanceSetup i).size) := by
  classical
  set i := failing S publicValues δ' traces perms terminals lα lβ
  set p : Iop.Batch.Prover S := ⟨traces, fun _ _ ↦ perms, fun _ _ ↦ terminals,
    fun _ _ _ ↦ quotients, fun _ _ _ _ ↦ openings⟩
  refine le_trans ?_ (le_iSup (fun i ↦ batchingErrorOf (S.instanceSetup i)
    (S.groupNumOpened (S.logN i + S.params.logBlowup)) δ
    ((δ' : ℝ) - 2 / (S.instanceSetup i).size)) i)
  rw [SampleableType.prEvent_uniformSample]
  by_cases hfar : NearTogether (S.instanceSetup i) ((δ' : ℝ) - 2 / (S.instanceSetup i).size)
    (groupComponents p lα lβ α ζ i)
  · have h : (Finset.univ.filter fun a : 𝕂 ↦
        BatchBad S publicValues δ δ' traces perms terminals lα lβ α quotients ζ openings a) = ∅ :=
      Finset.filter_false_of_mem fun a _ ha ↦ ha.1 hfar
    rw [h, Finset.card_empty, Nat.cast_zero, ENNReal.zero_div]
    exact bot_le
  have hset : (Finset.univ.filter fun a : 𝕂 ↦
      BatchBad S publicValues δ δ' traces perms terminals lα lβ α quotients ζ openings a) =
      Finset.univ.filter fun a : 𝕂 ↦ Near (S.instanceSetup i) δ
        fun x ↦ ∑ k : Fin (S.groupNumOpened (S.logN i + S.params.logBlowup)),
          a ^ (k : Nat) * groupComponents p lα lβ α ζ i k x :=
    Finset.filter_congr fun a _ ↦ by
      change (¬ _ ∧ Near _ δ (Iop.Batch.groupDeepWord p lα lβ α ζ a _)) ↔ _
      rw [groupDeepWord_eq]
      exact and_iff_right hfar
  rw [hset]
  exact batchingStep _ _ δ _ _ hfar

/-- FRI fold `j`: a uniform challenge is bad with probability at most the fold's error, for every
committed word and injected words. -/
theorem prob_foldBad_le (words : ℕ → (m : ℕ) → Fin (2 ^ m) → 𝕂)
    (inj : (m : ℕ) → Fin (2 ^ m) → 𝕂) (j : ℕ) :
    Pr{let β ← $ᵗ 𝕂}[FoldBad S δ loss (S.domainSetup.friRounds inj S.friHeights) words j β] ≤
      Iop.Batch.friFoldError S δ loss j := by
  refine (Rounds.prob_foldFails_le (Nat.two_pow_pos _) δ loss words j _ _).trans (le_of_eq ?_)
  exact Rounds.foldErrorAt_schedule_congr _ _ _ _ _ _ _ _ _ _ _ _

/-- FRI fold `j` with its grinding sample, drawn in the same answer: at most
`powFraction commitPowBits · friFoldError`. -/
theorem prob_foldRound_le (words : ℕ → (m : ℕ) → Fin (2 ^ m) → 𝕂)
    (inj : (m : ℕ) → Fin (2 ^ m) → 𝕂) (j : ℕ) :
    Pr{let z ← $ᵗ (F × 𝕂)}[CompPoly.CanonicalNat.toNat z.1 % 2 ^ S.params.commitPowBits = 0 ∧
      FoldBad S δ loss (S.domainSetup.friRounds inj S.friHeights) words j z.2] ≤
      powFraction F S.params.commitPowBits * Iop.Batch.friFoldError S δ loss j :=
  (prob_pow_and_le _ _).trans (mul_le_mul_right (prob_foldBad_le S δ loss words inj j) _)

/-- FRI's rounds have as many folds as the rounds of `roundError`. -/
theorem numFolds_rounds (t : Transcript S) : t.rounds.numFolds = S.friRounds.numFolds :=
  (Rounds.foldError_schedule_congr _ _ (2 ^ S.params.logFinalPolyLen) 0 0 _ _ _ _
    S.domainSetup.domain _).2.1

/-- The query round: at most `powFraction queryPowBits · friQueryError`. -/
theorem prob_queryBad_le (t : Transcript S) :
    Pr{let z ← $ᵗ (F × (Fin S.params.numQueries → F))}[QueryBad S δ loss t z.1 z.2] ≤
      powFraction F S.params.queryPowBits * Iop.Batch.friQueryError S δ loss := by
  classical
  by_cases hready : QueryReady S δ loss t
  · set D := S.domainSetup
    set m := D.logN + D.params.logBlowup
    set G := t.consistentQueries.image fun z ↦ reverseBits z.val m
    set nf : ℕ := t.rounds.numFolds
    have hdens := t.fri.consistent_density_le (t.deepWords S.logTop) δ δ loss loss.coe_nonneg
      hready.2.1 (Rounds.finalInCode_run _ _ t.finalPoly hready.2.2 _ _ _ _)
      (by rw [Transcript.fri, Rounds.inputsAgree_run]; exact hready.1)
    rw [Transcript.fri, Rounds.numFolds_run] at hdens
    have hmin : min ((δ : ℝ) - ((nf : ℝ) - 1) * loss) (δ - nf * loss) = δ - nf * loss :=
      min_eq_right (by nlinarith [loss.coe_nonneg])
    rw [hmin] at hdens
    have hG : (G.card : ℝ) ≤ 2 ^ m * (1 - δ + S.friRounds.numFolds * loss) := by
      have hpos : (0 : ℝ) < 2 ^ m := by positivity
      rw [div_le_iff₀ hpos] at hdens
      have hcard : (G.card : ℝ) ≤ t.consistentQueries.card := by
        exact_mod_cast Finset.card_image_le
      rw [← numFolds_rounds S t]
      change (G.card : ℝ) ≤ _
      have : (t.consistentQueries.card : ℝ) ≤ (1 - (δ - nf * loss)) * 2 ^ m := hdens
      nlinarith
    have h := prob_queryRound_le S.params.queryPowBits m S.params.numQueries
      (BaseField.two_pow_dvd_card_sub_one_of_le D.valid.twoAdic) G _ hG
    refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
    · congr 1
      funext z
      simp only [QueryBad, hready, true_and, queryPoint_mem_iff, G, m, D]
    · rw [Iop.Batch.friQueryError]
  · rw [SampleableType.prEvent_uniformSample]
    have h : (Finset.univ.filter fun z : F × (Fin S.params.numQueries → F) ↦
        QueryBad S δ loss t z.1 z.2) = ∅ :=
      Finset.filter_false_of_mem fun z _ hz ↦ hready hz.1
    rw [h, Finset.card_empty, Nat.cast_zero, ENNReal.zero_div]
    exact bot_le

end Bounds

/-! ### The terminal lemma -/

section Terminal
variable {withLookups : Bool} (S : Iop.Batch.Setup EF withLookups)
  (publicValues : Fin S.k → List F)

/-- Every instance's code has the batch's rate. -/
theorem rate_instanceSetup (i : Fin S.k) : (S.instanceSetup i).rate = S.rate := by
  rw [Iop.Setup.rate, Iop.Batch.Setup.rate, Iop.Setup.n, Iop.Setup.size, pow_add, Nat.cast_mul]
  have : ((2 ^ S.logN i : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- If an instance fails, the check passes at `ζ` and the rounds `α`, `ζ`, `a` are safe, the
batched DEEP word of the failing instance's domain size is `δ`-far from its code. -/
theorem not_near_deepWords (δ δ' : NNReal) (hδ' : (δ' : ℝ) < 1 - S.rate) (t : Transcript S)
    (hfail : ∃ i, Failing S publicValues δ' t.trace t.perm t.terminal t.lookupAlpha
      t.lookupBeta i)
    (hcheck : ∀ i, ConstraintsHoldAt (S.instanceSetup i) (publicValues i) t.alpha t.zeta
      (t.openings i) (S.challenges t.lookupAlpha t.lookupBeta i) (t.terminal i))
    (hα : ¬ AlphaBad S publicValues δ' t.trace t.perm t.terminal t.lookupAlpha t.lookupBeta
      t.alpha)
    (hζ : ¬ ZetaBad S publicValues δ' t.trace t.perm t.terminal t.lookupAlpha t.lookupBeta
      t.alpha t.quotient t.zeta)
    (ha : ¬ BatchBad S publicValues δ δ' t.trace t.perm t.terminal t.lookupAlpha t.lookupBeta
      t.alpha t.quotient t.zeta t.openings t.batch) :
    let i := failing S publicValues δ' t.trace t.perm t.terminal t.lookupAlpha t.lookupBeta
    ¬ Near (S.instanceSetup i) δ (t.deepWords (S.logN i + S.params.logBlowup)) := by
  intro i hnear
  set I := S.instanceSetup i
  have hf := failing_spec S publicValues δ' t.trace t.perm t.terminal t.lookupAlpha t.lookupBeta
    hfail
  have htogether : NearTogether I ((δ' : ℝ) - 2 / I.size)
      (groupComponents t.prover t.lookupAlpha t.lookupBeta t.alpha t.zeta i) :=
    not_not.mp fun h ↦ ha ⟨h, hnear⟩
  have hinst := nearTogether_instance t.prover t.lookupAlpha t.lookupBeta t.alpha t.zeta i _
    htogether
  have hoff : OffTraceDomain I t.zeta := not_not.mp fun h ↦ hζ ⟨hα, Or.inl h⟩
  have hδI : (δ' : ℝ) < 1 - I.rate := by rw [rate_instanceSetup]; exact hδ'
  obtain ⟨P, Q, R, hPd, hQd, hRd, hagree, ho⟩ :=
    decodingStep I δ' hδI (t.prover.instanceProver t.lookupAlpha t.lookupBeta i) t.alpha t.zeta
      hoff hinst
  have hJ := committed_mem_candidates hPd hRd hQd hagree
  refine hζ ⟨hα, Or.inr ⟨I.committed P R Q, hJ, hf _ (committedTrace_mem_candidates hJ) _
    (committedPerm_mem_candidates hJ), ?_⟩⟩
  have h : t.openings i = trueOpenings I P Q t.zeta R := ho
  rw [Setup.committedTrace_committed, Setup.committedQuotient_committed,
    Setup.committedPerm_committed, ← h]
  exact hcheck i

/-- A batched word far from its code makes FRI's first word or one of its injected words far: it
is the tallest batched word, or FRI injects it at its domain's size. -/
theorem not_agrees_of_not_near (δ : NNReal) (t : Transcript S) (i : Fin S.k)
    (hfar : ¬ Near (S.instanceSetup i) δ (t.deepWords (S.logN i + S.params.logBlowup))) :
    ¬ (Agrees S.domainSetup.domain (t.rounds.degree (2 ^ S.params.logFinalPolyLen)) (1 - δ)
        (t.deepWords S.logTop) ∧
      t.rounds.InputsAgree (2 ^ S.params.logFinalPolyLen) (1 - δ) S.domainSetup.domain) := by
  set D := S.domainSetup
  have hf := D.valid.finalPolyFits
  have hfit := fits_friHeights S
  have hDl : D.logN = S.logN S.top := rfl
  have hDf : D.params.logFinalPolyLen = S.params.logFinalPolyLen := rfl
  have hDb : D.params.logBlowup = S.params.logBlowup := rfl
  have hfar' : ∀ hm, ¬ Agrees (cosetDomain (EF := EF) (S.logN i + S.params.logBlowup) hm)
      (2 ^ S.logN i) (1 - δ) (t.deepWords (S.logN i + S.params.logBlowup)) :=
    fun _ hA ↦ hfar (near_of_agrees (S.instanceSetup i) δ _ hA)
  rintro ⟨hw, hin⟩
  by_cases htop : S.logN i = S.logN S.top
  · rw [Transcript.rounds, degree_friRounds D _ _ hfit] at hw
    rw [htop] at hfar'
    exact hfar' D.valid.twoAdic hw
  · have hm : S.logN i + S.params.logBlowup ∈ S.friHeights :=
      (mem_friHeights S _).mpr ⟨i, rfl, by omega⟩
    obtain ⟨E, hE, hagree⟩ := Rounds.agrees_of_inputsAgree D.valid.folds (injected S t.deepWords)
      _ _ (fun E ↦ IsLevel E) (fun E k hE ↦ isLevel_subdomain E k hE)
      (D.logN + D.params.logBlowup) _ D.domain S.friHeights (by omega) (Nat.sub_le _ _) hfit
      (isLevel_cosetDomain _ _) hin _ hm
    have hdeg : 2 ^ (S.logN i + S.params.logBlowup -
        (S.params.logFinalPolyLen + S.params.logBlowup)) * 2 ^ S.params.logFinalPolyLen =
        2 ^ S.logN i := by
      rw [← pow_add]
      congr 1
      have := S.folds i
      omega
    rw [hdeg] at hagree
    have h1 := agrees_of_agrees_mul (inv_ne_zero (foldShift_ne_zero S _)) hagree
    have h2 := agrees_cosetDomain_of_isLevel E hE _ (Nat.two_pow_pos _) _ _ h1
    exact hfar' hE.1 h2

/-- **The terminal lemma.** If the verifier's checks pass on a transcript whose rounds are all
safe, some tuple of candidate traces satisfies the batch: the terminals of the instances with
lookups sum to zero, every instance's check at `ζ`, a final polynomial of degree below
`2 ^ logFinalPolyLen`, a grinding sample with `queryPowBits` vanishing low bits, and every query
sample selecting a point where the checks pass and FRI's first word agrees with the tallest
batched word. -/
theorem exists_satisfied_of_safe (δ δ' loss : NNReal) (hδ' : (δ' : ℝ) < 1 - S.rate)
    (t : Transcript S) (pow : F) (queries : Fin S.params.numQueries → F)
    (hsum : (∑ i with S.lookups i ≠ [], t.terminal i) = 0)
    (hcheck : ∀ i, ConstraintsHoldAt (S.instanceSetup i) (publicValues i) t.alpha t.zeta
      (t.openings i) (S.challenges t.lookupAlpha t.lookupBeta i) (t.terminal i))
    (hdegree : t.finalPoly.natDegree < 2 ^ S.params.logFinalPolyLen)
    (hpow : CompPoly.CanonicalNat.toNat pow % 2 ^ S.params.queryPowBits = 0)
    (hqueries : ∀ j, queryPoint S.domainSetup (queries j) ∈ t.consistentQueries)
    (hlookup : ¬ LookupBad S publicValues δ' t.trace t.lookupAlpha t.lookupBeta)
    (hα : ¬ AlphaBad S publicValues δ' t.trace t.perm t.terminal t.lookupAlpha t.lookupBeta
      t.alpha)
    (hζ : ¬ ZetaBad S publicValues δ' t.trace t.perm t.terminal t.lookupAlpha t.lookupBeta
      t.alpha t.quotient t.zeta)
    (ha : ¬ BatchBad S publicValues δ δ' t.trace t.perm t.terminal t.lookupAlpha t.lookupBeta
      t.alpha t.quotient t.zeta t.openings t.batch)
    (hfolds : ∀ j, ¬ FoldBad S δ loss t.rounds t.words j (t.betas j))
    (hq : ¬ QueryBad S δ loss t pow queries) :
    ∃ traces ∈ Iop.Batch.closeTraces S δ' t.trace, S.Satisfied traces publicValues := by
  by_contra hno
  have hfail : ∀ traces ∈ Iop.Batch.closeTraces S δ' t.trace, ¬ S.Satisfied traces publicValues :=
    fun traces h hs ↦ hno ⟨traces, h, hs⟩
  obtain ⟨i, hi⟩ := exists_failing_instance publicValues δ' t.trace t.perm t.terminal
    t.lookupAlpha t.lookupBeta hfail hlookup hsum
  have hfar := not_near_deepWords S publicValues δ δ' hδ' t ⟨i, hi⟩ hcheck hα hζ ha
  refine hq ⟨⟨not_agrees_of_not_near S δ t _ hfar, ?_, hdegree⟩, hpow, hqueries⟩
  rw [Transcript.fri, Rounds.safeLossy_run_iff]
  exact hfolds

end Terminal

end Batch

end CompStark.Sound
