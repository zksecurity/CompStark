/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.BatchAssembly
public import CompStark.Sound.Rbr
public import CompStark.BatchSoundnessError
public import CompStark.Sound.FriRun

/-! # Round-by-round soundness of the batch STARK

The batch STARK's rounds as bad events on transcript prefixes, each bounded for every prefix by
its error: in `CompStark/BatchSoundnessError.lean` for the interactive protocol, whose knowledge
certificate (`CompStark/Interaction/BatchKnowledge.lean`) is built from the events of the lookup
challenges, `α`, `ζ` and `a`, with the failing instance's errors (`prob_batchBad_le_failing`). The
transcript (`Batch.Transcript`) holds every instance's
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

With safe lookup challenges and terminals summing to zero, a tuple of candidate traces that does
not satisfy the batch has a failing instance (`exists_failing_instance`), and as for the STARK its
safe `α`, `ζ` and `a` make the batched word of its domain size far (`not_near_deepWords`).
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

/-- FRI's injected words: Plonky3 adds the batched DEEP word of the domain of `2 ^ m` points times
`β ^ 2 ^ k` to a fold by `2 ^ k` at `β`, which is ArkLib's fold at `s β`, `s` the shift of the
folded domain's square root: so ArkLib's fold injects the word divided by the folded domain's
shift. -/
noncomputable def injected (words : (m : ℕ) → Fin (2 ^ m) → 𝕂) (m : ℕ) (x : Fin (2 ^ m)) : 𝕂 :=
  (foldShift S m)⁻¹ * words m x

end Injected

/-! ### The transcript -/

/-- The transcript of the batch STARK, as the extractor reads it off a proof: every instance's
words, terminals and claimed values, the challenges, and FRI's committed words, final polynomial
and folding challenges. -/
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
not near the code on a common set at `δ'`, but their batched word is `δ`-near. -/
def BatchBad (α : 𝕂)
    (quotients : (i : Fin S.k) → Fin (S.instanceSetup i).chunks → Fin (Challenge.d EF) →
      (S.instanceSetup i).Point → F) (ζ : 𝕂)
    (openings : (i : Fin S.k) → Openings (S.instanceSetup i)) (a : 𝕂) : Prop :=
  let i := failing S publicValues δ' traces perms terminals lα lβ
  let p : Iop.Batch.Prover S := ⟨traces, fun _ _ ↦ perms, fun _ _ ↦ terminals,
    fun _ _ _ ↦ quotients, fun _ _ _ _ ↦ openings⟩
  ¬ NearTogether (S.instanceSetup i) δ'
      (groupComponents p lα lβ α ζ i) ∧
    Near (S.instanceSetup i) δ
      (Iop.Batch.groupDeepWord p lα lβ α ζ a (S.logN i + S.params.logBlowup))

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

/-- Round `a`: a uniform `a` is bad with probability at most the failing instance's batching
error over the opened words of its domain size. -/
theorem prob_batchBad_le_failing (α : 𝕂)
    (quotients : (i : Fin S.k) → Fin (S.instanceSetup i).chunks → Fin (Challenge.d EF) →
      (S.instanceSetup i).Point → F) (ζ : 𝕂)
    (openings : (i : Fin S.k) → Openings (S.instanceSetup i)) :
    let i := failing S publicValues δ' traces perms terminals lα lβ
    Pr{let a ← $ᵗ 𝕂}[BatchBad S publicValues δ δ' traces perms terminals lα lβ α quotients ζ
      openings a] ≤
      batchingErrorOf (S.instanceSetup i) (S.groupNumOpened (S.logN i + S.params.logBlowup)) δ
        δ' := by
  classical
  intro i
  set p : Iop.Batch.Prover S := ⟨traces, fun _ _ ↦ perms, fun _ _ ↦ terminals,
    fun _ _ _ ↦ quotients, fun _ _ _ _ ↦ openings⟩
  rw [SampleableType.prEvent_uniformSample]
  by_cases hfar : NearTogether (S.instanceSetup i) δ'
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
  have htogether : NearTogether I δ'
      (groupComponents t.prover t.lookupAlpha t.lookupBeta t.alpha t.zeta i) :=
    not_not.mp fun h ↦ ha ⟨h, hnear⟩
  have hinst := nearTogether_instance t.prover t.lookupAlpha t.lookupBeta t.alpha t.zeta i _
    htogether
  have hoff : OffTraceDomain I t.zeta := not_not.mp fun h ↦ hζ ⟨hα, Or.inl h⟩
  have hL : OffDomain I t.zeta := not_not.mp fun h ↦ hζ ⟨hα, Or.inr (Or.inl h)⟩
  have hδI : (δ' : ℝ) < 1 - I.rate := by rw [rate_instanceSetup]; exact hδ'
  obtain ⟨P, Q, R, hPd, hQd, hRd, hagree, ho⟩ :=
    decodingStep I δ' hδI (t.prover.instanceProver t.lookupAlpha t.lookupBeta i) t.alpha t.zeta
      hoff hL hinst
  have hJ := committed_mem_candidates hPd hRd hQd hagree
  refine hζ ⟨hα, Or.inr (Or.inr ⟨I.committed P R Q, hJ,
    hf _ (committedTrace_mem_candidates hJ) _ (committedPerm_mem_candidates hJ), ?_⟩)⟩
  have h : t.openings i = trueOpenings I P Q t.zeta R := ho
  rw [Setup.committedTrace_committed, Setup.committedQuotient_committed,
    Setup.committedPerm_committed, ← h]
  exact hcheck i

end Terminal

end Batch

end CompStark.Sound
