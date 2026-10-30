/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Interaction.Batch
public import CompStark.Interaction.StarkKnowledge
public import CompStark.Sound.BatchRbr

/-! # The batch STARK's knowledge certificate on the interaction layer

The batch STARK on ArkLib's interaction layer (`CompStark/Interaction/Batch.lean`) is
round-by-round knowledge sound, with a `KnowledgeCertificate`: the rounds before FRI
(`Setup.prefixCertificate`) appended with `KnowledgeCertificate.append` to FRI's certificate on
the batched DEEP words (`Fri.Interaction.certificate`), gated by the checks in the clear
(`Setup.friCertificate`).

The extractor reads every instance's trace off the trace oracle (`Setup.rootState`). After the
trace message, the state asks for a tuple of close traces satisfying the batch; after that, the
states are those of the doomed-transcript argument of `CompStark/Sound/BatchRbr.lean`: they hold
unless no tuple of close traces satisfies the batch and the challenges so far are safe. A challenge
is bad only if it is bad in the round's sense:

* `(α_L, β_L)`: `LookupBad`, with probability at most `lookupError`;
* `α`, `ζ`, `a`: the events of the instance the traces, permutation traces and terminals make
  fail (`Batch.failing`), with that instance's folding, out-of-domain and batching errors, which
  the errors of each path sum to its `instanceError`;
* FRI's rounds, with FRI's errors.

`Setup.extraction_le_knowledgeError` bounds the probability that the verifier accepts while no
tuple of traces close to the committed ones satisfies the batch by the knowledge error
`knowledgeError`, and `Statement.extraction_le_knowledgeError` by the statement's, the prover
choosing the lengths.
-/

@[expose] public section
namespace CompStark.Iop.Batch
open CompStark.Stark CompStark.Sound CompStark.Interaction _root_.Interaction
open _root_.Interaction.Oracle _root_.Interaction.Oracle.Security OracleComp OracleSpec
open scoped NNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

namespace Setup
variable {withLookups : Bool} (S : Setup EF withLookups) (publicValues : Fin S.k → List F)

/-! ### The rounds before FRI -/

/-- The batch STARK's rounds before FRI. -/
def prefixProtocol : Protocol :=
  .oracle S.TraceMessage <|
  .public .receiver (𝕂 × 𝕂) fun _ ↦
  .oracle S.PermMessage <|
  .public .sender (Fin S.k → 𝕂) fun _ ↦
  .public .receiver 𝕂 fun _ ↦
  .oracle S.QuotientMessage <|
  .public .receiver 𝕂 fun _ ↦
  .public .sender S.OpeningsMessage fun _ ↦
  .public .receiver 𝕂 fun _ ↦ .done

/-- The batch STARK is its rounds before FRI, then FRI. -/
theorem protocol_tree :
    S.protocol.tree = PFunctor.FreeM.append S.prefixProtocol.tree (fun _ ↦ S.friProtocol.tree) :=
  rfl

variable (δ δ' : ℝ≥0)

/-- No tuple of traces close to the committed words satisfies the batch. -/
def Far (T : S.TraceMessage) : Prop :=
  ∀ traces ∈ closeTraces S δ' (S.traceWords T), ¬ S.Satisfied traces publicValues

/-- The input state: a trace message and a tuple of traces close to it satisfying the batch. -/
def rootState : KnowledgeState where
  Witness := S.TraceMessage × (Fin S.k → Array F)
  holds w := w.2 ∈ closeTraces S δ' (S.traceWords w.1) ∧ S.Satisfied w.2 publicValues

/-- After the trace message `T`: a tuple of traces close to it satisfying the batch. -/
def traceState (T : S.TraceMessage) : KnowledgeState where
  Witness := Fin S.k → Array F
  holds traces := traces ∈ closeTraces S δ' (S.traceWords T) ∧ S.Satisfied traces publicValues

/-- A tuple of traces close to the trace message satisfying the batch, if there is one. -/
noncomputable def chooseTraces (T : S.TraceMessage) : Fin S.k → Array F :=
  Classical.epsilon fun traces : Fin S.k → Array F ↦
    (S.traceState publicValues δ' T).holds traces

/-- Doomed after the lookup challenges: no tuple of close traces satisfies the batch, and the
lookup challenges are safe. -/
def lookupDoom (T : S.TraceMessage) (l : 𝕂 × 𝕂) : Prop :=
  S.Far publicValues δ' T ∧ ¬ Sound.Batch.LookupBad S publicValues δ' (S.traceWords T) l.1 l.2

/-- The instance the traces, permutation traces and terminals make fail. -/
noncomputable def failingOf (T : S.TraceMessage) (l : 𝕂 × 𝕂) (P : S.PermMessage)
    (terminals : Fin S.k → 𝕂) : Fin S.k :=
  Sound.Batch.failing S publicValues δ' (S.traceWords T) (S.permWords P) terminals l.1 l.2

/-- Doomed after `α`: doomed after the lookup challenges, and `α` is safe. -/
def alphaDoom (T : S.TraceMessage) (l : 𝕂 × 𝕂) (P : S.PermMessage) (terminals : Fin S.k → 𝕂)
    (α : 𝕂) : Prop :=
  S.lookupDoom publicValues δ' T l ∧ ¬ Sound.Batch.AlphaBad S publicValues δ' (S.traceWords T)
    (S.permWords P) terminals l.1 l.2 α

/-- Doomed after `ζ`: doomed after `α`, and `ζ` is safe. -/
def zetaDoom (T : S.TraceMessage) (l : 𝕂 × 𝕂) (P : S.PermMessage) (terminals : Fin S.k → 𝕂)
    (α : 𝕂) (Q : S.QuotientMessage) (ζ : 𝕂) : Prop :=
  S.alphaDoom publicValues δ' T l P terminals α ∧ ¬ Sound.Batch.ZetaBad S publicValues δ'
    (S.traceWords T) (S.permWords P) terminals l.1 l.2 α (S.quotientWords Q) ζ

/-- FRI's input state on the batched DEEP words, at proximity `δ` and proximity loss `loss`, once
the checks in the clear pass. -/
noncomputable def friState (T : S.TraceMessage) (l : 𝕂 × 𝕂) (P : S.PermMessage)
    (terminals : Fin S.k → 𝕂) (α : 𝕂) (Q : S.QuotientMessage) (ζ : 𝕂) (o : S.OpeningsMessage)
    (a : 𝕂) (loss : ℝ≥0) : KnowledgeState :=
  gateState (S.Checks publicValues l.1 l.2 terminals α ζ o)
    (Fri.Interaction.levelState (S.logN S.top + S.params.logBlowup)
      (2 ^ S.params.logFinalPolyLen) (S.deepWords T l.1 l.2 P terminals α Q ζ o a) δ loss
      S.domainSetup.domain (S.domainSetup.friSchedule S.friHeights) 0
      (S.deepWords T l.1 l.2 P terminals α Q ζ o a _) Finset.univ)

/-- The witness maps of the rounds before FRI. -/
noncomputable def prefixExtractor (loss : ℝ≥0) :
    RoundExtractor S.prefixProtocol.tree (S.rootState publicValues δ') :=
  fun T ↦ ⟨S.traceState publicValues δ' T, fun t ↦ (T, t), fun l ↦
    ⟨Setup.doomState (S.lookupDoom publicValues δ' T l), fun _ ↦ S.chooseTraces publicValues δ' T,
      fun P ↦ ⟨Setup.doomState (S.lookupDoom publicValues δ' T l), id, fun τ ↦
        ⟨Setup.doomState (S.lookupDoom publicValues δ' T l), id, fun α ↦
          ⟨Setup.doomState (S.alphaDoom publicValues δ' T l P τ α), fun _ ↦ (), fun Q ↦
            ⟨Setup.doomState (S.alphaDoom publicValues δ' T l P τ α), id, fun ζ ↦
              ⟨Setup.doomState (S.zetaDoom publicValues δ' T l P τ α Q ζ), fun _ ↦ (), fun o ↦
                ⟨Setup.doomState (S.zetaDoom publicValues δ' T l P τ α Q ζ), id, fun a ↦
                  ⟨S.friState publicValues δ T l P τ α Q ζ o a loss, fun _ ↦ (),
                    PUnit.unit⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The rounds' challenge programs and errors: uniform challenges, with the lookup error and the
failing instance's folding, out-of-domain and batching errors. -/
noncomputable def prefixChallenges :
    RoundExtractor.ChallengeSchedule S.prefixProtocol.tree S.prefixProtocol.roles :=
  fun T ↦ ⟨($ᵗ (𝕂 × 𝕂), S.lookupError δ'), fun l P ↦ ⟨PUnit.unit, fun τ ↦
    ⟨($ᵗ 𝕂, foldingError (S.instanceSetup (S.failingOf publicValues δ' T l P τ)) δ'), fun _ _ ↦
      ⟨($ᵗ 𝕂, outOfDomainError (S.instanceSetup (S.failingOf publicValues δ' T l P τ)) δ'),
        fun _ ↦ ⟨PUnit.unit, fun _ ↦
          ⟨($ᵗ 𝕂, batchingErrorOf (S.instanceSetup (S.failingOf publicValues δ' T l P τ))
            (S.groupNumOpened (S.logN (S.failingOf publicValues δ' T l P τ) + S.params.logBlowup))
            δ δ'), fun _ ↦ PUnit.unit⟩⟩⟩⟩⟩⟩

theorem prefixExtractor_isProverPreserving (loss : ℝ≥0) :
    (S.prefixExtractor publicValues δ δ' loss).IsProverPreserving S.prefixProtocol.roles :=
  ⟨fun _ _ h ↦ h, fun _ ↦ ⟨fun _ h _ ↦ (nomatch h), fun _ ↦ ⟨fun _ _ h ↦ h, fun _ ↦
    ⟨fun _ _ _ h ↦ h, fun _ ↦ ⟨fun _ h _ ↦ (nomatch h), fun _ ↦ ⟨fun _ _ h ↦ h, fun _ ↦
      ⟨fun _ h _ ↦ (nomatch h), fun _ ↦ ⟨fun _ _ _ h ↦ h, fun _ ↦
        ⟨fun _ h _ ↦ (nomatch h), fun _ ↦ trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The chosen traces hold unless no tuple of close traces satisfies the batch. -/
theorem chooseTraces_holds (T : S.TraceMessage) (hfar : ¬ S.Far publicValues δ' T) :
    (S.traceState publicValues δ' T).holds (S.chooseTraces publicValues δ' T) := by
  simp only [Far, not_forall, not_not] at hfar
  obtain ⟨t, ht, hsat⟩ := hfar
  exact Classical.epsilon_spec (p := fun traces : Fin S.k → Array F ↦
    (S.traceState publicValues δ' T).holds traces) ⟨t, ht, hsat⟩

/-- FRI's state on the batched words holds only if every instance's batched word is `δ`-near its
code. -/
theorem near_of_levelState (w : (m : ℕ) → Fin (2 ^ m) → 𝕂) (loss : ℝ≥0)
    (x : (Fri.Interaction.levelState (S.logN S.top + S.params.logBlowup)
      (2 ^ S.params.logFinalPolyLen) w δ loss S.domainSetup.domain
      (S.domainSetup.friSchedule S.friHeights) 0 (w _) Finset.univ).Witness)
    (hx : (Fri.Interaction.levelState (S.logN S.top + S.params.logBlowup)
      (2 ^ S.params.logFinalPolyLen) w δ loss S.domainSetup.domain
      (S.domainSetup.friSchedule S.friHeights) 0 (w _) Finset.univ).holds x)
    (i : Fin S.k) : Near (S.instanceSetup i) δ (w (S.logN i + S.params.logBlowup)) := by
  obtain ⟨hword, hin⟩ := Fri.Interaction.agrees_of_root_holds _ _ w δ loss _ _ x hx
  have hfit : Fri.Interaction.Schedule.Fits (S.params.logFinalPolyLen + S.params.logBlowup)
      (S.logN S.top + S.params.logBlowup) S.friHeights := fits_friHeights S
  have hf := (S.valid i).finalPolyFits
  have hft := (S.valid S.top).finalPolyFits
  have hDl : S.domainSetup.logN = S.logN S.top := rfl
  have hDb : S.domainSetup.params.logBlowup = S.params.logBlowup := rfl
  suffices h : ∀ hm, FriInject.Agrees (cosetDomain (EF := EF) (S.logN i + S.params.logBlowup) hm)
      (2 ^ S.logN i) (1 - δ) (w (S.logN i + S.params.logBlowup)) from
    near_of_agrees (S.instanceSetup i) δ _ (h (S.valid i).twoAdic)
  intro hm
  by_cases htop : S.logN i = S.logN S.top
  · rw [S.domainSetup.degree_friSchedule _ hfit] at hword
    have key : ∀ (n : ℕ) (hn : n + S.params.logBlowup ≤ twoAdicity F), n = S.logN S.top →
        FriInject.Agrees (cosetDomain (EF := EF) (n + S.params.logBlowup) hn) (2 ^ n) (1 - δ)
          (w (n + S.params.logBlowup)) := by
      intro n hn h
      subst h
      exact hword
    exact key _ hm htop
  · have hmem : S.logN i + S.params.logBlowup ∈ S.friHeights :=
      (mem_friHeights S _).mpr ⟨i, rfl, by omega⟩
    obtain ⟨E, hE, hagree⟩ := Fri.Interaction.Schedule.agrees_of_inputsAgree
      S.domainSetup.valid.folds w _ _ (fun E ↦ IsLevel E) (fun E k hE ↦ isLevel_subdomain E k hE)
      (S.logN S.top + S.params.logBlowup) _ S.domainSetup.domain S.friHeights (by omega)
      (Nat.sub_le _ _) hfit (isLevel_cosetDomain _ _) hin _ hmem
    have hdeg : 2 ^ (S.logN i + S.params.logBlowup -
        (S.params.logFinalPolyLen + S.params.logBlowup)) * 2 ^ S.params.logFinalPolyLen =
        2 ^ S.logN i := by
      rw [← pow_add]
      congr 1
      omega
    rw [hdeg] at hagree
    exact agrees_cosetDomain_of_isLevel E hE _ (Nat.two_pow_pos _) _ _ hagree

/-- The transcript of the rounds before FRI, without FRI's words. -/
noncomputable def transcriptOf (T : S.TraceMessage) (l : 𝕂 × 𝕂) (P : S.PermMessage)
    (terminals : Fin S.k → 𝕂) (α : 𝕂) (Q : S.QuotientMessage) (ζ : 𝕂) (o : S.OpeningsMessage)
    (a : 𝕂) : Sound.Batch.Transcript S :=
  ⟨S.traceWords T, l.1, l.2, S.permWords P, terminals, α, S.quotientWords Q, ζ, o, a,
    fun _ _ _ ↦ 0, 0, fun _ ↦ 0⟩

theorem prefixExtractor_isLocallyBounded (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0) :
    (S.prefixExtractor publicValues δ δ' loss).IsLocallyBounded S.prefixProtocol.roles
      (S.prefixChallenges publicValues δ δ') := by
  intro T
  refine ⟨?_, fun l P τ ↦ ⟨?_, fun α Q ↦ ⟨?_, fun ζ o ↦ ⟨?_, fun _ ↦ trivial⟩⟩⟩⟩
  · rw [_root_.RoundByRound.GameFamily.isBounded_iff]
    intro _ _
    refine (prEvent_mono _ _ _ fun l (h : ∃ _ : Unit,
      ¬ (S.traceState publicValues δ' T).holds (S.chooseTraces publicValues δ' T) ∧
        ¬ S.lookupDoom publicValues δ' T l) ↦ ?_).trans
      (Sound.Batch.prob_lookupBad_le S publicValues δ' (S.traceWords T))
    obtain ⟨-, hnot, hdoom⟩ := h
    by_contra hl
    have hfar : S.Far publicValues δ' T := by
      by_contra hfar
      exact hnot (S.chooseTraces_holds publicValues δ' T hfar)
    exact hdoom ⟨hfar, hl⟩
  · rw [_root_.RoundByRound.GameFamily.isBounded_iff]
    intro _ _
    refine (prEvent_mono _ _ _ fun α (h : ∃ _ : Unit,
      ¬ ¬ S.lookupDoom publicValues δ' T l ∧ ¬ S.alphaDoom publicValues δ' T l P τ α) ↦ ?_).trans
      (Sound.prob_alphaBad_le (S.instanceSetup (S.failingOf publicValues δ' T l P τ))
        (publicValues (S.failingOf publicValues δ' T l P τ)) (S.challenges l.1 l.2 (S.failingOf publicValues δ' T l P τ))
        (τ (S.failingOf publicValues δ' T l P τ)) δ' (S.traceWords T (S.failingOf publicValues δ' T l P τ))
        (S.permWords P (S.failingOf publicValues δ' T l P τ)))
    obtain ⟨-, hnot, hdoom⟩ := h
    by_contra hα
    exact hdoom ⟨not_not.mp hnot, hα⟩
  · rw [_root_.RoundByRound.GameFamily.isBounded_iff]
    intro _ _
    refine (prEvent_mono _ _ _ fun ζ (h : ∃ _ : Unit,
      ¬ ¬ S.alphaDoom publicValues δ' T l P τ α ∧
        ¬ S.zetaDoom publicValues δ' T l P τ α Q ζ) ↦ ?_).trans
      (Sound.prob_zetaBad_le (S.instanceSetup (S.failingOf publicValues δ' T l P τ))
        (publicValues (S.failingOf publicValues δ' T l P τ)) (S.challenges l.1 l.2 (S.failingOf publicValues δ' T l P τ))
        (τ (S.failingOf publicValues δ' T l P τ)) δ' (S.traceWords T (S.failingOf publicValues δ' T l P τ)) α
        (S.quotientWords Q (S.failingOf publicValues δ' T l P τ)) (S.permWords P (S.failingOf publicValues δ' T l P τ)))
    obtain ⟨-, hnot, hdoom⟩ := h
    by_contra hζ
    exact hdoom ⟨not_not.mp hnot, hζ⟩
  · rw [_root_.RoundByRound.GameFamily.isBounded_iff]
    intro _ _
    refine (prEvent_mono _ _ _ fun a (h : ∃ w,
      ¬ ¬ S.zetaDoom publicValues δ' T l P τ α Q ζ ∧
        (S.friState publicValues δ T l P τ α Q ζ o a loss).holds w) ↦ ?_).trans
      (Sound.Batch.prob_batchBad_le_failing S publicValues δ δ' (S.traceWords T) (S.permWords P)
        τ l.1 l.2 α (S.quotientWords Q) ζ o)
    obtain ⟨w, hnot, ⟨hsum, hcheck⟩, hw⟩ := h
    obtain ⟨⟨⟨hfar, hl⟩, hα⟩, hζ⟩ := not_not.mp hnot
    by_contra hbatch
    have hfail := exists_failing_instance publicValues δ' (S.traceWords T) (S.permWords P) τ l.1
      l.2 hfar hl hsum
    exact Sound.Batch.not_near_deepWords S publicValues δ δ' hδ'
      (S.transcriptOf T l P τ α Q ζ o a) hfail hcheck hα hζ hbatch
      (S.near_of_levelState δ _ loss w hw _)

/-- **The rounds before FRI**, as a knowledge certificate. -/
noncomputable def prefixCertificate (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0) :
    KnowledgeCertificate S.prefixProtocol.tree S.prefixProtocol.roles
      (S.rootState publicValues δ') where
  extractor := S.prefixExtractor publicValues δ δ' loss
  challenges := S.prefixChallenges publicValues δ δ'
  prover_preserving := S.prefixExtractor_isProverPreserving publicValues δ δ' loss
  local_bound := S.prefixExtractor_isLocallyBounded publicValues δ δ' hδ' loss

/-- FRI's knowledge certificate on the batched DEEP words, gated by the checks in the clear. -/
noncomputable def friCertificate (T : S.TraceMessage) (l : 𝕂 × 𝕂) (P : S.PermMessage)
    (terminals : Fin S.k → 𝕂) (α : 𝕂) (Q : S.QuotientMessage) (ζ : 𝕂) (o : S.OpeningsMessage)
    (a : 𝕂) (loss : ℝ≥0) :
    KnowledgeCertificate S.friProtocol.tree S.friProtocol.roles
      (S.friState publicValues δ T l P terminals α Q ζ o a loss) :=
  gateCertificate _ (Fri.Interaction.certificate (S.logN S.top + S.params.logBlowup)
    (2 ^ S.params.logFinalPolyLen) S.params.numQueries
    (S.deepWords T l.1 l.2 P terminals α Q ζ o a) δ loss (Nat.two_pow_pos _) loss.coe_nonneg
    le_rfl S.domainSetup.domain (S.domainSetup.friSchedule S.friHeights) 0
    (S.deepWords T l.1 l.2 P terminals α Q ζ o a _) Finset.univ)

/-- **The batch STARK's knowledge certificate**: the rounds before FRI, appended with FRI's on the
batched DEEP words. -/
noncomputable def certificate (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0) :
    KnowledgeCertificate S.protocol.tree S.protocol.roles (S.rootState publicValues δ') :=
  (S.prefixCertificate publicValues δ δ' hδ' loss).append (fun _ ↦ S.friProtocol.tree)
    (fun _ ↦ S.friProtocol.roles) fun path ↦
      S.friCertificate publicValues δ path.1 path.2.1 path.2.2.1 path.2.2.2.1 path.2.2.2.2.1
        path.2.2.2.2.2.1 path.2.2.2.2.2.2.1 path.2.2.2.2.2.2.2.1 path.2.2.2.2.2.2.2.2.1 loss

/-- The certificate's largest path error: the lookup error, the worst instance's error, and FRI's
at the proximity loss. -/
theorem maxError_certificate (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0) :
    (S.certificate publicValues δ δ' hδ' loss).challenges.maxError S.protocol.roles ≤
      S.lookupError δ' + (⨆ i, S.instanceError δ δ' i) +
        S.domainSetup.friBound S.friHeights δ loss := by
  have hfri : ∀ T l P τ α Q ζ o a, RoundExtractor.ChallengeSchedule.maxError S.friProtocol.roles
      (S.friCertificate publicValues δ T l P τ α Q ζ o a loss).challenges ≤
      S.domainSetup.friBound S.friHeights δ loss := by
    intro T l P τ α Q ζ o a
    refine (Fri.Interaction.maxError_certificate (S.logN S.top + S.params.logBlowup)
      (2 ^ S.params.logFinalPolyLen) S.params.numQueries
      (S.deepWords T l.1 l.2 P τ α Q ζ o a) δ loss (Nat.two_pow_pos _) loss.coe_nonneg le_rfl
      S.domainSetup.domain (S.domainSetup.friSchedule S.friHeights) 0
      (S.deepWords T l.1 l.2 P τ α Q ζ o a _) Finset.univ).trans (le_of_eq ?_)
    simp only [Iop.Setup.friBound, Fri.Interaction.threshold, zero_add]
  change (⨆ T : S.TraceMessage, (S.lookupError δ' + ⨆ l : 𝕂 × 𝕂, ⨆ P : S.PermMessage,
    ⨆ τ : Fin S.k → 𝕂, (foldingError (S.instanceSetup (S.failingOf publicValues δ' T l P τ)) δ' +
      ⨆ α : 𝕂, ⨆ Q : S.QuotientMessage,
        (outOfDomainError (S.instanceSetup (S.failingOf publicValues δ' T l P τ)) δ' +
          ⨆ ζ : 𝕂, ⨆ o : S.OpeningsMessage,
            (batchingErrorOf (S.instanceSetup (S.failingOf publicValues δ' T l P τ))
              (S.groupNumOpened (S.logN (S.failingOf publicValues δ' T l P τ) +
                S.params.logBlowup)) δ δ' + ⨆ a : 𝕂,
              RoundExtractor.ChallengeSchedule.maxError S.friProtocol.roles
                (S.friCertificate publicValues δ T l P τ α Q ζ o a loss).challenges))))) ≤ _
  refine iSup_le fun T ↦ ?_
  rw [add_assoc]
  refine add_le_add le_rfl (iSup₂_le fun l P ↦ iSup_le fun τ ↦ ?_)
  refine le_trans ?_ (add_le_add (le_iSup (fun i ↦ S.instanceError δ δ' i)
    (S.failingOf publicValues δ' T l P τ)) le_rfl)
  rw [instanceError, add_assoc, add_assoc]
  refine add_le_add le_rfl (iSup₂_le fun α Q ↦ add_le_add le_rfl (iSup₂_le fun ζ o ↦
    add_le_add le_rfl (iSup_le fun a ↦ hfri T l P τ α Q ζ o a)))

/-! ### The verifier's challenge laws -/

section Samples
variable (impl : QueryImpl (OracleSpec.ofPFunctor S.quotientAccess) Id)

set_option backward.isDefEq.respectTransparency false in
theorem samples_fri (T : S.TraceMessage) (l : 𝕂 × 𝕂) (P : S.PermMessage)
    (τ : Fin S.k → 𝕂) (α : 𝕂) (Q : S.QuotientMessage) (ζ : 𝕂) (o : S.OpeningsMessage) (a : 𝕂)
    (loss : ℝ≥0) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.friProtocol.tree S.friProtocol.roles
      S.friProtocol.oracles S.quotientAccess impl _
      (S.friVerifier publicValues l.1 l.2 τ α ζ o a)
      (S.friCertificate publicValues δ T l P τ α Q ζ o a loss).challenges :=
  samplesChallenges_mapOutput unifSpec (QueryImpl.id' unifSpec) _ _ _ _ _ _ _ _ _ _
    (Fri.Interaction.samplesChallenges_verifier (S.logN S.top + S.params.logBlowup)
      (2 ^ S.params.logFinalPolyLen) S.params.numQueries
      (S.deepWords T l.1 l.2 P τ α Q ζ o a) δ loss (Nat.two_pow_pos _) loss.coe_nonneg
      (S.domainSetup.friSchedule S.friHeights) le_rfl S.domainSetup.domain _ _ _ 0
      (S.deepWords T l.1 l.2 P τ α Q ζ o a _) Finset.univ)

set_option backward.isDefEq.respectTransparency false in
theorem samples_afterOpenings (lα lβ : 𝕂) (τ : Fin S.k → 𝕂) (α ζ : 𝕂) (o : S.OpeningsMessage)
    (schedule : RoundExtractor.ChallengeSchedule S.afterOpenings.tree S.afterOpenings.roles)
    (hsample : schedule.1.1 = $ᵗ 𝕂)
    (hrest : ∀ a, SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.friProtocol.tree
      S.friProtocol.roles S.friProtocol.oracles S.quotientAccess impl _
      (S.friVerifier publicValues lα lβ τ α ζ o a) (schedule.2 a)) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.afterOpenings.tree
      S.afterOpenings.roles S.afterOpenings.oracles S.quotientAccess impl _
      (S.verifierAfterOpenings publicValues lα lβ τ α ζ o) schedule := by
  refine ⟨fun event ↦ ?_, fun chosen hchosen ↦ ?_⟩
  · simp only [simulateQ_id', verifierAfterOpenings, simulateQ_bind, simulateQ_pure]
    erw [Fri.Interaction.simulateQ_liftAccessImpl_liftComp]
    rw [bind_pure_comp, prEvent_map, hsample]
  simp only [simulateQ_id', verifierAfterOpenings, simulateQ_bind, simulateQ_pure] at hchosen
  erw [Fri.Interaction.simulateQ_liftAccessImpl_liftComp] at hchosen
  obtain ⟨a, -, hchosen⟩ := support_bind_exists hchosen
  rw [mem_support_pure_iff] at hchosen
  subst hchosen
  exact hrest a

set_option backward.isDefEq.respectTransparency false in
theorem samples_afterZeta (lα lβ : 𝕂) (τ : Fin S.k → 𝕂) (α ζ : 𝕂)
    (schedule : RoundExtractor.ChallengeSchedule S.afterZeta.tree S.afterZeta.roles)
    (hrest : ∀ o, SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.afterOpenings.tree
      S.afterOpenings.roles S.afterOpenings.oracles S.quotientAccess impl _
      (S.verifierAfterOpenings publicValues lα lβ τ α ζ o) (schedule.2 o)) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.afterZeta.tree S.afterZeta.roles
      S.afterZeta.oracles S.quotientAccess impl _
      (S.verifierAfterZeta publicValues lα lβ τ α ζ) schedule := by
  intro o after hafter
  rw [simulateQ_id', verifierAfterZeta, simulateQ_pure, mem_support_pure_iff] at hafter
  subst hafter
  exact hrest o

set_option backward.isDefEq.respectTransparency false in
theorem samples_afterQuotient (lα lβ : 𝕂) (τ : Fin S.k → 𝕂) (α : 𝕂)
    (schedule : RoundExtractor.ChallengeSchedule S.afterQuotient.tree S.afterQuotient.roles)
    (hsample : schedule.1.1 = $ᵗ 𝕂)
    (hrest : ∀ ζ, SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.afterZeta.tree
      S.afterZeta.roles S.afterZeta.oracles S.quotientAccess impl _
      (S.verifierAfterZeta publicValues lα lβ τ α ζ) (schedule.2 ζ)) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.afterQuotient.tree
      S.afterQuotient.roles S.afterQuotient.oracles S.quotientAccess impl _
      (S.verifierAfterQuotient publicValues lα lβ τ α) schedule := by
  refine ⟨fun event ↦ ?_, fun chosen hchosen ↦ ?_⟩
  · simp only [simulateQ_id', verifierAfterQuotient, simulateQ_bind, simulateQ_pure]
    erw [Fri.Interaction.simulateQ_liftAccessImpl_liftComp]
    rw [bind_pure_comp, prEvent_map, hsample]
  simp only [simulateQ_id', verifierAfterQuotient, simulateQ_bind, simulateQ_pure] at hchosen
  erw [Fri.Interaction.simulateQ_liftAccessImpl_liftComp] at hchosen
  obtain ⟨ζ, -, hchosen⟩ := support_bind_exists hchosen
  rw [mem_support_pure_iff] at hchosen
  subst hchosen
  exact hrest ζ

end Samples

section SamplesPerm
variable (impl : QueryImpl (OracleSpec.ofPFunctor S.permAccess) Id)

set_option backward.isDefEq.respectTransparency false in
theorem samples_afterAlpha (lα lβ : 𝕂) (τ : Fin S.k → 𝕂) (α : 𝕂)
    (schedule : RoundExtractor.ChallengeSchedule S.afterAlpha.tree S.afterAlpha.roles)
    (hrest : ∀ Q, SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.afterQuotient.tree
      S.afterQuotient.roles S.afterQuotient.oracles S.quotientAccess
      (Access.extendImpl S.permAccess OracleInterface.instFunction impl Q) _
      (S.verifierAfterQuotient publicValues lα lβ τ α) (schedule Q)) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.afterAlpha.tree S.afterAlpha.roles
      S.afterAlpha.oracles S.permAccess impl _ (S.verifierAfterAlpha publicValues lα lβ τ α)
      schedule := by
  intro Q after hafter
  rw [simulateQ_id', verifierAfterAlpha, simulateQ_pure, mem_support_pure_iff] at hafter
  subst hafter
  exact hrest Q

set_option backward.isDefEq.respectTransparency false in
theorem samples_afterTerminals (lα lβ : 𝕂) (τ : Fin S.k → 𝕂)
    (schedule : RoundExtractor.ChallengeSchedule S.afterTerminals.tree S.afterTerminals.roles)
    (hsample : schedule.1.1 = $ᵗ 𝕂)
    (hrest : ∀ α, SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.afterAlpha.tree
      S.afterAlpha.roles S.afterAlpha.oracles S.permAccess impl _
      (S.verifierAfterAlpha publicValues lα lβ τ α) (schedule.2 α)) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.afterTerminals.tree
      S.afterTerminals.roles S.afterTerminals.oracles S.permAccess impl _
      (S.verifierAfterTerminals publicValues lα lβ τ) schedule := by
  refine ⟨fun event ↦ ?_, fun chosen hchosen ↦ ?_⟩
  · simp only [simulateQ_id', verifierAfterTerminals, simulateQ_bind, simulateQ_pure]
    erw [Fri.Interaction.simulateQ_liftAccessImpl_liftComp]
    rw [bind_pure_comp, prEvent_map, hsample]
  simp only [simulateQ_id', verifierAfterTerminals, simulateQ_bind, simulateQ_pure] at hchosen
  erw [Fri.Interaction.simulateQ_liftAccessImpl_liftComp] at hchosen
  obtain ⟨α, -, hchosen⟩ := support_bind_exists hchosen
  rw [mem_support_pure_iff] at hchosen
  subst hchosen
  exact hrest α

set_option backward.isDefEq.respectTransparency false in
theorem samples_afterPerm (lα lβ : 𝕂)
    (schedule : RoundExtractor.ChallengeSchedule S.afterPerm.tree S.afterPerm.roles)
    (hrest : ∀ τ, SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.afterTerminals.tree
      S.afterTerminals.roles S.afterTerminals.oracles S.permAccess impl _
      (S.verifierAfterTerminals publicValues lα lβ τ) (schedule.2 τ)) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.afterPerm.tree S.afterPerm.roles
      S.afterPerm.oracles S.permAccess impl _ (S.verifierAfterPerm publicValues lα lβ)
      schedule := by
  intro τ after hafter
  rw [simulateQ_id', verifierAfterPerm, simulateQ_pure, mem_support_pure_iff] at hafter
  subst hafter
  exact hrest τ

end SamplesPerm

section SamplesTrace
variable (impl : QueryImpl (OracleSpec.ofPFunctor S.traceAccess) Id)

set_option backward.isDefEq.respectTransparency false in
theorem samples_afterLookup (lα lβ : 𝕂)
    (schedule : RoundExtractor.ChallengeSchedule S.afterLookup.tree S.afterLookup.roles)
    (hrest : ∀ P, SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.afterPerm.tree
      S.afterPerm.roles S.afterPerm.oracles S.permAccess
      (Access.extendImpl S.traceAccess OracleInterface.instFunction impl P) _
      (S.verifierAfterPerm publicValues lα lβ) (schedule P)) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.afterLookup.tree S.afterLookup.roles
      S.afterLookup.oracles S.traceAccess impl _ (S.verifierAfterLookup publicValues lα lβ)
      schedule := by
  intro P after hafter
  rw [simulateQ_id', verifierAfterLookup, simulateQ_pure, mem_support_pure_iff] at hafter
  subst hafter
  exact hrest P

set_option backward.isDefEq.respectTransparency false in
theorem samples_afterTrace
    (schedule : RoundExtractor.ChallengeSchedule S.afterTrace.tree S.afterTrace.roles)
    (hsample : schedule.1.1 = $ᵗ (𝕂 × 𝕂))
    (hrest : ∀ l : 𝕂 × 𝕂, SamplesChallenges unifSpec (QueryImpl.id' unifSpec)
      S.afterLookup.tree S.afterLookup.roles S.afterLookup.oracles S.traceAccess impl _
      (S.verifierAfterLookup publicValues l.1 l.2) (schedule.2 l)) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.afterTrace.tree S.afterTrace.roles
      S.afterTrace.oracles S.traceAccess impl _ (S.verifierAfterTrace publicValues) schedule := by
  refine ⟨fun event ↦ ?_, fun chosen hchosen ↦ ?_⟩
  · simp only [simulateQ_id', verifierAfterTrace, simulateQ_bind, simulateQ_pure]
    erw [Fri.Interaction.simulateQ_liftAccessImpl_liftComp]
    rw [bind_pure_comp, prEvent_map, hsample]
  simp only [simulateQ_id', verifierAfterTrace, simulateQ_bind, simulateQ_pure] at hchosen
  erw [Fri.Interaction.simulateQ_liftAccessImpl_liftComp] at hchosen
  obtain ⟨l, -, hchosen⟩ := support_bind_exists hchosen
  rw [mem_support_pure_iff] at hchosen
  subst hchosen
  exact hrest l

end SamplesTrace

set_option backward.isDefEq.respectTransparency false in
/-- The verifier samples its challenges as the certificate's challenge programs. -/
theorem samplesChallenges_verifier (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.protocol.tree S.protocol.roles
      S.protocol.oracles noAccess noImpl _ (S.verifier publicValues)
      (S.certificate publicValues δ δ' hδ' loss).challenges := by
  intro T after hafter
  rw [simulateQ_id', verifier, simulateQ_pure, mem_support_pure_iff] at hafter
  subst hafter
  exact S.samples_afterTrace publicValues _ _ rfl fun l ↦
    S.samples_afterLookup publicValues _ l.1 l.2 _ fun P ↦
      S.samples_afterPerm publicValues _ l.1 l.2 _ fun τ ↦
        S.samples_afterTerminals publicValues _ l.1 l.2 τ _ rfl fun α ↦
          S.samples_afterAlpha publicValues _ l.1 l.2 τ α _ fun Q ↦
            S.samples_afterQuotient publicValues _ l.1 l.2 τ α _ rfl fun ζ ↦
              S.samples_afterZeta publicValues _ l.1 l.2 τ α ζ _ fun o ↦
                S.samples_afterOpenings publicValues _ l.1 l.2 τ α ζ o _ rfl fun a ↦
                  S.samples_fri publicValues δ _ T l P τ α Q ζ o a loss

/-! ### The verifier's terminal law -/

/-- The certificate's terminal state is FRI's, on the batched DEEP words of the path's messages. -/
theorem terminalState_certificate (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0)
    (path : S.protocol.tree.ExecutionPath) :
    (S.certificate publicValues δ δ' hδ' loss).extractor.terminalState path =
      (S.friCertificate publicValues δ path.1 path.2.1 path.2.2.1 path.2.2.2.1 path.2.2.2.2.1
        path.2.2.2.2.2.1 path.2.2.2.2.2.2.1 path.2.2.2.2.2.2.2.1 path.2.2.2.2.2.2.2.2.1
        loss).extractor.terminalState path.2.2.2.2.2.2.2.2.2 := rfl

/-- The extractor's input witness is the path's trace message, with traces. -/
theorem extractWitness_fst (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0)
    (path : S.protocol.tree.ExecutionPath)
    (w : ((S.certificate publicValues δ δ' hδ' loss).extractor.terminalState path).Witness) :
    ((S.certificate publicValues δ δ' hδ' loss).extractor.extractWitness path w).1 = path.1 :=
  rfl

section Terminal
variable (loss : ℝ≥0)

set_option backward.isDefEq.respectTransparency false in
theorem terminal_fri (T : S.TraceMessage) (l : 𝕂 × 𝕂) (P : S.PermMessage) (τ : Fin S.k → 𝕂)
    (α : 𝕂) (Q : S.QuotientMessage) (ζ : 𝕂) (o : S.OpeningsMessage) (a : 𝕂)
    {OutP : S.friProtocol.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.friProtocol.tree
      S.friProtocol.roles OutP) :
    ∀ result ∈ support (executeStrategies unifSpec S.friProtocol.tree S.friProtocol.roles
      S.friProtocol.oracles S.quotientAccess (S.messagesImpl T P Q) prover
      (S.friVerifier publicValues l.1 l.2 τ α ζ o a)), result.2.2 = true →
      ∃ w, ((S.friCertificate publicValues δ T l P τ α Q ζ o a loss).extractor.terminalState
        result.1).holds w := by
  intro result hres hacc
  rw [execute_fri, support_map] at hres
  obtain ⟨r, hr, rfl⟩ := hres
  have hacc' : @decide _ (Classical.propDecidable (S.Checks publicValues l.1 l.2 τ α ζ o)) =
      true ∧ r.2.2 = true := Bool.and_eq_true _ _ ▸ hacc
  obtain ⟨w, hw⟩ := Fri.Interaction.terminal_holds_of_accepts
    (S.logN S.top + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen) S.params.numQueries
    (S.deepWords T l.1 l.2 P τ α Q ζ o a) δ loss unifSpec (Nat.two_pow_pos _) loss.coe_nonneg
    _ _ (S.domainSetup.friSchedule S.friHeights) le_rfl S.domainSetup.domain _ _ _ 0
    (S.deepWords T l.1 l.2 P τ α Q ζ o a _) Finset.univ prover
    (S.reads_deepReader T l.1 l.2 P τ α Q ζ o a)
    (fun x ↦ by simp only [Finset.mem_univ, decide_true]; rfl) r hr hacc'.2
  simp only [friCertificate, gateCertificate]
  rw [terminalState_gateExtractor]
  exact ⟨w, @of_decide_eq_true _ (Classical.propDecidable _) hacc'.1, hw⟩

set_option backward.isDefEq.respectTransparency false in
theorem terminal_afterOpenings (T : S.TraceMessage) (l : 𝕂 × 𝕂) (P : S.PermMessage)
    (τ : Fin S.k → 𝕂) (α : 𝕂) (Q : S.QuotientMessage) (ζ : 𝕂) (o : S.OpeningsMessage)
    {OutP : S.afterOpenings.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.afterOpenings.tree
      S.afterOpenings.roles OutP) :
    ∀ result ∈ support (executeStrategies unifSpec S.afterOpenings.tree S.afterOpenings.roles
      S.afterOpenings.oracles S.quotientAccess (S.messagesImpl T P Q) prover
      (S.verifierAfterOpenings publicValues l.1 l.2 τ α ζ o)), result.2.2 = true →
      ∃ w, ((S.friCertificate publicValues δ T l P τ α Q ζ o result.1.1
        loss).extractor.terminalState result.1.2).holds w := by
  intro result hres hacc
  rw [execute_afterOpenings] at hres
  obtain ⟨a, -, hres⟩ := support_bind_exists hres
  obtain ⟨p, -, hres⟩ := support_bind_exists hres
  obtain ⟨r, hr, hres⟩ := support_bind_exists hres
  rw [mem_support_pure_iff] at hres
  subst hres
  exact S.terminal_fri publicValues δ loss T l P τ α Q ζ o a (OutP := fun path ↦ OutP ⟨a, path⟩)
    p r hr hacc

set_option backward.isDefEq.respectTransparency false in
theorem terminal_afterZeta (T : S.TraceMessage) (l : 𝕂 × 𝕂) (P : S.PermMessage)
    (τ : Fin S.k → 𝕂) (α : 𝕂) (Q : S.QuotientMessage) (ζ : 𝕂)
    {OutP : S.afterZeta.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.afterZeta.tree
      S.afterZeta.roles OutP) :
    ∀ result ∈ support (executeStrategies unifSpec S.afterZeta.tree S.afterZeta.roles
      S.afterZeta.oracles S.quotientAccess (S.messagesImpl T P Q) prover
      (S.verifierAfterZeta publicValues l.1 l.2 τ α ζ)), result.2.2 = true →
      ∃ w, ((S.friCertificate publicValues δ T l P τ α Q ζ result.1.1 result.1.2.1
        loss).extractor.terminalState result.1.2.2).holds w := by
  intro result hres hacc
  rw [execute_afterZeta] at hres
  obtain ⟨chosen, -, hres⟩ := support_bind_exists hres
  obtain ⟨r, hr, hres⟩ := support_bind_exists hres
  rw [mem_support_pure_iff] at hres
  subst hres
  exact S.terminal_afterOpenings publicValues δ loss T l P τ α Q ζ chosen.1
    (OutP := fun path ↦ OutP ⟨chosen.1, path⟩) chosen.2 r hr hacc

set_option backward.isDefEq.respectTransparency false in
theorem terminal_afterQuotient (T : S.TraceMessage) (l : 𝕂 × 𝕂) (P : S.PermMessage)
    (τ : Fin S.k → 𝕂) (α : 𝕂) (Q : S.QuotientMessage)
    {OutP : S.afterQuotient.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.afterQuotient.tree
      S.afterQuotient.roles OutP) :
    ∀ result ∈ support (executeStrategies unifSpec S.afterQuotient.tree S.afterQuotient.roles
      S.afterQuotient.oracles S.quotientAccess (S.messagesImpl T P Q) prover
      (S.verifierAfterQuotient publicValues l.1 l.2 τ α)), result.2.2 = true →
      ∃ w, ((S.friCertificate publicValues δ T l P τ α Q result.1.1 result.1.2.1 result.1.2.2.1
        loss).extractor.terminalState result.1.2.2.2).holds w := by
  intro result hres hacc
  rw [execute_afterQuotient] at hres
  obtain ⟨ζ, -, hres⟩ := support_bind_exists hres
  obtain ⟨p, -, hres⟩ := support_bind_exists hres
  obtain ⟨r, hr, hres⟩ := support_bind_exists hres
  rw [mem_support_pure_iff] at hres
  subst hres
  exact S.terminal_afterZeta publicValues δ loss T l P τ α Q ζ (OutP := fun path ↦ OutP ⟨ζ, path⟩)
    p r hr hacc

set_option backward.isDefEq.respectTransparency false in
theorem terminal_afterAlpha (T : S.TraceMessage) (l : 𝕂 × 𝕂) (P : S.PermMessage)
    (τ : Fin S.k → 𝕂) (α : 𝕂) {OutP : S.afterAlpha.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.afterAlpha.tree
      S.afterAlpha.roles OutP) :
    ∀ result ∈ support (executeStrategies unifSpec S.afterAlpha.tree S.afterAlpha.roles
      S.afterAlpha.oracles S.permAccess
      (Access.extendImpl S.traceAccess OracleInterface.instFunction
        (Access.extendImpl noAccess OracleInterface.instFunction noImpl T) P) prover
      (S.verifierAfterAlpha publicValues l.1 l.2 τ α)), result.2.2 = true →
      ∃ w, ((S.friCertificate publicValues δ T l P τ α result.1.1 result.1.2.1 result.1.2.2.1
        result.1.2.2.2.1 loss).extractor.terminalState result.1.2.2.2.2).holds w := by
  intro result hres hacc
  rw [execute_afterAlpha] at hres
  obtain ⟨chosen, -, hres⟩ := support_bind_exists hres
  obtain ⟨r, hr, hres⟩ := support_bind_exists hres
  rw [mem_support_pure_iff] at hres
  subst hres
  exact S.terminal_afterQuotient publicValues δ loss T l P τ α chosen.1
    (OutP := fun path ↦ OutP ⟨chosen.1, path⟩) chosen.2 r hr hacc

set_option backward.isDefEq.respectTransparency false in
theorem terminal_afterTerminals (T : S.TraceMessage) (l : 𝕂 × 𝕂) (P : S.PermMessage)
    (τ : Fin S.k → 𝕂) {OutP : S.afterTerminals.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.afterTerminals.tree
      S.afterTerminals.roles OutP) :
    ∀ result ∈ support (executeStrategies unifSpec S.afterTerminals.tree S.afterTerminals.roles
      S.afterTerminals.oracles S.permAccess
      (Access.extendImpl S.traceAccess OracleInterface.instFunction
        (Access.extendImpl noAccess OracleInterface.instFunction noImpl T) P) prover
      (S.verifierAfterTerminals publicValues l.1 l.2 τ)), result.2.2 = true →
      ∃ w, ((S.friCertificate publicValues δ T l P τ result.1.1 result.1.2.1 result.1.2.2.1
        result.1.2.2.2.1 result.1.2.2.2.2.1 loss).extractor.terminalState
          result.1.2.2.2.2.2).holds w := by
  intro result hres hacc
  rw [execute_afterTerminals] at hres
  obtain ⟨α, -, hres⟩ := support_bind_exists hres
  obtain ⟨p, -, hres⟩ := support_bind_exists hres
  obtain ⟨r, hr, hres⟩ := support_bind_exists hres
  rw [mem_support_pure_iff] at hres
  subst hres
  exact S.terminal_afterAlpha publicValues δ loss T l P τ α (OutP := fun path ↦ OutP ⟨α, path⟩)
    p r hr hacc

set_option backward.isDefEq.respectTransparency false in
theorem terminal_afterPerm (T : S.TraceMessage) (l : 𝕂 × 𝕂) (P : S.PermMessage)
    {OutP : S.afterPerm.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.afterPerm.tree
      S.afterPerm.roles OutP) :
    ∀ result ∈ support (executeStrategies unifSpec S.afterPerm.tree S.afterPerm.roles
      S.afterPerm.oracles S.permAccess
      (Access.extendImpl S.traceAccess OracleInterface.instFunction
        (Access.extendImpl noAccess OracleInterface.instFunction noImpl T) P) prover
      (S.verifierAfterPerm publicValues l.1 l.2)), result.2.2 = true →
      ∃ w, ((S.friCertificate publicValues δ T l P result.1.1 result.1.2.1 result.1.2.2.1
        result.1.2.2.2.1 result.1.2.2.2.2.1 result.1.2.2.2.2.2.1 loss).extractor.terminalState
          result.1.2.2.2.2.2.2).holds w := by
  intro result hres hacc
  rw [execute_afterPerm] at hres
  obtain ⟨chosen, -, hres⟩ := support_bind_exists hres
  obtain ⟨r, hr, hres⟩ := support_bind_exists hres
  rw [mem_support_pure_iff] at hres
  subst hres
  exact S.terminal_afterTerminals publicValues δ loss T l P chosen.1
    (OutP := fun path ↦ OutP ⟨chosen.1, path⟩) chosen.2 r hr hacc

set_option backward.isDefEq.respectTransparency false in
theorem terminal_afterLookup (T : S.TraceMessage) (l : 𝕂 × 𝕂)
    {OutP : S.afterLookup.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.afterLookup.tree
      S.afterLookup.roles OutP) :
    ∀ result ∈ support (executeStrategies unifSpec S.afterLookup.tree S.afterLookup.roles
      S.afterLookup.oracles S.traceAccess
      (Access.extendImpl noAccess OracleInterface.instFunction noImpl T) prover
      (S.verifierAfterLookup publicValues l.1 l.2)), result.2.2 = true →
      ∃ w, ((S.friCertificate publicValues δ T l result.1.1 result.1.2.1 result.1.2.2.1
        result.1.2.2.2.1 result.1.2.2.2.2.1 result.1.2.2.2.2.2.1 result.1.2.2.2.2.2.2.1
        loss).extractor.terminalState result.1.2.2.2.2.2.2.2).holds w := by
  intro result hres hacc
  rw [execute_afterLookup] at hres
  obtain ⟨chosen, -, hres⟩ := support_bind_exists hres
  obtain ⟨r, hr, hres⟩ := support_bind_exists hres
  rw [mem_support_pure_iff] at hres
  subst hres
  exact S.terminal_afterPerm publicValues δ loss T l chosen.1
    (OutP := fun path ↦ OutP ⟨chosen.1, path⟩) chosen.2 r hr hacc

set_option backward.isDefEq.respectTransparency false in
theorem terminal_afterTrace (T : S.TraceMessage)
    {OutP : S.afterTrace.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.afterTrace.tree
      S.afterTrace.roles OutP) :
    ∀ result ∈ support (executeStrategies unifSpec S.afterTrace.tree S.afterTrace.roles
      S.afterTrace.oracles S.traceAccess
      (Access.extendImpl noAccess OracleInterface.instFunction noImpl T) prover
      (S.verifierAfterTrace publicValues)), result.2.2 = true →
      ∃ w, ((S.friCertificate publicValues δ T result.1.1 result.1.2.1 result.1.2.2.1
        result.1.2.2.2.1 result.1.2.2.2.2.1 result.1.2.2.2.2.2.1 result.1.2.2.2.2.2.2.1
        result.1.2.2.2.2.2.2.2.1 loss).extractor.terminalState
          result.1.2.2.2.2.2.2.2.2).holds w := by
  intro result hres hacc
  rw [execute_afterTrace] at hres
  obtain ⟨l, -, hres⟩ := support_bind_exists hres
  obtain ⟨p, -, hres⟩ := support_bind_exists hres
  obtain ⟨r, hr, hres⟩ := support_bind_exists hres
  rw [mem_support_pure_iff] at hres
  subst hres
  exact S.terminal_afterLookup publicValues δ loss T l (OutP := fun path ↦ OutP ⟨l, path⟩)
    p r hr hacc

set_option backward.isDefEq.respectTransparency false in
/-- An accepting run reaches a terminal state of the certificate that holds. -/
theorem terminal_holds_of_accepts (hδ' : (δ' : ℝ) < 1 - S.rate)
    {OutP : S.protocol.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.protocol.tree
      S.protocol.roles OutP) :
    ∀ result ∈ support (executeStrategies unifSpec S.protocol.tree S.protocol.roles
      S.protocol.oracles noAccess noImpl prover (S.verifier publicValues)), result.2.2 = true →
      ∃ w, ((S.certificate publicValues δ δ' hδ' loss).extractor.terminalState
        result.1).holds w := by
  intro result hres hacc
  rw [terminalState_certificate]
  rw [execute_protocol] at hres
  obtain ⟨chosen, -, hres⟩ := support_bind_exists hres
  obtain ⟨r, hr, hres⟩ := support_bind_exists hres
  rw [mem_support_pure_iff] at hres
  subst hres
  exact S.terminal_afterTrace publicValues δ loss chosen.1
    (OutP := fun path ↦ OutP ⟨chosen.1, path⟩) chosen.2 r hr hacc

end Terminal

/-- **Knowledge soundness of the batch at its lengths, at a proximity loss.** -/
theorem extraction_le (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0)
    {OutP : S.protocol.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.protocol.tree
      S.protocol.roles OutP) :
    Pr{let result ← (executeStrategies unifSpec S.protocol.tree S.protocol.roles
      S.protocol.oracles noAccess noImpl prover (S.verifier publicValues))}[
        result.2.2 = true ∧ S.Far publicValues δ' result.1.1] ≤
      S.lookupError δ' + (⨆ i, S.instanceError δ δ' i) +
        S.domainSetup.friBound S.friHeights δ loss := by
  have key := (S.certificate publicValues δ δ' hδ' loss).executeStrategies_extraction_le unifSpec
    (QueryImpl.id' unifSpec) S.protocol.oracles noAccess noImpl prover (S.verifier publicValues)
    (S.samplesChallenges_verifier publicValues δ δ' hδ' loss)
  rw [simulateQ_id'] at key
  refine (prEvent_mono_of_support _ _ _ fun result hresult h ↦ ?_).trans
    (key.trans (S.maxError_certificate publicValues δ δ' hδ' loss))
  obtain ⟨hacc, hfar⟩ := h
  obtain ⟨w, hw⟩ := S.terminal_holds_of_accepts publicValues δ δ' loss hδ' prover result hresult
    hacc
  exact ⟨w, hw, fun hroot ↦ hfar _ hroot.1 hroot.2⟩

/-- **Knowledge soundness of the batch at its lengths.** Against any prover, the verifier accepts
while no tuple of traces close to the committed ones satisfies the batch with probability at most
the knowledge error. -/
theorem extraction_le_knowledgeError (hδ' : (δ' : ℝ) < 1 - S.rate)
    {OutP : S.protocol.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.protocol.tree
      S.protocol.roles OutP) :
    Pr{let result ← (executeStrategies unifSpec S.protocol.tree S.protocol.roles
      S.protocol.oracles noAccess noImpl prover (S.verifier publicValues))}[
        result.2.2 = true ∧ S.Far publicValues δ' result.1.1] ≤ knowledgeError S δ δ' := by
  rw [knowledgeError, friErrorWith_eq, Fri.Interaction.error, ENNReal.add_iInf]
  exact le_iInf fun loss ↦ S.extraction_le publicValues δ δ' hδ' loss prover

end Setup

/-! ### Statements -/

namespace Statement
variable (C : Statement F) (EF : Type) [Challenge F EF] (publicValues : Fin C.k → List F)
  (δ δ' : (Fin C.k → ℕ) → ℝ≥0)

/-- No tuple of traces close to an execution's committed traces satisfies the batch at its
lengths. -/
def Far (path : (C.protocol EF).tree.ExecutionPath) : Prop :=
  (C.setup EF path.1).Far publicValues (δ' (path.1 : C.Length).1) path.2.1

/-- The batch's error at lengths, but FRI's at the proximity loss `loss`. -/
noncomputable def lengthBound (n : C.Length) (loss : ℝ≥0) : ENNReal :=
  (C.setup EF n).lookupError (δ' n) + (⨆ i, (C.setup EF n).instanceError (δ n) (δ' n) i) +
    (C.setup EF n).domainSetup.friBound (C.setup EF n).friHeights (δ n) loss

set_option backward.isDefEq.respectTransparency false in
/-- **Knowledge soundness of the batch for a statement, at proximity losses.** Against any
prover, the verifier accepts while no tuple of traces close to the committed ones satisfies the
batch at the claimed lengths with probability at most the largest over the lengths of the batch's
errors there, FRI's at the proximity loss `loss n`: whatever lengths the prover sends, the batch's
certificate there bounds the rest. -/
theorem extraction_le (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate)
    (loss : C.Length → ℝ≥0) {OutP : (C.protocol EF).tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec (C.protocol EF).tree
      (C.protocol EF).roles OutP) :
    Pr{let result ← (executeStrategies unifSpec (C.protocol EF).tree (C.protocol EF).roles
      (C.protocol EF).oracles noAccess noImpl prover (C.verifier EF publicValues))}[
        result.2.2 = true ∧ C.Far EF publicValues δ' result.1] ≤
      ⨆ n, C.lengthBound EF δ δ' n (loss n) := by
  rw [execute_protocol]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun chosen _ ↦ ?_
  rw [bind_pure_comp, prEvent_map]
  exact ((C.setup EF chosen.1).extraction_le publicValues (δ (chosen.1 : C.Length).1)
    (δ' (chosen.1 : C.Length).1) (hδ' (chosen.1 : C.Length).1 (chosen.1 : C.Length).2)
    (loss chosen.1) (OutP := fun path ↦ OutP ⟨chosen.1, path⟩) chosen.2).trans
    (le_iSup (fun n ↦ C.lengthBound EF δ δ' n (loss n)) chosen.1)

/-- **Knowledge soundness of the batch for a statement.** Against any prover, the verifier accepts
while no tuple of traces close to the committed ones satisfies the batch at the claimed lengths
with probability at most the statement's knowledge error. -/
theorem extraction_le_knowledgeError (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate)
    {OutP : (C.protocol EF).tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec (C.protocol EF).tree
      (C.protocol EF).roles OutP) :
    Pr{let result ← (executeStrategies unifSpec (C.protocol EF).tree (C.protocol EF).roles
      (C.protocol EF).oracles noAccess noImpl prover (C.verifier EF publicValues))}[
        result.2.2 = true ∧ C.Far EF publicValues δ' result.1] ≤ C.knowledgeError EF δ δ' := by
  have hK : C.knowledgeError EF δ δ' = ⨆ n : C.Length,
      Batch.knowledgeError (C.setup EF n) (δ n) (δ' n) := by
    rw [Statement.knowledgeError, iSup_subtype']
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt ↦ ?_
  have hloss (n : C.Length) : ∃ loss,
      (C.setup EF n).domainSetup.friBound (C.setup EF n).friHeights (δ n) loss ≤
        friErrorWith (C.setup EF n).domainSetup (C.setup EF n).friHeights (δ n) + ε := by
    have hfin : friErrorWith (C.setup EF n).domainSetup (C.setup EF n).friHeights (δ n) < ⊤ := by
      refine lt_of_le_of_lt (le_trans (le_add_self) (le_iSup (fun n : C.Length ↦
        Batch.knowledgeError (C.setup EF n) (δ n) (δ' n)) n)) (hK ▸ hlt)
    rw [friErrorWith_eq, Fri.Interaction.error] at hfin ⊢
    obtain ⟨loss, hl⟩ := iInf_lt_iff.mp (ENNReal.lt_add_right hfin.ne
      (ENNReal.coe_ne_zero.mpr hε.ne'))
    exact ⟨loss, hl.le⟩
  choose loss hl using hloss
  refine (C.extraction_le EF publicValues δ δ' hδ' loss prover).trans ?_
  rw [hK]
  refine iSup_le fun n ↦ ?_
  refine le_trans ?_ (add_le_add (le_iSup (fun n : C.Length ↦
    Batch.knowledgeError (C.setup EF n) (δ n) (δ' n)) n) le_rfl)
  rw [lengthBound, Batch.knowledgeError, add_assoc _ (friErrorWith _ _ _)]
  exact add_le_add le_rfl (hl n)

end Statement

end CompStark.Iop.Batch
