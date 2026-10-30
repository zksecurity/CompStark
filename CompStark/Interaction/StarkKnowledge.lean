/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Interaction.Stark
public import CompStark.Interaction.Gate
public import CompStark.Sound.Rbr

/-! # The STARK's knowledge certificate on the interaction layer

The STARK on ArkLib's interaction layer (`CompStark/Interaction/Stark.lean`) is round-by-round
knowledge sound, with a `KnowledgeCertificate`: the rounds before FRI (`Setup.prefixCertificate`)
appended with `KnowledgeCertificate.append` to FRI's certificate on the DEEP word
(`Fri.Interaction.certificate`), gated by the constraint check at `ζ` (`Setup.friCertificate`).

The extractor reads the trace off the trace oracle: its input witness is the trace message and a
trace (`Setup.rootState`), holding when the trace is close to the committed words and satisfies
the AIR. After the trace message, the state asks for such a trace (`Setup.traceState`). After
that, the states are those of the doomed-transcript argument of `CompStark/Sound/Rbr.lean`: after
`α`, `ζ` and the claimed values they hold unless no close trace satisfies the AIR and the
challenges so far are safe (`alphaDoom`, `zetaDoom`), and after `a` they are FRI's, on the DEEP
word, once the check at `ζ` passes. A challenge is bad only if it is bad in the round's sense:

* `α`: `AlphaBad`, with probability at most `foldingError`;
* `ζ`: `ZetaBad`, with probability at most `outOfDomainError`;
* `a`: `BatchBad`, with probability at most `batchingError` (`not_near_deepWord`: FRI's state on
  the DEEP word holds only if the DEEP word is near the code);
* FRI's rounds, with FRI's errors.

`Setup.extraction_le` bounds the probability that the verifier accepts while no trace close to the
committed one satisfies the AIR by the sum, at every proximity loss, and
`Setup.extraction_le_knowledgeError` by the knowledge error `knowledgeError`. For a statement, the prover first sends the length, and
`Statement.extraction_le_knowledgeError` bounds the same event by the statement's knowledge
error, the largest over the admitted lengths: whatever length the prover sends, the certificate
at that length bounds the rest.
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound CompStark.Interaction _root_.Interaction
open _root_.Interaction.Oracle _root_.Interaction.Oracle.Security OracleComp OracleSpec
open scoped NNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

namespace Setup
variable (S : Setup EF) (publicValues : List F)

/-! ### The rounds before FRI -/

/-- The STARK's rounds before FRI: the trace, `α`, the quotient, `ζ`, the claimed values and
`a`. -/
def prefixProtocol : Protocol :=
  .oracle S.TraceMessage <|
  .public .receiver 𝕂 fun _ ↦
  .oracle S.QuotientMessage <|
  .public .receiver 𝕂 fun _ ↦
  .public .sender (Openings S) fun _ ↦
  .public .receiver 𝕂 fun _ ↦ .done

/-- The STARK is its rounds before FRI, then FRI. -/
theorem protocol_tree :
    S.protocol.tree = PFunctor.FreeM.append S.prefixProtocol.tree
      (fun _ ↦ (S.friProtocol []).tree) := rfl

variable (δ δ' : ℝ≥0)

/-- No trace close to the committed words satisfies the AIR. -/
def Far (T : S.TraceMessage) : Prop :=
  ∀ t ∈ closeTraces S δ' (S.traceWords T), ¬ S.air.Satisfied S.logN t publicValues

/-- The input state: a trace message and a trace close to it satisfying the AIR. -/
def rootState : KnowledgeState where
  Witness := S.TraceMessage × Array F
  holds w := w.2 ∈ closeTraces S δ' (S.traceWords w.1) ∧ S.air.Satisfied S.logN w.2 publicValues

/-- After the trace message `T`: a trace close to it satisfying the AIR. -/
def traceState (T : S.TraceMessage) : KnowledgeState where
  Witness := Array F
  holds t := t ∈ closeTraces S δ' (S.traceWords T) ∧ S.air.Satisfied S.logN t publicValues

/-- A trace close to the trace message satisfying the AIR, if there is one. -/
noncomputable def chooseTrace (T : S.TraceMessage) : Array F :=
  Classical.epsilon fun t : Array F ↦ (S.traceState publicValues δ' T).holds t

/-- The state of a doomed transcript: no witness, holding unless the transcript is doomed. -/
def doomState (doom : Prop) : KnowledgeState := ⟨Unit, fun _ ↦ ¬ doom⟩

/-- Doomed after `α`: no close trace satisfies the AIR, and `α` is safe. -/
def alphaDoom (T : S.TraceMessage) (α : 𝕂) : Prop :=
  S.Far publicValues δ' T ∧ ¬ AlphaBad S publicValues δ' (S.traceWords T) α

/-- Doomed after `ζ`: doomed after `α`, and `ζ` is safe. -/
def zetaDoom (T : S.TraceMessage) (α : 𝕂) (Q : S.QuotientMessage) (ζ : 𝕂) : Prop :=
  S.alphaDoom publicValues δ' T α ∧
    ¬ ZetaBad S publicValues δ' (S.traceWords T) α (S.quotientWords Q) ζ

/-- The DEEP word of the messages and challenges. -/
noncomputable def deepOf (T : S.TraceMessage) (α : 𝕂) (Q : S.QuotientMessage) (ζ : 𝕂)
    (o : Openings S) (a : 𝕂) : S.Point → 𝕂 :=
  deepWord (S.messageProver T Q o) α ζ a

/-- FRI's input state on the DEEP word, at proximity `δ` and proximity loss `loss`, once the check
at `ζ` passes. -/
noncomputable def friState (T : S.TraceMessage) (α : 𝕂) (Q : S.QuotientMessage) (ζ : 𝕂) (o : Openings S)
    (a : 𝕂) (loss : ℝ≥0) : KnowledgeState :=
  gateState (ConstraintsHoldAt S publicValues α ζ o)
    (Fri.Interaction.levelState (S.logN + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
      (S.deepInputs (S.deepOf T α Q ζ o a)) δ loss S.domain (S.friSchedule []) 0
      (S.deepOf T α Q ζ o a) Finset.univ)

/-- The witness maps of the rounds before FRI. -/
noncomputable def prefixExtractor (loss : ℝ≥0) :
    RoundExtractor S.prefixProtocol.tree (S.rootState publicValues δ') :=
  fun T ↦ ⟨S.traceState publicValues δ' T, fun t ↦ (T, t), fun α ↦
    ⟨doomState (S.alphaDoom publicValues δ' T α), fun _ ↦ S.chooseTrace publicValues δ' T,
      fun Q ↦ ⟨doomState (S.alphaDoom publicValues δ' T α), id, fun ζ ↦
        ⟨doomState (S.zetaDoom publicValues δ' T α Q ζ), fun _ ↦ (), fun o ↦
          ⟨doomState (S.zetaDoom publicValues δ' T α Q ζ), id, fun a ↦
            ⟨S.friState publicValues δ T α Q ζ o a loss, fun _ ↦ (), PUnit.unit⟩⟩⟩⟩⟩⟩

/-- The rounds' challenge programs and errors: uniform `α`, `ζ` and `a`, with the folding, the
out-of-domain and the batching error. -/
noncomputable def prefixChallenges :
    RoundExtractor.ChallengeSchedule S.prefixProtocol.tree S.prefixProtocol.roles :=
  fun _ ↦ ⟨($ᵗ 𝕂, foldingError S δ'), fun _ _ ↦ ⟨($ᵗ 𝕂, outOfDomainError S δ'), fun _ ↦
    ⟨PUnit.unit, fun _ ↦ ⟨($ᵗ 𝕂, batchingError S δ δ'), fun _ ↦ PUnit.unit⟩⟩⟩⟩

/-- FRI's state on a word holds only if the word is `δ`-near the code. -/
theorem near_of_levelState (w : S.Point → 𝕂) (loss : ℝ≥0)
    (x : (Fri.Interaction.levelState (S.logN + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
      (S.deepInputs w) δ loss S.domain (S.friSchedule []) 0 w Finset.univ).Witness)
    (hx : (Fri.Interaction.levelState (S.logN + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
      (S.deepInputs w) δ loss S.domain (S.friSchedule []) 0 w Finset.univ).holds x) :
    Near S δ w := by
  obtain ⟨hu, -, hagree, hcard, -⟩ := hx
  rw [S.degree_friSchedule [] (Fri.Interaction.Schedule.fits_nil _ _)] at hu
  have hproj (y : S.Point) : Fri.Interaction.proj (S.logN + S.params.logBlowup) y = y :=
    Fin.ext (Nat.mod_eq_of_lt y.isLt)
  refine ⟨x.1, ?_, x.2, hu, fun i hi ↦ ?_⟩
  · have h : Fri.Interaction.threshold (δ : ℝ) loss 0 = 1 - δ := by
      simp only [Fri.Interaction.threshold, Nat.cast_zero, zero_mul, add_zero]
    rw [h] at hcard
    rw [ge_iff_le, Setup.size, Nat.cast_pow, Nat.cast_ofNat, mul_comm]
    exact hcard
  · have := hagree i hi
    rw [hproj] at this
    exact this.symm

/-- The rounds before FRI preserve knowledge at the prover's messages: the trace message maps a
trace back to itself with the message, and the other messages leave the states unchanged. -/
theorem prefixExtractor_isProverPreserving (loss : ℝ≥0) :
    (S.prefixExtractor publicValues δ δ' loss).IsProverPreserving S.prefixProtocol.roles :=
  ⟨fun _ _ h ↦ h, fun _ ↦ ⟨fun _ h _ ↦ (nomatch h), fun _ ↦ ⟨fun _ _ h ↦ h, fun _ ↦
    ⟨fun _ h _ ↦ (nomatch h), fun _ ↦ ⟨fun _ _ _ h ↦ h, fun _ ↦
      ⟨fun _ h _ ↦ (nomatch h), fun _ ↦ trivial⟩⟩⟩⟩⟩⟩

/-- No close trace satisfies the AIR exactly when the trace state holds for no trace. -/
theorem far_iff (T : S.TraceMessage) :
    S.Far publicValues δ' T ↔ ¬ ∃ t, (S.traceState publicValues δ' T).holds t := by
  constructor
  · rintro hfar ⟨t, ht, hsat⟩
    exact hfar t ht hsat
  · intro h t ht hsat
    exact h ⟨t, ht, hsat⟩

/-- The chosen trace holds unless no close trace satisfies the AIR. -/
theorem chooseTrace_holds (T : S.TraceMessage) (hfar : ¬ S.Far publicValues δ' T) :
    (S.traceState publicValues δ' T).holds (S.chooseTrace publicValues δ' T) := by
  rw [far_iff, not_not] at hfar
  exact Classical.epsilon_spec hfar

/-- Without lookups, a candidate trace and permutation trace hold exactly when the trace satisfies
the AIR. -/
theorem holds_nil_iff (t : Array F) (R : Fin S.permWidth → Fin (Challenge.d EF) → Polynomial F) :
    Holds S publicValues [] 0 t R ↔ S.air.Satisfied S.logN t publicValues :=
  ⟨fun h ↦ h.air, fun h ↦ ⟨h, fun _ hg ↦ absurd hg List.not_mem_nil⟩⟩

/-- The rounds before FRI have their errors at every prefix: a bad `α` is `AlphaBad`, a bad `ζ` is
`ZetaBad`, and a bad `a` is `BatchBad`. -/
theorem prefixExtractor_isLocallyBounded (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0) :
    (S.prefixExtractor publicValues δ δ' loss).IsLocallyBounded S.prefixProtocol.roles
      (S.prefixChallenges δ δ') := by
  intro T
  refine ⟨?_, fun α Q ↦ ⟨?_, fun ζ o ↦ ⟨?_, fun _ ↦ trivial⟩⟩⟩
  · rw [_root_.RoundByRound.GameFamily.isBounded_iff]
    intro _ _
    refine (prEvent_mono _ _ _ fun α (h : ∃ _ : Unit,
      ¬ (S.traceState publicValues δ' T).holds (S.chooseTrace publicValues δ' T) ∧
        ¬ S.alphaDoom publicValues δ' T α) ↦ ?_).trans
      (prob_alphaBad_le S publicValues [] 0 δ' (S.traceWords T))
    obtain ⟨-, hnot, hdoom⟩ := h
    by_contra hα
    have hfar : S.Far publicValues δ' T := by
      by_contra hfar
      exact hnot (S.chooseTrace_holds publicValues δ' T hfar)
    exact hdoom ⟨hfar, hα⟩
  · rw [_root_.RoundByRound.GameFamily.isBounded_iff]
    intro _ _
    refine (prEvent_mono _ _ _ fun ζ (h : ∃ _ : Unit,
      ¬ ¬ S.alphaDoom publicValues δ' T α ∧ ¬ S.zetaDoom publicValues δ' T α Q ζ) ↦ ?_).trans
      (prob_zetaBad_le S publicValues [] 0 δ' (S.traceWords T) α (S.quotientWords Q))
    obtain ⟨-, hnot, hdoom⟩ := h
    by_contra hζ
    exact hdoom ⟨not_not.mp hnot, hζ⟩
  · rw [_root_.RoundByRound.GameFamily.isBounded_iff]
    intro _ _
    refine (prEvent_mono _ _ _ fun a (h : ∃ w, ¬ ¬ S.zetaDoom publicValues δ' T α Q ζ ∧
      (S.friState publicValues δ T α Q ζ o a loss).holds w) ↦ ?_).trans
      (prob_batchBad_le S δ δ' (S.traceWords T) α (S.quotientWords Q) ζ o)
    obtain ⟨w, hnot, hcheck, hw⟩ := h
    obtain ⟨⟨hfar, hα⟩, hζ⟩ := not_not.mp hnot
    by_contra hbatch
    refine not_near_deepWord S publicValues [] 0 δ δ' hδ' (S.traceWords T) _ α
      (S.quotientWords Q) ζ o a (fun P hP _ _ h ↦
        hfar _ ⟨P, hP.1, hP.2, rfl⟩ ((S.holds_nil_iff publicValues _ _).mp h))
      hcheck hα hζ hbatch ?_
    exact S.near_of_levelState δ _ loss w hw

/-- **The rounds before FRI**, as a knowledge certificate. -/
noncomputable def prefixCertificate (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0) :
    KnowledgeCertificate S.prefixProtocol.tree S.prefixProtocol.roles
      (S.rootState publicValues δ') where
  extractor := S.prefixExtractor publicValues δ δ' loss
  challenges := S.prefixChallenges δ δ'
  prover_preserving := S.prefixExtractor_isProverPreserving publicValues δ δ' loss
  local_bound := S.prefixExtractor_isLocallyBounded publicValues δ δ' hδ' loss

/-- FRI's knowledge certificate on the DEEP word, gated by the check at `ζ`. -/
noncomputable def friCertificate (T : S.TraceMessage) (α : 𝕂) (Q : S.QuotientMessage) (ζ : 𝕂)
    (o : Openings S) (a : 𝕂) (loss : ℝ≥0) :
    KnowledgeCertificate (S.friProtocol []).tree (S.friProtocol []).roles
      (S.friState publicValues δ T α Q ζ o a loss) :=
  (Fri.Interaction.certificate (S.logN + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
    S.params.numQueries (S.deepInputs (S.deepOf T α Q ζ o a)) δ loss (Nat.two_pow_pos _)
    loss.coe_nonneg le_rfl S.domain (S.friSchedule []) 0 (S.deepOf T α Q ζ o a)
    Finset.univ)
    |> gateCertificate _

/-- **The STARK's knowledge certificate**: the rounds before FRI, appended with FRI's on the DEEP
word. -/
noncomputable def certificate (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0) :
    KnowledgeCertificate S.protocol.tree S.protocol.roles (S.rootState publicValues δ') :=
  (S.prefixCertificate publicValues δ δ' hδ' loss).append (fun _ ↦ (S.friProtocol []).tree)
    (fun _ ↦ (S.friProtocol []).roles) fun path ↦
      S.friCertificate publicValues δ path.1 path.2.1 path.2.2.1 path.2.2.2.1 path.2.2.2.2.1
        path.2.2.2.2.2.1 loss

/-- FRI's folds' errors and query term at the proximity loss `loss`, with inputs injected at the
log sizes `heights`. -/
noncomputable def friBound {lookups : List (Lookup F)} (T : Iop.Setup EF lookups)
    (heights : List ℕ) (δ loss : ℝ≥0) : ENNReal :=
  (T.friSchedule heights).foldError (2 ^ T.params.logFinalPolyLen) δ loss T.domain +
    ENNReal.ofReal (1 - δ + (T.friSchedule heights).numFolds * loss) ^ T.params.numQueries

/-- The certificate's largest path error: the folding, out-of-domain and batching errors, and
FRI's at the proximity loss. -/
theorem maxError_certificate (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0) :
    (S.certificate publicValues δ δ' hδ' loss).challenges.maxError S.protocol.roles ≤
      foldingError S δ' + outOfDomainError S δ' + batchingError S δ δ' + S.friBound [] δ loss := by
  have hfri : ∀ T α Q ζ o a, RoundExtractor.ChallengeSchedule.maxError (S.friProtocol []).roles
      (S.friCertificate publicValues δ T α Q ζ o a loss).challenges ≤ S.friBound [] δ loss := by
    intro T α Q ζ o a
    refine (Fri.Interaction.maxError_certificate (S.logN + S.params.logBlowup)
      (2 ^ S.params.logFinalPolyLen) S.params.numQueries
      (S.deepInputs (S.deepOf T α Q ζ o a)) δ loss (Nat.two_pow_pos _) loss.coe_nonneg le_rfl
      S.domain (S.friSchedule []) 0 (S.deepOf T α Q ζ o a) Finset.univ).trans (le_of_eq ?_)
    simp only [friBound, Fri.Interaction.threshold, zero_add]
  change (⨆ T : S.TraceMessage, (foldingError S δ' + ⨆ α : 𝕂, ⨆ Q : S.QuotientMessage,
    (outOfDomainError S δ' + ⨆ ζ : 𝕂, ⨆ o : Openings S, (batchingError S δ δ' + ⨆ a : 𝕂,
      RoundExtractor.ChallengeSchedule.maxError (S.friProtocol []).roles
        (S.friCertificate publicValues δ T α Q ζ o a loss).challenges)))) ≤ _
  refine iSup_le fun T ↦ ?_
  rw [add_assoc, add_assoc]
  refine add_le_add le_rfl (iSup₂_le fun α Q ↦ add_le_add le_rfl (iSup₂_le fun ζ o ↦
    add_le_add le_rfl (iSup_le fun a ↦ hfri T α Q ζ o a)))

section Samples
variable (impl : QueryImpl (OracleSpec.ofPFunctor S.quotientAccess) Id)

set_option backward.isDefEq.respectTransparency false in
theorem samples_fri (T : S.TraceMessage) (α : 𝕂) (Q : S.QuotientMessage) (ζ : 𝕂)
    (o : Openings S) (a : 𝕂) (loss : ℝ≥0) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) (S.friProtocol []).tree
      (S.friProtocol []).roles (S.friProtocol []).oracles S.quotientAccess impl _
      (S.friVerifier publicValues α ζ o a)
      (S.friCertificate publicValues δ T α Q ζ o a loss).challenges :=
  samplesChallenges_mapOutput unifSpec (QueryImpl.id' unifSpec) _ _ _ _ _ _ _ _ _ _
    (Fri.Interaction.samplesChallenges_verifier (S.logN + S.params.logBlowup)
      (2 ^ S.params.logFinalPolyLen) S.params.numQueries (S.deepInputs (S.deepOf T α Q ζ o a)) δ
      loss (Nat.two_pow_pos _) loss.coe_nonneg (S.friSchedule []) le_rfl S.domain _ _ _ 0
      (S.deepOf T α Q ζ o a) Finset.univ)

set_option backward.isDefEq.respectTransparency false in
theorem samples_afterOpenings (α ζ : 𝕂) (o : Openings S)
    (schedule : RoundExtractor.ChallengeSchedule S.afterOpenings.tree S.afterOpenings.roles)
    (hsample : schedule.1.1 = $ᵗ 𝕂)
    (hrest : ∀ a, SamplesChallenges unifSpec (QueryImpl.id' unifSpec) (S.friProtocol []).tree
      (S.friProtocol []).roles (S.friProtocol []).oracles S.quotientAccess impl _
      (S.friVerifier publicValues α ζ o a) (schedule.2 a)) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.afterOpenings.tree
      S.afterOpenings.roles S.afterOpenings.oracles S.quotientAccess impl _
      (S.verifierAfterOpenings publicValues α ζ o) schedule := by
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
theorem samples_afterZeta (α ζ : 𝕂)
    (schedule : RoundExtractor.ChallengeSchedule S.afterZeta.tree S.afterZeta.roles)
    (hrest : ∀ o, SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.afterOpenings.tree
      S.afterOpenings.roles S.afterOpenings.oracles S.quotientAccess impl _
      (S.verifierAfterOpenings publicValues α ζ o) (schedule.2 o)) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.afterZeta.tree S.afterZeta.roles
      S.afterZeta.oracles S.quotientAccess impl _ (S.verifierAfterZeta publicValues α ζ)
      schedule := by
  intro o after hafter
  rw [simulateQ_id', verifierAfterZeta, simulateQ_pure, mem_support_pure_iff] at hafter
  subst hafter
  exact hrest o

set_option backward.isDefEq.respectTransparency false in
theorem samples_afterQuotient (α : 𝕂)
    (schedule : RoundExtractor.ChallengeSchedule S.afterQuotient.tree S.afterQuotient.roles)
    (hsample : schedule.1.1 = $ᵗ 𝕂)
    (hrest : ∀ ζ, SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.afterZeta.tree
      S.afterZeta.roles S.afterZeta.oracles S.quotientAccess impl _
      (S.verifierAfterZeta publicValues α ζ) (schedule.2 ζ)) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.afterQuotient.tree
      S.afterQuotient.roles S.afterQuotient.oracles S.quotientAccess impl _
      (S.verifierAfterQuotient publicValues α) schedule := by
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

set_option backward.isDefEq.respectTransparency false in
theorem samples_afterAlpha (impl : QueryImpl (OracleSpec.ofPFunctor S.traceAccess) Id) (α : 𝕂)
    (schedule : RoundExtractor.ChallengeSchedule S.afterAlpha.tree S.afterAlpha.roles)
    (hrest : ∀ Q, SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.afterQuotient.tree
      S.afterQuotient.roles S.afterQuotient.oracles S.quotientAccess
      (Access.extendImpl S.traceAccess OracleInterface.instFunction impl Q) _
      (S.verifierAfterQuotient publicValues α) (schedule Q)) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.afterAlpha.tree S.afterAlpha.roles
      S.afterAlpha.oracles S.traceAccess impl _ (S.verifierAfterAlpha publicValues α)
      schedule := by
  intro Q after hafter
  rw [simulateQ_id', verifierAfterAlpha, simulateQ_pure, mem_support_pure_iff] at hafter
  subst hafter
  exact hrest Q

set_option backward.isDefEq.respectTransparency false in
theorem samples_afterTrace (impl : QueryImpl (OracleSpec.ofPFunctor S.traceAccess) Id)
    (schedule : RoundExtractor.ChallengeSchedule S.afterTrace.tree S.afterTrace.roles)
    (hsample : schedule.1.1 = $ᵗ 𝕂)
    (hrest : ∀ α, SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.afterAlpha.tree
      S.afterAlpha.roles S.afterAlpha.oracles S.traceAccess impl _
      (S.verifierAfterAlpha publicValues α) (schedule.2 α)) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.afterTrace.tree S.afterTrace.roles
      S.afterTrace.oracles S.traceAccess impl _ (S.verifierAfterTrace publicValues) schedule := by
  refine ⟨fun event ↦ ?_, fun chosen hchosen ↦ ?_⟩
  · simp only [simulateQ_id', verifierAfterTrace, simulateQ_bind, simulateQ_pure]
    erw [Fri.Interaction.simulateQ_liftAccessImpl_liftComp]
    rw [bind_pure_comp, prEvent_map, hsample]
  simp only [simulateQ_id', verifierAfterTrace, simulateQ_bind, simulateQ_pure] at hchosen
  erw [Fri.Interaction.simulateQ_liftAccessImpl_liftComp] at hchosen
  obtain ⟨α, -, hchosen⟩ := support_bind_exists hchosen
  rw [mem_support_pure_iff] at hchosen
  subst hchosen
  exact hrest α

set_option backward.isDefEq.respectTransparency false in
/-- The verifier samples its challenges as the certificate's challenge programs. -/
theorem samplesChallenges_verifier (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) S.protocol.tree S.protocol.roles
      S.protocol.oracles noAccess noImpl _ (S.verifier publicValues)
      (S.certificate publicValues δ δ' hδ' loss).challenges := by
  intro T after hafter
  rw [simulateQ_id', verifier, simulateQ_pure, mem_support_pure_iff] at hafter
  subst hafter
  exact S.samples_afterTrace publicValues _ _ rfl fun α ↦
    S.samples_afterAlpha publicValues _ α _ fun Q ↦
      S.samples_afterQuotient publicValues _ α _ rfl fun ζ ↦
        S.samples_afterZeta publicValues _ α ζ _ fun o ↦
          S.samples_afterOpenings publicValues _ α ζ o _ rfl fun a ↦
            S.samples_fri publicValues δ _ T α Q ζ o a loss

/-- The certificate's terminal state is FRI's, on the DEEP word of the path's messages. -/
theorem terminalState_certificate (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0)
    (path : S.protocol.tree.ExecutionPath) :
    (S.certificate publicValues δ δ' hδ' loss).extractor.terminalState path =
      (S.friCertificate publicValues δ path.1 path.2.1 path.2.2.1 path.2.2.2.1 path.2.2.2.2.1
        path.2.2.2.2.2.1 loss).extractor.terminalState path.2.2.2.2.2.2 := rfl

/-- The extractor's input witness is the path's trace message, with a trace. -/
theorem extractWitness_fst (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0)
    (path : S.protocol.tree.ExecutionPath)
    (w : ((S.certificate publicValues δ δ' hδ' loss).extractor.terminalState path).Witness) :
    ((S.certificate publicValues δ δ' hδ' loss).extractor.extractWitness path w).1 = path.1 :=
  rfl

section Terminal
variable (loss : ℝ≥0)

set_option backward.isDefEq.respectTransparency false in
/-- An accepting run of FRI on the DEEP word reaches a terminal state that holds. -/
theorem terminal_fri (T : S.TraceMessage) (α : 𝕂) (Q : S.QuotientMessage) (ζ : 𝕂)
    (o : Openings S) (a : 𝕂) {OutP : (S.friProtocol []).tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec (S.friProtocol []).tree
      (S.friProtocol []).roles OutP) :
    ∀ result ∈ support (executeStrategies unifSpec (S.friProtocol []).tree
      (S.friProtocol []).roles (S.friProtocol []).oracles S.quotientAccess (S.messagesImpl T Q)
      prover (S.friVerifier publicValues α ζ o a)), result.2.2 = true →
      ∃ w, ((S.friCertificate publicValues δ T α Q ζ o a loss).extractor.terminalState
        result.1).holds w := by
  intro result hres hacc
  rw [execute_fri, support_map] at hres
  obtain ⟨r, hr, rfl⟩ := hres
  have hacc' : @decide _ (Classical.propDecidable (ConstraintsHoldAt S publicValues α ζ o)) = true ∧
      r.2.2 = true := Bool.and_eq_true _ _ ▸ hacc
  obtain ⟨w, hw⟩ := Fri.Interaction.terminal_holds_of_accepts (S.logN + S.params.logBlowup)
    (2 ^ S.params.logFinalPolyLen) S.params.numQueries (S.deepInputs (S.deepOf T α Q ζ o a)) δ
    loss unifSpec (Nat.two_pow_pos _) loss.coe_nonneg _ _ (S.friSchedule []) le_rfl S.domain _ _
    _ 0 (S.deepOf T α Q ζ o a) Finset.univ prover (S.reads_deepReader T Q α ζ o a)
    (fun x ↦ by simp only [Finset.mem_univ, decide_true]; rfl) r hr hacc'.2
  simp only [friCertificate, gateCertificate]
  rw [terminalState_gateExtractor]
  exact ⟨w, @of_decide_eq_true _ (Classical.propDecidable _) hacc'.1, hw⟩

set_option backward.isDefEq.respectTransparency false in
theorem terminal_afterOpenings (T : S.TraceMessage) (α : 𝕂) (Q : S.QuotientMessage) (ζ : 𝕂)
    (o : Openings S) {OutP : S.afterOpenings.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.afterOpenings.tree
      S.afterOpenings.roles OutP) :
    ∀ result ∈ support (executeStrategies unifSpec S.afterOpenings.tree S.afterOpenings.roles
      S.afterOpenings.oracles S.quotientAccess (S.messagesImpl T Q) prover
      (S.verifierAfterOpenings publicValues α ζ o)), result.2.2 = true →
      ∃ w, ((S.friCertificate publicValues δ T α Q ζ o result.1.1 loss).extractor.terminalState
        result.1.2).holds w := by
  intro result hres hacc
  rw [execute_afterOpenings] at hres
  obtain ⟨a, -, hres⟩ := support_bind_exists hres
  obtain ⟨p, -, hres⟩ := support_bind_exists hres
  obtain ⟨r, hr, hres⟩ := support_bind_exists hres
  rw [mem_support_pure_iff] at hres
  subst hres
  exact S.terminal_fri publicValues δ loss T α Q ζ o a (OutP := fun path ↦ OutP ⟨a, path⟩) p r hr
    hacc

set_option backward.isDefEq.respectTransparency false in
theorem terminal_afterZeta (T : S.TraceMessage) (α : 𝕂) (Q : S.QuotientMessage) (ζ : 𝕂)
    {OutP : S.afterZeta.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.afterZeta.tree
      S.afterZeta.roles OutP) :
    ∀ result ∈ support (executeStrategies unifSpec S.afterZeta.tree S.afterZeta.roles
      S.afterZeta.oracles S.quotientAccess (S.messagesImpl T Q) prover
      (S.verifierAfterZeta publicValues α ζ)), result.2.2 = true →
      ∃ w, ((S.friCertificate publicValues δ T α Q ζ result.1.1 result.1.2.1
        loss).extractor.terminalState result.1.2.2).holds w := by
  intro result hres hacc
  rw [execute_afterZeta] at hres
  obtain ⟨chosen, -, hres⟩ := support_bind_exists hres
  obtain ⟨r, hr, hres⟩ := support_bind_exists hres
  rw [mem_support_pure_iff] at hres
  subst hres
  exact S.terminal_afterOpenings publicValues δ loss T α Q ζ chosen.1
    (OutP := fun path ↦ OutP ⟨chosen.1, path⟩) chosen.2 r hr hacc

set_option backward.isDefEq.respectTransparency false in
theorem terminal_afterQuotient (T : S.TraceMessage) (α : 𝕂) (Q : S.QuotientMessage)
    {OutP : S.afterQuotient.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.afterQuotient.tree
      S.afterQuotient.roles OutP) :
    ∀ result ∈ support (executeStrategies unifSpec S.afterQuotient.tree S.afterQuotient.roles
      S.afterQuotient.oracles S.quotientAccess (S.messagesImpl T Q) prover
      (S.verifierAfterQuotient publicValues α)), result.2.2 = true →
      ∃ w, ((S.friCertificate publicValues δ T α Q result.1.1 result.1.2.1 result.1.2.2.1
        loss).extractor.terminalState result.1.2.2.2).holds w := by
  intro result hres hacc
  rw [execute_afterQuotient] at hres
  obtain ⟨ζ, -, hres⟩ := support_bind_exists hres
  obtain ⟨p, -, hres⟩ := support_bind_exists hres
  obtain ⟨r, hr, hres⟩ := support_bind_exists hres
  rw [mem_support_pure_iff] at hres
  subst hres
  exact S.terminal_afterZeta publicValues δ loss T α Q ζ (OutP := fun path ↦ OutP ⟨ζ, path⟩) p r hr
    hacc

set_option backward.isDefEq.respectTransparency false in
theorem terminal_afterAlpha (T : S.TraceMessage) (α : 𝕂)
    {OutP : S.afterAlpha.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.afterAlpha.tree
      S.afterAlpha.roles OutP) :
    ∀ result ∈ support (executeStrategies unifSpec S.afterAlpha.tree S.afterAlpha.roles
      S.afterAlpha.oracles S.traceAccess
      (Access.extendImpl noAccess OracleInterface.instFunction noImpl T) prover
      (S.verifierAfterAlpha publicValues α)), result.2.2 = true →
      ∃ w, ((S.friCertificate publicValues δ T α result.1.1 result.1.2.1 result.1.2.2.1
        result.1.2.2.2.1 loss).extractor.terminalState result.1.2.2.2.2).holds w := by
  intro result hres hacc
  rw [execute_afterAlpha] at hres
  obtain ⟨chosen, -, hres⟩ := support_bind_exists hres
  obtain ⟨r, hr, hres⟩ := support_bind_exists hres
  rw [mem_support_pure_iff] at hres
  subst hres
  exact S.terminal_afterQuotient publicValues δ loss T α chosen.1
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
        result.1.2.2.2.1 result.1.2.2.2.2.1 loss).extractor.terminalState
          result.1.2.2.2.2.2).holds w := by
  intro result hres hacc
  rw [execute_afterTrace] at hres
  obtain ⟨α, -, hres⟩ := support_bind_exists hres
  obtain ⟨p, -, hres⟩ := support_bind_exists hres
  obtain ⟨r, hr, hres⟩ := support_bind_exists hres
  rw [mem_support_pure_iff] at hres
  subst hres
  exact S.terminal_afterAlpha publicValues δ loss T α (OutP := fun path ↦ OutP ⟨α, path⟩) p r hr hacc

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
  exact S.terminal_afterTrace publicValues δ loss chosen.1 (OutP := fun path ↦ OutP ⟨chosen.1, path⟩)
    chosen.2 r hr hacc

end Terminal

/-- **Knowledge soundness at a length, at a proximity loss.** Against any prover, the verifier
accepts while no trace close to the committed trace satisfies the AIR with probability at most
the folding, out-of-domain and batching errors and FRI's error at the proximity loss `loss`. -/
theorem extraction_le (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0)
    {OutP : S.protocol.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.protocol.tree
      S.protocol.roles OutP) :
    Pr{let result ← (executeStrategies unifSpec S.protocol.tree S.protocol.roles
      S.protocol.oracles noAccess noImpl prover (S.verifier publicValues))}[
        result.2.2 = true ∧ S.Far publicValues δ' result.1.1] ≤
      foldingError S δ' + outOfDomainError S δ' + batchingError S δ δ' + S.friBound [] δ loss := by
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

/-- **Knowledge soundness at a length.** Against any prover, the verifier accepts while no trace
close to the committed trace satisfies the AIR with probability at most the knowledge error. -/
theorem extraction_le_knowledgeError (hδ' : (δ' : ℝ) < 1 - S.rate)
    {OutP : S.protocol.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.protocol.tree
      S.protocol.roles OutP) :
    Pr{let result ← (executeStrategies unifSpec S.protocol.tree S.protocol.roles
      S.protocol.oracles noAccess noImpl prover (S.verifier publicValues))}[
        result.2.2 = true ∧ S.Far publicValues δ' result.1.1] ≤ knowledgeError S δ δ' := by
  rw [knowledgeError, friError_eq, Fri.Interaction.error, ENNReal.add_iInf]
  exact le_iInf fun loss ↦ S.extraction_le publicValues δ δ' hδ' loss prover

end Setup

/-! ### Statements -/

namespace Statement
variable (C : Statement F) (EF : Type) [Challenge F EF] (publicValues : List F)
  (δ δ' : ℕ → ℝ≥0)

/-- No trace close to an execution's committed trace satisfies the AIR at its length. -/
def Far (path : (C.protocol EF).tree.ExecutionPath) : Prop :=
  (C.setup EF path.1).Far publicValues (δ' (path.1 : C.Length).1) path.2.1

variable {C}

theorem rate_setup (n : C.Length) : (C.setup EF n).rate = C.rate :=
  Statement.rate_setupAt C n.1 n.2

variable (C)

/-- The STARK's error at a length, but FRI's at the proximity loss `loss`. -/
noncomputable def lengthBound (n : C.Length) (loss : ℝ≥0) : ENNReal :=
  foldingError (C.setup EF n) (δ' n) + outOfDomainError (C.setup EF n) (δ' n) +
    batchingError (C.setup EF n) (δ n) (δ' n) + (C.setup EF n).friBound [] (δ n) loss

set_option backward.isDefEq.respectTransparency false in
/-- **Knowledge soundness for a statement, at proximity losses.** Against any prover, the
verifier accepts while no trace close to the committed trace satisfies the AIR at the claimed
length with probability at most the largest over the lengths of the STARK's errors there, FRI's
at the proximity loss `loss n`: whatever length the prover sends, the STARK's certificate there
bounds the rest. -/
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
    (δ' (chosen.1 : C.Length).1)
    (by rw [rate_setup]; exact hδ' (chosen.1 : C.Length).1 (chosen.1 : C.Length).2)
    (loss chosen.1) (OutP := fun path ↦ OutP ⟨chosen.1, path⟩) chosen.2).trans
    (le_iSup (fun n ↦ C.lengthBound EF δ δ' n (loss n)) chosen.1)

/-- **Knowledge soundness for a statement.** Against any prover, the verifier accepts while no
trace close to the committed trace satisfies the AIR at the claimed length with probability at
most the statement's knowledge error. -/
theorem extraction_le_knowledgeError (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate)
    {OutP : (C.protocol EF).tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec (C.protocol EF).tree
      (C.protocol EF).roles OutP) :
    Pr{let result ← (executeStrategies unifSpec (C.protocol EF).tree (C.protocol EF).roles
      (C.protocol EF).oracles noAccess noImpl prover (C.verifier EF publicValues))}[
        result.2.2 = true ∧ C.Far EF publicValues δ' result.1] ≤ C.knowledgeError EF δ δ' := by
  have hK : C.knowledgeError EF δ δ' = ⨆ n : C.Length,
      Iop.knowledgeError (C.setup EF n) (δ n) (δ' n) := by
    rw [Statement.knowledgeError, iSup_subtype']
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt ↦ ?_
  have hloss (n : C.Length) : ∃ loss, (C.setup EF n).friBound [] (δ n) loss ≤
      friError (C.setup EF n) (δ n) + ε := by
    have hfin : friError (C.setup EF n) (δ n) < ⊤ := by
      refine lt_of_le_of_lt (le_trans (le_add_self) (le_iSup (fun n : C.Length ↦
        Iop.knowledgeError (C.setup EF n) (δ n) (δ' n)) n)) (hK ▸ hlt)
    rw [friError_eq, Fri.Interaction.error] at hfin ⊢
    obtain ⟨loss, hl⟩ := iInf_lt_iff.mp (ENNReal.lt_add_right hfin.ne
      (ENNReal.coe_ne_zero.mpr hε.ne'))
    exact ⟨loss, hl.le⟩
  choose loss hl using hloss
  refine (C.extraction_le EF publicValues δ δ' hδ' loss prover).trans ?_
  rw [hK]
  refine iSup_le fun n ↦ ?_
  refine le_trans ?_ (add_le_add (le_iSup (fun n : C.Length ↦
    Iop.knowledgeError (C.setup EF n) (δ n) (δ' n)) n) le_rfl)
  rw [lengthBound, Iop.knowledgeError, add_assoc _ (friError _ _)]
  exact add_le_add le_rfl (hl n)

end Statement

end CompStark.Iop
