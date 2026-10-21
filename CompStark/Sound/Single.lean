/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.BatchAssembly

/-! # A STARK is a batch of one instance

A STARK's acceptance and knowledge error are those of the batch of its one instance
(`Setup.toBatch`, `Prover.toBatch`): the batch's opened words are the STARK's, in the same order,
and the batch's error terms are the STARK's.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-- The batch of one instance has the STARK's rate. -/
theorem rate_toBatch (S : Iop.Setup EF) : S.toBatch.rate = S.rate := by
  rw [Batch.Setup.rate, Iop.Setup.rate, Iop.Setup.n, Iop.Setup.size, pow_add, Nat.cast_mul]
  have : ((2 ^ S.logN : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- The batch of one instance injects nothing into FRI. -/
theorem friHeights_toBatch (S : Iop.Setup EF) : S.toBatch.friHeights = [] := by
  simp only [Batch.Setup.friHeights, Finset.univ_unique, Finset.image_singleton,
    Finset.erase_singleton, Finset.sort_empty]

/-- The batch of one instance opens the STARK's words. -/
theorem groupOpened_toBatch {S : Iop.Setup EF} (p : Iop.Prover S) (α ζ : 𝕂) :
    Batch.groupOpened p.toBatch α ζ (S.logN + S.params.logBlowup) = Iop.openedWords p α ζ := by
  rw [openedWords_eq_append]
  simp only [Batch.groupOpened, List.finRange_succ, List.finRange_zero, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [onSize_self, onSize_self, onSize_self]
  rfl

/-- The batch of one instance batches the STARK's DEEP word. -/
theorem groupDeepWord_toBatch {S : Iop.Setup EF} (p : Iop.Prover S) (α ζ a : 𝕂) :
    Batch.groupDeepWord p.toBatch α ζ a (S.logN + S.params.logBlowup) = Iop.deepWord p α ζ a := by
  funext x
  unfold Batch.groupDeepWord Iop.deepWord
  rw [groupOpened_toBatch]
  congr 1
  refine List.map_congr_left fun w _ ↦ ?_
  obtain ⟨⟨f, z, y⟩, k⟩ := w
  rw [domain_eq]

/-- The batch of one instance accepts as the STARK does. -/
theorem acceptance_toBatch {S : Iop.Setup EF} (publicValues : List F) (p : Iop.Prover S) :
    Batch.acceptance (fun _ ↦ publicValues) p.toBatch = acceptance publicValues p := by
  classical
  unfold Batch.acceptance Iop.acceptance
  congr 1
  refine Finset.sum_congr rfl fun α _ ↦ Finset.sum_congr rfl fun ζ _ ↦
    Finset.sum_congr rfl fun a _ ↦ ?_
  have hfri : friAcceptanceWith S.toBatch.domainSetup (Batch.groupDeepWord p.toBatch α ζ a)
      S.toBatch.friHeights (Batch.groupDeepWord p.toBatch α ζ a _) =
      friAcceptance S (Iop.deepWord p α ζ a) := by
    rw [friHeights_toBatch, friAcceptance, friAcceptanceWith, friAcceptanceWith, Setup.friRounds,
      Setup.friRounds, FriGame.Rounds.schedule_nil _ _ _ (fun _ _ ↦ 0)]
    exact congrArg _ (groupDeepWord_toBatch p α ζ a)
  rw [hfri]
  exact if_congr ⟨fun h ↦ h ⟨0, Nat.one_pos⟩, fun h _ ↦ h⟩ rfl rfl

/-- The batch of one instance has the STARK's knowledge error. -/
theorem knowledgeError_toBatch (S : Iop.Setup EF) (δ δ' : NNReal) :
    Batch.knowledgeError S.toBatch δ δ' = knowledgeError S δ δ' := by
  have hnum : S.toBatch.groupNumOpened (S.logN + S.params.logBlowup) = S.numOpened := by
    simp only [Batch.Setup.groupNumOpened, Finset.univ_unique, Finset.filter_singleton,
      ite_true, Finset.sum_singleton]
  rw [Batch.knowledgeError, iSup_unique, friHeights_toBatch, Batch.Setup.instanceError]
  change foldingError S δ' + outOfDomainError S δ' + batchingErrorOf S
    (S.toBatch.groupNumOpened (S.logN + S.params.logBlowup)) δ ((δ' : ℝ) - 2 / S.size) +
    friErrorWith S [] δ = _
  rw [hnum]
  rfl

end CompStark.Sound
