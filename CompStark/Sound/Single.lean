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

/-- The batch of one instance opens the STARK's words. -/
theorem openedWords_toBatch {S : Iop.Setup EF} (p : Iop.Prover S) (α ζ : 𝕂) :
    Batch.openedWords p.toBatch α ζ = Iop.openedWords p α ζ := by
  rw [openedWords_eq_append]
  simp only [Batch.openedWords, List.finRange_succ, List.finRange_zero, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rfl

/-- The batch of one instance accepts as the STARK does. -/
theorem acceptance_toBatch {S : Iop.Setup EF} (publicValues : List F) (p : Iop.Prover S) :
    Batch.acceptance (fun _ ↦ publicValues) p.toBatch = acceptance publicValues p := by
  classical
  unfold Batch.acceptance Iop.acceptance
  congr 1
  refine Finset.sum_congr rfl fun α _ ↦ Finset.sum_congr rfl fun ζ _ ↦
    Finset.sum_congr rfl fun a _ ↦ ?_
  have hdeep : Batch.deepWord p.toBatch α ζ a = Iop.deepWord p α ζ a := by
    unfold Batch.deepWord Iop.deepWord
    rw [openedWords_toBatch]
  rw [hdeep]
  exact if_congr ⟨fun h ↦ h ⟨0, Nat.one_pos⟩, fun h _ ↦ h⟩ rfl rfl

/-- The batch of one instance has the STARK's knowledge error. -/
theorem knowledgeError_toBatch (S : Iop.Setup EF) (δ δ' : NNReal) :
    Batch.knowledgeError S.toBatch δ δ' = knowledgeError S δ δ' := by
  rw [Batch.knowledgeError, Batch.Setup.numOpened, Fin.sum_univ_one, iSup_unique]
  rfl

end CompStark.Sound
