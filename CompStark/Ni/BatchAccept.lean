/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BatchRun
public import CompStark.Batch.Verifier

/-! # Accepting runs of the batch verifier on pure primitives

`verifyBatchWith_ok` reads an accepting run of the batch STARK's verifier on pure primitives
backwards, as `verifyWith_ok` does the STARK's: the proof's shape checks, the out-of-domain
grinding witness checks, `ζ` is off every instance's trace domain, the commitment scheme accepts
at the batching challenge, and every instance's constraints hold at `ζ`, all with the challenges
the challenger returns (`alphaOfB`, `zetaOfB`, `batchOfB`).
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Batch

variable {F : Type} (H : Primitives F Id) [BaseField F] {EF : Type} [Challenge F EF]

section States
variable (P : Params) (instances : List (Instance F)) (common : Common F)
  (proof : BatchProof F EF) (pis : List (List F))

/-- The challenger before `α`: after the batch's domain separator, every instance's degree bits,
the main commitment, the public values and the preprocessed commitment. -/
abbrev stateAlphaB : H.State :=
  obsList H (obsList H (obsList H (obsExts H (obsList H H.init (batchSeedOf EF P instances common))
    (instances.map fun I ↦ (Ext.ofBase (I.logN : F) : EF))) proof.mainCommit.toList) pis.flatten)
    ((common.preprocessed.map (·.toList)).getD [])

/-- The constraint-folding challenge `α`. -/
def alphaOfB : EF := (smpExt H (stateAlphaB H P instances common proof pis)).1

/-- The out-of-domain grinding check, after the quotient commitment. -/
abbrev oodCheckB : Bool × H.State :=
  chkWit H P.oodPowBits proof.oodWitness
    (obsList H (smpExt (EF := EF) H (stateAlphaB H P instances common proof pis)).2
      proof.quotientCommit.toList)

/-- The out-of-domain point `ζ`. -/
def zetaOfB : EF := (smpExt H (oodCheckB (EF := EF) H P instances common proof pis).2).1

/-- The batching grinding check, after the PCS's domain separator and the opened values. -/
def batchCheckB : Bool × H.State :=
  chkWit H P.batchPowBits proof.fri.batchWitness
    (pcsState H P (batchRounds instances common proof (zetaOfB H P instances common proof pis))
    (smpExt (EF := EF) H (oodCheckB (EF := EF) H P instances common proof pis).2).2)

/-- FRI's batching challenge. -/
def batchOfB : EF := (smpExt H (batchCheckB H P instances common proof pis).2).1

/-- The challenger when FRI starts, after the batching challenge. -/
def stateFriB : H.State := (smpExt (EF := EF) H (batchCheckB H P instances common proof pis).2).2

end States

/-- A passed `unless` check: its condition holds, and the rest runs. -/
theorem unless_ok {α : Type} (b : Bool) (e : String) (k : PUnit → ExceptT String Id α) (x : α)
    (h : (have jp := k
      if b = true then jp PUnit.unit else (throw e >>= fun r ↦ jp r) : ExceptT String Id α).run =
        .ok x) :
    b = true ∧ (k PUnit.unit).run = .ok x := by
  cases b
  · exact absurd h (by intro h'; cases h')
  · exact ⟨rfl, h⟩

/-- **An accepting batch verifier** on pure primitives: the proof's shape checks, the grinding
witnesses check, `ζ` is off every trace domain, FRI accepts from the challenger after the batching
challenge, and every instance's constraints hold at `ζ` with the challenger's `α` and `ζ`. -/
theorem verifyBatchWith_ok (P : Params) (instances : List (Instance F)) (common : Common F)
    (proof : BatchProof F EF) (pis : List (List F))
    (h : verifyBatchWith H P instances common proof pis = .ok ()) :
    let zeta := zetaOfB H P instances common proof pis
    proof.opened.size = instances.length ∧ pis.length = instances.length ∧
      proof.degreeBits.toList = instances.map (·.logN) ∧
      (∀ I ∈ instances, I.logN + I.air.logQuotientChunks I.logN ≤ twoAdicity F) ∧
      (∀ x ∈ instances.zip pis, x.2.length = x.1.air.numPublicValues) ∧
      (∀ x ∈ instances.zip proof.opened.toList, openedShapeOk x.1.air x.2 x.1.logN = true) ∧
      common.preprocessed.isSome = instances.any (0 < ·.air.preprocessedWidth) ∧
      (oodCheckB (EF := EF) H P instances common proof pis).1 = true ∧
      (∀ I ∈ instances, (Ext.powTwo zeta I.logN - 1 != 0) = true) ∧
      (batchCheckB H P instances common proof pis).1 = true ∧
      (∃ st, verifyFri H P proof.fri (batchRounds instances common proof zeta)
        (batchOfB H P instances common proof pis) (stateFriB H P instances common proof pis) =
          .ok ((), st)) ∧
      ∀ x ∈ instances.zip (proof.opened.toList.zip pis),
        instanceCheck x.1 x.2.1 x.2.2 zeta (alphaOfB H P instances common proof pis) = true := by
  intro zeta
  unfold verifyBatchWith at h
  obtain ⟨hcount, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨hdb, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨hq, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨-, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨hpub, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨hshape, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨hprep, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨-, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨x, hx, hc⟩ := except_bind_ok _ _ _ h
  unfold StateT.run at hx
  rw [bind_ok_of H (observeList_eq H _ _), bind_ok_of H (observeExts_eq H _ _),
    bind_ok_of H (observeList_eq H _ _), bind_ok_of H (observeList_eq H _ _),
    bind_ok_of H (observeList_eq H _ _),
    bind_ok_of H (a := alphaOfB H P instances common proof pis)
      (s' := (smpExt (EF := EF) H (stateAlphaB H P instances common proof pis)).2)
      (sampleExt_eq H _),
    bind_ok_of H (observeList_eq H _ _),
    bind_ok_of H (a := (oodCheckB (EF := EF) H P instances common proof pis).1)
      (s' := (oodCheckB (EF := EF) H P instances common proof pis).2)
      (checkWitness_eq H _ _ _)] at hx
  obtain ⟨hood, hx⟩ := ensure_bind_eq_ok H hx
  rw [bind_ok_of H (a := zeta) (s' := (smpExt (EF := EF) H
    (oodCheckB (EF := EF) H P instances common proof pis).2).2)
    (sampleExt_eq H _)] at hx
  obtain ⟨hz, hx⟩ := ensure_bind_eq_ok H hx
  obtain ⟨u, st, h3, h4⟩ := bind_eq_ok H hx
  obtain ⟨-, hbc, hfri⟩ := verifyPcs_ok H P _ proof.fri _ _ h3
  have hx' := pure_eq_ok H h4
  subst hx'
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hcount hdb hq
  simp only [beq_iff_eq, List.all_eq_true] at hpub hshape
  simp only [beq_iff_eq, List.all_eq_true] at hprep hz hc
  exact ⟨hcount.1, hcount.2, hdb, hq, fun x hx ↦ hpub x hx, hshape, hprep, hood, hz, hbc,
    ⟨_, hfri⟩, hc⟩

end CompStark.Ni
