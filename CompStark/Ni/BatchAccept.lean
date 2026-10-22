/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BatchRun
public import CompStark.Batch.Verifier

/-! # Accepting runs of the batch verifier on pure primitives

`verifyBatchWith_ok` reads an accepting run of the batch STARK's verifier on pure primitives
backwards, as `verifyWith_ok` does the STARK's: the proof's shape checks, the lookup and
out-of-domain grinding witnesses check, `ζ` is off every instance's trace domain, the commitment
scheme accepts at the batching challenge, every instance's constraints hold at `ζ`, and the
terminals sum to zero, all with the challenges the challenger returns (`lookupRunB`, `alphaOfB`,
`zetaOfB`, `batchOfB`).
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Batch

variable {F : Type} (H : Primitives F Id) [BaseField F] {EF : Type} [Challenge F EF]

section States
variable (P : Params) (instances : List (Instance F)) (common : Common F)
  (proof : BatchProof F EF) (pis : List (List F))

/-- The challenger before the lookup phase: after the batch's domain separator, every instance's
degree bits, the main commitment, the public values and the preprocessed commitment. -/
abbrev stateLookupB : H.State :=
  obsList H (obsList H (obsList H (obsExts H
    (obsList H H.init (batchSeedOf EF P instances common))
    (instances.map fun I ↦ (Ext.ofBase (I.logN : F) : EF))) (capElems proof.mainCommit))
    pis.flatten) ((common.preprocessed.map capElems).getD [])

/-- The lookup phase's challenges `(α_L, β_L)` from the state `s`, after the lookup grinding
check, and the challenger after them; `(0, 0)` and no change without lookups. -/
def lookupRun (s : H.State) : (EF × EF) × H.State :=
  if hasLookups instances then
    let a := smpExt (EF := EF) H (chkWit H P.lookupPowBits (proof.lookupWitness.getD 0) s).2
    let b := smpExt (EF := EF) H a.2
    ((a.1, b.1), b.2)
  else ((0, 0), s)

/-- The lookup grinding check. -/
abbrev lookupCheckB : Bool × H.State :=
  chkWit H P.lookupPowBits (proof.lookupWitness.getD 0)
      (stateLookupB H P instances common proof pis)

/-- The lookup challenges `(α_L, β_L)`. -/
def lookupRunB : EF × EF :=
  (lookupRun H P instances proof (stateLookupB H P instances common proof pis)).1

/-- The challenger before `α`: after the lookup phase, the permutation commitment and the
terminals. -/
abbrev stateAlphaB : H.State :=
  obsExts H (obsList H (lookupRun H P instances proof
    (stateLookupB H P instances common proof pis)).2
    ((proof.permutationCommit.map capElems).getD [])) (proof.lookupTerminals.toList.filterMap id)

/-- The constraint-folding challenge `α`. -/
def alphaOfB : EF := (smpExt H (stateAlphaB H P instances common proof pis)).1

/-- The out-of-domain grinding check, after the quotient commitment. -/
abbrev oodCheckB : Bool × H.State :=
  chkWit H P.oodPowBits proof.oodWitness
    (obsList H (smpExt (EF := EF) H (stateAlphaB H P instances common proof pis)).2
      (capElems proof.quotientCommit))

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

/-- **The lookup phase**, when it accepts: with lookups the grinding witness checks, and it returns
the lookup challenges of `lookupRun` and then observes the permutation commitment and the
terminals. -/
theorem lookupPhase_ok (P : Params) (instances : List (Instance F)) (proof : BatchProof F EF)
    (s : H.State) (r : (EF × EF) × H.State)
    (h : (lookupPhase (H := H) P instances proof : M H (EF × EF)) s = .ok r) :
    (hasLookups instances = true →
      (chkWit H P.lookupPowBits (proof.lookupWitness.getD 0) s).1 = true) ∧
    r = ((lookupRun H P instances proof s).1, obsExts H (obsList H
      (lookupRun H P instances proof s).2 ((proof.permutationCommit.map capElems).getD []))
      (proof.lookupTerminals.toList.filterMap id)) := by
  unfold lookupPhase at h
  cases hl : hasLookups instances with
  | false =>
    rw [hl, ite_eq_right Bool.false_ne_true] at h
    refine ⟨fun h' ↦ absurd h' Bool.false_ne_true, ?_⟩
    have h' : r = ((0, 0), obsExts H (obsList H s ((proof.permutationCommit.map capElems).getD
        [])) (proof.lookupTerminals.toList.filterMap id)) := by
      have := h
      exact (Except.ok.inj this).symm
    rw [h', lookupRun, hl]
    rfl
  | true =>
    rw [hl, ite_eq_left rfl] at h
    rw [bind_ok_of H (checkWitness_eq H _ _ _)] at h
    obtain ⟨hw, h⟩ := ensure_bind_eq_ok H h
    rw [bind_ok_of H (sampleExt_eq H _), bind_ok_of H (sampleExt_eq H _)] at h
    change (observeList H _ >>= fun _ ↦ observeExts H _ >>= fun _ ↦ pure _) _ = _ at h
    rw [bind_ok_of H (observeList_eq H _ _), bind_ok_of H (observeExts_eq H _ _)] at h
    have hr := pure_eq_ok H h
    refine ⟨fun _ ↦ hw, ?_⟩
    rw [hr, lookupRun, hl]
    rfl

/-- A proof that passes the lookup checks commits to permutation traces exactly with lookups, and
its permutation openings and terminals have every instance's shape. -/
theorem lookupShapeOk_spec (P : Params) (instances : List (Instance F)) (proof : BatchProof F EF)
    (hlk : lookupShapeOk P instances proof = true) :
    (∀ x ∈ instances.zip (proof.permutationLocal.toList.zip (proof.permutationNext.toList.zip
      proof.lookupTerminals.toList)), permutationShapeOk x.1 x.2.1 x.2.2.1 x.2.2.2 = true) ∧
    proof.permutationCommit.isSome = hasLookups instances ∧
    ∀ c ∈ proof.permutationCommit, c.size ≠ 0 := by
  simp only [lookupShapeOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    Option.all_eq_true_iff_get, bne_iff_ne, ne_eq] at hlk
  refine ⟨fun x hx ↦ hlk.1.1.1.2 x hx, hlk.1.1.2, fun c hc ↦ ?_⟩
  have := hlk.1.2 (Option.isSome_of_mem hc)
  rwa [Option.get_of_mem _ hc] at this

/-- The rest of an accepted run after a computation. -/
theorem except_bind_ok' {α : Type} (R : ExceptT String Id α) (k : α → ExceptT String Id Unit)
    (h : (R >>= k).run = .ok ()) : ∃ x, R = .ok x ∧ (k x).run = .ok () := by
  revert h
  match R with
  | .ok x => exact fun h ↦ ⟨x, rfl, h⟩
  | .error e => exact fun h ↦ absurd h (by intro h'; cases h')

/-- **An accepting batch verifier** on pure primitives: the proof's shape checks, the grinding
witnesses check, `ζ` is off every trace domain, FRI accepts from the challenger after the batching
challenge, every instance's constraints hold at `ζ` with the challenger's lookup challenges, `α`
and `ζ`, and the terminals sum to zero. -/
theorem verifyBatchWith_ok (P : Params) (instances : List (Instance F)) (common : Common F)
    (proof : BatchProof F EF) (pis : List (List F))
    (h : verifyBatchWith H P instances common proof pis = .ok ()) :
    let zeta := zetaOfB H P instances common proof pis
    let lk := lookupRunB H P instances common proof pis
    proof.opened.size = instances.length ∧ pis.length = instances.length ∧
      proof.permutationLocal.size = instances.length ∧
      proof.permutationNext.size = instances.length ∧
      proof.lookupTerminals.size = instances.length ∧
      proof.degreeBits.toList = instances.map (·.logN) ∧
      (∀ I ∈ instances, I.logN + I.logQuotientChunks ≤ twoAdicity F) ∧
      (∀ x ∈ instances.zip pis, x.2.length = x.1.air.numPublicValues) ∧
      (∀ x ∈ instances.zip proof.opened.toList, openedShapeOk x.1 x.2 = true) ∧
      common.preprocessed.isSome = instances.any (0 < ·.air.preprocessedWidth) ∧
      lookupShapeOk P instances proof = true ∧
      (hasLookups instances = true →
        (lookupCheckB H P instances common proof pis).1 = true) ∧
      (oodCheckB (EF := EF) H P instances common proof pis).1 = true ∧
      (∀ I ∈ instances, (Ext.powTwo zeta I.logN - 1 != 0) = true) ∧
      (batchCheckB H P instances common proof pis).1 = true ∧
      (∃ st, verifyFri H P proof.fri (batchRounds instances common proof zeta)
        (batchOfB H P instances common proof pis) (stateFriB H P instances common proof pis) =
          .ok ((), st)) ∧
      (∀ x ∈ instances.zipIdx.zip (proof.opened.toList.zip pis),
        instanceCheck x.1.1 x.2.1 x.2.2 (proof.permutationLocal.getD x.1.2 #[])
          (proof.permutationNext.getD x.1.2 #[]) ((CompStark.Lookup.challengeLayout
            (instances.map (·.lookups)) lk.1 lk.2).getD x.1.2 [])
          ((proof.lookupTerminals.getD x.1.2 none).getD 0) zeta
          (alphaOfB H P instances common proof pis) = true) ∧
      (proof.lookupTerminals.toList.filterMap id).foldl (· + ·) 0 = 0 := by
  intro zeta lk
  unfold verifyBatchWith at h
  obtain ⟨hcount, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨hdb, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨hq, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨-, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨hpub, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨hshape, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨hprep, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨hlk, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨-, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨-, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨x, hx, hc⟩ := except_bind_ok' _ _ h
  unfold StateT.run observeCap at hx
  rw [bind_ok_of H (observeList_eq H _ _), bind_ok_of H (observeExts_eq H _ _),
    bind_ok_of H (observeList_eq H _ _), bind_ok_of H (observeList_eq H _ _),
    bind_ok_of H (observeList_eq H _ _)] at hx
  obtain ⟨pair, s1, h1, hx⟩ := bind_eq_ok H hx
  obtain ⟨hlw, hpair⟩ := lookupPhase_ok H P instances proof _ _ h1
  simp only [Prod.mk.injEq] at hpair
  rw [hpair.1, hpair.2] at hx
  dsimp only at hx
  rw [bind_ok_of H (a := alphaOfB H P instances common proof pis)
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
  obtain ⟨hc, hc'⟩ := unless_ok _ _ _ _ hc
  obtain ⟨hsum, -⟩ := unless_ok _ _ _ _ hc'
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hcount hdb hq
  simp only [beq_iff_eq, List.all_eq_true] at hpub hshape
  simp only [beq_iff_eq, List.all_eq_true] at hprep hz hc hsum
  exact ⟨hcount.1.1.1.1, hcount.1.1.1.2, hcount.1.1.2, hcount.1.2, hcount.2, hdb, hq,
    fun x hx ↦ hpub x hx, hshape, hprep, hlk, hlw, hood, hz, hbc, ⟨_, hfri⟩, hc, hsum⟩

/-- An accepted batch proof's quotient cap is not empty. -/
theorem size_quotientCommit_neB (P : Params) (instances : List (Instance F)) (common : Common F)
    (proof : BatchProof F EF) (pis : List (List F))
    (h : verifyBatchWith H P instances common proof pis = .ok ()) :
    proof.quotientCommit.size ≠ 0 := by
  unfold verifyBatchWith at h
  obtain ⟨-, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨-, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨-, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨-, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨-, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨-, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨-, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨-, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨-, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨hq, -⟩ := unless_ok _ _ _ _ h
  simpa only [bne_iff_ne, ne_eq] using hq

end CompStark.Ni
