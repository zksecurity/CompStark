/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.BatchTranscript
public import CompStark.Fs.Observations
public import CompStark.Fs.BatchCalls
public import CompStark.Fs.StarkLengths

/-! # Facts about an accepted batch proof

An accepted batch proof has the instances' shapes (`shape_of_verifyInstancesWith`); without
lookups no instance has lookups (`lookups_eq_nil_of`); the batch's domain separator on a proof
with the setup's preprocessed commitment is the setup's (`batchSeedOf_eq`); and the observed
terminals read back as a list (`filterMap_id_eq`).
-/

@[expose] public section
namespace CompStark.Fs
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop CompStark.RandomOracle
open Polynomial OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-! ### Accepted proofs -/

section Accepted
variable (S : Iop.Batch.Setup EF) (H : Primitives F Id) (common : CompStark.Batch.Common F)
  (proof : CompStark.Batch.BatchProof F EF) (pis : List (List F))

/-- **The shape of an accepted batch proof.** One opened value set per instance, each in its
AIR's shape, the preprocessed commitment exactly when some instance has preprocessed columns,
permutation openings in their shapes and a terminal exactly for the instances with lookups, the
permutation commitment exactly with lookups, a commitment and grinding witness per fold, and a
final polynomial of its length. -/
theorem shape_of_verifyInstancesWith
    (h : CompStark.Batch.verifyInstancesWith H S.params S.instances common proof pis = .ok ()) :
    proof.opened.size = S.k ∧
      (∀ i : Fin S.k, CompStark.Batch.openedShapeOk ⟨S.air i, S.logN i, S.lookups i⟩
        (proof.opened.toList.getD i noOpenings) = true) ∧
      common.preprocessed.isSome = S.instances.any (0 < ·.air.preprocessedWidth) ∧
      proof.fri.commits.size = S.friArities.length ∧
      proof.fri.commitWitnesses.size = S.friArities.length ∧
      proof.fri.finalPoly.size = 2 ^ S.params.logFinalPolyLen ∧
      proof.permutationLocal.size = S.k ∧ proof.permutationNext.size = S.k ∧
      proof.lookupTerminals.size = S.k ∧
      (∀ i : Fin S.k,
        (proof.permutationLocal.getD i #[]).size = Challenge.d EF * (S.instanceSetup i).permWidth ∧
        (proof.permutationNext.getD i #[]).size = Challenge.d EF * (S.instanceSetup i).permWidth ∧
        (proof.lookupTerminals.getD i none).isSome = !(S.lookups i).isEmpty) ∧
      proof.permutationCommit.isSome = S.hasLookups := by
  obtain ⟨hsize, -, hlsize, hnsize, htsize, -, -, hshapeZ, hprepS, hlk, -, -, -, -,
    ⟨st, hfriOk⟩, -⟩ := verifyInstancesWith_ok H S.params S.instances common proof pis h
  obtain ⟨hpshapes, hperm, -⟩ := lookupShapeOk_spec S.params S.instances proof hlk
  rw [length_instances] at hsize hlsize hnsize htsize
  have hos : proof.opened.toList.length = S.k := by rw [Array.length_toList, hsize]
  have hD := descHeights_batchRounds S common proof
    (zetaOfB H S.params S.instances common proof pis) hsize
  have hok := verifyFri_okR H S.params proof.fri _ _ _ _ hfriOk
  dsimp only at hok
  rw [hD, List.headD_cons] at hok
  obtain ⟨-, -, -, -, -, hcs, hcw, hfp, -⟩ := hok
  exact ⟨hsize, fun i ↦ hshapeZ _ (zip_instances S _ hos ▸
    List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩), hprepS, hcs, hcw, hfp, hlsize, hnsize,
    htsize, permShapes S proof hlsize hnsize htsize hpshapes, hperm⟩

end Accepted

/-! ### Congruences -/

section Congr
variable (S : Iop.Batch.Setup EF)

/-- Without lookups, no instance has lookups. -/
theorem lookups_eq_nil_of (hl : S.hasLookups = false) (i : Fin S.k) : S.lookups i = [] := by
  by_contra hne
  have : S.hasLookups = true :=
    List.any_eq_true.mpr ⟨⟨S.air i, S.logN i, S.lookups i⟩, List.mem_ofFn.mpr ⟨i, rfl⟩, by
      rw [show (⟨S.air i, S.logN i, S.lookups i⟩ : CompStark.Batch.Instance F).lookups = S.lookups
          i from rfl]
      simpa only [Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff] using hne⟩
  rw [hl] at this
  exact Bool.false_ne_true this

end Congr

/-! ### The schedule of an accepted proof -/

section Schedule
variable (S : Iop.Batch.Setup EF) (common : CompStark.Batch.Common F)
  (proof : CompStark.Batch.BatchProof F EF) (pis : List (List F))

/-- The batch's domain separator on a proof with the setup's preprocessed commitment is `S`'s. -/
theorem batchSeedOf_eq
    (hprep : common.preprocessed.isSome = S.instances.any (0 < ·.air.preprocessedWidth)) :
    CompStark.Batch.batchSeedOf EF S.params S.instances common.preprocessed = batchSeedS S := by
  rw [CompStark.Batch.batchSeedOf, batchSeedS, hprep, hasPreprocessed_eq]

/-- The observed terminals, read back. -/
theorem filterMap_id_eq {k : ℕ} (ts : List (Option EF)) (hlen : ts.length = k) :
    ts.filterMap id = (List.finRange k).flatMap fun j : Fin k ↦ (ts.getD j.val none).toList := by
  subst hlen
  rw [List.filterMap_eq_flatMap_toList]
  conv_lhs => rw [← List.ofFn_getElem (xs := ts)]
  rw [List.ofFn_eq_map, List.flatMap_map]
  refine List.flatMap_congr fun j _ ↦ ?_
  rw [List.getD_eq_getElem _ _ j.isLt]
  rfl

end Schedule

end CompStark.Fs

/-! ## The batch's trace lengths from the proof

The batch verifier takes every instance's trace length from the proof. An accepted proof's lengths
are a vector the statement admits (`Statement.admits_of_ok`): the common data fixes the lengths of
the instances with preprocessed columns (`keyOk_of_ok`), the verifier checks the quotient domains,
the periodic columns and the lookups' multiplicity bound, and FRI checks its parameters, that the
tallest domain fits the two-adic subgroups and that every query folds every height down to the
final polynomial's, so every trace is at least as long as the final polynomial
(`logBlowup_add_le_of_verifyFri`). The batch's domain separator is the same at every vector of
lengths (`batchSeed`, `batchSeedS_setupAt`).
-/

@[expose] public section
namespace CompStark.Fs
open CompStark.Stark CompStark.Fri CompStark.Iop CompStark.RandomOracle OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-! ### FRI folds every height down to the final one -/

section Final

/-- The folds never raise the height. -/
theorem height_foldl_le : ∀ (l : List (EF × QueryFold EF)) (st : List (Nat × EF) × EF × Nat × Nat),
    (l.foldl (fun st x ↦ foldStepR x st) st).2.2.2 ≤ st.2.2.2
  | [], _ => le_rfl
  | x :: l, st => by
    rw [List.foldl_cons]
    refine (height_foldl_le l _).trans ?_
    rw [foldStepR_snd]
    exact Nat.sub_le _ _

/-- Folds that consume every pending reduced opening end at most at the height of each: a pending
opening is consumed when the folds reach its height, which only decreases. -/
theorem height_foldl_le_of_nil : ∀ (l : List (EF × QueryFold EF))
    (st : List (Nat × EF) × EF × Nat × Nat), (l.foldl (fun st x ↦ foldStepR x st) st).1 = [] →
      ∀ e ∈ st.1, (l.foldl (fun st x ↦ foldStepR x st) st).2.2.2 ≤ e.1
  | [], _, h, e, he => by rw [List.foldl_nil] at h; rw [h] at he; exact absurd he List.not_mem_nil
  | x :: l, ⟨ro, v, i, hgt⟩, h, e, he => by
    rw [List.foldl_cons] at h ⊢
    have ih := height_foldl_le_of_nil l _ h
    have hle := height_foldl_le l (foldStepR x (ro, v, i, hgt))
    rw [foldStepR_snd] at hle
    dsimp only at he hle
    cases ro with
    | nil => exact absurd he List.not_mem_nil
    | cons hr rest =>
      obtain ⟨h0, r⟩ := hr
      by_cases hh : h0 = hgt - x.2.logArity
      · have hs : (foldStepR x ((h0, r) :: rest, v, i, hgt)).1 = rest := by
          simp only [foldStepR, hh, beq_self_eq_true, ↓reduceIte]
        rcases List.mem_cons.mp he with rfl | he
        · dsimp only
          omega
        · exact ih e (by rw [hs]; exact he)
      · have hs : (foldStepR x ((h0, r) :: rest, v, i, hgt)).1 = (h0, r) :: rest := by
          simp only [foldStepR, beq_iff_eq, hh, ↓reduceIte]
        exact ih e (by rw [hs]; exact he)

variable (H : Primitives F Id)

/-- **An accepting FRI verifier on rounds of mixed heights opens no matrix shorter than the final
polynomial**: its first query folds from the tallest height and injects every shorter one when
the folds reach it, ending at the final height with nothing left. -/
theorem logBlowup_add_le_of_verifyFri (P : Params) (proof : FriProof F EF)
    (rounds : List (Round F EF)) (alpha : EF) (s : H.State) (r : Unit × H.State)
    (h : verifyFri H P proof rounds alpha s = .ok r) :
    ∀ a ∈ matHeights P rounds, P.logBlowup + P.logFinalPolyLen ≤ a := by
  have hok := verifyFri_okR H P proof rounds alpha s r h
  obtain ⟨hq, -, hne, -, -, -, -, -, -, -, hall⟩ := hok
  obtain ⟨-, -, -, hfin, hnil, -⟩ := hall 0 hq
  unfold foldStateR at hfin hnil
  rw [List.take_length] at hfin hnil
  intro a ha
  have hd := (mem_descHeights _ a).mpr ha
  cases hD : descHeights (matHeights P rounds) with
  | nil => rw [hD] at hd; exact absurd hd List.not_mem_nil
  | cons hd0 tl =>
    rw [hD] at hd hfin hnil
    simp only [List.tail_cons, List.headD_cons] at hfin hnil
    rcases List.mem_cons.mp hd with rfl | hd
    · rw [← hfin]
      exact height_foldl_le _ _
    · rw [← hfin]
      exact height_foldl_le_of_nil _ _ hnil (a, _) (List.mem_map.mpr ⟨a, hd, rfl⟩)

end Final

/-! ### The verifier's checks -/

/-- An accepting batch verifier checked every instance's periodic columns. -/
theorem periodicFits_of_verifyInstancesWith (H : Primitives F Id) (P : Params)
    (instances : List (CompStark.Batch.Instance F)) (common : CompStark.Batch.Common F)
    (proof : CompStark.Batch.BatchProof F EF) (pis : List (List F))
    (h : CompStark.Batch.verifyInstancesWith H P instances common proof pis = .ok ()) :
    ∀ I ∈ instances, I.air.periodicFits I.logN = true := by
  unfold CompStark.Batch.verifyInstancesWith at h
  obtain ⟨-, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨-, h⟩ := unless_ok _ _ _ _ h
  obtain ⟨hp, -⟩ := unless_ok _ _ _ _ h
  exact List.all_eq_true.mp hp

/-- An accepting batch verifier on pure primitives checked the common data. -/
theorem keyOk_of_ok (H : Primitives F Id) (P : Fri.Params) (airs : List (Air F))
    (common : CompStark.Batch.Common F) (proof : CompStark.Batch.BatchProof F EF)
    (pis : List (List F))
    (h : CompStark.Batch.verifyBatchWith H P airs common proof pis = .ok ()) :
    CompStark.Batch.keyOk airs common proof.degreeBits.toList = true := by
  unfold CompStark.Batch.verifyBatchWith at h
  split at h
  · assumption
  · exact absurd h (by intro h'; cases h')

omit [BaseField F] in
/-- The quotient chunks of an AIR's constraints are at most those with extension constraints. -/
theorem logQuotientChunks_le_with [Field F] (A : Air F) (logN : Nat)
    (ext : List (Lookup.ExtExpr F)) :
    A.logQuotientChunks logN ≤ A.logQuotientChunksWith logN ext := by
  unfold Air.logQuotientChunks Air.logQuotientChunksWith
  dsimp only
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.log_mono_right (by omega)

/-! ### One vector of lengths per duplex call -/

omit [Challenge F EF] in
/-- The two-adicity is below the number of elements. -/
theorem twoAdicity_lt_card : twoAdicity F < Nat.card F := by
  have hp := (BaseField.card_prime (F := F)).two_le
  have hd := Nat.le_of_dvd (by omega) (BaseField.two_pow_dvd_card_sub_one (F := F))
  have := Nat.lt_two_pow_self (n := twoAdicity F)
  omega

omit [Challenge F EF] in
/-- Numbers below `p` are distinct in `F`. -/
theorem natCast_inj_of_lt {a b : ℕ} (ha : a < Nat.card F) (hb : b < Nat.card F)
    (h : (a : F) = b) : a = b := by
  have hc : CharP F (Nat.card F) := BaseField.ringChar_eq_card (F := F) ▸ ringChar.charP F
  rw [CharP.natCast_eq_natCast F (Nat.card F)] at h
  exact Nat.ModEq.eq_of_lt_of_lt h ha hb

end CompStark.Fs

namespace CompStark.Iop.Batch.Statement
open CompStark.Stark CompStark.Fri CompStark.Fs CompStark.RandomOracle OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] (C : Statement F)

/-- The common data on pure primitives has the statement's keygen heights and lookups. -/
theorem commonWith_keyInstances (H : Primitives F Id) :
    (CompStark.Batch.commonWith H C.params C.keyInstances).degreeBits = List.ofFn C.keyLogN ∧
      (CompStark.Batch.commonWith H C.params C.keyInstances).lookups = List.ofFn C.lookups := by
  refine ⟨?_, ?_⟩
  · show C.keyInstances.map (·.logN) = _
    rw [keyInstances, instancesAt, List.map_ofFn]
    rfl
  · show C.keyInstances.map (·.lookups) = _
    rw [keyInstances, instancesAt, List.map_ofFn]
    rfl

/-- **An accepted proof's lengths are admitted.** -/
theorem admits_of_ok {K : Nat} (answer : (q : Query F) → Answer K q)
    (proof : CompStark.Batch.BatchProof F EF) (pis : List (List F))
    (hok : CompStark.Batch.verifyBatchWith (idealOf answer) C.params C.airs
      (CompStark.Batch.commonWith (idealOf answer) C.params C.keyInstances) proof pis = .ok ()) :
    C.Admits (C.lengthsOf proof) := by
  obtain ⟨hd, hl⟩ := C.commonWith_keyInstances (idealOf answer)
  set common := CompStark.Batch.commonWith (idealOf answer) C.params C.keyInstances
  have hkey := keyOk_of_ok _ _ _ _ _ _ hok
  have hdl := C.length_degreeBits_of_keyOk common proof hkey
  rw [CompStark.Batch.verifyBatchWith_of_keyOk _ _ _ _ _ _ hkey,
    C.instancesOf_eq common hl proof hdl] at hok
  set n := C.lengthsOf proof
  have hper := periodicFits_of_verifyInstancesWith _ _ _ _ _ _ hok
  obtain ⟨hsize, -, -, -, -, hq, -, -, -, hlk, -, -, -, -, ⟨st, hfri⟩, -⟩ :=
    verifyInstancesWith_ok (idealOf answer) C.params (C.instancesAt n) common proof pis hok
  obtain ⟨hnq, hb, ha, hmax⟩ := verifyFri_checks (idealOf answer) _ _ _ _ _ _ hfri
  have hfin := logBlowup_add_le_of_verifyFri (idealOf answer) _ _ _ _ _ _ hfri
  have hI : ∀ i, (⟨C.air i, n i, C.lookups i⟩ : CompStark.Batch.Instance F) ∈ C.instancesAt n :=
    fun i ↦ List.mem_ofFn.mpr ⟨i, rfl⟩
  have hext : ∀ i, n i + C.params.logBlowup ∈ matHeights C.params
      (CompStark.Batch.batchRounds (C.instancesAt n) common proof
        (zetaOfB (idealOf answer) C.params (C.instancesAt n) common proof pis)) := fun i ↦
    (CompStark.Batch.mem_matHeights_batchRounds _ _ _ _ _ hsize _).mpr ⟨_, hI i, rfl⟩
  have hquot : ∀ i, n i + (C.air i).logQuotientChunksWith (n i)
      (Lookup.logUpConstraints (C.lookups i)) ≤ twoAdicity F := fun i ↦ hq _ (hI i)
  refine ⟨fun i ↦ ⟨C.colsInWidth i, hper _ (hI i), ?_, ?_, ha, ?_, hnq, hb⟩, hquot, ?_, ?_⟩
  · refine le_trans ?_ hmax
    exact CompStark.Batch.headD_le_of_mem (pairwise_descHeights _)
      ((mem_descHeights _ _).mpr (hext i))
  · exact (Nat.add_le_add_left (logQuotientChunks_le_with _ _ _) _).trans (hquot i)
  · have := hfin _ (hext i)
    omega
  · intro i hw
    simp only [CompStark.Batch.keyOk, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      beq_iff_eq] at hkey
    have hi : i.val < (C.airs.zip (proof.degreeBits.toList.zip common.degreeBits)).length := by
      simp only [List.length_zip, airs, List.length_ofFn, hdl, hd, Nat.min_self]
      exact i.2
    rcases hkey.2 _ (List.getElem_mem hi) with h0 | h
    · simp only [List.getElem_zip, airs, List.getElem_ofFn, Fin.eta] at h0
      omega
    · simp only [List.getElem_zip, hd, List.getElem_ofFn, Fin.eta] at h
      rw [← h]
      show proof.degreeBits.toList.getD i 0 = _
      rw [List.getD_eq_getElem _ _ (by rw [hdl]; exact i.2)]
  · simp only [CompStark.Batch.lookupShapeOk, Bool.and_eq_true] at hlk
    have h := hlk.1.1.1.1.2
    rwa [instancesAt, List.map_ofFn] at h

variable (EF)

/-- The batch's domain separator, at every vector of lengths. -/
def batchSeed : List F :=
  DomainSeparator.batchSeed F EF (List.ofFn fun i ↦ (C.air i).width)
    (List.ofFn fun i ↦ (C.air i).preprocessedWidth) (List.ofFn fun i ↦ (C.air i).numPublicValues)
    C.hasPreprocessed ((List.ofFn C.lookups).countP (!·.isEmpty)) C.params.lookupPowBits
    C.params.oodPowBits

variable {EF}

theorem batchSeedS_setupAt (n : Fin C.k → ℕ) (h : C.Admits n) :
    batchSeedS (C.setupAt EF n h) = C.batchSeed EF :=
  batchSeedS_eq _

end CompStark.Iop.Batch.Statement
