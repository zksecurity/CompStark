/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BatchQueryBound
public import CompStark.Ni.BatchExtracted
public import CompStark.Ni.Lengths

/-! # The batch's trace lengths from the proof

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
namespace CompStark.Ni
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

end CompStark.Ni

namespace CompStark.Iop.Batch.Statement
open CompStark.Stark CompStark.Fri CompStark.Ni CompStark.RandomOracle OracleSpec OracleComp

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
