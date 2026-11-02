/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.Samples
public import CompStark.Fs.Observations
public import CompStark.Fs.StarkSetup
public import CompStark.Fs.DomainSeparator

/-! # Trace lengths from the proof

The verifier takes the trace length from the proof. An accepted proof's length is one the
statement admits (`Statement.admits_of_ok`): the verifier checks the quotient domain and the
periodic columns, FRI checks its parameters and that `L` fits the two-adic subgroups, and the shape
check ties a preprocessed AIR's proofs to its verifying key's length (`degreeBits_of_shapeOk`). At
an admitted length, the setup's verifying key on an answer table is the statement's
(`preprocessedKeyWith_setupAt`).
-/

@[expose] public section
namespace CompStark.Fs
open CompStark.Stark CompStark.Fri CompStark.Iop CompStark.RandomOracle OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-! ### Verifying keys -/

/-- The verifying key is the same at two lengths if the AIR has no preprocessed columns. -/
theorem preprocessedKeyWith_congr {m : Type → Type} [Monad m] (H : Primitives F m) (P : Params)
    (A : Air F) {n n' : Nat} (h : 0 < A.preprocessedWidth → n = n') :
    preprocessedKeyWith H P A n = preprocessedKeyWith H P A n' := by
  unfold preprocessedKeyWith
  by_cases hw : A.preprocessedWidth = 0
  · simp only [hw, ↓reduceIte]
  · rw [h (Nat.pos_of_ne_zero hw)]

/-- On pure primitives, a preprocessed AIR has a verifying key, of the length it is computed
at. -/
theorem exists_preprocessedKeyWith (H : Primitives F Id) (P : Params) (A : Air F) (n : Nat)
    (hw : 0 < A.preprocessedWidth) :
    ∃ k, preprocessedKeyWith H P A n = some k ∧ k.degreeBits = n := by
  unfold preprocessedKeyWith
  simp only [show A.preprocessedWidth ≠ 0 from Nat.pos_iff_ne_zero.mp hw, ↓reduceIte]
  exact ⟨_, rfl, rfl⟩

/-- Every matrix the verifier opens at `ζ` has the trace's length. -/
theorem logSize_openingRounds (A : Air F) (vk : Option (PreprocessedKey F)) (proof : Proof F EF)
    (zeta : EF) : ∀ x ∈ openingRounds A vk proof zeta, ∀ dp ∈ x.2,
      dp.1.logSize = proof.degreeBits := by
  intro x hx dp hdp
  simp only [openingRounds, List.cons_append, List.nil_append, List.mem_cons] at hx
  rcases hx with rfl | rfl | hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hdp
    rw [hdp]
  · obtain ⟨ch, -, rfl⟩ := List.mem_map.mp hdp
    rfl
  · unfold preprocessedRound at hx
    split at hx
    · rw [List.mem_singleton] at hx
      subst hx
      rw [List.mem_singleton] at hdp
      rw [hdp]
    · exact absurd hx List.not_mem_nil

/-- An accepting FRI verifier on the trace's rounds folds down to the final polynomial's length:
the trace is at least as long, the query's checks ending at the final height. -/
theorem finalPolyFits_of_verifyFri (H : Primitives F Id) (P : Params) (A : Air F)
    (vk : Option (PreprocessedKey F)) (proof : Proof F EF) (zeta alpha : EF) (s : H.State)
    (r : Unit × H.State)
    (h : verifyFri H P proof.fri (openingRounds A vk proof zeta) alpha s = .ok r) :
    P.logFinalPolyLen ≤ proof.degreeBits := by
  obtain ⟨hq, -, -, -⟩ := verifyFri_checks H _ _ _ _ _ _ h
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨-, hfolds, -, -, -, -, -, hok⟩ := verifyFri_ok H P proof.fri _ alpha
    (proof.degreeBits + P.logBlowup)
    (fun x hx dp hdp ↦ by rw [logSize_openingRounds A vk proof zeta x hx dp hdp]) s r h
  have har : foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen)
      (proof.degreeBits + P.logBlowup) [proof.degreeBits + P.logBlowup] = [] := by
    cases hm : proof.degreeBits + P.logBlowup with
    | zero => rfl
    | succ m =>
      have hle : m + 1 ≤ P.logBlowup + P.logFinalPolyLen := by omega
      simp only [foldSchedule, hle, ↓reduceIte]
  obtain ⟨-, -, -, hfin, -⟩ := hok 0 hq
  simp only [har, querySteps, List.zip_nil_left, List.map_nil, List.zip_nil_right,
    List.length_nil, foldState_zero] at hfin
  omega

omit [BaseField F] [Challenge F EF] in
/-- A proof that passes the shape check against a key has the key's length. -/
theorem degreeBits_of_shapeOk {A : Air F} {k : PreprocessedKey F} {o : OpenedValues EF}
    {db : Nat} (h : preprocessedShapeOk A (some k) o db = true) : k.degreeBits = db := by
  rcases o with ⟨tl, tn, _ | l, n, qc⟩
  · simp only [preprocessedShapeOk, Bool.false_eq_true] at h
  · simp only [preprocessedShapeOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact h.1.1.2

end CompStark.Fs

namespace CompStark.Iop.Statement
open CompStark.Stark CompStark.Fri CompStark.Fs CompStark.RandomOracle OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] (C : Statement F)

/-- **An accepted proof's length is admitted.** -/
theorem admits_of_ok {K : Nat} (answer : (q : Query F) → Answer K q) (proof : Proof F EF)
    (pis : List F)
    (hok : verifyWith (idealOf answer) C.params C.air
      (preprocessedKeyWith (idealOf answer) C.params C.air C.preprocessedLogN) proof pis = .ok ()) :
    C.Admits proof.degreeBits := by
  obtain ⟨-, -, -, -, hshape, hdeg, -, -, -, -, ⟨st, hfri⟩, -⟩ :=
    verifyWith_ok (idealOf answer) C.params C.air _ proof pis hok
  obtain ⟨hq, hb, ha, hmax⟩ := verifyFri_checks (idealOf answer) _ _ _ _ _ _ hfri
  have hfin := finalPolyFits_of_verifyFri (idealOf answer) _ _ _ _ _ _ _ _ hfri
  rw [heights_openingRounds, List.headD_cons] at hmax
  refine ⟨⟨C.colsInWidth, periodicFits_of_ok (idealOf answer) _ _ _ proof pis hok, hmax, hdeg, ha,
    hfin, hq, hb⟩, fun hw ↦ ?_⟩
  obtain ⟨k, hk, hkd⟩ := exists_preprocessedKeyWith (idealOf answer) C.params C.air
    C.preprocessedLogN hw
  rw [hk] at hshape
  rw [← degreeBits_of_shapeOk hshape, hkd]

/-- At an admitted length, the setup's verifying key on an answer table is the statement's. -/
theorem preprocessedKeyWith_setupAt {K : Nat} (answer : (q : Query F) → Answer K q) (n : Nat)
    (h : C.Admits n) :
    preprocessedKeyWith (idealOf answer) (C.setupAt EF n h).params (C.setupAt EF n h).air
      (C.setupAt EF n h).logN =
      preprocessedKeyWith (idealOf answer) C.params C.air C.preprocessedLogN :=
  preprocessedKeyWith_congr _ _ _ h.preprocessed

end CompStark.Iop.Statement

namespace CompStark.Fs
open CompStark.Stark CompStark.Fri CompStark.Iop CompStark.RandomOracle OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-! ### One length per duplex call -/

end CompStark.Fs
