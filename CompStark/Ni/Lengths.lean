/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BadQuery
public import CompStark.Ni.Seed

/-! # Trace lengths from the proof

The verifier takes the trace length from the proof. Against an answer table:

* an accepted proof's length is one the statement admits (`Statement.admits_of_ok`): the verifier
  checks the quotient domain and the periodic columns, FRI checks its parameters and that `L`
  fits the two-adic subgroups, and the shape check ties a preprocessed AIR's proofs to its
  verifying key's length;
* at an admitted length, the setup's verifying key is the statement's (`setupRo_setupAt`), and
  the digests a round binds are the same at every length (`boundDigests_setupAt`), the STARK's
  domain separator having one length;
* a duplex call is bad for at most one trace length (`eq_of_roundBad`): its first round observes
  the STARK's domain separator of that length first, and the domain separator fixes the length
  (`DomainSeparator.starkSeedOf_inj`).
-/

@[expose] public section
namespace CompStark.Ni
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

omit [BaseField F] [Challenge F EF] in
/-- A proof that passes the shape check against a key has the key's length. -/
theorem degreeBits_of_shapeOk {A : Air F} {k : PreprocessedKey F} {o : OpenedValues EF}
    {db : Nat} (h : preprocessedShapeOk A (some k) o db = true) : k.degreeBits = db := by
  rcases o with ⟨tl, tn, _ | l, n, qc⟩
  · simp only [preprocessedShapeOk, Bool.false_eq_true] at h
  · simp only [preprocessedShapeOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact h.1.1.2

end CompStark.Ni

namespace CompStark.Iop.Statement
open CompStark.Stark CompStark.Fri CompStark.Ni CompStark.RandomOracle OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] (C : Statement F)

/-- **An accepted proof's length is admitted.** -/
theorem admits_of_ok {K : Nat} (answer : (q : Query F) → Answer K q) (proof : Proof F EF)
    (pis : List F)
    (hok : verifyWith (idealOf answer) C.params C.air
      (preprocessedKeyWith (idealOf answer) C.params C.air C.preprocessedLogN) proof pis = .ok ())
    (hf : C.params.logFinalPolyLen < proof.degreeBits) : C.Admits proof.degreeBits := by
  obtain ⟨-, -, -, -, hshape, hdeg, -, -, -, -, ⟨st, hfri⟩, -⟩ :=
    verifyWith_ok (idealOf answer) C.params C.air _ proof pis hok
  obtain ⟨hq, hb, ha, hmax⟩ := verifyFri_checks (idealOf answer) _ _ _ _ _ _ hfri
  rw [heights_openingRounds, List.headD_cons] at hmax
  refine ⟨⟨C.colsInWidth, periodicFits_of_ok (idealOf answer) _ _ _ proof pis hok, hmax, hdeg, ha,
    hf.le, hq, hb⟩, fun hw ↦ ?_⟩
  obtain ⟨k, hk, hkd⟩ := exists_preprocessedKeyWith (idealOf answer) C.params C.air
    C.preprocessedLogN hw
  rw [hk] at hshape
  rw [← degreeBits_of_shapeOk hshape, hkd]

/-- At an admitted length, the setup's verifying key is the statement's. -/
theorem setupRo_setupAt (n : Nat) (h : C.Admits n) (hf : C.params.logFinalPolyLen < n) :
    (C.setupAt EF n h hf).setupRo = C.setupRo EF :=
  preprocessedKeyWith_congr _ _ _ h.preprocessed

/-- At an admitted length, the setup's verifying key on an answer table is the statement's. -/
theorem preprocessedKeyWith_setupAt {K : Nat} (answer : (q : Query F) → Answer K q) (n : Nat)
    (h : C.Admits n) (hf : C.params.logFinalPolyLen < n) :
    preprocessedKeyWith (idealOf answer) (C.setupAt EF n h hf).params (C.setupAt EF n h hf).air
      (C.setupAt EF n h hf).logN =
      preprocessedKeyWith (idealOf answer) C.params C.air C.preprocessedLogN :=
  preprocessedKeyWith_congr _ _ _ h.preprocessed

/-- The digests a duplex call's input binds, at every trace length. -/
noncomputable abbrev boundDigestsC : Digest F → List F → List (Digest F) :=
  boundDigestsOf C.params (starkSeedOf EF C.params C.air 0).length

theorem boundDigests_setupAt (n : Nat) (h : C.Admits n) (hf : C.params.logFinalPolyLen < n) :
    boundDigests (C.setupAt EF n h hf) = C.boundDigestsC (EF := EF) := by
  funext cap input
  show boundDigestsOf C.params (starkSeedOf EF C.params C.air n).length cap input = _
  rw [DomainSeparator.length_starkSeedOf EF _ _ n 0]

end CompStark.Iop.Statement

namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Iop CompStark.RandomOracle OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-! ### One length per duplex call -/

/-- The first round's input in the parse of a duplex call after the queries `pre`. -/
def firstBlock {K : Nat} (pre : QueryLog (spec F K)) : Query F → List F
  | .duplex cap input => match parse pre (.duplex cap input) with
    | some (steps, _) => (steps.map Prod.fst ++ [input]).getD 0 []
    | none => []
  | .leaf _ | .node .. => []

/-- A bad duplex call's first round observes the setup's domain separator first. -/
theorem prefix_firstBlock (S : Iop.Setup EF) (publicValues : List F) (δ δ' loss : NNReal)
    (pre : QueryLog (spec F S.streamLen)) (t : Query F) (u : Answer S.streamLen t)
    (h : RoundBad S publicValues δ δ' loss pre t u) : starkSeedS S <+: firstBlock pre t := by
  cases t with
  | duplex cap input =>
    unfold RoundBad at h
    unfold firstBlock
    dsimp only at h ⊢
    cases hp : parse pre (.duplex cap input) with
    | none => rw [hp] at h; exact absurd h id
    | some r =>
      obtain ⟨steps, rest⟩ := r
      rw [hp] at h
      exact h.1
  | leaf => exact absurd h id
  | node => exact absurd h id

/-- **One length per duplex call.** On fields of at least `2 ^ 8` elements with two-adicity
below `2 ^ 64`, a list starts with the STARK's domain separator of at most one admitted length. -/
theorem eq_of_seed_prefix (C : Statement F) (h8 : 2 ^ 8 ≤ Nat.card F)
    (h64 : twoAdicity F < 2 ^ 64) {n n' : Nat} (hn : C.Admits n) (hn' : C.Admits n')
    (b : List F) (h1 : starkSeedOf EF C.params C.air n <+: b)
    (h2 : starkSeedOf EF C.params C.air n' <+: b) : n = n' := by
  have hl := DomainSeparator.length_starkSeedOf EF C.params C.air n n'
  rw [List.prefix_iff_eq_take] at h1 h2
  have he : starkSeedOf EF C.params C.air n = starkSeedOf EF C.params C.air n' := by
    rw [h1, h2, hl]
  have := hn.sound.twoAdic
  have := hn'.sound.twoAdic
  exact DomainSeparator.starkSeedOf_inj EF h8 C.params C.air (by omega) (by omega) he

end CompStark.Ni
