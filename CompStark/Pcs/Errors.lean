/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.Parameters
public import CompStark.Multilinear.Basic

/-! Exact, unrounded per-challenge errors of a WHIR opening over the challenge field, one row per
verifier message in transcript order. Each level carries its own list bound. -/

@[expose] public section

namespace CompStark.Pcs

open CompStark.BinaryFields CompStark.Multilinear

noncomputable section

/-- One verifier message of a WHIR opening; OOD and query vectors are single messages. -/
inductive WhirChallenge where
  /-- The level's power batch over its claims. -/
  | batch (level : ℕ)
  /-- One fold coordinate of an encoded level. -/
  | fold (level coordinate : ℕ)
  /-- The OOD vector drawn after the next level's commitment. -/
  | ood (enteringLevel : ℕ)
  /-- The vector of independent column queries of a level. -/
  | queries (level : ℕ)
  /-- The final residual and sampled-column batch. -/
  | finalBatch
  /-- One coordinate of the closing plaintext sumcheck. -/
  | close (coordinate : ℕ)

/-- A verifier message and its local error. -/
structure WhirErrorRow where
  /-- The message and its position in the opening. -/
  challenge : WhirChallenge
  /-- The exact local error. -/
  error : ENNReal

/-- WHIR's error rows, with level-local real Johnson bounds and `claims` claims entering `level`. -/
def whirErrorRows : {vars : ℕ} → (schedule : Whir.Schedule K vars) →
    Whir.SecurityParameters schedule → ℕ → ℕ → List WhirErrorRow
  | _, .last lanes tail encoding queries, security, claims, level =>
      [⟨.batch level, Whir.batchError (E := E) encoding security claims⟩] ++
      (List.range lanes).map (fun i =>
        ⟨.fold level i, Whir.foldError (E := E) encoding security⟩) ++
      [⟨.queries level, Whir.queryError encoding security queries⟩,
        ⟨.finalBatch, overE queries⟩] ++
      (List.range tail).map (fun i => ⟨.close i, overE 2⟩)
  | _, .more lanes encoding queries rest, security, claims, level =>
      [⟨.batch level, Whir.batchError (E := E) encoding security.1 claims⟩] ++
      (List.range lanes).map (fun i =>
        ⟨.fold level i, Whir.foldError (E := E) encoding security.1⟩) ++
      [⟨.ood (level + 1), Whir.enteringOodError (E := E) rest security.2⟩,
        ⟨.queries level, Whir.queryError encoding security.1 queries⟩] ++
      whirErrorRows rest security.2 (queries + 2) (level + 1)

/-- The head level's real Johnson list bound, without rounding. -/
def initialListBound : {vars : ℕ} → (schedule : Whir.Schedule K vars) →
    Whir.SecurityParameters schedule → ℝ
  | _, .last _ _ encoding _, security => Whir.listBound encoding security
  | _, .more _ encoding _ _, security => Whir.listBound encoding security.1

/-- An error of a protocol run before the opening, fixed per candidate and of degree `degree`,
unioned over the opening's initial list. -/
def outerError (initialList : ℝ) (degree : ℕ) : ENNReal :=
  ENNReal.ofReal initialList * overE degree

end

end CompStark.Pcs
