/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.StarkChallenges
public import CompStark.Fs.StarkTranscript

/-! # The ideal challenger's observations

On the ideal primitives of an answer table (`idealOf answer`), observing a list appends it to the
pending input (`obsList_idealOf`), and the verifier's observations of extension elements, points,
matrices and opened values are observations of their coefficient lists (`obsExts_eq`,
`obsPts_eq`, `obsMats_eq`, `obsOpened_eq`).
-/

@[expose] public section
namespace CompStark.Fs
open CompStark.Stark CompStark.Fri CompStark.RandomOracle OracleSpec OracleComp

variable {F : Type} {K : Nat}

/-! ### On any primitives -/

theorem obsList_append (H : Primitives F Id) (s : H.State) (a b : List F) :
    obsList H s (a ++ b) = obsList H (obsList H s a) b := List.foldl_append

variable [BaseField F] {EF : Type} [Challenge F EF] (answer : (q : Query F) → Answer K q)

/-! ### The ideal challenger on an answer table -/

theorem obsList_idealOf (s : Sponge F) (hs : s.samples = []) (xs : List F) :
    obsList (idealOf answer) s xs = ⟨s.cap, s.input ++ xs, []⟩ := by
  induction xs generalizing s with
  | nil => obtain ⟨c, i, l⟩ := s; dsimp only at hs; subst hs; simp only [obsList,
      List.foldl_nil, List.append_nil]
  | cons x xs ih =>
    rw [obsList, List.foldl_cons, ← obsList, ih _ rfl]
    simp only [idealOf, withAnswers, List.append_assoc, List.singleton_append]

theorem obsList_idealOf_mk (cap : Digest F) (input xs : List F) :
    obsList (idealOf answer) ⟨cap, input, []⟩ xs = ⟨cap, input ++ xs, []⟩ :=
  obsList_idealOf answer _ rfl xs

theorem obsList_idealOf_ne (s : Sponge F) (xs : List F) (hxs : xs ≠ []) :
    obsList (idealOf answer) s xs = ⟨s.cap, s.input ++ xs, []⟩ := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hxs
  rw [obsList, List.foldl_cons, ← obsList, obsList_idealOf answer _ rfl]
  simp only [idealOf, withAnswers, List.append_assoc, List.singleton_append]

theorem sample_idealOf_nil (cap : Digest F) (input : List F) :
    (idealOf answer).sample ⟨cap, input, []⟩ =
      ((answer (.duplex cap input)).2.toList.headD 0,
        ⟨(answer (.duplex cap input)).1, [], (answer (.duplex cap input)).2.toList.tail⟩) := rfl

/-! ### Observations as lists -/

theorem coeffs_append (a b : List EF) : coeffs (a ++ b) = coeffs a ++ coeffs b :=
  List.flatMap_append

theorem obsExts_eq (H : Primitives F Id) (s : H.State) (xs : List EF) :
    obsExts H s xs = obsList H s (coeffs xs) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [obsExts, List.foldl_cons, ← obsExts, ih, show x :: xs = [x] ++ xs from rfl,
      coeffs_append, obsList_append,
      show coeffs [x] = Ext.coeffs x from List.append_nil _]
    rfl

theorem obsPts_eq (H : Primitives F Id) (pts : List (EF × List EF)) (s : H.State) :
    pts.foldl (fun s p ↦ obsExts H s p.2) s = obsList H s (coeffs (pts.flatMap (·.2))) := by
  induction pts generalizing s with
  | nil => rfl
  | cons p pts ih => rw [List.foldl_cons, ih, obsExts_eq, List.flatMap_cons, coeffs_append,
      obsList_append]

theorem obsMats_eq (H : Primitives F Id) (mats : List (Domain F × List (EF × List EF)))
    (s : H.State) :
    mats.foldl (fun s m ↦ m.2.foldl (fun s p ↦ obsExts H s p.2) s) s =
      obsList H s (coeffs (mats.flatMap fun m ↦ m.2.flatMap (·.2))) := by
  induction mats generalizing s with
  | nil => rfl
  | cons m mats ih => rw [List.foldl_cons, ih, obsPts_eq, List.flatMap_cons, coeffs_append,
      obsList_append]

theorem obsOpened_eq (H : Primitives F Id) (s : H.State) (rounds : List (Round F EF)) :
    obsOpened H s rounds = obsList H s (coeffs (roundValues rounds)) := by
  induction rounds generalizing s with
  | nil => rfl
  | cons r rounds ih =>
    rw [obsOpened, List.foldl_cons, ← obsOpened, ih, obsMats_eq,
      show roundValues (r :: rounds) = r.2.flatMap (fun m ↦ m.2.flatMap (·.2)) ++
        roundValues rounds from List.flatMap_cons, coeffs_append, obsList_append]

/-! ### Round by round -/

section Rounds
variable (P : Params) (A : Air F) (vk : Option (PreprocessedKey F)) (proof : Proof F EF)
  (pis : List F)

end Rounds

end CompStark.Fs

/-! ## The PCS's claimed evaluation counts

`pcsCountsS`: the claimed evaluation counts of a proof for a setup, the static layout in which the
PCS observes the opened values.
-/

@[expose] public section
namespace CompStark.Fs
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop CompStark.RandomOracle
open Polynomial Fri.Spec OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### The transcript of a prefix -/

section Prefix
variable (S : Iop.Setup EF) [S.Folds]

/-- The claimed evaluation counts of a proof for `S`. -/
def pcsCountsS : List (List (List Nat)) :=
  [[S.air.width :: if S.air.mainNextRow then [S.air.width] else []],
    List.replicate S.chunks [Challenge.d EF]] ++
    if S.air.preprocessedWidth = 0 then [] else
      [[S.air.preprocessedWidth ::
        if S.air.opensPreprocessedNext then [S.air.preprocessedWidth] else []]]

variable (publicValues : List F) (δ δ' loss : NNReal)

end Prefix

end CompStark.Fs
