/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BatchRounds
public import CompStark.Ni.Rounds

/-! # Facts about an accepted batch proof

An accepted batch proof has the instances' shapes (`shape_of_verifyInstancesWith`); without
lookups no instance has lookups (`lookups_eq_nil_of`); the batch's domain separator on a proof
with the setup's preprocessed commitment is the setup's (`batchSeedOf_eq`); and the observed
terminals read back as a list (`filterMap_id_eq`).
-/

@[expose] public section
namespace CompStark.Ni
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

end CompStark.Ni
