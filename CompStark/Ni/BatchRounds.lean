/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BatchParse
public import CompStark.Ni.BcsChallenges
public import CompStark.Ni.Rounds

/-! # The batch PCS's observations

The values the batch verifier's PCS observes, laid out by instance: every instance's opened trace,
quotient, preprocessed and permutation values (`mainVals`, `quotVals`, `prepVals`, `permVals`,
`roundValues_batchRounds_eq`), observed in the static counts `countsB`
(`claimCounts_batchRounds_eq`). The domain separators of the batch and of its PCS on a proof for a
setup (`batchSeedS`, `pcsSeedB`); the batch's depends on the AIRs and the instances' lookups only
(`batchSeedS_eq`).
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop CompStark.RandomOracle
open Polynomial OracleSpec OracleComp

variable {F : Type} {EF : Type}

local notation "𝕂" => Challenge.Spec EF

/-! ### The opened values' layout -/

section Values

/-- An instance's opened trace values, in the order the verifier observes them. -/
def mainVals (A : Air F) (o : OpenedValues EF) : List EF :=
  o.traceLocal.toList ++ if A.mainNextRow then (o.traceNext.getD #[]).toList else []

/-- An instance's opened quotient values. -/
def quotVals (o : OpenedValues EF) : List EF := o.quotientChunks.toList.flatMap (·.toList)

/-- An instance's opened preprocessed values. -/
def prepVals (A : Air F) (o : OpenedValues EF) : List EF :=
  if 0 < A.preprocessedWidth then
    (o.preprocessedLocal.getD #[]).toList ++
      if A.opensPreprocessedNext then (o.preprocessedNext.getD #[]).toList else []
  else []

/-- An instance's opened permutation values, at `ζ` and `ζ ω`, if it has lookups. -/
def permVals (lookups : List (Lookup F)) (cur next : Array EF) : List EF :=
  if lookups.isEmpty then [] else cur.toList ++ next.toList

theorem flatMap_filter_ite {α β : Type} (p : α → Bool) (f : α → List β) :
    ∀ L : List α, (L.filter p).flatMap f = L.flatMap fun a ↦ if p a then f a else []
  | [] => rfl
  | a :: L => by
    by_cases h : p a = true
    · rw [List.filter_cons_of_pos h, List.flatMap_cons, List.flatMap_cons,
        flatMap_filter_ite p f L, ite_eq_left_of_eq_true _ _ (eq_true h)]
    · rw [List.filter_cons_of_neg h, List.flatMap_cons, flatMap_filter_ite p f L,
        ite_eq_right_of_eq_false _ _ (eq_false h), List.nil_append]

theorem traceOpenings_values (A : Air F) (o : OpenedValues EF) (z zn : EF) :
    (traceOpenings A o z zn).flatMap (·.2) = mainVals A o := by
  by_cases h : A.mainNextRow = true
  · simp only [traceOpenings, mainVals, h, ↓reduceIte, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
  · simp only [traceOpenings, mainVals, h, ↓reduceIte, Bool.false_eq_true, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]

theorem traceOpenings_counts (A : Air F) (o : OpenedValues EF) (z zn : EF)
    (htl : o.traceLocal.size = A.width) (htn : traceNextOk A o = true) :
    (traceOpenings A o z zn).map (·.2.length) =
      A.width :: if A.mainNextRow then [A.width] else [] := by
  unfold traceOpenings
  unfold traceNextOk at htn
  rcases h : o.traceNext with _ | r <;> rw [h] at htn
  · simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at htn
    simp only [htn, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil,
      Array.length_toList, htl]
  · simp only [Bool.and_eq_true, beq_iff_eq] at htn
    simp only [htn.1, ↓reduceIte, List.map_cons, List.map_nil, Array.length_toList, htl,
      Option.getD_some, htn.2]

end Values

section Layout
variable [BaseField F] [Challenge F EF] (S : Iop.Batch.Setup EF)

/-- The values the PCS observes, laid out by instance. -/
theorem roundValues_batchRounds_eq (common : CompStark.Batch.Common F)
    (proof : CompStark.Batch.BatchProof F EF) (hsize : proof.opened.size = S.k)
    (hlsize : proof.permutationLocal.size = S.k) (hnsize : proof.permutationNext.size = S.k)
    (z : EF) :
    roundValues (CompStark.Batch.batchRounds S.instances common proof z) =
      (List.finRange S.k).flatMap (fun i ↦ mainVals (S.air i)
        (proof.opened.toList.getD i noOpenings)) ++
      (List.finRange S.k).flatMap (fun i : Fin S.k ↦
        quotVals (proof.opened.toList.getD i noOpenings)) ++
      (match common.preprocessed with
        | some _ => (List.finRange S.k).flatMap fun i ↦ prepVals (S.air i)
            (proof.opened.toList.getD i noOpenings)
        | none => []) ++
      (match proof.permutationCommit with
        | some _ => (List.finRange S.k).flatMap fun i ↦ permVals (S.lookups i)
            (proof.permutationLocal.getD i #[]) (proof.permutationNext.getD i #[])
        | none => []) := by
  have hos : proof.opened.toList.length = S.k := by rw [Array.length_toList, hsize]
  have hcons : ∀ (r : Round F EF) (rs : List (Round F EF)),
      roundValues (r :: rs) = r.2.flatMap (fun m ↦ m.2.flatMap (·.2)) ++ roundValues rs :=
    fun _ _ ↦ List.flatMap_cons
  have happ : ∀ (rs rs' : List (Round F EF)),
      roundValues (rs ++ rs') = roundValues rs ++ roundValues rs' :=
    fun _ _ ↦ List.flatMap_append
  have hM : ((S.instances.zip proof.opened.toList).map fun x ↦
      ((⟨1, x.1.logN⟩ : Domain F), traceOpenings x.1.air x.2 z
        (z * Ext.ofBase (twoAdicGen x.1.logN)))).flatMap (fun m ↦ m.2.flatMap (·.2)) =
      (List.finRange S.k).flatMap (fun i ↦ mainVals (S.air i)
        (proof.opened.toList.getD i noOpenings)) := by
    rw [zip_instances S _ hos, List.flatMap_map, List.flatMap_map]
    exact List.flatMap_congr fun i _ ↦ traceOpenings_values _ _ _ _
  have hQ : ((S.instances.zip proof.opened.toList).flatMap fun x ↦
      x.2.quotientChunks.toList.map fun ch ↦
        ((⟨1, x.1.logN⟩ : Domain F), [(z, ch.toList)])).flatMap (fun m ↦ m.2.flatMap (·.2)) =
      (List.finRange S.k).flatMap (fun i : Fin S.k ↦
        quotVals (proof.opened.toList.getD i noOpenings)) := by
    rw [zip_instances S _ hos, List.flatMap_map, List.flatMap_assoc]
    refine List.flatMap_congr fun i _ ↦ ?_
    rw [List.flatMap_map, quotVals]
    refine List.flatMap_congr fun ch _ ↦ ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hP : roundValues (prepRounds S proof z common) =
      (match common.preprocessed with
        | some _ => (List.finRange S.k).flatMap fun i ↦ prepVals (S.air i)
            (proof.opened.toList.getD i noOpenings)
        | none => []) := by
    rw [prepRounds]
    cases common.preprocessed with
    | none => rfl
    | some root =>
      dsimp only
      rw [hcons]
      simp only [roundValues, List.flatMap_nil, List.append_nil]
      rw [zip_instances S _ hos, List.flatMap_map, List.filter_map, List.flatMap_map,
        flatMap_filter_ite]
      refine List.flatMap_congr fun i _ ↦ ?_
      by_cases hp : 0 < (S.air i).preprocessedWidth
      · by_cases h : (S.air i).opensPreprocessedNext = true <;>
          simp only [Function.comp_apply, prepVals, hp, decide_true, h, ↓reduceIte,
            Bool.false_eq_true, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      · simp only [Function.comp_apply, prepVals, hp, decide_false, ↓reduceIte,
          Bool.false_eq_true]
  have hR : roundValues (permRounds S proof z) =
      (match proof.permutationCommit with
        | some _ => (List.finRange S.k).flatMap fun i ↦ permVals (S.lookups i)
            (proof.permutationLocal.getD i #[]) (proof.permutationNext.getD i #[])
        | none => []) := by
    rw [permRounds]
    cases proof.permutationCommit with
    | none => rfl
    | some root =>
      dsimp only
      rw [hcons]
      simp only [roundValues, List.flatMap_nil, List.append_nil]
      rw [permMats_eq S proof z hlsize hnsize, permInsts, List.flatMap_map, flatMap_filter_ite]
      refine List.flatMap_congr fun i _ ↦ ?_
      by_cases hl : (S.lookups i).isEmpty = true
      · simp only [hl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, permVals]
      · simp only [hl, Bool.not_false, Bool.false_eq_true, ↓reduceIte, permVals,
          List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [batchRounds_cases, happ, happ, hcons, hcons, hM, hQ, hP, hR]
  simp only [roundValues, List.flatMap_nil, List.append_nil, List.append_assoc]

end Layout

/-! ### The static counts and domain separators -/

section Static
variable [BaseField F] [Challenge F EF] (S : Iop.Batch.Setup EF)

theorem hasPreprocessed_eq :
    S.hasPreprocessed = S.instances.any (0 < ·.air.preprocessedWidth) := by
  rw [Iop.Batch.Setup.hasPreprocessed, Iop.Batch.Setup.instances, List.ofFn_eq_map,
    List.ofFn_eq_map, List.any_map, List.any_map]
  rfl

/-- The claimed evaluation counts of a batch proof for `S`: every instance's trace at one or two
points, every quotient chunk at one, every preprocessed trace at one or two, and every permutation
trace at two. -/
def countsB : List (List (List Nat)) :=
  [(List.finRange S.k).map (fun i ↦
      (S.air i).width :: if (S.air i).mainNextRow then [(S.air i).width] else []),
    (List.finRange S.k).flatMap fun i ↦
      List.replicate (S.instanceSetup i).chunks [Challenge.d EF]] ++
    (if S.hasPreprocessed then
      [((List.finRange S.k).filter fun i ↦ 0 < (S.air i).preprocessedWidth).map fun i ↦
        (S.air i).preprocessedWidth ::
          if (S.air i).opensPreprocessedNext then [(S.air i).preprocessedWidth] else []]
    else []) ++
    if S.hasLookups then
      [((List.finRange S.k).filter fun i ↦ !(S.lookups i).isEmpty).map fun i ↦
        [Challenge.d EF * (S.instanceSetup i).permWidth,
          Challenge.d EF * (S.instanceSetup i).permWidth]]
    else []

/-- The PCS's domain separator on a batch proof for `S`. -/
def pcsSeedB : List F := DomainSeparator.pcsSeed F EF (countsB S) S.params.batchPowBits

/-- The batch's domain separator on a proof for `S`. -/
def batchSeedS : List F :=
  DomainSeparator.batchSeed F EF (S.instances.map (·.air.width))
    (S.instances.map (·.air.preprocessedWidth)) (S.instances.map (·.air.numPublicValues))
    S.hasPreprocessed (S.instances.countP (!·.lookups.isEmpty)) S.params.lookupPowBits
    S.params.oodPowBits

/-- The batch's domain separator depends on the AIRs and the instances' lookups only. -/
theorem batchSeedS_eq : batchSeedS S = DomainSeparator.batchSeed F EF
    (List.ofFn fun i ↦ (S.air i).width) (List.ofFn fun i ↦ (S.air i).preprocessedWidth)
    (List.ofFn fun i ↦ (S.air i).numPublicValues) S.hasPreprocessed
    ((List.ofFn S.lookups).countP (!·.isEmpty)) S.params.lookupPowBits S.params.oodPowBits := by
  have hmap : ∀ f : Air F → ℕ, S.instances.map (f ·.air) = List.ofFn fun i ↦ f (S.air i) :=
    fun f ↦ by rw [Iop.Batch.Setup.instances, List.map_ofFn]; rfl
  have hcount : S.instances.countP (!·.lookups.isEmpty) =
      (List.ofFn S.lookups).countP (!·.isEmpty) := by
    rw [Iop.Batch.Setup.instances, List.ofFn_eq_map, List.ofFn_eq_map, List.countP_map,
      List.countP_map]
    rfl
  rw [batchSeedS, hmap, hmap, hmap, hcount]

/-- **The PCS's counts are static.** On opened values in the instances' shapes, the PCS observes
the counts `countsB`. -/
theorem claimCounts_batchRounds_eq (common : CompStark.Batch.Common F)
    (proof : CompStark.Batch.BatchProof F EF) (hsize : proof.opened.size = S.k)
    (hlsize : proof.permutationLocal.size = S.k) (hnsize : proof.permutationNext.size = S.k)
    (hshape : ∀ i : Fin S.k, CompStark.Batch.openedShapeOk ⟨S.air i, S.logN i, S.lookups i⟩
      (proof.opened.toList.getD i noOpenings) = true)
    (hprep : common.preprocessed.isSome = S.instances.any (0 < ·.air.preprocessedWidth))
    (hpw : ∀ i : Fin S.k,
      (proof.permutationLocal.getD i #[]).size = Challenge.d EF * (S.instanceSetup i).permWidth ∧
      (proof.permutationNext.getD i #[]).size = Challenge.d EF * (S.instanceSetup i).permWidth)
    (hperm : proof.permutationCommit.isSome = S.hasLookups) (z : EF) :
    claimCounts (CompStark.Batch.batchRounds S.instances common proof z) = countsB S := by
  have hos : proof.opened.toList.length = S.k := by rw [Array.length_toList, hsize]
  have hsh := fun i ↦ openedShapeOk_spec (hshape i)
  dsimp only at hsh
  have hM : ((S.instances.zip proof.opened.toList).map fun x ↦
      ((⟨1, x.1.logN⟩ : Domain F), traceOpenings x.1.air x.2 z
        (z * Ext.ofBase (twoAdicGen x.1.logN)))).map (fun m ↦ m.2.map (·.2.length)) =
      (List.finRange S.k).map (fun i ↦
        (S.air i).width :: if (S.air i).mainNextRow then [(S.air i).width] else []) := by
    rw [zip_instances S _ hos, List.map_map, List.map_map]
    exact List.map_congr_left fun i _ ↦ traceOpenings_counts _ _ _ _ (hsh i).1 (hsh i).2.1
  have hQ : ((S.instances.zip proof.opened.toList).flatMap fun x ↦
      x.2.quotientChunks.toList.map fun ch ↦
        ((⟨1, x.1.logN⟩ : Domain F), [(z, ch.toList)])).map (fun m ↦ m.2.map (·.2.length)) =
      (List.finRange S.k).flatMap fun i ↦
        List.replicate (S.instanceSetup i).chunks [Challenge.d EF] := by
    rw [zip_instances S _ hos, List.flatMap_map, List.map_flatMap]
    refine List.flatMap_congr fun i _ ↦ ?_
    rw [List.map_map, List.eq_replicate_iff, List.length_map, Array.length_toList]
    refine ⟨(hsh i).2.2.1.trans (congrArg (2 ^ ·) (logChunks_eq S i).symm), fun l hl ↦ ?_⟩
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.mp hl
    simp only [Function.comp_apply, List.map_cons, List.map_nil, Array.length_toList,
      (hsh i).2.2.2.1 ch (Array.mem_toList_iff.mp hch)]
  have hR : (permRounds S proof z).map (fun r ↦ r.2.map fun m ↦ m.2.map (·.2.length)) =
      if S.hasLookups then
        [((List.finRange S.k).filter fun i ↦ !(S.lookups i).isEmpty).map fun i ↦
          [Challenge.d EF * (S.instanceSetup i).permWidth,
            Challenge.d EF * (S.instanceSetup i).permWidth]]
      else [] := by
    rw [permRounds, ← hperm]
    cases proof.permutationCommit with
    | none => rfl
    | some root =>
      simp only [Option.isSome_some, ↓reduceIte, List.map_cons, List.map_nil, List.cons.injEq,
        and_true]
      rw [permMats_eq S proof z hlsize hnsize, permInsts, List.map_map]
      refine List.map_congr_left fun i _ ↦ ?_
      simp only [Function.comp_apply, List.map_cons, List.map_nil, Array.length_toList,
        (hpw i).1, (hpw i).2]
  rw [batchRounds_cases, claimCounts, List.map_append, List.map_append, List.map_cons,
    List.map_cons, List.map_nil, hR]
  dsimp only
  rw [hM, hQ, countsB, hasPreprocessed_eq, ← hprep]
  congr 2
  rw [prepRounds]
  cases common.preprocessed with
  | none => rfl
  | some root =>
    simp only [Option.isSome_some, ↓reduceIte, List.map_cons, List.map_nil, List.cons.injEq,
      and_true]
    rw [zip_instances S _ hos, List.filter_map, List.map_map, List.map_map]
    refine List.map_congr_left fun i hi ↦ ?_
    have hp : 0 < (S.air i).preprocessedWidth := by
      simpa using (List.mem_filter.mp hi).2
    obtain ⟨-, -, -, -, hpl, hpn⟩ := hsh i
    by_cases h : (S.air i).opensPreprocessedNext = true
    · have hw : (S.air i).preprocessedNextWidth = (S.air i).preprocessedWidth := by
        simp only [Air.preprocessedNextWidth, h, ↓reduceIte]
      simp only [Function.comp_apply, h, ↓reduceIte, List.map_cons, List.map_nil,
        Array.length_toList, hpl, hpn, hw]
    · simp only [Function.comp_apply, h, Bool.false_eq_true, ↓reduceIte, List.map_cons,
        List.map_nil, Array.length_toList, hpl]

end Static

/-! ### The transcript of a prefix -/

section Prefix
variable [BaseField F] [Challenge F EF] (S : Iop.Batch.Setup EF)

/-- The levels below fold `j`'s commitment: the tallest extended trace's, less the arities of the
folds up to `j`. -/
def friDepthB (j : ℕ) : ℕ := S.logTop - (S.friArities.take (j + 1)).sum

variable (publicValues : Fin S.k → List F) (δ δ' loss : NNReal)

end Prefix

end CompStark.Ni
