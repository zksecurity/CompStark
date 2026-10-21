/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BatchChallenges
public import CompStark.Ni.Rounds

/-! # The batch rounds' bad events on duplex calls

As for the STARK (`Ni/Rounds.lean`): a fresh duplex call is bad (`RoundBadB`) when the queries
before it parse it as round `i` of a batch transcript and its answer makes round `i` bad
(`roundBadAtB`, the events of `Sound/BatchRbr.lean`) for the transcript read off the parsed
prefix and the cache of the earlier hash queries (`prefixTranscriptB`): every instance's trace
and quotient words are extracted under the digests rounds `0` and `1` observe, FRI's words under
those of the fold rounds; the openings are decoded from the batching round's observations
(`openingsAtB`), the final polynomial from the query round's; and the challenges are read off the
answers.

The decoder inverts the verifier's observations: on opened values of the instances' shapes, the
PCS observes the static counts `countsB` and the values in a static layout
(`claimCounts_batchRounds_eq`, `openingsAtB_coeffs`).
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop CompStark.RandomOracle
open Polynomial OracleSpec OracleComp

variable {F : Type} {EF : Type}

local notation "𝕂" => Challenge.Spec EF

/-! ### Blocks of a concatenation over the instances -/

section Blocks
variable {k : ℕ}

/-- The offset of block `i` of blocks of lengths `len`: the earlier blocks' lengths. -/
def blockOff (len : Fin k → ℕ) (i : Fin k) : ℕ := (((List.finRange k).take i).map len).sum

/-- The total length of blocks of lengths `len`. -/
def blockSum (len : Fin k → ℕ) : ℕ := ((List.finRange k).map len).sum

theorem length_flatMap_finRange {α : Type} (f : Fin k → List α) (len : Fin k → ℕ)
    (hlen : ∀ i, (f i).length = len i) : ((List.finRange k).flatMap f).length = blockSum len := by
  rw [List.length_flatMap, blockSum]
  exact congrArg List.sum (List.map_congr_left fun i _ ↦ hlen i)

theorem getD_flatMap_finRange {α : Type} (f : Fin k → List α) (len : Fin k → ℕ)
    (hlen : ∀ i, (f i).length = len i) (d : α) (i : Fin k) (c : ℕ) (hc : c < len i) :
    ((List.finRange k).flatMap f).getD (blockOff len i + c) d = (f i).getD c d := by
  have hik : i.val < (List.finRange k).length := by rw [List.length_finRange]; exact i.isLt
  have hfi : (List.finRange k)[i.val] = i := by
    rw [List.getElem_finRange]
    rfl
  have h := getD_flatMap_blocks f d (List.finRange k) i.val hik c (by rw [hfi, hlen]; exact hc)
  rw [hfi] at h
  rw [← h, blockOff]
  congr 2
  exact congrArg List.sum (List.map_congr_left fun i' _ ↦ (hlen i').symm)

theorem blockOff_add_le (len : Fin k → ℕ) (i : Fin k) : blockOff len i + len i ≤ blockSum len := by
  have hik : i.val < ((List.finRange k).map len).length := by
    rw [List.length_map, List.length_finRange]; exact i.isLt
  have h := List.sum_take_add_sum_drop ((List.finRange k).map len) i.val
  rw [List.drop_eq_getElem_cons hik, List.sum_cons, List.getElem_map, List.getElem_finRange] at h
  rw [blockOff, blockSum, List.map_take]
  have : len (Fin.cast (List.length_finRange (n := k)) ⟨i.val, by simp⟩) = len i := rfl
  omega

end Blocks

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

theorem flatMap_filter_ite {α β : Type} (p : α → Bool) (f : α → List β) :
    ∀ L : List α, (L.filter p).flatMap f = L.flatMap fun a ↦ if p a then f a else []
  | [] => rfl
  | a :: L => by
    by_cases h : p a = true
    · rw [List.filter_cons_of_pos h, List.flatMap_cons, List.flatMap_cons,
        flatMap_filter_ite p f L, ite_eq_left_of_eq_true _ _ (eq_true h)]
    · rw [List.filter_cons_of_neg h, List.flatMap_cons, flatMap_filter_ite p f L,
        ite_eq_right_of_eq_false _ _ (eq_false h), List.nil_append]

theorem flatMap_ite' {α β : Type} (c : Prop) [Decidable c] (A B : List α) (g : α → List β) :
    (if c then A else B).flatMap g = if c then A.flatMap g else B.flatMap g := by
  split <;> rfl

theorem traceOpenings_values (A : Air F) (o : OpenedValues EF) (z zn : EF) :
    (traceOpenings A o z zn).flatMap (·.2) = mainVals A o := by
  by_cases h : A.mainNextRow = true
  · simp only [traceOpenings, mainVals, h, ↓reduceIte, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
  · simp only [traceOpenings, mainVals, h, ↓reduceIte, Bool.false_eq_true, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]

theorem length_mainVals (A : Air F) (o : OpenedValues EF) (htl : o.traceLocal.size = A.width)
    (htn : traceNextOk A o = true) : (mainVals A o).length = A.width + A.mainNextWidth := by
  unfold mainVals Air.mainNextWidth
  unfold traceNextOk at htn
  rcases h : o.traceNext with _ | r <;> rw [h] at htn
  · simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at htn
    simp only [htn, Bool.false_eq_true, ↓reduceIte, List.append_nil, Array.length_toList, htl,
      Nat.add_zero]
  · simp only [Bool.and_eq_true, beq_iff_eq] at htn
    simp only [htn.1, ↓reduceIte, List.length_append, Array.length_toList, htl, Option.getD_some,
      htn.2]

theorem length_quotVals [BaseField F] [Challenge F EF] (o : OpenedValues EF) (n : ℕ)
    (hqc : o.quotientChunks.size = n) (hq4 : ∀ ch ∈ o.quotientChunks, ch.size = Challenge.d EF) :
    (quotVals o).length = Challenge.d EF * n := by
  rw [quotVals, List.length_flatMap, List.sum_eq_length_nsmul _ (Challenge.d EF) (by
    intro m hm
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.mp hm
    exact hq4 ch (Array.mem_toList_iff.mp hch)), List.length_map, Array.length_toList, hqc,
    smul_eq_mul, Nat.mul_comm]

theorem length_prepVals (A : Air F) (o : OpenedValues EF)
    (hpl : (o.preprocessedLocal.getD #[]).size = A.preprocessedWidth)
    (hpn : (o.preprocessedNext.getD #[]).size = A.preprocessedNextWidth) :
    (prepVals A o).length = A.preprocessedWidth + A.preprocessedNextWidth := by
  unfold prepVals
  have hle := A.preprocessedNextWidth_le
  split
  · by_cases h : A.opensPreprocessedNext = true
    · simp only [h, ↓reduceIte, List.length_append, Array.length_toList, hpl, hpn]
    · have : A.preprocessedNextWidth = 0 := by
        simp only [Air.preprocessedNextWidth, h, Bool.false_eq_true, ↓reduceIte]
      simp only [h, Bool.false_eq_true, ↓reduceIte, List.append_nil, Array.length_toList, hpl,
        this, Nat.add_zero]
  · rename_i h
    simp only [List.length_nil]
    omega

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

/-- Instance `i`'s number of opened trace values: its width, twice if it reads the next row. -/
def mainLenB (i : Fin S.k) : ℕ := (S.air i).width + (S.air i).mainNextWidth

/-- Instance `i`'s number of opened quotient values: `d` per chunk. -/
def quotLenB (i : Fin S.k) : ℕ := Challenge.d EF * (S.instanceSetup i).chunks

/-- Instance `i`'s number of opened preprocessed values. -/
def prepLenB (i : Fin S.k) : ℕ :=
  (S.air i).preprocessedWidth + (S.air i).preprocessedNextWidth

/-- Every instance's openings, decoded from the extension elements in `xs` in the order the batch
verifier observes them: every instance's trace values, then every instance's quotient chunks,
then every instance's preprocessed values. -/
noncomputable def openingsAtB (xs : List F) (i : Fin S.k) : Openings (S.instanceSetup i) where
  traceAt j := Challenge.toSpec (extFrom (EF := EF) xs (blockOff (mainLenB S) i + j))
  traceNext j := Challenge.toSpec (extFrom (EF := EF) xs
    (blockOff (mainLenB S) i + (S.air i).width + j))
  quotientAt c e := Challenge.toSpec (extFrom (EF := EF) xs
    (blockSum (mainLenB S) + blockOff (quotLenB S) i + (Challenge.d EF * c.val + e.val)))
  preprocessedAt j := Challenge.toSpec (extFrom (EF := EF) xs
    (blockSum (mainLenB S) + blockSum (quotLenB S) + blockOff (prepLenB S) i + j))
  preprocessedNext j := Challenge.toSpec (extFrom (EF := EF) xs
    (blockSum (mainLenB S) + blockSum (quotLenB S) + blockOff (prepLenB S) i +
      (S.air i).preprocessedWidth + j))

/-- The values the PCS observes, laid out by instance. -/
theorem roundValues_batchRounds_eq (common : CompStark.Batch.Common F)
    (proof : CompStark.Batch.BatchProof F EF) (hsize : proof.opened.size = S.k) (z : EF) :
    roundValues (CompStark.Batch.batchRounds S.instances common proof z) =
      (List.finRange S.k).flatMap (fun i ↦ mainVals (S.air i)
        (proof.opened.toList.getD i noOpenings)) ++
      (List.finRange S.k).flatMap (fun i : Fin S.k ↦
        quotVals (proof.opened.toList.getD i noOpenings)) ++
      (match common.preprocessed with
        | some _ => (List.finRange S.k).flatMap fun i ↦ prepVals (S.air i)
            (proof.opened.toList.getD i noOpenings)
        | none => []) := by
  have hos : proof.opened.toList.length = S.k := by rw [Array.length_toList, hsize]
  have hcons : ∀ (r : Round F EF) (rs : List (Round F EF)),
      roundValues (r :: rs) = r.2.flatMap (fun m ↦ m.2.flatMap (·.2)) ++ roundValues rs :=
    fun _ _ ↦ List.flatMap_cons
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
  have hP : (((S.instances.zip proof.opened.toList).filter
      (0 < ·.1.air.preprocessedWidth)).map fun x ↦ ((⟨1, x.1.logN⟩ : Domain F),
        (z, (x.2.preprocessedLocal.getD #[]).toList) ::
          if x.1.air.opensPreprocessedNext then
            [(z * Ext.ofBase (twoAdicGen x.1.logN), (x.2.preprocessedNext.getD #[]).toList)]
          else [])).flatMap (fun m ↦ m.2.flatMap (·.2)) =
      (List.finRange S.k).flatMap fun i ↦ prepVals (S.air i)
        (proof.opened.toList.getD i noOpenings) := by
    rw [zip_instances S _ hos, List.flatMap_map, List.filter_map, List.flatMap_map,
      flatMap_filter_ite]
    refine List.flatMap_congr fun i _ ↦ ?_
    by_cases hp : 0 < (S.air i).preprocessedWidth
    · by_cases h : (S.air i).opensPreprocessedNext = true <;>
        simp only [Function.comp_apply, prepVals, hp, decide_true, h, ↓reduceIte,
          Bool.false_eq_true, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    · simp only [Function.comp_apply, prepVals, hp, decide_false, ↓reduceIte,
        Bool.false_eq_true]
  rw [batchRounds_cases]
  cases common.preprocessed with
  | none =>
    rw [List.append_nil, hcons, hcons, hM, hQ]
    simp only [roundValues, List.flatMap_nil, List.append_nil]
  | some root =>
    rw [List.cons_append, List.cons_append, List.nil_append, hcons, hcons, hcons, hM, hQ, hP]
    simp only [roundValues, List.flatMap_nil, List.append_nil, List.append_assoc]

/-- **Decoding the opened values.** On opened values in the instances' shapes, the decoder reads
every instance's openings back from the values the PCS observes. -/
theorem openingsAtB_coeffs (common : CompStark.Batch.Common F)
    (proof : CompStark.Batch.BatchProof F EF) (hsize : proof.opened.size = S.k)
    (hshape : ∀ i : Fin S.k, CompStark.Batch.openedShapeOk (S.air i)
      (proof.opened.toList.getD i noOpenings) (S.logN i) = true)
    (hprep : common.preprocessed.isSome = S.instances.any (0 < ·.air.preprocessedWidth))
    (z : EF) (rest : List F) (i : Fin S.k) :
    openingsAtB S (coeffs (roundValues (CompStark.Batch.batchRounds S.instances common proof z)) ++
      rest) i = openingsOf (S.instanceSetup i) (proof.opened.toList.getD i noOpenings) := by
  have hsh := fun i ↦ openedShapeOk_spec (hshape i)
  set A := (List.finRange S.k).flatMap fun i ↦ mainVals (S.air i)
    (proof.opened.toList.getD i noOpenings) with hAdef
  set B := (List.finRange S.k).flatMap fun i : Fin S.k ↦
    quotVals (proof.opened.toList.getD i noOpenings) with hBdef
  set P := (List.finRange S.k).flatMap fun i ↦ prepVals (S.air i)
    (proof.opened.toList.getD i noOpenings) with hPdef
  have hmL : ∀ i : Fin S.k, (mainVals (S.air i) (proof.opened.toList.getD i noOpenings)).length =
      mainLenB S i := fun i ↦ length_mainVals _ _ (hsh i).1 (hsh i).2.1
  have hqL : ∀ i : Fin S.k, (quotVals (proof.opened.toList.getD i noOpenings)).length =
      quotLenB S i := fun i ↦ length_quotVals _ _ (hsh i).2.2.1 (hsh i).2.2.2.1
  have hpL : ∀ i : Fin S.k, (prepVals (S.air i) (proof.opened.toList.getD i noOpenings)).length =
      prepLenB S i := fun i ↦ length_prepVals _ _ (hsh i).2.2.2.2.1 (hsh i).2.2.2.2.2
  have hA : A.length = blockSum (mainLenB S) := length_flatMap_finRange _ _ hmL
  have hB : B.length = blockSum (quotLenB S) := length_flatMap_finRange _ _ hqL
  have hP : P.length = blockSum (prepLenB S) := length_flatMap_finRange _ _ hpL
  have hC : (match common.preprocessed with
      | some _ => P
      | none => []) = P := by
    cases hc : common.preprocessed with
    | some _ => rfl
    | none =>
      refine (List.flatMap_eq_nil_iff.mpr fun i _ ↦ ?_).symm
      have hpw : ¬ 0 < (S.air i).preprocessedWidth := fun hp ↦ by
        rw [hc] at hprep
        have : S.instances.any (0 < ·.air.preprocessedWidth) = true :=
          List.any_eq_true.mpr ⟨⟨S.air i, S.logN i⟩, List.mem_ofFn.mpr ⟨i, rfl⟩,
            decide_eq_true hp⟩
        rw [this] at hprep
        exact Bool.false_ne_true hprep
      simp only [prepVals, hpw, ↓reduceIte]
  rw [roundValues_batchRounds_eq S common proof hsize z, hC]
  have hx : ∀ k < (A ++ B ++ P).length,
      extFrom (EF := EF) (coeffs (A ++ B ++ P) ++ rest) k = (A ++ B ++ P).getD k 0 :=
    fun k hk ↦ by rw [extFrom_coeffs rest _ k hk, List.getD_eq_getElem _ _ hk]
  have hlen : (A ++ B ++ P).length =
      blockSum (mainLenB S) + blockSum (quotLenB S) + blockSum (prepLenB S) := by
    rw [List.length_append, List.length_append, hA, hB, hP]
  have hgA : ∀ k < blockSum (mainLenB S), (A ++ B ++ P).getD k 0 = A.getD k 0 := fun k hk ↦ by
    rw [List.append_assoc, List.getD_append _ _ _ _ (by omega)]
  have hgB : ∀ k < blockSum (quotLenB S),
      (A ++ B ++ P).getD (blockSum (mainLenB S) + k) 0 = B.getD k 0 := fun k hk ↦ by
    rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), hA,
      Nat.add_sub_cancel_left, List.getD_append _ _ _ _ (by omega)]
  have hgP : ∀ k < blockSum (prepLenB S),
      (A ++ B ++ P).getD (blockSum (mainLenB S) + blockSum (quotLenB S) + k) 0 = P.getD k 0 :=
    fun k hk ↦ by
      rw [List.getD_append_right _ _ _ _ (by rw [List.length_append]; omega),
        List.length_append, hA, hB, Nat.add_sub_cancel_left]
  have hmi := blockOff_add_le (mainLenB S) i
  have hqi := blockOff_add_le (quotLenB S) i
  have hpi := blockOff_add_le (prepLenB S) i
  obtain ⟨htl, htn, hqc, hq4, hpl, hpn⟩ := hsh i
  set o := proof.opened.toList.getD i noOpenings with ho
  cases hS : openingsOf (S.instanceSetup i) o with
  | mk ta tn qa pa pn =>
  have hta : ta = (openingsOf (S.instanceSetup i) o).traceAt := by rw [hS]
  have htn' : tn = (openingsOf (S.instanceSetup i) o).traceNext := by rw [hS]
  have hqa : qa = (openingsOf (S.instanceSetup i) o).quotientAt := by rw [hS]
  have hpa : pa = (openingsOf (S.instanceSetup i) o).preprocessedAt := by rw [hS]
  have hpn' : pn = (openingsOf (S.instanceSetup i) o).preprocessedNext := by rw [hS]
  subst hta htn' hqa hpa hpn'
  simp only [openingsAtB, Openings.mk.injEq]
  have hmw : mainLenB S i = (S.air i).width + (S.air i).mainNextWidth := rfl
  have hpw : prepLenB S i = (S.air i).preprocessedWidth + (S.air i).preprocessedNextWidth := rfl
  refine ⟨funext fun j ↦ ?_, funext fun j ↦ ?_, funext fun c ↦ funext fun e ↦ ?_,
    funext fun j ↦ ?_, funext fun j ↦ ?_⟩
  · have hj := j.isLt
    rw [hx _ (by omega), hgA _ (by omega), getD_flatMap_finRange _ _ hmL _ i j (by
      change j.val < (S.air i).width + _; omega), mainVals,
      List.getD_append _ _ _ _ (by rw [Array.length_toList, htl]; exact hj), toList_getD]
    rfl
  · have hj := j.isLt
    have hnr : (S.air i).mainNextRow = true := by
      by_contra h
      have : (S.air i).mainNextWidth = 0 := by
        simp only [Air.mainNextWidth, h, ↓reduceIte]
      change j.val < (S.air i).mainNextWidth at hj
      omega
    have hjw : j.val < (S.air i).width := by
      have := (S.air i).mainNextWidth_le; change j.val < (S.air i).mainNextWidth at hj; omega
    rw [hx _ (by change j.val < (S.air i).mainNextWidth at hj; omega),
      hgA _ (by change j.val < (S.air i).mainNextWidth at hj; omega), Nat.add_assoc,
      getD_flatMap_finRange _ _ hmL _ i _ (by change j.val < (S.air i).mainNextWidth at hj; omega),
      mainVals, List.getD_append_right _ _ _ _ (by rw [Array.length_toList, htl]; omega),
      Array.length_toList, htl, Nat.add_sub_cancel_left, ite_eq_left_of_eq_true _ _ (eq_true hnr),
      toList_getD]
    rfl
  · have hc := c.isLt
    have he := e.isLt
    have hce : Challenge.d EF * c.val + e.val < quotLenB S i :=
      (Nat.add_lt_add_left he _).trans_le (Nat.mul_le_mul_left _ hc)
    rw [hx _ (by omega), Nat.add_assoc, hgB _ (by omega),
      getD_flatMap_finRange _ _ hqL _ i _ hce, quotVals]
    have hL : ∀ l ∈ o.quotientChunks.toList.map (·.toList), l.length = Challenge.d EF := by
      intro l hl
      obtain ⟨ch, hch, rfl⟩ := List.mem_map.mp hl
      rw [Array.length_toList]
      exact hq4 ch (Array.mem_toList_iff.mp hch)
    have hfm : o.quotientChunks.toList.flatMap (·.toList) =
        (o.quotientChunks.toList.map (·.toList)).flatMap id := by
      rw [List.flatMap_map]; rfl
    have hcL : c.val < (o.quotientChunks.toList.map (·.toList)).length := by
      rw [List.length_map, Array.length_toList, hqc]; exact hc
    have hfl : Challenge.d EF * c.val + e.val <
        ((o.quotientChunks.toList.map (·.toList)).flatMap id).length := by
      rw [← hfm]
      have := length_quotVals o _ hqc hq4
      rw [quotVals] at this
      rw [this]
      exact hce
    rw [hfm, List.getD_eq_getElem _ _ hfl, getElem_flatMap_of_length _ _ hL _ _ hcL he]
    simp only [List.getElem_map, Array.getElem_toList]
    have hc' : c.val < o.quotientChunks.size := by rw [hqc]; exact hc
    have hch : o.quotientChunks.getD c.val #[] = o.quotientChunks[c.val] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hc', Option.getD_some]
    have he' : e.val < o.quotientChunks[c.val].size := by
      rw [hq4 _ (Array.getElem_mem hc')]; exact he
    show _ = Challenge.toSpec ((o.quotientChunks.getD c.val #[]).getD e.val 0)
    rw [hch, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem he', Option.getD_some]
  · have hj : j.val < (S.air i).preprocessedWidth := j.isLt
    have hp : 0 < (S.air i).preprocessedWidth := by omega
    rw [hx _ (by omega), Nat.add_assoc, hgP _ (by omega),
      getD_flatMap_finRange _ _ hpL _ i j (by omega), prepVals,
      ite_eq_left_of_eq_true _ _ (eq_true hp),
      List.getD_append _ _ _ _ (by rw [Array.length_toList, hpl]; exact hj), toList_getD]
    rfl
  · have hj := j.isLt
    change j.val < (S.air i).preprocessedNextWidth at hj
    have hle := (S.air i).preprocessedNextWidth_le
    have hp : 0 < (S.air i).preprocessedWidth := by omega
    have hnr : (S.air i).opensPreprocessedNext = true := by
      by_contra h
      have : (S.air i).preprocessedNextWidth = 0 := by
        simp only [Air.preprocessedNextWidth, h, ↓reduceIte]
      omega
    rw [hx _ (by omega), Nat.add_assoc (blockSum (mainLenB S) + blockSum (quotLenB S)),
      Nat.add_assoc, hgP _ (by omega), Nat.add_assoc,
      getD_flatMap_finRange _ _ hpL _ i _ (by omega), prepVals,
      ite_eq_left_of_eq_true _ _ (eq_true hp),
      List.getD_append_right _ _ _ _ (by rw [Array.length_toList, hpl]; omega),
      Array.length_toList, hpl, Nat.add_sub_cancel_left,
      ite_eq_left_of_eq_true _ _ (eq_true hnr), toList_getD]
    rfl

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
points, every quotient chunk at one, and every preprocessed trace at one or two. -/
def countsB : List (List (List Nat)) :=
  [(List.finRange S.k).map (fun i ↦
      (S.air i).width :: if (S.air i).mainNextRow then [(S.air i).width] else []),
    (List.finRange S.k).flatMap fun i ↦
      List.replicate (S.instanceSetup i).chunks [Challenge.d EF]] ++
    if S.hasPreprocessed then
      [((List.finRange S.k).filter fun i ↦ 0 < (S.air i).preprocessedWidth).map fun i ↦
        (S.air i).preprocessedWidth ::
          if (S.air i).opensPreprocessedNext then [(S.air i).preprocessedWidth] else []]
    else []

/-- The PCS's domain separator on a batch proof for `S`. -/
def pcsSeedB : List F := DomainSeparator.pcsSeed F EF (countsB S) S.params.batchPowBits

/-- The batch's domain separator on a proof for `S`. -/
def batchSeedS : List F :=
  DomainSeparator.batchSeed F EF (S.instances.map (·.air.width))
    (S.instances.map (·.air.preprocessedWidth)) (S.instances.map (·.air.numPublicValues))
    S.hasPreprocessed S.params.oodPowBits

/-- Where the main commitment sits in the first round's input: after the batch's domain separator
and every instance's degree bits. -/
def mainOffsetB : Nat := (batchSeedS S).length + Challenge.d EF * S.k

/-- **The PCS's counts are static.** On opened values in the instances' shapes, the PCS observes
the counts `countsB`. -/
theorem claimCounts_batchRounds_eq (common : CompStark.Batch.Common F)
    (proof : CompStark.Batch.BatchProof F EF) (hsize : proof.opened.size = S.k)
    (hshape : ∀ i : Fin S.k, CompStark.Batch.openedShapeOk (S.air i)
      (proof.opened.toList.getD i noOpenings) (S.logN i) = true)
    (hprep : common.preprocessed.isSome = S.instances.any (0 < ·.air.preprocessedWidth))
    (z : EF) : claimCounts (CompStark.Batch.batchRounds S.instances common proof z) = countsB S := by
  have hos : proof.opened.toList.length = S.k := by rw [Array.length_toList, hsize]
  have hsh := fun i ↦ openedShapeOk_spec (hshape i)
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
    refine ⟨(hsh i).2.2.1, fun l hl ↦ ?_⟩
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.mp hl
    simp only [Function.comp_apply, List.map_cons, List.map_nil, Array.length_toList,
      (hsh i).2.2.2.1 ch (Array.mem_toList_iff.mp hch)]
  rw [batchRounds_cases, claimCounts, List.map_append, List.map_cons, List.map_cons,
    List.map_nil]
  dsimp only
  rw [hM, hQ, countsB, hasPreprocessed_eq, ← hprep]
  congr 1
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

/-- The digest observed in a duplex call's input, the one a commitment round binds: the main
commitment after the batch's domain separator and the degree bits in the first round (initial
capacity), after FRI's domain separator in the first fold round (an input of its length), first
otherwise. -/
noncomputable def boundDigestB (cap : Digest F) (input : List F) : Digest F :=
  digestAt input (if cap = initCap then mainOffsetB S
    else if input.length = (friSeedB S).length + 8 + challengeOffset S.params.commitPowBits
      then (friSeedB S).length else 0)

/-- FRI's folding challenges in ArkLib's coordinate, from the answers `sample` of the fold rounds:
`s_j β_j`, `s_j` the shift of word `j`'s domain; none past the last fold. -/
noncomputable def betasAtB (sample : ℕ → Vector F S.streamLen) (j : ℕ) : 𝕂 :=
  if j < (friAritiesB S).length then
    lift gen ^ 2 ^ ((friAritiesB S).take j).sum *
      extAt (sample (3 + j)) (challengeOffset S.params.commitPowBits)
  else 0

/-- The batch transcript read off the inputs `block j` and answers `sample j` of the rounds `j`
and the hash queries `cache`: the words extracted under the observed digests, the observed
openings and final polynomial, and the challenges of the answers. -/
noncomputable def prefixTranscriptB (cache : Merkle.Cache F (Digest F)) (block : ℕ → List F)
    (sample : ℕ → Vector F S.streamLen) : Sound.Batch.Transcript S where
  trace i c x := Merkle.matColumn cache (digestAt (block 0) (mainOffsetB S)) S.logTop
    S.mainHeights S.mainWidths i c (S.logN i + S.params.logBlowup)
    (reverseBits x (S.logN i + S.params.logBlowup))
  alpha := extAt (sample 0) 0
  quotient i c e x := Merkle.matColumn cache (digestAt (block 1) 0) S.logTop (quotHeights S)
    (quotWidths S) (quotOffset S i + c) e (S.logN i + S.params.logBlowup)
    (reverseBits x (S.logN i + S.params.logBlowup))
  zeta := extAt (sample 1) (challengeOffset S.params.oodPowBits)
  openings := openingsAtB S ((block 2).drop (pcsSeedB S).length)
  batch := extAt (sample 2) (challengeOffset S.params.batchPowBits)
  words j m z := friWordAt cache
    (digestAt (block (3 + j)) (if j = 0 then (friSeedB S).length else 0)) m
    ((friAritiesB S).getD j 0) z.val
  finalPoly := finalPoly S.domainSetup
    (finalPolyAt S.domainSetup (block (3 + (friAritiesB S).length)))
  betas := betasAtB S sample

/-- The query round's grinding sample: the answer's first sample, `0` without grinding. -/
def powAtB (u : Vector F S.streamLen) : F :=
  if S.params.queryPowBits = 0 then 0 else u.toList.getD 0 0

/-- The query round's query samples, after the grinding sample. -/
def queriesAtB (u : Vector F S.streamLen) (j : Fin S.params.numQueries) : F :=
  u.toList.getD (challengeOffset S.params.queryPowBits + j.val) 0

variable (publicValues : Fin S.k → List F) (δ δ' loss : NNReal)

/-- Round `i`'s bad event (`Sound/BatchRbr.lean`) on the transcript `t`, whose round `i` was
answered `u`: `α`; `ζ`, batching and fold `i - 3`, each with its grinding sample, the answer's
first; and the queries. -/
def roundBadAtB (i : ℕ) (t : Sound.Batch.Transcript S) (u : Vector F S.streamLen) : Prop :=
  if i = 0 then Sound.Batch.AlphaBad S publicValues δ' t.trace t.alpha
  else if i = 1 then
    (S.params.oodPowBits ≠ 0 →
      CompPoly.CanonicalNat.toNat (u.toList.getD 0 0) % 2 ^ S.params.oodPowBits = 0) ∧
      Sound.Batch.ZetaBad S publicValues δ' t.trace t.alpha t.quotient t.zeta
  else if i = 2 then
    (S.params.batchPowBits ≠ 0 →
      CompPoly.CanonicalNat.toNat (u.toList.getD 0 0) % 2 ^ S.params.batchPowBits = 0) ∧
      Sound.Batch.BatchBad S publicValues δ δ' t.trace t.alpha t.quotient t.zeta t.openings
        t.batch
  else if i - 3 < (friAritiesB S).length then
    (S.params.commitPowBits ≠ 0 →
      CompPoly.CanonicalNat.toNat (u.toList.getD 0 0) % 2 ^ S.params.commitPowBits = 0) ∧
      Sound.Batch.FoldBad S δ loss t.rounds t.words (i - 3) (t.betas (i - 3))
  else if i = 3 + (friAritiesB S).length then
    Sound.Batch.QueryBad S δ loss t (powAtB S u) (queriesAtB S u)
  else False

/-- A duplex call is bad after the queries `pre` if `pre` parses it as round `i` and its answer
makes round `i` bad for the prefix transcript on `pre`'s hash queries. -/
def RoundBadB (pre : QueryLog (spec F S.streamLen)) :
    (t : Query F) → Answer S.streamLen t → Prop
  | .duplex cap input, u => match parse pre (.duplex cap input) with
    | some (steps, _) =>
      roundBadAtB S publicValues δ δ' loss steps.length
        (prefixTranscriptB S (logCache pre) (fun j ↦ (steps.map Prod.fst ++ [input]).getD j [])
          fun j ↦ (steps.map Prod.snd ++ [u.2]).getD j (Vector.replicate _ 0)) u.2
    | none => False
  | .leaf _, _ => False
  | .node .., _ => False

end Prefix

end CompStark.Ni
