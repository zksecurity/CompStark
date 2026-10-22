/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BatchBind
public import CompStark.Ni.BcsDeep
public import CompStark.BatchRandomOracle

/-! # The batched DEEP words at a query, at mixed heights

A query's reduced opening at a height is the batched DEEP word of the instances of that domain
size, at the query's point. The reduced opening sums the DEEP terms of the opened values of the
round's matrices of that height in the rounds' order (`round_terms`), each matrix's terms reading
its columns at the query (`matTerms`); with binding commitments those are the extracted columns
(`matColumn_eq`).
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop Polynomial

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### Batches without lookups -/

section NoLookups

theorem lookups_eq_nil (I : CompStark.Batch.Instance F) (h : I.air.lookups = []) :
    I.lookups = [] := by
  simp only [CompStark.Batch.Instance.lookups, Air.packedLookups, h, CompStark.Lookup.packSameBus,
    CompStark.Lookup.buses, List.filter_nil, List.foldl_nil, List.flatMap_nil, List.append_nil]

theorem lookupConstraints_eq_nil (I : CompStark.Batch.Instance F) (h : I.air.lookups = []) :
    I.air.lookupConstraints I.logN = [] := by
  have := lookups_eq_nil I h
  simp only [CompStark.Batch.Instance.lookups] at this
  simp only [Air.lookupConstraints, this, CompStark.Lookup.logUpConstraints, List.isEmpty_nil,
    ↓reduceIte]

/-- Without lookups, an instance's quotient has its AIR's chunks. -/
theorem logQuotientChunks_eq (I : CompStark.Batch.Instance F) (h : I.air.lookups = []) :
    I.logQuotientChunks = I.air.logQuotientChunks I.logN := by
  rw [CompStark.Batch.Instance.logQuotientChunks, lookupConstraints_eq_nil I h,
    Air.logQuotientChunksWith, Air.logQuotientChunks]
  have h0 : CompStark.Lookup.extDegree I.air I.logN [] = 0 := by
    unfold CompStark.Lookup.extDegree
    split <;> simp only [List.foldl_nil, ↓reduceIte]
  rw [h0, Nat.max_zero]

theorem hasLookups_instances (S : Iop.Batch.Setup EF) (h : S.NoLookups) :
    CompStark.Batch.hasLookups S.instances = false := by
  rw [CompStark.Batch.hasLookups, List.any_eq_false]
  intro I hI
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hI
  simp only [lookups_eq_nil ⟨S.air i, S.logN i⟩ (h i), List.isEmpty_nil, Bool.not_true, Bool.false_eq_true,
    not_false_eq_true]

end NoLookups

/-! ### DEEP terms -/

/-- The DEEP term of an opened value `pz` at `z` of a column whose value at the query point `x` is
`px`. -/
noncomputable def deepTerm (x : F) (t : (F × EF) × EF) : 𝕂 :=
  (Challenge.toSpec t.1.2 - lift t.1.1) * (Challenge.toSpec t.2 - lift x)⁻¹

/-- The DEEP terms of one matrix, opened at the points `pts`, its column `j` worth `f j` at the
query point `x`. -/
noncomputable def matTerms (x : F) (f : ℕ → F) (pts : List (EF × List EF)) : List 𝕂 :=
  pts.flatMap fun zy ↦ (List.range zy.2.length).map fun j ↦
    (Challenge.toSpec (zy.2.getD j 0) - lift (f j)) * (Challenge.toSpec zy.1 - lift x)⁻¹

theorem batchTerms_single (x : F) (row : Array F) (d : Domain F) (pts : List (EF × List EF))
    (hw : ∀ zy ∈ pts, zy.2.length = row.size) (f : ℕ → F)
    (hf : ∀ j < row.size, row.toList.getD j 0 = f j) :
    (batchTerms [(row, d, pts)]).map (deepTerm x) = matTerms x f pts := by
  simp only [batchTerms, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_flatMap,
    matTerms]
  refine List.flatMap_congr fun zy hzy ↦ ?_
  rw [List.map_map, map_zip_eq_range row.toList zy.2 zy.2.length
    (by rw [Array.length_toList, hw zy hzy]) rfl _ 0 0]
  refine List.map_congr_left fun j hj ↦ ?_
  have hj' : j < row.size := by rw [← hw zy hzy]; exact List.mem_range.mp hj
  simp only [Function.comp_apply, deepTerm, hf j hj']

/-- **A round's DEEP terms at a height.** The DEEP terms of the opened values of a round's
matrices of height `2 ^ m`, a row each, are each such matrix's terms read from its columns. -/
theorem round_terms (x : F) (P : Params) (m : ℕ) :
    ∀ (rows : List (Array F)) (mats : List (Domain F × List (EF × List EF))),
      rows.length = mats.length → (∀ y ∈ rows.zip mats, ∀ zy ∈ y.2.2, zy.2.length = y.1.size) →
      ∀ (f : ℕ → ℕ → F), (∀ t (ht : t < rows.length), ∀ j < rows[t].size,
        rows[t].toList.getD j 0 = f t j) →
      (batchTerms ((rows.zip mats).filter fun y ↦ y.2.1.logSize + P.logBlowup == m)).map
          (deepTerm x) =
        (List.range mats.length).flatMap fun t ↦
          if (mats.getD t (⟨0, 0⟩, [])).1.logSize + P.logBlowup = m then
            matTerms x (f t) (mats.getD t (⟨0, 0⟩, [])).2 else []
  | [], [], _, _, _, _ => rfl
  | r :: rows, d :: mats, hl, hw, f, hf => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have ih := round_terms x P m rows mats hl (fun y hy ↦ hw y (List.mem_cons_of_mem _ hy))
      (fun t j ↦ f (t + 1) j) (fun t ht j hj ↦ hf (t + 1) (by simp only [List.length_cons]; omega)
        j (by simpa only [List.getElem_cons_succ] using hj))
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      List.zip_cons_cons, List.filter_cons]
    have h0 := batchTerms_single x r d.1 d.2 (hw _ List.mem_cons_self) (f 0)
      (fun j hj ↦ hf 0 (by simp only [List.length_cons]; omega) j hj)
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    by_cases hm : d.1.logSize + P.logBlowup = m
    · rw [ite_eq_left_of_eq_true _ _ (by simp only [hm, beq_self_eq_true]),
        ite_eq_left_of_eq_true _ _ (eq_true hm), batchTerms, List.flatMap_cons, List.map_append,
        ← batchTerms, ← ih, ← h0]
      simp only [batchTerms, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    · rw [ite_eq_right_of_eq_false _ _
          (by simp only [beq_eq_false_iff_ne.mpr hm, Bool.false_eq_true]),
        ite_eq_right_of_eq_false _ _ (eq_false hm), List.nil_append, ih]

/-! ### Indexing lists of blocks -/

section Lists
variable {β γ δ : Type}

/-- A sum over the indices of a concatenation of blocks is a sum over the blocks of a sum over
their entries, at their offsets. -/
theorem range_flatMap_blocks (f : β → List γ) (G : ℕ → γ → List δ) (d : γ) (b0 : β) :
    ∀ (L : List β) (o : ℕ),
      (List.range (L.flatMap f).length).flatMap (fun t ↦ G (o + t) ((L.flatMap f).getD t d)) =
        (List.range L.length).flatMap fun i ↦ (List.range (f (L.getD i b0)).length).flatMap
          fun c ↦ G (o + ((L.take i).map fun b ↦ (f b).length).sum + c)
            ((f (L.getD i b0)).getD c d)
  | [], _ => rfl
  | b :: L, o => by
    rw [List.flatMap_cons, List.length_append, List.range_add, List.flatMap_append,
      List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    congr 1
    · refine List.flatMap_congr fun t ht ↦ ?_
      rw [List.getD_append _ _ _ _ (List.mem_range.mp ht)]
      simp only [List.getD_cons_zero, List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero]
    · rw [List.flatMap_map]
      have ih := range_flatMap_blocks f G d b0 L (o + (f b).length)
      refine Eq.trans ?_ (ih.trans ?_)
      · refine List.flatMap_congr fun t ht ↦ ?_
        rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, Nat.add_assoc]
      · refine List.flatMap_congr fun i _ ↦ ?_
        simp only [List.getD_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons]
        refine List.flatMap_congr fun c _ ↦ ?_
        rw [Nat.add_assoc o]

/-- A sum over the indices of a filtered list is a sum over the list's entries that pass, at
their ranks among them. -/
theorem range_flatMap_filter (q : β → Bool) (G : ℕ → β → List δ) (d : β) :
    ∀ (L : List β) (o : ℕ),
      (List.range (L.filter q).length).flatMap (fun t ↦ G (o + t) ((L.filter q).getD t d)) =
        (List.range L.length).flatMap fun i ↦
          if q (L.getD i d) then G (o + ((L.take i).filter q).length) (L.getD i d) else []
  | [], _ => rfl
  | b :: L, o => by
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [List.getD_cons_zero, List.take_zero, List.filter_nil, List.length_nil,
      Nat.add_zero, List.getD_cons_succ, List.take_succ_cons]
    by_cases hb : q b = true
    · rw [List.filter_cons_of_pos hb, List.length_cons, List.range_succ_eq_map,
        List.flatMap_cons, List.flatMap_map]
      simp only [List.getD_cons_zero, List.getD_cons_succ, hb, ↓reduceIte, Nat.add_zero]
      congr 1
      have ih := range_flatMap_filter q G d L (o + 1)
      refine Eq.trans ?_ (ih.trans ?_)
      · refine List.flatMap_congr fun t _ ↦ ?_
        rw [Nat.add_assoc, Nat.add_comm 1 t]
      · refine List.flatMap_congr fun i _ ↦ ?_
        rw [List.filter_cons_of_pos hb, List.length_cons, Nat.add_assoc, Nat.add_comm 1]
    · rw [List.filter_cons_of_neg hb]
      simp only [hb, Bool.false_eq_true, ↓reduceIte, List.nil_append]
      refine (range_flatMap_filter q G d L o).trans (List.flatMap_congr fun i _ ↦ ?_)
      rw [List.filter_cons_of_neg hb]

end Lists

/-! ### An instance's opened words -/

section Instance
variable {T : Iop.Setup EF} (p : Iop.Prover T) (α ζ : Challenge.Spec EF) (o : OpenedValues EF)
  (zeta : EF)
  (xi : T.Point) (x : F)

/-- The DEEP term of an opened word at the query's point `xi`, of value `x`. -/
noncomputable def wordTerm (w : (T.Point → F) × 𝕂 × 𝕂) : 𝕂 :=
  (w.2.2 - algebraMap F 𝕂 (w.1 xi)) / (w.2.1 - lift x)

theorem map_finRange_div (w : ℕ) (u : ℕ → 𝕂) (z : 𝕂) :
    (List.finRange w).map (fun j ↦ u j.val / z) = (List.range w).map fun j ↦ u j * z⁻¹ := by
  rw [map_finRange_eq_range (f := fun j ↦ u j / z)]
  exact List.map_congr_left fun j _ ↦ div_eq_mul_inv _ _

/-- An instance's opened trace words' DEEP terms are its trace matrix's, read from its words. -/
theorem main_terms (hz : Challenge.toSpec zeta = ζ) (hopen : p.openings α ζ = openingsOf T o)
    (hloc : o.traceLocal.size = T.air.width) (htn : traceNextOk T.air o = true)
    (f : ℕ → F) (hf : ∀ j (hj : j < T.air.width), f j = p.trace ⟨j, hj⟩ xi) :
    (Iop.Batch.mainOpened p α ζ).map (wordTerm xi x) =
      matTerms x f (traceOpenings T.air o zeta (zeta * Ext.ofBase (twoAdicGen T.logN))) := by
  obtain ⟨hns, -⟩ := traceNext_of_ok htn
  have hω : Challenge.toSpec (zeta * Ext.ofBase (twoAdicGen T.logN) : EF) =
      ζ * rootOfUnity T.logN := by
    rw [Challenge.toSpec_mul, Challenge.toSpec_ofBase', hz]
    rfl
  rw [Iop.Batch.mainOpened, List.map_append, List.map_map, List.map_map, traceOpenings,
    matTerms, List.flatMap_cons]
  simp only [hopen]
  congr 1
  · rw [← map_finRange_eq_range]
    refine List.ext_getElem (by simp only [List.length_map, List.length_finRange,
      Array.length_toList, hloc]) fun j h1 h2 ↦ ?_
    have hj : j < T.air.width := by simpa only [List.length_map, List.length_finRange] using h1
    simp only [List.getElem_map, List.getElem_finRange, Function.comp_apply, wordTerm,
      openingsOf, Fin.cast_mk, hz, hf j hj, toList_getD, div_eq_mul_inv]
  · split
    · rename_i hnext
      rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have hnw : T.air.mainNextWidth = T.air.width := by
        simp only [Air.mainNextWidth, hnext, ↓reduceIte]
      refine List.ext_getElem (by simp only [List.length_map, List.length_finRange,
        Array.length_toList, List.length_range, hns]) fun j h1 h2 ↦ ?_
      have hj : j < T.air.mainNextWidth := by
        simpa only [List.length_map, List.length_finRange] using h1
      simp only [List.getElem_map, List.getElem_finRange, Function.comp_apply, wordTerm,
        openingsOf, List.getElem_range, hω, toList_getD, div_eq_mul_inv]
      rw [hf j (by omega)]
      rfl
    · rename_i hnext
      have hnw : T.air.mainNextWidth = 0 := by
        simp only [Air.mainNextWidth, hnext, Bool.false_eq_true, ↓reduceIte]
      rw [List.flatMap_nil]
      exact List.eq_nil_of_length_eq_zero (by simp only [List.length_map,
        List.length_finRange, hnw])

/-- A quotient chunk's opened coordinate words' DEEP terms are its matrix's, read from its words. -/
theorem chunk_terms (hz : Challenge.toSpec zeta = ζ) (hopen : p.openings α ζ = openingsOf T o)
    (c : Fin T.chunks) (hc : (o.quotientChunks.getD c #[]).size = Challenge.d EF)
    (f : ℕ → F) (hf : ∀ e (he : e < Challenge.d EF), f e = p.quotient α c ⟨e, he⟩ xi) :
    ((List.finRange (Challenge.d EF)).map fun e ↦
        wordTerm xi x (p.quotient α c e, ζ, (p.openings α ζ).quotientAt c e)) =
      matTerms x f [(zeta, (o.quotientChunks.getD c #[]).toList)] := by
  rw [matTerms, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  refine List.ext_getElem (by simp only [List.length_map, List.length_finRange,
    Array.length_toList, List.length_range, hc]) fun e h1 h2 ↦ ?_
  have he : e < Challenge.d EF := by simpa only [List.length_map, List.length_finRange] using h1
  simp only [List.getElem_map, List.getElem_finRange, List.getElem_range, wordTerm, hopen,
    openingsOf, Fin.cast_mk, hz, hf e he, toList_getD, div_eq_mul_inv]

/-- An instance's opened preprocessed words' DEEP terms are its preprocessed matrix's, read from
its preprocessed words. -/
theorem prep_terms (hz : Challenge.toSpec zeta = ζ) (hopen : p.openings α ζ = openingsOf T o)
    (hloc : (o.preprocessedLocal.getD #[]).size = T.air.preprocessedWidth)
    (hnext : (o.preprocessedNext.getD #[]).size = T.air.preprocessedNextWidth)
    (f : ℕ → F) (hf : ∀ j < T.air.preprocessedWidth, f j = T.preprocessedWord j xi) :
    (Iop.Batch.preprocessedOpened p α ζ).map (wordTerm xi x) =
      matTerms x f ((zeta, (o.preprocessedLocal.getD #[]).toList) ::
        if T.air.opensPreprocessedNext then
          [(zeta * Ext.ofBase (twoAdicGen T.logN), (o.preprocessedNext.getD #[]).toList)]
        else []) := by
  have hω : Challenge.toSpec (zeta * Ext.ofBase (twoAdicGen T.logN) : EF) =
      ζ * rootOfUnity T.logN := by
    rw [Challenge.toSpec_mul, Challenge.toSpec_ofBase', hz]
    rfl
  rw [Iop.Batch.preprocessedOpened, List.map_append, List.map_map, List.map_map, matTerms,
    List.flatMap_cons]
  simp only [hopen]
  congr 1
  · refine List.ext_getElem (by simp only [List.length_map, List.length_finRange,
      Array.length_toList, List.length_range, hloc]) fun j h1 h2 ↦ ?_
    have hj : j < T.air.preprocessedWidth := by
      simpa only [List.length_map, List.length_finRange] using h1
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_range, Function.comp_apply,
      wordTerm, openingsOf, Fin.cast_mk, hz, hf j hj, toList_getD, div_eq_mul_inv]
  · split
    · rename_i hn
      rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have hnw : T.air.preprocessedNextWidth = T.air.preprocessedWidth := by
        simp only [Air.preprocessedNextWidth, hn, ↓reduceIte]
      refine List.ext_getElem (by simp only [List.length_map, List.length_finRange,
        Array.length_toList, List.length_range, hnext]) fun j h1 h2 ↦ ?_
      have hj : j < T.air.preprocessedNextWidth := by
        simpa only [List.length_map, List.length_finRange] using h1
      simp only [List.getElem_map, List.getElem_finRange, List.getElem_range, Function.comp_apply,
        wordTerm, openingsOf, Fin.cast_mk, hω, toList_getD, div_eq_mul_inv]
      rw [hf j (by omega)]
    · rename_i hn
      have hnw : T.air.preprocessedNextWidth = 0 := by
        simp only [Air.preprocessedNextWidth, hn, Bool.false_eq_true, ↓reduceIte]
      rw [List.flatMap_nil]
      exact List.eq_nil_of_length_eq_zero (by simp only [List.length_map,
        List.length_finRange, hnw])

end Instance

/-! ### The batched DEEP words -/

/-- Opened values of no instance. -/
def noOpenings : OpenedValues EF := ⟨#[], none, none, none, #[]⟩

section Group
variable {S : Iop.Batch.Setup EF}

/-- The DEEP term of an opened word of a domain of `2 ^ m` points at the point of index `z`. -/
noncomputable def groupTerm (m : ℕ) (z : Fin (2 ^ m)) (w : (Fin (2 ^ m) → F) × 𝕂 × 𝕂) : 𝕂 :=
  (w.2.2 - algebraMap F 𝕂 (w.1 z)) / (w.2.1 - lift (basePoint m z))

/-- A batched DEEP word is Horner's rule over its opened words' DEEP terms. -/
theorem groupDeepWord_eq_horner (p : Iop.Batch.Prover S) (α ζ a : 𝕂) (m : ℕ) (z : Fin (2 ^ m)) :
    Iop.Batch.groupDeepWord p α ζ a m z =
      ((Iop.Batch.groupOpened p α ζ m).map (groupTerm m z)).foldr
        (fun v acc ↦ v + a * acc) 0 := by
  rw [Iop.Batch.groupDeepWord]
  have h := sum_zipIdx_pow a ((Iop.Batch.groupOpened p α ζ m).map (groupTerm m z)) 0
  rw [pow_zero, one_mul, List.zipIdx_map, List.map_map] at h
  rw [← h]
  congr 1
  refine List.map_congr_left fun w _ ↦ ?_
  obtain ⟨⟨f, zz, y⟩, k⟩ := w
  simp only [Function.comp_apply, Prod.map, id, groupTerm, mul_div_assoc]

/-- An instance's opened words read on its domain's size: their DEEP terms at the point. -/
theorem onSize_map (i : Fin S.k) (m : ℕ)
    (words : List (((S.instanceSetup i).Point → F) × 𝕂 × 𝕂)) (z : Fin (2 ^ m)) :
    (Iop.Batch.onSize i m words).map (groupTerm m z) =
      if h : S.logN i + S.params.logBlowup = m then
        words.map (wordTerm (Fin.cast (by rw [h]) z) (basePoint m z)) else [] := by
  unfold Iop.Batch.onSize
  split
  · rw [List.map_map]
    rfl
  · rfl

/-- The query's point at a height is the domain's point at the query's index there. -/
theorem pointAt_eq (logMax I m : ℕ) :
    pointAt (F := F) logMax I m =
      basePoint m (finMod m (reverseBits (I >>> (logMax - m)) m)) := by
  rw [pointAt, basePoint, powF_eq, finMod_val (reverseBits_lt _ _)]

/-- The statement's instances, zipped with a list of opened values of every instance. -/
theorem getD_map_zip_instances {γ : Type} (os : List (OpenedValues EF)) (hos : os.length = S.k)
    (φ : CompStark.Batch.Instance F × OpenedValues EF → γ) (d : γ) (i : Fin S.k) :
    ((S.instances.zip os).map φ).getD i d = φ (⟨S.air i, S.logN i⟩, os.getD i noOpenings) := by
  have hl : i.val < (S.instances.zip os).length := by
    rw [List.length_zip, Iop.Batch.Setup.instances, List.length_ofFn, hos, Nat.min_self]
    exact i.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl,
    Option.map_some, Option.getD_some, List.getElem_zip]
  congr 2
  · simp only [Iop.Batch.Setup.instances, List.getElem_ofFn]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem length_instances : S.instances.length = S.k := by
  rw [Iop.Batch.Setup.instances, List.length_ofFn]

end Group

section Parts
variable (S : Iop.Batch.Setup EF) (p : Iop.Batch.Prover S) (α ζ : Challenge.Spec EF)
  (proof : CompStark.Batch.BatchProof F EF) (zeta : EF) (logMax I m : ℕ)

/-- Instance `i`'s point at the query of index `I` into the tallest domain: the index shifted to
its domain's size, bit-reversed. -/
def instPoint (i : Fin S.k) : (S.instanceSetup i).Point :=
  finMod (S.logN i + S.params.logBlowup)
    (reverseBits (I >>> (logMax - (S.logN i + S.params.logBlowup)))
      (S.logN i + S.params.logBlowup))

/-- **The main traces' part.** -/
theorem main_part (hz : Challenge.toSpec zeta = ζ)
    (hopen : ∀ i, p.openings α ζ i =
      openingsOf (S.instanceSetup i) (proof.opened.toList.getD i noOpenings))
    (hsize : proof.opened.size = S.k)
    (hshape : ∀ i : Fin S.k, (proof.opened.toList.getD i noOpenings).traceLocal.size =
      (S.air i).width ∧ traceNextOk (S.air i) (proof.opened.toList.getD i noOpenings) = true)
    (rows : List (Array F))
    (hrl : rows.length = S.k)
    (hw : ∀ y ∈ rows.zip ((S.instances.zip proof.opened.toList).map fun x ↦
        ((⟨1, x.1.logN⟩ : Domain F), traceOpenings x.1.air x.2 zeta
          (zeta * Ext.ofBase (twoAdicGen x.1.logN)))), ∀ zy ∈ y.2.2, zy.2.length = y.1.size)
    (hrow : ∀ (i : Fin S.k) (j : ℕ) (hj : j < (S.air i).width),
      (rows.getD i #[]).toList.getD j 0 = p.trace i ⟨j, hj⟩ (instPoint S logMax I i)) :
    (batchTerms ((rows.zip ((S.instances.zip proof.opened.toList).map fun x ↦
        ((⟨1, x.1.logN⟩ : Domain F), traceOpenings x.1.air x.2 zeta
          (zeta * Ext.ofBase (twoAdicGen x.1.logN))))).filter
        fun y ↦ y.2.1.logSize + S.params.logBlowup == m)).map (deepTerm (pointAt logMax I m)) =
      ((List.finRange S.k).flatMap fun i ↦
        Iop.Batch.onSize i m (Iop.Batch.mainOpened (p.instanceProver i) α ζ)).map
          (groupTerm m (finMod m (reverseBits (I >>> (logMax - m)) m))) := by
  have hos : proof.opened.toList.length = S.k := by rw [Array.length_toList, hsize]
  have hml : ((S.instances.zip proof.opened.toList).map fun x ↦
      ((⟨1, x.1.logN⟩ : Domain F), traceOpenings x.1.air x.2 zeta
        (zeta * Ext.ofBase (twoAdicGen x.1.logN)))).length = S.k := by
    rw [List.length_map, List.length_zip, length_instances, hos, Nat.min_self]
  rw [round_terms _ S.params m rows _ (by rw [hrl, hml]) hw
    (fun t j ↦ (rows.getD t #[]).toList.getD j 0) (fun t ht j _ ↦ by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]),
    hml, ← flatMap_finRange_eq_range, List.map_flatMap]
  refine List.flatMap_congr fun i _ ↦ ?_
  rw [getD_map_zip_instances _ hos, onSize_map]
  dsimp only
  split
  · rename_i h
    subst h
    rw [pointAt_eq]
    obtain ⟨hloc, htn⟩ := hshape i
    refine (main_terms (p.instanceProver i) α ζ _ zeta _ _ hz (hopen i) hloc htn _
      fun j hj ↦ ?_).symm
    rw [hrow i j hj]
    rfl
  · rfl

/-- The offset of instance `i`'s quotient chunks among all instances': the chunks of the earlier
instances. -/
def quotOffset (i : Fin S.k) : ℕ :=
  ((List.ofFn fun i' : Fin S.k ↦ (S.instanceSetup i').chunks).take i).sum

theorem flatMap_ite_const {α δ : Type} (L : List α) (c : Prop) [Decidable c] (G : α → List δ) :
    (L.flatMap fun a ↦ if c then G a else []) = if c then L.flatMap G else [] := by
  split
  · rfl
  · induction L with
    | nil => rfl
    | cons a L ih => rw [List.flatMap_cons, ih, List.nil_append]

/-- **The quotient chunks' part.** -/
theorem quot_part (hz : Challenge.toSpec zeta = ζ)
    (hopen : ∀ i, p.openings α ζ i =
      openingsOf (S.instanceSetup i) (proof.opened.toList.getD i noOpenings))
    (hsize : proof.opened.size = S.k)
    (hshape : ∀ i : Fin S.k, (proof.opened.toList.getD i noOpenings).quotientChunks.size =
      (S.instanceSetup i).chunks ∧ ∀ ch ∈ (proof.opened.toList.getD i noOpenings).quotientChunks,
        ch.size = Challenge.d EF)
    (rows : List (Array F))
    (hrl : rows.length = ((S.instances.zip proof.opened.toList).flatMap fun x ↦
        x.2.quotientChunks.toList.map fun ch ↦
          ((⟨1, x.1.logN⟩ : Domain F), [(zeta, ch.toList)])).length)
    (hw : ∀ y ∈ rows.zip ((S.instances.zip proof.opened.toList).flatMap fun x ↦
        x.2.quotientChunks.toList.map fun ch ↦
          ((⟨1, x.1.logN⟩ : Domain F), [(zeta, ch.toList)])), ∀ zy ∈ y.2.2,
        zy.2.length = y.1.size)
    (hrow : ∀ (i : Fin S.k) (c : Fin (S.instanceSetup i).chunks) (e : ℕ)
      (he : e < Challenge.d EF),
      (rows.getD (quotOffset S i + c) #[]).toList.getD e 0 =
        p.quotient α i c ⟨e, he⟩ (instPoint S logMax I i)) :
    (batchTerms ((rows.zip ((S.instances.zip proof.opened.toList).flatMap fun x ↦
        x.2.quotientChunks.toList.map fun ch ↦
          ((⟨1, x.1.logN⟩ : Domain F), [(zeta, ch.toList)]))).filter
        fun y ↦ y.2.1.logSize + S.params.logBlowup == m)).map (deepTerm (pointAt logMax I m)) =
      ((List.finRange S.k).flatMap fun i ↦
        Iop.Batch.onSize i m (Iop.Batch.quotientOpened (p.instanceProver i) α ζ)).map
          (groupTerm m (finMod m (reverseBits (I >>> (logMax - m)) m))) := by
  have hos : proof.opened.toList.length = S.k := by rw [Array.length_toList, hsize]
  set L := S.instances.zip proof.opened.toList with hL
  have hLl : L.length = S.k := by rw [hL, List.length_zip, length_instances, hos, Nat.min_self]
  set blk : CompStark.Batch.Instance F × OpenedValues EF → List (Domain F × List (EF × List EF)) :=
    fun x ↦ x.2.quotientChunks.toList.map fun ch ↦
      ((⟨1, x.1.logN⟩ : Domain F), [(zeta, ch.toList)]) with hblk
  rw [round_terms _ S.params m rows _ hrl hw
    (fun t j ↦ (rows.getD t #[]).toList.getD j 0) (fun t ht j _ ↦ by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some])]
  have hb := range_flatMap_blocks blk (fun t y ↦ if y.1.logSize + S.params.logBlowup = m then
    matTerms (pointAt logMax I m) (fun j ↦ (rows.getD t #[]).toList.getD j 0) y.2 else [])
    (⟨0, 0⟩, []) (⟨S.air ⟨0, S.nonempty⟩, 0⟩, noOpenings) L 0
  simp only [Nat.zero_add] at hb
  rw [hb, hLl, ← flatMap_finRange_eq_range, List.map_flatMap]
  refine List.flatMap_congr fun i _ ↦ ?_
  have hLi : L.getD i (⟨S.air ⟨0, S.nonempty⟩, 0⟩, noOpenings) =
      (⟨S.air i, S.logN i⟩, proof.opened.toList.getD i noOpenings) := by
    have := getD_map_zip_instances (S := S) _ hos id (⟨S.air ⟨0, S.nonempty⟩, 0⟩, noOpenings) i
    rwa [List.map_id] at this
  obtain ⟨hcs, hch⟩ := hshape i
  have hoff : ((L.take i).map fun b ↦ (blk b).length).sum = quotOffset S i := by
    unfold quotOffset
    congr 1
    refine List.ext_getElem (by
      simp only [List.length_map, List.length_take, hLl, List.length_ofFn]) fun i' h1 h2 ↦ ?_
    have hi' : i' < i.val := by
      simp only [List.length_map, List.length_take, hLl] at h1; omega
    have hk : i' < S.k := by omega
    have hLi' := getD_map_zip_instances (S := S) _ hos id
      (⟨S.air ⟨0, S.nonempty⟩, 0⟩, noOpenings) ⟨i', hk⟩
    rw [List.map_id] at hLi'
    simp only [List.getElem_map, List.getElem_take, List.getElem_ofFn, hblk, List.length_map,
      Array.length_toList]
    rw [← List.getD_eq_getElem _ (⟨S.air ⟨0, S.nonempty⟩, 0⟩, noOpenings), hLi']
    exact (hshape ⟨i', hk⟩).1
  rw [hLi, hoff, onSize_map]
  have hlen : (blk (⟨S.air i, S.logN i⟩, proof.opened.toList.getD i noOpenings)).length =
      (S.instanceSetup i).chunks := by
    simp only [hblk, List.length_map, Array.length_toList, hcs]
  have hget : ∀ c < (S.instanceSetup i).chunks,
      (blk (⟨S.air i, S.logN i⟩, proof.opened.toList.getD i noOpenings)).getD c (⟨0, 0⟩, []) =
        ((⟨1, S.logN i⟩ : Domain F),
          [(zeta, ((proof.opened.toList.getD i noOpenings).quotientChunks.getD c #[]).toList)]) :=
        by
    intro c hc
    generalize proof.opened.toList.getD i noOpenings = o at hcs ⊢
    simp only [hblk, List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
      Array.getElem?_eq_getElem (hcs ▸ hc), Option.map_some, Option.getD_some,
      Array.getD_eq_getD_getElem?]
  rw [hlen]
  rw [List.flatMap_congr (fun c hc ↦ by rw [hget c (List.mem_range.mp hc)])]
  dsimp only
  by_cases h : S.logN i + S.params.logBlowup = m
  · simp only [h, ↓reduceIte, ↓reduceDIte]
    subst h
    rw [Iop.Batch.quotientOpened, List.map_flatMap, ← flatMap_finRange_eq_range, pointAt_eq]
    refine List.flatMap_congr fun c _ ↦ ?_
    rw [List.map_map]
    refine (chunk_terms (p.instanceProver i) α ζ _ zeta _ _ hz (hopen i) c ?_ _
      fun e he ↦ ?_).symm
    · exact hch _ (by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hcs]; exact c.isLt),
          Option.getD_some]
        exact Array.getElem_mem _)
    · rw [hrow i c e he]
      rfl
  · simp only [h, ↓reduceIte, ↓reduceDIte]
    induction List.range (S.instanceSetup i).chunks with
    | nil => rfl
    | cons a L ih => rw [List.flatMap_cons, ih, List.nil_append]

theorem length_filter_zip {α β : Type} (r : α → Bool) :
    ∀ (A : List α) (B : List β), A.length ≤ B.length →
      ((A.zip B).filter fun x ↦ r x.1).length = (A.filter r).length
  | [], _, _ => rfl
  | _ :: _, [], h => by simp only [List.length_cons, List.length_nil] at h; omega
  | a :: A, b :: B, h => by
    simp only [List.length_cons, Nat.add_le_add_iff_right] at h
    rw [List.zip_cons_cons, List.filter_cons, List.filter_cons]
    split <;> simp only [List.length_cons, length_filter_zip r A B h]

/-- Instance `i`'s rank among the instances with preprocessed columns. -/
def prepIndex (i : Fin S.k) : ℕ :=
  ((S.instances.take i).filter (0 < ·.air.preprocessedWidth)).length

/-- **The preprocessed traces' part.** -/
theorem prep_part (hz : Challenge.toSpec zeta = ζ)
    (hopen : ∀ i, p.openings α ζ i =
      openingsOf (S.instanceSetup i) (proof.opened.toList.getD i noOpenings))
    (hsize : proof.opened.size = S.k)
    (hshape : ∀ i : Fin S.k,
      ((proof.opened.toList.getD i noOpenings).preprocessedLocal.getD #[]).size =
        (S.air i).preprocessedWidth ∧
      ((proof.opened.toList.getD i noOpenings).preprocessedNext.getD #[]).size =
        (S.air i).preprocessedNextWidth)
    (rows : List (Array F))
    (hrl : rows.length = (((S.instances.zip proof.opened.toList).filter
      (0 < ·.1.air.preprocessedWidth)).map fun x ↦ ((⟨1, x.1.logN⟩ : Domain F),
        (zeta, (x.2.preprocessedLocal.getD #[]).toList) ::
          if x.1.air.opensPreprocessedNext then
            [(zeta * Ext.ofBase (twoAdicGen x.1.logN), (x.2.preprocessedNext.getD #[]).toList)]
          else [])).length)
    (hw : ∀ y ∈ rows.zip (((S.instances.zip proof.opened.toList).filter
      (0 < ·.1.air.preprocessedWidth)).map fun x ↦ ((⟨1, x.1.logN⟩ : Domain F),
        (zeta, (x.2.preprocessedLocal.getD #[]).toList) ::
          if x.1.air.opensPreprocessedNext then
            [(zeta * Ext.ofBase (twoAdicGen x.1.logN), (x.2.preprocessedNext.getD #[]).toList)]
          else [])), ∀ zy ∈ y.2.2, zy.2.length = y.1.size)
    (hrow : ∀ (i : Fin S.k), 0 < (S.air i).preprocessedWidth → ∀ (j : ℕ),
      j < (S.air i).preprocessedWidth →
      (rows.getD (prepIndex S i) #[]).toList.getD j 0 =
        (S.instanceSetup i).preprocessedWord j (instPoint S logMax I i)) :
    (batchTerms ((rows.zip (((S.instances.zip proof.opened.toList).filter
      (0 < ·.1.air.preprocessedWidth)).map fun x ↦ ((⟨1, x.1.logN⟩ : Domain F),
        (zeta, (x.2.preprocessedLocal.getD #[]).toList) ::
          if x.1.air.opensPreprocessedNext then
            [(zeta * Ext.ofBase (twoAdicGen x.1.logN), (x.2.preprocessedNext.getD #[]).toList)]
          else []))).filter
        fun y ↦ y.2.1.logSize + S.params.logBlowup == m)).map (deepTerm (pointAt logMax I m)) =
      ((List.finRange S.k).flatMap fun i ↦
        Iop.Batch.onSize i m (Iop.Batch.preprocessedOpened (p.instanceProver i) α ζ)).map
          (groupTerm m (finMod m (reverseBits (I >>> (logMax - m)) m))) := by
  have hos : proof.opened.toList.length = S.k := by rw [Array.length_toList, hsize]
  set L := S.instances.zip proof.opened.toList with hL
  have hLl : L.length = S.k := by rw [hL, List.length_zip, length_instances, hos, Nat.min_self]
  set q : CompStark.Batch.Instance F × OpenedValues EF → Bool :=
    fun x ↦ decide (0 < x.1.air.preprocessedWidth) with hq
  set ψ : CompStark.Batch.Instance F × OpenedValues EF → Domain F × List (EF × List EF) :=
    fun x ↦ ((⟨1, x.1.logN⟩ : Domain F),
      (zeta, (x.2.preprocessedLocal.getD #[]).toList) ::
        if x.1.air.opensPreprocessedNext then
          [(zeta * Ext.ofBase (twoAdicGen x.1.logN), (x.2.preprocessedNext.getD #[]).toList)]
        else []) with hψ
  set b0 : CompStark.Batch.Instance F × OpenedValues EF := (⟨S.air ⟨0, S.nonempty⟩, 0⟩, noOpenings)
  set G : ℕ → CompStark.Batch.Instance F × OpenedValues EF → List 𝕂 := fun t y ↦
    if (ψ y).1.logSize + S.params.logBlowup = m then
      matTerms (pointAt logMax I m) (fun j ↦ (rows.getD t #[]).toList.getD j 0) (ψ y).2 else []
    with hG
  rw [round_terms _ S.params m rows _ hrl hw
    (fun t j ↦ (rows.getD t #[]).toList.getD j 0) (fun t ht j _ ↦ by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]),
    List.length_map]
  rw [List.flatMap_congr (g := fun t ↦ G t ((L.filter q).getD t b0)) fun t ht ↦ by
    have ht' : t < (L.filter q).length := List.mem_range.mp ht
    simp only [hG, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem ht', Option.map_some, Option.getD_some]]
  have hf := range_flatMap_filter q G b0 L 0
  simp only [Nat.zero_add] at hf
  rw [hf, hLl, ← flatMap_finRange_eq_range, List.map_flatMap]
  refine List.flatMap_congr fun i _ ↦ ?_
  have hLi : L.getD i b0 = (⟨S.air i, S.logN i⟩, proof.opened.toList.getD i noOpenings) := by
    have := getD_map_zip_instances (S := S) _ hos id b0 i
    rwa [List.map_id] at this
  have hrank : ((L.take i).filter q).length = prepIndex S i := by
    rw [show L.take i = (S.instances.take i).zip (proof.opened.toList.take i) from
      List.take_zipWith, prepIndex]
    exact length_filter_zip (fun I ↦ decide (0 < I.air.preprocessedWidth)) (S.instances.take i)
      (proof.opened.toList.take i) (by
        rw [List.length_take, List.length_take, length_instances, hos])
  rw [hLi, hrank, onSize_map]
  obtain ⟨hloc, hnext⟩ := hshape i
  by_cases hp : 0 < (S.air i).preprocessedWidth
  · simp only [hq, hp, decide_true, ↓reduceIte, hG, hψ]
    by_cases hm : S.logN i + S.params.logBlowup = m
    · simp only [hm, ↓reduceIte, ↓reduceDIte]
      subst hm
      rw [pointAt_eq]
      refine (prep_terms (p.instanceProver i) α ζ _ zeta _ _ hz (hopen i) hloc hnext _
        fun j hj ↦ ?_).symm
      rw [hrow i hp j hj]
      rfl
    · simp only [hm, ↓reduceIte, ↓reduceDIte]
  · have hw0 : (S.air i).preprocessedWidth = 0 := by omega
    have hn0 : (S.air i).preprocessedNextWidth = 0 := by
      have := (S.air i).preprocessedNextWidth_le; omega
    have hpo : Iop.Batch.preprocessedOpened (p.instanceProver i) α ζ = [] := by
      simp only [Iop.Batch.preprocessedOpened, List.append_eq_nil_iff, List.map_eq_nil_iff,
        List.finRange_eq_nil_iff]
      exact ⟨hw0, hn0⟩
    simp only [hq, hp, decide_false, Bool.false_eq_true, ↓reduceIte, hpo, List.map_nil,
      dite_eq_ite, ite_self]

/-- The commitment scheme's rounds of a batch proof at `ζ`: the main traces, the quotient chunks,
and the preprocessed traces if the common data commits to some. -/
theorem batchRounds_cases (common : CompStark.Batch.Common F)
    (hperm : proof.permutationCommit = none) :
    CompStark.Batch.batchRounds S.instances common proof zeta =
      [(proof.mainCommit, (S.instances.zip proof.opened.toList).map fun x ↦
          ((⟨1, x.1.logN⟩ : Domain F), traceOpenings x.1.air x.2 zeta
            (zeta * Ext.ofBase (twoAdicGen x.1.logN)))),
        (proof.quotientCommit, (S.instances.zip proof.opened.toList).flatMap fun x ↦
          x.2.quotientChunks.toList.map fun ch ↦
            ((⟨1, x.1.logN⟩ : Domain F), [(zeta, ch.toList)]))] ++
        match common.preprocessed with
        | some root => [(root, ((S.instances.zip proof.opened.toList).filter
            (0 < ·.1.air.preprocessedWidth)).map fun x ↦ ((⟨1, x.1.logN⟩ : Domain F),
              (zeta, (x.2.preprocessedLocal.getD #[]).toList) ::
                if x.1.air.opensPreprocessedNext then
                  [(zeta * Ext.ofBase (twoAdicGen x.1.logN),
                    (x.2.preprocessedNext.getD #[]).toList)]
                else []))]
        | none => [] := by
  rw [CompStark.Batch.batchRounds, hperm]
  exact List.append_nil _

/-- An instance without preprocessed columns opens no preprocessed words. -/
theorem preprocessedOpened_nil {T : Iop.Setup EF} (q : Iop.Prover T) (α ζ : 𝕂)
    (hp : T.air.preprocessedWidth = 0) : Iop.Batch.preprocessedOpened q α ζ = [] := by
  have hn0 : T.air.preprocessedNextWidth = 0 := by
    have := T.air.preprocessedNextWidth_le; omega
  simp only [Iop.Batch.preprocessedOpened, List.append_eq_nil_iff, List.map_eq_nil_iff,
    List.finRange_eq_nil_iff]
  exact ⟨hp, hn0⟩

/-- Opened values in the shape of an instance without lookups have its AIR's widths. -/
theorem openedShapeOk_spec {I : CompStark.Batch.Instance F} {o : OpenedValues EF}
    (hl : I.air.lookups = []) (h : CompStark.Batch.openedShapeOk I o = true) :
    o.traceLocal.size = I.air.width ∧ traceNextOk I.air o = true ∧
      o.quotientChunks.size = 2 ^ I.air.logQuotientChunks I.logN ∧
      (∀ ch ∈ o.quotientChunks, ch.size = Challenge.d EF) ∧
      (o.preprocessedLocal.getD #[]).size = I.air.preprocessedWidth ∧
      (o.preprocessedNext.getD #[]).size = I.air.preprocessedNextWidth := by
  rw [← logQuotientChunks_eq I hl]
  rcases o with ⟨tl, tn, pl, pn, qc⟩
  simp only [CompStark.Batch.openedShapeOk, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true']
    at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, ?_⟩
  have hnl := I.air.preprocessedNextWidth_le
  match pl, pn, h5 with
  | none, none, h5 =>
    simp only [beq_iff_eq] at h5
    simp only [Option.getD_none, Array.size_empty]
    exact ⟨h5.symm, by omega⟩
  | some l, none, h5 =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h5
    simp only [Option.getD_some, Option.getD_none, Array.size_empty, Air.preprocessedNextWidth,
      h5.2, Bool.false_eq_true, ↓reduceIte]
    exact ⟨h5.1.2, trivial⟩
  | some l, some r, h5 =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h5
    simp only [Option.getD_some, Air.preprocessedNextWidth, h5.2.1, ↓reduceIte]
    exact ⟨h5.1.2, h5.2.2⟩
  | none, some _, h5 => simp only [Bool.false_eq_true] at h5

/-- **The batched DEEP words at a query.** If a query's rows of the main traces, the quotient
chunks and the preprocessed traces at index `I` hold the prover's words at the instances' points,
its reduced opening at each height is the batched DEEP word of the instances of that domain size
at the query's point, at the batching challenge. -/
theorem reducedAt_eq_groupDeepWord (hnl : S.NoLookups) (hz : Challenge.toSpec zeta = ζ)
    (hopen : ∀ i, p.openings α ζ i =
      openingsOf (S.instanceSetup i) (proof.opened.toList.getD i noOpenings))
    (hsize : proof.opened.size = S.k)
    (hshape : ∀ i : Fin S.k, CompStark.Batch.openedShapeOk ⟨S.air i, S.logN i⟩
      (proof.opened.toList.getD i noOpenings) = true)
    (common : CompStark.Batch.Common F)
    (hprep : common.preprocessed.isSome = S.instances.any (0 < ·.air.preprocessedWidth))
    (hperm : proof.permutationCommit = none) (rM rQ rP : List (Array F))
    (hw : ∀ x ∈ ([rM, rQ] ++ (match common.preprocessed with | some _ => [rP] | none => [])).zip
      (CompStark.Batch.batchRounds S.instances common proof zeta),
      x.1.length = x.2.2.length ∧ ∀ y ∈ x.1.zip x.2.2, ∀ zy ∈ y.2.2, zy.2.length = y.1.size)
    (hM : ∀ (i : Fin S.k) (j : ℕ) (hj : j < (S.air i).width),
      (rM.getD i #[]).toList.getD j 0 = p.trace i ⟨j, hj⟩ (instPoint S logMax I i))
    (hQ : ∀ (i : Fin S.k) (c : Fin (S.instanceSetup i).chunks) (e : ℕ)
      (he : e < Challenge.d EF), (rQ.getD (quotOffset S i + c) #[]).toList.getD e 0 =
        p.quotient α i c ⟨e, he⟩ (instPoint S logMax I i))
    (hP : ∀ (i : Fin S.k), 0 < (S.air i).preprocessedWidth → ∀ (j : ℕ),
      j < (S.air i).preprocessedWidth →
      (rP.getD (prepIndex S i) #[]).toList.getD j 0 =
        (S.instanceSetup i).preprocessedWord j (instPoint S logMax I i))
    (a : EF) :
    Challenge.toSpec (reducedAt S.params logMax I a
      (queryMats (([rM, rQ] ++ (match common.preprocessed with | some _ => [rP] | none => [])).zip
        (CompStark.Batch.batchRounds S.instances common proof zeta))) m).2 =
      Iop.Batch.groupDeepWord p α ζ (Challenge.toSpec a) m
        (finMod m (reverseBits (I >>> (logMax - m)) m)) := by
  rw [reducedAt, toSpec_accTerms, Challenge.toSpec_zero, Challenge.toSpec_one, zero_add,
    one_mul, groupDeepWord_eq_horner]
  congr 1
  change (batchTerms _).map (deepTerm (pointAt logMax I m)) = _
  have hsh := fun i ↦ openedShapeOk_spec (hnl i) (hshape i)
  rw [Iop.Batch.groupOpened, List.map_append, List.map_append]
  rw [batchRounds_cases (hperm := hperm)] at hw ⊢
  have hbt : ∀ (u v : List (Array F × Domain F × List (EF × List EF))),
      batchTerms (u ++ v) = batchTerms u ++ batchTerms v := fun u v ↦ List.flatMap_append
  have hq : ∀ (x y : List (Array F) × Round F EF) (xs : List (List (Array F) × Round F EF)),
      queryMats (x :: y :: xs) = x.1.zip x.2.2 ++ y.1.zip y.2.2 ++ queryMats xs := by
    intro x y xs
    simp only [queryMats, List.flatMap_cons, List.append_assoc]
  have hmem : ∀ (x : List (Array F) × Round F EF) (xs : List (List (Array F) × Round F EF)),
      x ∈ x :: xs := fun _ _ ↦ List.mem_cons_self
  cases hc : common.preprocessed with
  | none =>
    simp only [hc, List.append_nil, List.zip_cons_cons, List.zip_nil_left] at hw ⊢
    obtain ⟨hlM, hwM⟩ := hw _ (hmem _ _)
    obtain ⟨hlQ, hwQ⟩ := hw _ (List.mem_cons_of_mem _ (hmem _ _))
    rw [hq, show queryMats ([] : List (List (Array F) × Round F EF)) = [] from rfl,
      List.append_nil, List.filter_append, hbt, List.map_append]
    have hlenM : rM.length = S.k := by
      rw [hlM, List.length_map, List.length_zip, length_instances, Array.length_toList, hsize,
        Nat.min_self]
    rw [main_part S p α ζ proof zeta logMax I m hz hopen hsize
      (fun i ↦ ⟨(hsh i).1, (hsh i).2.1⟩) rM hlenM hwM hM,
      quot_part S p α ζ proof zeta logMax I m hz hopen hsize
      (fun i ↦ ⟨(hsh i).2.2.1, (hsh i).2.2.2.1⟩) rQ hlQ hwQ hQ]
    have hC : ((List.finRange S.k).flatMap fun i ↦
        Iop.Batch.onSize i m (Iop.Batch.preprocessedOpened (p.instanceProver i) α ζ)).map
          (groupTerm m (finMod m (reverseBits (I >>> (logMax - m)) m))) = [] := by
      rw [List.map_flatMap]
      refine List.flatMap_eq_nil_iff.mpr fun i _ ↦ ?_
      have hp : (S.air i).preprocessedWidth = 0 := by
        rw [hc, Option.isSome_none] at hprep
        have := (List.any_eq_false.mp hprep.symm) ⟨S.air i, S.logN i⟩ (by
          rw [Iop.Batch.Setup.instances, List.mem_ofFn]; exact ⟨i, rfl⟩)
        simp only [decide_eq_true_eq] at this
        omega
      rw [preprocessedOpened_nil _ _ _ hp, Iop.Batch.onSize]
      split <;> rfl
    rw [hC, List.append_nil]
  | some root =>
    simp only [hc, List.cons_append, List.nil_append, List.zip_cons_cons,
      List.zip_nil_left] at hw ⊢
    obtain ⟨hlM, hwM⟩ := hw _ (hmem _ _)
    obtain ⟨hlQ, hwQ⟩ := hw _ (List.mem_cons_of_mem _ (hmem _ _))
    obtain ⟨hlP, hwP⟩ := hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hmem _ _)))
    have hlenM : rM.length = S.k := by
      rw [hlM, List.length_map, List.length_zip, length_instances, Array.length_toList, hsize,
        Nat.min_self]
    rw [hq, show queryMats [(rP, (root, ((S.instances.zip proof.opened.toList).filter
        (0 < ·.1.air.preprocessedWidth)).map fun x ↦ ((⟨1, x.1.logN⟩ : Domain F),
          (zeta, (x.2.preprocessedLocal.getD #[]).toList) ::
            if x.1.air.opensPreprocessedNext then
              [(zeta * Ext.ofBase (twoAdicGen x.1.logN), (x.2.preprocessedNext.getD #[]).toList)]
            else [])))] = rP.zip (((S.instances.zip proof.opened.toList).filter
        (0 < ·.1.air.preprocessedWidth)).map fun x ↦ ((⟨1, x.1.logN⟩ : Domain F),
          (zeta, (x.2.preprocessedLocal.getD #[]).toList) ::
            if x.1.air.opensPreprocessedNext then
              [(zeta * Ext.ofBase (twoAdicGen x.1.logN), (x.2.preprocessedNext.getD #[]).toList)]
            else [])) by simp only [queryMats, List.flatMap_cons, List.flatMap_nil,
              List.append_nil],
      List.filter_append, List.filter_append, hbt, hbt, List.map_append, List.map_append,
      main_part S p α ζ proof zeta logMax I m hz hopen hsize
        (fun i ↦ ⟨(hsh i).1, (hsh i).2.1⟩) rM hlenM hwM hM,
      quot_part S p α ζ proof zeta logMax I m hz hopen hsize
        (fun i ↦ ⟨(hsh i).2.2.1, (hsh i).2.2.2.1⟩) rQ hlQ hwQ hQ,
      prep_part S p α ζ proof zeta logMax I m hz hopen hsize
        (fun i ↦ ⟨(hsh i).2.2.2.2.1, (hsh i).2.2.2.2.2⟩) rP hlP hwP hP]

end Parts

end CompStark.Ni
