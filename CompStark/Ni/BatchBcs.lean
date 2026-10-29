/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BatchCheck
public import CompStark.Ni.BatchFri
public import CompStark.Ni.BatchAccept
public import CompStark.Ni.Bcs
public import CompStark.Sound.BatchRbr

/-! # BCS consistency of the batch STARK

The batch verifier runs on pure primitives `H`, whose challenger answers are the Fiat–Shamir
challenges and whose Merkle hashes are answered from a cache of hash queries. The batch IOP's
transcript is read off the proof and the cache (`extractB`): every instance's trace and quotient
words are the columns extracted under the main and quotient commitments, at the instance's offset
among the matrices of its height (`Merkle.matColumn`, laid out by `Setup.mainHeights`,
`quotHeights` and the widths), FRI's words are extracted under the commit-phase commitments, the
opened values and final polynomial are the proof's, and the challenges are those the challenger
returns (`friStartB`, `commitReplayB`, `powSampleOfB`, `querySampleOfB`).

A query's accepted opening of each round, if it binds, opens the extracted columns (`main_rows`,
`quot_rows`, `prep_rows`), so its reduced openings are the batched DEEP words at its point
(`reducedAt_eq_groupDeepWord`), and FRI's checks on them are the run's (`query_run`).

`bcsB`: if the verifier accepts a proof whose commitments bind the rows extracted from the cache,
and under whose preprocessed commitment the cache holds the preprocessed traces' extensions, the
extracted transcript passes the deterministic checks of the batch terminal lemma
(`Sound.Batch.exists_satisfied_of_safe`): every instance's constraints hold at `ζ`, the final
polynomial has low degree, the query grinding sample has its vanishing bits, and every query lands
where FRI's checks pass and FRI's first word agrees with the tallest batched DEEP word.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop Polynomial

variable {F : Type} {EF : Type}

local notation "𝕂" => Challenge.Spec EF

/-! ### The rounds' heights -/

section Heights
variable [BaseField F] [Challenge F EF] (S : Iop.Batch.Setup EF) [S.CapFits] (common : CompStark.Batch.Common F)
  (proof : CompStark.Batch.BatchProof F EF) (zeta : EF)

/-- Every matrix of the rounds is some instance's extension, and every instance's extended
trace is a matrix of the main round. -/
theorem mem_matHeights (hsize : proof.opened.size = S.k) (a : ℕ) :
    a ∈ matHeights S.params (CompStark.Batch.batchRounds S.instances common proof zeta) ↔
      ∃ i : Fin S.k, S.logN i + S.params.logBlowup = a := by
  have hos : proof.opened.toList.length = S.k := by rw [Array.length_toList, hsize]
  have hinst : ∀ I ∈ S.instances, ∃ i : Fin S.k, I = ⟨S.air i, S.logN i, S.lookups i⟩ := fun I hI
      ↦ by
    rw [Iop.Batch.Setup.instances, List.mem_ofFn] at hI
    obtain ⟨i, hi⟩ := hI
    exact ⟨i, hi.symm⟩
  have hzip : ∀ x ∈ S.instances.zip proof.opened.toList,
      ∃ i : Fin S.k, x.1 = ⟨S.air i, S.logN i, S.lookups i⟩ := fun x hx ↦ hinst x.1
          (List.of_mem_zip hx).1
  constructor
  · intro ha
    simp only [matHeights, batchRounds_cases, List.mem_map, List.mem_flatMap,
      List.mem_append] at ha
    obtain ⟨d, ⟨r, hr, hd⟩, rfl⟩ := ha
    rcases hr with ((hr | hr) | hr)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
        obtain ⟨i, hi⟩ := hzip x hx
        exact ⟨i, by rw [hi]⟩
      · obtain ⟨x, hx, hd⟩ := List.mem_flatMap.mp hd
        obtain ⟨ch, -, rfl⟩ := List.mem_map.mp hd
        obtain ⟨i, hi⟩ := hzip x hx
        exact ⟨i, by rw [hi]⟩
    · rw [prepRounds] at hr
      split at hr
      · rw [List.mem_singleton] at hr
        subst hr
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
        obtain ⟨i, hi⟩ := hzip x (List.mem_filter.mp hx).1
        exact ⟨i, by rw [hi]⟩
      · exact absurd hr List.not_mem_nil
    · rw [permRounds] at hr
      split at hr
      · rw [List.mem_singleton] at hr
        subst hr
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
        obtain ⟨i, hi⟩ := hinst x.1 (List.of_mem_zip (List.mem_filter.mp hx).1).1
        exact ⟨i, by rw [hi]⟩
      · exact absurd hr List.not_mem_nil
  · rintro ⟨i, rfl⟩
    simp only [matHeights, batchRounds_cases, List.mem_map, List.mem_flatMap, List.mem_append]
    refine ⟨((⟨1, S.logN i⟩ : Domain F), traceOpenings (S.air i)
      (proof.opened.toList.getD i noOpenings) zeta (zeta * Ext.ofBase (twoAdicGen (S.logN i)))),
      ⟨_, Or.inl (Or.inl List.mem_cons_self), ?_⟩, rfl⟩
    refine List.mem_map.mpr ⟨(⟨S.air i, S.logN i, S.lookups i⟩, proof.opened.toList.getD i
        noOpenings), ?_,
      rfl⟩
    have hi : i.val < (S.instances.zip proof.opened.toList).length := by
      rw [List.length_zip, length_instances, hos, Nat.min_self]; exact i.isLt
    have := getD_map_zip_instances (S := S) _ hos id (⟨S.air i, S.logN i, S.lookups i⟩,
        noOpenings) i
    rw [List.map_id, List.getD_eq_getElem _ _ hi] at this
    rw [show ((⟨S.air i, S.logN i, S.lookups i⟩ : CompStark.Batch.Instance F),
      proof.opened.toList.getD i noOpenings) = (S.instances.zip proof.opened.toList)[i.val] from
        this.symm]
    exact List.getElem_mem hi

/-- The FRI verifier's heights are the tallest domain's, then the shorter instances'. -/
theorem descHeights_batchRounds (hsize : proof.opened.size = S.k) :
    descHeights (matHeights S.params (CompStark.Batch.batchRounds S.instances common proof zeta)) =
      S.logTop :: S.friHeights := by
  have hfit := fits_friHeights S
  refine List.Pairwise.eq_of_mem_iff (r := (· > ·)) (pairwise_descHeights _)
    (List.pairwise_cons.mpr ⟨fun m hm ↦ (hfit.2 m hm).2, hfit.1⟩) fun a ↦ ?_
  rw [mem_descHeights, mem_matHeights S common proof zeta hsize, List.mem_cons,
    mem_friHeights]
  constructor
  · rintro ⟨i, rfl⟩
    by_cases h : S.logN i + S.params.logBlowup = S.logTop
    · exact Or.inl h
    · exact Or.inr ⟨i, rfl, h⟩
  · rintro (rfl | ⟨i, rfl, -⟩)
    · exact ⟨S.top, rfl⟩
    · exact ⟨i, rfl⟩

end Heights

/-! ### The rounds' matrices -/

section Matrices
variable [BaseField F] [Challenge F EF] (S : Iop.Batch.Setup EF) [S.CapFits]

/-- The statement's instances, zipped with every instance's opened values. -/
theorem zip_instances (os : List (OpenedValues EF)) (hos : os.length = S.k) :
    S.instances.zip os = (List.finRange S.k).map fun i ↦
      ((⟨S.air i, S.logN i, S.lookups i⟩ : CompStark.Batch.Instance F), os.getD i noOpenings) := by
  refine List.ext_getElem (by rw [List.length_zip, length_instances, hos, Nat.min_self,
    List.length_map, List.length_finRange]) fun j h1 h2 ↦ ?_
  have hj : j < S.k := by simpa only [List.length_map, List.length_finRange] using h2
  have := getD_map_zip_instances (S := S) _ hos id (⟨S.air ⟨0, S.nonempty⟩, 0, []⟩, noOpenings)
    ⟨j, hj⟩
  rw [List.map_id, List.getD_eq_getElem _ _ h1] at this
  rw [this, List.getElem_map, List.getElem_finRange]
  rfl

/-- The quotient commitment's matrices' heights: every instance's chunks. -/
def quotHeights : List ℕ :=
  (List.finRange S.k).flatMap fun i ↦
    List.replicate (S.instanceSetup i).chunks (2 ^ (S.logN i + S.params.logBlowup))

/-- The quotient commitment's matrices' widths: a chunk's `d` coordinates. -/
def quotWidths : List ℕ := (quotHeights S).map fun _ ↦ Challenge.d EF

/-- The instances with preprocessed columns. -/
def prepInsts : List (Fin S.k) := (List.finRange S.k).filter fun i ↦ 0 < (S.air i).preprocessedWidth

/-- The preprocessed commitment's matrices' heights. -/
def prepHeights : List ℕ := (prepInsts S).map fun i ↦ 2 ^ (S.logN i + S.params.logBlowup)

/-- The preprocessed commitment's matrices' widths. -/
def prepWidths : List ℕ := (prepInsts S).map fun i ↦ (S.air i).preprocessedWidth

/-- The log height of the tallest preprocessed trace's extension. -/
def prepLog : ℕ := ((prepInsts S).map fun i ↦ S.logN i + S.params.logBlowup).foldl max 0

/-- The instances with lookups. -/
def permInsts : List (Fin S.k) := (List.finRange S.k).filter fun i ↦ !(S.lookups i).isEmpty

/-- The permutation commitment's matrices' heights. -/
def permHeights : List ℕ := (permInsts S).map fun i ↦ 2 ^ (S.logN i + S.params.logBlowup)

/-- The permutation commitment's matrices' widths: every column's `d` coordinates. -/
def permWidths : List ℕ := (permInsts S).map fun i ↦ Challenge.d EF * (S.instanceSetup i).permWidth

/-- The log height of the tallest permutation trace's extension. -/
def permLog : ℕ := ((permInsts S).map fun i ↦ S.logN i + S.params.logBlowup).foldl max 0

end Matrices

/-! ### A round's rows are its extracted columns -/

section Rows

/-- A round's tallest matrix has the height every matrix is at most and some matrix has. -/
theorem logBatch_eq (P : Params) (mats : List (Domain F × List (EF × List EF))) (a : ℕ)
    (ha : a ∈ mats.map (·.1.logSize + P.logBlowup))
    (hle : ∀ x ∈ mats, x.1.logSize + P.logBlowup ≤ a) : logBatch P mats = a := by
  unfold logBatch
  refine le_antisymm ?_ ((le_foldl_max _ 0).2 a ha)
  rcases foldl_max_mem (mats.map (·.1.logSize + P.logBlowup)) 0 with h | h
  · rw [h]
    exact Nat.zero_le _
  · obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h
    rw [← hxe]
    exact hle x hx

variable [BaseField F] (H : Primitives F Id)

/-- The opened values at every point of a round's matrix have a value per column of its row. -/
theorem size_of_batchOk (P : Params) (logMax I : ℕ) (x : List (Array F) × Round F EF)
    (hok : BatchOkR H P logMax I x) (t : ℕ) (ht : t < x.2.2.length) :
    ∀ zy ∈ (x.2.2[t]'ht).2, zy.2.length = (x.1.getD t #[]).size := by
  obtain ⟨-, -, -, hlen, hw⟩ := hok
  have ht1 : t < x.1.length := hlen ▸ ht
  have hz : t < (x.1.zip x.2.2).length := by rw [List.length_zip]; omega
  have hmem := hw _ (List.getElem_mem hz)
  rw [List.getElem_zip] at hmem
  rw [List.getD_eq_getElem _ _ ht1]
  exact hmem

/-- **A round's rows are its extracted columns.** If a round's opening at `I` is accepted and
binds, every matrix's row opens its columns extracted under the round's commitment, at the index
shifted to the matrix's height. -/
theorem rows_eq_matColumn (P : Params) (cache : Merkle.Cache F (Digest F)) (logMax I : ℕ)
    (x : List (Array F) × Round F EF) (hok : BatchOkR H P logMax I x)
    (hbind : CapBindingM cache H x.2.1 P.capHeight (logBatch P x.2.2) (roundHeights P x.2.2))
    (hle : logBatch P x.2.2 ≤ logMax) (ws : List ℕ)
    (hws : ∀ t < x.2.2.length, (x.1.getD t #[]).size = ws.getD t 0)
    (t : ℕ) (ht : t < x.2.2.length) (m : ℕ)
    (hm : (x.2.2[t]'ht).1.logSize + P.logBlowup = m) (hcap : P.capHeight ≤ m) (j : ℕ)
    (hj : j < ws.getD t 0) :
    Merkle.matColumnCap cache x.2.1.toList P.capHeight (logBatch P x.2.2) (roundHeights P x.2.2)
      ws t j m (I >>> (logMax - m)) = (x.1.getD t #[]).toList.getD j 0 := by
  obtain ⟨-, -, ⟨path, hv⟩, -, -⟩ := hok
  have hmK : m ≤ logBatch P x.2.2 :=
    (le_foldl_max _ 0).2 m (List.mem_map.mpr ⟨_, List.getElem_mem ht, hm⟩)
  have hsh : I >>> (logMax - logBatch P x.2.2) >>> (logBatch P x.2.2 - m) =
      I >>> (logMax - m) := by
    rw [← Nat.shiftRight_add]
    congr 1
    omega
  have hvals : ∀ t', (x.1.map (·.toList)).getD t' [] = (x.1.getD t' #[]).toList := fun t' ↦
    List.getD_map x.1 (#[] : Array F) (fun a : Array F ↦ a.toList) (n := t')
  have hlen : (roundHeights P x.2.2).length = x.2.2.length := List.length_map _
  rw [← hsh, matColumnCap_eq cache H x.2.1 _ _ _ ws hbind _ (x.1.map (·.toList)) path hv
    (fun t' ht' ↦ by rw [hvals, Array.length_toList]; exact hws t' (hlen ▸ ht')) t m
    (hlen ▸ ht) ?_ ((Nat.min_le_left _ _).trans hcap) hmK j hj, hvals]
  rw [roundHeights, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem ht,
    Option.map_some, Option.getD_some, hm]

end Rows

/-! ### The main traces' round -/

section Main
variable [BaseField F] [Challenge F EF] (H : Primitives F Id) (S : Iop.Batch.Setup EF) [S.CapFits]
  (cache : Merkle.Cache F (Digest F)) (proof : CompStark.Batch.BatchProof F EF) (zeta : EF)

theorem getD_ofFn {α : Type} {k : ℕ} (f : Fin k → α) (i : Fin k) (d : α) :
    (List.ofFn f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]

/-- The main round's matrices: every instance's extended trace, opened at `ζ` and, if read, at
`ζ ω`. -/
abbrev mainMats : List (Domain F × List (EF × List EF)) :=
  (S.instances.zip proof.opened.toList).map fun x ↦
    ((⟨1, x.1.logN⟩ : Domain F), traceOpenings x.1.air x.2 zeta
      (zeta * Ext.ofBase (twoAdicGen x.1.logN)))

theorem mainMats_eq (hsize : proof.opened.size = S.k) :
    mainMats S proof zeta = (List.finRange S.k).map fun i ↦
      ((⟨1, S.logN i⟩ : Domain F), traceOpenings (S.air i)
        (proof.opened.toList.getD i noOpenings) zeta
        (zeta * Ext.ofBase (twoAdicGen (S.logN i)))) := by
  rw [mainMats, zip_instances S _ (by rw [Array.length_toList, hsize]), List.map_map]
  rfl

theorem capHeight_le_logSize (i : Fin S.k) :
    S.params.capHeight ≤ S.logN i + S.params.logBlowup :=
  (S.capFits i).trans (Nat.sub_le _ _)

theorem logTop_ge (i : Fin S.k) : S.logN i + S.params.logBlowup ≤ S.logTop := by
  have := S.logN_le_top i
  unfold Iop.Batch.Setup.logTop
  omega

/-- **The main traces' rows.** If a query's opening of the main round at `I` is accepted and
binds, every instance's row opens its trace columns extracted under the main commitment. -/
theorem main_rows (hsize : proof.opened.size = S.k)
    (hshape : ∀ i : Fin S.k, (proof.opened.toList.getD i noOpenings).traceLocal.size =
      (S.air i).width)
    (I : ℕ) (rM : List (Array F))
    (hok : BatchOkR H S.params S.logTop I (rM, proof.mainCommit, mainMats S proof zeta))
    (hbind : CapBindingM cache H proof.mainCommit S.params.capHeight S.logTop S.mainHeights)
    (i : Fin S.k) (j : ℕ) (hj : j < (S.air i).width) :
    (rM.getD i #[]).toList.getD j 0 = Merkle.matColumnCap cache proof.mainCommit.toList
      S.params.capHeight S.logTop S.mainHeights S.mainWidths i j (S.logN i + S.params.logBlowup)
      (I >>> (S.logTop - (S.logN i + S.params.logBlowup))) := by
  have hM := mainMats_eq S proof zeta hsize
  have hlen : (mainMats S proof zeta).length = S.k := by
    rw [hM, List.length_map, List.length_finRange]
  have hget : ∀ (t : ℕ) (ht : t < (mainMats S proof zeta).length),
      (mainMats S proof zeta)[t] = ((⟨1, S.logN ⟨t, hlen ▸ ht⟩⟩ : Domain F),
        traceOpenings (S.air ⟨t, hlen ▸ ht⟩) (proof.opened.toList.getD t noOpenings) zeta
        (zeta * Ext.ofBase (twoAdicGen (S.logN ⟨t, hlen ▸ ht⟩)))) := by
    intro t ht
    simp only [hM, List.getElem_map, List.getElem_finRange, Fin.cast_mk]
  have hlb : logBatch S.params (mainMats S proof zeta) = S.logTop := by
    refine logBatch_eq S.params _ _ ?_ fun x hx ↦ ?_
    · rw [hM, List.map_map]
      exact List.mem_map.mpr ⟨S.top, List.mem_finRange _, rfl⟩
    · rw [hM] at hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact logTop_ge S i
  have hrh : roundHeights S.params (mainMats S proof zeta) = S.mainHeights := by
    rw [hM, roundHeights, List.map_map, Iop.Batch.Setup.mainHeights, List.ofFn_eq_map]
    rfl
  have hit : i.val < (mainMats S proof zeta).length := by rw [hlen]; exact i.isLt
  have hws : ∀ t < (mainMats S proof zeta).length,
      (rM.getD t #[]).size = S.mainWidths.getD t 0 := by
    intro t ht
    have h1 := size_of_batchOk H S.params S.logTop I _ hok t ht
    dsimp only at h1
    rw [hget t ht] at h1
    have h2 := h1 _ List.mem_cons_self
    dsimp only at h2
    rw [← h2, Array.length_toList, hshape ⟨t, hlen ▸ ht⟩, Iop.Batch.Setup.mainWidths]
    exact (getD_ofFn (fun i ↦ (S.air i).width) ⟨t, hlen ▸ ht⟩ 0).symm
  have := rows_eq_matColumn H S.params cache S.logTop I _ hok (by rw [hlb, hrh]; exact hbind)
    (by rw [hlb]) S.mainWidths hws i hit (S.logN i + S.params.logBlowup) (by rw [hget])
    (capHeight_le_logSize S i) j (by rw [Iop.Batch.Setup.mainWidths, getD_ofFn]; exact hj)
  rw [← this, hlb, hrh]

end Main

/-! ### The quotient chunks' round -/

section Quotient

/-- Reading an entry of a block of a concatenation of blocks, past the earlier blocks. -/
theorem getD_flatMap_blocks {β γ : Type} (f : β → List γ) (d : γ) :
    ∀ (L : List β) (i : ℕ) (hi : i < L.length) (c : ℕ), c < (f L[i]).length →
      (L.flatMap f).getD (((L.take i).map fun b ↦ (f b).length).sum + c) d = (f L[i]).getD c d
  | [], _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | b :: L, 0, _, c, hc => by
    rw [List.getElem_cons_zero] at hc ⊢
    rw [List.flatMap_cons, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add,
      List.getD_append _ _ _ _ hc]
  | b :: L, i + 1, hi, c, hc => by
    rw [List.flatMap_cons, List.take_succ_cons, List.map_cons, List.sum_cons, Nat.add_assoc,
      List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
    exact getD_flatMap_blocks f d L i (by simp only [List.length_cons] at hi; omega) c hc

variable [BaseField F] [Challenge F EF] (H : Primitives F Id) (S : Iop.Batch.Setup EF) [S.CapFits]
  (cache : Merkle.Cache F (Digest F)) (proof : CompStark.Batch.BatchProof F EF) (zeta : EF)

/-- The quotient round's matrices: every instance's chunks, opened at `ζ`. -/
abbrev quotMats : List (Domain F × List (EF × List EF)) :=
  (S.instances.zip proof.opened.toList).flatMap fun x ↦
    x.2.quotientChunks.toList.map fun ch ↦ ((⟨1, x.1.logN⟩ : Domain F), [(zeta, ch.toList)])

/-- Instance `i`'s block of the quotient round's matrices. -/
abbrev quotBlock (i : Fin S.k) : List (Domain F × List (EF × List EF)) :=
  (proof.opened.toList.getD i noOpenings).quotientChunks.toList.map fun ch ↦
    ((⟨1, S.logN i⟩ : Domain F), [(zeta, ch.toList)])

theorem quotMats_eq (hsize : proof.opened.size = S.k) :
    quotMats S proof zeta = (List.finRange S.k).flatMap (quotBlock S proof zeta) := by
  rw [quotMats, zip_instances S _ (by rw [Array.length_toList, hsize]), List.flatMap_map]

/-- **The quotient chunks' rows.** If a query's opening of the quotient round at `I` is accepted
and binds, every chunk's row opens its coordinates extracted under the quotient commitment. -/
theorem quot_rows (hsize : proof.opened.size = S.k)
    (hshape : ∀ i : Fin S.k, (proof.opened.toList.getD i noOpenings).quotientChunks.size =
      (S.instanceSetup i).chunks ∧ ∀ ch ∈ (proof.opened.toList.getD i noOpenings).quotientChunks,
        ch.size = Challenge.d EF)
    (I : ℕ) (rQ : List (Array F))
    (hok : BatchOkR H S.params S.logTop I (rQ, proof.quotientCommit, quotMats S proof zeta))
    (hbind : CapBindingM cache H proof.quotientCommit S.params.capHeight S.logTop (quotHeights S))
    (i : Fin S.k) (c : Fin (S.instanceSetup i).chunks) (e : ℕ) (he : e < Challenge.d EF) :
    (rQ.getD (quotOffset S i + c) #[]).toList.getD e 0 = Merkle.matColumnCap cache
      proof.quotientCommit.toList S.params.capHeight S.logTop (quotHeights S) (quotWidths S)
      (quotOffset S i + c) e (S.logN i + S.params.logBlowup)
      (I >>> (S.logTop - (S.logN i + S.params.logBlowup))) := by
  have hQ := quotMats_eq S proof zeta hsize
  have hbl : ∀ i' : Fin S.k, (quotBlock S proof zeta i').length = (S.instanceSetup i').chunks :=
    fun i' ↦ by rw [List.length_map, Array.length_toList, (hshape i').1]
  have hoff : (((List.finRange S.k).take i).map fun b ↦ (quotBlock S proof zeta b).length).sum =
      quotOffset S i := by
    rw [quotOffset, List.ofFn_eq_map, ← List.map_take]
    exact congrArg List.sum (List.map_congr_left fun i' _ ↦ hbl i')
  have hik : i.val < (List.finRange S.k).length := by rw [List.length_finRange]; exact i.isLt
  have hfi : (List.finRange S.k)[i.val] = i := by
    rw [List.getElem_finRange]
    rfl
  have hcb : c.val < (quotBlock S proof zeta (List.finRange S.k)[i.val]).length := by
    rw [hfi, hbl]
    exact c.isLt
  have hblk := getD_flatMap_blocks (quotBlock S proof zeta) (⟨0, 0⟩, []) _ i.val hik c.val hcb
  rw [hoff, hfi] at hblk
  rw [← hQ] at hblk
  have hmem : ∀ x ∈ quotMats S proof zeta, ∃ i' : Fin S.k, x.1.logSize = S.logN i' ∧
      ∃ ch ∈ (proof.opened.toList.getD i' noOpenings).quotientChunks,
        x.2 = [(zeta, ch.toList)] := by
    intro x hx
    rw [hQ] at hx
    obtain ⟨i', -, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.mp hx
    exact ⟨i', rfl, ch, Array.mem_toList_iff.mp hch, rfl⟩
  have hlb : logBatch S.params (quotMats S proof zeta) = S.logTop := by
    refine logBatch_eq S.params _ _ ?_ fun x hx ↦ ?_
    · have h0 : 0 < (quotBlock S proof zeta S.top).length := by
        rw [hbl]
        exact Nat.two_pow_pos _
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos h0)
      refine List.mem_map.mpr ⟨x, ?_, ?_⟩
      · rw [hQ]
        exact List.mem_flatMap.mpr ⟨S.top, List.mem_finRange _, hx⟩
      · obtain ⟨ch, -, rfl⟩ := List.mem_map.mp hx
        rfl
    · obtain ⟨i', hi', -⟩ := hmem x hx
      rw [hi']
      exact logTop_ge S i'
  have hrh : roundHeights S.params (quotMats S proof zeta) = quotHeights S := by
    rw [hQ, roundHeights, List.map_flatMap, quotHeights]
    refine List.flatMap_congr fun i' _ ↦ ?_
    rw [← hbl i', quotBlock, List.map_map, List.length_map]
    exact List.map_const' (b := 2 ^ (S.logN i' + S.params.logBlowup))
  have hwl : (quotWidths S).length = (quotMats S proof zeta).length := by
    rw [quotWidths, List.length_map, ← hrh, roundHeights, List.length_map]
  have hwd : ∀ t < (quotMats S proof zeta).length, (quotWidths S).getD t 0 = Challenge.d EF := by
    intro t ht
    rw [List.getD_eq_getElem _ _ (hwl ▸ ht)]
    simp only [quotWidths, List.getElem_map]
  have hws : ∀ t < (quotMats S proof zeta).length,
      (rQ.getD t #[]).size = (quotWidths S).getD t 0 := by
    intro t ht
    have h1 := size_of_batchOk H S.params S.logTop I _ hok t ht
    obtain ⟨i', -, ch, hch, h2⟩ := hmem _ (List.getElem_mem ht)
    dsimp only at h1
    rw [h2] at h1
    have h3 := h1 _ List.mem_cons_self
    dsimp only at h3
    rw [hwd t ht, ← h3, Array.length_toList, (hshape i').2 ch hch]
  have hlen : (quotMats S proof zeta).length = ((List.finRange S.k).flatMap
      (quotBlock S proof zeta)).length := by rw [hQ]
  have ht : quotOffset S i + c.val < (quotMats S proof zeta).length := by
    by_contra hge
    have hnil := List.getD_eq_default (quotMats S proof zeta) (⟨0, 0⟩, [])
      (Nat.le_of_not_lt hge)
    rw [hnil] at hblk
    have hc2 : c.val < (quotBlock S proof zeta i).length := by rw [hbl]; exact c.isLt
    rw [List.getD_eq_getElem _ _ hc2] at hblk
    have := congrArg Prod.snd hblk
    simp only [List.getElem_map] at this
    exact absurd this.symm (List.cons_ne_nil _ _)
  have hti : (quotMats S proof zeta)[quotOffset S i + c.val] =
      ((⟨1, S.logN i⟩ : Domain F), [(zeta,
        ((proof.opened.toList.getD i noOpenings).quotientChunks.toList.getD c #[]).toList)]) := by
    rw [← List.getD_eq_getElem _ (⟨0, 0⟩, []) ht, hblk]
    have hc2 : c.val < (quotBlock S proof zeta i).length := by rw [hbl]; exact c.isLt
    have hcc : c.val < (proof.opened.toList.getD i noOpenings).quotientChunks.toList.length := by
      rw [Array.length_toList, (hshape i).1]; exact c.isLt
    rw [List.getD_eq_getElem _ #[] hcc, List.getD_eq_getElem _ _ hc2]
    simp only [List.getElem_map]
  have := rows_eq_matColumn H S.params cache S.logTop I _ hok (by rw [hlb, hrh]; exact hbind)
    (by rw [hlb]) (quotWidths S) hws _ ht (S.logN i + S.params.logBlowup) (by rw [hti])
    (capHeight_le_logSize S i) e (by rw [hwd _ ht]; exact he)
  rw [← this, hlb, hrh]

end Quotient

/-! ### The preprocessed traces' round -/

section Preprocessed

/-- The entry of a filtered list at an entry's rank among those that pass is that entry. -/
theorem getD_filter_rank {β : Type} (q : β → Bool) (d : β) :
    ∀ (L : List β) (n : ℕ) (hn : n < L.length), q L[n] = true →
      (L.filter q).getD ((L.take n).filter q).length d = L[n]
  | [], _, hn, _ => absurd hn (Nat.not_lt_zero _)
  | b :: L, 0, _, hq => by
    rw [List.getElem_cons_zero] at hq ⊢
    rw [List.take_zero, List.filter_nil, List.length_nil, List.filter_cons_of_pos hq,
      List.getD_cons_zero]
  | b :: L, n + 1, hn, hq => by
    rw [List.getElem_cons_succ] at hq ⊢
    have ih := getD_filter_rank q d L n (by simp only [List.length_cons] at hn; omega) hq
    rw [List.take_succ_cons, List.filter_cons, List.filter_cons]
    split
    · rw [List.length_cons, List.getD_cons_succ, ih]
    · exact ih

variable [BaseField F] [Challenge F EF] (H : Primitives F Id) (S : Iop.Batch.Setup EF) [S.CapFits]
  (cache : Merkle.Cache F (Digest F)) (proof : CompStark.Batch.BatchProof F EF) (zeta : EF)

/-- The preprocessed round's matrices: the extended preprocessed traces of the instances that
have them, opened at `ζ` and, if read, at `ζ ω`. -/
abbrev prepMats : List (Domain F × List (EF × List EF)) :=
  ((S.instances.zip proof.opened.toList).filter (0 < ·.1.air.preprocessedWidth)).map fun x ↦
    ((⟨1, x.1.logN⟩ : Domain F), (zeta, (x.2.preprocessedLocal.getD #[]).toList) ::
      if x.1.air.opensPreprocessedNext then
        [(zeta * Ext.ofBase (twoAdicGen x.1.logN), (x.2.preprocessedNext.getD #[]).toList)]
      else [])

/-- Instance `i`'s preprocessed matrix. -/
abbrev prepMat (i : Fin S.k) : Domain F × List (EF × List EF) :=
  let o := proof.opened.toList.getD i noOpenings
  ((⟨1, S.logN i⟩ : Domain F), (zeta, (o.preprocessedLocal.getD #[]).toList) ::
    if (S.air i).opensPreprocessedNext then
      [(zeta * Ext.ofBase (twoAdicGen (S.logN i)), (o.preprocessedNext.getD #[]).toList)]
    else [])

theorem prepMats_eq (hsize : proof.opened.size = S.k) :
    prepMats S proof zeta = (prepInsts S).map (prepMat S proof zeta) := by
  rw [prepMats, zip_instances S _ (by rw [Array.length_toList, hsize]), List.filter_map,
    List.map_map, prepInsts]
  rfl

theorem prepIndex_eq (i : Fin S.k) :
    prepIndex S i = (((List.finRange S.k).take i).filter fun i' ↦
      0 < (S.air i').preprocessedWidth).length := by
  rw [prepIndex, Iop.Batch.Setup.instances, List.ofFn_eq_map, ← List.map_take, List.filter_map,
    List.length_map]
  rfl

/-- Instance `i` is at its rank among the instances with preprocessed columns. -/
theorem getD_prepInsts (i : Fin S.k) (hp : 0 < (S.air i).preprocessedWidth) (d : Fin S.k) :
    (prepInsts S).getD (prepIndex S i) d = i := by
  have hik : i.val < (List.finRange S.k).length := by rw [List.length_finRange]; exact i.isLt
  have hfi : (List.finRange S.k)[i.val] = i := by
    rw [List.getElem_finRange]
    rfl
  rw [prepIndex_eq, prepInsts]
  have := getD_filter_rank (fun i' ↦ decide (0 < (S.air i').preprocessedWidth)) d _ i.val hik
    (by rw [hfi]; exact decide_eq_true hp)
  rw [hfi] at this
  exact this

theorem prepLog_le : prepLog S ≤ S.logTop := by
  unfold prepLog
  rcases foldl_max_mem ((prepInsts S).map fun i ↦ S.logN i + S.params.logBlowup) 0 with h | h
  · rw [h]
    exact Nat.zero_le _
  · obtain ⟨i, -, hi⟩ := List.mem_map.mp h
    rw [← hi]
    exact logTop_ge S i

/-- **The preprocessed traces' rows.** If a query's opening of the preprocessed round at `I` is
accepted and binds, the row of every instance with preprocessed columns opens them as extracted
under the preprocessed commitment. -/
theorem prep_rows (hsize : proof.opened.size = S.k)
    (hshape : ∀ i : Fin S.k,
      ((proof.opened.toList.getD i noOpenings).preprocessedLocal.getD #[]).size =
        (S.air i).preprocessedWidth)
    (I : ℕ) (root : Cap F) (rP : List (Array F))
    (hok : BatchOkR H S.params S.logTop I (rP, root, prepMats S proof zeta))
    (hbind : CapBindingM cache H root S.params.capHeight (prepLog S) (prepHeights S))
    (i : Fin S.k) (hp : 0 < (S.air i).preprocessedWidth) (j : ℕ)
    (hj : j < (S.air i).preprocessedWidth) :
    (rP.getD (prepIndex S i) #[]).toList.getD j 0 = Merkle.matColumnCap cache root.toList
      S.params.capHeight (prepLog S) (prepHeights S) (prepWidths S) (prepIndex S i) j
      (S.logN i + S.params.logBlowup)
      (I >>> (S.logTop - (S.logN i + S.params.logBlowup))) := by
  have hP := prepMats_eq S proof zeta hsize
  have hlen : (prepMats S proof zeta).length = (prepInsts S).length := by
    rw [hP, List.length_map]
  have hget : ∀ (t : ℕ) (ht : t < (prepMats S proof zeta).length),
      (prepMats S proof zeta)[t] = prepMat S proof zeta ((prepInsts S)[t]'(hlen ▸ ht)) := by
    intro t ht
    simp only [hP, List.getElem_map]
  have hlb : logBatch S.params (prepMats S proof zeta) = prepLog S := by
    rw [logBatch, hP, List.map_map, prepLog]
    rfl
  have hrh : roundHeights S.params (prepMats S proof zeta) = prepHeights S := by
    rw [hP, roundHeights, List.map_map, prepHeights]
    rfl
  have hwd : ∀ t (ht : t < (prepMats S proof zeta).length),
      (prepWidths S).getD t 0 = (S.air ((prepInsts S)[t]'(hlen ▸ ht))).preprocessedWidth := by
    intro t ht
    rw [prepWidths, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hlen ▸ ht),
      List.getElem_map]
  have hws : ∀ t < (prepMats S proof zeta).length,
      (rP.getD t #[]).size = (prepWidths S).getD t 0 := by
    intro t ht
    have h1 := size_of_batchOk H S.params S.logTop I _ hok t ht
    dsimp only at h1
    rw [hget t ht] at h1
    have h2 := h1 _ List.mem_cons_self
    dsimp only at h2
    rw [← h2, Array.length_toList, hshape, hwd t ht]
  have hrank : prepIndex S i < (prepInsts S).length := by
    rw [prepIndex_eq, prepInsts]
    have hik : i.val < (List.finRange S.k).length := by rw [List.length_finRange]; exact i.isLt
    have hfi : (List.finRange S.k)[i.val] = i := by
      rw [List.getElem_finRange]
      rfl
    have hsplit := List.take_append_drop i.val (List.finRange S.k)
    rw [List.drop_eq_getElem_cons hik, hfi] at hsplit
    conv_rhs => rw [← hsplit]
    rw [List.filter_append, List.length_append, List.filter_cons_of_pos
      (p := fun i ↦ decide (0 < (S.air i).preprocessedWidth)) (decide_eq_true hp),
      List.length_cons]
    omega
  have ht : prepIndex S i < (prepMats S proof zeta).length := hlen ▸ hrank
  have hti : (prepInsts S)[prepIndex S i]'hrank = i := by
    rw [← List.getD_eq_getElem _ i hrank]
    exact getD_prepInsts S i hp i
  have := rows_eq_matColumn H S.params cache S.logTop I _ hok (by rw [hlb, hrh]; exact hbind)
    (by rw [hlb]; exact prepLog_le S) (prepWidths S) hws _ ht (S.logN i + S.params.logBlowup)
    (by rw [hget, hti]) (capHeight_le_logSize S i) j (by rw [hwd _ ht, hti]; exact hj)
  rw [← this, hlb, hrh]

end Preprocessed

/-! ### The permutation traces' round -/

section Permutation
variable [BaseField F] [Challenge F EF] (H : Primitives F Id) (S : Iop.Batch.Setup EF) [S.CapFits]
  (cache : Merkle.Cache F (Digest F)) (proof : CompStark.Batch.BatchProof F EF) (zeta : EF)

/-- The statement's instances, zipped with a list of one entry per instance. -/
theorem zip_instances_getD {β : Type} (os : List β) (hos : os.length = S.k) (d : β) :
    S.instances.zip os = (List.finRange S.k).map fun i ↦
      ((⟨S.air i, S.logN i, S.lookups i⟩ : CompStark.Batch.Instance F), os.getD i d) := by
  refine List.ext_getElem (by rw [List.length_zip, length_instances, hos, Nat.min_self,
    List.length_map, List.length_finRange]) fun j h1 h2 ↦ ?_
  have hj : j < S.k := by simpa only [List.length_map, List.length_finRange] using h2
  rw [List.getElem_zip, List.getElem_map, List.getElem_finRange,
    List.getD_eq_getElem _ _ (by rw [hos]; exact hj)]
  simp only [Iop.Batch.Setup.instances, List.getElem_ofFn]
  rfl

/-- Instance `i`'s permutation matrix, opened at `ζ` and `ζ ω`. -/
abbrev permMat (i : Fin S.k) : Domain F × List (EF × List EF) :=
  ((⟨1, S.logN i⟩ : Domain F), [(zeta, (proof.permutationLocal.getD i #[]).toList),
    (zeta * Ext.ofBase (twoAdicGen (S.logN i)), (proof.permutationNext.getD i #[]).toList)])

theorem permMats_eq (hlsize : proof.permutationLocal.size = S.k)
    (hnsize : proof.permutationNext.size = S.k) :
    permMats S proof zeta = (permInsts S).map (permMat S proof zeta) := by
  have hz : (proof.permutationLocal.toList.zip proof.permutationNext.toList).length = S.k := by
    rw [List.length_zip, Array.length_toList, Array.length_toList, hlsize, hnsize, Nat.min_self]
  rw [permMats, zip_instances_getD S _ hz (#[], #[]), List.filter_map, List.map_map, permInsts]
  refine List.map_congr_left fun i _ ↦ ?_
  have hpair : (proof.permutationLocal.toList.zip proof.permutationNext.toList).getD i
      (#[], #[]) = (proof.permutationLocal.getD i #[], proof.permutationNext.getD i #[]) := by
    rw [List.getD_eq_getElem _ _ (by rw [hz]; exact i.isLt), List.getElem_zip,
      Array.getElem_toList, Array.getElem_toList, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by rw [hlsize]; exact i.isLt), Option.getD_some,
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hnsize]; exact i.isLt),
      Option.getD_some]
  simp only [Function.comp_apply, hpair]

theorem permIndex_eq (i : Fin S.k) :
    permIndex S i = (((List.finRange S.k).take i).filter fun i' ↦
      !(S.lookups i').isEmpty).length := by
  rw [permIndex, Iop.Batch.Setup.instances, List.ofFn_eq_map, ← List.map_take, List.filter_map,
    List.length_map]
  rfl

/-- Instance `i` is at its rank among the instances with lookups. -/
theorem getD_permInsts (i : Fin S.k) (hp : S.lookups i ≠ []) (d : Fin S.k) :
    (permInsts S).getD (permIndex S i) d = i := by
  have hik : i.val < (List.finRange S.k).length := by rw [List.length_finRange]; exact i.isLt
  have hfi : (List.finRange S.k)[i.val] = i := by
    rw [List.getElem_finRange]
    rfl
  rw [permIndex_eq, permInsts]
  have := getD_filter_rank (fun i' ↦ !(S.lookups i').isEmpty) d _ i.val hik
    (by rw [hfi]; simpa only [Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff]
      using hp)
  rw [hfi] at this
  exact this

theorem permLog_le : permLog S ≤ S.logTop := by
  unfold permLog
  rcases foldl_max_mem ((permInsts S).map fun i ↦ S.logN i + S.params.logBlowup) 0 with h | h
  · rw [h]
    exact Nat.zero_le _
  · obtain ⟨i, -, hi⟩ := List.mem_map.mp h
    rw [← hi]
    exact logTop_ge S i

/-- **The permutation traces' rows.** If a query's opening of the permutation round at `I` is
accepted and binds, the row of every instance with lookups opens its permutation trace's
coordinates as extracted under the permutation commitment. -/
theorem perm_rows (hlsize : proof.permutationLocal.size = S.k)
    (hnsize : proof.permutationNext.size = S.k)
    (hshape : ∀ i : Fin S.k,
      (proof.permutationLocal.getD i #[]).size = Challenge.d EF * (S.instanceSetup i).permWidth)
    (I : ℕ) (root : Cap F) (rR : List (Array F))
    (hok : BatchOkR H S.params S.logTop I (rR, root, permMats S proof zeta))
    (hbind : CapBindingM cache H root S.params.capHeight (permLog S) (permHeights S))
    (i : Fin S.k) (hp : S.lookups i ≠ []) (j : ℕ)
    (hj : j < Challenge.d EF * (S.instanceSetup i).permWidth) :
    (rR.getD (permIndex S i) #[]).toList.getD j 0 = Merkle.matColumnCap cache root.toList
      S.params.capHeight (permLog S) (permHeights S) (permWidths S) (permIndex S i) j
      (S.logN i + S.params.logBlowup)
      (I >>> (S.logTop - (S.logN i + S.params.logBlowup))) := by
  have hP := permMats_eq S proof zeta hlsize hnsize
  have hlen : (permMats S proof zeta).length = (permInsts S).length := by
    rw [hP, List.length_map]
  have hget : ∀ (t : ℕ) (ht : t < (permMats S proof zeta).length),
      (permMats S proof zeta)[t] = permMat S proof zeta ((permInsts S)[t]'(hlen ▸ ht)) := by
    intro t ht
    simp only [hP, List.getElem_map]
  have hlb : logBatch S.params (permMats S proof zeta) = permLog S := by
    rw [logBatch, hP, List.map_map, permLog]
    rfl
  have hrh : roundHeights S.params (permMats S proof zeta) = permHeights S := by
    rw [hP, roundHeights, List.map_map, permHeights]
    rfl
  have hwd : ∀ t (ht : t < (permMats S proof zeta).length),
      (permWidths S).getD t 0 =
        Challenge.d EF * (S.instanceSetup ((permInsts S)[t]'(hlen ▸ ht))).permWidth := by
    intro t ht
    rw [permWidths, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hlen ▸ ht),
      List.getElem_map]
  have hws : ∀ t < (permMats S proof zeta).length,
      (rR.getD t #[]).size = (permWidths S).getD t 0 := by
    intro t ht
    have h1 := size_of_batchOk H S.params S.logTop I _ hok t ht
    dsimp only at h1
    rw [hget t ht] at h1
    have h2 := h1 _ List.mem_cons_self
    dsimp only at h2
    rw [← h2, Array.length_toList, hshape, hwd t ht]
  have hrank : permIndex S i < (permInsts S).length := by
    rw [permIndex_eq, permInsts]
    have hik : i.val < (List.finRange S.k).length := by rw [List.length_finRange]; exact i.isLt
    have hfi : (List.finRange S.k)[i.val] = i := by
      rw [List.getElem_finRange]
      rfl
    have hsplit := List.take_append_drop i.val (List.finRange S.k)
    rw [List.drop_eq_getElem_cons hik, hfi] at hsplit
    conv_rhs => rw [← hsplit]
    rw [List.filter_append, List.length_append, List.filter_cons_of_pos
      (p := fun i ↦ !(S.lookups i).isEmpty) (by
        simpa only [Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff] using hp),
      List.length_cons]
    omega
  have ht : permIndex S i < (permMats S proof zeta).length := hlen ▸ hrank
  have hti : (permInsts S)[permIndex S i]'hrank = i := by
    rw [← List.getD_eq_getElem _ i hrank]
    exact getD_permInsts S i hp i
  have := rows_eq_matColumn H S.params cache S.logTop I _ hok (by rw [hlb, hrh]; exact hbind)
    (by rw [hlb]; exact permLog_le S) (permWidths S) hws _ ht (S.logN i + S.params.logBlowup)
    (by rw [hget, hti]) (capHeight_le_logSize S i) j (by rw [hwd _ ht, hti]; exact hj)
  rw [← this, hlb, hrh]

end Permutation

/-! ### The run's challenges -/

section Challenges
variable [BaseField F] [Challenge F EF] (H : Primitives F Id) (S : Iop.Batch.Setup EF) [S.CapFits]
  (common : CompStark.Batch.Common F) (proof : CompStark.Batch.BatchProof F EF)
  (pis : List (List F))

/-- The challenger when FRI's commit loop starts, after FRI's domain separator. -/
noncomputable def friStartB : H.State :=
  obsList H (stateFriB H S.params S.instances common proof pis)
    (DomainSeparator.friSeed F EF S.friArities (2 ^ S.params.logFinalPolyLen)
      S.params.commitPowBits S.params.queryPowBits S.params.numQueries S.logTop
      S.params.logBlowup S.params.maxLogArity)

/-- The commit loop's replay: the folding challenges and the challenger after them. -/
noncomputable def commitReplayB : List EF × H.State :=
  commitReplay H S.params (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)
    (friStartB H S common proof pis)

/-- The challenger before the query grinding check: after the commit loop and the final
polynomial. -/
noncomputable def queryStateB : H.State :=
  obsExts H (commitReplayB H S common proof pis).2 proof.fri.finalPoly.toList

/-- The query grinding sample, after the witness; `0` without query grinding. -/
noncomputable def powSampleOfB : F :=
  if S.params.queryPowBits = 0 then 0
  else (H.sample (H.observe (queryStateB H S common proof pis) proof.fri.queryWitness)).1

/-- Query `j`'s sample, whose low bits are its index. -/
noncomputable def querySampleOfB (j : ℕ) : F :=
  (H.sample (sampleStates H (chkWit H S.params.queryPowBits proof.fri.queryWitness
    (queryStateB H S common proof pis)).2 j)).1

end Challenges

/-! ### The extracted transcript -/

/-- The permutation commitment's root, if the proof commits to permutation traces. -/
def permRoot (proof : CompStark.Batch.BatchProof F EF) : Cap F :=
  proof.permutationCommit.getD #[]

/-- The batch IOP's transcript extracted from an accepted proof: every instance's trace,
permutation trace and quotient words and FRI's words from `cache`, the opened values, terminals
and final polynomial from the proof, and the challenges of the run on `H`. ArkLib folds at `s β`
where Plonky3 folds at `β`, `s` the shift of the folded domain. -/
noncomputable def extractB [BaseField F] [Challenge F EF] (S : Iop.Batch.Setup EF) [S.CapFits]
    (cache : Merkle.Cache F (Digest F)) (H : Primitives F Id) (common : CompStark.Batch.Common F)
    (proof : CompStark.Batch.BatchProof F EF) (pis : List (List F)) : Sound.Batch.Transcript S where
  trace i c x := Merkle.matColumnCap cache proof.mainCommit.toList S.params.capHeight S.logTop
    S.mainHeights S.mainWidths i c (S.logN i + S.params.logBlowup)
    (reverseBits x (S.logN i + S.params.logBlowup))
  lookupAlpha := Challenge.toSpec (lookupRunB H S.params S.instances common proof pis).1
  lookupBeta := Challenge.toSpec (lookupRunB H S.params S.instances common proof pis).2
  perm i c e x := Merkle.matColumnCap cache (permRoot proof).toList S.params.capHeight
    (permLog S) (permHeights S) (permWidths S) (permIndex S i) (c.val * Challenge.d EF + e.val)
    (S.logN i + S.params.logBlowup) (reverseBits x (S.logN i + S.params.logBlowup))
  terminal i := Challenge.toSpec ((proof.lookupTerminals.getD i none).getD 0)
  alpha := Challenge.toSpec (alphaOfB H S.params S.instances common proof pis)
  quotient i c e x := Merkle.matColumnCap cache proof.quotientCommit.toList S.params.capHeight
    S.logTop (quotHeights S) (quotWidths S) (quotOffset S i + c) e (S.logN i + S.params.logBlowup)
    (reverseBits x (S.logN i + S.params.logBlowup))
  zeta := Challenge.toSpec (zetaOfB H S.params S.instances common proof pis)
  openings i := openingsOf (S.instanceSetup i) (proof.opened.toList.getD i noOpenings)
    (proof.permutationLocal.getD i #[]) (proof.permutationNext.getD i #[])
  batch := Challenge.toSpec (batchOfB H S.params S.instances common proof pis)
  words j m z := if j < S.friArities.length then
      friWordAt cache (proof.fri.commits.toList.getD j #[]) S.params.capHeight m
        (S.friArities.getD j 0) z.val
    else 0
  finalPoly := finalPoly S.domainSetup proof.fri.finalPoly
  betas j := lift gen ^ 2 ^ (S.friArities.take j).sum *
    Challenge.toSpec ((commitReplayB H S common proof pis).1.getD j 0)

/-! ### BCS consistency -/

section Bcs
variable [BaseField F] [Challenge F EF]

theorem shiftRight_lt {I L : ℕ} (hI : I < 2 ^ L) (m : ℕ) (hm : m ≤ L) : I >>> (L - m) < 2 ^ m := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
    Nat.add_sub_cancel' hm]
  exact hI

/-- The point of a query at a height is the extracted words' point of its row there. -/
theorem reverseBits_instPoint (S : Iop.Batch.Setup EF) [S.CapFits] (I : ℕ) (hI : I < 2 ^ S.logTop)
    (i : Fin S.k) :
    reverseBits (instPoint S S.logTop I i).val (S.logN i + S.params.logBlowup) =
      I >>> (S.logTop - (S.logN i + S.params.logBlowup)) := by
  have hlt := shiftRight_lt hI _ (logTop_ge S i)
  rw [instPoint, finMod_val (reverseBits_lt _ _), reverseBits_reverseBits hlt]

/-- An instance's opened values and public values are those the verifier checks. -/
theorem mem_zip_check (S : Iop.Batch.Setup EF) [S.CapFits] (os : List (OpenedValues EF))
    (hos : os.length = S.k) (publicValues : Fin S.k → List F) (i : Fin S.k) :
    (((⟨S.air i, S.logN i, S.lookups i⟩ : CompStark.Batch.Instance F), i.val), os.getD i noOpenings,
      publicValues i) ∈ S.instances.zipIdx.zip (os.zip (List.ofFn publicValues)) := by
  have hl : i.val < (S.instances.zipIdx.zip (os.zip (List.ofFn publicValues))).length := by
    rw [List.length_zip, List.length_zip, List.length_zipIdx, length_instances, hos,
      List.length_ofFn]
    simp only [Nat.min_self]
    exact i.isLt
  have := List.getElem_mem hl
  rw [List.getElem_zip, List.getElem_zip, List.getElem_zipIdx] at this
  simp only [Iop.Batch.Setup.instances, List.getElem_ofFn, Nat.zero_add] at this
  rw [List.getD_eq_getElem _ _ (by rw [hos]; exact i.isLt)]
  exact this

/-- The terminals of an accepted proof: the instances with lookups' sum to the verifier's sum of
the proof's terminals. -/
theorem sum_terminals_toSpec (S : Iop.Batch.Setup EF) [S.CapFits] (ts : List (Option EF))
    (hlen : ts.length = S.k)
    (hsome : ∀ i : Fin S.k, (ts.getD i none).isSome = !(S.lookups i).isEmpty) :
    (∑ i with S.lookups i ≠ [], Challenge.toSpec ((ts.getD i none).getD 0)) =
      Challenge.toSpec ((ts.filterMap id).foldl (· + ·) 0) := by
  classical
  have hzero : ∀ i ∈ Finset.univ, ¬ (S.lookups i ≠ []) →
      Challenge.toSpec ((ts.getD i none).getD 0) = 0 := by
    intro i _ hi
    have h := hsome i
    rw [not_not.mp hi, List.isEmpty_nil, Bool.not_true] at h
    rcases hx : ts.getD i none with _ | y
    · rw [Option.getD_none, Challenge.toSpec_zero]
    · rw [hx, Option.isSome_some] at h
      exact absurd h (by decide)
  rw [Finset.sum_filter_of_ne fun i _ h ↦ by_contra fun hn ↦ h (hzero i (Finset.mem_univ _) hn)]
  have hgen : ∀ (l : List (Option EF)) (x : EF), Challenge.toSpec ((l.filterMap id).foldl
      (· + ·) x) = Challenge.toSpec x + (l.map fun o ↦ Challenge.toSpec (o.getD 0)).sum := by
    intro l
    induction l with
    | nil => intro x; simp only [List.filterMap_nil, List.foldl_nil, List.map_nil, List.sum_nil,
        add_zero]
    | cons o l ih =>
      intro x
      cases o with
      | none =>
        rw [List.filterMap_cons, show (id none : Option EF) = none from rfl]
        dsimp only
        rw [ih, List.map_cons, List.sum_cons, Option.getD_none, Challenge.toSpec_zero, zero_add]
      | some y =>
        rw [List.filterMap_cons, show (id (some y) : Option EF) = some y from rfl]
        dsimp only
        rw [List.foldl_cons, ih, Challenge.toSpec_add, List.map_cons, List.sum_cons,
          Option.getD_some, add_assoc]
  rw [hgen, Challenge.toSpec_zero, zero_add, Fin.sum_univ_def]
  congr 1
  refine List.ext_getElem (by rw [List.length_map, List.length_map, List.length_finRange, hlen])
    fun j h1 h2 ↦ ?_
  have hj : j < S.k := by simpa only [List.length_map, List.length_finRange] using h1
  rw [List.getElem_map, List.getElem_map, List.getElem_finRange,
    List.getD_eq_getElem _ _ (by rw [hlen]; exact hj)]
  rfl

/-- The permutation openings' and terminals' shapes of a proof whose lookup checks pass: `d`
coordinates per permutation column at both points, and a terminal exactly for the instances with
lookups. -/
theorem permShapes (S : Iop.Batch.Setup EF) [S.CapFits] (proof : CompStark.Batch.BatchProof F EF)
    (hlsize : proof.permutationLocal.size = S.k) (hnsize : proof.permutationNext.size = S.k)
    (htsize : proof.lookupTerminals.size = S.k)
    (hpshapes : ∀ x ∈ S.instances.zip (proof.permutationLocal.toList.zip
      (proof.permutationNext.toList.zip proof.lookupTerminals.toList)),
        CompStark.Batch.permutationShapeOk x.1 x.2.1 x.2.2.1 x.2.2.2 = true) (i : Fin S.k) :
    (proof.permutationLocal.getD i #[]).size = Challenge.d EF * (S.instanceSetup i).permWidth ∧
      (proof.permutationNext.getD i #[]).size = Challenge.d EF * (S.instanceSetup i).permWidth ∧
      (proof.lookupTerminals.getD i none).isSome = !(S.lookups i).isEmpty := by
  have hpsh : ∀ i : Fin S.k, CompStark.Batch.permutationShapeOk ⟨S.air i, S.logN i, S.lookups i⟩
      (proof.permutationLocal.getD i #[]) (proof.permutationNext.getD i #[])
      (proof.lookupTerminals.getD i none) = true := by
    intro i
    have hz : (proof.permutationLocal.toList.zip (proof.permutationNext.toList.zip
        proof.lookupTerminals.toList)).length = S.k := by
      simp only [List.length_zip, Array.length_toList, hlsize, hnsize, htsize, Nat.min_self]
    have hm := hpshapes _ (by
      rw [zip_instances_getD S _ hz (#[], #[], none)]
      exact List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩)
    have hget : (proof.permutationLocal.toList.zip (proof.permutationNext.toList.zip
        proof.lookupTerminals.toList)).getD i (#[], #[], none) = (proof.permutationLocal.getD i #[],
          proof.permutationNext.getD i #[], proof.lookupTerminals.getD i none) := by
      rw [List.getD_eq_getElem _ _ (by rw [hz]; exact i.isLt)]
      simp only [List.getElem_zip, Array.getElem_toList, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem (show i.val < proof.permutationLocal.size by
          rw [hlsize]; exact i.isLt),
        Array.getElem?_eq_getElem (show i.val < proof.permutationNext.size by
          rw [hnsize]; exact i.isLt),
        Array.getElem?_eq_getElem (show i.val < proof.lookupTerminals.size by
          rw [htsize]; exact i.isLt), Option.getD_some]
    rw [hget] at hm
    exact hm
  have h := hpsh i
  simp only [CompStark.Batch.permutationShapeOk, Bool.and_eq_true, beq_iff_eq] at h
  have hw : (if (S.lookups i).isEmpty then 0 else ((S.lookups i).length + 1) *
      Challenge.d EF) = Challenge.d EF * (S.instanceSetup i).permWidth := by
    rw [permWidth_eq]
    cases (S.lookups i).isEmpty <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_mul, Nat.mul_comm]
  exact ⟨h.1.1.trans hw, h.1.2.trans hw, h.2⟩

/-- **BCS consistency of the batch STARK.** If the batch verifier on pure primitives `H` accepts
a proof whose commitments bind the rows extracted from `cache`, and under whose preprocessed
commitment `cache` holds the preprocessed traces' extensions, the extracted transcript passes the
deterministic checks of `Sound.Batch.exists_satisfied_of_safe`, with the run's grinding and query
samples. -/
theorem bcsB (S : Iop.Batch.Setup EF) [S.CapFits] (cache : Merkle.Cache F (Digest F)) (H : Primitives F Id)
    (common : CompStark.Batch.Common F) (proof : CompStark.Batch.BatchProof F EF)
    (publicValues : Fin S.k → List F)
    (hmain : CapBindingM cache H proof.mainCommit S.params.capHeight S.logTop S.mainHeights)
    (hquot : CapBindingM cache H proof.quotientCommit S.params.capHeight S.logTop (quotHeights S))
    (hfri : ∀ c ∈ proof.fri.commits, CapBinding cache H c)
    (hprepBind : ∀ root ∈ common.preprocessed,
      CapBindingM cache H root S.params.capHeight (prepLog S) (prepHeights S))
    (hprep : ∀ root ∈ common.preprocessed, ∀ i : Fin S.k, 0 < (S.air i).preprocessedWidth →
      ∀ j < (S.air i).preprocessedWidth, ∀ r < 2 ^ (S.logN i + S.params.logBlowup),
        Merkle.matColumnCap cache root.toList S.params.capHeight (prepLog S) (prepHeights S)
          (prepWidths S) (prepIndex S i) j (S.logN i + S.params.logBlowup) r =
        (S.instanceSetup i).preprocessedWord j
          (finMod _ (reverseBits r (S.logN i + S.params.logBlowup))))
    (hpermBind : ∀ root ∈ proof.permutationCommit,
      CapBindingM cache H root S.params.capHeight (permLog S) (permHeights S))
    (h : CompStark.Batch.verifyInstancesWith H S.params S.instances common proof
      (List.ofFn publicValues) = .ok ()) :
    let t := extractB S cache H common proof (List.ofFn publicValues)
    (∑ i with S.lookups i ≠ [], t.terminal i) = 0 ∧
    (∀ i, ConstraintsHoldAt (S.instanceSetup i) (publicValues i) t.alpha t.zeta (t.openings i)
      (S.challenges t.lookupAlpha t.lookupBeta i) (t.terminal i)) ∧
      t.finalPoly.natDegree < 2 ^ S.params.logFinalPolyLen ∧
      CompPoly.CanonicalNat.toNat (powSampleOfB H S common proof (List.ofFn publicValues)) %
        2 ^ S.params.queryPowBits = 0 ∧
      ∀ j : Fin S.params.numQueries, queryPoint S.domainSetup
        (querySampleOfB H S common proof (List.ofFn publicValues) j) ∈ t.consistentQueries := by
  intro t
  set pis := List.ofFn publicValues with hpis
  obtain ⟨hsize, -, hlsize, hnsize, htsize, -, -, hshapeZ, hprepS, hlk, -, -, -, -,
    ⟨st, hfriOk⟩, hcheck, hsum⟩ :=
    verifyInstancesWith_ok H S.params S.instances common proof pis h
  obtain ⟨hpshapes, hperm, -⟩ := lookupShapeOk_spec S.params S.instances proof hlk
  have hos : proof.opened.toList.length = S.k := by
    rw [Array.length_toList, hsize, length_instances]
  rw [length_instances] at hsize hlsize hnsize htsize
  have hshape : ∀ i : Fin S.k, CompStark.Batch.openedShapeOk ⟨S.air i, S.logN i, S.lookups i⟩
      (proof.opened.toList.getD i noOpenings) = true := by
    intro i
    have hm := hshapeZ _ (zip_instances S _ hos ▸ List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩)
    exact hm
  have hsh := fun i ↦ openedShapeOk_spec (hshape i)
  have hpw := permShapes S proof hlsize hnsize htsize hpshapes
  set zeta := zetaOfB H S.params S.instances common proof pis with hzeta
  have hD := descHeights_batchRounds S common proof zeta (by rw [hsize])
  have hok := verifyFri_okR H S.params proof.fri _ _ _ _ hfriOk
  dsimp only at hok
  rw [hD, List.headD_cons] at hok
  obtain ⟨-, -, -, hK, hfolds, hcs, -, hfp, hw, hcrlen, hq⟩ := hok
  refine ⟨?_, fun i ↦ ?_, ?_, ?_, fun j ↦ ?_⟩
  · show (∑ i with S.lookups i ≠ [],
      Challenge.toSpec ((proof.lookupTerminals.getD i none).getD 0)) = 0
    have h1 := sum_terminals_toSpec S proof.lookupTerminals.toList
      (by rw [Array.length_toList, htsize]) fun i ↦ by
        rw [show proof.lookupTerminals.toList.getD i none = proof.lookupTerminals.getD i none by
          rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]]
        exact (hpw i).2.2
    simp only [show ∀ i : Fin S.k, proof.lookupTerminals.toList.getD i none =
      proof.lookupTerminals.getD i none from fun i ↦ by
        rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]]
      at h1
    rw [h1, hsum, Challenge.toSpec_zero]
  · have hc := hcheck _ (mem_zip_check S _ hos publicValues i)
    have hci := constraintsHoldAt_of_instanceCheck S i (publicValues i) _ _ _ _ _ _ _
      ((hsh i).2.2.1.trans (congrArg (2 ^ ·) (logChunks_eq S i).symm)) (hpw i).1 (hpw i).2.1 hc
    rw [challenges_eq] at hci
    exact hci
  · show (finalPoly S.domainSetup proof.fri.finalPoly).natDegree < _
    refine natDegree_lt_of_degree ?_ (Nat.two_pow_pos _)
    rw [← hfp]
    exact degree_sum_C_mul_X_pow_lt _ _
  · unfold powSampleOfB
    split
    · rename_i h0
      rw [h0, pow_zero, Nat.mod_one]
    · rename_i h0
      simp only [chkWit, h0, ↓reduceIte, beq_iff_eq] at hw
      exact hw
  set rounds := CompStark.Batch.batchRounds S.instances common proof zeta with hrounds
  set alpha := batchOfB H S.params S.instances common proof pis with halpha
  set index := (smpBits H S.logTop (sampleStates H (chkWit H S.params.queryPowBits
    proof.fri.queryWitness (queryStateB H S common proof pis)).2 j.val)).1 with hindex
  have hqj : QueryOkR H S.params S.logTop alpha rounds (commitReplayB H S common proof pis).1
      proof.fri.commits.toList S.friArities proof.fri.folds.toList proof.fri.inputs.toList
      proof.fri.finalPoly j index := hq j.val j.isLt
  have hidx : index < 2 ^ S.logTop := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hpt : queryPoint S.domainSetup (querySampleOfB H S common proof pis j) =
      finMod S.logTop (reverseBits index S.logTop) := by
    apply Fin.ext
    simp only [queryPoint, finMod, Nat.mod_eq_of_lt (reverseBits_lt _ _), hindex, smpBits,
      querySampleOfB]
  unfold QueryOkR at hqj
  dsimp only at hqj
  rw [hD, List.tail_cons] at hqj
  obtain ⟨hrl, hbok, hsteps, hfin, hnil, hfinal⟩ := hqj
  set rows := proof.fri.inputs.toList.map fun b ↦ (b.values.getD j.val #[]).toList with hrows
  obtain ⟨rM, rQ, rP, rR, hrs⟩ : ∃ rM rQ rP rR, rows = [rM, rQ] ++
      (match common.preprocessed with | some _ => [rP] | none => []) ++
      (match proof.permutationCommit with | some _ => [rR] | none => []) := by
    have hl := hrl
    rw [hrounds, batchRounds_cases, prepRounds, permRounds] at hl
    cases hc : common.preprocessed with
    | none =>
      cases hp : proof.permutationCommit with
      | none =>
        simp only [hc, hp, List.append_nil, List.length_cons, List.length_nil] at hl
        exact ⟨_, _, [], [], List.eq_getElem_of_length_eq_two rows hl⟩
      | some r =>
        simp only [hc, hp, List.append_nil, List.cons_append, List.nil_append, List.length_cons,
          List.length_nil] at hl
        exact ⟨_, _, [], _, List.eq_getElem_of_length_eq_three rows hl⟩
    | some root =>
      cases hp : proof.permutationCommit with
      | none =>
        simp only [hc, hp, List.append_nil, List.cons_append, List.nil_append, List.length_cons,
          List.length_nil] at hl
        exact ⟨_, _, _, [], List.eq_getElem_of_length_eq_three rows hl⟩
      | some r =>
        simp only [hc, hp, List.cons_append, List.nil_append, List.length_cons,
          List.length_nil] at hl
        obtain ⟨a, b, c, d, hr⟩ : ∃ a b c d, rows = [a, b, c, d] := by
          match rows, hl with
          | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
        exact ⟨a, b, c, d, hr⟩
  have hzip : rows.zip rounds = [(rM, proof.mainCommit, mainMats S proof zeta),
      (rQ, proof.quotientCommit, quotMats S proof zeta)] ++
      (match common.preprocessed with | some _ => [rP] | none => []).zip
        (prepRounds S proof zeta common) ++
      (match proof.permutationCommit with | some _ => [rR] | none => []).zip
        (permRounds S proof zeta) := by
    rw [hrs, hrounds, batchRounds_cases, List.zip_append (by
      rw [prepRounds]; cases common.preprocessed <;> rfl),
      List.zip_append (by simp only [List.length_cons, List.length_nil])]
    rfl
  have hbM : BatchOkR H S.params S.logTop index (rM, proof.mainCommit, mainMats S proof zeta) :=
    hbok _ (by rw [hzip]; exact List.mem_append_left _ (List.mem_append_left _
      List.mem_cons_self))
  have hbQ : BatchOkR H S.params S.logTop index (rQ, proof.quotientCommit, quotMats S proof zeta) :=
    hbok _ (by rw [hzip]; exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hbP : ∀ root, common.preprocessed = some root →
      BatchOkR H S.params S.logTop index (rP, root, prepMats S proof zeta) := by
    intro root hc
    refine hbok _ ?_
    rw [hzip]
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    simp only [prepRounds, hc, List.zip_cons_cons, List.zip_nil_left, List.mem_singleton]
  have hbR : ∀ root, proof.permutationCommit = some root →
      BatchOkR H S.params S.logTop index (rR, root, permMats S proof zeta) := by
    intro root hc
    refine hbok _ ?_
    rw [hzip]
    refine List.mem_append_right _ ?_
    simp only [permRounds, hc, List.zip_cons_cons, List.zip_nil_left, List.mem_singleton]
  have hdeep : ∀ m, Challenge.toSpec (reducedAt S.params S.logTop index alpha
      (queryMats (rows.zip rounds)) m).2 =
        t.deepWords m (finMod m (reverseBits (index >>> (S.logTop - m)) m)) := by
    intro m
    rw [hrs, hrounds]
    refine reducedAt_eq_groupDeepWord S t.prover t.lookupAlpha t.lookupBeta t.alpha t.zeta proof
      zeta S.logTop index m rfl (fun i ↦ rfl) hsize hshape hlsize hnsize
      (fun i ↦ ⟨(hpw i).1, (hpw i).2.1⟩) common hprepS hperm rM rQ rP rR (fun x hx ↦ ?_)
      (fun i j hj ↦ ?_) (fun i c e he ↦ ?_) (fun i hp j hj ↦ ?_) (fun i hl c hcw e he ↦ ?_) alpha
    · have hx' : x ∈ rows.zip rounds := by rw [hrs, hrounds]; exact hx
      obtain ⟨-, -, -, h3, h4⟩ := hbok x hx'
      exact ⟨h3, h4⟩
    · rw [main_rows H S cache proof zeta hsize (fun i ↦ (hsh i).1) index rM hbM hmain i j hj]
      show _ = Merkle.matColumnCap cache proof.mainCommit.toList S.params.capHeight S.logTop
        S.mainHeights S.mainWidths i j _ (reverseBits (instPoint S S.logTop index i).val _)
      rw [reverseBits_instPoint S index hidx i]
    · rw [quot_rows H S cache proof zeta hsize (fun i ↦ ⟨(hsh i).2.2.1.trans
        (congrArg (2 ^ ·) (logChunks_eq S i).symm), (hsh i).2.2.2.1⟩) index rQ hbQ hquot i c e he]
      show _ = Merkle.matColumnCap cache proof.quotientCommit.toList S.params.capHeight S.logTop
        (quotHeights S) (quotWidths S) _ e _ (reverseBits (instPoint S S.logTop index i).val _)
      rw [reverseBits_instPoint S index hidx i]
    · cases hc : common.preprocessed with
      | none =>
        rw [hc] at hprepS
        have hany : S.instances.any (0 < ·.air.preprocessedWidth) = true :=
          List.any_eq_true.mpr ⟨⟨S.air i, S.logN i, S.lookups i⟩, List.mem_ofFn.mpr ⟨i, rfl⟩,
            decide_eq_true hp⟩
        rw [hany] at hprepS
        exact absurd hprepS Bool.false_ne_true
      | some root =>
        rw [prep_rows H S cache proof zeta hsize (fun i ↦ (hsh i).2.2.2.2.1) index root rP
          (hbP root hc) (hprepBind root hc) i hp j hj,
          hprep root hc i hp j hj _ (shiftRight_lt hidx _ (logTop_ge S i))]
        rfl
    · cases hc : proof.permutationCommit with
      | none =>
        rw [hc, Option.isSome_none] at hperm
        have hany : CompStark.Batch.hasLookups S.instances = true :=
          List.any_eq_true.mpr ⟨⟨S.air i, S.logN i, S.lookups i⟩, List.mem_ofFn.mpr ⟨i, rfl⟩, by
            rw [← lookups_eq]
            simpa only [Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff]
              using hl⟩
        rw [hany] at hperm
        exact absurd hperm Bool.false_ne_true
      | some root =>
        have hj : c * Challenge.d EF + e < Challenge.d EF * (S.instanceSetup i).permWidth := by
          rw [Nat.mul_comm (Challenge.d EF)]
          calc c * Challenge.d EF + e < c * Challenge.d EF + Challenge.d EF := by omega
            _ = (c + 1) * Challenge.d EF := (Nat.succ_mul _ _).symm
            _ ≤ _ := Nat.mul_le_mul_right _ hcw
        rw [perm_rows H S cache proof zeta hlsize hnsize (fun i ↦ (hpw i).1) index root rR
          (hbR root hc) (hpermBind root hc) i hl _ hj]
        show _ = Merkle.matColumnCap cache (permRoot proof).toList S.params.capHeight (permLog S)
          (permHeights S) (permWidths S) (permIndex S i) (c * Challenge.d EF + e) _
          (reverseBits (instPoint S S.logTop index i).val _)
        rw [reverseBits_instPoint S index hidx i, permRoot, hc, Option.getD_some]
  set cr := commitReplayB H S common proof pis with hcr
  set l := cr.1.zip (querySteps j.val S.friArities proof.fri.folds.toList) with hl
  set ro := S.friHeights.map fun h ↦
    (h, (reducedAt S.params S.logTop index alpha (queryMats (rows.zip rounds)) h).2) with hro
  set e0 := (reducedAt S.params S.logTop index alpha (queryMats (rows.zip rounds)) S.logTop).2
    with he0
  have hfl : proof.fri.folds.toList.length = S.friArities.length := by
    rw [Array.length_toList, hfolds]
    rfl
  have hqs := length_querySteps j.val S.friArities _ hfl
  have hlar : l.map (·.2.logArity) = S.friArities := by
    show List.map ((fun x : QueryFold EF ↦ x.logArity) ∘ Prod.snd) _ = _
    rw [← List.map_map, List.map_snd_zip (by rw [hqs]; exact hcrlen.ge),
      map_logArity_querySteps _ _ _ hfl]
  have hll : l.length = S.friArities.length := by rw [← hlar, List.length_map]
  have hsum : S.friArities.sum ≤ S.logTop := by
    have := sum_foldSchedule_le S.params.maxLogArity (S.params.logBlowup + S.params.logFinalPolyLen)
      S.logTop (S.logTop :: S.friHeights)
    rw [List.headD_cons] at this
    exact this
  have hpre : ∀ j', ((l.take j').map (·.2.logArity)).sum = (S.friArities.take j').sum := by
    intro j'
    rw [List.map_take, hlar]
  have hpre_le : ∀ j', (S.friArities.take j').sum ≤ S.logTop := fun j' ↦ by
    have := List.sum_take_add_sum_drop S.friArities j'
    omega
  have hI0 : index >>> (S.logTop - S.logTop) = index := by
    rw [Nat.sub_self, Nat.shiftRight_zero]
  have hω : ∀ x : Fin (2 ^ S.logTop), S.domainSetup.domain x =
      (lift gen : 𝕂) ^ 2 ^ (S.logTop - S.logTop) * lift (twoAdicGen S.logTop ^ x.val) := by
    intro x
    rw [Nat.sub_self, pow_zero, pow_one, lift_pow]
    exact cosetDomain_apply _ _ x
  have hrom : ro.map (·.1) = S.friHeights := by
    simp only [hro, List.map_map, Function.comp_def, List.map_id']
  have hW : ∀ hv ∈ ro, hv.1 ≤ S.logTop ∧ (lift gen : 𝕂) ^ 2 ^ (S.logTop - hv.1) *
      Sound.Batch.injected S t.deepWords hv.1
        (finMod hv.1 (reverseBits (index >>> (S.logTop - hv.1)) hv.1)) =
      Challenge.toSpec hv.2 := by
    intro hv hmem
    rw [hro] at hmem
    obtain ⟨h', hh, rfl⟩ := List.mem_map.mp hmem
    refine ⟨((fits_friHeights S).2 h' hh).2.le, ?_⟩
    rw [Sound.Batch.injected, Sound.Batch.foldShift, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ lift_gen_ne_zero), one_mul]
    exact (hdeep h').symm
  have hsched : l.map (·.2.logArity) = foldSchedule S.params.maxLogArity
      (S.params.logFinalPolyLen + S.params.logBlowup) S.logTop (S.logTop :: S.friHeights) := by
    rw [hlar, Iop.Batch.Setup.friArities, Nat.add_comm S.params.logFinalPolyLen]
  have hbind : ∀ j' < l.length, CapBinding cache H (proof.fri.commits.toList.getD j' #[]) := by
    intro j' hj'
    have hlt : j' < proof.fri.commits.toList.length := by
      rw [Array.length_toList, hcs]
      exact hll ▸ hj'
    rw [List.getD_eq_getElem _ _ hlt]
    exact hfri _ (Array.mem_toList_iff.mp (List.getElem_mem hlt))
  have hfw : ∀ j' (hj' : j' < l.length), t.words j' = fun m z ↦
      friWordAt cache (proof.fri.commits.toList.getD j' #[]) S.params.capHeight m
        l[j'].2.logArity z.val := by
    intro j' hj'
    have hget : l[j'].2.logArity = S.friArities.getD j' 0 := by
      have := congrArg (fun L : List ℕ ↦ L.getD j' 0) hlar
      rw [List.getD_eq_getElem (l.map (·.2.logArity)) 0 (by rw [List.length_map]; exact hj'),
        List.getElem_map] at this
      exact this
    funext m z
    show (if j' < S.friArities.length then friWordAt cache (proof.fri.commits.toList.getD j' #[])
      S.params.capHeight m (S.friArities.getD j' 0) z.val else 0) = _
    rw [ite_eq_left_of_eq_true _ _ (eq_true (hll ▸ hj')), hget]
  have hβ : ∀ j' (hj' : j' < l.length), t.betas j' = (lift gen : 𝕂) ^ 2 ^ (S.logTop -
      (foldStateR l (ro, e0, index >>> (S.logTop - S.logTop), S.logTop) j').2.2.2) *
        Challenge.toSpec l[j'].1 := by
    intro j' hj'
    rw [foldStateR_snd l ro e0 (index >>> (S.logTop - S.logTop)) S.logTop j']
    dsimp only
    rw [hpre j', Nat.sub_sub_self (hpre_le j')]
    have hj1 : j' < cr.1.length := lt_of_lt_of_le hj'
      (by rw [List.length_zip]; exact Nat.min_le_left _ _)
    show (lift gen : 𝕂) ^ 2 ^ (S.friArities.take j').sum * Challenge.toSpec (cr.1.getD j' 0) = _
    rw [List.getD_eq_getElem _ _ hj1, List.getElem_zip]
  have hfinal' : t.finalPoly.eval ((lift gen : 𝕂) ^ 2 ^ (S.logTop -
      (foldStateR l (ro, e0, index >>> (S.logTop - S.logTop), S.logTop) l.length).2.2.2) *
      lift (twoAdicGen (foldStateR l (ro, e0, index >>> (S.logTop - S.logTop), S.logTop)
        l.length).2.2.2 ^
        reverseBits (foldStateR l (ro, e0, index >>> (S.logTop - S.logTop), S.logTop)
          l.length).2.2.1
          (foldStateR l (ro, e0, index >>> (S.logTop - S.logTop), S.logTop) l.length).2.2.2)) =
      Challenge.toSpec (foldStateR l (ro, e0, index >>> (S.logTop - S.logTop), S.logTop)
        l.length).2.1 := by
    rw [hI0]
    have h2 := foldStateR_snd l ro e0 index S.logTop l.length
    rw [List.take_length, hlar] at h2
    have hidx' : (foldStateR l (ro, e0, index, S.logTop) l.length).2.2.1 <
        2 ^ (S.params.logBlowup + S.params.logFinalPolyLen) := by
      rw [← hfin, h2]
      dsimp only
      have := shiftRight_lt hidx (S.logTop - S.friArities.sum) (Nat.sub_le _ _)
      rwa [Nat.sub_sub_self hsum] at this
    rw [hfin]
    have hsub : S.logTop - (S.params.logBlowup + S.params.logFinalPolyLen) =
        S.domainSetup.logN - S.params.logFinalPolyLen := by
      have := S.folds S.top
      have hl : S.domainSetup.logN = S.logN S.top := rfl
      unfold Iop.Batch.Setup.logTop
      omega
    rw [hsub]
    show (finalPoly S.domainSetup proof.fri.finalPoly).eval _ = _
    rw [eval_finalPoly S.domainSetup _ _ hidx']
    exact congrArg Challenge.toSpec hfinal
  obtain ⟨hacc, hinit⟩ := query_run cache H S.params.capHeight S.logTop index hK
    S.params.maxLogArity (S.params.logFinalPolyLen + S.params.logBlowup)
    (2 ^ S.params.logFinalPolyLen) (Nat.two_pow_pos _) (Sound.Batch.injected S t.deepWords)
    t.finalPoly S.logTop S.logTop
    S.friHeights S.domainSetup.domain l proof.fri.commits.toList ro e0 t.words t.betas le_rfl hidx
    hω hrom hW hsched (by rw [hI0]; exact hsteps) hbind hfw hβ (by rw [hI0]; exact hnil) hfinal'
  rw [hI0] at hacc hinit
  rw [hpt]
  simp only [Sound.Batch.Transcript.consistentQueries, Finset.mem_filter]
  refine ⟨hacc, hinit.trans ?_⟩
  rw [he0, hdeep, Nat.sub_self, Nat.shiftRight_zero]

end Bcs

end CompStark.Ni
