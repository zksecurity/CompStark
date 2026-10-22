/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BatchBcs
public import CompStark.Ni.BatchNatural
public import CompStark.Ni.Setup

/-! # The batch setup in the random-oracle model

The game computes the batch's common data on the oracles (`Setup.setupRo`, Plonky3's setup on the
instances' preprocessed traces) and logs its queries with the prover's. Against an answer table:

* the setup is `commonWith` on the table's primitives (`evalWithAnswerFn_setupRoB`), whose tree is
  the mixed-height tree `Merkle.injNode` of the preprocessed traces' extensions
  (`injNodeWith_idealOf`);
* the preprocessed commitment is the digest of one of the setup's queries (`exists_prep_mem`), so
  a log that holds them binds it;
* a cache under whose commitment the honest openings bind holds the extensions: the columns read
  off it are the preprocessed words (`matColumn_setup`), since honest multi-openings of mixed
  heights verify (`Merkle.verifyMulti_prune_mixed`).
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.RandomOracle CompStark.Iop OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {K : Nat}

/-- The batch setup's nodes on an answer table are the mixed-height tree's nodes. -/
theorem injNodeWith_idealOf (g : (q : Query F) → Answer K q) (ms : List (Merkle.Matrix F))
    (k : Nat) : ∀ l i, CompStark.Batch.injNodeWith (idealOf g) ms k l i =
      Merkle.injNode (fun xs ↦ g (.leaf xs)) (fun a b ↦ g (.node a b)) ms k l i
  | 0, _ => rfl
  | l + 1, i => by
    rw [CompStark.Batch.injNodeWith, Merkle.injNode, ← injNodeWith_idealOf g ms k l (2 * i),
      ← injNodeWith_idealOf g ms k l (2 * i + 1)]
    rfl

theorem simulateQ_injNodeWith {n : Type → Type} [Monad n] [LawfulMonad n]
    (impl : QueryImpl (spec F K) n) (ms : List (Merkle.Matrix F)) (k l i : Nat) :
    simulateQ impl (CompStark.Batch.injNodeWith (ideal F K) ms k l i) =
      CompStark.Batch.injNodeWith (withAnswers K impl) ms k l i := by
  have h := CompStark.Batch.injNodeWith_map (simulateQ' impl) (ideal F K) ms k l i
  rw [withAnswers_map] at h
  simpa only [simulateQ'_apply, simulateQ_spec_query] using h

/-- The digest of a node computed on the oracles is the answer to one of its queries. -/
theorem exists_digest_injNode (answer : (q : Query F) → Answer K q)
    (ms : List (Merkle.Matrix F)) (k : Nat) :
    ∀ l i, ∃ e ∈ tableQueryLog (CompStark.Batch.injNodeWith (ideal F K) ms k l i) answer,
      digestOf e.1 e.2 = CompStark.Batch.injNodeWith (idealOf answer) ms k l i
  | 0, i => by
    refine ⟨⟨.leaf (Merkle.groupRows ms k i), answer (.leaf (Merkle.groupRows ms k i))⟩, ?_, rfl⟩
    show _ ∈ tableQueryLog (liftM ((spec F K).query (.leaf _))) answer
    rw [tableQueryLog_query]
    exact List.mem_singleton_self _
  | l + 1, i => by
    have hL : evalWithAnswerFn (QueryImpl.ofFn answer)
        (CompStark.Batch.injNodeWith (ideal F K) ms k l (2 * i)) =
        CompStark.Batch.injNodeWith (idealOf answer) ms k l (2 * i) :=
      simulateQ_injNodeWith (QueryImpl.ofFn answer) ms k l (2 * i)
    have hR : evalWithAnswerFn (QueryImpl.ofFn answer)
        (CompStark.Batch.injNodeWith (ideal F K) ms k l (2 * i + 1)) =
        CompStark.Batch.injNodeWith (idealOf answer) ms k l (2 * i + 1) :=
      simulateQ_injNodeWith (QueryImpl.ofFn answer) ms k l (2 * i + 1)
    set L := CompStark.Batch.injNodeWith (idealOf answer) ms k l (2 * i)
    set R := CompStark.Batch.injNodeWith (idealOf answer) ms k l (2 * i + 1)
    have hval : CompStark.Batch.injNodeWith (idealOf answer) ms k (l + 1) i =
        if ms.any (·.height == 2 ^ (k - (l + 1))) then
          answer (.node (answer (.node L R))
            (answer (.leaf (Merkle.groupRows ms (k - (l + 1)) i))))
        else answer (.node L R) := by
      rw [CompStark.Batch.injNodeWith]
      split <;> rfl
    rw [hval]
    simp only [CompStark.Batch.injNodeWith]
    rw [tableQueryLog_bind, tableQueryLog_bind, hL, hR, tableQueryLog_bind]
    simp only [evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply, tableQueryLog_query]
    split
    · refine ⟨⟨.node (answer (.node L R)) (answer (.leaf (Merkle.groupRows ms (k - (l + 1)) i))),
        answer (.node (answer (.node L R))
          (answer (.leaf (Merkle.groupRows ms (k - (l + 1)) i))))⟩, ?_, rfl⟩
      refine List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ ?_))
      rw [tableQueryLog_bind, tableQueryLog_query, evalWithAnswerFn_liftM_query,
        QueryImpl.ofFn_apply, tableQueryLog_query]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact ⟨⟨.node L R, answer (.node L R)⟩, List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ (List.mem_singleton_self _))), rfl⟩

/-- **The batch setup against an answer table** is the batch setup on `idealOf`. -/
theorem evalWithAnswerFn_setupRoB (S : Iop.Batch.Setup EF)
    (answer : (q : Query F) → Answer S.streamLen q) :
    evalWithAnswerFn (QueryImpl.ofFn answer) S.setupRo =
      CompStark.Batch.commonWith (idealOf answer) S.params S.instances :=
  evalWithAnswerFn_commonWith answer S.params S.instances

/-- The setup's preprocessed commitment is the digest of one of its queries. -/
theorem exists_prep_mem (S : Iop.Batch.Setup EF) (answer : (q : Query F) → Answer S.streamLen q)
    (root : Digest F)
    (h : (CompStark.Batch.commonWith (idealOf answer) S.params S.instances).preprocessed =
      some root) :
    ∃ e ∈ tableQueryLog S.setupRo answer, digestOf e.1 e.2 = root := by
  unfold Iop.Batch.Setup.setupRo CompStark.Batch.commonWith at *
  split at h
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  · rename_i hne
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨e, he, hd⟩ := exists_digest_injNode answer
      ((CompStark.Batch.preprocessedMats S.params S.instances).map Mat.toMatrix)
      (CompStark.Batch.preprocessedLogHeight S.params S.instances)
      (CompStark.Batch.preprocessedLogHeight S.params S.instances) 0
    rw [tableQueryLog_bind]
    refine ⟨e, List.mem_append_left _ he, hd.trans ?_⟩
    exact Option.some_injective _ h

/-- A row of a preprocessed trace's extension holds the preprocessed words at its point. -/
theorem lde_row {lookups : List (Lookup F)} (T : Iop.Setup EF lookups) (j : Nat)
    (hj : j < T.air.preprocessedWidth) (r : Nat)
    (hr : r < 2 ^ T.logSize) :
    ((preprocessedLde T.params T.air T.logN).toMatrix.row r).getD j 0 =
      T.preprocessedWord j (finMod T.logSize (reverseBits r T.logSize)) := by
  set ext := preprocessedLde T.params T.air T.logN
  obtain ⟨ps, hlde, hval⟩ := ldeRef_isLde T.logN T.params.logBlowup gen T.air.preprocessedWidth
    T.air.preprocessed T.valid.twoAdic BaseField.gen_ne_zero
  have hP := lde_eq_preprocessedPoly T ps hlde hval j hj
  have hjw : j < ext.toMatrix.width := hj
  have hlen : j < ((List.range ext.toMatrix.width).map fun j ↦
      ext.toMatrix.values.getD (r * ext.toMatrix.width + j) 0).length := by
    rw [List.length_map, List.length_range]; exact hjw
  rw [Merkle.Matrix.row, List.getD_eq_getElem _ _ hlen, List.getElem_map, List.getElem_range]
  have hcell : ext.values.getD (r * ext.width + j) 0 = _ :=
    hlde.2.2.2.2.2.2 r hr j (by rw [← hlde.1]; exact hj)
  show ext.values.getD (r * ext.width + j) 0 = _
  rw [hcell, hP, Iop.Setup.preprocessedWord, finMod_val (reverseBits_lt _ _)]
  rfl

theorem filterMap_ite {α β : Type} (p : α → Prop) [DecidablePred p] (h : α → β) :
    ∀ L : List α, L.filterMap (fun a ↦ if p a then none else some (h a)) =
      (L.filter fun a ↦ ¬ p a).map h
  | [] => rfl
  | a :: L => by
    by_cases hp : p a
    · rw [List.filterMap_cons, ite_eq_left hp, List.filter_cons_of_neg (by simpa using hp)]
      exact filterMap_ite p h L
    · rw [List.filterMap_cons, ite_eq_right hp, List.filter_cons_of_pos (by simpa using hp),
        List.map_cons, filterMap_ite p h L]

section Prep
variable (S : Iop.Batch.Setup EF)

theorem preprocessedMats_eq :
    (CompStark.Batch.preprocessedMats S.params S.instances).map Mat.toMatrix =
      (prepInsts S).map fun i ↦ (preprocessedLde S.params (S.air i) (S.logN i)).toMatrix := by
  rw [CompStark.Batch.preprocessedMats, Iop.Batch.Setup.instances, List.ofFn_eq_map,
    List.filterMap_map]
  simp only [Function.comp_def]
  rw [filterMap_ite (fun i : Fin S.k ↦ (S.air i).preprocessedWidth = 0)
    (fun i ↦ ldeRef (S.logN i) S.params.logBlowup gen (S.air i).preprocessedWidth
      (S.air i).preprocessed), List.map_map, prepInsts]
  congr 1
  refine List.filter_congr fun i _ ↦ ?_
  simp only [decide_not, Nat.pos_iff_ne_zero, ne_eq]

theorem preprocessedLogHeight_eq :
    CompStark.Batch.preprocessedLogHeight S.params S.instances = prepLog S := by
  rw [CompStark.Batch.preprocessedLogHeight, prepLog, Iop.Batch.Setup.instances,
    List.ofFn_eq_map, List.filter_map, List.map_map, prepInsts]
  rfl

end Prep

theorem prepIndex_lt (S : Iop.Batch.Setup EF) (i : Fin S.k)
    (hp : 0 < (S.air i).preprocessedWidth) : prepIndex S i < (prepInsts S).length := by
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

theorem le_prepLog (S : Iop.Batch.Setup EF) (i : Fin S.k) (hp : 0 < (S.air i).preprocessedWidth) :
    S.logN i + S.params.logBlowup ≤ prepLog S :=
  (le_foldl_max _ 0).2 _ (List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨List.mem_finRange _,
    decide_eq_true hp⟩, rfl⟩)

/-- **The preprocessed traces under a binding commitment.** If honest openings against the batch
setup's preprocessed commitment bind the rows of `cache`, the columns read off `cache` under it
are the preprocessed traces' words. -/
theorem matColumn_setup (S : Iop.Batch.Setup EF) (cache : Merkle.Cache F (Digest F))
    (g : (q : Query F) → Answer K q) (root : Digest F)
    (hroot : (CompStark.Batch.commonWith (idealOf g) S.params S.instances).preprocessed =
      some root)
    (hbind : BindingM cache (idealOf g) root (prepLog S) (prepHeights S)) (i : Fin S.k)
    (hp : 0 < (S.air i).preprocessedWidth) (j : ℕ) (hj : j < (S.air i).preprocessedWidth)
    (r : ℕ) (hr : r < 2 ^ (S.logN i + S.params.logBlowup)) :
    Merkle.matColumn cache root (prepLog S) (prepHeights S) (prepWidths S) (prepIndex S i) j
      (S.logN i + S.params.logBlowup) r =
      (S.instanceSetup i).preprocessedWord j
        (finMod _ (reverseBits r (S.logN i + S.params.logBlowup))) := by
  set hash : List F → Digest F := fun xs ↦ g (.leaf xs)
  set compress : Digest F → Digest F → Digest F := fun a b ↦ g (.node a b)
  set ms := (prepInsts S).map fun i ↦ (preprocessedLde S.params (S.air i) (S.logN i)).toMatrix
    with hms
  set k := prepLog S
  set m := S.logN i + S.params.logBlowup
  have hmk : m ≤ k := le_prepLog S i hp
  -- the commitment is the tree's root
  have hroot' : root = Merkle.injNode hash compress ms k k 0 := by
    unfold CompStark.Batch.commonWith at hroot
    split at hroot
    · exact absurd hroot (by simp only [reduceCtorEq, not_false_eq_true])
    · have := Option.some_injective _ hroot
      rw [← this, preprocessedMats_eq, preprocessedLogHeight_eq]
      exact injNodeWith_idealOf g ms k k 0
  have hheight : ∀ i' : Fin S.k, (preprocessedLde S.params (S.air i') (S.logN i')).toMatrix.height =
      2 ^ (S.logN i' + S.params.logBlowup) := fun i' ↦
    (shape_ldeRef (S.logN i') S.params.logBlowup gen (S.air i').preprocessedWidth
      (S.air i').preprocessed).2.1
  have hwidth : ∀ i' : Fin S.k, (preprocessedLde S.params (S.air i') (S.logN i')).toMatrix.width =
      (S.air i').preprocessedWidth := fun _ ↦ rfl
  have hhs : ms.map (·.height) = prepHeights S := by
    rw [hms, List.map_map, prepHeights]
    exact List.map_congr_left fun i' _ ↦ hheight i'
  have hpow : ∀ mt ∈ ms, ∃ l ≤ k, mt.height = 2 ^ l := by
    intro mt hmt
    obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hmt
    exact ⟨_, (le_foldl_max _ 0).2 _ (List.mem_map.mpr ⟨i', hi', rfl⟩), hheight i'⟩
  have htop : ∃ mt ∈ ms, mt.height = 2 ^ k := by
    rcases foldl_max_mem ((prepInsts S).map fun i ↦ S.logN i + S.params.logBlowup) 0 with h | h
    · have : k = 0 := h
      have := le_prepLog S i hp
      have := (S.valid i).blowup
      omega
    · obtain ⟨i', hi', he⟩ := List.mem_map.mp h
      exact ⟨_, List.mem_map.mpr ⟨i', hi', rfl⟩, by rw [hheight i']; exact congrArg (2 ^ ·) he⟩
  -- an honest opening at a top index above `r`
  set I := r * 2 ^ (k - m) with hI
  have hIk : I < 2 ^ k := by
    calc I < 2 ^ m * 2 ^ (k - m) := Nat.mul_lt_mul_of_pos_right hr (Nat.two_pow_pos _)
      _ = 2 ^ k := by rw [← Nat.pow_add, Nat.add_sub_cancel' hmk]
  have hIr : I >>> (k - m) = r := by
    rw [hI, Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  set paths := [(List.range k).map fun l ↦ Merkle.injNode hash compress ms k l ((I >>> l) ^^^ 1)]
  have hv := Merkle.verifyMulti_prune_mixed hash compress ms k hpow htop [I]
    (fun i' hi' ↦ by rw [List.mem_singleton.mp hi']; exact hIk) paths (fun q hq l hl ↦ by
      simp only [List.length_singleton, Nat.lt_one_iff] at hq
      subst hq
      simp only [paths, List.getD_cons_zero, List.getElem_singleton]
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hl),
        List.getElem_map, List.getElem_range])
  obtain ⟨path, hpath⟩ := Merkle.verifyBatch_of_verifyMulti_mixed hash compress _ k _ (by
      intro x hx
      obtain ⟨mt, hmt, rfl⟩ := List.mem_map.mp hx
      exact hpow mt hmt) (by
      obtain ⟨mt, hmt, he⟩ := htop
      exact ⟨_, List.mem_map.mpr ⟨mt, hmt, rfl⟩, he⟩) [I] _ _ hv 0 (by simp)
  rw [← hroot'] at hpath
  simp only [List.map_map, List.getElem_singleton, List.map_cons, List.map_nil,
    List.getD_cons_zero] at hpath
  have hhs' : List.map ((fun x : ℕ × ℕ ↦ x.1) ∘ fun mt : Merkle.Matrix F ↦ (mt.height, mt.width))
      ms = prepHeights S := by rw [← hhs]; rfl
  rw [hhs'] at hpath
  set values := List.map (fun mt : Merkle.Matrix F ↦ mt.row (I >>> (k - mt.height.log2))) ms
  have hlenP : (prepHeights S).length = (prepInsts S).length := by
    rw [prepHeights, List.length_map]
  have hrank := prepIndex_lt S i hp
  have hti : (prepInsts S)[prepIndex S i]'hrank = i := by
    rw [← List.getD_eq_getElem _ i hrank]
    exact getD_prepInsts S i hp i
  have hval : ∀ t (ht : t < (prepInsts S).length), values.getD t [] =
      (preprocessedLde S.params (S.air ((prepInsts S)[t])) (S.logN ((prepInsts S)[t]))).toMatrix.row
        (I >>> (k - (S.logN ((prepInsts S)[t]) + S.params.logBlowup))) := by
    intro t ht
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map, hms, List.length_map]; exact ht),
      List.getElem_map]
    simp only [hms, List.getElem_map, hheight, Nat.log2_two_pow]
  have hw : ∀ t < (prepHeights S).length, (values.getD t []).length = (prepWidths S).getD t 0 := by
    intro t ht
    rw [hlenP] at ht
    rw [hval t ht, Merkle.Matrix.row, List.length_map, List.length_range, hwidth, prepWidths,
      List.getD_eq_getElem _ _ (by rw [List.length_map]; exact ht), List.getElem_map]
  have htm : (prepHeights S).getD (prepIndex S i) 0 = 2 ^ m := by
    rw [prepHeights, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hrank),
      List.getElem_map, hti]
  have hjw : j < (prepWidths S).getD (prepIndex S i) 0 := by
    rw [prepWidths, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hrank),
      List.getElem_map, hti]
    exact hj
  have := matColumn_eq cache (idealOf g) root k (prepHeights S) (prepWidths S) hbind I values path
    hpath hw (prepIndex S i) m (hlenP ▸ hrank) htm j hjw
  rw [hIr] at this
  rw [this, hval _ hrank]
  simp only [hti]
  rw [show I >>> (k - (S.logN i + S.params.logBlowup)) = r from hIr]
  exact lde_row (S.instanceSetup i) j hj r hr
