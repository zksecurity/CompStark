/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Refines
public import CompStark.Plonky3.Batch

/-! # Batch provers on refining backends

A backend that refines the specification (`Fri.Refines`) proves what the specification proves for
batches too (`proveBatchWith_refines`): for instances whose traces are of their AIRs' shapes and
whose commitments are addressable side by side (`InputOk`), when the opening point `ζ` of the
specification's proof lies outside the base field. Every instance's quotient is
`uni-stark`'s (`quotientChunks_refines`), and the commitments of mixed heights are the backend's
(`CommitOk`).
-/

@[expose] public section
namespace CompStark.Batch
open CompStark.Fri CompStark.Stark

variable {F : Type} [BaseField F]

/-- What an instance commits to, in columns at its extended height: its trace, its preprocessed
trace and its quotient's chunks. -/
def Instance.columns (EF : Type) [Challenge F EF] (I : Instance F) : Nat :=
  I.air.width + I.air.preprocessedWidth + Challenge.d EF * 2 ^ I.air.logQuotientChunks I.logN

/-- The shapes the fast batch prover supports: at least one instance, every instance's trace of
its AIR's shape (`Stark.InputOk`), and the batch's extensions addressable side by side at the
extended height of some `2 ^ logH` rows at least every instance's. -/
structure InputOk (EF : Type) [Challenge F EF] (P : Params) (instances : List (Instance F))
    (traces : List (Array F)) : Prop where
  /-- At least one instance. -/
  nonempty : instances ≠ []
  /-- Every trace of its AIR's shape. -/
  traces : List.Forall₂ (fun I t ↦ Stark.InputOk EF P I.air I.logN t) instances traces
  /-- The extensions side by side are addressable. -/
  mem : ∃ logH, (∀ I ∈ instances, I.logN ≤ logH) ∧
    Addressable (2 ^ (logH + P.logBlowup) * (instances.map (·.columns EF)).sum)

theorem exists_of_forall₂ {α β : Type} {R : α → β → Prop} :
    ∀ {xs ys}, List.Forall₂ R xs ys → ∀ x ∈ xs, ∃ y, R x y
  | _ :: _, _ :: _, .cons h hs, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, h⟩
    · exact exists_of_forall₂ hs x hx

theorem forall₂_filterMap_id {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List (Option α)} {ys : List (Option β)}, List.Forall₂ (Option.Rel R) xs ys →
      List.Forall₂ R (xs.filterMap id) (ys.filterMap id)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons .none hs => by
    simp only [List.filterMap_cons, id]; exact forall₂_filterMap_id hs
  | _ :: _, _ :: _, .cons (.some hr) hs => by
    simp only [List.filterMap_cons, id]; exact .cons hr (forall₂_filterMap_id hs)

theorem forall₂_of_getElem {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (hl : l₁.length = l₂.length)
    (h : ∀ i (h₁ : i < l₁.length) (h₂ : i < l₂.length), R l₁[i] l₂[i]) : List.Forall₂ R l₁ l₂ :=
  List.forall₂_iff_get.mpr ⟨hl, fun i h₁ h₂ ↦ by simpa only [List.get_eq_getElem] using h i h₁ h₂⟩

theorem getElem_of_forall₂ {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) (i : Nat) (h₁ : i < l₁.length) (h₂ : i < l₂.length) :
    R l₁[i] l₂[i] := by
  simpa only [List.get_eq_getElem] using (List.forall₂_iff_get.mp h).2 i h₁ h₂

theorem foldl_width_sum {K : Type} (l : List (Mat K)) (a : Nat) :
    l.foldl (· + ·.width) a = a + (l.map Mat.width).sum := by
  induction l generalizing a with
  | nil => rfl
  | cons m l ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]; omega

theorem addressable_le {m n : Nat} (h : m ≤ n) (hn : Addressable n) : Addressable m := by
  unfold Addressable at *; omega

theorem tracePoints_outside {EF : Type} [Challenge F EF] {A : Air F} {logN : Nat}
    (hlog : logN ≤ twoAdicity F) {zeta : EF}
    (hz : Ext.OutsideBase zeta) :
    ∀ z ∈ tracePoints A zeta (zeta * Ext.ofBase (twoAdicGen logN)), Ext.OutsideBase z := by
  have hw := Ext.outsideBase_mul_ofBase hz (BaseField.twoAdicGen_ne_zero logN hlog)
  intro z hz'
  unfold tracePoints at hz'
  split at hz'
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz'
    rcases hz' with rfl | rfl
    · exact hz
    · exact hw
  · rw [List.mem_singleton.mp hz']; exact hz

theorem preprocessedPoints_outside {EF : Type} [Challenge F EF] {A : Air F} {logN : Nat}
    (hlog : logN ≤ twoAdicity F) {zeta : EF} (hz : Ext.OutsideBase zeta) :
    ∀ z ∈ preprocessedPoints A zeta (zeta * Ext.ofBase (twoAdicGen logN)), Ext.OutsideBase z := by
  have hw := Ext.outsideBase_mul_ofBase hz (BaseField.twoAdicGen_ne_zero logN hlog)
  intro z hz'
  unfold preprocessedPoints at hz'
  split at hz'
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz'
    rcases hz' with rfl | rfl
    · exact hz
    · exact hw
  · rw [List.mem_singleton.mp hz']; exact hz

variable [Poseidon2Field F] {EF : Type} [Challenge F EF] {B : Backend F EF 24}

/-- The preprocessed trace's extension of an instance, if it has preprocessed columns. -/
abbrev prepExt (B : Backend F EF 24) (P : Params) (I : Instance F) : Option B.M :=
  if I.air.preprocessedWidth = 0 then none
  else some (B.lde I.logN P.logBlowup gen I.air.preprocessedWidth I.air.preprocessed)

theorem sum_prep_widths (P : Params) : ∀ instances : List (Instance F),
    (((instances.map (prepExt (specBackend EF) P)).filterMap id).map Mat.width).sum ≤
      (instances.map (·.columns EF)).sum
  | [] => le_rfl
  | I :: is => by
    have ih : (((is.map (prepExt (specBackend EF) P)).filterMap fun x ↦ x).map Mat.width).sum ≤
        (is.map (·.columns EF)).sum := sum_prep_widths P is
    rw [List.map_cons, List.filterMap_cons, List.map_cons, List.sum_cons]
    by_cases hpw : I.air.preprocessedWidth = 0
    · simp only [prepExt, hpw, ↓reduceIte, id]
      exact le_trans ih (Nat.le_add_left _ _)
    · simp only [prepExt, hpw, ↓reduceIte, id, List.map_cons, List.sum_cons]
      have hw := (shape_ldeRef I.logN P.logBlowup gen I.air.preprocessedWidth I.air.preprocessed).1
      exact Nat.add_le_add (by rw [hw, Instance.columns]; omega) ih

/-- The preprocessed traces' extensions and commitment by a refining backend and by the
specification are related, and of the prover's shapes. -/
theorem setupBatchWith_refines (h : Refines B) {P : Params} {instances : List (Instance F)}
    {traces : List (Array F)} (hin : InputOk EF P instances traces) :
    List.Forall₂ (Option.Rel h.RM) (setupBatchWith B P instances).1
        (setupBatchWith (specBackend EF) P instances).1 ∧
      Option.Rel h.RC (setupBatchWith B P instances).2
        (setupBatchWith (specBackend EF) P instances).2 ∧
      List.Forall₂ (fun I (y : Option (Mat F)) ↦
          (∀ q ∈ y, MatOk q ∧ q.height = 2 ^ (I.logN + P.logBlowup)) ∧
            (y.map (·.width)).getD 0 = I.air.preprocessedWidth)
        instances (setupBatchWith (specBackend EF) P instances).1 := by
  obtain ⟨logH, hlogH, hmem⟩ := hin.mem
  have hI : ∀ I ∈ instances, ∃ t, Stark.InputOk EF P I.air I.logN t :=
    exists_of_forall₂ hin.traces
  have hrel : List.Forall₂ (Option.Rel h.RM) (instances.map (prepExt B P))
      (instances.map (prepExt (specBackend EF) P)) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun I hIm ↦ ?_
    obtain ⟨t, ht⟩ := hI I hIm
    unfold prepExt
    split
    · exact .none
    · exact .some (h.lde _ _ _ _ _ ht.preprocessed ht.twoAdic
        (addressable_le (Nat.mul_le_mul_left _ (by omega)) ht.mem))
  have hq : ∀ I ∈ instances, (∀ q ∈ prepExt (specBackend EF) P I,
      MatOk q ∧ q.height = 2 ^ (I.logN + P.logBlowup)) ∧
      ((prepExt (specBackend EF) P I).map (·.width)).getD 0 = I.air.preprocessedWidth := by
    intro I hIm
    obtain ⟨t, ht⟩ := hI I hIm
    obtain ⟨hew, heh, hev⟩ :=
      shape_ldeRef I.logN P.logBlowup gen I.air.preprocessedWidth I.air.preprocessed
    by_cases hpw : I.air.preprocessedWidth = 0
    · simp only [prepExt, hpw, ↓reduceIte]
      exact ⟨(fun q hq ↦ nomatch hq), rfl⟩
    · simp only [prepExt, hpw, ↓reduceIte]
      refine ⟨fun q hq ↦ ?_, hew⟩
      obtain rfl := Option.some_injective _ hq
      exact ⟨⟨by rw [hew]; omega, ⟨_, ht.twoAdic, heh⟩, by rw [hev, hew, heh],
        by rw [hew, heh, Nat.mul_comm]
           exact addressable_le (Nat.mul_le_mul_left _ (by omega)) ht.mem⟩, heh⟩
  refine ⟨hrel, ?_, List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr hq)⟩
  unfold setupBatchWith
  dsimp only
  have hf := forall₂_filterMap_id hrel
  have hiff : ∀ {a : List B.M} {b : List (Mat F)}, List.Forall₂ h.RM a b →
      a.isEmpty = b.isEmpty := by
    intro a b hab; cases hab <;> rfl
  simp only [hiff hf]
  split
  · exact .none
  · rename_i hne
    refine .some (h.commit hf ⟨2 ^ (logH + P.logBlowup), fun he ↦ hne (by rw [he]; rfl),
      fun q hqm ↦ ?_, ?_⟩)
    · obtain ⟨y, hy, hyq⟩ := List.mem_filterMap.mp hqm
      obtain ⟨I, hIm, rfl⟩ := List.mem_map.mp hy
      obtain ⟨hok, hh⟩ := (hq I hIm).1 q hyq
      exact ⟨hok, by
        rw [hh]; exact Nat.pow_le_pow_right (by decide) (by have := hlogH I hIm; omega)⟩
    · rw [foldl_width_sum, Nat.zero_add]
      exact addressable_le (Nat.mul_le_mul_left _ (sum_prep_widths P instances)) hmem

theorem sum_le_sum_map {α : Type} (l : List α) (f g : α → Nat) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact le_rfl
  | cons x l ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    exact Nat.add_le_add (h x List.mem_cons_self) (ih fun y hy ↦ h y (List.mem_cons_of_mem _ hy))

/-- The commitments and challenges of a batch by a refining backend and by the specification are
related, the specification's matrices of the prover's shapes. -/
theorem batchCommitAndSample_refines (h : Refines B) {P : Params}
    {instances : List (Instance F)} {traces : List (Array F)} {pis : List (List F)}
    (hin : InputOk EF P instances traces) (hpis : pis.length = instances.length) :
    RelM (fun x y ↦ List.Forall₂ h.RM x.1 y.1 ∧ h.RC x.2.1 y.2.1 ∧
        List.Forall₂ (List.Forall₂ h.RM) x.2.2.1 y.2.2.1 ∧ h.RC x.2.2.2.1 y.2.2.2.1 ∧
        x.2.2.2.2 = y.2.2.2.2 ∧ (∀ m ∈ y.1, MatOk m) ∧ ∀ c ∈ y.2.2.1, ∀ m ∈ c, MatOk m)
      (batchCommitAndSample B P instances (setupBatchWith B P instances) traces pis)
      (batchCommitAndSample (specBackend EF) P instances
        (setupBatchWith (specBackend EF) P instances) traces pis) := by
  obtain ⟨hprep, hprepC, hprepS⟩ := setupBatchWith_refines h hin
  obtain ⟨logH, hlogH, hmem⟩ := hin.mem
  have hne := hin.nonempty
  have htl := hin.traces.length_eq
  have hT : ∀ i (hi : i < instances.length) (ht : i < traces.length),
      Stark.InputOk EF P instances[i].air instances[i].logN traces[i] :=
    fun i hi ht ↦ getElem_of_forall₂ hin.traces i hi ht
  -- The main traces' extensions.
  have hext : List.Forall₂ h.RM
      ((instances.zip traces).map fun (I, t) ↦ B.lde I.logN P.logBlowup gen I.air.width t)
      ((instances.zip traces).map fun (I, t) ↦
        (specBackend EF).lde I.logN P.logBlowup gen I.air.width t) := by
    refine forall₂_of_getElem (by simp only [List.length_map]) fun i h1 h2 ↦ ?_
    simp only [List.length_map, List.length_zip] at h1
    have hI := hT i (by omega) (by omega)
    simp only [List.getElem_map, List.getElem_zip]
    exact h.lde _ _ _ _ _ hI.trace hI.twoAdic
      (addressable_le (Nat.mul_le_mul_left _ (by omega)) hI.mem)
  have hextOk : ∀ m ∈ (instances.zip traces).map (fun (I, t) ↦
      (specBackend EF).lde I.logN P.logBlowup gen I.air.width t), MatOk m ∧
        m.height ≤ 2 ^ (logH + P.logBlowup) := by
    intro m hm
    obtain ⟨⟨I, t⟩, hIt, rfl⟩ := List.mem_map.mp hm
    have hIm := (List.of_mem_zip hIt).1
    have hI : Stark.InputOk EF P I.air I.logN t := List.forall₂_iff_zip.mp hin.traces |>.2 hIt
    obtain ⟨hew, heh, hev⟩ := shape_ldeRef I.logN P.logBlowup gen I.air.width t
    exact ⟨⟨by rw [hew]; exact hI.width, ⟨_, hI.twoAdic, heh⟩, by rw [hev, hew, heh],
      by rw [hew, heh, Nat.mul_comm]
         exact addressable_le (Nat.mul_le_mul_left _ (by omega)) hI.mem⟩,
      by rw [heh]; exact Nat.pow_le_pow_right (by decide) (by have := hlogH I hIm; omega)⟩
  have hzl : (instances.zip traces).map (·.1) = instances := List.map_fst_zip (by omega)
  have hct := h.commit hext ⟨2 ^ (logH + P.logBlowup), by
      intro he
      rw [List.map_eq_nil_iff, List.zip_eq_nil_iff] at he
      rcases he with he | he
      · exact hne he
      · exact hne (List.length_eq_zero_iff.mp (by rw [htl, he]; rfl)),
    hextOk, by
      rw [foldl_width_sum, Nat.zero_add, List.map_map]
      refine addressable_le (Nat.mul_le_mul_left _ ?_) hmem
      calc _ ≤ ((instances.zip traces).map fun p ↦ p.1.columns EF).sum :=
            sum_le_sum_map _ _ _ fun ⟨I, t⟩ _ ↦ by
              simp only [Function.comp_apply, Instance.columns]
              rw [(shape_ldeRef I.logN P.logBlowup gen I.air.width t).1]
              omega
        _ = (instances.map (·.columns EF)).sum := by
            conv_rhs => rw [← hzl]
            rw [List.map_map]; rfl⟩
  -- The preprocessed commitment's root.
  have hroot : (setupBatchWith B P instances).2.map B.root =
      (setupBatchWith (specBackend EF) P instances).2.map (specBackend EF).root := by
    generalize (setupBatchWith B P instances).2 = cB at hprepC
    generalize (setupBatchWith (specBackend EF) P instances).2 = cS at hprepC
    cases hprepC with
    | none => rfl
    | some hr => exact congrArg some (h.root hr)
  have hroots : ((setupBatchWith B P instances).2.map fun c ↦ (B.root c).toList).getD [] =
      ((setupBatchWith (specBackend EF) P instances).2.map fun c ↦
        ((specBackend EF).root c).toList).getD [] := by
    generalize (setupBatchWith B P instances).2 = cB at hprepC
    generalize (setupBatchWith (specBackend EF) P instances).2 = cS at hprepC
    cases hprepC with
    | none => rfl
    | some hr => exact congrArg Vector.toList (h.root hr)
  unfold batchCommitAndSample
  dsimp only
  rw [hroot, h.root hct, hroots]
  refine RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦
    RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦ RelM.bind_eq fun alpha ↦ ?_
  -- Every instance's quotient chunks.
  generalize hPB : (setupBatchWith B P instances).1 = pB at hprep
  generalize hPS : (setupBatchWith (specBackend EF) P instances).1 = pS at hprep hprepS
  have hpBl : pB.length = instances.length := by
    rw [← hPB, setupBatchWith]; exact List.length_map _
  have hpSl : pS.length = instances.length := by rw [← hprepS.length_eq]
  have hq : ∀ i (hi : i < instances.length),
      List.Forall₂ h.RM (quotientChunks B P instances[i].air instances[i].logN
          (B.lde instances[i].logN P.logBlowup gen instances[i].air.width (traces[i]'(by omega)))
          (pB[i]'(by omega)) (pis[i]'(by omega)) alpha)
        (quotientChunks (specBackend EF) P instances[i].air instances[i].logN
          (ldeRef instances[i].logN P.logBlowup gen instances[i].air.width (traces[i]'(by omega)))
          (pS[i]'(by omega)) (pis[i]'(by omega)) alpha) ∧
      (∀ m ∈ quotientChunks (specBackend EF) P instances[i].air instances[i].logN
          (ldeRef instances[i].logN P.logBlowup gen instances[i].air.width (traces[i]'(by omega)))
          (pS[i]'(by omega)) (pis[i]'(by omega)) alpha,
        MatOk m ∧ m.height = 2 ^ (instances[i].logN + P.logBlowup) ∧
          m.width = Challenge.d EF) ∧
      (quotientChunks (specBackend EF) P instances[i].air instances[i].logN
          (ldeRef instances[i].logN P.logBlowup gen instances[i].air.width (traces[i]'(by omega)))
          (pS[i]'(by omega)) (pis[i]'(by omega)) alpha).length =
        2 ^ instances[i].air.logQuotientChunks instances[i].logN := by
    intro i hi
    have hI := hT i hi (by omega)
    have hS := getElem_of_forall₂ hprepS i hi (by omega)
    exact quotientChunks_refines h _ hI
      (h.lde _ _ _ _ _ hI.trace hI.twoAdic
        (addressable_le (Nat.mul_le_mul_left _ (by omega)) hI.mem))
      (getElem_of_forall₂ hprep i (by omega) (by omega)) hS.1 hS.2 alpha
  have hlenB : (((instances.zip ((instances.zip traces).map fun (I, t) ↦
      B.lde I.logN P.logBlowup gen I.air.width t)).zip (pB.zip pis)).map
        fun ((I, ext), (pext, p)) ↦ quotientChunks B P I.air I.logN ext pext p alpha).length =
      instances.length := by
    simp only [List.length_map, List.length_zip, hpBl, hpis, htl, Nat.min_self]
  have hlenS : (((instances.zip ((instances.zip traces).map fun (I, t) ↦
      (specBackend EF).lde I.logN P.logBlowup gen I.air.width t)).zip (pS.zip pis)).map
        fun ((I, ext), (pext, p)) ↦
          quotientChunks (specBackend EF) P I.air I.logN ext pext p alpha).length =
      instances.length := by
    simp only [List.length_map, List.length_zip, hpSl, hpis, htl, Nat.min_self]
  have hch := forall₂_of_getElem (R := List.Forall₂ h.RM) (by rw [hlenB, hlenS])
    fun i h1 h2 ↦ by
      have hi : i < instances.length := by rw [hlenB] at h1; exact h1
      simp only [List.getElem_map, List.getElem_zip]
      exact (hq i hi).1
  have hSmem : ∀ c ∈ ((instances.zip ((instances.zip traces).map fun (I, t) ↦
      (specBackend EF).lde I.logN P.logBlowup gen I.air.width t)).zip (pS.zip pis)).map
        (fun ((I, ext), (pext, p)) ↦
          quotientChunks (specBackend EF) P I.air I.logN ext pext p alpha), ∀ m ∈ c,
      MatOk m ∧ m.height ≤ 2 ^ (logH + P.logBlowup) ∧ m.width = Challenge.d EF := by
    intro c hc m hm
    obtain ⟨i, h1, rfl⟩ := List.getElem_of_mem hc
    have hi : i < instances.length := by rw [hlenS] at h1; exact h1
    simp only [List.getElem_map, List.getElem_zip] at hm
    obtain ⟨hok, hh, hw⟩ := (hq i hi).2.1 m hm
    exact ⟨hok, by
      rw [hh]
      exact Nat.pow_le_pow_right (by decide) (by have := hlogH _ (List.getElem_mem hi); omega),
      hw⟩
  have hsums : (((instances.zip ((instances.zip traces).map fun (I, t) ↦
      (specBackend EF).lde I.logN P.logBlowup gen I.air.width t)).zip (pS.zip pis)).map
        (fun ((I, ext), (pext, p)) ↦
          quotientChunks (specBackend EF) P I.air I.logN ext pext p alpha)).map
        (fun c ↦ (c.map Mat.width).sum) =
      instances.map fun I ↦ Challenge.d EF * 2 ^ I.air.logQuotientChunks I.logN := by
    refine List.ext_getElem (by rw [List.length_map, hlenS, List.length_map]) fun i h1 h2 ↦ ?_
    have hi : i < instances.length := by rw [List.length_map] at h2; exact h2
    rw [List.getElem_map, List.getElem_map]
    have hw := (hq i hi).2.1
    have hl := (hq i hi).2.2
    simp only [List.getElem_map, List.getElem_zip] at hw hl ⊢
    have e := foldl_width_sum (quotientChunks (specBackend EF) P instances[i].air
      instances[i].logN (ldeRef instances[i].logN P.logBlowup gen instances[i].air.width
        traces[i]) pS[i] pis[i] alpha) 0
    rw [Nat.zero_add] at e
    rw [← e, foldl_width_const _ _ fun m hm ↦ (hw m hm).2.2, hl, Nat.zero_add]
  have hqc := h.commit (List.rel_flatten hch) ⟨2 ^ (logH + P.logBlowup), by
      intro he
      rw [List.flatten_eq_nil_iff] at he
      have h0 : 0 < instances.length := List.length_pos_of_ne_nil hne
      have := he _ (List.getElem_mem (by rw [hlenS]; exact h0))
      have hl := (hq 0 h0).2.2
      simp only [List.getElem_map, List.getElem_zip] at this hl
      rw [this, List.length_nil] at hl
      exact absurd hl.symm (Nat.two_pow_pos _).ne',
    fun m hm ↦ by
      obtain ⟨c, hc, hm⟩ := List.mem_flatten.mp hm
      exact ⟨(hSmem c hc m hm).1, (hSmem c hc m hm).2.1⟩, by
      rw [foldl_width_sum, Nat.zero_add, List.map_flatten, List.sum_flatten, List.map_map]
      refine addressable_le (Nat.mul_le_mul_left _ ?_) hmem
      rw [show (List.sum ∘ List.map Mat.width) = fun c : List (Mat F) ↦ (c.map Mat.width).sum
        from rfl, hsums]
      exact sum_le_sum_map _ _ _ fun I _ ↦ by simp only [Instance.columns]; omega⟩
  rw [h.root hqc]
  dsimp only
  refine RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦ ?_
  exact RelM.pure ⟨hext, hct, hch, hqc, rfl, fun m hm ↦ (hextOk m hm).1,
    fun c hc m hm ↦ (hSmem c hc m hm).1⟩

theorem forall₂_zip_right {α β γ : Type} {R : β → γ → Prop} (l : List α) :
    ∀ {xs ys}, List.Forall₂ R xs ys →
      List.Forall₂ (fun a b ↦ a.1 = b.1 ∧ R a.2 b.2) (l.zip xs) (l.zip ys)
  | [], [], .nil => by simp only [List.zip_nil_right]; exact .nil
  | _ :: _, _ :: _, .cons h hs => by
    cases l with
    | nil => exact .nil
    | cons a l => exact .cons ⟨rfl, h⟩ (forall₂_zip_right l hs)

theorem forall₂_filterMap {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {f : α → Option γ} {g : β → Option δ} (hfg : ∀ a b, R a b → Option.Rel S (f a) (g b)) :
    ∀ {xs ys}, List.Forall₂ R xs ys → List.Forall₂ S (xs.filterMap f) (ys.filterMap g)
  | [], [], .nil => .nil
  | a :: _, b :: _, .cons h hs => by
    have hr := hfg a b h
    simp only [List.filterMap_cons]
    rcases hfa : f a with _ | c <;> rcases hgb : g b with _ | d <;> rw [hfa, hgb] at hr
    · exact forall₂_filterMap hfg hs
    · cases hr
    · cases hr
    · cases hr with
      | some hr => exact .cons hr (forall₂_filterMap hfg hs)

/-- The openings of related commitments at an opening point outside the base field are the
specification's, and so is the assembled proof. -/
theorem batchOpenAndAssemble_refines (hA : DomainsAddressable F EF) (h : Refines B) {P : Params}
    {instances : List (Instance F)} {traces : List (Array F)} (hin : InputOk EF P instances traces)
    {x : List B.M × B.C × List (List B.M) × B.C × EF × F}
    {y : List (specBackend EF).M × (specBackend EF).C × List (List (specBackend EF).M) ×
        (specBackend EF).C × EF × F}
    (hR : List.Forall₂ h.RM x.1 y.1 ∧ h.RC x.2.1 y.2.1 ∧
      List.Forall₂ (List.Forall₂ h.RM) x.2.2.1 y.2.2.1 ∧ h.RC x.2.2.2.1 y.2.2.2.1 ∧
      x.2.2.2.2 = y.2.2.2.2 ∧ (∀ m ∈ y.1, MatOk m) ∧ ∀ c ∈ y.2.2.1, ∀ m ∈ c, MatOk m)
    (hz : Ext.OutsideBase y.2.2.2.2.1) :
    RelM Eq (batchOpenAndAssemble B P instances (setupBatchWith B P instances) x)
      (batchOpenAndAssemble (specBackend EF) P instances
        (setupBatchWith (specBackend EF) P instances) y) := by
  obtain ⟨exts, mainC, chunks, quotC, zeta, ow⟩ := x
  obtain ⟨exts', mainC', chunks', quotC', zeta', ow'⟩ := y
  obtain ⟨hext, hct, hch, hqc, hzz, hextOk, hchOk⟩ := hR
  dsimp only at hext hct hch hqc hzz hextOk hchOk hz
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hzz
  obtain ⟨hprep, hprepC, hprepS⟩ := setupBatchWith_refines h hin
  have hlog : ∀ I ∈ instances, I.logN ≤ twoAdicity F := fun I hI ↦ by
    obtain ⟨t, ht⟩ := exists_of_forall₂ hin.traces I hI
    have := ht.twoAdic; omega
  -- The rounds.
  have hmain : List.Forall₂ (fun x y ↦ h.RM x.1 y.1 ∧ x.2 = y.2)
      ((instances.zip exts).map fun (I, e) ↦
        (e, tracePoints I.air zeta (zeta * Ext.ofBase (twoAdicGen I.logN))))
      ((instances.zip exts').map fun (I, e) ↦
        (e, tracePoints I.air zeta (zeta * Ext.ofBase (twoAdicGen I.logN)))) :=
    forall₂_map (fun ⟨_, _⟩ ⟨_, _⟩ ⟨hI, hr⟩ ↦ by dsimp only at hI hr; subst hI; exact ⟨hr, rfl⟩)
      (forall₂_zip_right instances hext)
  have hquot : List.Forall₂ (fun x y ↦ h.RM x.1 y.1 ∧ x.2 = y.2)
      (chunks.flatten.map fun m ↦ (m, [zeta])) (chunks'.flatten.map fun m ↦ (m, [zeta])) :=
    forall₂_map (fun _ _ hab ↦ ⟨hab, rfl⟩) (List.rel_flatten hch)
  have hprepR : List.Forall₂ (RoundRel h)
      (((setupBatchWith B P instances).2.map fun pc ↦ (pc,
        (instances.zip (setupBatchWith B P instances).1).filterMap fun (I, pext) ↦
          pext.map fun e ↦ (e, preprocessedPoints I.air zeta
            (zeta * Ext.ofBase (twoAdicGen I.logN))))).toList)
      (((setupBatchWith (specBackend EF) P instances).2.map fun pc ↦ (pc,
        (instances.zip (setupBatchWith (specBackend EF) P instances).1).filterMap
          fun (I, pext) ↦ pext.map fun e ↦ (e, preprocessedPoints I.air zeta
            (zeta * Ext.ofBase (twoAdicGen I.logN))))).toList) := by
    have hf : List.Forall₂ (fun x y ↦ h.RM x.1 y.1 ∧ x.2 = y.2)
        ((instances.zip (setupBatchWith B P instances).1).filterMap fun (I, pext) ↦
          pext.map fun e ↦ (e, preprocessedPoints I.air zeta
            (zeta * Ext.ofBase (twoAdicGen I.logN))))
        ((instances.zip (setupBatchWith (specBackend EF) P instances).1).filterMap
          fun (I, pext) ↦ pext.map fun e ↦ (e, preprocessedPoints I.air zeta
            (zeta * Ext.ofBase (twoAdicGen I.logN)))) :=
      forall₂_filterMap (fun ⟨_, _⟩ ⟨_, _⟩ ⟨hI, hr⟩ ↦ by
        dsimp only at hI hr
        subst hI
        cases hr with
        | none => exact .none
        | some hr => exact .some ⟨hr, rfl⟩) (forall₂_zip_right instances hprep)
    generalize (setupBatchWith B P instances).2 = cB at hprepC ⊢
    generalize (setupBatchWith (specBackend EF) P instances).2 = cS at hprepC ⊢
    cases hprepC with
    | none => exact .nil
    | some hr => exact .cons ⟨hr, hf⟩ .nil
  unfold batchOpenAndAssemble
  dsimp only
  refine RelM.bind (openPcs_refines hA h P (.cons ⟨hct, hmain⟩ (.cons ⟨hqc, hquot⟩ hprepR)) ?_)
    fun _ _ hx ↦ hx ▸ ?_
  · intro r hr x hx
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
    · obtain ⟨⟨I, e⟩, hIe, rfl⟩ := List.mem_map.mp hx
      exact ⟨hextOk e (List.of_mem_zip hIe).2,
        tracePoints_outside (hlog I (List.of_mem_zip hIe).1) hz⟩
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      obtain ⟨c, hc, hm⟩ := List.mem_flatten.mp hm
      exact ⟨hchOk c hc m hm, fun z hz' ↦ by rw [List.mem_singleton.mp hz']; exact hz⟩
    · obtain ⟨pc, -, rfl⟩ := Option.mem_map.mp (Option.mem_toList.mp hr)
      obtain ⟨⟨I, pext⟩, hIp, hx⟩ := List.mem_filterMap.mp hx
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hx
      have hshape := List.forall₂_zip hprepS hIp
      exact ⟨(hshape.1 e he).1, preprocessedPoints_outside (hlog I (List.of_mem_zip hIp).1) hz⟩
  · rw [h.root hct, h.root hqc,
      forall₂_map_eq (f := List.length) (g := List.length) (fun _ _ hab ↦ hab.length_eq) hch]
    exact RelM.pure rfl

/-- **A refining backend proves what the specification proves** for batches of the prover's
shapes with a list of public values per instance, when the specification's opening point `ζ` lies
outside the base field. -/
theorem proveBatchWith_refines (hA : DomainsAddressable F EF) (h : Refines B) {P : Params}
    {instances : List (Instance F)} {traces : List (Array F)} {pis : List (List F)}
    (hin : InputOk EF P instances traces) (hpis : pis.length = instances.length)
    (hz : Ext.OutsideBase (outOfDomainPoint EF P instances traces pis)) :
    proveBatchWith B P instances traces pis = proveBatch EF P instances traces pis := by
  unfold proveBatch proveBatchWith
  dsimp only
  rw [h.transcript, RelM.run_bind, RelM.run_bind]
  obtain ⟨hR, ht⟩ := batchCommitAndSample_refines h hin hpis (specBackend EF).transcript
  rw [ht]
  exact (batchOpenAndAssemble_refines hA h hin hR hz _).1

end CompStark.Batch
