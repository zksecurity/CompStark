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
specification's proof lies outside the base field. Every instance's quotient, its LogUp
constraints' included, is the specification's (`batchQuotientChunks_refines`), and the
commitments of mixed heights are the backend's (`CommitOk`).
-/

@[expose] public section
namespace CompStark.Batch
open CompStark.Fri CompStark.Stark CompStark.Lookup

variable {F : Type} [BaseField F]

/-- The width of an instance's permutation trace in base coordinates: `0` without lookups, the
accumulator and a fraction column per lookup otherwise. -/
def Instance.permWidth (EF : Type) [Challenge F EF] (I : Instance F) : Nat :=
  if I.lookups.isEmpty then 0 else (I.lookups.length + 1) * Challenge.d EF

/-- What an instance commits to, in columns at its extended height: its trace, its preprocessed
trace, its permutation trace and its quotient's chunks. -/
def Instance.columns (EF : Type) [Challenge F EF] (I : Instance F) : Nat :=
  I.air.width + I.air.preprocessedWidth + I.permWidth EF + Challenge.d EF * 2 ^ I.logQuotientChunks

/-- The shapes the fast batch prover supports: at least one instance, every instance's trace of
its AIR's shape (`Stark.InputOk`) and its quotient's chunks, its lookups' included, within the
blowup, and the batch's extensions addressable side by side at the extended height of some
`2 ^ logH` rows at least every instance's. -/
structure InputOk (EF : Type) [Challenge F EF] (P : Params) (instances : List (Instance F))
    (traces : List (Array F)) : Prop where
  /-- At least one instance. -/
  nonempty : instances ≠ []
  /-- Every trace of its AIR's shape. -/
  traces : List.Forall₂ (fun I t ↦ Stark.InputOk EF P I.air I.logN t) instances traces
  /-- Every instance's quotient's chunks fit the blowup. -/
  chunks : ∀ I ∈ instances, I.logQuotientChunks ≤ P.logBlowup
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

theorem size_permutationTrace {EF : Type} [Challenge F EF] (A : Air F)
    (ls : List (Stark.Lookup F)) (logN : Nat) (t : Array F) (pis : List F) (chs : List EF) :
    (permutationTrace A ls logN t pis chs).1.size = 2 ^ logN * (ls.length + 1) := by
  suffices h : ∀ (l : List Nat) (init : Array EF × EF), (l.foldl (fun (out, acc) i ↦
      let fs := rowFractions A ls logN t pis chs i
      ((out.push acc) ++ fs.toArray, fs.foldl (· + ·) acc)) init).1.size =
      init.1.size + l.length * (ls.length + 1) by
    rw [permutationTrace, h, List.length_range, Array.size_empty, Nat.zero_add, Nat.mul_comm]
  intro l
  induction l with
  | nil => intro _; simp only [List.foldl_nil, List.length_nil, Nat.zero_mul, Nat.add_zero]
  | cons i l ih =>
    intro init
    rw [List.foldl_cons, ih]
    simp only [rowFractions, Array.size_append, Array.size_push, List.size_toArray,
      List.length_map, List.length_zipIdx, List.length_cons]
    rw [Nat.succ_mul]
    omega

theorem size_flatten {EF : Type} [Challenge F EF] (vs : Array EF) :
    (flatten vs).size = Challenge.d EF * vs.size := by
  rw [flatten, Array.size_flatMap, ← Array.sum_toList, Array.toList_map]
  simp only [List.size_toArray, Challenge.length_coeffs]
  rw [List.map_const', List.sum_replicate, smul_eq_mul, Array.length_toList, Nat.mul_comm]

theorem sum_filterMap_width_le {α K : Type} (L : List α) (g : α → Option (Mat K)) (w : α → Nat)
    (h : ∀ x ∈ L, ∀ m ∈ g x, m.width ≤ w x) :
    (((L.map g).filterMap id).map Mat.width).sum ≤ (L.map w).sum := by
  induction L with
  | nil => exact le_rfl
  | cons x L ih =>
    have ih' := ih fun y hy ↦ h y (List.mem_cons_of_mem _ hy)
    rw [List.map_cons, List.filterMap_cons, List.map_cons, List.sum_cons]
    rcases hg : g x with _ | m
    · simp only [id]; exact le_trans ih' (Nat.le_add_left _ _)
    · simp only [id, List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h x List.mem_cons_self m (by rw [hg]; rfl)) ih'

theorem sum_map_le_of_getElem {α β : Type} (f : α → Nat) (g : β → Nat) :
    ∀ (L : List α) (M : List β), L.length = M.length →
      (∀ i (h1 : i < L.length) (h2 : i < M.length), f L[i] ≤ g M[i]) →
      (L.map f).sum ≤ (M.map g).sum
  | [], [], _, _ => le_rfl
  | [], _ :: _, h, _ => absurd h (by simp only [List.length_nil, List.length_cons]; omega)
  | _ :: _, [], h, _ => absurd h (by simp only [List.length_nil, List.length_cons]; omega)
  | a :: L, b :: M, hl, h => by
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    exact Nat.add_le_add (h 0 (by simp only [List.length_cons]; omega)
      (by simp only [List.length_cons]; omega))
      (sum_map_le_of_getElem f g L M (by simpa only [List.length_cons,
        Nat.add_right_cancel_iff] using hl) fun i h1 h2 ↦ h (i + 1)
          (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega))

theorem forall_mem_zip_map_zip {α β γ : Type} (P : α → γ → Prop) (g : α × β → γ)
    (hg : ∀ a b, P a (g (a, b))) :
    ∀ (l : List α) (r : List β), ∀ x ∈ l.zip ((l.zip r).map g), P x.1 x.2
  | [], _, _, hx => by simp only [List.zip_nil_left, List.not_mem_nil] at hx
  | _ :: _, [], _, hx => by
    simp only [List.zip_nil_right, List.map_nil, List.not_mem_nil] at hx
  | a :: l, b :: r, x, hx => by
    simp only [List.zip_cons_cons, List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hg a b
    · exact forall_mem_zip_map_zip P g hg l r x hx

theorem length_permutations {EF : Type} [Challenge F EF] (instances : List (Instance F))
    (traces : List (Array F)) (pis : List (List F)) (chs : List (List EF))
    (ht : traces.length = instances.length) (hp : pis.length = instances.length)
    (hc : chs.length = instances.length) :
    (permutations instances traces pis chs).length = instances.length := by
  simp only [permutations, List.length_map, List.length_zip, ht, hp, hc, Nat.min_self]

/-- The lookup phase returns a list of challenges per instance. -/
theorem lookupChallenges_rel {EF : Type} [Challenge F EF] (P : Params)
    (instances : List (Instance F)) :
    RelM (fun a b ↦ a = b ∧ a.2.length = instances.length)
      (lookupChallenges (EF := EF) (width := 24) P instances)
      (lookupChallenges (EF := EF) (width := 24) P instances) := by
  intro t
  refine ⟨⟨rfl, ?_⟩, rfl⟩
  show (challengeLayout _ _ _).length = _
  rw [length_challengeLayout, List.length_map]

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

/-- The chunks of the same quotient values by a refining backend and by the specification are
related, of the prover's shapes, `d` columns wide and `2 ^ logChunks` of them. -/
theorem chunksOf_refines (h : Refines B) (P : Params) {logN : Nat} (lc : Nat) (qs : Array EF)
    (hlog : logN + P.logBlowup ≤ twoAdicity F)
    (hm4 : Addressable (2 ^ (logN + P.logBlowup) * Challenge.d EF)) :
    List.Forall₂ h.RM (chunksOf B P logN lc qs) (chunksOf (specBackend EF) P logN lc qs) ∧
      (∀ m ∈ chunksOf (specBackend EF) P logN lc qs, MatOk m ∧
        m.height = 2 ^ (logN + P.logBlowup) ∧ m.width = Challenge.d EF) ∧
      (chunksOf (specBackend EF) P logN lc qs).length = 2 ^ lc := by
  unfold chunksOf
  dsimp only
  have hchOk : ∀ c, MatOk (ldeRef logN P.logBlowup
      (gen * (gen * powF (twoAdicGen (logN + lc)) c)⁻¹) (Challenge.d EF)
      (chunkValues qs (2 ^ lc) c (2 ^ logN))) := fun c ↦ by
    obtain ⟨h1, h2, h3⟩ := shape_ldeRef logN P.logBlowup
      (gen * (gen * powF (twoAdicGen (logN + lc)) c)⁻¹) (Challenge.d EF)
      (chunkValues qs (2 ^ lc) c (2 ^ logN))
    exact ⟨by rw [h1]; exact (Challenge.params EF).d_pos, ⟨_, hlog, h2⟩, by rw [h3, h1, h2],
      by rw [h1, h2, Nat.mul_comm]; exact hm4⟩
  refine ⟨forall₂_map (fun c c' hc ↦ ?_) (List.forall₂_same.2 fun _ _ ↦ rfl), fun m hm ↦ ?_, by
    rw [List.length_map, List.length_range]⟩
  · subst hc
    exact h.lde _ _ _ _ _ (by
      rw [size_chunkValues (K := EF) qs (2 ^ lc) c (2 ^ logN), Nat.mul_comm]) hlog hm4
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hm
  exact ⟨hchOk c, (shape_ldeRef ..).2.1, (shape_ldeRef ..).1⟩

/-- An instance's quotient chunks by a refining backend and by the specification, from related
extensions of a trace of the prover's shapes, of its preprocessed trace and of its permutation
trace, are related, of the prover's shapes, `d` columns wide and `2 ^ logChunks` of them. -/
theorem batchQuotientChunks_refines (h : Refines B) {P : Params} {I : Instance F}
    {trace : Array F} (pis : List F) (hin : Stark.InputOk EF P I.air I.logN trace)
    (hlc : I.logQuotientChunks ≤ P.logBlowup)
    (hm4 : Addressable (2 ^ (I.logN + P.logBlowup) * Challenge.d EF)) {ext : B.M}
    (hext : h.RM ext (ldeRef I.logN P.logBlowup gen I.air.width trace)) {pext : Option B.M}
    {spext : Option (Mat F)} (hp : Option.Rel h.RM pext spext)
    (hpok : ∀ q ∈ spext, MatOk q ∧ q.height = 2 ^ (I.logN + P.logBlowup))
    (hpw : (spext.map (·.width)).getD 0 = I.air.preprocessedWidth) {rext : Option B.M}
    {srext : Option (Mat F)} (hr : Option.Rel h.RM rext srext) (chs : List EF)
    (terminal alpha : EF) :
    List.Forall₂ h.RM (batchQuotientChunks B P I ext pext rext pis chs terminal alpha)
        (batchQuotientChunks (specBackend EF) P I (ldeRef I.logN P.logBlowup gen I.air.width trace)
          spext srext pis chs terminal alpha) ∧
      (∀ m ∈ batchQuotientChunks (specBackend EF) P I
        (ldeRef I.logN P.logBlowup gen I.air.width trace) spext srext pis chs terminal alpha,
        MatOk m ∧ m.height = 2 ^ (I.logN + P.logBlowup) ∧ m.width = Challenge.d EF) ∧
      (batchQuotientChunks (specBackend EF) P I (ldeRef I.logN P.logBlowup gen I.air.width trace)
        spext srext pis chs terminal alpha).length = 2 ^ I.logQuotientChunks := by
  obtain ⟨-, -, hw, hcols, hlog, -, hmem⟩ := hin
  obtain ⟨hew, heh, hev⟩ := shape_ldeRef I.logN P.logBlowup gen I.air.width trace
  have hextOk : MatOk (ldeRef I.logN P.logBlowup gen I.air.width trace) :=
    ⟨by rw [hew]; exact hw, ⟨_, hlog, heh⟩, by rw [hev, hew, heh],
      by rw [hew, heh, Nat.mul_comm]
         exact addressable_mono (Nat.mul_le_mul_left _ (by omega)) hmem⟩
  have hq : 2 ^ (I.logN + I.logQuotientChunks) ≤
      (ldeRef I.logN P.logBlowup gen I.air.width trace).height :=
    heh ▸ Nat.pow_le_pow_right (by decide) (by omega)
  have hquot := h.quotient I.air pis I.logN I.logQuotientChunks alpha hext hextOk hq hp
    (fun q hq' ↦ ⟨(hpok q hq').1, by rw [(hpok q hq').2, heh]⟩) (fun c hc ↦ by
      rw [hew, hpw]
      exact Expr.colsBelow_mono I.air.mainNextWidth_le le_rfl I.air.preprocessedNextWidth_le c
        (hcols c hc))
  unfold batchQuotientChunks batchQuotientValues
  dsimp only
  rw [hquot]
  cases hr with
  | none => exact chunksOf_refines h P _ _ hlog hm4
  | some hr =>
    dsimp only
    rw [h.lookupQuotient _ _ _ _ _ chs terminal alpha hext hp hr]
    exact chunksOf_refines h P _ _ hlog hm4

/-- The permutation traces' extensions and commitment by a refining backend and by the
specification are related, of the prover's shapes. -/
theorem commitPermutations_refines (h : Refines B) {P : Params} {instances : List (Instance F)}
    {traces : List (Array F)} (hin : InputOk EF P instances traces) {pis : List (List F)}
    {chs : List (List EF)} (hpis : pis.length = instances.length)
    (hchs : chs.length = instances.length) :
    List.Forall₂ (Option.Rel h.RM)
        (commitPermutations B P instances (permutations instances traces pis chs)).1
        (commitPermutations (specBackend EF) P instances
          (permutations instances traces pis chs)).1 ∧
      Option.Rel h.RC (commitPermutations B P instances (permutations instances traces pis chs)).2
        (commitPermutations (specBackend EF) P instances
          (permutations instances traces pis chs)).2 ∧
      ∀ e ∈ (commitPermutations (specBackend EF) P instances
        (permutations instances traces pis chs)).1, ∀ m ∈ e, MatOk m := by
  obtain ⟨logH, hlogH, hmem⟩ := hin.mem
  have htl := hin.traces.length_eq
  have hlog : ∀ I ∈ instances, I.logN + P.logBlowup ≤ twoAdicity F := fun I hI ↦ by
    obtain ⟨t, ht⟩ := exists_of_forall₂ hin.traces I hI
    exact ht.twoAdic
  have hpl := length_permutations instances traces pis chs htl.symm hpis hchs
  -- Every permutation trace is its instance's, of `2 ^ logN` rows of its lookups and the
  -- accumulator.
  have hsz : ∀ x ∈ instances.zip (permutations instances traces pis chs), x.1 ∈ instances ∧
      (x.2.isSome = !x.1.lookups.isEmpty) ∧
      ∀ y ∈ x.2, y.1.size = 2 ^ x.1.logN * (x.1.lookups.length + 1) := by
    intro x hx
    refine ⟨(List.of_mem_zip hx).1, ?_⟩
    revert x
    unfold permutations
    refine forall_mem_zip_map_zip (fun (I : Instance F) (y : Option (Array EF × EF)) ↦
      (y.isSome = !I.lookups.isEmpty) ∧
        ∀ z ∈ y, z.1.size = 2 ^ I.logN * (I.lookups.length + 1)) _ (fun I r ↦ ?_) _ _
    dsimp only
    split
    · rename_i he; simp only [Option.isSome_none, he, Bool.not_true, true_and]
      exact fun z hz ↦ nomatch hz
    · rename_i he
      simp only [Option.isSome_some, Bool.eq_false_iff.mpr he, Bool.not_false, true_and]
      intro z hz
      obtain rfl := Option.some_injective _ hz
      exact size_permutationTrace ..
  -- The widths, addressable at each instance's height.
  have hw : ∀ I ∈ instances, Addressable (2 ^ (I.logN + P.logBlowup) * I.permWidth EF) := by
    intro I hI
    refine addressable_le (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide)
      (by have := hlogH I hI; omega)) ((?_ : I.permWidth EF ≤ I.columns EF).trans
        (List.le_sum_of_mem (List.mem_map_of_mem hI)))) hmem
    unfold Instance.columns; omega
  have hrel : ∀ x ∈ instances.zip (permutations instances traces pis chs),
      Option.Rel h.RM (x.2.map fun (vs, _) ↦ B.lde x.1.logN P.logBlowup gen
          ((x.1.lookups.length + 1) * Challenge.d EF) (flatten vs))
        (x.2.map fun (vs, _) ↦ (specBackend EF).lde x.1.logN P.logBlowup gen
          ((x.1.lookups.length + 1) * Challenge.d EF) (flatten vs)) ∧
      ∀ m ∈ x.2.map (fun (vs, _) ↦ (specBackend EF).lde x.1.logN P.logBlowup gen
          ((x.1.lookups.length + 1) * Challenge.d EF) (flatten vs)),
        MatOk m ∧ m.height = 2 ^ (x.1.logN + P.logBlowup) ∧
          m.width = (x.1.lookups.length + 1) * Challenge.d EF := by
    intro x hx
    obtain ⟨hI, hsome, hs⟩ := hsz x hx
    rcases hx2 : x.2 with _ | ⟨vs, t⟩
    · exact ⟨.none, fun m hm ↦ nomatch hm⟩
    · have hne : x.1.lookups.isEmpty = false := by
        rw [hx2, Option.isSome_some] at hsome
        cases he : x.1.lookups.isEmpty <;> simp only [he, Bool.not_true, Bool.not_false,
          Bool.true_eq_false] at hsome ⊢
      have hpw : x.1.permWidth EF = (x.1.lookups.length + 1) * Challenge.d EF := by
        simp only [Instance.permWidth, hne, Bool.false_eq_true, ↓reduceIte]
      have hvs : vs.size = 2 ^ x.1.logN * (x.1.lookups.length + 1) := hs (vs, t) (by rw [hx2]; rfl)
      have hfs : (flatten vs).size =
          2 ^ x.1.logN * ((x.1.lookups.length + 1) * Challenge.d EF) := by
        rw [size_flatten, hvs]; ring
      have hmw := hw x.1 hI
      rw [hpw] at hmw
      obtain ⟨hew, heh, hev⟩ := shape_ldeRef x.1.logN P.logBlowup gen
        ((x.1.lookups.length + 1) * Challenge.d EF) (flatten vs)
      refine ⟨.some (h.lde _ _ _ _ _ hfs (hlog x.1 hI) hmw), fun m hm ↦ ?_⟩
      obtain rfl := Option.some_injective _ hm
      exact ⟨⟨by rw [hew]; exact Nat.mul_pos (Nat.succ_pos _) (Challenge.params EF).d_pos,
        ⟨_, hlog x.1 hI, heh⟩, by rw [hev, hew, heh], by rw [hew, heh, Nat.mul_comm]; exact hmw⟩,
        heh, hew⟩
  have hR : List.Forall₂ (Option.Rel h.RM)
      (commitPermutations B P instances (permutations instances traces pis chs)).1
      (commitPermutations (specBackend EF) P instances (permutations instances traces pis chs)).1 :=
    by
    unfold commitPermutations
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun x hx ↦ (hrel x hx).1
  have hok : ∀ e ∈ (commitPermutations (specBackend EF) P instances
      (permutations instances traces pis chs)).1, ∀ m ∈ e,
        MatOk m ∧ m.height ≤ 2 ^ (logH + P.logBlowup) := by
    intro e he m hm
    unfold commitPermutations at he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    obtain ⟨hmok, hmh, -⟩ := (hrel x hx).2 m hm
    exact ⟨hmok, by
      rw [hmh]; exact Nat.pow_le_pow_right (by decide) (by have := hlogH _ (hsz x hx).1; omega)⟩
  refine ⟨hR, ?_, fun e he m hm ↦ (hok e he m hm).1⟩
  have hf := forall₂_filterMap_id hR
  unfold commitPermutations at hf ⊢
  dsimp only at hf ⊢
  split
  · rename_i hl
    refine .some (h.commit hf ⟨2 ^ (logH + P.logBlowup), ?_, fun m hm ↦ ?_, ?_⟩)
    · -- an instance has lookups, so its permutation trace is committed
      obtain ⟨I, hI, hlk⟩ := List.any_eq_true.mp hl
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hI
      have hiz : i < (instances.zip (permutations instances traces pis chs)).length := by
        rw [List.length_zip, hpl, Nat.min_self]; exact hi
      have hx := List.getElem_mem hiz
      have hsome := (hsz _ hx).2.1
      simp only [List.getElem_zip] at hsome
      rw [hlk] at hsome
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hsome
      rw [Ne, List.filterMap_eq_nil_iff]
      intro h0
      have := h0 _ (List.mem_map_of_mem hx)
      simp only [List.getElem_zip, hy, Option.map_some, id, reduceCtorEq] at this
    · obtain ⟨e, he, hm⟩ := List.mem_filterMap.mp hm
      exact hok e he m (by rw [id] at hm; rw [hm]; rfl)
    · rw [foldl_width_sum, Nat.zero_add]
      refine addressable_le (Nat.mul_le_mul_left _ ((sum_filterMap_width_le _ _
        (fun x ↦ x.1.permWidth EF) fun x hx m hm ↦ ?_).trans ?_)) hmem
      · obtain ⟨-, -, hmw⟩ := (hrel x hx).2 m hm
        have hne : x.1.lookups.isEmpty = false := by
          have hsome := (hsz x hx).2.1
          cases hx2 : x.2 with
          | none => rw [hx2] at hm; exact nomatch hm
          | some _ =>
            rw [hx2, Option.isSome_some] at hsome
            cases he : x.1.lookups.isEmpty <;> simp only [he, Bool.not_true,
              Bool.true_eq_false] at hsome ⊢
        simp only [Instance.permWidth, hne, Bool.false_eq_true, ↓reduceIte, hmw, le_refl]
      · have hfst : (instances.zip (permutations instances traces pis chs)).map
            (fun x ↦ x.1.permWidth EF) = instances.map (·.permWidth EF) := by
          have := congrArg (List.map fun I ↦ I.permWidth EF)
            (List.map_fst_zip (l₁ := instances) (l₂ := permutations instances traces pis chs)
              (by rw [hpl]))
          rw [List.map_map] at this
          exact this
        rw [hfst]
        exact sum_le_sum_map _ _ _ fun I _ ↦ by unfold Instance.columns; omega
  · exact .none

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

/-- Every instance's quotient chunks by a refining backend and by the specification, from related
extensions, are related, of the prover's shapes, and as many as each instance's chunks. -/
theorem allQuotientChunks_refines (h : Refines B) {P : Params} {instances : List (Instance F)}
    {traces : List (Array F)} (hin : InputOk EF P instances traces) {pis : List (List F)}
    (hpis : pis.length = instances.length) (chs : List (List EF)) (terminals : List (Option EF))
    {prepB : List (Option B.M)} {prepS : List (Option (Mat F))}
    (hprep : List.Forall₂ (Option.Rel h.RM) prepB prepS)
    (hprepS : List.Forall₂ (fun I (y : Option (Mat F)) ↦
          (∀ q ∈ y, MatOk q ∧ q.height = 2 ^ (I.logN + P.logBlowup)) ∧
            (y.map (·.width)).getD 0 = I.air.preprocessedWidth) instances prepS)
    {permB : List (Option B.M)} {permS : List (Option (Mat F))}
    (hperm : List.Forall₂ (Option.Rel h.RM) permB permS) (alpha : EF) :
    List.Forall₂ (List.Forall₂ h.RM)
        (allQuotientChunks B P instances ((instances.zip traces).map fun (I, t) ↦
          B.lde I.logN P.logBlowup gen I.air.width t) prepB permB pis chs terminals alpha)
        (allQuotientChunks (specBackend EF) P instances ((instances.zip traces).map fun (I, t) ↦
          (specBackend EF).lde I.logN P.logBlowup gen I.air.width t) prepS permS pis chs
            terminals alpha) ∧
      ∀ i (hi : i < (allQuotientChunks (specBackend EF) P instances
        ((instances.zip traces).map fun (I, t) ↦
          (specBackend EF).lde I.logN P.logBlowup gen I.air.width t) prepS permS pis chs
            terminals alpha).length),
        ∃ hi' : i < instances.length,
        (∀ m ∈ (allQuotientChunks (specBackend EF) P instances
          ((instances.zip traces).map fun (I, t) ↦
            (specBackend EF).lde I.logN P.logBlowup gen I.air.width t) prepS permS pis chs
              terminals alpha)[i], MatOk m ∧
          m.height = 2 ^ (instances[i].logN + P.logBlowup) ∧ m.width = Challenge.d EF) ∧
        (allQuotientChunks (specBackend EF) P instances ((instances.zip traces).map fun (I, t) ↦
          (specBackend EF).lde I.logN P.logBlowup gen I.air.width t) prepS permS pis chs
            terminals alpha)[i].length = 2 ^ instances[i].logQuotientChunks := by
  obtain ⟨logH, hlogH, hmem⟩ := hin.mem
  have htl := hin.traces.length_eq
  have hpBl := hprep.length_eq
  have hpSl : prepS.length = instances.length := hprepS.length_eq.symm
  have hrBl := hperm.length_eq
  have hT : ∀ i (hi : i < instances.length) (ht : i < traces.length),
      Stark.InputOk EF P instances[i].air instances[i].logN traces[i] :=
    fun i hi ht ↦ getElem_of_forall₂ hin.traces i hi ht
  have hm4 : ∀ i (hi : i < instances.length),
      Addressable (2 ^ (instances[i].logN + P.logBlowup) * Challenge.d EF) := by
    intro i hi
    refine addressable_le (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide)
      (by have := hlogH _ (List.getElem_mem hi); omega)) ((?_ : Challenge.d EF ≤
        instances[i].columns EF).trans (List.le_sum_of_mem (List.mem_map_of_mem
          (List.getElem_mem hi))))) hmem
    unfold Instance.columns
    have := Nat.one_le_two_pow (n := instances[i].logQuotientChunks)
    nlinarith
  have hq : ∀ i (h1 : i < (allQuotientChunks B P instances ((instances.zip traces).map
      fun (I, t) ↦ B.lde I.logN P.logBlowup gen I.air.width t) prepB permB pis chs terminals
        alpha).length) (h2 : i < (allQuotientChunks (specBackend EF) P instances
      ((instances.zip traces).map fun (I, t) ↦
        (specBackend EF).lde I.logN P.logBlowup gen I.air.width t) prepS permS pis chs terminals
          alpha).length), ∃ hi : i < instances.length,
      List.Forall₂ h.RM (allQuotientChunks B P instances ((instances.zip traces).map
        fun (I, t) ↦ B.lde I.logN P.logBlowup gen I.air.width t) prepB permB pis chs terminals
          alpha)[i]
        (allQuotientChunks (specBackend EF) P instances ((instances.zip traces).map
          fun (I, t) ↦ (specBackend EF).lde I.logN P.logBlowup gen I.air.width t) prepS permS pis
            chs terminals alpha)[i] ∧
      (∀ m ∈ (allQuotientChunks (specBackend EF) P instances
        ((instances.zip traces).map fun (I, t) ↦
          (specBackend EF).lde I.logN P.logBlowup gen I.air.width t) prepS permS pis chs
            terminals alpha)[i], MatOk m ∧
        m.height = 2 ^ (instances[i].logN + P.logBlowup) ∧ m.width = Challenge.d EF) ∧
      (allQuotientChunks (specBackend EF) P instances ((instances.zip traces).map fun (I, t) ↦
        (specBackend EF).lde I.logN P.logBlowup gen I.air.width t) prepS permS pis chs
          terminals alpha)[i].length = 2 ^ instances[i].logQuotientChunks := by
    intro i h1 h2
    simp only [allQuotientChunks, List.length_map, List.length_zip] at h1 h2
    have hi : i < instances.length := by omega
    refine ⟨hi, ?_⟩
    simp only [allQuotientChunks, List.getElem_map, List.getElem_zip]
    have hI := hT i hi (by omega)
    have hS := getElem_of_forall₂ hprepS i hi (by omega)
    exact batchQuotientChunks_refines h _ hI (hin.chunks _ (List.getElem_mem hi)) (hm4 i hi)
      (h.lde _ _ _ _ _ hI.trace hI.twoAdic
        (addressable_le (Nat.mul_le_mul_left _ (by omega)) hI.mem))
      (getElem_of_forall₂ hprep i (by omega) (by omega)) hS.1 hS.2
      (getElem_of_forall₂ hperm i (by omega) (by omega)) _ _ _
  have hlen : (allQuotientChunks B P instances ((instances.zip traces).map fun (I, t) ↦
      B.lde I.logN P.logBlowup gen I.air.width t) prepB permB pis chs terminals alpha).length =
      (allQuotientChunks (specBackend EF) P instances ((instances.zip traces).map fun (I, t) ↦
        (specBackend EF).lde I.logN P.logBlowup gen I.air.width t) prepS permS pis chs
          terminals alpha).length := by
    simp only [allQuotientChunks, List.length_map, List.length_zip, hpBl, hrBl]
  refine ⟨forall₂_of_getElem hlen fun i h1 h2 ↦ (hq i h1 h2).2.1, fun i hi ↦ ?_⟩
  obtain ⟨hi', -, h2, h3⟩ := hq i (by rw [hlen]; exact hi) hi
  exact ⟨hi', h2, h3⟩

/-- The commit phases of a batch by a refining backend and by the specification: related
matrices and commitments, equal plain values, and the specification's matrices of the prover's
shapes. -/
structure CommitmentsRel (h : Refines B) (x : Commitments B)
    (y : Commitments (specBackend EF)) :
    Prop where
  exts : List.Forall₂ h.RM x.exts y.exts
  mainC : h.RC x.mainC y.mainC
  challenges : x.challenges = y.challenges
  permExts : List.Forall₂ (Option.Rel h.RM) x.permExts y.permExts
  permC : Option.Rel h.RC x.permC y.permC
  terminals : x.terminals = y.terminals
  lookupWitness : x.lookupWitness = y.lookupWitness
  chunks : List.Forall₂ (List.Forall₂ h.RM) x.chunks y.chunks
  quotC : h.RC x.quotC y.quotC
  zeta : x.zeta = y.zeta
  oodWitness : x.oodWitness = y.oodWitness
  extsOk : ∀ m ∈ y.exts, MatOk m
  permExtsOk : ∀ e ∈ y.permExts, ∀ m ∈ e, MatOk m
  chunksOk : ∀ c ∈ y.chunks, ∀ m ∈ c, MatOk m

/-- The commitments and challenges of a batch by a refining backend and by the specification are
related, the specification's matrices of the prover's shapes. -/
theorem batchCommitAndSample_refines (h : Refines B) {P : Params}
    {instances : List (Instance F)} {traces : List (Array F)} {pis : List (List F)}
    (hin : InputOk EF P instances traces) (hpis : pis.length = instances.length) :
    RelM (CommitmentsRel h)
      (batchCommitAndSample B P instances (setupBatchWith B P instances) traces pis)
      (batchCommitAndSample (specBackend EF) P instances
        (setupBatchWith (specBackend EF) P instances) traces pis) := by
  obtain ⟨hprep, hprepC, hprepS⟩ := setupBatchWith_refines h hin
  obtain ⟨logH, hlogH, hmem⟩ := hin.mem
  have hne := hin.nonempty
  have htl := hin.traces.length_eq
  -- The main traces' extensions.
  have hext : List.Forall₂ h.RM
      ((instances.zip traces).map fun (I, t) ↦ B.lde I.logN P.logBlowup gen I.air.width t)
      ((instances.zip traces).map fun (I, t) ↦
        (specBackend EF).lde I.logN P.logBlowup gen I.air.width t) := by
    refine forall₂_of_getElem (by simp only [List.length_map]) fun i h1 h2 ↦ ?_
    simp only [List.length_map, List.length_zip] at h1
    have hI : Stark.InputOk EF P instances[i].air instances[i].logN traces[i] :=
      getElem_of_forall₂ hin.traces i (by omega) (by omega)
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
    RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦ ?_
  refine RelM.bind (lookupChallenges_rel P instances) fun lc lc' ⟨hlc, hchs⟩ ↦ hlc ▸ ?_
  obtain ⟨lw, chs⟩ := lc
  dsimp only at hchs ⊢
  -- The permutation traces.
  obtain ⟨hpe, hpc, hpeOk⟩ := commitPermutations_refines h hin (traces := traces) hpis hchs
  have hpl := length_permutations instances traces pis chs htl.symm hpis hchs
  generalize hperms : permutations instances traces pis chs = perms at hpe hpc hpeOk hpl
  have hpeSl : (commitPermutations (specBackend EF) P instances perms).1.length =
      instances.length := by
    simp only [commitPermutations, List.length_map, List.length_zip, hpl, Nat.min_self]
  generalize commitPermutations B P instances perms = cpB at hpe hpc
  generalize commitPermutations (specBackend EF) P instances perms = cpS at hpe hpc hpeOk hpeSl
  obtain ⟨peB, pcB⟩ := cpB
  obtain ⟨peS, pcS⟩ := cpS
  dsimp only at hpe hpc hpeOk ⊢
  have hproot : (pcB.map fun c ↦ (B.root c).toList).getD [] =
      (pcS.map fun c ↦ ((specBackend EF).root c).toList).getD [] := by
    cases hpc with
    | none => rfl
    | some hr => exact congrArg Vector.toList (h.root hr)
  rw [hproot]
  refine RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦ RelM.bind_eq fun alpha ↦ ?_
  -- Every instance's quotient chunks.
  obtain ⟨hch, hchS⟩ := allQuotientChunks_refines h hin hpis chs (perms.map (·.map (·.2)))
    hprep hprepS hpe alpha
  have hchSl : (allQuotientChunks (specBackend EF) P instances ((instances.zip traces).map
      fun (I, t) ↦ (specBackend EF).lde I.logN P.logBlowup gen I.air.width t)
        (setupBatchWith (specBackend EF) P instances).1 peS pis chs (perms.map (·.map (·.2)))
          alpha).length = instances.length := by
    have := hprepS.length_eq
    simp only [allQuotientChunks, List.length_map, List.length_zip, htl, hpis, hchs, hpl,
      hpeSl, ← this, Nat.min_self]
  generalize allQuotientChunks B P instances _ _ peB pis chs _ alpha = chB at hch
  generalize allQuotientChunks (specBackend EF) P instances _ _ peS pis chs _ alpha = chS
    at hch hchS hchSl
  have hSmem : ∀ c ∈ chS, ∀ m ∈ c,
      MatOk m ∧ m.height ≤ 2 ^ (logH + P.logBlowup) ∧ m.width = Challenge.d EF := by
    intro c hc m hm
    obtain ⟨i, h1, rfl⟩ := List.getElem_of_mem hc
    obtain ⟨hi, hok, -⟩ := hchS i h1
    obtain ⟨hmok, hh, hw⟩ := hok m hm
    exact ⟨hmok, by
      rw [hh]
      exact Nat.pow_le_pow_right (by decide) (by have := hlogH _ (List.getElem_mem hi); omega),
      hw⟩
  have hsum : (chS.map fun c ↦ (c.map Mat.width).sum).sum ≤ (instances.map (·.columns EF)).sum :=
    sum_map_le_of_getElem _ _ _ _ (by rw [hchSl]) fun i h1 h2 ↦ by
      obtain ⟨hi, hok, hl⟩ := hchS i h1
      have e := foldl_width_sum chS[i] 0
      rw [Nat.zero_add] at e
      rw [← e, foldl_width_const _ _ fun m hm ↦ (hok m hm).2.2, hl, Nat.zero_add]
      unfold Instance.columns; omega
  have hqc := h.commit (List.rel_flatten hch) ⟨2 ^ (logH + P.logBlowup), by
      intro he
      rw [List.flatten_eq_nil_iff] at he
      have h0 : 0 < chS.length := by rw [hchSl]; exact List.length_pos_of_ne_nil hne
      obtain ⟨_, _, hl⟩ := hchS 0 h0
      rw [he _ (List.getElem_mem h0), List.length_nil] at hl
      exact absurd hl.symm (Nat.two_pow_pos _).ne',
    fun m hm ↦ by
      obtain ⟨c, hc, hm⟩ := List.mem_flatten.mp hm
      exact ⟨(hSmem c hc m hm).1, (hSmem c hc m hm).2.1⟩, by
      rw [foldl_width_sum, Nat.zero_add, List.map_flatten, List.sum_flatten, List.map_map]
      exact addressable_le (Nat.mul_le_mul_left _ hsum) hmem⟩
  rw [h.root hqc]
  refine RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦ ?_
  exact RelM.pure ⟨hext, hct, rfl, hpe, hpc, rfl, rfl, hch, hqc, rfl, rfl,
    fun m hm ↦ (hextOk m hm).1, hpeOk, fun c hc m hm ↦ (hSmem c hc m hm).1⟩

/-- The openings of related commitments at an opening point outside the base field are the
specification's, and so is the assembled proof. -/
theorem batchOpenAndAssemble_refines (hA : DomainsAddressable F EF) (h : Refines B) {P : Params}
    {instances : List (Instance F)} {traces : List (Array F)} (hin : InputOk EF P instances traces)
    {x : Commitments B} {y : Commitments (specBackend EF)} (hR : CommitmentsRel h x y)
    (hz : Ext.OutsideBase y.zeta) :
    RelM Eq (batchOpenAndAssemble B P instances (setupBatchWith B P instances) x)
      (batchOpenAndAssemble (specBackend EF) P instances
        (setupBatchWith (specBackend EF) P instances) y) := by
  obtain ⟨hprep, hprepC, hprepS⟩ := setupBatchWith_refines h hin
  have hlog : ∀ I ∈ instances, I.logN ≤ twoAdicity F := fun I hI ↦ by
    obtain ⟨t, ht⟩ := exists_of_forall₂ hin.traces I hI
    have := ht.twoAdic; omega
  have hzeta := hR.zeta
  -- The rounds.
  have hmain : List.Forall₂ (fun x y ↦ h.RM x.1 y.1 ∧ x.2 = y.2)
      ((instances.zip x.exts).map fun (I, e) ↦
        (e, tracePoints I.air x.zeta (x.zeta * Ext.ofBase (twoAdicGen I.logN))))
      ((instances.zip y.exts).map fun (I, e) ↦
        (e, tracePoints I.air y.zeta (y.zeta * Ext.ofBase (twoAdicGen I.logN)))) :=
    forall₂_map (fun ⟨_, _⟩ ⟨_, _⟩ ⟨hI, hr⟩ ↦ by
      dsimp only at hI hr; subst hI; exact ⟨hr, by rw [hzeta]⟩)
      (forall₂_zip_right instances hR.exts)
  have hquot : List.Forall₂ (fun x y ↦ h.RM x.1 y.1 ∧ x.2 = y.2)
      (x.chunks.flatten.map fun m ↦ (m, [x.zeta])) (y.chunks.flatten.map fun m ↦ (m, [y.zeta])) :=
    forall₂_map (fun _ _ hab ↦ ⟨hab, by rw [hzeta]⟩) (List.rel_flatten hR.chunks)
  have hprepR : List.Forall₂ (RoundRel h)
      (((setupBatchWith B P instances).2.map fun pc ↦ (pc,
        (instances.zip (setupBatchWith B P instances).1).filterMap fun (I, pext) ↦
          pext.map fun e ↦ (e, preprocessedPoints I.air x.zeta
            (x.zeta * Ext.ofBase (twoAdicGen I.logN))))).toList)
      (((setupBatchWith (specBackend EF) P instances).2.map fun pc ↦ (pc,
        (instances.zip (setupBatchWith (specBackend EF) P instances).1).filterMap
          fun (I, pext) ↦ pext.map fun e ↦ (e, preprocessedPoints I.air y.zeta
            (y.zeta * Ext.ofBase (twoAdicGen I.logN))))).toList) := by
    have hf : List.Forall₂ (fun x y ↦ h.RM x.1 y.1 ∧ x.2 = y.2)
        ((instances.zip (setupBatchWith B P instances).1).filterMap fun (I, pext) ↦
          pext.map fun e ↦ (e, preprocessedPoints I.air x.zeta
            (x.zeta * Ext.ofBase (twoAdicGen I.logN))))
        ((instances.zip (setupBatchWith (specBackend EF) P instances).1).filterMap
          fun (I, pext) ↦ pext.map fun e ↦ (e, preprocessedPoints I.air y.zeta
            (y.zeta * Ext.ofBase (twoAdicGen I.logN)))) :=
      forall₂_filterMap (fun ⟨_, _⟩ ⟨_, _⟩ ⟨hI, hr⟩ ↦ by
        dsimp only at hI hr
        subst hI
        cases hr with
        | none => exact .none
        | some hr => exact .some ⟨hr, by rw [hzeta]⟩) (forall₂_zip_right instances hprep)
    generalize (setupBatchWith B P instances).2 = cB at hprepC ⊢
    generalize (setupBatchWith (specBackend EF) P instances).2 = cS at hprepC ⊢
    cases hprepC with
    | none => exact .nil
    | some hr => exact .cons ⟨hr, hf⟩ .nil
  have hpermR : List.Forall₂ (RoundRel h)
      ((x.permC.map fun pc ↦ (pc, (instances.zip x.permExts).filterMap fun (I, r) ↦
        r.map fun e ↦ (e, [x.zeta, x.zeta * Ext.ofBase (twoAdicGen I.logN)]))).toList)
      ((y.permC.map fun pc ↦ (pc, (instances.zip y.permExts).filterMap fun (I, r) ↦
        r.map fun e ↦ (e, [y.zeta, y.zeta * Ext.ofBase (twoAdicGen I.logN)]))).toList) := by
    have hf : List.Forall₂ (fun x y ↦ h.RM x.1 y.1 ∧ x.2 = y.2)
        ((instances.zip x.permExts).filterMap fun (I, r) ↦
          r.map fun e ↦ (e, [x.zeta, x.zeta * Ext.ofBase (twoAdicGen I.logN)]))
        ((instances.zip y.permExts).filterMap fun (I, r) ↦
          r.map fun e ↦ (e, [y.zeta, y.zeta * Ext.ofBase (twoAdicGen I.logN)])) :=
      forall₂_filterMap (fun ⟨_, _⟩ ⟨_, _⟩ ⟨hI, hr⟩ ↦ by
        dsimp only at hI hr
        subst hI
        cases hr with
        | none => exact .none
        | some hr => exact .some ⟨hr, by rw [hzeta]⟩) (forall₂_zip_right instances hR.permExts)
    have hpc := hR.permC
    generalize x.permC = cB at hpc ⊢
    generalize y.permC = cS at hpc ⊢
    cases hpc with
    | none => exact .nil
    | some hr => exact .cons ⟨hr, hf⟩ .nil
  unfold batchOpenAndAssemble
  dsimp only
  refine RelM.bind (openPcs_refines hA h P
    (List.rel_append (List.rel_append (.cons ⟨hR.mainC, hmain⟩
      (.cons ⟨hR.quotC, hquot⟩ .nil)) hprepR) hpermR) ?_) fun _ _ ho ↦ ho ▸ ?_
  · intro r hr z hx
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | rfl | hr | hr
    · obtain ⟨⟨I, e⟩, hIe, rfl⟩ := List.mem_map.mp hx
      exact ⟨hR.extsOk e (List.of_mem_zip hIe).2,
        tracePoints_outside (hlog I (List.of_mem_zip hIe).1) hz⟩
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      obtain ⟨c, hc, hm⟩ := List.mem_flatten.mp hm
      exact ⟨hR.chunksOk c hc m hm, fun z hz' ↦ by rw [List.mem_singleton.mp hz']; exact hz⟩
    · obtain ⟨pc, -, rfl⟩ := Option.mem_map.mp (Option.mem_toList.mp hr)
      obtain ⟨⟨I, pext⟩, hIp, hx⟩ := List.mem_filterMap.mp hx
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hx
      have hshape := List.forall₂_zip hprepS hIp
      exact ⟨(hshape.1 e he).1, preprocessedPoints_outside (hlog I (List.of_mem_zip hIp).1) hz⟩
    · obtain ⟨pc, -, rfl⟩ := Option.mem_map.mp (Option.mem_toList.mp hr)
      obtain ⟨⟨I, r⟩, hIr, hx⟩ := List.mem_filterMap.mp hx
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hx
      have hw := Ext.outsideBase_mul_ofBase hz
        (BaseField.twoAdicGen_ne_zero I.logN (hlog I (List.of_mem_zip hIr).1))
      refine ⟨hR.permExtsOk r (List.of_mem_zip hIr).2 e he, fun z hz' ↦ ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz'
      rcases hz' with rfl | rfl
      · exact hz
      · exact hw
  · have hpc : x.permC.map B.root = y.permC.map (specBackend EF).root := by
      have hpc0 := hR.permC
      generalize x.permC = cB at hpc0 ⊢
      generalize y.permC = cS at hpc0 ⊢
      cases hpc0 with
      | none => rfl
      | some hr => exact congrArg some (h.root hr)
    have hprepSome : (setupBatchWith B P instances).2.isSome =
        (setupBatchWith (specBackend EF) P instances).2.isSome := by
      generalize (setupBatchWith B P instances).2 = cB at hprepC ⊢
      generalize (setupBatchWith (specBackend EF) P instances).2 = cS at hprepC ⊢
      cases hprepC with
      | none => rfl
      | some => rfl
    rw [h.root hR.mainC, h.root hR.quotC, hpc, hprepSome, hR.terminals, hR.lookupWitness,
      hR.oodWitness, forall₂_map_eq (f := List.length) (g := List.length)
        (fun _ _ hab ↦ hab.length_eq) hR.chunks]
    exact RelM.pure rfl

/-- **A refining backend proves what the specification proves** for batches of the prover's
shapes with a list of public values per instance, when the specification's opening point `ζ` lies
outside the base field. -/
theorem proveBatchWith_refines (hA : DomainsAddressable F EF) (h : Refines B) {P : Params}
    {instances : List (Instance F)} {traces : List (Array F)} {pis : List (List F)}
    (hin : InputOk EF P instances traces) (hpis : pis.length = instances.length)
    (hz : Ext.OutsideBase (batchOutOfDomainPoint EF P instances traces pis)) :
    proveBatchWith B P instances traces pis = proveBatch EF P instances traces pis := by
  unfold proveBatch proveBatchWith
  dsimp only
  rw [h.transcript, RelM.run_bind, RelM.run_bind]
  obtain ⟨hR, ht⟩ := batchCommitAndSample_refines h hin hpis (specBackend EF).transcript
  rw [ht]
  exact (batchOpenAndAssemble_refines hA h hin hR hz _).1

end CompStark.Batch
