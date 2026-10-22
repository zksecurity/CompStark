/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Refines
public import CompStark.Stark.Prover
public import CompStark.Stark.Fast.OpeningsSpec

/-! # Provers on refining backends

A backend that refines the specification (`Fri.Refines`) proves what the specification proves
(`proveWith_refines`), for a trace of the AIR's shape within the base field's two-adic subgroups
whose buffers are addressable, when the opening point `ζ` of the specification's proof lies outside
the base field.
-/

@[expose] public section
namespace CompStark.Stark
open CompStark.Fri

variable {F : Type} [BaseField F]

/-- Coordinate `e` of an extension element. -/
abbrev coordOf {K : Type} [Challenge F K] (e : Nat) (y : K) : F := (Ext.coeffs y).getD e 0

/-- A chunk's coordinates, tabulated. -/
theorem chunkValues_eq {K : Type} [Challenge F K] (qs : Array K) (stride c n : Nat) :
    chunkValues qs stride c n = Array.ofFn (n := n * Challenge.d K) fun k ↦
      coordOf (k.val % Challenge.d K) (qs.getD (k.val / Challenge.d K * stride + c) 0) := by
  unfold chunkValues
  refine parChunks_eq_blocks n _ (Challenge.d K) _
    (fun k ↦ coordOf (k % Challenge.d K) (qs.getD (k / Challenge.d K * stride + c) 0))
    (fun s len _ ↦ ?_) (by left; split <;> omega)
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, pure_bind, Std.Legacy.Range.size, Nat.add_sub_cancel_left,
    Nat.add_sub_cancel, Nat.div_one]
  show List.foldl _ _ _ = _
  have hbody : (fun (out : Array F) (r : Nat) ↦
      out ++ (Ext.coeffs (qs.getD (r * stride + c) 0)).toArray) =
      fun out r ↦ (List.range' 0 (Challenge.d K)).foldl
        (fun o i ↦ o.push (coordOf i (qs.getD (r * stride + c) 0))) out := by
    funext out r
    have hl : (Ext.coeffs (qs.getD (r * stride + c) 0)).length = Challenge.d K :=
      Challenge.length_coeffs _
    rw [foldl_push_range']
    congr 1
    refine Array.ext (by rw [List.size_toArray, Array.size_ofFn, hl]) fun i h1 _ ↦ ?_
    rw [Array.getElem_ofFn, List.getElem_toArray, coordOf, Nat.zero_add,
      List.getD_eq_getElem _ _ (by rw [List.size_toArray] at h1; exact h1)]
  rw [hbody, foldl_blocks (fun r i ↦ coordOf i (qs.getD (r * stride + c) 0)) (Challenge.d K) len s,
    Array.emptyWithCapacity_eq, Array.empty_append]
  refine congrArg Array.ofFn (funext fun k ↦ ?_)
  have hd : 0 < Challenge.d K := (Challenge.params K).d_pos
  have e1 : (s * Challenge.d K + k.val) / Challenge.d K = s + k.val / Challenge.d K := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.add_comm]
  have e2 : (s * Challenge.d K + k.val) % Challenge.d K = k.val % Challenge.d K := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right]
  rw [e1, e2]

theorem size_chunkValues {K : Type} [Challenge F K] (qs : Array K) (stride c n : Nat) :
    (chunkValues qs stride c n).size = Challenge.d K * n := by
  rw [chunkValues_eq, Array.size_ofFn, Nat.mul_comm]

theorem addressable_mono {m n : Nat} (h : m ≤ n) (hn : Addressable n) : Addressable m := by
  unfold Addressable at *; omega

/-- The shapes the fast prover supports: a trace and an AIR within the base field's two-adic
subgroups whose extension over `EF` fits machine-word indices. -/
structure InputOk (EF : Type) [Challenge F EF] (P : Params) (A : Air F) (logN : Nat)
    (trace : Array F) : Prop where
  /-- The trace has `2 ^ logN` rows of the AIR's width. -/
  trace : trace.size = 2 ^ logN * A.width
  /-- The preprocessed trace has `2 ^ logN` rows of the AIR's preprocessed width. -/
  preprocessed : A.preprocessed.size = 2 ^ logN * A.preprocessedWidth
  /-- The AIR has a column. -/
  width : 0 < A.width
  /-- The constraints read only the AIR's columns. -/
  cols : A.ColsInWidth
  /-- The extended trace domain is a two-adic subgroup of the base field. -/
  twoAdic : logN + P.logBlowup ≤ twoAdicity F
  /-- The quotient's chunks fit the blowup. -/
  chunks : A.logQuotientChunks logN ≤ P.logBlowup
  /-- The extended traces and quotient are addressable by `USize` word indices. -/
  mem : Addressable (2 ^ (logN + P.logBlowup) *
    (A.width + A.preprocessedWidth + Challenge.d EF * 2 ^ A.logQuotientChunks logN))

variable [Poseidon2Field F] {EF : Type} [Challenge F EF] {B : Backend F EF 24}

/-- The preprocessed trace's extensions and commitments by a refining backend and by the
specification are related, and of the prover's shapes. -/
theorem setupWith_refines (h : Refines B) {P : Params} {A : Air F} {logN : Nat}
    {trace : Array F} (hin : InputOk EF P A logN trace) :
    Option.Rel (fun x y ↦ h.RM x.1 y.1 ∧ h.RC x.2 y.2) (setupWith B P A logN)
      (setupWith (specBackend EF) P A logN) ∧
    ∀ y ∈ setupWith (specBackend EF) P A logN, MatOk y.1 ∧
      y.1.height = 2 ^ (logN + P.logBlowup) ∧ y.1.width = A.preprocessedWidth := by
  have hm : Addressable (2 ^ (logN + P.logBlowup) * A.preprocessedWidth) :=
    addressable_mono (Nat.mul_le_mul_left _ (by omega)) hin.mem
  unfold setupWith
  by_cases hpw : A.preprocessedWidth = 0
  · simp only [hpw, ↓reduceIte]
    exact ⟨.none, fun y hy ↦ nomatch hy⟩
  · simp only [hpw, ↓reduceIte]
    obtain ⟨hew, heh, hev⟩ :=
      shape_ldeRef logN P.logBlowup gen A.preprocessedWidth A.preprocessed
    have hextOk : MatOk (ldeRef logN P.logBlowup gen A.preprocessedWidth A.preprocessed) :=
      ⟨by rw [hew]; omega, ⟨_, hin.twoAdic, heh⟩, by rw [hev, hew, heh],
        by rw [hew, heh, Nat.mul_comm]; exact hm⟩
    have hext := h.lde logN P.logBlowup gen A.preprocessedWidth A.preprocessed hin.preprocessed
      hin.twoAdic hm
    have hct := h.commit (.cons hext .nil) ⟨_, List.cons_ne_nil _ _,
      fun m hm' ↦ by obtain rfl := List.mem_singleton.mp hm'; exact ⟨hextOk, heh.le⟩,
      by show Addressable (_ * (0 + A.preprocessedWidth)); rw [Nat.zero_add]; exact hm⟩
    refine ⟨.some ⟨hext, hct⟩, fun y hy ↦ ?_⟩
    obtain rfl := Option.some_injective _ hy
    exact ⟨hextOk, heh, hew⟩

/-- The width the quotient reads off the specification's preprocessed extension. -/
theorem width_setupWith (P : Params) (A : Air F) (logN : Nat) :
    (((setupWith (specBackend EF) P A logN).map (·.1)).map (·.width)).getD 0 =
      A.preprocessedWidth := by
  unfold setupWith
  by_cases hpw : A.preprocessedWidth = 0
  · simp only [hpw, ↓reduceIte, Option.map_none, Option.getD_none]
  · simp only [hpw, ↓reduceIte, Option.map_some, Option.getD_some]
    exact (shape_ldeRef ..).1

/-- The quotient's chunks by a refining backend and by the specification, from related
extensions of a trace of the prover's shapes and of its preprocessed trace, are related, of the
prover's shapes, `d` columns wide and `2 ^ logChunks` of them. -/
theorem quotientChunks_refines (h : Refines B) {P : Params} {A : Air F} {logN : Nat}
    {trace : Array F} (pis : List F) (hin : InputOk EF P A logN trace) {ext : B.M}
    (hext : h.RM ext (ldeRef logN P.logBlowup gen A.width trace)) {pext : Option B.M}
    {spext : Option (Mat F)} (hp : Option.Rel h.RM pext spext)
    (hpok : ∀ q ∈ spext, MatOk q ∧ q.height = 2 ^ (logN + P.logBlowup))
    (hpw : (spext.map (·.width)).getD 0 = A.preprocessedWidth) (alpha : EF) :
    List.Forall₂ h.RM (quotientChunks B P A logN ext pext pis alpha)
        (quotientChunks (specBackend EF) P A logN (ldeRef logN P.logBlowup gen A.width trace)
          spext pis alpha) ∧
      (∀ m ∈ quotientChunks (specBackend EF) P A logN (ldeRef logN P.logBlowup gen A.width trace)
        spext pis alpha, MatOk m ∧ m.height = 2 ^ (logN + P.logBlowup) ∧
          m.width = Challenge.d EF) ∧
      (quotientChunks (specBackend EF) P A logN (ldeRef logN P.logBlowup gen A.width trace)
        spext pis alpha).length = 2 ^ A.logQuotientChunks logN := by
  obtain ⟨-, -, hw, hcols, hlog, hchunks, hmem⟩ := hin
  have hmq :
      Addressable (2 ^ (logN + P.logBlowup) * (Challenge.d EF * 2 ^ A.logQuotientChunks logN)) :=
    addressable_mono (Nat.mul_le_mul_left _ (Nat.le_add_left _ _)) hmem
  have h1 : 1 ≤ 2 ^ A.logQuotientChunks logN := Nat.one_le_two_pow
  have hm4 : Addressable (2 ^ (logN + P.logBlowup) * Challenge.d EF) :=
    addressable_mono (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ h1)) hmq
  obtain ⟨hew, heh, hev⟩ := shape_ldeRef logN P.logBlowup gen A.width trace
  have hextOk : MatOk (ldeRef logN P.logBlowup gen A.width trace) :=
    ⟨by rw [hew]; exact hw, ⟨_, hlog, heh⟩, by rw [hev, hew, heh],
      by rw [hew, heh, Nat.mul_comm]
         exact addressable_mono (Nat.mul_le_mul_left _ (by omega)) hmem⟩
  have hprepQok : ∀ q ∈ spext,
      MatOk q ∧ q.height = (ldeRef logN P.logBlowup gen A.width trace).height := by
    intro q hq
    obtain ⟨hok, hh⟩ := hpok q hq
    exact ⟨hok, by rw [hh, heh]⟩
  unfold quotientChunks chunksOf
  dsimp only
  have hq :
      2 ^ (logN + A.logQuotientChunks logN) ≤ (ldeRef logN P.logBlowup gen A.width trace).height :=
    heh ▸ Nat.pow_le_pow_right (by decide) (by omega)
  rw [h.quotient _ _ _ _ _ hext hextOk hq hp hprepQok (fun c hc ↦ by
    rw [hew, hpw]
    exact Expr.colsBelow_mono A.mainNextWidth_le le_rfl A.preprocessedNextWidth_le c
      (hcols c hc))]
  dsimp only
  generalize quotientOfLde A pis logN (A.logQuotientChunks logN) _ _ alpha = qs
  have hchOk : ∀ c, MatOk (ldeRef logN P.logBlowup
      (gen * (gen * powF (twoAdicGen (logN + A.logQuotientChunks logN)) c)⁻¹) (Challenge.d EF)
      (chunkValues qs (2 ^ A.logQuotientChunks logN) c (2 ^ logN))) := fun c ↦ by
    obtain ⟨h1, h2, h3⟩ := shape_ldeRef logN P.logBlowup
      (gen * (gen * powF (twoAdicGen (logN + A.logQuotientChunks logN)) c)⁻¹) (Challenge.d EF)
      (chunkValues qs (2 ^ A.logQuotientChunks logN) c (2 ^ logN))
    exact ⟨by rw [h1]; exact (Challenge.params EF).d_pos, ⟨_, hlog, h2⟩, by rw [h3, h1, h2],
      by rw [h1, h2, Nat.mul_comm]; exact hm4⟩
  refine ⟨forall₂_map (fun c c' hc ↦ ?_) (List.forall₂_same.2 fun _ _ ↦ rfl), fun m hm ↦ ?_, by
    rw [List.length_map, List.length_range]⟩
  · subst hc
    exact h.lde _ _ _ _ _ (by
      rw [size_chunkValues (K := EF) qs (2 ^ A.logQuotientChunks logN) c (2 ^ logN), Nat.mul_comm])
      hlog hm4
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hm
  exact ⟨hchOk c, (shape_ldeRef ..).2.1, (shape_ldeRef ..).1⟩

/-- The widths of matrices of width `w` side by side. -/
theorem foldl_width_const {K : Type} (l : List (Mat K)) (w : Nat) (hl : ∀ m ∈ l, m.width = w)
    (a : Nat) :
    l.foldl (· + ·.width) a = a + w * l.length := by
  induction l generalizing a with
  | nil => rfl
  | cons m l ih =>
    rw [List.foldl_cons, ih (fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)), hl m List.mem_cons_self,
      List.length_cons, Nat.mul_succ]
    omega

theorem commitAndSample_refines (h : Refines B) {P : Params} {A : Air F} {logN : Nat}
    {t : B.Trace} {trace : Array F} (pis : List F) (ht : h.RT t trace)
    (hin : InputOk EF P A logN trace) :
    RelM (fun x y ↦ h.RM x.1 y.1 ∧ h.RC x.2.1 y.2.1 ∧ List.Forall₂ h.RM x.2.2.1 y.2.2.1 ∧
        h.RC x.2.2.2.1 y.2.2.2.1 ∧ x.2.2.2.2 = y.2.2.2.2 ∧ MatOk y.1 ∧ ∀ m ∈ y.2.2.1, MatOk m)
      (commitAndSample B P A logN (setupWith B P A logN) t pis)
          (commitAndSample (specBackend EF) P A logN (setupWith (specBackend EF) P A logN)
            trace pis) := by
  obtain ⟨hprep, hprepOk⟩ := setupWith_refines h hin
  have hin' := hin
  obtain ⟨htrace, -, hw, hcols, hlog, hchunks, hmem⟩ := hin
  have hmw : Addressable (2 ^ (logN + P.logBlowup) * A.width) :=
    addressable_mono (Nat.mul_le_mul_left _ (by omega)) hmem
  have hmq :
      Addressable (2 ^ (logN + P.logBlowup) * (Challenge.d EF * 2 ^ A.logQuotientChunks logN)) :=
    addressable_mono (Nat.mul_le_mul_left _ (Nat.le_add_left _ _)) hmem
  -- The extended trace.
  obtain ⟨hew, heh, hev⟩ := shape_ldeRef logN P.logBlowup gen A.width trace
  have hextOk : MatOk (ldeRef logN P.logBlowup gen A.width trace) :=
    ⟨by rw [hew]; exact hw, ⟨_, hlog, heh⟩, by rw [hev, hew, heh],
      by rw [hew, heh, Nat.mul_comm]; exact hmw⟩
  have hext := h.ldeTrace logN P.logBlowup gen A.width ht htrace hlog hmw
  have hct := h.commit (.cons hext .nil) ⟨_, List.cons_ne_nil _ _,
    fun m hm ↦ by obtain rfl := List.mem_singleton.mp hm; exact ⟨hextOk, heh.le⟩,
    by show Addressable (_ * (0 + A.width)); rw [Nat.zero_add]; exact hmw⟩
  -- The preprocessed trace's root and extension.
  have hroots : ((setupWith B P A logN).map fun x ↦ (B.root x.2).toList).getD [] =
      ((setupWith (specBackend EF) P A logN).map fun x ↦
        ((specBackend EF).root x.2).toList).getD [] := by
    generalize setupWith B P A logN = xp at hprep
    generalize setupWith (specBackend EF) P A logN = yp at hprep
    cases hprep with
    | none => rfl
    | @some a b hr =>
      show (B.root a.2).toList = ((specBackend EF).root b.2).toList
      rw [h.root hr.2]
  have hprepQ : Option.Rel h.RM ((setupWith B P A logN).map (·.1))
      ((setupWith (specBackend EF) P A logN).map (·.1)) := by
    generalize setupWith B P A logN = xp at hprep
    generalize setupWith (specBackend EF) P A logN = yp at hprep
    cases hprep with
    | none => exact .none
    | @some a b hr => exact .some hr.1
  have hprepQok : ∀ q ∈ (setupWith (specBackend EF) P A logN).map (·.1),
      MatOk q ∧ q.height = 2 ^ (logN + P.logBlowup) := by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := Option.mem_map.mp hq
    exact ⟨(hprepOk y hy).1, (hprepOk y hy).2.1⟩
  unfold commitAndSample
  dsimp only
  rw [h.root hct, hroots]
  refine RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦
    RelM.bind_eq fun _ ↦ RelM.bind_eq fun alpha ↦ ?_
  obtain ⟨hch, hall, hlen⟩ := quotientChunks_refines h pis hin' hext hprepQ hprepQok
    (width_setupWith (EF := EF) P A logN) alpha
  have hqc := h.commit hch ⟨_, List.ne_nil_of_length_pos (by rw [hlen]; exact Nat.two_pow_pos _),
    fun m hm ↦ ⟨(hall m hm).1, (hall m hm).2.1.le⟩, by
      rw [foldl_width_const _ _ (fun m hm ↦ (hall m hm).2.2), hlen, Nat.zero_add]
      exact hmq⟩
  rw [h.root hqc]
  dsimp only
  refine RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦ ?_
  exact RelM.pure ⟨hext, hct, hch, hqc, rfl, hextOk, fun m hm ↦ (hall m hm).1⟩

/-- The openings of related commitments at an opening point outside the base field are the
specification's. -/
theorem openAndAssemble_refines (hA : DomainsAddressable F EF) (h : Refines B) (P : Params)
    {A : Air F} {logN : Nat} (hlog : logN ≤ twoAdicity F) {xprep : Option (B.M × B.C)}
    {yprep : Option ((specBackend EF).M × (specBackend EF).C)}
    (hprep : Option.Rel (fun x y ↦ h.RM x.1 y.1 ∧ h.RC x.2 y.2) xprep yprep)
    (hprepOk : ∀ y ∈ yprep, MatOk y.1) {x : B.M × B.C × List B.M × B.C × EF × F}
    {y : (specBackend EF).M × (specBackend EF).C × List (specBackend EF).M ×
        (specBackend EF).C × EF × F}
    (hR : h.RM x.1 y.1 ∧ h.RC x.2.1 y.2.1 ∧ List.Forall₂ h.RM x.2.2.1 y.2.2.1 ∧
      h.RC x.2.2.2.1 y.2.2.2.1 ∧ x.2.2.2.2 = y.2.2.2.2 ∧ MatOk y.1 ∧ ∀ m ∈ y.2.2.1, MatOk m)
    (hz : Ext.OutsideBase y.2.2.2.2.1) :
    RelM Eq (openAndAssemble B P A logN xprep x)
      (openAndAssemble (specBackend EF) P A logN yprep y) := by
  obtain ⟨ext, traceC, chunks, quotC, zeta, ow⟩ := x
  obtain ⟨ext', traceC', chunks', quotC', zeta', ow'⟩ := y
  obtain ⟨hext, hct, hch, hqc, hzz, hextOk, hchOk⟩ := hR
  dsimp only at hext hct hch hqc hzz hextOk hchOk hz
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hzz
  have hw := Ext.outsideBase_mul_ofBase hz (BaseField.twoAdicGen_ne_zero logN hlog)
  have hpts : ∀ z ∈ preprocessedPoints A zeta (zeta * Ext.ofBase (twoAdicGen logN)),
      Ext.OutsideBase z := by
    intro z hz'
    unfold preprocessedPoints at hz'
    split at hz'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz'
      rcases hz' with rfl | rfl
      · exact hz
      · exact hw
    · rw [List.mem_singleton.mp hz']; exact hz
  have htpts : ∀ z ∈ tracePoints A zeta (zeta * Ext.ofBase (twoAdicGen logN)),
      Ext.OutsideBase z := by
    intro z hz'
    unfold tracePoints at hz'
    split at hz'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz'
      rcases hz' with rfl | rfl
      · exact hz
      · exact hw
    · rw [List.mem_singleton.mp hz']; exact hz
  have hprepRounds : List.Forall₂ (RoundRel h)
      (xprep.map fun (pext, pc) ↦
        (pc, [(pext, preprocessedPoints A zeta (zeta * Ext.ofBase (twoAdicGen logN)))])).toList
      (yprep.map fun (pext, pc) ↦
        (pc, [(pext, preprocessedPoints A zeta
          (zeta * Ext.ofBase (twoAdicGen logN)))])).toList := by
    cases hprep with
    | none => exact .nil
    | @some a b hr => exact .cons ⟨hr.2, .cons ⟨hr.1, rfl⟩ .nil⟩ .nil
  have hmapEq {γ : Type} (v : γ) : xprep.map (fun _ ↦ v) = yprep.map (fun _ ↦ v) := by
    cases hprep with
    | none => rfl
    | some _ => rfl
  unfold openAndAssemble
  refine RelM.bind (openPcs_refines hA h P ?_ ?_) fun _ _ hx ↦ hx ▸ ?_
  · exact .cons ⟨hct, .cons ⟨hext, rfl⟩ .nil⟩
      (.cons ⟨hqc, forall₂_map (fun _ _ hm ↦ ⟨hm, rfl⟩) hch⟩ hprepRounds)
  · intro r hr x hx
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
    · simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨hextOk, htpts⟩
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      refine ⟨hchOk m hm, fun z hz' ↦ ?_⟩
      simp only [List.mem_singleton] at hz'
      rw [hz']; exact hz
    · obtain ⟨⟨pext, pc⟩, hy, rfl⟩ := Option.mem_map.mp (Option.mem_toList.mp hr)
      simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨hprepOk _ hy, hpts⟩
  · rw [h.root hct, h.root hqc]
    simp only [hmapEq]
    exact RelM.pure rfl

/-- **A refining backend proves what the specification proves**, for inputs of the prover's
shapes, when the specification's opening point `ζ` lies outside the base field. -/
theorem proveWith_refines (hA : DomainsAddressable F EF) (h : Refines B) {P : Params} {A : Air F}
    {logN : Nat} {t : B.Trace} {trace : Array F} (pis : List F) (ht : h.RT t trace)
    (hin : InputOk EF P A logN trace)
    (hz : Ext.OutsideBase (outOfDomainPoint EF P A logN trace pis)) :
    proveWith B P A logN t pis = prove EF P A logN trace pis := by
  unfold prove proveWith
  dsimp only
  rw [h.transcript, RelM.run_bind, RelM.run_bind]
  obtain ⟨hR, he⟩ := commitAndSample_refines h pis ht hin (specBackend EF).transcript
  rw [he]
  obtain ⟨hprep, hprepOk⟩ := setupWith_refines h hin
  exact (openAndAssemble_refines hA h P (by have := hin.twoAdic; omega) hprep
    (fun y hy ↦ (hprepOk y hy).1) hR hz _).1

end CompStark.Stark
