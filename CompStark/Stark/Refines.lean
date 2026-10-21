/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Refines
public import CompStark.Stark.Prover

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

theorem size_chunkValues {K : Type} [Challenge F K] (qs : Array K) (stride c n : Nat) :
    (chunkValues qs stride c n).size = Challenge.d K * n := by
  simp only [chunkValues, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, pure_bind, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  show Array.size (List.foldl _ _ _) = _
  suffices h : ∀ (l : List Nat) (init : Array F), (l.foldl (fun out r ↦
      out ++ (Ext.coeffs (qs.getD (r * stride + c) 0)).toArray) init).size =
      init.size + Challenge.d K * l.length by
    rw [h, List.length_range', Array.emptyWithCapacity_eq, Array.size_empty, Nat.zero_add]
  intro l
  induction l with
  | nil => intro _; rfl
  | cons r l ih =>
    intro init
    have h4 : (Ext.coeffs (qs.getD (r * stride + c) 0)).length = Challenge.d K :=
      Challenge.length_coeffs _
    rw [List.foldl_cons, ih]
    simp only [Array.size_append, List.size_toArray, h4, List.length_cons]
    rw [Nat.mul_succ]
    omega

theorem addressable_mono {m n : Nat} (h : m ≤ n) (hn : Addressable n) : Addressable m := by
  unfold Addressable at *; omega

/-- The shapes the fast prover supports: a trace and an AIR within the base field's two-adic
subgroups whose extension over `EF` fits machine-word indices. -/
structure InputOk (EF : Type) [Challenge F EF] (P : Params) (A : Air F) (logN : Nat)
    (trace : Array F) : Prop where
  /-- The trace has `2 ^ logN` rows of the AIR's width. -/
  trace : trace.size = 2 ^ logN * A.width
  /-- The AIR has a column. -/
  width : 0 < A.width
  /-- The constraints read only the AIR's columns. -/
  cols : A.ColsInWidth
  /-- The extended trace domain is a two-adic subgroup of the base field. -/
  twoAdic : logN + P.logBlowup ≤ twoAdicity F
  /-- The quotient's chunks fit the blowup. -/
  chunks : A.logQuotientChunks ≤ P.logBlowup
  /-- The extended trace and quotient are addressable by `USize` word indices. -/
  mem : Addressable (2 ^ (logN + P.logBlowup) *
    (A.width + Challenge.d EF * 2 ^ A.logQuotientChunks))

variable [Poseidon2Field F] {EF : Type} [Challenge F EF] {B : Backend F EF 24}

theorem commitAndSample_refines (h : Refines B) {P : Params} {A : Air F} {logN : Nat}
    {trace : Array F} (pis : List F) (hin : InputOk EF P A logN trace) :
    RelM (fun x y ↦ h.RM x.1 y.1 ∧ h.RC x.2.1 y.2.1 ∧ List.Forall₂ h.RM x.2.2.1 y.2.2.1 ∧
        h.RC x.2.2.2.1 y.2.2.2.1 ∧ x.2.2.2.2 = y.2.2.2.2 ∧ MatOk y.1 ∧ ∀ m ∈ y.2.2.1, MatOk m)
      (commitAndSample B P A logN trace pis)
          (commitAndSample (specBackend EF) P A logN trace pis) := by
  obtain ⟨htrace, hw, hcols, hlog, hchunks, hmem⟩ := hin
  have hmw : Addressable (2 ^ (logN + P.logBlowup) * A.width) :=
    addressable_mono (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)) hmem
  have hmq : Addressable (2 ^ (logN + P.logBlowup) * (Challenge.d EF * 2 ^ A.logQuotientChunks)) :=
    addressable_mono (Nat.mul_le_mul_left _ (Nat.le_add_left _ _)) hmem
  have h1 : 1 ≤ 2 ^ A.logQuotientChunks := Nat.one_le_two_pow
  have hm4 : Addressable (2 ^ (logN + P.logBlowup) * Challenge.d EF) :=
    addressable_mono (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ h1)) hmq
  -- The extended trace.
  obtain ⟨hew, heh, hev⟩ := shape_ldeRef logN P.logBlowup gen A.width trace
  have hextOk : MatOk (ldeRef logN P.logBlowup gen A.width trace) :=
    ⟨by rw [hew]; exact hw, ⟨_, hlog, heh⟩, by rw [hev, hew, heh],
      by rw [hew, heh, Nat.mul_comm]; exact hmw⟩
  have hext := h.lde logN P.logBlowup gen A.width trace htrace hlog hmw
  have hct := h.commit (.cons hext .nil) ⟨_, List.cons_ne_nil _ _,
    fun m hm ↦ by obtain rfl := List.mem_singleton.mp hm; exact ⟨hextOk, heh⟩,
    by show Addressable (_ * (0 + A.width)); rw [Nat.zero_add]; exact hmw⟩
  unfold commitAndSample
  dsimp only
  rw [h.root hct]
  refine RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦
    RelM.bind_eq fun alpha ↦ ?_
  have hq : 2 ^ (logN + A.logQuotientChunks) ≤ (ldeRef logN P.logBlowup gen A.width trace).height :=
    heh ▸ Nat.pow_le_pow_right (by decide) (by omega)
  rw [h.quotient _ _ _ _ _ hext hextOk hq (hew ▸ hcols)]
  generalize (specBackend EF).quotient _ _ _ _ _ _ = qs
  -- The quotient's chunks.
  have hchOk : ∀ c, MatOk (ldeRef logN P.logBlowup
      (gen * (gen * powF (twoAdicGen (logN + A.logQuotientChunks)) c)⁻¹) (Challenge.d EF)
      (chunkValues qs (2 ^ A.logQuotientChunks) c (2 ^ logN))) := fun c ↦ by
    obtain ⟨h1, h2, h3⟩ := shape_ldeRef logN P.logBlowup
      (gen * (gen * powF (twoAdicGen (logN + A.logQuotientChunks)) c)⁻¹) (Challenge.d EF)
      (chunkValues qs (2 ^ A.logQuotientChunks) c (2 ^ logN))
    exact ⟨by rw [h1]; exact (Challenge.params EF).d_pos, ⟨_, hlog, h2⟩, by rw [h3, h1, h2],
      by rw [h1, h2, Nat.mul_comm]; exact hm4⟩
  have hch : List.Forall₂ h.RM
      ((List.range (2 ^ A.logQuotientChunks)).map fun c ↦
        B.lde logN P.logBlowup (gen * (gen * powF (twoAdicGen (logN + A.logQuotientChunks)) c)⁻¹)
          (Challenge.d EF)
          (chunkValues qs (2 ^ A.logQuotientChunks) c (2 ^ logN)))
      ((List.range (2 ^ A.logQuotientChunks)).map fun c ↦
        (specBackend EF).lde logN P.logBlowup
          (gen * (gen * powF (twoAdicGen (logN + A.logQuotientChunks)) c)⁻¹) (Challenge.d EF)
          (chunkValues qs (2 ^ A.logQuotientChunks) c (2 ^ logN))) :=
    forall₂_map (fun _ _ hc ↦ hc ▸ h.lde _ _ _ _ _ (by rw [size_chunkValues, Nat.mul_comm])
      hlog hm4) (List.forall₂_same.2 fun _ _ ↦ rfl)
  have hall : ∀ m ∈ ((List.range (2 ^ A.logQuotientChunks)).map fun c ↦
      (specBackend EF).lde logN P.logBlowup
        (gen * (gen * powF (twoAdicGen (logN + A.logQuotientChunks)) c)⁻¹) (Challenge.d EF)
        (chunkValues qs (2 ^ A.logQuotientChunks) c (2 ^ logN))), MatOk m ∧
        m.height = 2 ^ (logN + P.logBlowup) := fun m hm ↦ by
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hm
    exact ⟨hchOk c, (shape_ldeRef ..).2.1⟩
  have hwsum : ∀ (l : List Nat) (acc : Nat),
      (l.map fun c ↦ (specBackend EF).lde logN P.logBlowup
          (gen * (gen * powF (twoAdicGen (logN + A.logQuotientChunks)) c)⁻¹) (Challenge.d EF)
      (chunkValues qs (2 ^ A.logQuotientChunks) c (2 ^ logN))).foldl (· + ·.width) acc =
      acc + Challenge.d EF * l.length := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons c l ih =>
      intro acc
      rw [List.map_cons, List.foldl_cons, ih, List.length_cons]
      show acc + Challenge.d EF + Challenge.d EF * l.length = _
      rw [Nat.mul_succ]
      omega
  have hqc := h.commit hch ⟨_, List.ne_nil_of_length_pos (by
    rw [List.length_map, List.length_range]; exact Nat.two_pow_pos _), hall, by
    have e := hwsum (List.range (2 ^ A.logQuotientChunks)) 0
    rw [List.length_range, Nat.zero_add] at e
    exact e.symm ▸ hmq⟩
  rw [h.root hqc]
  refine RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦ ?_
  exact RelM.pure ⟨hext, hct, hch, hqc, rfl, hextOk, fun m hm ↦ (hall m hm).1⟩

/-- The openings of related commitments at an opening point outside the base field are the
specification's. -/
theorem openAndAssemble_refines (hA : DomainsAddressable F EF) (h : Refines B) (P : Params)
    {logN : Nat} (hlog : logN ≤ twoAdicity F) {x : B.M × B.C × List B.M × B.C × EF × F}
    {y : (specBackend EF).M × (specBackend EF).C × List (specBackend EF).M ×
        (specBackend EF).C × EF × F}
    (hR : h.RM x.1 y.1 ∧ h.RC x.2.1 y.2.1 ∧ List.Forall₂ h.RM x.2.2.1 y.2.2.1 ∧
      h.RC x.2.2.2.1 y.2.2.2.1 ∧ x.2.2.2.2 = y.2.2.2.2 ∧ MatOk y.1 ∧ ∀ m ∈ y.2.2.1, MatOk m)
    (hz : Ext.OutsideBase y.2.2.2.2.1) :
    RelM Eq (openAndAssemble B P logN x) (openAndAssemble (specBackend EF) P logN y) := by
  obtain ⟨ext, traceC, chunks, quotC, zeta, ow⟩ := x
  obtain ⟨ext', traceC', chunks', quotC', zeta', ow'⟩ := y
  obtain ⟨hext, hct, hch, hqc, hzz, hextOk, hchOk⟩ := hR
  dsimp only at hext hct hch hqc hzz hextOk hchOk hz
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hzz
  unfold openAndAssemble
  refine RelM.bind (openPcs_refines hA h P ?_ ?_) fun _ _ hx ↦ hx ▸ ?_
  · exact .cons ⟨hct, .cons ⟨hext, rfl⟩ .nil⟩
      (.cons ⟨hqc, forall₂_map (fun _ _ hm ↦ ⟨hm, rfl⟩) hch⟩ .nil)
  · have hw := Ext.outsideBase_mul_ofBase hz (BaseField.twoAdicGen_ne_zero logN hlog)
    intro r hr x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [List.mem_singleton] at hx
      subst hx
      refine ⟨hextOk, fun z hz' ↦ ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz'
      rcases hz' with rfl | rfl
      · exact hz
      · exact hw
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      refine ⟨hchOk m hm, fun z hz' ↦ ?_⟩
      simp only [List.mem_singleton] at hz'
      rw [hz']; exact hz
  · rw [h.root hct, h.root hqc]
    exact RelM.pure rfl

/-- **A refining backend proves what the specification proves**, for inputs of the prover's
shapes, when the specification's opening point `ζ` lies outside the base field. -/
theorem proveWith_refines (hA : DomainsAddressable F EF) (h : Refines B) {P : Params} {A : Air F}
    {logN : Nat} {trace : Array F} (pis : List F) (hin : InputOk EF P A logN trace)
    (hz : Ext.OutsideBase (outOfDomainPoint EF P A logN trace pis)) :
    proveWith B P A logN trace pis = prove EF P A logN trace pis := by
  unfold prove proveWith
  rw [h.transcript, RelM.run_bind, RelM.run_bind]
  obtain ⟨hR, ht⟩ := commitAndSample_refines h pis hin (specBackend EF).transcript
  rw [ht]
  exact (openAndAssemble_refines hA h P (by have := hin.twoAdic; omega) hR hz _).1

end CompStark.Stark
