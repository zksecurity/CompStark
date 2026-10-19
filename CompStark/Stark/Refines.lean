/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Refines
public import CompStark.Stark.Prover
public import CompStark.Stark.Fast.Norm

/-! # Provers on refining backends

A backend that refines the specification (`Fri.Refines`) proves what the specification proves
(`proveWith_refines`), for a trace of the AIR's shape within KoalaBear's two-adic subgroups whose
buffers are addressable, when the opening point `ζ` of the specification's proof lies outside the
base field.
-/

@[expose] public section
namespace CompStark.Stark
open CompStark.Fri CompStark.KoalaBear

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4

theorem size_chunkValues (qs : Array EF) (stride c n : Nat) :
    (chunkValues qs stride c n).size = 4 * n := by
  simp only [chunkValues, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, pure_bind, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  show Array.size (List.foldl _ _ _) = _
  suffices h : ∀ (l : List Nat) (init : Array F), (l.foldl (fun out r ↦
      ((((out.push (qs.getD (r * stride + c) 0).c0).push (qs.getD (r * stride + c) 0).c1).push
        (qs.getD (r * stride + c) 0).c2).push (qs.getD (r * stride + c) 0).c3)) init).size =
      init.size + 4 * l.length by
    rw [h, List.length_range', Array.emptyWithCapacity_eq, Array.size_empty, Nat.zero_add]
  intro l
  induction l with
  | nil => intro _; rfl
  | cons r l ih =>
    intro init
    rw [List.foldl_cons, ih]
    simp only [Array.size_push, List.length_cons]
    omega

theorem addressable_mono {m n : Nat} (h : m ≤ n) (hn : Addressable n) : Addressable m := by
  unfold Addressable at *; omega

theorem outsideBase_mul_ofBase {z : EF} (hz : Ext.OutsideBase z) {x : F} (hx : x ≠ 0) :
    Ext.OutsideBase (z * Ext.ofBase x) := by
  have e1 : (z * Ext.ofBase x).c1 = z.c1 * x := by
    rw [Norm.mul_c1]; simp only [Ext.ofBase, KoalaBear.Fast.Ext4.ofBase]; ring
  have e2 : (z * Ext.ofBase x).c2 = z.c2 * x := by
    rw [Norm.mul_c2]; simp only [Ext.ofBase, KoalaBear.Fast.Ext4.ofBase]; ring
  have e3 : (z * Ext.ofBase x).c3 = z.c3 * x := by
    rw [Norm.mul_c3]; simp only [Ext.ofBase, KoalaBear.Fast.Ext4.ofBase]; ring
  unfold Ext.OutsideBase at *
  rw [e1, e2, e3]
  rcases hz with h | h | h
  · exact Or.inl (mul_ne_zero h hx)
  · exact Or.inr (Or.inl (mul_ne_zero h hx))
  · exact Or.inr (Or.inr (mul_ne_zero h hx))

/-- What the prover assumes of its input: the trace has `2 ^ logN` rows of the AIR's width, a
positive width, the AIR reads only its columns, the extension stays within the two-adic subgroups
and the quotient fits the blowup, and the extended trace and quotient are addressable. -/
structure InputOk (P : Params) (A : Air) (logN : Nat) (trace : Array F) : Prop where
  trace : trace.size = 2 ^ logN * A.width
  width : 0 < A.width
  cols : A.ColsInWidth
  twoAdic : logN + P.logBlowup ≤ 24
  chunks : A.logQuotientChunks ≤ P.logBlowup
  mem : Addressable (2 ^ (logN + P.logBlowup) * (A.width + 4 * 2 ^ A.logQuotientChunks))

variable {B : Backend}

theorem commitAndSample_refines (h : Refines B) {P : Params} {A : Air} {logN : Nat}
    {trace : Array F} (pis : List F) (hin : InputOk P A logN trace) :
    RelM (fun x y ↦ h.RM x.1 y.1 ∧ h.RC x.2.1 y.2.1 ∧ List.Forall₂ h.RM x.2.2.1 y.2.2.1 ∧
        h.RC x.2.2.2.1 y.2.2.2.1 ∧ x.2.2.2.2 = y.2.2.2.2 ∧ MatOk y.1 ∧ ∀ m ∈ y.2.2.1, MatOk m)
      (commitAndSample B P A logN trace pis) (commitAndSample Backend.spec P A logN trace pis) := by
  obtain ⟨htrace, hw, hcols, hlog, hchunks, hmem⟩ := hin
  have hH : 2 ^ (logN + P.logBlowup) ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hlog
  have hmw : Addressable (2 ^ (logN + P.logBlowup) * A.width) :=
    addressable_mono (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)) hmem
  have hmq : Addressable (2 ^ (logN + P.logBlowup) * (4 * 2 ^ A.logQuotientChunks)) :=
    addressable_mono (Nat.mul_le_mul_left _ (Nat.le_add_left _ _)) hmem
  have h1 : 1 ≤ 2 ^ A.logQuotientChunks := Nat.one_le_two_pow
  have hm4 : Addressable (2 ^ (logN + P.logBlowup) * 4) :=
    addressable_mono (Nat.mul_le_mul_left _ (show 4 ≤ 4 * 2 ^ A.logQuotientChunks by omega)) hmq
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
  refine RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦
    RelM.bind_eq fun _ ↦ RelM.bind_eq fun alpha ↦ ?_
  have hq : 2 ^ (logN + A.logQuotientChunks) ≤ (ldeRef logN P.logBlowup gen A.width trace).height :=
    heh ▸ Nat.pow_le_pow_right (by decide) (by omega)
  rw [h.quotient _ _ _ _ _ hext hextOk hq (hew ▸ hcols)]
  generalize Backend.spec.quotient _ _ _ _ _ _ = qs
  -- The quotient's chunks.
  have hchOk : ∀ c, MatOk (ldeRef logN P.logBlowup
      (gen * (gen * powF (twoAdicGen (logN + A.logQuotientChunks)) c)⁻¹) 4
      (chunkValues qs (2 ^ A.logQuotientChunks) c (2 ^ logN))) := fun c ↦ by
    obtain ⟨h1, h2, h3⟩ := shape_ldeRef logN P.logBlowup
      (gen * (gen * powF (twoAdicGen (logN + A.logQuotientChunks)) c)⁻¹) 4
      (chunkValues qs (2 ^ A.logQuotientChunks) c (2 ^ logN))
    exact ⟨by rw [h1]; decide, ⟨_, hlog, h2⟩, by rw [h3, h1, h2],
      by rw [h1, h2, Nat.mul_comm]; exact hm4⟩
  have hch : List.Forall₂ h.RM
      ((List.range (2 ^ A.logQuotientChunks)).map fun c ↦
        B.lde logN P.logBlowup (gen * (gen * powF (twoAdicGen (logN + A.logQuotientChunks)) c)⁻¹) 4
          (chunkValues qs (2 ^ A.logQuotientChunks) c (2 ^ logN)))
      ((List.range (2 ^ A.logQuotientChunks)).map fun c ↦
        Backend.spec.lde logN P.logBlowup
          (gen * (gen * powF (twoAdicGen (logN + A.logQuotientChunks)) c)⁻¹) 4
          (chunkValues qs (2 ^ A.logQuotientChunks) c (2 ^ logN))) :=
    forall₂_map (fun _ _ hc ↦ hc ▸ h.lde _ _ _ _ _ (by rw [size_chunkValues, Nat.mul_comm])
      hlog hm4) (List.forall₂_same.2 fun _ _ ↦ rfl)
  have hall : ∀ m ∈ ((List.range (2 ^ A.logQuotientChunks)).map fun c ↦
      Backend.spec.lde logN P.logBlowup
        (gen * (gen * powF (twoAdicGen (logN + A.logQuotientChunks)) c)⁻¹) 4
        (chunkValues qs (2 ^ A.logQuotientChunks) c (2 ^ logN))), MatOk m ∧
        m.height = 2 ^ (logN + P.logBlowup) := fun m hm ↦ by
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hm
    exact ⟨hchOk c, (shape_ldeRef ..).2.1⟩
  have hwsum : ∀ (l : List Nat) (acc : Nat), (l.map fun c ↦ Backend.spec.lde logN P.logBlowup
      (gen * (gen * powF (twoAdicGen (logN + A.logQuotientChunks)) c)⁻¹) 4
      (chunkValues qs (2 ^ A.logQuotientChunks) c (2 ^ logN))).foldl (· + ·.width) acc =
      acc + 4 * l.length := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons c l ih =>
      intro acc
      rw [List.map_cons, List.foldl_cons, ih, List.length_cons]
      show acc + 4 + 4 * l.length = _
      omega
  have hqc := h.commit hch ⟨_, List.ne_nil_of_length_pos (by
    rw [List.length_map, List.length_range]; exact Nat.two_pow_pos _), hall, by
    have e := hwsum (List.range (2 ^ A.logQuotientChunks)) 0
    rw [List.length_range, Nat.zero_add] at e
    exact e.symm ▸ hmq⟩
  rw [h.root hqc]
  refine RelM.bind_eq fun _ ↦ RelM.bind_eq fun zeta ↦ ?_
  exact RelM.pure ⟨hext, hct, hch, hqc, rfl, hextOk, fun m hm ↦ (hall m hm).1⟩

/-- The openings of related commitments at an opening point outside the base field are the
specification's. -/
theorem openAndAssemble_refines (h : Refines B) (P : Params) {logN : Nat}
    (hlog : logN ≤ 24) {x : B.M × B.C × List B.M × B.C × EF}
    {y : Backend.spec.M × Backend.spec.C × List Backend.spec.M × Backend.spec.C × EF}
    (hR : h.RM x.1 y.1 ∧ h.RC x.2.1 y.2.1 ∧ List.Forall₂ h.RM x.2.2.1 y.2.2.1 ∧
      h.RC x.2.2.2.1 y.2.2.2.1 ∧ x.2.2.2.2 = y.2.2.2.2 ∧ MatOk y.1 ∧ ∀ m ∈ y.2.2.1, MatOk m)
    (hz : Ext.OutsideBase y.2.2.2.2) :
    RelM Eq (openAndAssemble B P logN x) (openAndAssemble Backend.spec P logN y) := by
  obtain ⟨ext, traceC, chunks, quotC, zeta⟩ := x
  obtain ⟨ext', traceC', chunks', quotC', zeta'⟩ := y
  obtain ⟨hext, hct, hch, hqc, hzz, hextOk, hchOk⟩ := hR
  dsimp only at hext hct hch hqc hzz hextOk hchOk hz
  subst hzz
  unfold openAndAssemble
  refine RelM.bind (openPcs_refines h P ?_ ?_) fun _ _ hx ↦ hx ▸ ?_
  · exact .cons ⟨hct, .cons ⟨hext, rfl⟩ .nil⟩
      (.cons ⟨hqc, forall₂_map (fun _ _ hm ↦ ⟨hm, rfl⟩) hch⟩ .nil)
  · have hw := outsideBase_mul_ofBase hz (twoAdicGen_ne_zero logN hlog)
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
theorem proveWith_refines (h : Refines B) {P : Params} {A : Air} {logN : Nat} {trace : Array F}
    (pis : List F) (hin : InputOk P A logN trace)
    (hz : Ext.OutsideBase (zetaOf P A logN trace pis)) :
    proveWith B P A logN trace pis = prove P A logN trace pis := by
  unfold prove proveWith
  rw [h.transcript, RelM.run_bind, RelM.run_bind]
  obtain ⟨hR, ht⟩ := commitAndSample_refines h pis hin Backend.spec.transcript
  rw [ht]
  exact (openAndAssemble_refines h P (by have := hin.twoAdic; omega) hR hz _).1

end CompStark.Stark
