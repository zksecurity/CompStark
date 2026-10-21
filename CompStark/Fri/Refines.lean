/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Shapes
public import CompStark.Plonky3.Prover
public import CompStark.KoalaBear.Poseidon2
public import CompStark.KoalaBear.Challenge
public import Mathlib.Data.List.Forall2

/-! # Backends that refine the specification

`Refines B` relates a backend's matrices, commitments and vectors to the specification's, and
asks every kernel to map related inputs to related outputs, with equal plain results. Under it
the FRI opening `openPcs` of related rounds gives the specification's opened values and proof
(`openPcs_refines`).
-/

@[expose] public section
namespace CompStark.Fri
open CompStark.Stark CompStark.KoalaBear

local notation "F" => _root_.KoalaBear.Fast.Field
local notation "EF" => _root_.KoalaBear.Fast.Ext4

/-- The backend `B` computes the specification's functions on the inputs the prover gives them,
through relations `RM`, `RC`, `RV` between its matrices, commitments and vectors and the
specification's. -/
structure Refines (B : Backend F EF 24) where
  RM : B.M → (specBackend EF).M → Prop
  RC : B.C → (specBackend EF).C → Prop
  RV : B.V → (specBackend EF).V → Prop
  transcript : B.transcript = (specBackend EF).transcript
  lde : ∀ logH bits shift w m, m.size = 2 ^ logH * w → logH + bits ≤ 24 →
    Addressable (2 ^ (logH + bits) * w) →
    RM (B.lde logH bits shift w m) ((specBackend EF).lde logH bits shift w m)
  commit : ∀ {ms ss}, List.Forall₂ RM ms ss → CommitOk ss →
    RC (B.commit ms) ((specBackend EF).commit ss)
  root : ∀ {c s}, RC c s → B.root c = (specBackend EF).root s
  openAt : ∀ {c s} i, RC c s → B.openAt c i = (specBackend EF).openAt s i
  logHeight : ∀ {c s}, RC c s → B.logHeight c = (specBackend EF).logHeight s
  quotient : ∀ A pis d l {m s} alpha, RM m s → MatOk s → 2 ^ (d + l) ≤ s.height →
    (∀ c ∈ A.constraints, c.colsBelow s.width) →
    B.quotient A pis d l m alpha = (specBackend EF).quotient A pis d l s alpha
  openedAt : ∀ b zs {m s}, RM m s → MatOk s → (∀ z ∈ zs, Ext.OutsideBase z) →
    B.openedAt b m zs = (specBackend EF).openedAt b s zs
  toArray : ∀ {v a}, RV v a → a.size ≤ 2 ^ 24 → B.toArray v = (specBackend EF).toArray a
  ofArray : ∀ a, RV (B.ofArray a) ((specBackend EF).ofArray a)
  size : ∀ {v a}, RV v a → B.size v = (specBackend EF).size a
  reduce : ∀ alpha {items sitems},
    List.Forall₂ (fun x y ↦ RM x.1 y.1 ∧ x.2 = y.2) items sitems →
    (∀ x ∈ sitems, MatOk x.1 ∧ ∀ p ∈ x.2, Ext.OutsideBase p.1) →
    List.Forall₂ (fun x y ↦ x.1 = y.1 ∧ RV x.2 y.2) (B.reduce alpha items)
      ((specBackend EF).reduce alpha sitems)
  fold2 : ∀ beta k {v a}, RV v a → a.size = 2 ^ (k + 1) → k < 24 →
    RV (B.fold2 v beta k) ((specBackend EF).fold2 a beta k)
  addScaled : ∀ x {v a w b}, RV v a → RV w b → a.size = b.size → a.size ≤ 2 ^ 24 →
    RV (B.addScaled v w x) ((specBackend EF).addScaled a b x)
  leaves : ∀ k {v a}, RV v a → a.size ≤ 2 ^ 24 → RM (B.leaves k v) ((specBackend EF).leaves k a)

/-- Prover computations that, from every transcript, return related results and the same
transcript. -/
def RelM {α β : Type} (R : α → β → Prop) (x : PM F 24 α) (y : PM F 24 β) : Prop :=
  ∀ t, R (x.run t).1 (y.run t).1 ∧ (x.run t).2 = (y.run t).2

namespace RelM

variable {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}

theorem run_bind {x : PM F 24 α} {f : α → PM F 24 γ} (t : Transcript F 24) :
    (x >>= f).run t = (f (x.run t).1).run (x.run t).2 := rfl

theorem pure {a : α} {b : β} (h : R a b) : RelM R (Pure.pure a) (Pure.pure b) :=
  fun _ ↦ ⟨h, rfl⟩

theorem refl (x : PM F 24 α) : RelM Eq x x := fun _ ↦ ⟨rfl, rfl⟩

theorem bind {x : PM F 24 α} {y : PM F 24 β} {f : α → PM F 24 γ} {g : β → PM F 24 δ}
    (hx : RelM R x y)
    (hf : ∀ a b, R a b → RelM S (f a) (g b)) : RelM S (x >>= f) (y >>= g) := by
  intro t
  obtain ⟨h1, h2⟩ := hx t
  rw [run_bind, run_bind, h2]
  exact hf _ _ h1 _

theorem bind_eq {x : PM F 24 α} {f : α → PM F 24 γ} {g : α → PM F 24 δ}
    (hf : ∀ a, RelM S (f a) (g a)) : RelM S (x >>= f) (x >>= g) :=
  bind (refl x) fun a _ h ↦ h ▸ hf a

theorem mapM {f : α → PM F 24 γ} {g : β → PM F 24 δ} (hf : ∀ a b, R a b → RelM S (f a) (g b)) :
    ∀ {xs ys}, List.Forall₂ R xs ys → RelM (List.Forall₂ S) (xs.mapM f) (ys.mapM g)
  | [], [], .nil => by
    simp only [List.mapM_nil]
    exact pure .nil
  | _ :: _, _ :: _, .cons h hs => by
    simp only [List.mapM_cons]
    exact bind (hf _ _ h) fun _ _ h1 ↦ bind (mapM hf hs) fun _ _ h2 ↦ pure (.cons h1 h2)

theorem imp {x : PM F 24 α} {y : PM F 24 β} {R' : α → β → Prop} (h : ∀ a b, R a b → R' a b)
    (hx : RelM R x y) : RelM R' x y :=
  fun t ↦ ⟨h _ _ (hx t).1, (hx t).2⟩

end RelM

theorem forall₂_map_eq {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (hfg : ∀ a b, R a b → f a = g b) : ∀ {xs ys}, List.Forall₂ R xs ys → xs.map f = ys.map g
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
    simp only [List.map_cons, hfg _ _ h, forall₂_map_eq hfg hs]

theorem forall₂_map {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {f : α → γ}
    {g : β → δ} (hfg : ∀ a b, R a b → S (f a) (g b)) :
    ∀ {xs ys}, List.Forall₂ R xs ys → List.Forall₂ S (xs.map f) (ys.map g)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs => .cons (hfg _ _ h) (forall₂_map hfg hs)

/-- Commit phases with equal plain parts and related commitments. -/
structure CPRel {C D : Type} (RC : C → D → Prop) (cp : CommitPhase F EF C)
    (cs : CommitPhase F EF D) :
    Prop where
  commits : cp.commits = cs.commits
  data : List.Forall₂ RC cp.data cs.data
  witnesses : cp.witnesses = cs.witnesses
  arities : cp.arities = cs.arities
  finalPoly : cp.finalPoly = cs.finalPoly

variable {B : Backend F EF 24}

/-- A vector of the commit phase: empty, or `2 ^ s` values within the two-adic subgroups. -/
def ShapeOk (a : Array EF) : Prop := a.size = 0 ∨ ∃ s ≤ 24, a.size = 2 ^ s

theorem shapeOk_le {a : Array EF} (h : ShapeOk a) : a.size ≤ 2 ^ 24 := by
  rcases h with h | ⟨s, hs, h⟩
  · omega
  · rw [h]; exact Nat.pow_le_pow_right (by decide) hs

/-- The leaves of a commit-phase round are a matrix of the prover's shape. -/
theorem commitOk_leaves (a : Array EF) (s la : Nat) (hs : s ≤ 24) (ha : a.size = 2 ^ s)
    (hla : la ≤ s) : CommitOk [(specBackend EF).leaves (2 ^ la) a] := by
  have hd : a.size / 2 ^ la = 2 ^ (s - la) := by
    rw [ha, Nat.pow_div hla (by decide)]
  have hsz : 2 ^ la * 2 ^ (s - la) = 2 ^ s := by rw [← Nat.pow_add, Nat.add_sub_cancel' hla]
  have hadd : Addressable (4 * 2 ^ la * 2 ^ (s - la)) := addressable_of_le (by
    rw [Nat.mul_assoc, hsz]
    have : 2 ^ s ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hs
    omega)
  refine ⟨2 ^ (s - la), List.cons_ne_nil _ _, fun m hm ↦ ?_, ?_⟩
  · obtain rfl := List.mem_singleton.mp hm
    refine ⟨⟨by show 0 < 4 * 2 ^ la; positivity,
        ⟨s - la, by rw [KoalaBear.twoAdicity_eq]; omega, hd⟩,
      ?_, ?_⟩, hd⟩
    · show (a.flatMap fun x ↦ (Ext.coeffs x).toArray).size = 4 * 2 ^ la * (a.size / 2 ^ la)
      rw [size_flatMap_coeffs, Mont32.d_ext4, hd, Nat.mul_assoc, hsz, ha]
    · show Addressable (4 * 2 ^ la * (a.size / 2 ^ la))
      rw [hd]; exact hadd
  · show Addressable (2 ^ (s - la) * (0 + 4 * 2 ^ la))
    rw [Nat.zero_add, Nat.mul_comm]; exact hadd

theorem commitRounds_refines (h : Refines B) (P : Params) (fuel : Nat) :
    ∀ {folded a rest as cp cs}, h.RV folded a → ShapeOk a → List.Forall₂ h.RV rest as →
      (∀ x ∈ as, ShapeOk x) → CPRel h.RC cp cs →
      RelM (fun p q ↦ h.RV p.1 q.1 ∧ ShapeOk q.1 ∧ CPRel h.RC p.2 q.2)
        (commitRounds B P fuel folded rest cp) (commitRounds (specBackend EF) P fuel a as cs) := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ hf hfs _ _ hc; exact RelM.pure ⟨hf, hfs, hc⟩
  | succ fuel ih =>
    intro folded a rest as cp cs hf hfs hr hrs hc
    rw [commitRounds, commitRounds, h.size hf]
    split
    · exact RelM.pure ⟨hf, hfs, hc⟩
    rename_i hgt
    obtain ⟨s, hs, ha⟩ : ∃ s ≤ 24, a.size = 2 ^ s := by
      rcases hfs with h0 | h0
      · exact absurd (by show a.size ≤ _; rw [h0]; exact Nat.zero_le _) hgt
      · exact h0
    have hhead : Option.map (fun x ↦ (B.size x).log2) rest.head? =
        Option.map (fun x ↦ ((specBackend EF).size x).log2) as.head? := by
      cases hr with
      | nil => simp only [List.head?_nil, Option.map_none]
      | cons hv _ => rw [List.head?_cons, List.head?_cons, Option.map_some, Option.map_some,
          h.size hv]
    dsimp only
    rw [hhead]
    have hla := logArityFor_le P ((specBackend EF).size a).log2
      (Option.map (fun x ↦ ((specBackend EF).size x).log2) as.head?)
    generalize logArityFor P ((specBackend EF).size a).log2
      (Option.map (fun x ↦ ((specBackend EF).size x).log2) as.head?) = la at hla ⊢
    have hlog : ((specBackend EF).size a).log2 = s := by
      show a.size.log2 = s; rw [ha, Nat.log2_two_pow]
    rw [hlog] at hla
    have ha24 : a.size ≤ 2 ^ 24 := shapeOk_le (Or.inr ⟨s, hs, ha⟩)
    have hcm := h.commit (.cons (h.leaves (2 ^ la) hf ha24) .nil)
      (commitOk_leaves a s la hs ha hla)
    rw [h.root hcm]
    refine RelM.bind_eq fun _ ↦ RelM.bind_eq fun w ↦ RelM.bind_eq fun beta ↦ ?_
    have hrows : (specBackend EF).size a / 2 ^ la = 2 ^ (s - la) := by
      show a.size / 2 ^ la = _; rw [ha, Nat.pow_div hla (by decide)]
    generalize hfB : (if la = 1 then _ else _ : B.V) = fB
    generalize hfS : (if la = 1 then _ else _ : (specBackend EF).V) = fS
    have hfold : h.RV fB fS ∧ ShapeOk fS := by
      subst hfB hfS
      split
      · rename_i h1
        subst h1
        have hk : ((specBackend EF).size a / 2 ^ 1).log2 = s - 1 := by
          rw [hrows, Nat.log2_two_pow]
        rw [hk]
        refine ⟨h.fold2 _ _ hf (by rw [ha]; congr 1; omega) (by omega), Or.inr ⟨s - 1, by omega,
          size_foldPairs ..⟩⟩
      · rw [h.toArray hf ha24]
        refine ⟨h.ofArray _, Or.inr ⟨s - la, by omega, ?_⟩⟩
        show (Array.ofFn _).size = _
        rw [Array.size_ofFn, hrows]
    have hc' : CPRel h.RC
        ⟨cp.commits.push
            ((specBackend EF).root ((specBackend EF).commit [(specBackend EF).leaves (2 ^ la) a])),
          cp.data ++ [B.commit [B.leaves (2 ^ la) folded]], cp.witnesses.push w,
          cp.arities.push la, cp.finalPoly⟩
        ⟨cs.commits.push
            ((specBackend EF).root ((specBackend EF).commit [(specBackend EF).leaves (2 ^ la) a])),
          cs.data ++ [(specBackend EF).commit [(specBackend EF).leaves (2 ^ la) a]],
              cs.witnesses.push w,
          cs.arities.push la, cs.finalPoly⟩ :=
      ⟨by rw [hc.commits], List.rel_append hc.data (.cons hcm .nil), by rw [hc.witnesses],
        by rw [hc.arities], hc.finalPoly⟩
    cases hr with
    | nil => exact ih hfold.1 hfold.2 .nil (fun _ h ↦ absurd h List.not_mem_nil) hc'
    | @cons v x _ _ hv hvs =>
      dsimp only
      rw [h.size hv, h.size hfold.1]
      split
      · rename_i heq
        have he : fS.size = _ := beq_iff_eq.mp heq |>.symm
        refine ih (h.addScaled _ hfold.1 hv he (shapeOk_le hfold.2)) ?_ hvs
          (fun x hx ↦ hrs x (List.mem_cons_of_mem _ hx)) hc'
        have hz : Array.size ((specBackend EF).addScaled fS x (Ext.powTwo beta la) : Array EF) =
            Array.size (fS : Array EF) := by
          exact (Array.size_zipWith ..).trans (Nat.min_eq_left (Nat.le_of_eq he))
        show ShapeOk ((specBackend EF).addScaled fS x (Ext.powTwo beta la))
        unfold ShapeOk
        rw [hz]
        exact hfold.2
      · exact ih hfold.1 hfold.2 (.cons hv hvs) hrs hc'

theorem commitPhase_refines (h : Refines B) (P : Params) {inputs sinputs}
    (hi : List.Forall₂ h.RV inputs sinputs) (hs : ∀ x ∈ sinputs, ShapeOk x) :
    RelM (CPRel h.RC) (commitPhase B P inputs) (commitPhase (specBackend EF) P sinputs) := by
  have h0 : CPRel h.RC (⟨#[], [], #[], #[], #[]⟩ : CommitPhase F EF B.C) ⟨#[], [], #[], #[], #[]⟩ :=
    ⟨rfl, .nil, rfl, rfl, rfl⟩
  have tail : ∀ {f a rest as}, h.RV f a → ShapeOk a → List.Forall₂ h.RV rest as →
      (∀ x ∈ as, ShapeOk x) →
      RelM (CPRel h.RC)
        (do
          let (folded, cp) ← commitRounds B P (B.size f) f rest ⟨#[], [], #[], #[], #[]⟩
          let fa := B.toArray folded
          let truncated := Array.ofFn (n := 2 ^ P.logFinalPolyLen) fun i ↦
            fa.getD (reverseBits i P.logFinalPolyLen) 0
          let finalPoly := idft P.logFinalPolyLen truncated
          pObserveExts finalPoly.toList
          return { cp with finalPoly := finalPoly })
        (do
          let (folded, cp) ← commitRounds (specBackend EF) P ((specBackend EF).size a) a as
            ⟨#[], [], #[], #[], #[]⟩
          let fa := (specBackend EF).toArray folded
          let truncated := Array.ofFn (n := 2 ^ P.logFinalPolyLen) fun i ↦
            fa.getD (reverseBits i P.logFinalPolyLen) 0
          let finalPoly := idft P.logFinalPolyLen truncated
          pObserveExts finalPoly.toList
          return { cp with finalPoly := finalPoly }) := by
    intro f a rest as hf hfs hr hrs
    rw [h.size hf]
    refine RelM.bind (commitRounds_refines h P _ hf hfs hr hrs h0) ?_
    rintro ⟨f1, c1⟩ ⟨f2, c2⟩ ⟨hv, hvs, hc⟩
    dsimp only
    rw [h.toArray hv (shapeOk_le hvs)]
    exact RelM.bind_eq fun _ ↦ RelM.pure
      ⟨hc.commits, hc.data, hc.witnesses, hc.arities, rfl⟩
  unfold commitPhase
  cases hi with
  | nil => exact tail (h.ofArray #[]) (Or.inl rfl) .nil (fun _ h ↦ absurd h List.not_mem_nil)
  | cons hv hvs =>
    exact tail hv (hs _ List.mem_cons_self) hvs fun x hx ↦ hs x (List.mem_cons_of_mem _ hx)

theorem answerSteps_refines (h : Refines B) {cs ss} (hcs : List.Forall₂ h.RC cs ss) :
    ∀ las cur, answerSteps B cs las cur = answerSteps (specBackend EF) ss las cur := by
  induction hcs with
  | nil => intro las cur; simp only [answerSteps]
  | cons hc _ ih =>
    intro las cur
    cases las with
    | nil => simp only [answerSteps]
    | cons la las => simp only [answerSteps, h.openAt _ hc, ih]

/-- Rounds with related commitments and matrices and the same points. -/
abbrev RoundRel (h : Refines B) (r : OpenRound B) (s : OpenRound (specBackend EF)) : Prop :=
  h.RC r.1 s.1 ∧ List.Forall₂ (fun x y ↦ h.RM x.1 y.1 ∧ x.2 = y.2) r.2 s.2

theorem forall₂_and_mem {α β : Type} {R : α → β → Prop} {P : β → Prop} :
    ∀ {xs ys}, List.Forall₂ R xs ys → (∀ y ∈ ys, P y) →
      List.Forall₂ (fun a b ↦ R a b ∧ P b) xs ys
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons h hs, hp =>
    .cons ⟨h, hp _ List.mem_cons_self⟩ (forall₂_and_mem hs fun y hy ↦ hp y (List.mem_cons_of_mem _ hy))

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} {P : β → Prop}
    (hRP : ∀ a b, R a b → P b) : ∀ {xs ys}, List.Forall₂ R xs ys → ∀ y ∈ ys, P y
  | [], [], .nil, _, hy => absurd hy List.not_mem_nil
  | _ :: _, _ :: _, .cons h hs, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hRP _ _ h
    · exact forall₂_mem_right hRP hs y hy

/-- The matrices of opening rounds have the prover's shapes, and their points are outside the
base field. -/
def RoundsOk (rounds : List (OpenRound (specBackend EF))) : Prop :=
  ∀ r ∈ rounds, ∀ x ∈ r.2, MatOk x.1 ∧ ∀ z ∈ x.2, Ext.OutsideBase z

/-- `proveFri` of related rounds and related inputs of the prover's shapes is the
specification's. -/
theorem proveFri_refines (h : Refines B) (P : Params) {rounds srounds}
    (hr : List.Forall₂ (RoundRel h) rounds srounds) {inputsOf : EF → List B.V}
    {sinputsOf : EF → List (specBackend EF).V}
    (hin : ∀ alpha, List.Forall₂ h.RV (inputsOf alpha) (sinputsOf alpha))
    (hshape : ∀ alpha, ∀ x ∈ sinputsOf alpha, ShapeOk x) :
    RelM Eq (proveFri B P rounds inputsOf) (proveFri (specBackend EF) P srounds sinputsOf) := by
  rw [proveFri, proveFri]
  refine RelM.bind_eq fun alpha ↦ ?_
  have hin := hin alpha
  have hshape := hshape alpha
  generalize inputsOf alpha = inputs at hin ⊢
  generalize sinputsOf alpha = sinputs at hin hshape ⊢
  dsimp only
  rw [forall₂_map_eq (fun _ _ hv ↦ h.size hv) hin]
  generalize ((sinputs.map (specBackend EF).size).headD 0).log2 = logMax
  refine RelM.bind (commitPhase_refines h P hin hshape) fun cp cs hc ↦ ?_
  rw [hc.arities]
  refine RelM.bind_eq fun _ ↦ RelM.bind_eq fun qw ↦ ?_
  have hq : ∀ index, answerQuery B cp index = answerQuery (specBackend EF) cs index := by
    intro index
    simp only [answerQuery, hc.arities, answerSteps_refines h hc.data]
  have hins : ∀ index, (rounds.map fun (x : OpenRound B) ↦ match x with
      | (c, _) => B.openAt c (index >>> (logMax - B.logHeight c))) =
      srounds.map fun (x : OpenRound (specBackend EF)) ↦ match x with
      | (c, _) => (specBackend EF).openAt c (index >>> (logMax - (specBackend EF).logHeight c)) :=
    fun index ↦ forall₂_map_eq (fun r s hrs ↦ by
      simp only [h.logHeight hrs.1, h.openAt _ hrs.1]) hr
  simp only [hq, hins]
  refine RelM.bind_eq fun queries ↦ ?_
  rw [hc.commits, hc.witnesses, hc.finalPoly]
  exact RelM.pure rfl

/-- `openPcs` of related rounds is the specification's. -/
theorem openPcs_refines (h : Refines B) (P : Params) {rounds srounds}
    (hr : List.Forall₂ (RoundRel h) rounds srounds) (hok : RoundsOk srounds) :
    RelM Eq (openPcs B P rounds) (openPcs (specBackend EF) P srounds) := by
  rw [openPcs, openPcs]
  let S : List (Array EF) × B.M × List (EF × Array EF) →
      List (Array EF) × (specBackend EF).M × List (EF × Array EF) → Prop :=
    fun x y ↦ x.1 = y.1 ∧ h.RM x.2.1 y.2.1 ∧ x.2.2 = y.2.2 ∧
      (MatOk y.2.1 ∧ ∀ p ∈ y.2.2, Ext.OutsideBase p.1)
  have hop := RelM.mapM (S := List.Forall₂ S)
    (R := fun r s ↦ RoundRel h r s ∧ ∀ x ∈ s.2, MatOk x.1 ∧ ∀ z ∈ x.2, Ext.OutsideBase z)
    (f := fun (r : OpenRound B) ↦ r.2.mapM fun (m, zs) ↦ do
      let ov := B.openedAt P.logBlowup m zs
      ov.forM fun ys ↦ pObserveExts ys.toList
      return (ov, m, zs.zip ov))
    (g := fun (r : OpenRound (specBackend EF)) ↦ r.2.mapM fun (m, zs) ↦ do
      let ov := (specBackend EF).openedAt P.logBlowup m zs
      ov.forM fun ys ↦ pObserveExts ys.toList
      return (ov, m, zs.zip ov))
    (fun r s hrs ↦ RelM.mapM
      (R := fun x y ↦ (h.RM x.1 y.1 ∧ x.2 = y.2) ∧ (MatOk y.1 ∧ ∀ z ∈ y.2, Ext.OutsideBase z))
      (f := fun (x : B.M × List EF) ↦ match x with
        | (m, zs) => do
          let ov := B.openedAt P.logBlowup m zs
          ov.forM fun ys ↦ pObserveExts ys.toList
          return (ov, m, zs.zip ov))
      (g := fun (x : (specBackend EF).M × List EF) ↦ match x with
        | (m, zs) => do
          let ov := (specBackend EF).openedAt P.logBlowup m zs
          ov.forM fun ys ↦ pObserveExts ys.toList
          return (ov, m, zs.zip ov))
      (fun ⟨xm, xz⟩ ⟨ym, yz⟩ ⟨⟨hm, hz⟩, hmat, hzs⟩ ↦ by
        dsimp only at hm hz hmat hzs ⊢
        rw [hz, h.openedAt _ _ hm hmat hzs]
        exact RelM.bind_eq fun _ ↦ RelM.pure ⟨rfl, hm, rfl, hmat,
          fun p hp ↦ hzs p.1 (List.of_mem_zip hp).1⟩) (forall₂_and_mem hrs.1.2 hrs.2))
    (forall₂_and_mem hr hok)
  refine RelM.bind hop fun opened sopened hos ↦ ?_
  have hflat := List.rel_flatten hos
  have hitems : List.Forall₂ (fun x y ↦ h.RM x.1 y.1 ∧ x.2 = y.2)
      (opened.flatten.map (·.2)) (sopened.flatten.map (·.2)) :=
    forall₂_map (fun _ _ hs ↦ ⟨hs.2.1, hs.2.2.1⟩) hflat
  have hsok : ∀ x ∈ sopened.flatten.map (·.2), MatOk x.1 ∧ ∀ p ∈ x.2, Ext.OutsideBase p.1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact forall₂_mem_right (R := S) (fun _ _ hs ↦ hs.2.2.2) hflat y hy
  have hin : ∀ alpha, List.Forall₂ h.RV ((B.reduce alpha (opened.flatten.map (·.2))).map (·.2))
      (((specBackend EF).reduce alpha (sopened.flatten.map (·.2))).map (·.2)) :=
    fun alpha ↦ forall₂_map (fun _ _ hs ↦ hs.2) (h.reduce alpha hitems hsok)
  have hshape : ∀ alpha,
      ∀ x ∈ ((specBackend EF).reduce alpha (sopened.flatten.map (·.2))).map (·.2),
      ShapeOk x := fun alpha x hx ↦ by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact Or.inr (reduce_shape alpha _ (fun x hx ↦ (hsok x hx).1) y hy)
  refine RelM.bind (proveFri_refines h P hr hin hshape) fun fri _ hf ↦ hf ▸ ?_
  rw [forall₂_map_eq (fun a b hab ↦ forall₂_map_eq (fun x y hxy ↦ hxy.1) hab) hos]
  exact RelM.pure rfl

end CompStark.Fri
