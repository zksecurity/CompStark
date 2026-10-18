/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Prover
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

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4

/-- The backend `B` computes the specification's functions, through relations `RM`, `RC`, `RV`
between its matrices, commitments and vectors and the specification's. -/
structure Refines (B : Backend) where
  RM : B.M → Backend.spec.M → Prop
  RC : B.C → Backend.spec.C → Prop
  RV : B.V → Backend.spec.V → Prop
  transcript : B.transcript = Backend.spec.transcript
  lde : ∀ logH bits shift w m,
    RM (B.lde logH bits shift w m) (Backend.spec.lde logH bits shift w m)
  commit : ∀ {ms ss}, List.Forall₂ RM ms ss → RC (B.commit ms) (Backend.spec.commit ss)
  root : ∀ {c s}, RC c s → B.root c = Backend.spec.root s
  openAt : ∀ {c s} i, RC c s → B.openAt c i = Backend.spec.openAt s i
  logHeight : ∀ {c s}, RC c s → B.logHeight c = Backend.spec.logHeight s
  quotient : ∀ A pis d l {m s} alpha, RM m s →
    B.quotient A pis d l m alpha = Backend.spec.quotient A pis d l s alpha
  openedAt : ∀ b zs {m s}, RM m s → B.openedAt b m zs = Backend.spec.openedAt b s zs
  toArray : ∀ {v a}, RV v a → B.toArray v = Backend.spec.toArray a
  ofArray : ∀ a, RV (B.ofArray a) (Backend.spec.ofArray a)
  size : ∀ {v a}, RV v a → B.size v = Backend.spec.size a
  reduce : ∀ alpha {items sitems},
    List.Forall₂ (fun x y ↦ RM x.1 y.1 ∧ x.2 = y.2) items sitems →
    List.Forall₂ (fun x y ↦ x.1 = y.1 ∧ RV x.2 y.2) (B.reduce alpha items)
      (Backend.spec.reduce alpha sitems)
  fold2 : ∀ beta k {v a}, RV v a → RV (B.fold2 v beta k) (Backend.spec.fold2 a beta k)
  addScaled : ∀ x {v a w b}, RV v a → RV w b →
    RV (B.addScaled v w x) (Backend.spec.addScaled a b x)
  leaves : ∀ k {v a}, RV v a → RM (B.leaves k v) (Backend.spec.leaves k a)

/-- Prover computations that, from every transcript, return related results and the same
transcript. -/
def RelM {α β : Type} (R : α → β → Prop) (x : PM α) (y : PM β) : Prop :=
  ∀ t, R (x.run t).1 (y.run t).1 ∧ (x.run t).2 = (y.run t).2

namespace RelM

variable {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}

theorem run_bind {x : PM α} {f : α → PM γ} (t : Transcript) :
    (x >>= f).run t = (f (x.run t).1).run (x.run t).2 := rfl

theorem pure {a : α} {b : β} (h : R a b) : RelM R (Pure.pure a) (Pure.pure b) :=
  fun _ ↦ ⟨h, rfl⟩

theorem refl (x : PM α) : RelM Eq x x := fun _ ↦ ⟨rfl, rfl⟩

theorem bind {x : PM α} {y : PM β} {f : α → PM γ} {g : β → PM δ} (hx : RelM R x y)
    (hf : ∀ a b, R a b → RelM S (f a) (g b)) : RelM S (x >>= f) (y >>= g) := by
  intro t
  obtain ⟨h1, h2⟩ := hx t
  rw [run_bind, run_bind, h2]
  exact hf _ _ h1 _

theorem bind_eq {x : PM α} {f : α → PM γ} {g : α → PM δ}
    (hf : ∀ a, RelM S (f a) (g a)) : RelM S (x >>= f) (x >>= g) :=
  bind (refl x) fun a _ h ↦ h ▸ hf a

theorem mapM {f : α → PM γ} {g : β → PM δ} (hf : ∀ a b, R a b → RelM S (f a) (g b)) :
    ∀ {xs ys}, List.Forall₂ R xs ys → RelM (List.Forall₂ S) (xs.mapM f) (ys.mapM g)
  | [], [], .nil => by
    simp only [List.mapM_nil]
    exact pure .nil
  | _ :: _, _ :: _, .cons h hs => by
    simp only [List.mapM_cons]
    exact bind (hf _ _ h) fun _ _ h1 ↦ bind (mapM hf hs) fun _ _ h2 ↦ pure (.cons h1 h2)

theorem imp {x : PM α} {y : PM β} {R' : α → β → Prop} (h : ∀ a b, R a b → R' a b)
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
structure CPRel {C D : Type} (RC : C → D → Prop) (cp : CommitPhase C) (cs : CommitPhase D) :
    Prop where
  commits : cp.commits = cs.commits
  data : List.Forall₂ RC cp.data cs.data
  witnesses : cp.witnesses = cs.witnesses
  arities : cp.arities = cs.arities
  finalPoly : cp.finalPoly = cs.finalPoly

variable {B : Backend}

theorem commitRounds_refines (h : Refines B) (P : Params) (fuel : Nat) :
    ∀ {folded a rest as cp cs}, h.RV folded a → List.Forall₂ h.RV rest as →
      CPRel h.RC cp cs →
      RelM (fun p q ↦ h.RV p.1 q.1 ∧ CPRel h.RC p.2 q.2)
        (commitRounds B P fuel folded rest cp) (commitRounds Backend.spec P fuel a as cs) := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ hf _ hc; exact RelM.pure ⟨hf, hc⟩
  | succ fuel ih =>
    intro folded a rest as cp cs hf hr hc
    rw [commitRounds, commitRounds, h.size hf]
    split
    · exact RelM.pure ⟨hf, hc⟩
    have hcm := h.commit (.cons (h.leaves (2 ^ logArityFor P (Backend.spec.size a).log2
      (Option.map (fun x ↦ (Backend.spec.size x).log2) as.head?)) hf) .nil)
    have hhead : Option.map (fun x ↦ (B.size x).log2) rest.head? =
        Option.map (fun x ↦ (Backend.spec.size x).log2) as.head? := by
      cases hr with
      | nil => simp only [List.head?_nil, Option.map_none]
      | cons hv _ => rw [List.head?_cons, List.head?_cons, Option.map_some, Option.map_some,
          h.size hv]
    dsimp only
    rw [hhead, h.root hcm]
    refine RelM.bind_eq fun _ ↦ RelM.bind_eq fun w ↦ RelM.bind_eq fun beta ↦ ?_
    generalize logArityFor P (Backend.spec.size a).log2
      (Option.map (fun x ↦ (Backend.spec.size x).log2) as.head?) = la at hcm ⊢
    generalize hfB : (if la = 1 then _ else _ : B.V) = fB
    generalize hfS : (if la = 1 then _ else _ : Backend.spec.V) = fS
    have hfold : h.RV fB fS := by
      subst hfB hfS
      split
      · exact h.fold2 _ _ hf
      · rw [h.toArray hf]
        exact h.ofArray _
    have hc' : CPRel h.RC
        ⟨cp.commits.push (Backend.spec.root (Backend.spec.commit [Backend.spec.leaves (2 ^ la) a])),
          cp.data ++ [B.commit [B.leaves (2 ^ la) folded]], cp.witnesses.push w,
          cp.arities.push la, cp.finalPoly⟩
        ⟨cs.commits.push (Backend.spec.root (Backend.spec.commit [Backend.spec.leaves (2 ^ la) a])),
          cs.data ++ [Backend.spec.commit [Backend.spec.leaves (2 ^ la) a]], cs.witnesses.push w,
          cs.arities.push la, cs.finalPoly⟩ :=
      ⟨by rw [hc.commits], List.rel_append hc.data (.cons hcm .nil), by rw [hc.witnesses],
        by rw [hc.arities], hc.finalPoly⟩
    cases hr with
    | nil => exact ih hfold .nil hc'
    | cons hv hvs =>
      dsimp only
      rw [h.size hv, h.size hfold]
      split
      · exact ih (h.addScaled _ hfold hv) hvs hc'
      · exact ih hfold (.cons hv hvs) hc'

theorem commitPhase_refines (h : Refines B) (P : Params) {inputs sinputs}
    (hi : List.Forall₂ h.RV inputs sinputs) :
    RelM (CPRel h.RC) (commitPhase B P inputs) (commitPhase Backend.spec P sinputs) := by
  have h0 : CPRel h.RC (⟨#[], [], #[], #[], #[]⟩ : CommitPhase B.C) ⟨#[], [], #[], #[], #[]⟩ :=
    ⟨rfl, .nil, rfl, rfl, rfl⟩
  have tail : ∀ {f a rest as}, h.RV f a → List.Forall₂ h.RV rest as →
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
          let (folded, cp) ← commitRounds Backend.spec P (Backend.spec.size a) a as
            ⟨#[], [], #[], #[], #[]⟩
          let fa := Backend.spec.toArray folded
          let truncated := Array.ofFn (n := 2 ^ P.logFinalPolyLen) fun i ↦
            fa.getD (reverseBits i P.logFinalPolyLen) 0
          let finalPoly := idft P.logFinalPolyLen truncated
          pObserveExts finalPoly.toList
          return { cp with finalPoly := finalPoly }) := by
    intro f a rest as hf hr
    rw [h.size hf]
    refine RelM.bind (commitRounds_refines h P _ hf hr h0) ?_
    rintro ⟨f1, c1⟩ ⟨f2, c2⟩ ⟨hv, hc⟩
    dsimp only
    rw [h.toArray hv]
    exact RelM.bind_eq fun _ ↦ RelM.pure
      ⟨hc.commits, hc.data, hc.witnesses, hc.arities, rfl⟩
  unfold commitPhase
  cases hi with
  | nil => exact tail (h.ofArray #[]) .nil
  | cons hv hvs => exact tail hv hvs

theorem answerSteps_refines (h : Refines B) {cs ss} (hcs : List.Forall₂ h.RC cs ss) :
    ∀ las cur, answerSteps B cs las cur = answerSteps Backend.spec ss las cur := by
  induction hcs with
  | nil => intro las cur; simp only [answerSteps]
  | cons hc _ ih =>
    intro las cur
    cases las with
    | nil => simp only [answerSteps]
    | cons la las => simp only [answerSteps, h.openAt _ hc, ih]

/-- Rounds with related commitments and matrices and the same points. -/
abbrev RoundRel (h : Refines B) (r : OpenRound B) (s : OpenRound Backend.spec) : Prop :=
  h.RC r.1 s.1 ∧ List.Forall₂ (fun x y ↦ h.RM x.1 y.1 ∧ x.2 = y.2) r.2 s.2

/-- `openPcs` of related rounds is the specification's. -/
theorem openPcs_refines (h : Refines B) (P : Params) {rounds srounds}
    (hr : List.Forall₂ (RoundRel h) rounds srounds) :
    RelM Eq (openPcs B P rounds) (openPcs Backend.spec P srounds) := by
  rw [openPcs, openPcs]
  let S : List (Array EF) × B.M × List (EF × Array EF) →
      List (Array EF) × Backend.spec.M × List (EF × Array EF) → Prop :=
    fun x y ↦ x.1 = y.1 ∧ h.RM x.2.1 y.2.1 ∧ x.2.2 = y.2.2
  have hop := RelM.mapM (S := List.Forall₂ S) (R := RoundRel h)
    (f := fun (r : OpenRound B) ↦ r.2.mapM fun (m, zs) ↦ do
      let ov := B.openedAt P.logBlowup m zs
      ov.forM fun ys ↦ pObserveExts ys.toList
      return (ov, m, zs.zip ov))
    (g := fun (r : OpenRound Backend.spec) ↦ r.2.mapM fun (m, zs) ↦ do
      let ov := Backend.spec.openedAt P.logBlowup m zs
      ov.forM fun ys ↦ pObserveExts ys.toList
      return (ov, m, zs.zip ov))
    (fun r s hrs ↦ RelM.mapM (R := fun x y ↦ h.RM x.1 y.1 ∧ x.2 = y.2)
      (fun x y ⟨hm, hz⟩ ↦ by
        dsimp only
        rw [h.openedAt _ _ hm, hz]
        exact RelM.bind_eq fun _ ↦ RelM.pure ⟨rfl, hm, rfl⟩) hrs.2) hr
  refine RelM.bind hop fun opened sopened hos ↦ ?_
  refine RelM.bind_eq fun alpha ↦ ?_
  have hitems : List.Forall₂ (fun x y ↦ h.RM x.1 y.1 ∧ x.2 = y.2)
      (opened.flatten.map (·.2)) (sopened.flatten.map (·.2)) :=
    forall₂_map (fun _ _ hs ↦ hs.2) (List.rel_flatten hos)
  have hin : List.Forall₂ h.RV ((B.reduce alpha (opened.flatten.map (·.2))).map (·.2))
      ((Backend.spec.reduce alpha (sopened.flatten.map (·.2))).map (·.2)) :=
    forall₂_map (fun _ _ hs ↦ hs.2) (h.reduce alpha hitems)
  generalize (B.reduce alpha (opened.flatten.map (·.2))).map (·.2) = inputs at hin ⊢
  generalize (Backend.spec.reduce alpha (sopened.flatten.map (·.2))).map (·.2) = sinputs at hin ⊢
  dsimp only
  rw [forall₂_map_eq (fun _ _ hv ↦ h.size hv) hin]
  generalize ((sinputs.map Backend.spec.size).headD 0).log2 = logMax
  refine RelM.bind (commitPhase_refines h P hin) fun cp cs hc ↦ ?_
  rw [hc.arities]
  refine RelM.bind_eq fun _ ↦ RelM.bind_eq fun qw ↦ ?_
  have hq : ∀ index, answerQuery B cp index = answerQuery Backend.spec cs index := by
    intro index
    simp only [answerQuery, hc.arities, answerSteps_refines h hc.data]
  have hins : ∀ index, (rounds.map fun (x : OpenRound B) ↦ match x with
      | (c, _) => B.openAt c (index >>> (logMax - B.logHeight c))) =
      srounds.map fun (x : OpenRound Backend.spec) ↦ match x with
      | (c, _) => Backend.spec.openAt c (index >>> (logMax - Backend.spec.logHeight c)) :=
    fun index ↦ forall₂_map_eq (fun r s hrs ↦ by
      simp only [h.logHeight hrs.1, h.openAt _ hrs.1]) hr
  simp only [hq, hins]
  refine RelM.bind_eq fun queries ↦ ?_
  rw [forall₂_map_eq (fun a b hab ↦ forall₂_map_eq (fun x y hxy ↦ hxy.1) hab) hos,
    hc.commits, hc.witnesses, hc.finalPoly]
  exact RelM.pure rfl

end CompStark.Fri
