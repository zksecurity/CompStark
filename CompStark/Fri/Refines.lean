/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Shapes
public import CompStark.Plonky3.Prover
public import Mathlib.Data.List.Forall2

/-! # Backends that refine the specification

`Refines B` relates a backend's matrices, commitments and vectors to the specification's, and
asks every kernel to map related inputs to related outputs, with equal plain results. Under it
the FRI opening `openPcs` of related rounds gives the specification's opened values and proof
(`openPcs_refines`).
-/

@[expose] public section
namespace CompStark.Fri
open CompStark.Stark

variable {F : Type}

/-- Prover computations that, from every transcript, return related results and the same
transcript. -/
def RelM {α β : Type} (R : α → β → Prop) (x : PM F 24 α) (y : PM F 24 β) : Prop :=
  ∀ t, R (x.run t).1 (y.run t).1 ∧ (x.run t).2 = (y.run t).2

namespace RelM

variable {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}

theorem run_bind {x : PM F 24 α} {f : α → PM F 24 γ} (t : Transcript F 24) :
    (x >>= f).run t = (f (x.run t).1).run (x.run t).2 := rfl

theorem pure {a : α} {b : β} (h : R a b) : RelM (F := F) R (Pure.pure a) (Pure.pure b) :=
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

theorem mapM {f : α → PM F 24 γ} {g : β → PM F 24 δ} (hf : ∀ a b, R a b → RelM S (f a) (g b)) : ∀
    {xs ys}, List.Forall₂ R xs ys → RelM (List.Forall₂ S) (xs.mapM f) (ys.mapM g)
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

variable [BaseField F] {EF : Type}

/-- A vector of the commit phase: empty, or `2 ^ s` values within the two-adic subgroups. -/
def ShapeOk (a : Array EF) : Prop := a.size = 0 ∨ ∃ s ≤ twoAdicity F, a.size = 2 ^ s

theorem shapeOk_le {a : Array EF} (h : ShapeOk (F := F) a) : a.size ≤ 2 ^ twoAdicity F := by
  rcases h with h | ⟨s, hs, h⟩
  · rw [h]; exact Nat.zero_le _
  · rw [h]; exact Nat.pow_le_pow_right (by decide) hs

variable [Poseidon2Field F] [Challenge F EF]

/-- The backend `B` computes the specification's functions on the inputs the prover gives them,
through relations `RT`, `RM`, `RC`, `RV`, `RQ` between its traces, matrices, commitments, vectors
and quotient values and the specification's; `RT logH w` relates traces of `2 ^ logH` rows and `w` columns. -/
structure Refines (B : Backend F EF 24) where
  RT : Nat → Nat → B.Trace → Array F → Prop
  RM : B.M → (specBackend EF).M → Prop
  RC : B.C → (specBackend EF).C → Prop
  RV : B.V → (specBackend EF).V → Prop
  RQ : B.Q → (specBackend EF).Q → Prop
  transcript : B.transcript = (specBackend EF).transcript
  ldeTrace : ∀ logH bits shift w {t m}, RT logH w t m → m.size = 2 ^ logH * w →
    logH + bits ≤ twoAdicity F → Addressable (2 ^ (logH + bits) * w) →
    RM (B.ldeTrace logH bits shift w t) ((specBackend EF).lde logH bits shift w m)
  lde : ∀ logH bits shift w m, m.size = 2 ^ logH * w → logH + bits ≤ twoAdicity F →
    Addressable (2 ^ (logH + bits) * w) →
    RM (B.lde logH bits shift w m) ((specBackend EF).lde logH bits shift w m)
  commit : ∀ {ms ss}, List.Forall₂ RM ms ss → CommitOk ss →
    RC (B.commit ms) ((specBackend EF).commit ss)
  cap : ∀ {c s} h, RC c s → B.cap c h = (specBackend EF).cap s h
  openAt : ∀ {c s} i, RC c s → B.openAt c i = (specBackend EF).openAt s i
  logHeight : ∀ {c s}, RC c s → B.logHeight c = (specBackend EF).logHeight s
  quotient : ∀ A pis d l {m s pm ps} alpha, RM m s → MatOk s → 2 ^ (d + l) ≤ s.height →
    Option.Rel RM pm ps → (∀ p ∈ ps, MatOk p ∧ p.height = s.height) →
    (∀ c ∈ A.constraints, c.colsBelow s.width s.width ((ps.map (·.width)).getD 0)
      ((ps.map (·.width)).getD 0)) →
    RQ (B.quotient A pis d l m pm alpha) ((specBackend EF).quotient A pis d l s ps alpha)
  lookupQuotient : ∀ A ext pis d l {m s pm ps rm rs} chs t alpha k, RM m s → MatOk s →
    2 ^ (d + l) ≤ s.height → Option.Rel RM pm ps → (∀ p ∈ ps, MatOk p ∧ p.height = s.height) →
    RM rm rs → MatOk rs → rs.height = s.height → k * Challenge.d EF ≤ rs.width →
    (∀ c ∈ ext, c.colsBelow s.width s.width ((ps.map (·.width)).getD 0)
      ((ps.map (·.width)).getD 0) k) →
    RQ (B.lookupQuotient A ext pis d l m pm rm chs t alpha)
      ((specBackend EF).lookupQuotient A ext pis d l s ps rs chs t alpha)
  combine : ∀ x {q a r b}, RQ q a → RQ r b → a.size = b.size → a.size ≤ 2 ^ twoAdicity F →
    RQ (B.combine q r x) ((specBackend EF).combine a b x)
  chunks : ∀ bits logN l {v a}, RQ v a → a.size = 2 ^ (logN + l) → l ≤ bits →
    logN + bits ≤ twoAdicity F →
    List.Forall₂ RM (B.chunks bits logN l v) ((specBackend EF).chunks bits logN l a)
  permutation : ∀ bits A ls logN {t m} pis chs, RT logN A.width t m →
    PermutationOk EF A ls logN bits m →
    RM (B.permutation bits A ls logN t pis chs).1
        ((specBackend EF).permutation bits A ls logN m pis chs).1 ∧
      (B.permutation bits A ls logN t pis chs).2 =
        ((specBackend EF).permutation bits A ls logN m pis chs).2
  toArray : ∀ {v a}, RV v a → a.size ≤ 2 ^ twoAdicity F → B.toArray v = (specBackend EF).toArray a
  ofArray : ∀ a, RV (B.ofArray a) ((specBackend EF).ofArray a)
  size : ∀ {v a}, RV v a → B.size v = (specBackend EF).size a
  openings : ∀ b {rs srs},
    List.Forall₂ (List.Forall₂ fun x y ↦ RM x.1 y.1 ∧ x.2 = y.2) rs srs →
    (∀ ms ∈ srs, ∀ x ∈ ms, MatOk x.1 ∧ ∀ z ∈ x.2, Ext.OutsideBase z) →
    (B.openings b rs).1 = ((specBackend EF).openings b srs).1 ∧
      ∀ alpha, List.Forall₂ (fun x y ↦ x.1 = y.1 ∧ RV x.2 y.2) ((B.openings b rs).2 alpha)
        (((specBackend EF).openings b srs).2 alpha)
  fold : ∀ la beta s {v a}, RV v a → a.size = 2 ^ s → la ≤ s → s ≤ twoAdicity F →
    RV (B.fold la beta v) ((specBackend EF).fold la beta a)
  addScaled : ∀ x {v a w b}, RV v a → RV w b → a.size = b.size → a.size ≤ 2 ^ twoAdicity F →
    RV (B.addScaled v w x) ((specBackend EF).addScaled a b x)
  leaves : ∀ k {v a}, RV v a → a.size ≤ 2 ^ twoAdicity F → k ∣ a.size → 0 < a.size →
      RM (B.leaves k v) ((specBackend EF).leaves k a)

theorem forall₂_map_eq {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (hfg : ∀ a b, R a b → f a = g b) : ∀ {xs ys}, List.Forall₂ R xs ys → xs.map f = ys.map g
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
    simp only [List.map_cons, hfg _ _ h, forall₂_map_eq hfg hs]

theorem forall₂_map {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {f : α → γ} {g : β → δ}
    (hfg : ∀ a b, R a b → S (f a) (g b)) :
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

/-- The leaves of a commit-phase round are a matrix of the prover's shape. -/
theorem commitOk_leaves (hA : DomainsAddressable F EF) (a : Array EF) (s la : Nat)
    (hs : s ≤ twoAdicity F) (ha : a.size = 2 ^ s) (hla : la ≤ s) :
    CommitOk [(specBackend EF).leaves (2 ^ la) a] := by
  have hd : a.size / 2 ^ la = 2 ^ (s - la) := by
    rw [ha, Nat.pow_div hla (by decide)]
  have hsz : 2 ^ la * 2 ^ (s - la) = 2 ^ s := by rw [← Nat.pow_add, Nat.add_sub_cancel' hla]
  have hadd : Addressable (Challenge.d EF * 2 ^ la * 2 ^ (s - la)) := by
    rw [Nat.mul_assoc, hsz]
    have : 2 ^ s ≤ 2 ^ twoAdicity F := Nat.pow_le_pow_right (by decide) hs
    unfold DomainsAddressable Addressable at hA
    unfold Addressable
    have := Nat.mul_le_mul_left (Challenge.d EF) this
    omega
  refine ⟨2 ^ (s - la), List.cons_ne_nil _ _, fun m hm ↦ ?_, ?_⟩
  · obtain rfl := List.mem_singleton.mp hm
    refine ⟨⟨Nat.mul_pos (Challenge.params EF).d_pos (by positivity),
        ⟨s - la, by omega, hd⟩,
      ?_, ?_⟩, hd.le⟩
    · show (a.flatMap fun x ↦ (Ext.coeffs x).toArray).size =
        Challenge.d EF * 2 ^ la * (a.size / 2 ^ la)
      rw [size_flatMap_coeffs, hd, Nat.mul_assoc, hsz, ha]
    · show Addressable (Challenge.d EF * 2 ^ la * (a.size / 2 ^ la))
      rw [hd]; exact hadd
  · show Addressable (2 ^ (s - la) * (0 + Challenge.d EF * 2 ^ la))
    rw [Nat.zero_add, Nat.mul_comm]; exact hadd

/-- A commit-phase vector with log arities `las` left: no round left, or `2 ^ s` values within
the two-adic subgroups for `s` at least the arities' sum. -/
def FoldsFit (las : List Nat) (a : Array EF) : Prop :=
  las = [] ∨ ∃ s ≤ twoAdicity F, a.size = 2 ^ s ∧ las.sum ≤ s

theorem commitRounds_refines (hA : DomainsAddressable F EF) (h : Refines B) (P : Params) :
    ∀ las {folded a rest as cp cs}, h.RV folded a → ShapeOk (F := F) a →
      FoldsFit (F := F) las a → List.Forall₂ h.RV rest as →
      (∀ x ∈ as, ShapeOk (F := F) x) → CPRel h.RC cp cs →
      RelM (fun p q ↦ h.RV p.1 q.1 ∧ ShapeOk (F := F) q.1 ∧ CPRel h.RC p.2 q.2)
        (commitRounds B P las folded rest cp) (commitRounds (specBackend EF) P las a as cs)
  | [], _, _, _, _, _, _, hf, hfs, _, _, _, hc => RelM.pure ⟨hf, hfs, hc⟩
  | la :: las, folded, a, rest, as, cp, cs, hf, hfs, hfit, hr, hrs, hc => by
    rw [commitRounds, commitRounds]
    obtain ⟨s, hs, ha, hsum⟩ : ∃ s ≤ twoAdicity F, a.size = 2 ^ s ∧ (la :: las).sum ≤ s := by
      rcases hfit with h0 | h0
      · exact absurd h0 (List.cons_ne_nil _ _)
      · exact h0
    rw [List.sum_cons] at hsum
    have hla : la ≤ s := by omega
    have ha24 : a.size ≤ 2 ^ twoAdicity F := shapeOk_le (Or.inr ⟨s, hs, ha⟩)
    have hdvd : 2 ^ la ∣ a.size := by rw [ha]; exact Nat.pow_dvd_pow 2 hla
    have hpos : 0 < a.size := by rw [ha]; exact Nat.two_pow_pos s
    have hcm := h.commit (.cons (h.leaves (2 ^ la) hf ha24 hdvd hpos) .nil)
      (commitOk_leaves hA a s la hs ha hla)
    rw [h.cap _ hcm]
    dsimp only
    refine RelM.bind_eq fun _ ↦ RelM.bind_eq fun w ↦ RelM.bind_eq fun beta ↦ ?_
    generalize hfB : B.fold la beta folded = fB
    generalize hfS : foldOnce la beta a = fS
    have hfold : h.RV fB fS ∧ fS.size = 2 ^ (s - la) := by
      subst hfB hfS
      exact ⟨h.fold la beta s hf ha hla hs, size_foldOnce la s beta a ha hla⟩
    have hfit' : FoldsFit (F := F) las fS := Or.inr ⟨s - la, by omega, hfold.2, by omega⟩
    have hshape' : ShapeOk (F := F) fS := Or.inr ⟨s - la, by omega, hfold.2⟩
    have hc' : CPRel h.RC
        ⟨cp.commits.push
            ((specBackend EF).cap ((specBackend EF).commit [(specBackend EF).leaves (2 ^ la) a])
              P.capHeight),
          cp.data ++ [B.commit [B.leaves (2 ^ la) folded]], cp.witnesses.push w,
          cp.arities.push la, cp.finalPoly⟩
        ⟨cs.commits.push
            ((specBackend EF).cap ((specBackend EF).commit [(specBackend EF).leaves (2 ^ la) a])
              P.capHeight),
          cs.data ++ [(specBackend EF).commit [(specBackend EF).leaves (2 ^ la) a]],
              cs.witnesses.push w,
          cs.arities.push la, cs.finalPoly⟩ :=
      ⟨by rw [hc.commits], List.rel_append hc.data (.cons hcm .nil), by rw [hc.witnesses],
        by rw [hc.arities], hc.finalPoly⟩
    cases hr with
    | nil =>
      exact commitRounds_refines hA h P las hfold.1 hshape' hfit' .nil
        (fun _ h ↦ absurd h List.not_mem_nil) hc'
    | @cons v x _ _ hv hvs =>
      dsimp only
      rw [h.size hv, h.size hfold.1]
      split
      · rename_i heq
        have he : fS.size = _ := beq_iff_eq.mp heq |>.symm
        have hz : Array.size
            ((specBackend EF).addScaled fS x (Ext.powTwo beta la) : Array EF) = Array.size
                (fS : Array EF) :=
          (Array.size_zipWith ..).trans (Nat.min_eq_left (Nat.le_of_eq he))
        refine commitRounds_refines hA h P las (h.addScaled _ hfold.1 hv he (shapeOk_le hshape'))
          ?_ ?_ hvs (fun x hx ↦ hrs x (List.mem_cons_of_mem _ hx)) hc'
        · show ShapeOk (F := F) ((specBackend EF).addScaled fS x (Ext.powTwo beta la))
          unfold ShapeOk
          rw [hz]
          exact hshape'
        · show FoldsFit (F := F) las ((specBackend EF).addScaled fS x (Ext.powTwo beta la))
          unfold FoldsFit
          rw [hz]
          exact hfit'
      · exact commitRounds_refines hA h P las hfold.1 hshape' hfit' (.cons hv hvs) hrs hc'

theorem commitPhase_refines (hA : DomainsAddressable F EF) (h : Refines B) (P : Params)
    (las : List Nat) {inputs sinputs}
    (hi : List.Forall₂ h.RV inputs sinputs) (hs : ∀ x ∈ sinputs, ShapeOk (F := F) x)
    (hfit : FoldsFit (F := F) las ((sinputs.headD #[]))) :
    RelM (CPRel h.RC) (commitPhase B P las inputs)
      (commitPhase (specBackend EF) P las sinputs) := by
  have h0 : CPRel h.RC (⟨#[], [], #[], #[], #[]⟩ : CommitPhase F EF B.C) ⟨#[], [], #[], #[], #[]⟩ :=
    ⟨rfl, .nil, rfl, rfl, rfl⟩
  have tail : ∀ {f a rest as}, h.RV f a → ShapeOk (F := F) a → FoldsFit (F := F) las a →
      List.Forall₂ h.RV rest as → (∀ x ∈ as, ShapeOk (F := F) x) →
      RelM (CPRel h.RC)
        (do
          let (folded, cp) ← commitRounds B P las f rest ⟨#[], [], #[], #[], #[]⟩
          let fa := B.toArray folded
          let truncated := Array.ofFn (n := 2 ^ P.logFinalPolyLen) fun i ↦
            fa.getD (reverseBits i P.logFinalPolyLen) 0
          let finalPoly := idft P.logFinalPolyLen truncated
          pObserveExts finalPoly.toList
          return { cp with finalPoly := finalPoly })
        (do
          let (folded, cp) ← commitRounds (specBackend EF) P las a as ⟨#[], [], #[], #[], #[]⟩
          let fa := (specBackend EF).toArray folded
          let truncated := Array.ofFn (n := 2 ^ P.logFinalPolyLen) fun i ↦
            fa.getD (reverseBits i P.logFinalPolyLen) 0
          let finalPoly := idft P.logFinalPolyLen truncated
          pObserveExts finalPoly.toList
          return { cp with finalPoly := finalPoly }) := by
    intro f a rest as hf hfs hfa hr hrs
    refine RelM.bind (commitRounds_refines hA h P las hf hfs hfa hr hrs h0) ?_
    rintro ⟨f1, c1⟩ ⟨f2, c2⟩ ⟨hv, hvs, hc⟩
    dsimp only
    rw [h.toArray hv (shapeOk_le hvs)]
    exact RelM.bind_eq fun _ ↦ RelM.pure
      ⟨hc.commits, hc.data, hc.witnesses, hc.arities, rfl⟩
  unfold commitPhase
  cases hi with
  | nil => exact tail (h.ofArray #[]) (Or.inl rfl) hfit .nil (fun _ h ↦ absurd h List.not_mem_nil)
  | cons hv hvs =>
    exact tail hv (hs _ List.mem_cons_self) hfit hvs fun x hx ↦ hs x (List.mem_cons_of_mem _ hx)

theorem openMulti_refines (h : Refines B) (capHeight : Nat) {c s} (hc : h.RC c s)
    (indices : List Nat) :
    openMulti B capHeight c indices = openMulti (specBackend EF) capHeight s indices := by
  have ho : B.openAt c = (specBackend EF).openAt s := funext fun i ↦ h.openAt i hc
  simp only [openMulti, ho, h.logHeight hc]

theorem answerFolds_refines (h : Refines B) (capHeight : Nat) {cs ss}
    (hcs : List.Forall₂ h.RC cs ss) :
    ∀ las cur, answerFolds B capHeight cs las cur =
      answerFolds (specBackend EF) capHeight ss las cur := by
  induction hcs with
  | nil => intro las cur; simp only [answerFolds]
  | cons hc _ ih =>
    intro las cur
    cases las with
    | nil => simp only [answerFolds]
    | cons la las => simp only [answerFolds, openMulti_refines h capHeight hc, ih]

/-- Rounds with related commitments and matrices and the same points. -/
abbrev RoundRel (h : Refines B) (r : OpenRound B) (s : OpenRound (specBackend EF)) : Prop :=
  h.RC r.1 s.1 ∧ List.Forall₂ (fun x y ↦ h.RM x.1 y.1 ∧ x.2 = y.2) r.2 s.2

theorem forall₂_and_mem {α β : Type} {R : α → β → Prop} {P : β → Prop} :
    ∀ {xs ys}, List.Forall₂ R xs ys → (∀ y ∈ ys, P y) →
      List.Forall₂ (fun a b ↦ R a b ∧ P b) xs ys
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons h hs, hp =>
    .cons ⟨h, hp _ List.mem_cons_self⟩
        (forall₂_and_mem hs fun y hy ↦ hp y (List.mem_cons_of_mem _ hy))

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
theorem proveFri_refines (hA : DomainsAddressable F EF) (h : Refines B) (P : Params)
    {rounds srounds} (hr : List.Forall₂ (RoundRel h) rounds srounds) {inputs sinputs}
    (hin : List.Forall₂ h.RV inputs sinputs) (hshape : ∀ x ∈ sinputs, ShapeOk (F := F) x)
    (bw : F) :
    RelM Eq (proveFri B P rounds inputs bw) (proveFri (specBackend EF) P srounds sinputs bw) := by
  rw [proveFri, proveFri]
  dsimp only
  rw [forall₂_map_eq (fun _ _ hv ↦ by rw [h.size hv]) hin]
  generalize hheights : sinputs.map (fun x ↦ ((specBackend EF).size x).log2) = heights
  generalize hlogMax : heights.headD 0 = logMax
  refine RelM.bind_eq fun _ ↦ ?_
  have hfit : FoldsFit (F := F) (foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen)
      logMax heights) (sinputs.headD #[]) := by
    have hsum := sum_foldSchedule_le P.maxLogArity (P.logBlowup + P.logFinalPolyLen) logMax heights
    rw [hlogMax] at hsum
    cases sinputs with
    | nil =>
      left
      subst hheights hlogMax
      cases (List.map (fun x ↦ ((specBackend EF).size x).log2) []).headD 0 <;> rfl
    | cons x xs =>
      have hl : logMax = x.size.log2 := by
        rw [← hlogMax, ← hheights, List.map_cons, List.headD_cons]
      rcases hshape x List.mem_cons_self with h0 | ⟨s, hs, hx⟩
      · left
        rw [hl, h0]
        rfl
      · right
        refine ⟨s, hs, hx, ?_⟩
        have hs' : logMax = s := by rw [hl, hx, Nat.log2_two_pow]
        rw [hs'] at hsum ⊢
        exact hsum
  refine RelM.bind (commitPhase_refines hA h P _ hin hshape hfit) fun cp cs hc ↦ ?_
  refine RelM.bind_eq fun qw ↦ RelM.bind_eq fun indices ↦ ?_
  have hins : (rounds.map fun (x : OpenRound B) ↦ match x with
      | (c, _) => openMulti B P.capHeight c (indices.map (· >>> (logMax - B.logHeight c)))) =
      srounds.map fun (x : OpenRound (specBackend EF)) ↦ match x with
      | (c, _) => openMulti (specBackend EF) P.capHeight c
          (indices.map (· >>> (logMax - (specBackend EF).logHeight c))) :=
    forall₂_map_eq (fun r s hrs ↦ by
      simp only [h.logHeight hrs.1, openMulti_refines h P.capHeight hrs.1]) hr
  rw [hins, hc.arities, answerFolds_refines h P.capHeight hc.data, hc.commits, hc.witnesses,
    hc.finalPoly]
  exact RelM.pure rfl

theorem mem_openItems {M : Type} {rounds : List (List (M × List EF))}
    {ov : List (List (List (Array EF)))} {x : M × List (EF × Array EF)}
    (hx : x ∈ openItems rounds ov) : ∃ ms ∈ rounds, ∃ y ∈ ms, x.1 = y.1 := by
  unfold openItems at hx
  obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp hx
  obtain ⟨⟨ms, os⟩, hmo, rfl⟩ := List.mem_map.mp hl
  obtain ⟨⟨⟨m, zs⟩, ys⟩, hp, rfl⟩ := List.mem_map.mp hxl
  exact ⟨ms, (List.of_mem_zip hmo).1, (m, zs), (List.of_mem_zip hp).1, rfl⟩

/-- `openPcs` of related rounds is the specification's. -/
theorem openPcs_refines (hA : DomainsAddressable F EF) (h : Refines B) (P : Params)
    {rounds srounds} (hr : List.Forall₂ (RoundRel h) rounds srounds) (hok : RoundsOk srounds) :
    RelM Eq (openPcs B P rounds) (openPcs (specBackend EF) P srounds) := by
  have hrs : List.Forall₂ (List.Forall₂ fun x y ↦ h.RM x.1 y.1 ∧ x.2 = y.2)
      (rounds.map (·.2)) (srounds.map (·.2)) :=
    forall₂_map (fun _ _ hrs ↦ hrs.2) hr
  have hsok : ∀ ms ∈ srounds.map (·.2), ∀ x ∈ ms, MatOk x.1 ∧ ∀ z ∈ x.2, Ext.OutsideBase z := by
    intro ms hms
    obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hms
    exact hok r hr'
  obtain ⟨hov, hred⟩ := h.openings P.logBlowup hrs hsok
  rw [openPcs, openPcs]
  generalize B.openings P.logBlowup (rounds.map (·.2)) = o at hov hred
  obtain ⟨ov, red⟩ := o
  dsimp only at hov hred ⊢
  subst hov
  refine RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦ RelM.bind_eq fun bw ↦
    RelM.bind_eq fun alpha ↦ ?_
  have hin := forall₂_map (S := h.RV) (f := (·.2)) (g := (·.2)) (fun _ _ hs ↦ hs.2) (hred alpha)
  have hshape : ∀ x ∈ ((specBackend EF).openings P.logBlowup (srounds.map (·.2))).2 alpha |>.map
      (·.2), ShapeOk (F := F) x := fun x hx ↦ by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    refine Or.inr (reduce_shape alpha _ (fun x hx ↦ ?_) y hy)
    obtain ⟨ms, hms, z, hz, e⟩ := mem_openItems hx
    rw [e]
    exact (hsok ms hms z hz).1
  refine RelM.bind (proveFri_refines hA h P hr hin hshape bw) fun fri _ hf ↦ hf ▸ ?_
  exact RelM.pure rfl

end CompStark.Fri
