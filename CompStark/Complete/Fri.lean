/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Complete.FriRound

/-! # FRI completeness

The verifier's FRI accepts the specification prover's proof of one low-degree input
(`verifyFri_proveFri`).

The prover's commit rounds are a pure chain over the fold schedule (`chain`,
`commitRounds_run`): each round commits to the groups of the folded vector, grinds, samples `β`
and folds. The verifier replays the transcript: it observes the same domain separator and
commitments, the grinding witnesses check, and it samples the same `β`s and query indices. Each
query's folds walk the chain at the query's index: the verifier puts the running value back
between the siblings and recovers the opened group, whose `foldRow` is the next folded vector's
entry. The last folded vector has low degree, so the final polynomial evaluates to the last
entry. Every round's groups at the queries are an honest multi-opening of its commitment
(`verifyMulti_openMulti`).
-/

@[expose] public section
namespace CompStark.Complete
open CompStark.Stark CompStark.Fri

variable {F : Type}
local notation "hashF" => CompStark.Hash.Poseidon2.hash F
local notation "compF" => CompStark.Hash.Poseidon2.compress F

theorem prun_bind {α β : Type} (x : PM F 24 α) (f : α → PM F 24 β) (t : Transcript F 24) :
    (x >>= f).run t = (f (x.run t).1).run (x.run t).2 := rfl

variable [BaseField F]

/-! ### Observing on any field -/

theorem duplex_observe (t : Transcript F 24) (x : F) : (t.observe x).duplex = t.duplex := rfl

theorem foldl_observe (t : Transcript F 24) (xs : List F) :
    xs.foldl Transcript.observe t = t.observeList xs := by
  unfold Transcript.observeList Challenger.observeList
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih]; rfl

theorem flag_observeList (t : Transcript F 24) (xs : List F) :
    (t.observeList xs).grindFailed = t.grindFailed := by
  unfold Transcript.observeList; dsimp only

theorem flag_observe (t : Transcript F 24) (x : F) : (t.observe x).grindFailed = t.grindFailed := by
  unfold Transcript.observe; dsimp only

theorem duplex_observeList (t : Transcript F 24) (xs : List F) :
    (t.observeList xs).duplex = t.duplex := rfl

variable {EF : Type} [Challenge F EF]

/-! ### The verifier's monad on Poseidon2

On Poseidon2 the verifier's challenger is the prover's transcript: its steps are the transcript's.
Sampling bits reads the canonical value of the transcript's duplex, so it needs that duplex to be
Plonky3's (`Poseidon2.duplex`), which every step keeps. -/

theorem bind_ok [Poseidon2Field F] {α β : Type} {x : M (poseidon2 F) α}
    {f : α → M (poseidon2 F) β} {t t' : Transcript F 24} {a : α}
    (h : x t = .ok (a, t')) : (x >>= f) t = f a t' := by
  show StateT.bind x f t = _
  simp only [StateT.bind, h]
  rfl
theorem sample_bind [Poseidon2Field F] {β : Type} (f : F → M (poseidon2 F) β)
    (t : Transcript F 24) :
    (sample (poseidon2 F) >>= f) t = f t.sample.1 t.sample.2 := bind_ok rfl
theorem sampleList_run [Poseidon2Field F] (t : Transcript F 24) :
    ∀ k, sampleList (poseidon2 F) k t = .ok (t.sampleList k)
  | 0 => rfl
  | k + 1 => by
    simp only [sampleList, sample_bind]
    rw [bind_ok (sampleList_run _ k)]
    rfl
theorem sampleExt_run [Poseidon2Field F] (t : Transcript F 24) :
    (sampleExt (poseidon2 F) : M (poseidon2 F) EF) t =
      .ok ((t.sampleExtValue : EF), (Transcript.sampleExtState EF t)) := by
  simp only [sampleExt, Transcript.sampleExtValue, Transcript.sampleExtState]
  rw [bind_ok (sampleList_run t _)]
  rfl
theorem sampleBits_run [Poseidon2Field F] (t : Transcript F 24) (bits : Nat)
    (hd : t.duplex = Poseidon2.duplex) :
    sampleBits (poseidon2 F) bits t = .ok (t.sampleBits bits) := by
  unfold sampleBits Transcript.sampleBits Challenger.sampleBits
  rw [sample_bind]
  unfold Transcript.sample
  rw [hd]
  generalize Challenger.sample Poseidon2.duplex t.state = p
  obtain ⟨x, c⟩ := p
  rfl
theorem checkWitness_run [Poseidon2Field F] (t : Transcript F 24) (bits : Nat) (w : F)
    (hd : t.duplex = Poseidon2.duplex) :
    checkWitness (poseidon2 F) bits w t = .ok (t.checkWitness bits w) := by
  unfold checkWitness Transcript.checkWitness Challenger.checkWitness
  split
  · rfl
  · rw [bind_ok (t' := t.observe w) (a := ()) rfl,
      bind_ok (a := ((t.observe w).sampleBits bits).1) (t' := ((t.observe w).sampleBits bits).2)
        (sampleBits_run _ _ ((duplex_observe t w).trans hd))]
    unfold Transcript.sampleBits Transcript.observe
    generalize Challenger.sampleBits t.duplex (Challenger.observe t.duplex t.state w) bits = p
    obtain ⟨b, c⟩ := p
    rfl
theorem observeList_run [Poseidon2Field F] (t : Transcript F 24) (xs : List F) :
    observeList (poseidon2 F) xs t = .ok ((), t.observeList xs) := by
  rw [← foldl_observe]; rfl
theorem observeExts_run [Poseidon2Field F] (t : Transcript F 24) (xs : List EF) :
    observeExts (poseidon2 F) xs t = .ok ((), t.observeExts xs) := by
  unfold observeExts
  show Except.ok ((), xs.foldl (fun s x ↦ (Ext.coeffs x).foldl Transcript.observe s) t) = _
  simp only [foldl_observe]
  rfl

theorem ensure_true [Poseidon2Field F] (msg : String) : ensure (H := (poseidon2 F)) true msg = pure
    () := rfl

/-! ### The commit rounds as a chain -/

/-- One fold of the commit phase by `2 ^ la` at `β`. -/
def foldOnce (la : Nat) (beta : EF) (f : Array EF) : Array EF :=
  let rows := f.size / 2 ^ la
  if la = 1 then foldPairs f beta (Nat.log2 rows) else
    Array.ofFn (n := rows) fun i ↦ foldRow i (Nat.log2 rows) la beta
      ((List.range (2 ^ la)).map fun k ↦ f.getD (i * 2 ^ la + k) 0)

/-- A commit round: its log arity, the folded vector it starts from, the transcript before it, its
grinding witness and its folding challenge. -/
structure Rd (EF : Type) [Challenge F EF] where
  la : Nat
  folded : Array EF
  t : Transcript F 24
  w : F
  beta : EF

/-- A round's commitment. -/
def Rd.c [Poseidon2Field F] (r : Rd EF) : Committed F := Committed.ofMats hashF compF
    [(specBackend EF).leaves (2 ^ r.la) r.folded]

/-- The commit rounds of the specification prover with log arities `las` on one input, the final
vector and transcript. -/
def chain [Poseidon2Field F] (P : Params) :
    List Nat → Array EF → Transcript F 24 → List (Rd EF) × Array EF × Transcript F 24
  | [], f, t => ([], f, t)
  | la :: las, f, t =>
    let t1 := t.observeList
        (Committed.ofMats hashF compF [(specBackend EF).leaves (2 ^ la) f]).root.toList
    let t2 := (t1.grind P.commitPowBits).2
    let beta := (t2.sampleExtValue : EF)
    let r := chain P las (foldOnce la beta f) (Transcript.sampleExtState EF t2)
    (⟨la, f, t, (t1.grind P.commitPowBits).1, beta⟩ :: r.1, r.2)

/-- Record a round in the commit phase's result. -/
def pushRd [Poseidon2Field F] (cp : CommitPhase F EF (Committed F)) (r : Rd EF) : CommitPhase F EF
    (Committed F) :=
  ⟨cp.commits.push r.c.root, cp.data ++ [r.c], cp.witnesses.push r.w, cp.arities.push r.la,
    cp.finalPoly⟩

theorem commitRounds_run [Poseidon2Field F] (P : Params) :
    ∀ (las : List Nat) (f : Array EF) (cp : CommitPhase F EF (Committed F))
        (t : Transcript F 24),
      (commitRounds (specBackend EF) P las f [] cp).run t =
        let r := chain P las f t
        ((r.2.1, r.1.foldl pushRd cp), r.2.2)
  | [], f, cp, t => rfl
  | la :: las, f, cp, t => by
    simp only [commitRounds, chain]
    rw [prun_bind, prun_bind, prun_bind]
    dsimp only [foldOnce, specBackend, Backend.spec, id]
    exact commitRounds_run P las _ _ _

/-! ### The low-degree invariant of the commit rounds -/

/-- The folded vector has height `2 ^ h`, not below the final height, and low degree. -/
def Good (P : Params) (h : Nat) (f : Array EF) : Prop :=
  P.logBlowup + P.logFinalPolyLen ≤ h ∧ LowDegree h (h - P.logBlowup) f

theorem log2_size {h d : Nat} {v : Array EF} (hv : LowDegree h d v) : Nat.log2 v.size = h := by
  rw [hv.1, Nat.log2_two_pow]

/-- The fold of a vector of `2 ^ h` values is the groups' `foldRow`s. -/
theorem foldOnce_eq (la h : Nat) (beta : EF) (f : Array EF) (hs : f.size = 2 ^ h)
    (hla : la ≤ h) (h24 : h ≤ twoAdicity F) (hla1 : 1 ≤ la) :
    foldOnce la beta f = Array.ofFn (n := 2 ^ (h - la)) fun i ↦ foldRow i (h - la) la beta
      ((List.range (2 ^ la)).map fun k ↦ f.getD (i * 2 ^ la + k) 0) := by
  have hrows : f.size / 2 ^ la = 2 ^ (h - la) := by rw [hs, Nat.pow_div hla (by decide)]
  unfold foldOnce
  dsimp only
  rw [hrows, Nat.log2_two_pow]
  split
  · rename_i h1
    subst h1
    apply Array.ext (by rw [size_foldPairs, Array.size_ofFn])
    intro i h1 h2
    rw [Array.size_ofFn] at h2
    rw [← getD_lt _ i h1, foldPairs_getD f beta (h - 1) (by omega) i h2, Array.getElem_ofFn]
  · rfl

theorem size_foldOnce (la h : Nat) (beta : EF) (f : Array EF) (hs : f.size = 2 ^ h)
    (hla : la ≤ h) (h24 : h ≤ twoAdicity F) (hla1 : 1 ≤ la) : (foldOnce la beta f).size = 2 ^
        (h - la) := by
  rw [foldOnce_eq la h beta f hs hla h24 hla1, Array.size_ofFn]

theorem lowDegree_foldOnce (P : Params) (la h : Nat) (beta : EF) (f : Array EF)
    (hf : LowDegree h (h - P.logBlowup) f) (hla : la ≤ h - P.logBlowup) (hla1 : 1 ≤ la) :
    LowDegree (h - la) (h - la - P.logBlowup) (foldOnce la beta f) := by
  have h24 := hf.2.1
  rw [foldOnce_eq la h beta f hf.1 (by omega) h24 hla1]
  refine lowDegree_foldRows f (h - la) la (h - la - P.logBlowup) beta ?_
  rwa [show h - la + la = h by omega, show h - la - P.logBlowup + la = h - P.logBlowup by omega]

/-- A round folding by `1 ≤ la` bits, not below the final height, keeps the invariant. -/
theorem good_step (P : Params) {h : Nat} {f : Array EF} (hg : Good P h f) (la : Nat)
    (h1 : 1 ≤ la) (h2 : la ≤ h - (P.logBlowup + P.logFinalPolyLen)) (beta : EF) :
    Good P (h - la) (foldOnce la beta f) :=
  ⟨by have := hg.1; omega, lowDegree_foldOnce P la h beta f hg.2 (by omega) h1⟩

/-- The chain by arities of at least one bit adding up to the excess over the final height ends at
the final height with a low-degree vector. -/
theorem chain_final [Poseidon2Field F] (P : Params) : ∀ (las : List Nat) (h : Nat)
    (f : Array EF) (t : Transcript F 24), Good P h f →
      las.sum = h - (P.logBlowup + P.logFinalPolyLen) → (∀ la ∈ las, 1 ≤ la) →
      LowDegree (P.logBlowup + P.logFinalPolyLen) P.logFinalPolyLen (chain P las f t).2.1
  | [], h, f, t, hg, hsum, _ => by
    have hh : h = P.logBlowup + P.logFinalPolyLen := by have := hg.1; simp at hsum; omega
    subst hh
    have := hg.2
    rwa [show P.logBlowup + P.logFinalPolyLen - P.logBlowup = P.logFinalPolyLen by omega] at this
  | la :: las, h, f, t, hg, hsum, hpos => by
    rw [List.sum_cons] at hsum
    have h1 := hpos la List.mem_cons_self
    exact chain_final P las (h - la) _ _ (good_step P hg la h1 (by omega) _) (by omega)
      fun x hx ↦ hpos x (List.mem_cons_of_mem _ hx)

/-- Plonky3's schedule for one input folds by at least one bit per round, down to the final
height. -/
theorem foldArities_spec (m r : Nat) (hm : 0 < m) :
    (foldArities m r).sum = r ∧ ∀ la ∈ foldArities m r, 1 ≤ la ∧ la ≤ r := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    rcases r with _ | r
    · rw [foldArities]; exact ⟨rfl, fun _ h ↦ absurd h List.not_mem_nil⟩
    · rw [foldArities]
      obtain ⟨h1, h2⟩ := ih (r + 1 - max 1 (min m (r + 1))) (by omega)
      refine ⟨by rw [List.sum_cons, h1]; omega, fun la hla ↦ ?_⟩
      rcases List.mem_cons.mp hla with rfl | hla
      · omega
      · have := h2 la hla; omega

/-! ### The transcript's failure flag

Observing and sampling keep the flag, and grinding only sets it, so a final transcript without
the flag had every grind of the run check. -/

theorem flag_observeExts (t : Transcript F 24) (xs : List EF) :
    (t.observeExts xs).grindFailed = t.grindFailed := by
  unfold Transcript.observeExts
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    unfold Transcript.observeExt Transcript.observeList; dsimp only

theorem flag_sampleList (t : Transcript F 24) :
    ∀ k, (t.sampleList k).2.grindFailed = t.grindFailed
  | 0 => rfl
  | k + 1 => (flag_sampleList _ k).trans rfl

theorem flag_sampleExt (t : Transcript F 24) :
    (Transcript.sampleExtState EF t).grindFailed = t.grindFailed := by
  unfold Transcript.sampleExtState; exact flag_sampleList t _

theorem flag_sampleBits (t : Transcript F 24) (bits : Nat) :
    (t.sampleBits bits).2.grindFailed = t.grindFailed := by
  unfold Transcript.sampleBits; dsimp only

theorem flag_foldl_observe (l : List Nat) :
    ∀ t : Transcript F 24, (l.foldl (fun t (a : Nat) ↦ t.observe (a : F)) t).grindFailed =
      t.grindFailed := by
  induction l with
  | nil => intro t; rfl
  | cons a l ih => intro t; rw [List.foldl_cons, ih, flag_observe]

theorem flag_checkWitness (t : Transcript F 24) (bits : Nat) (w : F) :
    (t.checkWitness bits w).2.grindFailed = t.grindFailed := by
  unfold Transcript.checkWitness; dsimp only

theorem grind_of_ne (t : Transcript F 24) (bits : Nat) (h0 : bits ≠ 0) :
    t.grind bits = (t.grinder t.state bits,
      { (t.checkWitness bits (t.grinder t.state bits)).2 with
        grindFailed := (t.checkWitness bits (t.grinder t.state bits)).2.grindFailed ||
          !(t.checkWitness bits (t.grinder t.state bits)).1 }) := by
  unfold Transcript.grind
  rw [ite_eq_right h0]

/-- Without the flag after a grind, the transcript had no flag before it. -/
theorem flag_grind (t : Transcript F 24) (bits : Nat)
    (h : (t.grind bits).2.grindFailed = false) : t.grindFailed = false := by
  by_cases h0 : bits = 0
  · subst h0; exact h
  · rw [grind_of_ne t bits h0] at h
    rw [← flag_checkWitness t bits (t.grinder t.state bits)]
    exact (Bool.or_eq_false_iff.mp h).1

/-- A grind that leaves no flag found a witness that checks. -/
theorem checkWitness_grind (t : Transcript F 24) (bits : Nat)
    (h : (t.grind bits).2.grindFailed = false) :
    t.checkWitness bits (t.grind bits).1 = (true, (t.grind bits).2) := by
  by_cases h0 : bits = 0
  · subst h0; rfl
  · rw [grind_of_ne t bits h0] at h ⊢
    generalize t.checkWitness bits (t.grinder t.state bits) = cw at h ⊢
    obtain ⟨b, t'⟩ := cw
    cases b
    · simp only [Bool.not_false, Bool.or_true, reduceCtorEq] at h
    · simp only [Bool.not_true, Bool.or_false]

/-! ### The transcript's duplex

Every step keeps the transcript's duplex, so a run from `Transcript.init` stays on Plonky3's,
as the verifier's `sampleBits` and `checkWitness` need. -/

theorem duplex_observeExts (t : Transcript F 24) (xs : List EF) :
    (t.observeExts xs).duplex = t.duplex := by
  unfold Transcript.observeExts
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih]; rfl

theorem duplex_sampleList (t : Transcript F 24) : ∀ k, (t.sampleList k).2.duplex = t.duplex
  | 0 => rfl
  | k + 1 => (duplex_sampleList _ k).trans rfl

theorem duplex_sampleExt (t : Transcript F 24) :
    (Transcript.sampleExtState EF t).duplex = t.duplex := by
  unfold Transcript.sampleExtState; exact duplex_sampleList t _

theorem duplex_sampleBits (t : Transcript F 24) (bits : Nat) :
    (t.sampleBits bits).2.duplex = t.duplex := by
  unfold Transcript.sampleBits; dsimp only

theorem duplex_checkWitness (t : Transcript F 24) (bits : Nat) (w : F) :
    (t.checkWitness bits w).2.duplex = t.duplex := by
  unfold Transcript.checkWitness; dsimp only

theorem duplex_grind (t : Transcript F 24) (bits : Nat) : (t.grind bits).2.duplex = t.duplex := by
  by_cases h0 : bits = 0
  · subst h0; rfl
  · rw [grind_of_ne t bits h0]
    exact duplex_checkWitness t bits (t.grinder t.state bits)

theorem duplex_foldl_observe (l : List Nat) :
    ∀ t : Transcript F 24, (l.foldl (fun t (a : Nat) ↦ t.observe (a : F)) t).duplex = t.duplex := by
  induction l with
  | nil => intro t; rfl
  | cons a l ih => intro t; rw [List.foldl_cons, ih]; rfl

theorem duplex_chain [Poseidon2Field F] (P : Params) :
    ∀ (las : List Nat) (f : Array EF) (t : Transcript F 24),
      (chain P las f t).2.2.duplex = t.duplex
  | [], _, _ => rfl
  | la :: las, f, t => by
    rw [chain]
    dsimp only
    rw [duplex_chain, duplex_sampleExt, duplex_grind, duplex_observeList]

theorem forIn_cons_ok [Poseidon2Field F] {α σ : Type} (a : α) (l : List α) (b b' : σ)
    (body : α → σ → M (poseidon2 F) (ForInStep σ)) (t t' : Transcript F 24)
    (h : body a b t = .ok (.yield b', t')) : forIn (a :: l) b body t = forIn l b' body t' := by
  rw [List.forIn_cons, bind_ok h]

/-- Without the flag after the commit rounds, there was none before them. -/
theorem flag_chain [Poseidon2Field F] (P : Params) :
    ∀ (las : List Nat) (f : Array EF) (t : Transcript F 24),
      (chain P las f t).2.2.grindFailed = false → t.grindFailed = false
  | [], _, _, h => h
  | la :: las, f, t, h => by
    rw [chain] at h
    have := flag_chain P las _ _ h
    rw [flag_sampleExt] at this
    rw [← flag_observeList t _]
    exact flag_grind _ _ this

/-! ### The verifier's commit loop -/

/-- The body of the verifier's loop over the commitments. -/
def commitBody [Poseidon2Field F] (P : Params) (c : Digest F) (w : F) (betas : Array EF) : M
    (poseidon2 F) (ForInStep (Array EF)) :=
  do
  observeList (poseidon2 F) c.toList
  let ok ← checkWitness (poseidon2 F) P.commitPowBits w
  ensure ok "commit witness"
  let beta ← (sampleExt (poseidon2 F) : M (poseidon2 F) EF)
  pure (ForInStep.yield (betas.push beta))

theorem commitBody_run [Poseidon2Field F] (P : Params) (c : Digest F) (w : F) (b : Array EF)
    (t t2 : Transcript F 24)
    (hd : t.duplex = Poseidon2.duplex)
    (h : (t.observeList c.toList).checkWitness P.commitPowBits w = (true, t2)) :
    commitBody P c w b t = .ok (.yield (b.push (t2.sampleExtValue : EF)),
        (Transcript.sampleExtState EF t2)) := by
  unfold commitBody
  rw [bind_ok (observeList_run t c.toList),
    bind_ok (t' := t2) (a := true) (by
      rw [checkWitness_run _ _ _ ((duplex_observeList t _).trans hd), h]),
    ensure_true, pure_bind, bind_ok (sampleExt_run t2)]
  rfl

/-- The verifier observes the prover's commitments, its witnesses check, and it samples the
prover's folding challenges. -/
theorem commit_loop [Poseidon2Field F] (P : Params)
    (body : Digest F × F → Array EF → M (poseidon2 F) (ForInStep (Array EF)))
    (hbody : ∀ c w b, body (c, w) b = commitBody P c w b) :
    ∀ las f t betas, t.duplex = Poseidon2.duplex →
      (chain P las f t).2.2.grindFailed = false →
      forIn (((chain P las f t).1.map (·.c.root)).zip ((chain P las f t).1.map (·.w)))
        betas body t =
        .ok (betas ++ ((chain P las f t).1.map (·.beta)).toArray, (chain P las f t).2.2)
  | [], f, t, betas, _, _ => by
    simp only [chain, List.map_nil, List.zip_nil_left, List.forIn_nil, Array.append_empty]
    rfl
  | la :: las, f, t, betas, hd, ht => by
    rw [chain] at ht ⊢
    dsimp only at ht ⊢
    rw [List.map_cons, List.map_cons, List.zip_cons_cons, List.map_cons]
    generalize ht1 : t.observeList _ = t1 at ht ⊢
    have hd1 : (Transcript.sampleExtState EF
        ((t1.grind P.commitPowBits).2)).duplex = Poseidon2.duplex := by
      rw [duplex_sampleExt, duplex_grind, ← ht1, duplex_observeList, hd]
    have hg1 : (t1.grind P.commitPowBits).2.grindFailed = false := by
      have := flag_chain P las _ _ ht
      rwa [flag_sampleExt] at this
    rw [forIn_cons_ok _ _ _ _ _ _ _ (by
      rw [hbody]
      exact commitBody_run P _ _ _ t _ hd (by
        show (t.observeList
            (Committed.ofMats hashF compF [(specBackend EF).leaves (2 ^ la) f]).root.toList
          ).checkWitness P.commitPowBits (t1.grind P.commitPowBits).1 = _
        rw [ht1]; exact checkWitness_grind _ _ hg1)),
      commit_loop P body hbody las _ _ _ hd1 ht]
    refine congrArg Except.ok (Prod.ext (Array.toList_inj.mp ?_) rfl)
    simp only [Array.toList_append, Array.toList_push, List.append_assoc,
      List.singleton_append]

/-! ### A query's folds -/

/-- The body of the verifier's loop over a query's folds. -/
def foldBody [Poseidon2Field F] {K : Type} [Challenge F K] (q : Nat) (beta : K) (la : Nat)
    (o : CommitOpening F K) (ro : List (Nat × K)) (eval : K) (index logH : Nat)
    (groups : List (Nat × List K)) :
    M (poseidon2 F) (ForInStep (List (Nat × K) × K × Nat × Nat × List (Nat × List K))) := do
  let arity := 2 ^ la
  let sibs := o.siblings.getD q #[]
  ensure (sibs.size == arity - 1) "sibling count"
  let pos := index % arity
  let evals := (List.range arity).map fun j ↦
    if j < pos then sibs.getD j 0 else if j = pos then eval else sibs.getD (j - 1) 0
  let logFolded := logH - la
  let index := index >>> la
  let groups := groups ++ [(index, evals)]
  let eval := foldRow index logFolded la beta evals
  match ro with
  | (h, r) :: rest =>
    if h == logFolded then
      pure (ForInStep.yield (rest, eval + Ext.powTwo beta la * r, index, logFolded, groups))
    else pure (ForInStep.yield (ro, eval, index, logFolded, groups))
  | [] => pure (ForInStep.yield (ro, eval, index, logFolded, groups))

/-- The group of `idx` at `la` bits of a vector: its group index and its `2 ^ la` values. -/
def groupAt (la : Nat) (f : Array EF) (idx : Nat) : Nat × List EF :=
  (idx >>> la, (List.range (2 ^ la)).map fun k ↦ f.getD ((idx >>> la) * 2 ^ la + k) 0)

/-- The groups a query at `idx` opens in the rounds `rs`. -/
def qGroups : List (Rd EF) → Nat → List (Nat × List EF)
  | [], _ => []
  | r :: rs, idx => groupAt r.la r.folded idx :: qGroups rs (idx >>> r.la)

/-- The siblings a round answers a query at `idx` with: the group of `idx` without `idx`. -/
def sibsAt [Poseidon2Field F] (r : Rd EF) (idx : Nat) : Array EF :=
  let ev := unflatten (((r.c.openAt (idx >>> r.la)).values.getD 0 #[]).toList)
  (((List.range (2 ^ r.la)).filter (· != idx % 2 ^ r.la)).map fun j ↦ ev.getD j 0).toArray

theorem siblings_answerFolds [Poseidon2Field F] (r : Rd EF) (cur : List Nat) :
    (cur.zip (openMulti (specBackend EF) r.c (cur.map (· >>> r.la))).values.toList).map
        (fun (x : Nat × Array (Array F)) ↦
          let evals : List EF := unflatten ((x.2.getD 0 #[]).toList)
          (((List.range (2 ^ r.la)).filter (· != x.1 % 2 ^ r.la)).map fun j ↦
            evals.getD j 0).toArray) = cur.map (sibsAt r) := by
  apply List.ext_getElem (by simp only [openMulti, List.length_map, List.length_zip,
    List.toList_toArray, Nat.min_self])
  intro i h1 h2
  simp only [openMulti, List.toList_toArray, List.getElem_map, List.getElem_zip, sibsAt]
  rfl

theorem answerFolds_cons [Poseidon2Field F] (r : Rd EF) (rs : List (Rd EF)) (las : List Nat)
    (cur : List Nat) :
    answerFolds (specBackend EF) ((r :: rs).map (·.c)) (r.la :: las) cur =
      ⟨(cur.map (sibsAt r)).toArray,
        (openMulti (specBackend EF) r.c (cur.map (· >>> r.la))).siblings⟩ ::
        answerFolds (specBackend EF) (rs.map (·.c)) las (cur.map (· >>> r.la)) := by
  rw [← siblings_answerFolds]
  rfl

/-- One fold of a query at `idx`: the verifier recovers the group of `idx` from the siblings, folds
it to the next vector's entry, and records the group. -/
theorem fold_round [Poseidon2Field F] (P : Params) {h : Nat} {f : Array EF} (hg : Good P h f)
    (r : Rd EF) (hr : r.folded = f) (h1 : 1 ≤ r.la)
    (h2 : r.la ≤ h - (P.logBlowup + P.logFinalPolyLen)) (idx q : Nat) (hidx : idx < 2 ^ h)
    (o : CommitOpening F EF) (ho : o.siblings.getD q #[] = sibsAt r idx)
    (gs : List (Nat × List EF)) (t : Transcript F 24) :
    foldBody q r.beta r.la o [] (f.getD idx 0) idx h gs t =
      .ok (.yield ([], (foldOnce r.la r.beta f).getD (idx >>> r.la) 0, idx >>> r.la, h - r.la,
        gs ++ [groupAt r.la f idx]), t) := by
  obtain ⟨la, f', t0, w, beta⟩ := r
  dsimp only at hr h1 h2 ho ⊢
  subst hr
  have hsz := hg.2.1
  have h24 := hg.2.2.1
  obtain ⟨hs1, hs2, -⟩ := answer_round f' h la idx hsz (by omega) hidx
  have hr' : idx >>> la < 2 ^ (h - la) := by
    rw [Nat.shiftRight_eq_div_pow]
    refine Nat.div_lt_of_lt_mul ?_
    rw [← pow_add, Nat.add_sub_cancel' (by omega)]; exact hidx
  have hfold : foldRow (idx >>> la) (h - la) la beta
      ((List.range (2 ^ la)).map fun k ↦ f'.getD ((idx >>> la) * 2 ^ la + k) 0) =
      (foldOnce la beta f').getD (idx >>> la) 0 := by
    rw [foldOnce_eq la h beta f' hsz (by omega) h24 h1,
      CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ hr']
  unfold foldBody
  rw [ho]
  simp only [sibsAt, Rd.c] at hs1 hs2 ⊢
  rw [hs1, beq_self_eq_true, ensure_true, pure_bind, hs2, hfold]
  rfl

/-- A query's folds walk the chain at the query's index: they end at the final vector's entry and
record the groups the query opens. -/
theorem fold_loop [Poseidon2Field F] (P : Params) (q : Nat)
    (body : (EF × Nat) × CommitOpening F EF →
      List (Nat × EF) × EF × Nat × Nat × List (Nat × List EF) →
      M (poseidon2 F) (ForInStep (List (Nat × EF) × EF × Nat × Nat × List (Nat × List EF))))
    (hbody : ∀ beta la o ro eval index logH groups,
      body ((beta, la), o) (ro, eval, index, logH, groups) =
        foldBody q beta la o ro eval index logH groups) :
    ∀ (las : List Nat) (h : Nat) (f : Array EF) (t : Transcript F 24) (cur : List Nat)
      (hq : q < cur.length) (t' : Transcript F 24) (gs : List (Nat × List EF)),
      Good P h f → las.sum ≤ h - (P.logBlowup + P.logFinalPolyLen) → (∀ la ∈ las, 1 ≤ la) →
      cur[q] < 2 ^ h →
      forIn ((((chain P las f t).1.map (·.beta)).zip las).zip
          (answerFolds (specBackend EF) ((chain P las f t).1.map (·.c)) las cur))
        ([], f.getD cur[q] 0, cur[q], h, gs) body t' =
        .ok (([], (chain P las f t).2.1.getD (cur[q] >>> las.sum) 0, cur[q] >>> las.sum,
          h - las.sum, gs ++ qGroups (chain P las f t).1 cur[q]), t')
  | [], h, f, t, cur, hq, t', gs, _, _, _, _ => by
    simp only [chain, List.map_nil, List.zip_nil_left, List.forIn_nil, List.sum_nil,
      Nat.shiftRight_zero, Nat.sub_zero, qGroups, List.append_nil]
    rfl
  | la :: las, h, f, t, cur, hq, t', gs, hg, hsum, hpos, hidx => by
    rw [List.sum_cons] at hsum
    have h1 := hpos la List.mem_cons_self
    rw [chain]
    dsimp only
    generalize ht2 : ((t.observeList _).grind P.commitPowBits) = g2
    obtain ⟨w, t2⟩ := g2
    dsimp only
    set r : Rd EF := ⟨la, f, t, w, (t2.sampleExtValue : EF)⟩ with hr
    rw [show (la :: las) = r.la :: las from rfl, answerFolds_cons, List.map_cons,
      List.zip_cons_cons, List.zip_cons_cons,
      forIn_cons_ok _ _ _ _ _ _ _ (by
        rw [hbody]
        exact fold_round P hg r rfl h1 (by show la ≤ _; omega) cur[q] q hidx _ (by
          simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
            List.getElem?_eq_getElem hq, Option.map_some, Option.getD_some]) gs t')]
    have hq' : q < (cur.map (· >>> la)).length := by rw [List.length_map]; exact hq
    have hidx' : (cur.map (· >>> la))[q] < 2 ^ (h - la) := by
      rw [List.getElem_map, Nat.shiftRight_eq_div_pow]
      refine Nat.div_lt_of_lt_mul ?_
      rw [← pow_add, Nat.add_sub_cancel' (by omega : la ≤ h)]; exact hidx
    have ih := fold_loop P q body hbody las (h - la) (foldOnce la (t2.sampleExtValue : EF) f)
      (Transcript.sampleExtState EF t2) (cur.map (· >>> la)) hq' t' (gs ++ [groupAt la f cur[q]])
      (good_step P hg la h1 (by omega) _) (by omega)
      (fun x hx ↦ hpos x (List.mem_cons_of_mem _ hx)) hidx'
    rw [List.getElem_map] at ih
    rw [ih, ← Nat.shiftRight_add, show h - la - las.sum = h - (la + las.sum) by omega,
      List.append_assoc, List.singleton_append]
    rfl

/-- A query's folds from its one reduced opening end at the final vector's entry, with the groups
the query opens. -/
theorem foldQuery_run [Poseidon2Field F] (P : Params) (h0 : Nat) (f0 : Array EF) (hg : Good P h0 f0)
    (las : List Nat) (hsum : las.sum = h0 - (P.logBlowup + P.logFinalPolyLen))
    (hpos : ∀ la ∈ las, 1 ≤ la) (t : Transcript F 24) (cur : List Nat) (q : Nat)
    (hq : q < cur.length) (hidx : cur[q] < 2 ^ h0) (t' : Transcript F 24) :
    foldQuery (poseidon2 F) P h0 cur[q] q ((chain P las f0 t).1.map (·.beta)) las
      (answerFolds (specBackend EF) ((chain P las f0 t).1.map (·.c)) las cur)
      [(h0, f0.getD cur[q] 0)] t' =
      .ok (((chain P las f0 t).2.1.getD (cur[q] >>> las.sum) 0, cur[q] >>> las.sum,
        qGroups (chain P las f0 t).1 cur[q]), t') := by
  unfold foldQuery
  simp only [pure_bind, beq_self_eq_true, ensure_true, List.tail_cons]
  rw [bind_ok (fold_loop P q _ (fun _ _ _ _ _ _ _ _ ↦ rfl) las h0 f0 t cur hq t' [] hg
    (le_of_eq hsum) hpos hidx)]
  have hfin : h0 - las.sum = P.logBlowup + P.logFinalPolyLen := by
    have := hg.1; omega
  simp only [hfin, beq_self_eq_true, ensure_true, pure_bind, List.isEmpty_nil, List.nil_append]
  rfl

/-! ### The commit phase's result and the queries -/

theorem foldl_pushRd [Poseidon2Field F] (rs : List (Rd EF)) :
    ∀ cp : CommitPhase F EF (Committed F),
      (rs.foldl pushRd cp).commits.toList = cp.commits.toList ++ rs.map (·.c.root) ∧
      (rs.foldl pushRd cp).data = cp.data ++ rs.map (·.c) ∧
      (rs.foldl pushRd cp).witnesses.toList = cp.witnesses.toList ++ rs.map (·.w) ∧
      (rs.foldl pushRd cp).arities.toList = cp.arities.toList ++ rs.map (·.la) ∧
      (rs.foldl pushRd cp).finalPoly = cp.finalPoly := by
  induction rs with
  | nil => intro cp; simp only [List.foldl_nil, List.map_nil, List.append_nil, and_self]
  | cons r rs ih =>
    intro cp
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih (pushRd cp r)
    rw [List.foldl_cons, h1, h2, h3, h4, h5]
    simp only [pushRd, Array.toList_push, List.map_cons, List.append_assoc, List.singleton_append,
      and_self]

theorem sampleBits_lt (t : Transcript F 24) (bits : Nat) : (t.sampleBits bits).1 < 2 ^ bits := by
  unfold Transcript.sampleBits Challenger.sampleBits
  dsimp only
  exact Nat.mod_lt _ (by positivity)

/-- The indices `n` queries sample. -/
def sampleIndices (logMax : Nat) : Nat → Transcript F 24 → List Nat × Transcript F 24
  | 0, t => ([], t)
  | n + 1, t =>
    let r := sampleIndices logMax n (t.sampleBits logMax).2
    ((t.sampleBits logMax).1 :: r.1, r.2)

/-- The prover's queries, each sampling its index. -/
theorem mapM_queries {α β : Type} (logMax : Nat) (mk : Nat → β) (g : α → PM F 24 β)
    (hg : ∀ a t, (g a).run t = (mk (t.sampleBits logMax).1, (t.sampleBits logMax).2)) :
    ∀ (l : List α) (t : Transcript F 24), (l.mapM g).run t =
      ((sampleIndices logMax l.length t).1.map mk, (sampleIndices logMax l.length t).2)
  | [], _ => rfl
  | a :: l, t => by
    rw [List.mapM_cons, prun_bind, hg, prun_bind, mapM_queries logMax mk g hg l]
    rfl

theorem flag_sampleIndices (logMax : Nat) :
    ∀ n (t : Transcript F 24), (sampleIndices logMax n t).2.grindFailed = t.grindFailed
  | 0, _ => rfl
  | n + 1, t => by
    rw [sampleIndices]; exact (flag_sampleIndices logMax n _).trans (flag_sampleBits _ _)

theorem length_sampleIndices (logMax : Nat) :
    ∀ n (t : Transcript F 24), (sampleIndices logMax n t).1.length = n
  | 0, _ => rfl
  | n + 1, t => by
    rw [sampleIndices, List.length_cons, length_sampleIndices logMax n]

/-- The final polynomial of a commit phase ending at `fin`. -/
def finalPolyOf (P : Params) (fin : Array EF) : Array EF :=
  idft P.logFinalPolyLen (Array.ofFn (n := 2 ^ P.logFinalPolyLen) fun i ↦
    fin.getD (reverseBits i P.logFinalPolyLen) 0)

theorem commitPhase_run [Poseidon2Field F] (P : Params) (las : List Nat) (f0 : Array EF)
    (t : Transcript F 24) :
    (commitPhase (specBackend EF) P las [f0]).run t =
      ({ (chain P las f0 t).1.foldl pushRd ⟨#[], [], #[], #[], #[]⟩ with
          finalPoly := finalPolyOf P (chain P las f0 t).2.1 },
        (chain P las f0 t).2.2.observeExts (finalPolyOf P (chain P las f0 t).2.1).toList) := by
  unfold commitPhase
  rw [prun_bind]
  erw [commitRounds_run]
  rfl

/-- The verifier's queries sample the prover's indices. -/
theorem sampleIndices_mapM [Poseidon2Field F] (logMax : Nat) :
    ∀ (n : Nat) (t : Transcript F 24), t.duplex = Poseidon2.duplex →
      (List.range n).mapM (fun _ ↦ sampleBits (poseidon2 F) logMax) t =
        .ok (sampleIndices logMax n t)
  | 0, _, _ => rfl
  | n + 1, t, hd => by
    rw [List.range_succ_eq_map, List.mapM_cons, List.mapM_map]
    rw [bind_ok (a := (t.sampleBits logMax).1) (t' := (t.sampleBits logMax).2)
      (sampleBits_run t logMax hd)]
    have ih := sampleIndices_mapM logMax n _ ((duplex_sampleBits t logMax).trans hd)
    rw [show ((List.range n).mapM ((fun _ ↦ sampleBits (poseidon2 F) logMax) ∘ Nat.succ)) =
      (List.range n).mapM (fun _ ↦ sampleBits (poseidon2 F) logMax) from rfl,
      bind_ok ih]
    rfl

/-- The prover samples its indices as the verifier does. -/
theorem sampleIndices_pmapM (logMax : Nat) :
    ∀ (n : Nat) (t : Transcript F 24),
      ((List.range n).mapM (fun _ ↦ (pSampleBits logMax : PM F 24 Nat))).run t =
        sampleIndices logMax n t
  | 0, _ => rfl
  | n + 1, t => by
    rw [List.range_succ_eq_map, List.mapM_cons, List.mapM_map, prun_bind]
    rw [show ((List.range n).mapM ((fun _ ↦ (pSampleBits logMax : PM F 24 Nat)) ∘ Nat.succ)) =
      (List.range n).mapM (fun _ ↦ (pSampleBits logMax : PM F 24 Nat)) from rfl, prun_bind,
      sampleIndices_pmapM logMax n]
    rfl

theorem sampleIndices_lt (logMax : Nat) :
    ∀ (n : Nat) (t : Transcript F 24), ∀ i ∈ (sampleIndices logMax n t).1, i < 2 ^ logMax
  | 0, _, _, h => absurd h List.not_mem_nil
  | n + 1, t, i, h => by
    rw [sampleIndices] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact sampleBits_lt _ _
    · exact sampleIndices_lt logMax n _ i h

/-- The prover's FRI proof on one input `f0` of height `2 ^ h0`, after the batching grinding
witness `bw`. -/
theorem proveFri_run [Poseidon2Field F] (P : Params) (rounds : List (OpenRound (specBackend EF)))
    (f0 : Array EF) (bw : F) (t : Transcript F 24) :
    let h0 := Nat.log2 f0.size
    let las := foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen) h0 [h0]
    let t1 := t.observeList (DomainSeparator.friSeed F EF las (2 ^ P.logFinalPolyLen)
      P.commitPowBits P.queryPowBits P.numQueries h0 P.logBlowup P.maxLogArity)
    let r := chain P las f0 t1
    let cp := { r.1.foldl pushRd ⟨#[], [], #[], #[], #[]⟩ with finalPoly := finalPolyOf P r.2.1 }
    let t3 := r.2.2.observeExts (finalPolyOf P r.2.1).toList
    let qs := sampleIndices h0 P.numQueries (t3.grind P.queryPowBits).2
    (proveFri (specBackend EF) P rounds [f0] bw).run t =
      (⟨bw, cp.commits, cp.witnesses, (rounds.map fun (c, _) ↦ openMulti (specBackend EF) c
          (qs.1.map (· >>> (h0 - (specBackend EF).logHeight c)))).toArray,
        (answerFolds (specBackend EF) cp.data cp.arities.toList qs.1).toArray,
        finalPolyOf P r.2.1, (t3.grind P.queryPowBits).1⟩, qs.2) := by
  intro h0 las t1 r cp t3 qs
  unfold proveFri
  rw [prun_bind, prun_bind]
  erw [commitPhase_run]
  rw [prun_bind, prun_bind]
  erw [sampleIndices_pmapM]
  rfl

theorem la_chain [Poseidon2Field F] (P : Params) :
    ∀ (las : List Nat) (f : Array EF) (t : Transcript F 24), (chain P las f t).1.map (·.la) = las
  | [], _, _ => rfl
  | la :: las, f, t => by
    rw [chain]
    exact congrArg (List.cons la) (la_chain P las _ _)

theorem length_answerFolds [Poseidon2Field F] :
    ∀ (rs : List (Rd EF)) (cur : List Nat),
      (answerFolds (specBackend EF) (rs.map (·.c)) (rs.map (·.la)) cur).length = rs.length
  | [], _ => rfl
  | r :: rs, cur => by
    show (answerFolds (specBackend EF) ((r :: rs).map (·.c)) (r.la :: rs.map (·.la)) cur).length = _
    rw [answerFolds_cons, List.length_cons, List.length_cons, length_answerFolds rs]

theorem size_sibsAt [Poseidon2Field F] (r : Rd EF) (idx : Nat) :
    (sibsAt r idx).size = 2 ^ r.la - 1 := by
  rw [sibsAt, List.size_toArray, List.length_map,
    length_filter_range _ _ (Nat.mod_lt _ (Nat.two_pow_pos _))]

/-- Every fold answers every query with its siblings. -/
theorem answerFolds_shape [Poseidon2Field F] :
    ∀ (rs : List (Rd EF)) (cur : List Nat),
      ((answerFolds (specBackend EF) (rs.map (·.c)) (rs.map (·.la)) cur).zip
        (rs.map (·.la))).all (fun (o, la) ↦ o.siblings.size == cur.length &&
          o.siblings.all (·.size == 2 ^ la - 1)) = true
  | [], _ => rfl
  | r :: rs, cur => by
    show ((answerFolds (specBackend EF) ((r :: rs).map (·.c)) (r.la :: rs.map (·.la)) cur).zip
      (r.la :: rs.map (·.la))).all _ = true
    rw [answerFolds_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [Bool.and_eq_true]
      refine ⟨by rw [List.size_toArray, List.length_map, beq_self_eq_true], ?_⟩
      rw [Array.all_eq_true']
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hx)
      rw [size_sibsAt, beq_self_eq_true]
    · have := answerFolds_shape rs (cur.map (· >>> r.la))
      rwa [List.length_map] at this

/-! ### The folds' multi-openings -/

/-- The body of the verifier's loop over the folds' multi-openings. -/
def multiBody [Poseidon2Field F] (groups : List (List (Nat × List EF))) (c : Digest F)
    (o : CommitOpening F EF) (la i logH : Nat) : M (poseidon2 F) (ForInStep Nat) := do
  let logFolded := logH - la
  let gs := groups.map fun g ↦ g.getD i (0, [])
  ensure (← checkMulti (poseidon2 F) c [(2 ^ logFolded, Challenge.d EF * 2 ^ la)] (gs.map (·.1))
    (gs.map fun (_, evals) ↦ [evals.flatMap Ext.coeffs]) o.path.toList) "commit-phase opening"
  pure (ForInStep.yield logFolded)

/-- A round's groups at the queries' indices `cur` are an honest multi-opening of its
commitment. -/
theorem multiBody_run [Poseidon2Field F] (P : Params) {h : Nat} {f : Array EF} (hg : Good P h f)
    (r : Rd EF) (hr : r.folded = f) (h2 : r.la ≤ h - (P.logBlowup + P.logFinalPolyLen))
    (cur : List Nat) (hcur : ∀ i ∈ cur, i < 2 ^ h) (groups : List (List (Nat × List EF)))
    (n : Nat) (hgroups : groups.map (fun g ↦ g.getD n (0, [])) = cur.map (groupAt r.la f))
    (sibs : Array (Array EF)) (t : Transcript F 24) :
    multiBody groups r.c.root
      ⟨sibs, (openMulti (specBackend EF) r.c (cur.map (· >>> r.la))).siblings⟩
      r.la n h t = .ok (.yield (h - r.la), t) := by
  obtain ⟨la, f', t0, w, beta⟩ := r
  dsimp only at hr h2 hgroups ⊢
  subst hr
  have hsz := hg.2.1
  have hapos : 0 < 2 ^ la := Nat.two_pow_pos la
  have hhl : 2 ^ h = 2 ^ (h - la) * 2 ^ la := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
  have hm : ((specBackend EF).leaves (2 ^ la) f').height = 2 ^ (h - la) := by
    show f'.size / 2 ^ la = _
    rw [hsz, hhl, Nat.mul_div_cancel _ hapos]
  have hmw : ((specBackend EF).leaves (2 ^ la) f').width = Challenge.d EF * 2 ^ la := rfl
  have hlt : ∀ i ∈ cur.map (· >>> la), i < 2 ^ (h - la) := fun i hi ↦ by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hhl]; exact hcur j hj)
  have hv := verifyMulti_openMulti [(specBackend EF).leaves (2 ^ la) f'] (h - la)
    (List.cons_ne_nil _ _) (fun m hm' ↦ by
      rw [List.mem_singleton.mp hm']
      refine ⟨hm, ?_⟩
      show (f'.flatMap fun x ↦ (Ext.coeffs x).toArray).size =
        Challenge.d EF * 2 ^ la * (f'.size / 2 ^ la)
      rw [size_flatMap_coeffs, hsz, hhl, Nat.mul_div_cancel _ hapos]
      ring) (cur.map (· >>> la)) hlt
  have hmax : Nat.log2 (Committed.ofMats hashF compF
      [(specBackend EF).leaves (2 ^ la) f']).maxHeight = h - la := by
    have := maxHeight_ofMats (F := F) [((specBackend EF).leaves (2 ^ la) f' : Mat F)] _
      (List.cons_ne_nil _ _) fun m hm' ↦ (List.mem_singleton.mp hm') ▸ hm
    erw [this, Nat.log2_two_pow]
  have hrows : ((cur.map (· >>> la)).map fun i ↦ ((Committed.ofMats hashF compF
      [(specBackend EF).leaves (2 ^ la) f']).openAt i).values.toList.map (·.toList)) =
      cur.map fun i ↦ [((groupAt la f' i).2).flatMap Ext.coeffs] := by
    rw [List.map_map]
    refine List.map_congr_left fun i hi ↦ ?_
    have hrb : (i >>> la + 1) * 2 ^ la ≤ f'.size := by
      rw [hsz, hhl]
      exact Nat.mul_le_mul_right _ (hlt _ (List.mem_map_of_mem hi))
    simp only [Function.comp_apply]
    rw [openAt_values _ (h - la) (fun m hm' ↦ by rw [List.mem_singleton.mp hm']; exact hm)]
    show [(rowOf ((specBackend EF).leaves (2 ^ la) f') (i >>> la)).toList] = _
    rw [rowOf_leaves f' la _ hrb]
    rfl
  have hfst : (cur.map ((·.1) ∘ groupAt la f')) = cur.map (· >>> la) := by
    refine List.map_congr_left fun i _ ↦ ?_
    rfl
  have hsnd : (cur.map ((fun x : Nat × List EF ↦ [x.2.flatMap Ext.coeffs]) ∘ groupAt la f')) =
      cur.map fun i ↦ [((groupAt la f' i).2).flatMap Ext.coeffs] := rfl
  have hcheck : Merkle.verifyMultiM (m := Id) hashF compF
      (Committed.ofMats hashF compF [(specBackend EF).leaves (2 ^ la) f']).root
      [(2 ^ (h - la), Challenge.d EF * 2 ^ la)] (cur.map ((·.1) ∘ groupAt la f'))
      (cur.map ((fun x : Nat × List EF ↦ [x.2.flatMap Ext.coeffs]) ∘ groupAt la f'))
      (openMulti (specBackend EF) (Committed.ofMats hashF compF
        [(specBackend EF).leaves (2 ^ la) f']) (cur.map (· >>> la))).siblings.toList = true := by
    rw [hfst, hsnd, ← hrows, show [(2 ^ (h - la), Challenge.d EF * 2 ^ la)] =
      [(specBackend EF).leaves (2 ^ la) f'].map fun m ↦ (m.height, m.width) by
        rw [List.map_cons, List.map_nil, hm, hmw]]
    simp only [openMulti, List.toList_toArray]
    have hmax' : (specBackend EF).logHeight (Committed.ofMats hashF compF
        [(specBackend EF).leaves (2 ^ la) f']) = h - la := hmax
    rw [hmax']
    refine Eq.trans ?_ hv
    congr 2
    rw [List.map_map]
    rfl
  unfold multiBody
  simp only [hgroups, List.map_map]
  rw [bind_ok (a := true) (t' := t) (by rw [checkMulti_eq]; exact congrArg _ (congrArg₂ Prod.mk
    hcheck rfl))]
  rfl

/-- The verifier's loop over the folds' multi-openings accepts the honest groups. -/
theorem multi_loop [Poseidon2Field F] (P : Params) (groups : List (List (Nat × List EF)))
    (body : (Digest F × CommitOpening F EF) × Nat × Nat → Nat → M (poseidon2 F) (ForInStep Nat))
    (hbody : ∀ c o la i logH, body ((c, o), (la, i)) logH = multiBody groups c o la i logH) :
    ∀ (las : List Nat) (h : Nat) (f : Array EF) (t : Transcript F 24) (cur : List Nat) (n : Nat)
      (t' : Transcript F 24),
      Good P h f → las.sum ≤ h - (P.logBlowup + P.logFinalPolyLen) → (∀ la ∈ las, 1 ≤ la) →
      (∀ i ∈ cur, i < 2 ^ h) →
      (∀ j, groups.map (fun g ↦ g.getD (n + j) (0, [])) =
        cur.map fun i ↦ (qGroups (chain P las f t).1 i).getD j (0, [])) →
      forIn ((((chain P las f t).1.map (·.c.root)).zip
          (answerFolds (specBackend EF) ((chain P las f t).1.map (·.c)) las cur)).zip
          (las.zipIdx n)) h body t' = .ok (h - las.sum, t')
  | [], h, _, _, _, _, _, _, _, _, _, _ => by
    simp only [chain, List.map_nil, List.zip_nil_left, List.forIn_nil, List.sum_nil,
      Nat.sub_zero]
    rfl
  | la :: las, h, f, t, cur, n, t', hg, hsum, hpos, hcur, hgroups => by
    rw [List.sum_cons] at hsum
    have h1 := hpos la List.mem_cons_self
    rw [chain] at hgroups ⊢
    dsimp only at hgroups ⊢
    set g2 := (t.observeList (Committed.ofMats hashF compF
      [(specBackend EF).leaves (2 ^ la) f]).root.toList).grind P.commitPowBits with hg2
    set r : Rd EF := ⟨la, f, t, g2.1, (g2.2.sampleExtValue : EF)⟩ with hr
    rw [show (la :: las) = r.la :: las from rfl, answerFolds_cons, List.map_cons,
      List.zip_cons_cons, List.zipIdx_cons, List.zip_cons_cons]
    have h0 := hgroups 0
    simp only [Nat.add_zero, qGroups, List.getD_cons_zero] at h0
    rw [forIn_cons_ok _ _ _ _ _ _ _ (by
      rw [hbody]
      exact multiBody_run P hg r rfl (by show la ≤ _; omega) cur hcur groups n h0 _ t')]
    have hhl : 2 ^ h = 2 ^ (h - la) * 2 ^ la := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
    have hcur' : ∀ i ∈ cur.map (· >>> la), i < 2 ^ (h - la) := fun i hi ↦ by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hhl]; exact hcur j hj)
    rw [multi_loop P groups body hbody las (h - la) _ _ (cur.map (· >>> la)) (n + 1) t'
      (good_step P hg la h1 (by omega) _) (by omega)
      (fun x hx ↦ hpos x (List.mem_cons_of_mem _ hx)) hcur' fun j ↦ by
        have := hgroups (j + 1)
        rw [show n + (j + 1) = n + 1 + j by omega] at this
        rw [this, List.map_map]
        rfl,
      show h - la - las.sum = h - (la + las.sum) by omega]
    rfl

/-! ### The queries -/

theorem mapM_zipIdx_ok [Poseidon2Field F] {α β : Type} (body : α × Nat → M (poseidon2 F) β)
    (g : α → β) (t : Transcript F 24) :
    ∀ (l : List α) (n : Nat), (∀ k (hk : k < l.length), body (l[k], n + k) t = .ok (g l[k], t)) →
      (l.zipIdx n).mapM body t = .ok (l.map g, t)
  | [], _, _ => rfl
  | a :: l, n, h => by
    have h0 : body (a, n) t = .ok (g a, t) := by
      have := h 0 (Nat.zero_lt_succ _)
      rwa [Nat.add_zero, List.getElem_cons_zero] at this
    have hl : (l.zipIdx (n + 1)).mapM body t = .ok (l.map g, t) :=
      mapM_zipIdx_ok body g t l (n + 1) fun k hk ↦ by
        have := h (k + 1) (by simp only [List.length_cons]; omega)
        rwa [show n + (k + 1) = n + 1 + k by omega, List.getElem_cons_succ] at this
    rw [List.zipIdx_cons, List.mapM_cons, bind_ok h0, bind_ok hl]
    rfl

theorem values_openMulti [Poseidon2Field F] (c : (specBackend EF).C) (idxs : List Nat) (k : Nat)
    (hk : k < idxs.length) :
    (openMulti (specBackend EF) c idxs).values.getD k #[] =
      ((specBackend EF).openAt c idxs[k]).values := by
  simp only [openMulti, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some]

theorem w_chain_zero [Poseidon2Field F] (P : Params) (h0 : P.commitPowBits = 0) :
    ∀ (las : List Nat) (f : Array EF) (t : Transcript F 24), ∀ r ∈ (chain P las f t).1, r.w = 0
  | [], _, _, _, hr => absurd hr List.not_mem_nil
  | la :: las, f, t, r, hr => by
    rw [chain] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · show ((Transcript.observeList t _).grind P.commitPowBits).1 = 0
      rw [h0]; rfl
    · exact w_chain_zero P h0 las _ _ r hr

theorem length_chain [Poseidon2Field F] (P : Params) (las : List Nat) (f : Array EF)
    (t : Transcript F 24) : (chain P las f t).1.length = las.length := by
  conv_rhs => rw [← la_chain P las f t]
  rw [List.length_map]

/-! ### FRI completeness -/

/-- Without the flag after `proveFri`, there was none before it. -/
theorem flag_proveFri [Poseidon2Field F] (P : Params) (rounds : List (OpenRound (specBackend EF)))
    (f0 : Array EF) (bw : F) (t : Transcript F 24)
    (h : ((proveFri (specBackend EF) P rounds [f0] bw).run t).2.grindFailed = false) :
    t.grindFailed = false := by
  rw [proveFri_run] at h
  dsimp only at h
  rw [flag_sampleIndices] at h
  have h1 := flag_grind _ _ h
  rw [flag_observeExts] at h1
  have h2 := flag_chain P _ _ _ h1
  rwa [flag_observeList] at h2

/-- **FRI completeness**: the verifier's FRI accepts the specification prover's proof of one
low-degree input `f0`, when the prover's grinder found its witnesses, the verifier's rounds have
the input's height, and the input openings verify and give the input's entries. -/
theorem verifyFri_proveFri [Poseidon2Field F] (P : Params)
    (rounds : List (OpenRound (specBackend EF))) (f0 : Array EF) (bw : F)
    (vrounds : List (Round F EF)) (alpha : EF) (t : Transcript F 24)
    (hd : t.duplex = Poseidon2.duplex) (hg : Good P (Nat.log2 f0.size) f0)
    (hP : 0 < P.maxLogArity) (hq : 0 < P.numQueries) (hb : 0 < P.logBlowup)
    (hgrind : ((proveFri (specBackend EF) P rounds [f0] bw).run t).2.grindFailed = false)
    (hv : vrounds.any (!·.2.isEmpty) = true)
    (hheights : (((vrounds.flatMap (·.2)).map (·.1.logSize + P.logBlowup)).mergeSort
      (fun a b ↦ b ≤ a)).dedup = [Nat.log2 f0.size])
    (hinputs : ∀ (indices : List Nat) (t' : Transcript F 24),
      (∀ i ∈ indices, i < 2 ^ Nat.log2 f0.size) →
      verifyInputs (poseidon2 F) P (Nat.log2 f0.size) indices
        (rounds.map fun (c, _) ↦ openMulti (specBackend EF) c
          (indices.map (· >>> (Nat.log2 f0.size - (specBackend EF).logHeight c)))) vrounds t' =
        .ok ((), t'))
    (hreduce : ∀ (index : Nat) (t' : Transcript F 24), index < 2 ^ Nat.log2 f0.size →
      reduceQuery (poseidon2 F) P (Nat.log2 f0.size) index alpha
        (rounds.map fun (c, _) ↦ ((specBackend EF).openAt c
          (index >>> (Nat.log2 f0.size - (specBackend EF).logHeight c))).values.toList) vrounds t' =
        .ok ([(Nat.log2 f0.size, f0.getD index 0)], t')) :
    verifyFri (poseidon2 F) P ((proveFri (specBackend EF) P rounds [f0] bw).run t).1 vrounds
      alpha t = .ok ((), ((proveFri (specBackend EF) P rounds [f0] bw).run t).2) := by
  rw [proveFri_run] at hgrind ⊢
  dsimp only at hgrind ⊢
  unfold verifyFri
  rw [hheights]
  simp only [List.headD_cons]
  set h0 := Nat.log2 f0.size with hh0
  have hL := hg.1
  have h24 : h0 ≤ twoAdicity F := hg.2.2.1
  set las := foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen) h0 [h0] with hlas
  have hlas' : las = foldArities P.maxLogArity (h0 - (P.logBlowup + P.logFinalPolyLen)) :=
    foldSchedule_single _ _ hP _ _ (Nat.sub_le _ _)
  obtain ⟨hsum, hpos⟩ := foldArities_spec P.maxLogArity
    (h0 - (P.logBlowup + P.logFinalPolyLen)) hP
  rw [← hlas'] at hsum hpos
  set seed := DomainSeparator.friSeed F EF las (2 ^ P.logFinalPolyLen) P.commitPowBits
    P.queryPowBits P.numQueries h0 P.logBlowup P.maxLogArity with hseed
  set t1 := t.observeList seed with ht1
  set r := chain P las f0 t1 with hr
  set fp := finalPolyOf P r.2.1 with hfp
  set t3 := r.2.2.observeExts fp.toList with ht3
  set g4 := t3.grind P.queryPowBits with hg4
  set qs := sampleIndices h0 P.numQueries g4.2 with hqs
  obtain ⟨hcom, hdata, hwit, hari, -⟩ := foldl_pushRd r.1 ⟨#[], [], #[], #[], #[]⟩
  simp only [List.nil_append] at hcom hdata hwit hari
  have hrl : r.1.map (·.la) = las := la_chain P las f0 t1
  -- flags and duplexes
  have hq4 : g4.2.grindFailed = false := by
    rw [← flag_sampleIndices h0 P.numQueries]; exact hgrind
  have hf : r.2.2.grindFailed = false := by
    have := flag_grind _ _ hq4
    rwa [ht3, flag_observeExts] at this
  have hd1 : t1.duplex = Poseidon2.duplex := by rw [ht1, duplex_observeList, hd]
  have hd2 : r.2.2.duplex = Poseidon2.duplex := by rw [hr, duplex_chain, hd1]
  have hd3 : t3.duplex = Poseidon2.duplex := by rw [ht3, duplex_observeExts, hd2]
  -- the shape checks
  have hpar : (decide (0 < P.numQueries) && decide (0 < P.logBlowup) &&
      decide (0 < P.maxLogArity)) = true := by
    simp only [hq, hb, hP, decide_true, Bool.and_self]
  rw [hpar, ensure_true, pure_bind, hv, ensure_true, pure_bind]
  simp only [h24, decide_true, ensure_true, pure_bind]
  set cp := List.foldl pushRd ⟨#[], [], #[], #[], #[]⟩ r.1 with hcp
  have hdata' : cp.data = r.1.map (·.c) := hdata
  have hari' : cp.arities.toList = las := hari.trans hrl
  have hqlen : qs.1.length = P.numQueries := length_sampleIndices _ _ _
  have hfold1 : ((answerFolds (specBackend EF) cp.data cp.arities.toList qs.1).toArray.size ==
      las.length) = true := by
    rw [hdata', hari', List.size_toArray, ← hrl]
    erw [length_answerFolds]
    rw [List.length_map, beq_self_eq_true]
  have hfold2 : ((answerFolds (specBackend EF) cp.data cp.arities.toList qs.1).zip las).all
      (fun x ↦ x.1.siblings.size == P.numQueries &&
        x.1.siblings.all fun y ↦ y.size == 2 ^ x.2 - 1) = true := by
    rw [hdata', hari', ← hqlen]
    have := answerFolds_shape r.1 qs.1
    rwa [hrl] at this
  have hwit0 : (P.commitPowBits != 0 || cp.witnesses.all fun x ↦ x == 0) = true := by
    by_cases h0 : P.commitPowBits = 0
    · rw [h0, bne_self_eq_false, Bool.false_or, ← Array.all_toList, hwit, List.all_eq_true]
      intro x hx
      obtain ⟨rd, hrd, rfl⟩ := List.mem_map.mp hx
      rw [w_chain_zero P h0 las f0 t1 rd hrd, beq_self_eq_true]
    · rw [bne_iff_ne.mpr h0, Bool.true_or]
  have hqw0 : (P.queryPowBits != 0 || g4.1 == 0) = true := by
    by_cases h0 : P.queryPowBits = 0
    · have hw : (t3.grind P.queryPowBits).1 = 0 := by rw [h0]; rfl
      rw [h0, bne_self_eq_false, Bool.false_or, hg4, hw, beq_self_eq_true]
    · rw [bne_iff_ne.mpr h0, Bool.true_or]
  have hfps : (fp.size == 2 ^ P.logFinalPolyLen) = true := by
    rw [hfp, finalPolyOf, idft, Array.size_ofFn, beq_self_eq_true]
  have hcsz : (cp.commits.size == las.length && cp.witnesses.size == las.length) = true := by
    rw [← Array.length_toList, ← Array.length_toList, hcom, hwit, List.length_map, List.length_map,
      length_chain, beq_self_eq_true, Bool.and_self]
  rw [hfold1, ensure_true, pure_bind, hfold2, ensure_true, pure_bind, hwit0, ensure_true,
    pure_bind, hqw0, ensure_true, pure_bind, hfps, ensure_true, pure_bind,
    bind_ok (observeList_run t seed), ← ht1, hcsz, ensure_true, pure_bind, hcom, hwit]
  rw [bind_ok (commit_loop P _ (fun _ _ _ ↦ rfl) las f0 t1 #[] hd1 hf)]
  rw [bind_ok (observeExts_run r.2.2 fp.toList), ← ht3,
    bind_ok (a := true) (t' := g4.2) (by rw [checkWitness_run _ _ _ hd3, checkWitness_grind _ _
      hq4]), ensure_true, pure_bind,
    bind_ok (sampleIndices_mapM h0 P.numQueries g4.2 ((duplex_grind t3 _).trans hd3)), ← hqs,
    bind_ok (hinputs qs.1 qs.2 (sampleIndices_lt h0 _ _))]
  rw [hdata', hari']
  have hbetas : (#[] ++ (List.map (fun x : Rd EF ↦ x.beta) (chain P las f0 t1).1).toArray).toList =
      r.1.map (·.beta) := by
    rw [Array.toList_append, List.toList_toArray]; rfl
  rw [hbetas]
  have hidx := sampleIndices_lt h0 P.numQueries g4.2
  rw [bind_ok (mapM_zipIdx_ok _ (qGroups r.1) qs.2 qs.1 0 fun k hk ↦ by
    rw [Nat.zero_add]
    have hk' : qs.1[k] < 2 ^ h0 := hidx _ (List.getElem_mem hk)
    have hrows : (List.map (fun b ↦ (b.values.getD k #[]).toList)
        (List.map (fun x ↦ openMulti (specBackend EF) x.1
          (List.map (fun x_1 ↦ x_1 >>> (h0 - (specBackend EF).logHeight x.1)) qs.1)) rounds)) =
        rounds.map fun (c, _) ↦ ((specBackend EF).openAt c
          (qs.1[k] >>> (h0 - (specBackend EF).logHeight c))).values.toList := by
      rw [List.map_map]
      refine List.map_congr_left fun x _ ↦ ?_
      simp only [Function.comp_apply]
      rw [values_openMulti _ _ _ (by rw [List.length_map]; exact hk), List.getElem_map]
    simp only [hrows]
    have hfq := foldQuery_run P h0 f0 hg las hsum (fun x hx ↦ (hpos x hx).1) t1 qs.1 k hk hk' qs.2
    rw [← hr] at hfq
    rw [bind_ok (hreduce qs.1[k] qs.2 hk')]
    erw [bind_ok hfq]
    have hfin := horner_idft r.2.1 P.logBlowup P.logFinalPolyLen h0 (qs.1[k] >>> las.sum)
      (chain_final P las h0 f0 t1 hg hsum fun x hx ↦ (hpos x hx).1) hL h24 (by
        rw [Nat.shiftRight_eq_div_pow, hsum]
        refine Nat.div_lt_of_lt_mul ?_
        rw [← pow_add, Nat.sub_add_cancel hL]; exact hk')
    rw [← finalPolyOf] at hfin
    simp only [hfp] at ⊢
    rw [hfin, beq_self_eq_true, ensure_true, pure_bind]
    rfl)]
  erw [bind_ok (multi_loop P (qs.1.map (qGroups r.1)) _ (fun _ _ _ _ _ ↦ rfl) las h0 f0 t1 qs.1 0
    qs.2 hg (le_of_eq hsum) (fun x hx ↦ (hpos x hx).1) hidx fun j ↦ by
      rw [List.map_map, Nat.zero_add]
      rfl)]
  rfl

end CompStark.Complete
