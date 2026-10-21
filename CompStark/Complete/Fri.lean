/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Complete.FriRound

/-! # FRI completeness

The verifier's FRI accepts the specification prover's proof (`verifyFri_proveFri`).

The prover's commit rounds are a pure chain (`chain`, `commitRounds_run`): each round commits to
the groups of the folded vector, grinds, samples `β`, folds and adds the next input of the folded
height. The verifier replays the transcript: it observes the same commitments, the grinding
witnesses check, and it samples the same `β`s and query indices. Each query's folds walk the chain
at the query's index: the opened group verifies against its commitment and holds the running
value, its `foldRow` is the next folded vector's entry, and the reduced openings are the inputs'
entries, added where the prover added them. The last folded vector has low degree, so the final
polynomial evaluates to the last entry.
-/

@[expose] public section
namespace CompStark.Complete
open CompStark.Stark CompStark.Fri CompStark.KoalaBear

local notation "F" => _root_.KoalaBear.Fast.Field
local notation "hashF" => CompStark.Hash.KoalaBear.hash F
local notation "compF" => CompStark.Hash.KoalaBear.compress F
variable {EF : Type} [Challenge F EF]

/-! ### The verifier's monad on Poseidon2

On Poseidon2 the verifier's challenger is the prover's transcript: its steps are the transcript's.
Sampling bits reads the canonical value of the transcript's duplex, so it needs that duplex to be
KoalaBear's, which every step keeps. -/

theorem bind_ok {α β : Type} {x : M poseidon2 α}
    {f : α → M poseidon2 β} {t t' : Transcript F 24} {a : α}
    (h : x t = .ok (a, t')) : (x >>= f) t = f a t' := by
  show StateT.bind x f t = _
  simp only [StateT.bind, h]
  rfl
theorem sample_bind {β : Type} (f : F → M poseidon2 β) (t : Transcript F 24) :
    (sample poseidon2 >>= f) t = f t.sample.1 t.sample.2 := bind_ok rfl
theorem sampleList_run (t : Transcript F 24) :
    ∀ k, sampleList poseidon2 k t = .ok (t.sampleList k)
  | 0 => rfl
  | k + 1 => by
    simp only [sampleList, sample_bind]
    rw [bind_ok (sampleList_run _ k)]
    rfl
theorem sampleExt_run (t : Transcript F 24) :
    (sampleExt poseidon2 : M poseidon2 EF) t =
      .ok ((t.sampleExtValue : EF), (Transcript.sampleExtState EF t)) := by
  simp only [sampleExt, Transcript.sampleExtValue, Transcript.sampleExtState]
  rw [bind_ok (sampleList_run t _)]
  rfl
theorem sampleBits_run (t : Transcript F 24) (bits : Nat) (hd : t.duplex = KoalaBear.duplex) :
    sampleBits poseidon2 bits t = .ok (t.sampleBits bits) := by
  unfold sampleBits Transcript.sampleBits Challenger.sampleBits
  rw [sample_bind]
  unfold Transcript.sample
  rw [hd]
  generalize Challenger.sample KoalaBear.duplex t.state = p
  obtain ⟨x, c⟩ := p
  rfl
theorem duplex_observe (t : Transcript F 24) (x : F) : (t.observe x).duplex = t.duplex := rfl
theorem checkWitness_run (t : Transcript F 24) (bits : Nat) (w : F) (hd : t.duplex = KoalaBear.duplex) :
    checkWitness poseidon2 bits w t = .ok (t.checkWitness bits w) := by
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
theorem foldl_observe (t : Transcript F 24) (xs : List F) :
    xs.foldl Transcript.observe t = t.observeList xs := by
  unfold Transcript.observeList Challenger.observeList
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih]; rfl
theorem observeList_run (t : Transcript F 24) (xs : List F) :
    observeList poseidon2 xs t = .ok ((), t.observeList xs) := by
  rw [← foldl_observe]; rfl
theorem observeExts_run (t : Transcript F 24) (xs : List EF) :
    observeExts poseidon2 xs t = .ok ((), t.observeExts xs) := by
  unfold observeExts
  show Except.ok ((), xs.foldl (fun s x ↦ (Ext.coeffs x).foldl Transcript.observe s) t) = _
  simp only [foldl_observe]
  rfl

theorem prun_bind {α β : Type} (x : PM F 24 α) (f : α → PM F 24 β) (t : Transcript F 24) :
    (x >>= f).run t = (f (x.run t).1).run (x.run t).2 := rfl

theorem ensure_true (msg : String) : ensure (H := poseidon2) true msg = pure () := rfl

/-! ### The commit rounds as a chain -/

/-- One fold of the commit phase by `2 ^ la` at `β`. -/
def foldOnce (la : Nat) (beta : EF) (f : Array EF) : Array EF :=
  let rows := f.size / 2 ^ la
  if la = 1 then foldPairs f beta (Nat.log2 rows) else
    Array.ofFn (n := rows) fun i ↦ foldRow i (Nat.log2 rows) la beta
      ((List.range (2 ^ la)).map fun k ↦ f.getD (i * 2 ^ la + k) 0)

/-- Add the next input times `β ^ (2 ^ la)` if it has the folded vector's size. -/
def addNext (la : Nat) (beta : EF) (f : Array EF) (rest : List (Array EF)) :
    Array EF × List (Array EF) :=
  match rest with
  | v :: vs => if v.size == f.size then
      (Array.zipWith (fun u x ↦ u + Ext.powTwo beta la * x) f v, vs) else (f, rest)
  | [] => (f, [])

/-- A commit round: its log arity, the folded vector and remaining inputs it starts from, the
transcript before it, its grinding witness and its folding challenge. -/
structure Rd (EF : Type) [Challenge F EF] where
  la : Nat
  folded : Array EF
  rest : List (Array EF)
  t : Transcript F 24
  w : F
  beta : EF

/-- A round's commitment. -/
def Rd.c (r : Rd EF) : Committed F := Committed.ofMats hashF compF [(specBackend EF).leaves (2 ^ r.la) r.folded]

/-- The commit rounds of the specification prover, the final vector and transcript. -/
def chain (P : Params) :
    Nat → Array EF → List (Array EF) → Transcript F 24 → List (Rd EF) × Array EF × Transcript F 24
  | 0, f, _, t => ([], f, t)
  | fuel + 1, f, rest, t =>
    if f.size ≤ 2 ^ (P.logBlowup + P.logFinalPolyLen) then ([], f, t) else
    let la := logArityFor P (Nat.log2 f.size) (rest.head?.map (Nat.log2 ·.size))
    let t1 := t.observeList (Committed.ofMats hashF compF [(specBackend EF).leaves (2 ^ la) f]).root.toList
    let t2 := (t1.grind P.commitPowBits).2
    let beta := (t2.sampleExtValue : EF)
    let (f', rest') := addNext la beta (foldOnce la beta f) rest
    let r := chain P fuel f' rest' (Transcript.sampleExtState EF t2)
    (⟨la, f, rest, t, (t1.grind P.commitPowBits).1, beta⟩ :: r.1, r.2)

/-- Record a round in the commit phase's result. -/
def pushRd (cp : CommitPhase F EF (Committed F)) (r : Rd EF) : CommitPhase F EF (Committed F) :=
  ⟨cp.commits.push r.c.root, cp.data ++ [r.c], cp.witnesses.push r.w, cp.arities.push r.la,
    cp.finalPoly⟩

theorem commitRounds_run (P : Params) (fuel : Nat) :
    ∀ (f : Array EF) (rest : List (Array EF)) (cp : CommitPhase F EF (Committed F)) (t : Transcript F 24),
      (commitRounds (specBackend EF) P fuel f rest cp).run t =
        let r := chain P fuel f rest t
        ((r.2.1, r.1.foldl pushRd cp), r.2.2) := by
  induction fuel with
  | zero =>
    intro f rest cp t
    simp only [commitRounds, chain]
    rfl
  | succ fuel ih =>
    intro f rest cp t
    by_cases hs : f.size ≤ 2 ^ (P.logBlowup + P.logFinalPolyLen)
    · have hc : chain P (fuel + 1) f rest t = ([], f, t) := by rw [chain, ite_eq_left hs]
      rw [hc]
      simp only [commitRounds]
      rw [ite_eq_left (show (specBackend EF).size f ≤ _ from hs)]
      rfl
    · rw [chain, ite_eq_right hs]
      simp only [commitRounds]
      rw [ite_eq_right (show ¬ (specBackend EF).size f ≤ _ from hs)]
      rw [prun_bind, prun_bind, prun_bind]
      cases rest with
      | nil => exact ih _ _ _ _
      | cons v vs =>
        dsimp only [addNext, foldOnce, specBackend, Backend.spec, id]
        split
        · rename_i h
          simp only [h, ite_true]
          exact ih _ _ _ _
        · rename_i h
          simp only [h]
          exact ih _ _ _ _

/-! ### The low-degree invariant of the commit rounds -/

/-- The folded vector has height `2 ^ h` above the final height and low degree; the remaining
inputs are strictly shorter, tallest first, not below the final height, and low degree. -/
def Good (P : Params) (h : Nat) (f : Array EF) (rest : List (Array EF)) : Prop :=
  P.logBlowup + P.logFinalPolyLen ≤ h ∧ LowDegree h (h - P.logBlowup) f ∧
    rest.Pairwise (fun a b ↦ b.size < a.size) ∧
    ∀ v ∈ rest, Nat.log2 v.size < h ∧ P.logBlowup + P.logFinalPolyLen ≤ Nat.log2 v.size ∧
      LowDegree (Nat.log2 v.size) (Nat.log2 v.size - P.logBlowup) v

theorem log2_size {h d : Nat} {v : Array EF} (hv : LowDegree h d v) : Nat.log2 v.size = h := by
  rw [hv.1, Nat.log2_two_pow]

/-- The log arity of a round above the final height folds by at least one bit, not below the
final height or the next input. -/
theorem logArityFor_bounds (P : Params) (hP : 0 < P.maxLogArity) (h : Nat)
    (hgt : P.logBlowup + P.logFinalPolyLen < h) (next : Option Nat) (hn : ∀ h' ∈ next, h' < h) :
    1 ≤ logArityFor P h next ∧ logArityFor P h next ≤ h - (P.logBlowup + P.logFinalPolyLen) ∧
      ∀ h' ∈ next, logArityFor P h next ≤ h - h' := by
  unfold logArityFor
  cases next with
  | none => simp only [Option.mem_def, reduceCtorEq, IsEmpty.forall_iff, implies_true,
      and_true]; omega
  | some h' =>
    have := hn h' rfl
    simp only [Option.mem_def, Option.some.injEq, forall_eq']
    omega

/-- The fold of a vector of `2 ^ h` values is the groups' `foldRow`s. -/
theorem foldOnce_eq (la h : Nat) (beta : EF) (f : Array EF) (hs : f.size = 2 ^ h)
    (hla : la ≤ h) (h24 : h ≤ 24) (hla1 : 1 ≤ la) :
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
    rw [← getD_lt _ i h1, foldPairs_getD f beta (h - 1) (by omega24) i h2, Array.getElem_ofFn]
  · rfl

theorem size_foldOnce (la h : Nat) (beta : EF) (f : Array EF) (hs : f.size = 2 ^ h)
    (hla : la ≤ h) (h24 : h ≤ 24) (hla1 : 1 ≤ la) : (foldOnce la beta f).size = 2 ^ (h - la) := by
  rw [foldOnce_eq la h beta f hs hla h24 hla1, Array.size_ofFn]

theorem lowDegree_foldOnce (P : Params) (la h : Nat) (beta : EF) (f : Array EF)
    (hf : LowDegree h (h - P.logBlowup) f) (hla : la ≤ h - P.logBlowup) (hla1 : 1 ≤ la) :
    LowDegree (h - la) (h - la - P.logBlowup) (foldOnce la beta f) := by
  have h24 := hf.2.1
  rw [foldOnce_eq la h beta f hf.1 (by omega24) h24 hla1]
  refine lowDegree_foldRows f (h - la) la (h - la - P.logBlowup) beta ?_
  rwa [show h - la + la = h by omega, show h - la - P.logBlowup + la = h - P.logBlowup by omega]

/-- A round keeps the invariant at the folded height. -/
theorem good_step (P : Params) (hP : 0 < P.maxLogArity) {h : Nat} {f : Array EF}
    {rest : List (Array EF)} (hg : Good P h f rest) (hgt : P.logBlowup + P.logFinalPolyLen < h)
    (beta : EF) :
    let la := logArityFor P h (rest.head?.map (Nat.log2 ·.size))
    1 ≤ la ∧ la ≤ h - (P.logBlowup + P.logFinalPolyLen) ∧
      Good P (h - la) (addNext la beta (foldOnce la beta f) rest).1
        (addNext la beta (foldOnce la beta f) rest).2 := by
  obtain ⟨hL, hf, hsort, hrest⟩ := hg
  have hb := logArityFor_bounds P hP h hgt (rest.head?.map (Nat.log2 ·.size)) (by
    intro h' hh'
    obtain ⟨v, hv, rfl⟩ := Option.mem_map.mp hh'
    exact (hrest v (List.mem_of_mem_head? hv)).1)
  intro la
  refine ⟨hb.1, hb.2.1, ?_⟩
  have hfo := lowDegree_foldOnce P la h beta f hf (by omega24) hb.1
  have hsz : (foldOnce la beta f).size = 2 ^ (h - la) := hfo.1
  cases rest with
  | nil => exact ⟨by omega, hfo, List.Pairwise.nil, fun _ hv ↦ absurd hv List.not_mem_nil⟩
  | cons v vs =>
    obtain ⟨hvh, hvL, hvd⟩ := hrest v List.mem_cons_self
    have hla_v : la ≤ h - Nat.log2 v.size := hb.2.2 _ rfl
    have hvs := hvd.1
    rw [log2_size hvd] at hvs
    rw [List.pairwise_cons] at hsort
    simp only [addNext]
    split
    · rename_i heq
      have he : Nat.log2 v.size = h - la := by
        rw [beq_iff_eq, hvs, hsz] at heq
        exact Nat.pow_right_injective (le_refl 2) heq
      refine ⟨by omega, lowDegree_addScaled _ _ _ _ _ hfo (he ▸ hvd), hsort.2, fun x hx ↦ ?_⟩
      obtain ⟨hxh, hxL, hxd⟩ := hrest x (List.mem_cons_of_mem _ hx)
      refine ⟨?_, hxL, hxd⟩
      have hlt := hsort.1 x hx
      rw [hvs, hxd.1, log2_size hxd] at hlt
      have := (Nat.pow_lt_pow_iff_right (by decide)).mp hlt
      omega
    · rename_i hne
      have he : Nat.log2 v.size ≠ h - la := fun e ↦ hne (by rw [beq_iff_eq, hvs, hsz, e])
      refine ⟨by omega, hfo, List.pairwise_cons.mpr hsort, fun x hx ↦ ?_⟩
      obtain ⟨hxh, hxL, hxd⟩ := hrest x hx
      refine ⟨?_, hxL, hxd⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · have hlt := hsort.1 x hx
        rw [hvs, hxd.1, log2_size hxd] at hlt
        have := (Nat.pow_lt_pow_iff_right (by decide)).mp hlt
        omega

/-- The chain ends at the final height with a low-degree vector, after folding by the height's
excess. -/
theorem chain_final (P : Params) (hP : 0 < P.maxLogArity) (fuel : Nat) :
    ∀ (h : Nat) (f : Array EF) (rest : List (Array EF)) (t : Transcript F 24), Good P h f rest →
      h - (P.logBlowup + P.logFinalPolyLen) ≤ fuel →
      LowDegree (P.logBlowup + P.logFinalPolyLen) P.logFinalPolyLen (chain P fuel f rest t).2.1 ∧
        ((chain P fuel f rest t).1.map (·.la)).sum = h - (P.logBlowup + P.logFinalPolyLen) := by
  induction fuel with
  | zero =>
    intro h f rest t hg hfuel
    have hh : h = P.logBlowup + P.logFinalPolyLen := by have := hg.1; omega
    subst hh
    refine ⟨?_, by simp only [chain, List.map_nil, List.sum_nil]; omega⟩
    have := hg.2.1
    rwa [show P.logBlowup + P.logFinalPolyLen - P.logBlowup = P.logFinalPolyLen by omega] at this
  | succ fuel ih =>
    intro h f rest t hg hfuel
    have hsz := hg.2.1.1
    by_cases hs : f.size ≤ 2 ^ (P.logBlowup + P.logFinalPolyLen)
    · rw [chain, ite_eq_left hs]
      have hh : h = P.logBlowup + P.logFinalPolyLen := by
        rw [hsz] at hs
        have := (Nat.pow_le_pow_iff_right (by decide)).mp hs
        have := hg.1; omega
      subst hh
      refine ⟨?_, by simp only [List.map_nil, List.sum_nil]; omega⟩
      have := hg.2.1
      rwa [show P.logBlowup + P.logFinalPolyLen - P.logBlowup = P.logFinalPolyLen by omega] at this
    · rw [chain, ite_eq_right hs]
      have hgt : P.logBlowup + P.logFinalPolyLen < h := by
        by_contra hc
        exact hs (by rw [hsz]; exact Nat.pow_le_pow_right (by decide) (by omega24))
      rw [hsz, Nat.log2_two_pow]
      dsimp only
      generalize (((Transcript.observeList _ _).grind P.commitPowBits).2.sampleExtValue : EF) = beta
      obtain ⟨h1, h2, hg'⟩ := good_step P hP hg hgt beta
      have := fun t' ↦ ih _ _ _ t' hg' (by omega24)
      refine ⟨(this _).1, ?_⟩
      rw [List.map_cons, List.sum_cons, (this _).2]
      dsimp only
      omega

theorem addNext_nil (la : Nat) (beta : EF) (f : Array EF) : addNext la beta f [] = (f, []) :=
  rfl

theorem foldArities_succ (a r : Nat) :
    foldArities a (r + 1) =
      max 1 (min a (r + 1)) :: foldArities a (r + 1 - max 1 (min a (r + 1))) :=
  by rw [foldArities]

/-- With one input, the commit rounds fold by Plonky3's schedule `foldArities`. -/
theorem chain_arities (P : Params) (hP : 0 < P.maxLogArity) (fuel : Nat) :
    ∀ (h : Nat) (f : Array EF) (t : Transcript F 24), Good P h f [] →
      h - (P.logBlowup + P.logFinalPolyLen) ≤ fuel →
      (chain P fuel f [] t).1.map (·.la) =
        foldArities P.maxLogArity (h - (P.logBlowup + P.logFinalPolyLen)) := by
  induction fuel with
  | zero =>
    intro h f t hg hfuel
    rw [show h - (P.logBlowup + P.logFinalPolyLen) = 0 by omega, foldArities]
    rfl
  | succ fuel ih =>
    intro h f t hg hfuel
    have hsz := hg.2.1.1
    by_cases hs : f.size ≤ 2 ^ (P.logBlowup + P.logFinalPolyLen)
    · rw [chain, ite_eq_left hs]
      have hh : h ≤ P.logBlowup + P.logFinalPolyLen := by
        rw [hsz] at hs
        exact (Nat.pow_le_pow_iff_right (by decide)).mp hs
      rw [show h - (P.logBlowup + P.logFinalPolyLen) = 0 by omega, foldArities]
      rfl
    · rw [chain, ite_eq_right hs]
      have hgt : P.logBlowup + P.logFinalPolyLen < h := by
        by_contra hc
        exact hs (by rw [hsz]; exact Nat.pow_le_pow_right (by decide) (by omega24))
      rw [hsz, Nat.log2_two_pow]
      dsimp only
      generalize (((Transcript.observeList _ _).grind P.commitPowBits).2.sampleExtValue : EF) = beta
      obtain ⟨h1, h2, hg'⟩ := good_step P hP hg hgt beta
      have hla : logArityFor P h none = max 1 (min P.maxLogArity
          (h - (P.logBlowup + P.logFinalPolyLen) - 1 + 1)) := by
        simp only [logArityFor]; omega
      simp only [List.head?_nil, Option.map_none, addNext_nil] at h1 h2 hg' ⊢
      rw [List.map_cons, ih _ _ _ hg' (by omega24),
        show h - (P.logBlowup + P.logFinalPolyLen) =
          h - (P.logBlowup + P.logFinalPolyLen) - 1 + 1 by omega, foldArities_succ, ← hla]
      congr 2
      omega

/-! ### The transcript's failure flag

Observing and sampling keep the flag, and grinding only sets it, so a final transcript without
the flag had every grind of the run check. -/

theorem flag_observeList (t : Transcript F 24) (xs : List F) :
    (t.observeList xs).grindFailed = t.grindFailed := by
  unfold Transcript.observeList; dsimp only

theorem flag_observe (t : Transcript F 24) (x : F) : (t.observe x).grindFailed = t.grindFailed := by
  unfold Transcript.observe; dsimp only

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
theorem flag_grind (t : Transcript F 24) (bits : Nat) (h : (t.grind bits).2.grindFailed = false) :
    t.grindFailed = false := by
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

Every step keeps the transcript's duplex, so a run from `Transcript.init` stays on KoalaBear's,
as the verifier's `sampleBits` and `checkWitness` need. -/

theorem duplex_observeList (t : Transcript F 24) (xs : List F) :
    (t.observeList xs).duplex = t.duplex := rfl

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

theorem duplex_chain (P : Params) (fuel : Nat) :
    ∀ (f : Array EF) (rest : List (Array EF)) (t : Transcript F 24),
      (chain P fuel f rest t).2.2.duplex = t.duplex := by
  induction fuel with
  | zero => intro f rest t; rfl
  | succ fuel ih =>
    intro f rest t
    rw [chain]
    split
    · rfl
    · dsimp only
      rw [ih, duplex_sampleExt, duplex_grind, duplex_observeList]

theorem forIn_cons_ok {α σ : Type} (a : α) (l : List α) (b b' : σ)
    (body : α → σ → M poseidon2 (ForInStep σ)) (t t' : Transcript F 24)
    (h : body a b t = .ok (.yield b', t')) : forIn (a :: l) b body t = forIn l b' body t' := by
  rw [List.forIn_cons, bind_ok h]

/-- Without the flag after the commit rounds, there was none before them. -/
theorem flag_chain (P : Params) (fuel : Nat) :
    ∀ (f : Array EF) (rest : List (Array EF)) (t : Transcript F 24),
      (chain P fuel f rest t).2.2.grindFailed = false → t.grindFailed = false := by
  induction fuel with
  | zero => intro f rest t h; exact h
  | succ fuel ih =>
    intro f rest t h
    rw [chain] at h
    split at h
    · exact h
    · have := ih _ _ _ h
      rw [flag_sampleExt] at this
      rw [← flag_observeList t _]
      exact flag_grind _ _ this

/-! ### The verifier's commit loop -/

/-- The body of the verifier's loop over the commitments. -/
def commitBody (P : Params) (c : Digest F) (w : F) (betas : Array EF) :
    M poseidon2 (ForInStep (Array EF)) :=
  do
  observeList poseidon2 c.toList
  let ok ← checkWitness poseidon2 P.commitPowBits w
  ensure ok "commit witness"
  let beta ← (sampleExt poseidon2 : M poseidon2 EF)
  pure (ForInStep.yield (betas.push beta))

theorem commitBody_run (P : Params) (c : Digest F) (w : F) (b : Array EF) (t t2 : Transcript F 24)
    (hd : t.duplex = KoalaBear.duplex)
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
theorem commit_loop (P : Params)
    (body : Digest F × F → Array EF → M poseidon2 (ForInStep (Array EF)))
    (hbody : ∀ c w b, body (c, w) b = commitBody P c w b) (fuel : Nat) :
    ∀ f rest t betas, t.duplex = KoalaBear.duplex →
      (chain P fuel f rest t).2.2.grindFailed = false →
      forIn (((chain P fuel f rest t).1.map (·.c.root)).zip ((chain P fuel f rest t).1.map (·.w)))
        betas body t =
        .ok (betas ++ ((chain P fuel f rest t).1.map (·.beta)).toArray,
          (chain P fuel f rest t).2.2) := by
  induction fuel with
  | zero =>
    intro f rest t betas _ _
    simp only [chain, List.map_nil, List.zip_nil_left, List.forIn_nil, Array.append_empty]
    rfl
  | succ fuel ih =>
    intro f rest t betas hd ht
    by_cases hs : f.size ≤ 2 ^ (P.logBlowup + P.logFinalPolyLen)
    · rw [chain, ite_eq_left hs]
      simp only [List.map_nil, List.zip_nil_left, List.forIn_nil, Array.append_empty]
      rfl
    · rw [chain, ite_eq_right hs] at ht ⊢
      dsimp only at ht ⊢
      rw [List.map_cons, List.map_cons, List.zip_cons_cons, List.map_cons]
      generalize logArityFor P _ _ = la at ht ⊢
      generalize ht1 : t.observeList _ = t1 at ht ⊢
      have hd1 : (Transcript.sampleExtState EF ((t1.grind P.commitPowBits).2)).duplex =
          KoalaBear.duplex := by
        rw [duplex_sampleExt, duplex_grind, ← ht1, duplex_observeList, hd]
      have hg1 : (t1.grind P.commitPowBits).2.grindFailed = false := by
        have := flag_chain P fuel _ _ _ ht
        rwa [flag_sampleExt] at this
      rw [forIn_cons_ok _ _ _ _ _ _ _ (by
        rw [hbody]
        exact commitBody_run P _ _ _ t _ hd (by
          show (t.observeList (Committed.ofMats hashF compF [(specBackend EF).leaves (2 ^ la) f]).root.toList
            ).checkWitness P.commitPowBits (t1.grind P.commitPowBits).1 = _
          rw [ht1]; exact checkWitness_grind _ _ hg1)),
        ih _ _ _ _ hd1 ht]
      refine congrArg Except.ok (Prod.ext (Array.toList_inj.mp ?_) rfl)
      simp only [Array.toList_append, Array.toList_push, List.append_assoc,
        List.singleton_append]

/-! ### The verifier's fold loop -/

/-- The body of the verifier's loop over a query's folds. -/
def foldBody {K : Type} [Challenge F K] (beta : K) (commit : Digest F) (s : CommitStep F K)
    (ro : List (Nat × K)) (eval : K) (index logH : Nat) :
    M poseidon2 (ForInStep (List (Nat × K) × K × Nat × Nat)) := do
  let arity := 2 ^ s.logArity
  ensure (s.siblings.size == arity - 1) "sibling count"
  let pos := index % arity
  let evals := (List.range arity).map fun j ↦
    if j < pos then s.siblings.getD j 0 else if j = pos then eval else s.siblings.getD (j - 1) 0
  let logFolded := logH - s.logArity
  let index := index >>> s.logArity
  ensure (← checkOpening poseidon2 commit [2 ^ logFolded] index [evals.flatMap Ext.coeffs]
    s.path.toList) "commit-phase opening"
  let eval := foldRow index logFolded s.logArity beta evals
  match ro with
  | (h, r) :: rest =>
    if h == logFolded then
      pure (ForInStep.yield (rest, eval + Ext.powTwo beta s.logArity * r, index, logFolded))
    else pure (ForInStep.yield (ro, eval, index, logFolded))
  | [] => pure (ForInStep.yield (ro, eval, index, logFolded))

/-- The state after a fold: the next reduced opening is added if it has the folded height. -/
def foldNext (beta : EF) (la : Nat) (ro : List (Nat × EF)) (eval : EF) (index logFolded : Nat) :
    List (Nat × EF) × EF × Nat × Nat :=
  match ro with
  | (h, r) :: rest =>
    if h == logFolded then (rest, eval + Ext.powTwo beta la * r, index, logFolded)
    else (ro, eval, index, logFolded)
  | [] => (ro, eval, index, logFolded)

theorem foldBody_run (beta : EF) (commit : Digest F) (s : CommitStep F EF) (ro : List (Nat × EF))
    (eval : EF) (index logH : Nat) (t : Transcript F 24) (G : List EF)
    (h1 : s.siblings.size = 2 ^ s.logArity - 1)
    (h2 : (List.range (2 ^ s.logArity)).map (fun j ↦
      if j < index % 2 ^ s.logArity then s.siblings.getD j 0
      else if j = index % 2 ^ s.logArity then eval else s.siblings.getD (j - 1) 0) = G)
    (h3 : Merkle.KoalaBear.verifyBatch F commit [2 ^ (logH - s.logArity)]
      (index >>> s.logArity) [G.flatMap Ext.coeffs] s.path.toList = true) :
    foldBody beta commit s ro eval index logH t = .ok (.yield (foldNext beta s.logArity ro
      (foldRow (index >>> s.logArity) (logH - s.logArity) s.logArity beta G)
      (index >>> s.logArity) (logH - s.logArity)), t) := by
  unfold foldBody
  simp only [h1, beq_self_eq_true, ensure_true, pure_bind, h2, checkOpening_eq, h3]
  cases ro with
  | nil => rfl
  | cons p rest =>
    obtain ⟨h, r⟩ := p
    simp only [foldNext]
    split <;> rfl

/-- An input's reduced opening at the query index `index0` into the domain of `2 ^ logMax`. -/
def roOf (index0 logMax : Nat) (v : Array EF) : Nat × EF :=
  (Nat.log2 v.size, v.getD (index0 >>> (logMax - Nat.log2 v.size)) 0)

theorem shiftRight_shiftRight (i a b c : Nat) (hc : c ≤ b) (hb : b ≤ a) :
    i >>> (a - b) >>> c = i >>> (a - (b - c)) := by
  rw [← Nat.shiftRight_add]; congr 1; omega

/-- One fold of a query at the round's index: the verifier's step yields the next round's state. -/
theorem fold_round (P : Params) (hP : 0 < P.maxLogArity) {h : Nat} {f : Array EF}
    {rest : List (Array EF)} (hg : Good P h f rest)
    (hgt : P.logBlowup + P.logFinalPolyLen < h) (beta : EF) (index0 logMax : Nat)
    (hidx : index0 < 2 ^ logMax) (hh : h ≤ logMax) (t : Transcript F 24) :
    let la := logArityFor P h (rest.head?.map (Nat.log2 ·.size))
    let idx := index0 >>> (logMax - h)
    let c := Committed.ofMats hashF compF [(specBackend EF).leaves (2 ^ la) f]
    let o := c.openAt (idx >>> la)
    let ev := unflatten ((o.values.getD 0 #[]).toList)
    let sib := ((List.range (2 ^ la)).filter (· != idx % 2 ^ la)).map fun j ↦ ev.getD j 0
    let next := addNext la beta (foldOnce la beta f) rest
    foldBody beta c.root ⟨la, sib.toArray, o.path⟩ (rest.map (roOf index0 logMax)) (f.getD idx 0)
      idx h t = .ok (.yield (next.2.map (roOf index0 logMax), next.1.getD (idx >>> la) 0,
        idx >>> la, h - la), t) := by
  intro la idx c o ev sib next
  obtain ⟨h1, h2, hg'⟩ := good_step P hP hg hgt beta
  obtain ⟨hL, hf, hsort, hrest⟩ := hg
  have hsz := hf.1
  have h24 := hf.2.1
  have hidx' : idx < 2 ^ h := by
    show index0 >>> (logMax - h) < 2 ^ h
    rw [Nat.shiftRight_eq_div_pow]
    refine Nat.div_lt_of_lt_mul ?_
    rw [← pow_add, Nat.sub_add_cancel hh]; exact hidx
  obtain ⟨hs1, hs2, hs3⟩ := answer_round f h la idx hsz (by omega24) hidx'
  rw [hs2] at hs3
  rw [foldBody_run beta c.root ⟨la, sib.toArray, o.path⟩ (rest.map (roOf index0 logMax))
    (f.getD idx 0) idx h t ((List.range (2 ^ la)).map fun k ↦ f.getD ((idx >>> la) * 2 ^ la + k) 0)
    hs1 hs2 hs3]
  have hr : idx >>> la < 2 ^ (h - la) := by
    rw [Nat.shiftRight_eq_div_pow]
    refine Nat.div_lt_of_lt_mul ?_
    rw [← pow_add, Nat.add_sub_cancel' (by omega24)]; exact hidx'
  have hfold : foldRow (idx >>> la) (h - la) la beta
      ((List.range (2 ^ la)).map fun k ↦ f.getD ((idx >>> la) * 2 ^ la + k) 0) =
      (foldOnce la beta f).getD (idx >>> la) 0 := by
    rw [foldOnce_eq la h beta f hsz (by omega24) h24 h1,
      CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ hr]
  have hfo : (foldOnce la beta f).size = 2 ^ (h - la) :=
    size_foldOnce la h beta f hsz (by omega24) h24 h1
  dsimp only
  rw [hfold]
  refine congrArg Except.ok (Prod.ext (congrArg ForInStep.yield ?_) rfl)
  show foldNext beta la (rest.map (roOf index0 logMax)) _ _ _ = _
  have hshift : idx >>> la = index0 >>> (logMax - (h - la)) :=
    shiftRight_shiftRight index0 logMax h la (by omega24) hh
  cases rest with
  | nil => rfl
  | cons v vs =>
    obtain ⟨hvh, hvL, hvd⟩ := hrest v List.mem_cons_self
    have hvs := hvd.1
    rw [log2_size hvd] at hvs
    simp only [List.map_cons, foldNext, roOf, next, addNext]
    by_cases he : Nat.log2 v.size = h - la
    · have he' : (v.size == (foldOnce la beta f).size) = true := by
        rw [beq_iff_eq, hvs, hfo, he]
      rw [ite_eq_left (by rw [beq_iff_eq]; exact he), ite_eq_left he']
      congr 1
      have hz : idx >>> la < (Array.zipWith (fun u x ↦ u + Ext.powTwo beta la * x)
          (foldOnce la beta f) v).size := by
        rw [Array.size_zipWith, hfo, hvs, he, Nat.min_self]; exact hr
      rw [he, ← hshift, getD_lt _ _ hz, Array.getElem_zipWith,
        ← getD_lt _ _ (by rw [hfo]; exact hr),
        ← getD_lt _ _ (by rw [hvs, he]; exact hr)]
    · have he' : ¬ (v.size == (foldOnce la beta f).size) = true := by
        rw [beq_iff_eq, hvs, hfo]
        exact fun e ↦ he (by rw [log2_size hvd]; exact Nat.pow_right_injective (le_refl 2) e)
      rw [ite_eq_right (by rw [beq_iff_eq]; exact he), ite_eq_right he']
      rfl

theorem answerSteps_cons (r : Rd EF) (rs : List (Rd EF)) (la : Nat) (las : List Nat) (cur : Nat) :
    answerSteps (specBackend EF) ((r :: rs).map (·.c)) (la :: las) cur =
      ⟨la, (((List.range (2 ^ la)).filter (· != cur % 2 ^ la)).map fun j ↦
          (unflatten (((r.c.openAt (cur >>> la)).values.getD 0 #[]).toList)).getD j 0).toArray,
        (r.c.openAt (cur >>> la)).path⟩ ::
          answerSteps (specBackend EF) (rs.map (·.c)) las (cur >>> la) :=
  rfl

/-- At the final height no input remains. -/
theorem good_final {P : Params} {f : Array EF} {rest : List (Array EF)}
    (hg : Good P (P.logBlowup + P.logFinalPolyLen) f rest) : rest = [] := by
  cases rest with
  | nil => rfl
  | cons v vs =>
    have := hg.2.2.2 v List.mem_cons_self
    omega

/-- A query's folds walk the chain at the query's index and end at the final vector's entry, with
every reduced opening consumed. -/
theorem fold_loop (P : Params) (hP : 0 < P.maxLogArity)
    (body : (EF × Digest F) × CommitStep F EF → List (Nat × EF) × EF × Nat × Nat →
      M poseidon2 (ForInStep (List (Nat × EF) × EF × Nat × Nat)))
    (hbody : ∀ beta commit s ro eval index logH,
      body ((beta, commit), s) (ro, eval, index, logH) = foldBody beta commit s ro eval index logH)
    (index0 logMax : Nat) (hidx : index0 < 2 ^ logMax) (fuel : Nat) :
    ∀ h f rest t t', Good P h f rest → h - (P.logBlowup + P.logFinalPolyLen) ≤ fuel →
      h ≤ logMax →
      forIn ((((chain P fuel f rest t).1.map (·.beta)).zip
          ((chain P fuel f rest t).1.map (·.c.root))).zip
          (answerSteps (specBackend EF) ((chain P fuel f rest t).1.map (·.c))
            ((chain P fuel f rest t).1.map (·.la)) (index0 >>> (logMax - h))))
        (rest.map (roOf index0 logMax), f.getD (index0 >>> (logMax - h)) 0,
          index0 >>> (logMax - h), h) body t' =
        .ok (([], (chain P fuel f rest t).2.1.getD
          (index0 >>> (logMax - (P.logBlowup + P.logFinalPolyLen))) 0,
          index0 >>> (logMax - (P.logBlowup + P.logFinalPolyLen)),
          P.logBlowup + P.logFinalPolyLen), t') := by
  induction fuel with
  | zero =>
    intro h f rest t t' hg hfuel _
    have hh : h = P.logBlowup + P.logFinalPolyLen := by have := hg.1; omega
    subst hh
    rw [good_final hg]
    rfl
  | succ fuel ih =>
    intro h f rest t t' hg hfuel hh
    have hsz := hg.2.1.1
    by_cases hs : f.size ≤ 2 ^ (P.logBlowup + P.logFinalPolyLen)
    · rw [chain, ite_eq_left hs]
      have hh' : h = P.logBlowup + P.logFinalPolyLen := by
        rw [hsz] at hs
        have := (Nat.pow_le_pow_iff_right (by decide)).mp hs
        have := hg.1; omega
      subst hh'
      rw [good_final hg]
      rfl
    · rw [chain, ite_eq_right hs]
      have hgt : P.logBlowup + P.logFinalPolyLen < h := by
        by_contra hc
        exact hs (by rw [hsz]; exact Nat.pow_le_pow_right (by decide) (by omega24))
      rw [hsz, Nat.log2_two_pow]
      dsimp only
      generalize (((Transcript.observeList _ _).grind P.commitPowBits).2.sampleExtValue : EF) = beta
      generalize (Transcript.sampleExtState EF (((Transcript.observeList _ _).grind
          P.commitPowBits).2)) = t3
      obtain ⟨h1, h2, hg'⟩ := good_step P hP hg hgt beta
      simp only [List.map_cons]
      rw [answerSteps_cons, List.zip_cons_cons, List.zip_cons_cons,
        forIn_cons_ok _ _ _ _ _ _ _ (by
          rw [hbody]; exact fold_round P hP hg hgt beta index0 logMax hidx hh t'),
        shiftRight_shiftRight index0 logMax h _ (by omega24) hh]
      exact ih _ _ _ _ t' hg' (by omega24) (by omega24)

/-- `fold_loop` from the tallest input. -/
theorem fold_loop0 (P : Params) (hP : 0 < P.maxLogArity)
    (body : (EF × Digest F) × CommitStep F EF → List (Nat × EF) × EF × Nat × Nat →
      M poseidon2 (ForInStep (List (Nat × EF) × EF × Nat × Nat)))
    (hbody : ∀ beta commit s ro eval index logH,
      body ((beta, commit), s) (ro, eval, index, logH) = foldBody beta commit s ro eval index logH)
    (index0 h0 : Nat) (hidx : index0 < 2 ^ h0) (fuel : Nat) (f rest t t')
    (hg : Good P h0 f rest) (hfuel : h0 - (P.logBlowup + P.logFinalPolyLen) ≤ fuel) :
    forIn ((((chain P fuel f rest t).1.map (·.beta)).zip
        ((chain P fuel f rest t).1.map (·.c.root))).zip
        (answerSteps (specBackend EF) ((chain P fuel f rest t).1.map (·.c))
          ((chain P fuel f rest t).1.map (·.la)) index0))
      (rest.map (roOf index0 h0), f.getD index0 0, index0, h0) body t' =
      .ok (([], (chain P fuel f rest t).2.1.getD
        (index0 >>> (h0 - (P.logBlowup + P.logFinalPolyLen))) 0,
        index0 >>> (h0 - (P.logBlowup + P.logFinalPolyLen)),
        P.logBlowup + P.logFinalPolyLen), t') := by
  have := fold_loop P hP body hbody index0 h0 hidx fuel h0 f rest t t' hg hfuel le_rfl
  simp only [Nat.sub_self, Nat.shiftRight_zero] at this
  exact this

theorem length_answerSteps (rs : List (Rd EF)) :
    ∀ cur, (answerSteps (specBackend EF) (rs.map (·.c)) (rs.map (·.la)) cur).length = rs.length :=
        by
  induction rs with
  | nil => intro cur; rfl
  | cons r rs ih =>
    intro cur
    rw [show (r :: rs).map (·.la) = r.la :: rs.map (·.la) from rfl, answerSteps_cons,
      List.length_cons, ih, List.length_cons]

/-- A query's folds from the reduced openings of the inputs `f0 :: rest` at `index0` end at the
final vector's entry. -/
theorem verifyQuery_run (P : Params) (hP : 0 < P.maxLogArity) (f0 : Array EF)
    (rest : List (Array EF)) (h0 : Nat) (hg : Good P h0 f0 rest) (fuel : Nat)
    (hfuel : h0 - (P.logBlowup + P.logFinalPolyLen) ≤ fuel) (t t' : Transcript F 24) (index0 : Nat)
    (hidx : index0 < 2 ^ h0) :
    verifyQuery poseidon2 P h0 index0 ((chain P fuel f0 rest t).1.map (·.beta))
      ((chain P fuel f0 rest t).1.map (·.c.root))
      (answerSteps (specBackend EF) ((chain P fuel f0 rest t).1.map (·.c))
        ((chain P fuel f0 rest t).1.map (·.la)) index0)
      ((f0 :: rest).map (roOf index0 h0)) t' =
      .ok (((chain P fuel f0 rest t).2.1.getD
        (index0 >>> (h0 - (P.logBlowup + P.logFinalPolyLen))) 0,
        index0 >>> (h0 - (P.logBlowup + P.logFinalPolyLen))), t') := by
  have hlog : Nat.log2 f0.size = h0 := log2_size hg.2.1
  unfold verifyQuery
  simp only [List.map_cons, roOf, hlog, Nat.sub_self, Nat.shiftRight_zero]
  rw [pure_bind]
  simp only [beq_self_eq_true, ensure_true, pure_bind, List.length_map, length_answerSteps,
    Bool.and_self, List.tail_cons]
  rw [bind_ok (fold_loop0 P hP _ ?hb index0 h0 hidx fuel f0 rest t t' hg hfuel)]
  · simp only [beq_self_eq_true, ensure_true, pure_bind, List.isEmpty_nil]
    rfl
  · intros; rfl

/-! ### The commit phase's result and the queries -/

theorem foldl_pushRd (rs : List (Rd EF)) :
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

theorem answerSteps_logArity (rs : List (Rd EF)) :
    ∀ cur, (answerSteps (specBackend EF) (rs.map (·.c)) (rs.map (·.la)) cur).map (·.logArity) =
      rs.map (·.la) := by
  induction rs with
  | nil => intro cur; rfl
  | cons r rs ih =>
    intro cur
    rw [show (r :: rs).map (·.la) = r.la :: rs.map (·.la) from rfl, answerSteps_cons,
      List.map_cons, ih]

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

omit [Challenge F EF] in
/-- The verifier's queries sample the prover's indices. -/
theorem query_loop (logMax : Nat) (mk : Nat → QueryProof F EF)
    (body : QueryProof F EF → PUnit → M poseidon2 (ForInStep PUnit))
    (qb : QueryProof F EF → M poseidon2 (ForInStep PUnit))
    (hbody : ∀ q, body q () = qb q)
    (hstep : ∀ t : Transcript F 24, t.duplex = KoalaBear.duplex →
      qb (mk (t.sampleBits logMax).1) t = .ok (.yield (), (t.sampleBits logMax).2)) :
    ∀ n (t : Transcript F 24), t.duplex = KoalaBear.duplex →
      forIn ((sampleIndices logMax n t).1.map mk) () body t = .ok ((), (sampleIndices logMax n t).2)
  | 0, _, _ => rfl
  | n + 1, t, hd => by
    rw [sampleIndices, List.map_cons,
      forIn_cons_ok _ _ _ _ _ _ _ (by rw [hbody]; exact hstep t hd)]
    exact query_loop logMax mk body qb hbody hstep n _ ((duplex_sampleBits t logMax).trans hd)

theorem flag_sampleIndices (logMax : Nat) :
    ∀ n t, (sampleIndices logMax n t).2.grindFailed = t.grindFailed
  | 0, _ => rfl
  | n + 1, t => by
    rw [sampleIndices]; exact (flag_sampleIndices logMax n _).trans (flag_sampleBits _ _)

theorem forM_observe (l : List Nat) (t : Transcript F 24) :
    (l.forM fun la ↦ pObserve (la : F)).run t =
      ((), l.foldl (fun t (a : Nat) ↦ t.observe (a : F)) t) := by
  induction l generalizing t with
  | nil => rfl
  | cons a l ih =>
    show StateT.run (do pObserve (a : F); l.forM fun la ↦ pObserve (la : F)) t = _
    rw [prun_bind, ih]; rfl

theorem observe_loop (l : List Nat) (body : Nat → PUnit → M poseidon2 (ForInStep PUnit))
    (hbody : ∀ a t, body a () t = .ok (.yield (), t.observe (a : F))) :
    ∀ t, forIn l () body t = .ok ((), l.foldl (fun t (a : Nat) ↦ t.observe (a : F)) t) := by
  induction l with
  | nil => intro t; rfl
  | cons a l ih => intro t; rw [forIn_cons_ok _ _ _ _ _ _ _ (hbody a t), ih]; rfl

/-- The body of the verifier's loop over the queries. -/
def queryBody (P : Params) (logMax : Nat) (alpha : EF) (rounds : List (Round F EF)) (betas : Array EF)
    (commits : Array (Digest F)) (finalPoly : Array EF) (q : QueryProof F EF) :
    M poseidon2 (ForInStep PUnit) := do
  let index ← sampleBits poseidon2 logMax
  let ro ← openInput poseidon2 P logMax index alpha q.inputs.toList rounds
  let e ← verifyQuery poseidon2 P logMax index betas.toList commits.toList q.steps.toList ro
  ensure (finalPoly.foldr (fun c acc ↦
    acc * Ext.ofBase (powF (twoAdicGen logMax) (reverseBits e.2 logMax)) + c) 0 == e.1)
    "final polynomial mismatch"
  pure (ForInStep.yield PUnit.unit)

theorem queryBody_run (P : Params) (logMax : Nat) (alpha : EF) (rounds : List (Round F EF))
    (betas : Array EF) (commits : Array (Digest F)) (finalPoly : Array EF) (q : QueryProof F EF)
    (t : Transcript F 24) (hd : t.duplex = KoalaBear.duplex) (ro : List (Nat × EF)) (eval : EF)
    (idxF : Nat)
    (h1 : openInput poseidon2 P logMax (t.sampleBits logMax).1 alpha q.inputs.toList rounds
      (t.sampleBits logMax).2 = .ok (ro, (t.sampleBits logMax).2))
    (h2 : verifyQuery poseidon2 P logMax (t.sampleBits logMax).1 betas.toList commits.toList
      q.steps.toList ro (t.sampleBits logMax).2 = .ok ((eval, idxF), (t.sampleBits logMax).2))
    (h3 : finalPoly.foldr (fun c acc ↦
      acc * Ext.ofBase (powF (twoAdicGen logMax) (reverseBits idxF logMax)) + c) 0 = eval) :
    queryBody P logMax alpha rounds betas commits finalPoly q t =
      .ok (.yield (), (t.sampleBits logMax).2) := by
  unfold queryBody
  rw [bind_ok (t' := (t.sampleBits logMax).2) (a := (t.sampleBits logMax).1)
    (sampleBits_run t logMax hd), bind_ok h1,
    bind_ok h2]
  simp only [h3, beq_self_eq_true, ensure_true, pure_bind]
  rfl

/-! ### The prover's run -/

/-- The final polynomial of a commit phase ending at `fin`. -/
def finalPolyOf (P : Params) (fin : Array EF) : Array EF :=
  idft P.logFinalPolyLen (Array.ofFn (n := 2 ^ P.logFinalPolyLen) fun i ↦
    fin.getD (reverseBits i P.logFinalPolyLen) 0)

theorem commitPhase_run (P : Params) (f0 : Array EF) (rest : List (Array EF)) (t : Transcript F 24) :
    (commitPhase (specBackend EF) P (f0 :: rest)).run t =
      ({ (chain P f0.size f0 rest t).1.foldl pushRd ⟨#[], [], #[], #[], #[]⟩ with
          finalPoly := finalPolyOf P (chain P f0.size f0 rest t).2.1 },
        (chain P f0.size f0 rest t).2.2.observeExts
          (finalPolyOf P (chain P f0.size f0 rest t).2.1).toList) := by
  have hc : (commitRounds (specBackend EF) P ((specBackend EF).size f0) f0 rest
      ⟨#[], [], #[], #[], #[]⟩).run t =
      let r := chain P f0.size f0 rest t
      ((r.2.1, r.1.foldl pushRd ⟨#[], [], #[], #[], #[]⟩), r.2.2) :=
    commitRounds_run P _ f0 rest _ t
  unfold commitPhase
  rw [prun_bind, hc]
  rfl

/-- The specification prover's FRI proof, from the inputs `f0 :: rest`. -/
theorem proveFri_run (P : Params) (rounds : List (OpenRound (specBackend EF)))
    (inputsOf : EF → List (Array EF)) (t : Transcript F 24) (f0 : Array EF) (rest : List (Array EF))
    (hins : (inputsOf (t.sampleExtValue : EF) : List (specBackend EF).V) = (f0 :: rest : List
        (specBackend EF).V)) :
    let r := chain P f0.size f0 rest (Transcript.sampleExtState EF t)
    let cp := { r.1.foldl pushRd ⟨#[], [], #[], #[], #[]⟩ with finalPoly := finalPolyOf P r.2.1 }
    let t3 := cp.arities.toList.foldl (fun t (a : Nat) ↦ t.observe (a : F))
      (r.2.2.observeExts (finalPolyOf P r.2.1).toList)
    let mk : Nat → QueryProof F EF := fun index ↦
      ⟨(rounds.map fun (c, _) ↦ (specBackend EF).openAt c
        (index >>> (Nat.log2 f0.size - (specBackend EF).logHeight c))).toArray,
        answerQuery (specBackend EF) cp index⟩
    let qs := sampleIndices (Nat.log2 f0.size) P.numQueries (t3.grind P.queryPowBits).2
    (proveFri (specBackend EF) P rounds inputsOf).run t =
      (⟨cp.commits, cp.witnesses, (qs.1.map mk).toArray, finalPolyOf P r.2.1,
        (t3.grind P.queryPowBits).1⟩, qs.2) := by
  intro r cp t3 mk qs
  unfold proveFri
  rw [prun_bind]
  rw [show (StateT.run pSampleExt t) =
    ((t.sampleExtValue : EF), Transcript.sampleExtState EF t) from rfl]
  dsimp only
  rw [hins, show ((List.map (specBackend EF).size (f0 :: rest)).headD 0).log2 = Nat.log2 f0.size
    from rfl, prun_bind, commitPhase_run, prun_bind, forM_observe, prun_bind]
  rw [show StateT.run (pGrind P.queryPowBits) t3 = t3.grind P.queryPowBits from rfl, prun_bind,
    mapM_queries (Nat.log2 f0.size) mk _ ?hg, List.length_range]
  · rfl
  · intro _ _; rfl

theorem length_sampleIndices (logMax : Nat) :
    ∀ n t, (sampleIndices logMax n t).1.length = n
  | 0, _ => rfl
  | n + 1, t => by
    rw [sampleIndices, List.length_cons, length_sampleIndices logMax n]

/-! ### FRI completeness -/

/-- FRI's inputs: tallest first, with strictly decreasing heights not below the final height,
each the values in bit-reversed order of a polynomial of degree below its height over the blowup.
-/
def InputsOk (P : Params) (ins : List (Array EF)) : Prop :=
  ∃ f0 rest, ins = f0 :: rest ∧ Good P (Nat.log2 f0.size) f0 rest

/-- **FRI completeness**: the verifier's FRI accepts the specification prover's proof of
low-degree inputs whose openings give the inputs' entries, when the prover's grinder found its
witnesses. -/
theorem verifyFri_proveFri (P : Params) (rounds : List (OpenRound (specBackend EF)))
    (inputsOf : EF → List (Array EF)) (vrounds : List (Round F EF)) (t : Transcript F 24)
    (hd : t.duplex = KoalaBear.duplex) (hlow : ∀ alpha, InputsOk P (inputsOf alpha))
    (hP : 0 < P.maxLogArity) (hq : 0 < P.numQueries)
    (hgrind : ((proveFri (specBackend EF) P rounds inputsOf).run t).2.grindFailed = false)
    (hopen : ∀ alpha index, index < 2 ^ Nat.log2 (((inputsOf alpha).map Array.size).headD 0) →
      openInput poseidon2 P (Nat.log2 (((inputsOf alpha).map Array.size).headD 0)) index alpha
        (rounds.map fun (c, _) ↦ c.openAt (index >>>
          (Nat.log2 (((inputsOf alpha).map Array.size).headD 0) - Nat.log2 c.maxHeight)))
        vrounds =
      pure ((inputsOf alpha).map fun v ↦ (Nat.log2 v.size, v.getD (index >>>
        (Nat.log2 (((inputsOf alpha).map Array.size).headD 0) - Nat.log2 v.size)) 0))) :
    verifyFri poseidon2 P ((proveFri (specBackend EF) P rounds inputsOf).run t).1 vrounds t =
      .ok ((), ((proveFri (specBackend EF) P rounds inputsOf).run t).2) := by
  obtain ⟨f0, rest, hins, hg⟩ := hlow (t.sampleExtValue : EF)
  have hins' : (inputsOf (t.sampleExtValue : EF) : List (specBackend EF).V) =
      (f0 :: rest : List (specBackend EF).V) := hins
  set h0 := Nat.log2 f0.size with hh0
  set r := chain P f0.size f0 rest (Transcript.sampleExtState EF t) with hr
  set cp : CommitPhase F EF (Committed F) :=
    { r.1.foldl pushRd ⟨#[], [], #[], #[], #[]⟩ with finalPoly := finalPolyOf P r.2.1 } with hcp
  set t3 := cp.arities.toList.foldl (fun t (a : Nat) ↦ t.observe (a : F))
    (r.2.2.observeExts (finalPolyOf P r.2.1).toList) with ht3
  set mk : Nat → QueryProof F EF := fun index ↦
      ⟨(rounds.map fun (c, _) ↦ (specBackend EF).openAt c
        (index >>> (h0 - (specBackend EF).logHeight c))).toArray,
        answerQuery (specBackend EF) cp index⟩ with hmk
  set qs := sampleIndices h0 P.numQueries (t3.grind P.queryPowBits).2 with hqs
  have hrun : (proveFri (specBackend EF) P rounds inputsOf).run t =
      (⟨cp.commits, cp.witnesses, (qs.1.map mk).toArray, finalPolyOf P r.2.1,
        (t3.grind P.queryPowBits).1⟩, qs.2) := proveFri_run P rounds inputsOf t f0 rest hins'
  rw [hrun]
  obtain ⟨hcom, hdata, hwit, hari, -⟩ := foldl_pushRd r.1 ⟨#[], [], #[], #[], #[]⟩
  have hL := hg.1
  have h24 : h0 ≤ 24 := hg.2.1.2.1
  have hsz : f0.size = 2 ^ h0 := hg.2.1.1
  have hfuel : h0 - (P.logBlowup + P.logFinalPolyLen) ≤ f0.size := by
    rw [hsz]; exact le_trans (Nat.sub_le _ _) (Nat.lt_two_pow_self).le
  obtain ⟨hfin,
      hsum⟩ := chain_final P hP f0.size h0 f0 rest (Transcript.sampleExtState EF t) hg hfuel
  have hsteps : ∀ index, (mk index).steps.toList =
      answerSteps (specBackend EF) (r.1.map (·.c)) (r.1.map (·.la)) index := by
    intro index
    show (answerSteps (specBackend EF) cp.data cp.arities.toList index).toArray.toList = _
    rw [List.toList_toArray]
    show answerSteps (specBackend EF) (List.foldl pushRd ⟨#[], [], #[], #[], #[]⟩ r.1).data
      (List.foldl pushRd ⟨#[], [], #[], #[], #[]⟩ r.1).arities.toList index = _
    rw [hdata, hari]
    rfl
  obtain ⟨n, hn⟩ : ∃ n, P.numQueries = n + 1 := ⟨P.numQueries - 1, by omega⟩
  have hqs1 : ∃ i0 is, qs.1 = i0 :: is := by
    rw [hqs, hn, sampleIndices]; exact ⟨_, _, rfl⟩
  obtain ⟨i0, is, hqs1⟩ := hqs1
  have hlen : ∀ index, (mk index).steps.size = r.1.length := fun index ↦ by
    rw [← Array.length_toList, hsteps, length_answerSteps]
  have hcsize : cp.commits.size = r.1.length := by
    rw [← Array.length_toList]
    show (List.foldl pushRd ⟨#[], [], #[], #[], #[]⟩ r.1).commits.toList.length = _
    rw [hcom, List.length_append, List.length_map]; exact Nat.zero_add _
  have hwsize : cp.witnesses.size = r.1.length := by
    rw [← Array.length_toList]
    show (List.foldl pushRd ⟨#[], [], #[], #[], #[]⟩ r.1).witnesses.toList.length = _
    rw [hwit, List.length_append, List.length_map]; exact Nat.zero_add _
  have harities : (Option.map (fun q ↦ q.steps.toList.map (·.logArity))
      (qs.1.map mk).toArray[0]?).getD [] = r.1.map (·.la) := by
    rw [hqs1]
    show (List.map (·.logArity) (mk i0).steps.toList) = _
    rw [hsteps, answerSteps_logArity]
  have hct : cp.commits.toList = r.1.map (·.c.root) := by
    show (List.foldl pushRd ⟨#[], [], #[], #[], #[]⟩ r.1).commits.toList = _
    rw [hcom]; rfl
  have hwt : cp.witnesses.toList = r.1.map (·.w) := by
    show (List.foldl pushRd ⟨#[], [], #[], #[], #[]⟩ r.1).witnesses.toList = _
    rw [hwit]; rfl
  have ht3' : t3 = (r.1.map (·.la)).foldl (fun t (a : Nat) ↦ t.observe (a : F))
      (r.2.2.observeExts (finalPolyOf P r.2.1).toList) := by
    rw [ht3]
    show List.foldl _ _ (List.foldl pushRd ⟨#[], [], #[], #[], #[]⟩ r.1).arities.toList = _
    rw [hari]; rfl
  have hall : ((List.map mk qs.1).toArray.all fun q ↦
      q.steps.size == cp.commits.size &&
        List.map (fun x ↦ x.logArity) q.steps.toList == List.map (fun x ↦ x.la) r.1) = true := by
    rw [Array.all_eq_true']
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hx)
    rw [hlen, hcsize, hsteps, answerSteps_logArity, beq_self_eq_true, beq_self_eq_true,
      Bool.and_self]
  have hlog : (List.map (fun x ↦ x.la) r.1).sum + P.logBlowup + P.logFinalPolyLen = h0 := by
    rw [hsum]; omega
  have hq4 : (t3.grind P.queryPowBits).2.grindFailed = false := by
    rw [hrun] at hgrind
    rw [← flag_sampleIndices h0 P.numQueries]
    exact hgrind
  have hf : r.2.2.grindFailed = false := by
    have := flag_grind _ _ hq4
    rwa [ht3', flag_foldl_observe, flag_observeExts] at this
  have hd2 : r.2.2.duplex = KoalaBear.duplex := by rw [duplex_chain, duplex_sampleExt, hd]
  have hd3 : t3.duplex = KoalaBear.duplex := by
    rw [ht3', duplex_foldl_observe, duplex_observeExts, hd2]
  unfold verifyFri
  rw [bind_ok (t' := (Transcript.sampleExtState EF t)) (a := (t.sampleExtValue : EF))
      (sampleExt_run t)]
  dsimp only [arities]
  rw [harities, hall, ensure_true, pure_bind, hlog, hwsize, hcsize, beq_self_eq_true, ensure_true,
    pure_bind, hct, hwt]
  rw [bind_ok (commit_loop P _ ?hb f0.size f0 rest (Transcript.sampleExtState EF t) #[]
    ((duplex_sampleExt t).trans hd) hf)]
  rw [show ((finalPolyOf P r.2.1).size == 2 ^ P.logFinalPolyLen) = true by
      rw [show (finalPolyOf P r.2.1).size = 2 ^ P.logFinalPolyLen from Array.size_ofFn,
        beq_self_eq_true],
    ensure_true, pure_bind,
    bind_ok (observeExts_run r.2.2 (finalPolyOf P r.2.1).toList),
    List.size_toArray, List.length_map, length_sampleIndices, beq_self_eq_true, ensure_true,
    pure_bind, bind_ok (observe_loop _ _ ?hobs _), ← ht3']
  rw [bind_ok (t' := (t3.grind P.queryPowBits).2) (a := true) (by
      rw [checkWitness_run _ _ _ hd3, checkWitness_grind _ _ hq4]),
    ensure_true, pure_bind, ← Array.forIn_toList, List.toList_toArray,
    bind_ok (query_loop h0 mk _ (queryBody P h0 (t.sampleExtValue : EF) vrounds
      (#[] ++ (r.1.map Rd.beta).toArray) (r.1.map (·.c.root)).toArray (finalPolyOf P r.2.1))
      ?hqb ?hq _ _ ((duplex_grind t3 _).trans hd3))]
  · rfl
  · intro _; rfl
  · intro t' hd'
    set i := (t'.sampleBits h0).1 with hi_def
    have hi : i < 2 ^ h0 := sampleBits_lt _ _
    have h1 : openInput poseidon2 P h0 i (t.sampleExtValue : EF) (mk i).inputs.toList vrounds
        (t'.sampleBits h0).2 =
        .ok ((f0 :: rest).map (roOf i h0), (t'.sampleBits h0).2) := by
      have hop := hopen (t.sampleExtValue : EF) i
      rw [hins] at hop
      exact congrFun (hop hi) (t'.sampleBits h0).2
    have hidxF : i >>> (h0 - (P.logBlowup + P.logFinalPolyLen)) <
        2 ^ (P.logBlowup + P.logFinalPolyLen) := by
      rw [Nat.shiftRight_eq_div_pow]
      refine Nat.div_lt_of_lt_mul ?_
      rw [← pow_add, Nat.sub_add_cancel hL]; exact hi
    have h2 : verifyQuery poseidon2 P h0 i (#[] ++ (r.1.map Rd.beta).toArray : Array EF).toList
        (r.1.map (·.c.root)).toArray.toList
        (mk i).steps.toList ((f0 :: rest).map (roOf i h0)) (t'.sampleBits h0).2 =
        .ok ((r.2.1.getD (i >>> (h0 - (P.logBlowup + P.logFinalPolyLen))) 0,
          i >>> (h0 - (P.logBlowup + P.logFinalPolyLen))), (t'.sampleBits h0).2) := by
      rw [hsteps, Array.toList_append, List.toList_toArray, List.toList_toArray]
      exact verifyQuery_run P hP f0 rest h0 hg f0.size hfuel (Transcript.sampleExtState EF t) _ i hi
    exact queryBody_run P h0 (t.sampleExtValue : EF) vrounds _ _ (finalPolyOf P r.2.1) (mk i) t'
        hd' _
      _ _ h1 h2 (horner_idft r.2.1 P.logBlowup P.logFinalPolyLen h0 _ hfin hL h24 hidxF)
  · intros; rfl
  · intros; rfl

/-- With one input, the specification prover's proof folds by Plonky3's schedule, as the
verifier checks. -/
theorem arities_proveFri (P : Params) (rounds : List (OpenRound (specBackend EF)))
    (inputsOf : EF → List (Array EF)) (t : Transcript F 24) (f0 : Array EF)
    (hins : inputsOf (t.sampleExtValue : EF) = [f0]) (hg : Good P (Nat.log2 f0.size) f0 [])
    (hP : 0 < P.maxLogArity) (hq : 0 < P.numQueries) :
    arities ((proveFri (specBackend EF) P rounds inputsOf).run t).1 =
      foldArities P.maxLogArity (Nat.log2 f0.size - (P.logBlowup + P.logFinalPolyLen)) := by
  rw [proveFri_run P rounds inputsOf t f0 [] hins]
  dsimp only
  set r := chain P f0.size f0 [] (Transcript.sampleExtState EF t)
  obtain ⟨-, hdata, -, hari, -⟩ := foldl_pushRd r.1 ⟨#[], [], #[], #[], #[]⟩
  obtain ⟨n, hn⟩ : ∃ n, P.numQueries = n + 1 := ⟨P.numQueries - 1, by omega⟩
  have hfuel : Nat.log2 f0.size - (P.logBlowup + P.logFinalPolyLen) ≤ f0.size :=
    le_trans (Nat.sub_le _ _) (Nat.log2_le_self _)
  rw [← chain_arities P hP f0.size _ f0 (Transcript.sampleExtState EF t) hg hfuel, hn,
      sampleIndices]
  show List.map (·.logArity)
    (answerSteps (specBackend EF) (List.foldl pushRd ⟨#[], [], #[], #[], #[]⟩ r.1).data
      (List.foldl pushRd ⟨#[], [], #[], #[], #[]⟩ r.1).arities.toList _).toArray.toList = _
  rw [List.toList_toArray, hdata, hari]
  exact answerSteps_logArity r.1 _

end CompStark.Complete
