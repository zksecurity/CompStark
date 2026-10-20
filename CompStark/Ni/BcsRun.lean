/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Verifier
public import CompStark.Complete.Merkle

/-! # Accepting runs of the verifier on pure primitives

On primitives `H : Primitives Id` the verifier is a deterministic function of the proof. This file
reads an accepting run backwards: each check that passes is a fact about the proof and the values
the challenger returned. The facts are stated without the monad, so that `Ni/Bcs.lean` can turn
them into the consistency of the extracted oracles.

* `bind_eq_ok`, `forIn_cons_eq_ok`: an accepting bind or loop step has accepting parts.
* `foldState`: the running value, index and height of a query's folds; `verifyQuery_ok` reads the
  folds' openings and the result off an accepting `verifyQuery`.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4

variable (H : Primitives Id)

/-! ### The verifier's monad on pure primitives -/

theorem bind_eq_ok {α β : Type} {x : M H α} {f : α → M H β} {s : H.State} {r : β × H.State}
    (h : (x >>= f) s = .ok r) : ∃ a s', x s = .ok (a, s') ∧ f a s' = .ok r := by
  change StateT.bind x f s = _ at h
  simp only [StateT.bind] at h
  revert h
  generalize hx : x s = xs
  intro h
  match xs, h with
  | .ok (a, s'), h => exact ⟨a, s', rfl, h⟩
  | .error e, h => exact absurd h (by intro h'; cases h')

theorem bind_ok_of {α β : Type} {x : M H α} {f : α → M H β} {s s' : H.State} {a : α}
    (h : x s = .ok (a, s')) : (x >>= f) s = f a s' := by
  change StateT.bind x f s = _
  simp only [StateT.bind, h]
  rfl

theorem ensure_eq_ok {b : Bool} {msg : String} {s : H.State} {r : Unit × H.State}
    (h : ensure (H := H) b msg s = .ok r) : b = true ∧ r.2 = s := by
  unfold ensure at h
  cases b with
  | true => exact ⟨rfl, (Except.ok.inj h).symm ▸ rfl⟩
  | false => exact absurd h (by intro h'; cases h')

theorem ensure_bind_eq_ok {β : Type} {b : Bool} {msg : String} {f : Unit → M H β} {s : H.State}
    {r : β × H.State} (h : (ensure (H := H) b msg >>= f) s = .ok r) :
    b = true ∧ f () s = .ok r := by
  obtain ⟨_, s', h1, h2⟩ := bind_eq_ok H h
  obtain ⟨hb, hs⟩ := ensure_eq_ok H h1
  exact ⟨hb, by rw [← show s' = s from hs]; exact h2⟩

theorem pure_eq_ok {α : Type} {a : α} {s : H.State} {r : α × H.State}
    (h : (pure a : M H α) s = .ok r) : r = (a, s) := (Except.ok.inj h).symm

/-- A step of an accepting loop. -/
theorem forIn_cons_eq_ok {α σ : Type} (a : α) (l : List α) (b : σ)
    (body : α → σ → M H (ForInStep σ)) (s : H.State) (r : σ × H.State)
    (h : forIn (a :: l) b body s = .ok r) :
    ∃ step s', body a b s = .ok (step, s') ∧
      match step with
      | .done b' => r = (b', s')
      | .yield b' => forIn l b' body s' = .ok r := by
  rw [List.forIn_cons] at h
  obtain ⟨step, s', h1, h2⟩ := bind_eq_ok H h
  refine ⟨step, s', h1, ?_⟩
  cases step with
  | done b' => exact (pure_eq_ok H h2)
  | yield b' => exact h2

/-- The pure Merkle check of `H`. -/
abbrev verifyBatchH (commit : Digest) (heights : List Nat) (index : Nat) (values : List (List F))
    (path : List Digest) : Bool :=
  Merkle.verifyBatch H.hash H.compress commit heights index values path

theorem checkOpening_eq (commit : Digest) (heights : List Nat) (index : Nat)
    (values : List (List F)) (path : List Digest) (s : H.State) :
    checkOpening H commit heights index values path s =
      .ok (verifyBatchH H commit heights index values path, s) := by
  unfold checkOpening
  rw [show Merkle.verifyBatchM H.hash H.compress commit heights index values path =
    (pure (verifyBatchH H commit heights index values path) : Id Bool) from
    Merkle.verifyBatchM_pure (m := Id) H.hash H.compress _ _ _ _ _]
  rfl

/-! ### A query's folds -/

/-- The group a fold opens: the siblings with the running value `eval` at the index's position. -/
def groupOf (s : CommitStep) (index : Nat) (eval : EF) : List EF :=
  (List.range (2 ^ s.logArity)).map fun j ↦
    if j < index % 2 ^ s.logArity then s.siblings.getD j 0
    else if j = index % 2 ^ s.logArity then eval else s.siblings.getD (j - 1) 0

/-- One fold `x = ((β, commit), step)` of a query in state `(eval, index, logH)`: fold the group
at `β`, shift the index and lower the height by the arity. -/
def foldStep (x : (EF × Digest) × CommitStep) (st : EF × Nat × Nat) : EF × Nat × Nat :=
  let a := x.2.logArity
  (foldRow (st.2.1 >>> a) (st.2.2 - a) a x.1.1 (groupOf x.2 st.2.1 st.1), st.2.1 >>> a,
    st.2.2 - a)

/-- The state of a query before fold `j` of the folds `l`, from the state `st0` before the first. -/
def foldState (l : List ((EF × Digest) × CommitStep)) (st0 : EF × Nat × Nat) (j : Nat) :
    EF × Nat × Nat :=
  (l.take j).foldl (fun st x ↦ foldStep x st) st0

theorem foldState_cons (x : (EF × Digest) × CommitStep) (l : List ((EF × Digest) × CommitStep))
    (st0 : EF × Nat × Nat) (j : Nat) :
    foldState (x :: l) st0 (j + 1) = foldState l (foldStep x st0) j := by
  simp only [foldState, List.take_succ_cons, List.foldl_cons]

theorem foldState_zero (l : List ((EF × Digest) × CommitStep)) (st0 : EF × Nat × Nat) :
    foldState l st0 0 = st0 := by
  simp only [foldState, List.take_zero, List.foldl_nil]

theorem foldState_succ (l : List ((EF × Digest) × CommitStep)) (st0 : EF × Nat × Nat) (j : Nat)
    (hj : j < l.length) : foldState l st0 (j + 1) = foldStep l[j] (foldState l st0 j) := by
  simp only [foldState, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The index and height before fold `j`: the arities before `j` shifted out. -/
theorem foldState_snd (l : List ((EF × Digest) × CommitStep)) :
    ∀ (e : EF) (i h j : Nat), (foldState l (e, i, h) j).2 =
      (i >>> ((l.take j).map (·.2.logArity)).sum, h - ((l.take j).map (·.2.logArity)).sum) := by
  induction l with
  | nil => intro e i h j; simp only [foldState, List.take_nil, List.foldl_nil, List.map_nil,
      List.sum_nil, Nat.shiftRight_zero, Nat.sub_zero]
  | cons x l ih =>
    intro e i h j
    cases j with
    | zero => simp only [foldState_zero, List.take_zero, List.map_nil, List.sum_nil,
        Nat.shiftRight_zero, Nat.sub_zero]
    | succ j =>
      rw [foldState_cons]
      simp only [foldStep]
      rw [ih, List.take_succ_cons, List.map_cons, List.sum_cons, Nat.shiftRight_add,
        Nat.sub_add_eq]

/-- Fold `x` passes its checks in state `st`: the sibling count, and the opening of its group
against its commitment. -/
def StepOk (x : (EF × Digest) × CommitStep) (st : EF × Nat × Nat) : Prop :=
  x.2.siblings.size = 2 ^ x.2.logArity - 1 ∧
    verifyBatchH H x.1.2 [2 ^ (st.2.2 - x.2.logArity)] (st.2.1 >>> x.2.logArity)
      [(groupOf x.2 st.2.1 st.1).flatMap Ext.coeffs] x.2.path.toList = true

/-- The body of `verifyQuery`'s loop. -/
def foldBody (beta : EF) (commit : Digest) (s : CommitStep) (ro : List (Nat × EF)) (eval : EF)
    (index logH : Nat) : M H (ForInStep (List (Nat × EF) × EF × Nat × Nat)) := do
  let arity := 2 ^ s.logArity
  ensure (s.siblings.size == arity - 1) "sibling count"
  let pos := index % arity
  let evals := (List.range arity).map fun j ↦
    if j < pos then s.siblings.getD j 0 else if j = pos then eval else s.siblings.getD (j - 1) 0
  let logFolded := logH - s.logArity
  let index := index >>> s.logArity
  ensure (← checkOpening H commit [2 ^ logFolded] index [evals.flatMap Ext.coeffs]
    s.path.toList) "commit-phase opening"
  let eval := foldRow index logFolded s.logArity beta evals
  match ro with
  | (h, r) :: rest =>
    if h == logFolded then
      pure (ForInStep.yield (rest, eval + Ext.powTwo beta s.logArity * r, index, logFolded))
    else pure (ForInStep.yield (ro, eval, index, logFolded))
  | [] => pure (ForInStep.yield (ro, eval, index, logFolded))

theorem foldBody_ok (beta : EF) (commit : Digest) (s : CommitStep) (eval : EF) (index logH : Nat)
    (st : H.State) (r : ForInStep (List (Nat × EF) × EF × Nat × Nat) × H.State)
    (h : foldBody H beta commit s [] eval index logH st = .ok r) :
    StepOk H ((beta, commit), s) (eval, index, logH) ∧
      r = (.yield ([], foldStep ((beta, commit), s) (eval, index, logH)), st) := by
  unfold foldBody at h
  obtain ⟨h1, h⟩ := ensure_bind_eq_ok H h
  obtain ⟨b, st', h2, h⟩ := bind_eq_ok H h
  rw [checkOpening_eq] at h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h2)
  obtain ⟨h3, h⟩ := ensure_bind_eq_ok H h
  exact ⟨⟨beq_iff_eq.mp h1, h3⟩, pure_eq_ok H h⟩

/-- An accepting fold loop from no pending reduced openings: every fold passes its checks, and the
loop ends in the last state. -/
theorem foldLoop_ok (body : (EF × Digest) × CommitStep → List (Nat × EF) × EF × Nat × Nat →
      M H (ForInStep (List (Nat × EF) × EF × Nat × Nat)))
    (hbody : ∀ beta commit s ro eval index logH,
      body ((beta, commit), s) (ro, eval, index, logH) = foldBody H beta commit s ro eval index logH) :
    ∀ (l : List ((EF × Digest) × CommitStep)) (st0 : EF × Nat × Nat) (st : H.State)
      (r : (List (Nat × EF) × EF × Nat × Nat) × H.State),
      forIn l ([], st0) body st = .ok r →
        (∀ j x, l[j]? = some x → StepOk H x (foldState l st0 j)) ∧
          r = (([], foldState l st0 l.length), st)
  | [], st0, st, r, h => by
    refine ⟨fun j x hx ↦ by simp only [List.getElem?_nil, reduceCtorEq] at hx, ?_⟩
    rw [List.forIn_nil] at h
    rw [pure_eq_ok H h, List.length_nil, foldState_zero]
  | ((beta, commit), s) :: l, (eval, index, logH), st, r, h => by
    obtain ⟨step, st', h1, h2⟩ := forIn_cons_eq_ok H _ _ _ _ _ _ h
    rw [hbody] at h1
    obtain ⟨hok, hr⟩ := foldBody_ok H beta commit s eval index logH st _ h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
    obtain ⟨hl, hr⟩ := foldLoop_ok body hbody l _ _ r h2
    refine ⟨fun j x hx ↦ ?_, by rw [hr, List.length_cons, foldState_cons]⟩
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      rw [← hx, foldState_zero]
      exact hok
    | succ j =>
      rw [List.getElem?_cons_succ] at hx
      rw [foldState_cons]
      exact hl j x hx

/-- **An accepting `verifyQuery`** from one reduced opening at the top height `logMax`: the fold
counts match, every fold passes its checks, the folds end at the final height, and the result is
the last state's value and index. -/
theorem verifyQuery_ok (P : Params) (logMax index : Nat) (betas : List EF) (commits : List Digest)
    (steps : List CommitStep) (e0 : EF) (st : H.State) (r : (EF × Nat) × H.State)
    (h : verifyQuery H P logMax index betas commits steps [(logMax, e0)] st = .ok r) :
    let l := (betas.zip commits).zip steps
    let fin := foldState l (e0, index, logMax) l.length
    betas.length = steps.length ∧ commits.length = steps.length ∧
      (∀ j x, l[j]? = some x → StepOk H x (foldState l (e0, index, logMax) j)) ∧
      fin.2.2 = P.logBlowup + P.logFinalPolyLen ∧ r = ((fin.1, fin.2.1), st) := by
  intro l fin
  unfold verifyQuery at h
  simp only [pure_bind, List.tail_cons] at h
  obtain ⟨-, h1⟩ := ensure_bind_eq_ok H h
  obtain ⟨hlen, h2⟩ := ensure_bind_eq_ok H h1
  obtain ⟨res, st2, hloop, h3⟩ := bind_eq_ok H h2
  obtain ⟨hl, hres⟩ := foldLoop_ok H _ (fun _ _ _ _ _ _ _ ↦ rfl) l _ _ _ hloop
  obtain ⟨hr1, hr2⟩ := Prod.mk.inj hres
  rw [hr1, hr2] at h3
  obtain ⟨hfin, h4⟩ := ensure_bind_eq_ok H h3
  obtain ⟨-, h5⟩ := ensure_bind_eq_ok H h4
  simp only [Bool.and_eq_true, beq_iff_eq] at hlen
  exact ⟨hlen.1, hlen.2, hl, beq_iff_eq.mp hfin, pure_eq_ok H h5⟩

end CompStark.Ni
