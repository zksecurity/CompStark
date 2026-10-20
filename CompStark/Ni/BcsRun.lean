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

/-! ### A query's input openings -/

/-- One opened value's term of the batched quotient: `acc + ap (pz - px) q`, and the next power
of `α`. -/
def ptBody (alpha q : EF) (pp : F × EF) (s : EF × EF) : EF × EF :=
  (s.1 * alpha, s.2 + s.1 * (pp.2 - Ext.ofBase pp.1) * q)

/-- The body of `openInput`'s loop over a matrix's opening points. -/
def pointsBody (alpha : EF) (row : Array F) (x : F) (zy : EF × List EF) (s : EF × EF) :
    M H (ForInStep (EF × EF)) := do
  ensure (zy.2.length == row.size) "opened width"
  let s ← forIn (row.toList.zip zy.2) s fun pp s ↦
    pure (ForInStep.yield (ptBody alpha (zy.1 - Ext.ofBase x)⁻¹ pp s))
  pure (ForInStep.yield (s.1, s.2))

/-- The body of `openInput`'s loop over a batch's matrices. -/
def rowsBody (P : Params) (logMax index : Nat) (alpha : EF)
    (x : Array F × Domain × List (EF × List EF)) (ro : List (Nat × EF × EF)) :
    M H (ForInStep (List (Nat × EF × EF))) := do
  let logH := x.2.1.logSize + P.logBlowup
  let xpt := gen * powF (twoAdicGen logH) (reverseBits (index >>> (logMax - logH)) logH)
  let s ← forIn x.2.2 ((ro.lookup logH).getD (1, 0)) (pointsBody H alpha x.1 xpt)
  pure (ForInStep.yield ((logH, s.1, s.2) :: ro.filter (·.1 != logH)))

/-- The body of `openInput`'s loop over the batches. -/
def batchBody (P : Params) (logMax index : Nat) (alpha : EF) (x : BatchOpening × Round)
    (ro : List (Nat × EF × EF)) : M H (ForInStep (List (Nat × EF × EF))) := do
  let heights := x.2.2.map fun (d, _) ↦ 2 ^ (d.logSize + P.logBlowup)
  let reduced := match heights.max? with
    | some h => index >>> (logMax - Nat.log2 h)
    | none => 0
  ensure (← checkOpening H x.2.1 heights reduced (x.1.values.toList.map (·.toList))
    x.1.path.toList) "input opening"
  ensure (x.1.values.size == x.2.2.length) "input rows"
  let ro ← forIn (x.1.values.toList.zip x.2.2) ro (rowsBody H P logMax index alpha)
  match ro.lookup P.logBlowup with
  | some (_, acc) => do
    ensure (acc == 0) "nonzero quotient at the blowup height"
    pure (ForInStep.yield ro)
  | _ => pure (ForInStep.yield ro)

/-- `openInput` with its loop bodies named. -/
theorem openInput_eq (P : Params) (logMax index : Nat) (alpha : EF) (inputs : List BatchOpening)
    (rounds : List Round) :
    openInput H P logMax index alpha inputs rounds = (do
      ensure (inputs.length == rounds.length) "input batches"
      let ro ← forIn (inputs.zip rounds) [] (batchBody H P logMax index alpha)
      pure ((ro.mergeSort fun a b ↦ b.1 ≤ a.1).map fun (h, _, acc) ↦ (h, acc))) := rfl

/-- The opened values of a batch's matrices, each with its point, in `openInput`'s order. -/
def batchTerms (rows : List (Array F × Domain × List (EF × List EF))) : List ((F × EF) × EF) :=
  rows.flatMap fun x ↦ x.2.2.flatMap fun zy ↦ (x.1.toList.zip zy.2).map fun pp ↦ (pp, zy.1)

/-- The batched quotient's running power of `α` and sum over opened values at the point `x`. -/
def accTerms (alpha : EF) (x : F) (terms : List ((F × EF) × EF)) (s : EF × EF) : EF × EF :=
  terms.foldl (fun s t ↦ ptBody alpha (t.2 - Ext.ofBase x)⁻¹ t.1 s) s

theorem pointsLoop_ok (alpha : EF) (row : Array F) (x : F) :
    ∀ (pts : List (EF × List EF)) (s : EF × EF) (st : H.State) (r : (EF × EF) × H.State),
      forIn pts s (pointsBody H alpha row x) st = .ok r →
        (∀ zy ∈ pts, zy.2.length = row.size) ∧
          r = (accTerms alpha x (pts.flatMap fun zy ↦
            (row.toList.zip zy.2).map fun pp ↦ (pp, zy.1)) s, st)
  | [], s, st, r, h => by
    rw [List.forIn_nil] at h
    exact ⟨fun _ h ↦ absurd h List.not_mem_nil, by rw [pure_eq_ok H h]; rfl⟩
  | zy :: pts, s, st, r, h => by
    obtain ⟨step, st', h1, h2⟩ := forIn_cons_eq_ok H _ _ _ _ _ _ h
    unfold pointsBody at h1
    obtain ⟨hw, h1⟩ := ensure_bind_eq_ok H h1
    obtain ⟨s', st'', h3, h4⟩ := bind_eq_ok H h1
    rw [List.forIn_pure_yield_eq_foldl] at h3
    obtain ⟨hs1, hs2⟩ := Prod.mk.inj (pure_eq_ok H h3)
    subst hs1 hs2
    obtain ⟨hs3, hs4⟩ := Prod.mk.inj (pure_eq_ok H h4)
    subst hs3 hs4
    obtain ⟨hl, hr⟩ := pointsLoop_ok alpha row x pts _ _ r h2
    refine ⟨fun zy' hz ↦ ?_, ?_⟩
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact beq_iff_eq.mp hw
      · exact hl zy' hz
    · rw [hr, List.flatMap_cons, accTerms, accTerms, List.foldl_append, List.foldl_map]

/-- `openInput`'s state for a single height `logMax`: the lookup at `logMax` gives `s`, and nothing
else is pending. -/
def RoAt (logMax : Nat) (ro : List (Nat × EF × EF)) (s : EF × EF) : Prop :=
  (ro.lookup logMax).getD (1, 0) = s ∧ ro.filter (·.1 != logMax) = []

theorem rowsLoop_ok (P : Params) (logMax index : Nat) (alpha : EF) :
    ∀ (rows : List (Array F × Domain × List (EF × List EF))) (ro : List (Nat × EF × EF))
      (s : EF × EF) (st : H.State) (r : List (Nat × EF × EF) × H.State),
      (∀ x ∈ rows, x.2.1.logSize + P.logBlowup = logMax) → RoAt logMax ro s →
      forIn rows ro (rowsBody H P logMax index alpha) st = .ok r →
        (∀ x ∈ rows, ∀ zy ∈ x.2.2, zy.2.length = x.1.size) ∧ r.2 = st ∧
          RoAt logMax r.1 (accTerms alpha
            (gen * powF (twoAdicGen logMax) (reverseBits index logMax)) (batchTerms rows) s) ∧
          (rows ≠ [] → r.1 = [(logMax, accTerms alpha
            (gen * powF (twoAdicGen logMax) (reverseBits index logMax)) (batchTerms rows) s)])
  | [], ro, s, st, r, _, hro, h => by
    rw [List.forIn_nil] at h
    rw [pure_eq_ok H h]
    exact ⟨fun _ h ↦ absurd h List.not_mem_nil, rfl, hro, fun h ↦ absurd rfl h⟩
  | x :: rows, ro, s, st, r, hh, hro, h => by
    obtain ⟨step, st', h1, h2⟩ := forIn_cons_eq_ok H _ _ _ _ _ _ h
    have hx := hh x List.mem_cons_self
    unfold rowsBody at h1
    obtain ⟨s', st'', h3, h4⟩ := bind_eq_ok H h1
    simp only [hx, Nat.sub_self, Nat.shiftRight_zero, hro.1] at h3 h4
    obtain ⟨hw, hr3⟩ := pointsLoop_ok H alpha x.1 _ x.2.2 s st _ h3
    obtain ⟨hs1, hs2⟩ := Prod.mk.inj hr3
    subst hs1 hs2
    obtain ⟨hs3, hs4⟩ := Prod.mk.inj (pure_eq_ok H h4)
    subst hs3 hs4
    set A := accTerms alpha (gen * powF (twoAdicGen logMax) (reverseBits index logMax))
      (x.2.2.flatMap fun zy ↦ (x.1.toList.zip zy.2).map fun pp ↦ (pp, zy.1)) s with hA
    have hro' : RoAt logMax ((logMax, A.1, A.2) :: ro.filter (·.1 != logMax)) A := by
      refine ⟨?_, ?_⟩
      · simp only [List.lookup_cons, beq_self_eq_true, Option.getD_some]
      · rw [hro.2]; simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true,
          ↓reduceIte, List.filter_nil]
    obtain ⟨hl, hst, hro'', hne⟩ := rowsLoop_ok P logMax index alpha rows _ _ _ r
      (fun y hy ↦ hh y (List.mem_cons_of_mem _ hy)) hro' h2
    have hterms : accTerms alpha (gen * powF (twoAdicGen logMax) (reverseBits index logMax))
        (batchTerms (x :: rows)) s = accTerms alpha (gen * powF (twoAdicGen logMax)
          (reverseBits index logMax)) (batchTerms rows) A := by
      rw [batchTerms, List.flatMap_cons, accTerms, List.foldl_append]; rfl
    refine ⟨fun y hy ↦ ?_, hst, by rw [hterms]; exact hro'', fun _ ↦ ?_⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact hw
      · exact hl y hy
    · rw [hterms]
      cases rows with
      | nil =>
        dsimp only at h2
        rw [List.forIn_nil] at h2
        rw [pure_eq_ok H h2, hro.2]
        rfl
      | cons y ys => exact hne (List.cons_ne_nil _ _)

theorem verifyBatchH_nil (commit : Digest) (index : Nat) (values : List (List F))
    (path : List Digest) : verifyBatchH H commit [] index values path = false := by
  simp only [verifyBatchH, Merkle.verifyBatch, Merkle.heightGroups, List.length_nil,
    List.range_zero, List.mergeSort_nil, List.foldr_nil]

/-- One batch of a query's input openings passes its checks at `index`: its matrices, all of
height `2 ^ logMax`, open at `index` against the batch's commitment, one row per matrix, and every
opened point has a value per column. -/
def BatchOk (logMax index : Nat) (x : BatchOpening × Round) : Prop :=
  x.2.2 ≠ [] ∧
    verifyBatchH H x.2.1 (List.replicate x.2.2.length (2 ^ logMax)) index
      (x.1.values.toList.map (·.toList)) x.1.path.toList = true ∧
    x.1.values.size = x.2.2.length ∧
    ∀ y ∈ x.1.values.toList.zip x.2.2, ∀ zy ∈ y.2.2, zy.2.length = y.1.size

/-- The opened values of a query's batches, in `openInput`'s order. -/
def inputTerms (xs : List (BatchOpening × Round)) : List ((F × EF) × EF) :=
  xs.flatMap fun x ↦ batchTerms (x.1.values.toList.zip x.2.2)

theorem batchLoop_ok (P : Params) (logMax index : Nat) (alpha : EF)
    (hb : logMax ≠ P.logBlowup) :
    ∀ (xs : List (BatchOpening × Round)) (ro : List (Nat × EF × EF)) (s : EF × EF)
      (st : H.State) (r : List (Nat × EF × EF) × H.State),
      (∀ x ∈ xs, ∀ dp ∈ x.2.2, dp.1.logSize + P.logBlowup = logMax) → RoAt logMax ro s →
      forIn xs ro (batchBody H P logMax index alpha) st = .ok r →
        (∀ x ∈ xs, BatchOk H logMax index x) ∧ r.2 = st ∧
          RoAt logMax r.1 (accTerms alpha
            (gen * powF (twoAdicGen logMax) (reverseBits index logMax)) (inputTerms xs) s) ∧
          (xs ≠ [] → r.1 = [(logMax, accTerms alpha
            (gen * powF (twoAdicGen logMax) (reverseBits index logMax)) (inputTerms xs) s)])
  | [], ro, s, st, r, _, hro, h => by
    rw [List.forIn_nil] at h
    rw [pure_eq_ok H h]
    exact ⟨fun _ h ↦ absurd h List.not_mem_nil, rfl, hro, fun h ↦ absurd rfl h⟩
  | x :: xs, ro, s, st, r, hh, hro, h => by
    obtain ⟨step, st', h1, h2⟩ := forIn_cons_eq_ok H _ _ _ _ _ _ h
    have hx := hh x List.mem_cons_self
    have hheights : (x.2.2.map fun (d, _) ↦ 2 ^ (d.logSize + P.logBlowup)) =
        List.replicate x.2.2.length (2 ^ logMax) := by
      rw [List.eq_replicate_iff, List.length_map]
      refine ⟨rfl, fun b hb ↦ ?_⟩
      obtain ⟨⟨d, q⟩, hdp, rfl⟩ := List.mem_map.mp hb
      have := hx (d, q) hdp
      dsimp only at this ⊢
      rw [this]
    unfold batchBody at h1
    rw [hheights] at h1
    obtain ⟨ok, st1, h3, h1⟩ := bind_eq_ok H h1
    rw [checkOpening_eq] at h3
    obtain ⟨hok, hst1⟩ := Prod.mk.inj (Except.ok.inj h3)
    subst hst1
    obtain ⟨hv, h1⟩ := ensure_bind_eq_ok H h1
    have hne : x.2.2 ≠ [] := by
      intro he
      rw [he, List.length_nil, List.replicate_zero, List.max?_nil] at hok
      rw [← hok, verifyBatchH_nil] at hv
      exact Bool.false_ne_true hv
    rw [List.max?_replicate_of_pos (List.length_pos_of_ne_nil hne)] at hok
    dsimp only at hok
    rw [Nat.log2_two_pow, Nat.sub_self, Nat.shiftRight_zero] at hok
    obtain ⟨hsize, h1⟩ := ensure_bind_eq_ok H h1
    obtain ⟨ro', st2, h4, h5⟩ := bind_eq_ok H h1
    obtain ⟨hw, hst2, hro', hne'⟩ := rowsLoop_ok H P logMax index alpha _ ro s st _
      (fun y hy ↦ hx y.2 (List.of_mem_zip hy).2) hro h4
    simp only at hst2
    subst hst2
    have hvne : x.1.values.toList.zip x.2.2 ≠ [] := by
      intro he
      rw [List.zip_eq_nil_iff] at he
      rcases he with he | he
      · have := beq_iff_eq.mp hsize
        rw [← Array.length_toList, he] at this
        exact hne (List.length_eq_zero_iff.mp this.symm)
      · exact hne he
    have hro1 := hne' hvne
    simp only at hro1
    rw [hro1] at h5
    simp only [List.lookup_cons, show (P.logBlowup == logMax) = false from
      beq_false_of_ne (Ne.symm hb), List.lookup_nil] at h5
    obtain ⟨hs1, hs2⟩ := Prod.mk.inj (pure_eq_ok H h5)
    subst hs1 hs2
    have hterms : inputTerms (x :: xs) =
        batchTerms (x.1.values.toList.zip x.2.2) ++ inputTerms xs := List.flatMap_cons
    obtain ⟨hl, hst, hro'', hne''⟩ := batchLoop_ok P logMax index alpha hb xs _ _ _ r
      (fun y hy ↦ hh y (List.mem_cons_of_mem _ hy)) (by rw [hro1] at hro'; exact hro') h2
    refine ⟨fun y hy ↦ ?_, hst, ?_, fun _ ↦ ?_⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨hne, by rw [hok]; exact hv, beq_iff_eq.mp hsize, hw⟩
      · exact hl y hy
    · rw [hterms, accTerms, List.foldl_append]; exact hro''
    · rw [hterms, accTerms, List.foldl_append]
      cases xs with
      | nil =>
        dsimp only at h2
        rw [List.forIn_nil] at h2
        rw [pure_eq_ok H h2]
        rfl
      | cons y ys => exact hne'' (List.cons_ne_nil _ _)

/-- **An accepting `openInput`** on batches whose matrices all have height `2 ^ logMax`, above the
blowup: every batch passes its checks at `index`, and the result is the single reduced opening at
`logMax`, the batched quotient over all opened values at the query's point. -/
theorem openInput_ok (P : Params) (logMax index : Nat) (alpha : EF) (inputs : List BatchOpening)
    (rounds : List Round) (hb : logMax ≠ P.logBlowup) (hne : rounds ≠ [])
    (hh : ∀ x ∈ rounds, ∀ dp ∈ x.2, dp.1.logSize + P.logBlowup = logMax) (st : H.State)
    (r : List (Nat × EF) × H.State)
    (h : openInput H P logMax index alpha inputs rounds st = .ok r) :
    inputs.length = rounds.length ∧ (∀ x ∈ inputs.zip rounds, BatchOk H logMax index x) ∧
      r = ([(logMax, (accTerms alpha (gen * powF (twoAdicGen logMax) (reverseBits index logMax))
        (inputTerms (inputs.zip rounds)) (1, 0)).2)], st) := by
  rw [openInput_eq] at h
  obtain ⟨hlen, h⟩ := ensure_bind_eq_ok H h
  obtain ⟨ro, st', h1, h2⟩ := bind_eq_ok H h
  have hlen' := beq_iff_eq.mp hlen
  have hzne : inputs.zip rounds ≠ [] := by
    intro he
    rw [List.zip_eq_nil_iff] at he
    rcases he with he | he
    · rw [he, List.length_nil] at hlen'; exact hne (List.length_eq_zero_iff.mp hlen'.symm)
    · exact hne he
  obtain ⟨hok, hst, -, hro⟩ := batchLoop_ok H P logMax index alpha hb _ [] (1, 0) st _
    (fun x hx ↦ hh x.2 (List.of_mem_zip hx).2) ⟨rfl, rfl⟩ h1
  simp only at hst hro
  subst hst
  rw [hro hzne] at h2
  refine ⟨hlen', hok, ?_⟩
  rw [pure_eq_ok H h2, List.mergeSort_singleton]
  rfl

end CompStark.Ni
