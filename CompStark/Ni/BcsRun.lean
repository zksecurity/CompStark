/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Verifier
public import CompStark.Stark.Recompose
public import CompStark.Merkle.Multi
public import CompStark.Fri.Shapes

/-! # Accepting runs of the verifier on pure primitives

On primitives `H : Primitives Id` the verifier is a deterministic function of the proof. This file
reads an accepting run backwards: each check that passes is a fact about the proof and the values
the challenger returned. The facts are stated without the monad, so that `Ni/Bcs.lean` can turn
them into the consistency of the extracted oracles.

* `bind_eq_ok`, `forIn_cons_eq_ok`: an accepting bind or loop step has accepting parts.
* `foldState`: the running value, index and height of a query's folds; `foldQuery_ok` reads them
  off an accepting `foldQuery`, and the commit-phase multi-openings give every fold of every query
  an accepted single opening of its group (`Merkle.verifyBatch_of_verifyMulti`).
* `reduceQuery_ok`, `verifyInputs_ok`: a query's batched quotient, and the input multi-openings,
  which give every query an accepted single opening of its rows.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri

variable {F : Type} (H : Primitives F Id)

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

theorem forIn_unit_state {α : Type} (body : α → PUnit → M H (ForInStep PUnit))
    (f : H.State → α → H.State) (hbody : ∀ a s, body a () s = .ok (.yield (), f s a)) :
    ∀ (l : List α) (s : H.State), forIn l () body s = .ok ((), l.foldl f s)
  | [], _ => rfl
  | a :: l, s => by
    rw [List.forIn_cons, bind_ok_of H (hbody a s)]
    exact forIn_unit_state body f hbody l _

section Folds
variable {EF : Type}

/-- One fold of one query, read off a FRI proof: the arity and the other members of the folded
group. -/
structure QueryFold (EF : Type) where
  logArity : Nat
  siblings : Array EF

/-- The folds of query `q`: each fold's arity and the query's siblings in its opening. -/
def querySteps (q : Nat) (arities : List Nat) (folds : List (CommitOpening F EF)) :
    List (QueryFold EF) :=
  (arities.zip folds).map fun (la, o) ↦ ⟨la, o.siblings.getD q #[]⟩

theorem length_querySteps (q : Nat) (arities : List Nat) (folds : List (CommitOpening F EF))
    (h : folds.length = arities.length) : (querySteps q arities folds).length = arities.length := by
  rw [querySteps, List.length_map, List.length_zip, h, Nat.min_self]

theorem map_logArity_querySteps (q : Nat) (arities : List Nat)
    (folds : List (CommitOpening F EF)) (h : folds.length = arities.length) :
    (querySteps q arities folds).map (·.logArity) = arities := by
  rw [querySteps, List.map_map]
  exact List.map_fst_zip (by omega)

end Folds

section
variable [BaseField F] {EF : Type} [Challenge F EF]

/-- The pure Merkle check of `H`. -/
abbrev verifyBatchH (commit : Digest F) (heights : List Nat) (index : Nat) (values : List (List F))
    (path : List (Digest F)) : Bool :=
  Merkle.verifyBatch H.hash H.compress commit heights index values path

/-- The pure Merkle multi-opening check of `H`. -/
abbrev verifyMultiH (commit : Digest F) (dims : List (Nat × Nat)) (indices : List Nat)
    (rows : List (List (List F))) (sibs : List (Digest F)) : Bool :=
  Merkle.verifyMultiM (m := Id) H.hash H.compress commit dims indices rows sibs

theorem checkMulti_eq (commit : Digest F) (dims : List (Nat × Nat)) (indices : List Nat)
    (rows : List (List (List F))) (sibs : List (Digest F)) (s : H.State) :
    checkMulti H commit dims indices rows sibs s =
      .ok (verifyMultiH H commit dims indices rows sibs, s) := rfl

/-! ### A query's folds -/

/-- The group a fold opens: the siblings with the running value `eval` at the index's position. -/
def groupOf (s : QueryFold EF) (index : Nat) (eval : EF) : List EF :=
  (List.range (2 ^ s.logArity)).map fun j ↦
    if j < index % 2 ^ s.logArity then s.siblings.getD j 0
    else if j = index % 2 ^ s.logArity then eval else s.siblings.getD (j - 1) 0

/-- One fold `x = (β, step)` of a query in state `(eval, index, logH)`: fold the group at `β`,
shift the index and lower the height by the arity. -/
def foldStep (x : EF × QueryFold EF) (st : EF × Nat × Nat) : EF × Nat × Nat :=
  let a := x.2.logArity
  (foldRow (st.2.1 >>> a) (st.2.2 - a) a x.1 (groupOf x.2 st.2.1 st.1), st.2.1 >>> a,
    st.2.2 - a)

/-- The state of a query before fold `j` of the folds `l`, from the state `st0` before the first. -/
def foldState (l : List (EF × QueryFold EF)) (st0 : EF × Nat × Nat) (j : Nat) : EF × Nat × Nat :=
  (l.take j).foldl (fun st x ↦ foldStep x st) st0

theorem foldState_cons (x : EF × QueryFold EF) (l : List (EF × QueryFold EF))
    (st0 : EF × Nat × Nat) (j : Nat) :
    foldState (x :: l) st0 (j + 1) = foldState l (foldStep x st0) j := by
  simp only [foldState, List.take_succ_cons, List.foldl_cons]

theorem foldState_zero (l : List (EF × QueryFold EF)) (st0 : EF × Nat × Nat) :
    foldState l st0 0 = st0 := by
  simp only [foldState, List.take_zero, List.foldl_nil]

theorem foldState_succ (l : List (EF × QueryFold EF)) (st0 : EF × Nat × Nat) (j : Nat)
    (hj : j < l.length) : foldState l st0 (j + 1) = foldStep l[j] (foldState l st0 j) := by
  simp only [foldState, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The index and height before fold `j`: the arities before `j` shifted out. -/
theorem foldState_snd (l : List (EF × QueryFold EF)) :
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

/-- The index and values of the group fold `x` opens in state `st`. -/
def foldGroup (x : EF × QueryFold EF) (st : EF × Nat × Nat) : Nat × List EF :=
  (st.2.1 >>> x.2.logArity, groupOf x.2 st.2.1 st.1)

/-- The groups the folds `l` open from the state `st`. -/
def foldGroups : List (EF × QueryFold EF) → EF × Nat × Nat → List (Nat × List EF)
  | [], _ => []
  | x :: l, st => foldGroup x st :: foldGroups l (foldStep x st)

theorem length_foldGroups : ∀ (l : List (EF × QueryFold EF)) (st : EF × Nat × Nat),
    (foldGroups l st).length = l.length
  | [], _ => rfl
  | x :: l, st => by rw [foldGroups, List.length_cons, length_foldGroups l, List.length_cons]

theorem getElem_foldGroups : ∀ (l : List (EF × QueryFold EF)) (st : EF × Nat × Nat) (j : Nat)
    (hj : j < l.length), (foldGroups l st)[j]'(by rw [length_foldGroups]; exact hj) =
      foldGroup l[j] (foldState l st j)
  | [], _, _, hj => absurd hj (Nat.not_lt_zero _)
  | x :: l, st, 0, _ => by simp only [foldGroups, List.getElem_cons_zero, foldState_zero]
  | x :: l, st, j + 1, hj => by
    simp only [foldGroups, List.getElem_cons_succ, foldState_cons]
    exact getElem_foldGroups l _ j (by simp only [List.length_cons] at hj; omega)

/-- Fold `x` against `commit` passes its checks in state `st`: the sibling count, and an accepted
opening of its group. -/
def StepOk (commit : Digest F) (x : EF × QueryFold EF) (st : EF × Nat × Nat) : Prop :=
  x.2.siblings.size = 2 ^ x.2.logArity - 1 ∧ ∃ path,
    verifyBatchH H commit [2 ^ (st.2.2 - x.2.logArity)] (st.2.1 >>> x.2.logArity)
      [(groupOf x.2 st.2.1 st.1).flatMap Ext.coeffs] path = true

/-- The body of `foldQuery`'s loop. -/
def foldBody {K : Type} [Challenge F K] (q : Nat) (beta : K) (la : Nat) (o : CommitOpening F K)
    (ro : List (Nat × K)) (eval : K) (index logH : Nat) (groups : List (Nat × List K)) :
    M H (ForInStep (List (Nat × K) × K × Nat × Nat × List (Nat × List K))) := do
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

theorem foldBody_ok (q : Nat) (beta : EF) (la : Nat) (o : CommitOpening F EF) (eval : EF)
    (index logH : Nat) (groups : List (Nat × List EF)) (st : H.State)
    (r : ForInStep (List (Nat × EF) × EF × Nat × Nat × List (Nat × List EF)) × H.State)
    (h : foldBody H q beta la o [] eval index logH groups st = .ok r) :
    let x : EF × QueryFold EF := (beta, ⟨la, o.siblings.getD q #[]⟩)
    x.2.siblings.size = 2 ^ la - 1 ∧
      r = (.yield ([], (foldStep x (eval, index, logH)).1, (foldStep x (eval, index, logH)).2.1,
        (foldStep x (eval, index, logH)).2.2, groups ++ [foldGroup x (eval, index, logH)]),
        st) := by
  intro x
  unfold foldBody at h
  obtain ⟨h1, h⟩ := ensure_bind_eq_ok H h
  exact ⟨beq_iff_eq.mp h1, pure_eq_ok H h⟩

/-- An accepting fold loop from no pending reduced openings: every fold's sibling count checks,
the loop ends in the last state, and it adds every fold's group. -/
theorem foldLoop_ok (q : Nat) (body : (EF × Nat) × CommitOpening F EF →
      List (Nat × EF) × EF × Nat × Nat × List (Nat × List EF) →
        M H (ForInStep (List (Nat × EF) × EF × Nat × Nat × List (Nat × List EF))))
    (hbody : ∀ beta la o ro eval index logH groups,
      body ((beta, la), o) (ro, eval, index, logH, groups) =
        foldBody H q beta la o ro eval index logH groups) :
    ∀ (betas : List EF) (arities : List Nat) (folds : List (CommitOpening F EF))
      (st0 : EF × Nat × Nat) (g0 : List (Nat × List EF)) (st : H.State)
      (r : (List (Nat × EF) × EF × Nat × Nat × List (Nat × List EF)) × H.State),
      forIn ((betas.zip arities).zip folds) ([], st0.1, st0.2.1, st0.2.2, g0) body st = .ok r →
        let l := betas.zip (querySteps q arities folds)
        let fin := foldState l st0 l.length
        (∀ (j : Nat) (x : EF × QueryFold EF), l[j]? = some x →
          x.2.siblings.size = 2 ^ x.2.logArity - 1) ∧
          r = (([], fin.1, fin.2.1, fin.2.2, g0 ++ foldGroups l st0), st)
  | [], _, _, st0, g0, st, r, h
  | _ :: _, [], _, st0, g0, st, r, h
  | _ :: _, _ :: _, [], st0, g0, st, r, h => by
    simp only [List.zip_nil_left, List.zip_nil_right, List.zip_cons_cons, List.forIn_nil,
      querySteps, List.map_nil] at h ⊢
    refine ⟨fun j x hx ↦ by simp only [List.getElem?_nil, reduceCtorEq] at hx, ?_⟩
    rw [pure_eq_ok H h]
    simp only [List.length_nil, foldState_zero, foldGroups, List.append_nil]
  | beta :: betas, la :: arities, o :: folds, (eval, index, logH), g0, st, r, h => by
    simp only [List.zip_cons_cons] at h
    obtain ⟨step, st', h1, h2⟩ := forIn_cons_eq_ok H _ _ _ _ _ _ h
    rw [hbody] at h1
    obtain ⟨hok, hr⟩ := foldBody_ok H q beta la o eval index logH g0 st _ h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
    obtain ⟨hl, hr⟩ := foldLoop_ok q body hbody betas arities folds _ _ _ r h2
    have hsteps : querySteps q (la :: arities) (o :: folds) =
        ⟨la, o.siblings.getD q #[]⟩ :: querySteps q arities folds := rfl
    simp only [hsteps, List.zip_cons_cons, List.length_cons, foldState_cons, foldGroups]
    refine ⟨fun j x hx ↦ ?_, by rw [hr, List.append_assoc]; rfl⟩
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      rw [← hx]
      exact hok
    | succ j =>
      rw [List.getElem?_cons_succ] at hx
      exact hl j x hx

/-- **An accepting `foldQuery`** of query `q` from one reduced opening at the top height
`logMax`: every fold's sibling count checks, the folds end at the final height, and the result is
the last state's value and index and the groups the folds open. -/
theorem foldQuery_ok (P : Params) (logMax index q : Nat) (betas : List EF) (arities : List Nat)
    (folds : List (CommitOpening F EF)) (e0 : EF) (st : H.State)
    (r : (EF × Nat × List (Nat × List EF)) × H.State)
    (h : foldQuery H P logMax index q betas arities folds [(logMax, e0)] st = .ok r) :
    let l := betas.zip (querySteps q arities folds)
    let fin := foldState l (e0, index, logMax) l.length
    (∀ (j : Nat) (x : EF × QueryFold EF), l[j]? = some x →
      x.2.siblings.size = 2 ^ x.2.logArity - 1) ∧
      fin.2.2 = P.logBlowup + P.logFinalPolyLen ∧
      r = ((fin.1, fin.2.1, foldGroups l (e0, index, logMax)), st) := by
  intro l fin
  unfold foldQuery at h
  simp only [pure_bind, List.tail_cons] at h
  obtain ⟨-, h1⟩ := ensure_bind_eq_ok H h
  obtain ⟨res, st2, hloop, h3⟩ := bind_eq_ok H h1
  obtain ⟨hl, hres⟩ := foldLoop_ok H q _ (fun _ _ _ _ _ _ _ _ ↦ rfl) betas arities folds
    (e0, index, logMax) [] _ _ hloop
  obtain ⟨hr1, hr2⟩ := Prod.mk.inj hres
  rw [hr1, hr2] at h3
  obtain ⟨hfin, h4⟩ := ensure_bind_eq_ok H h3
  obtain ⟨-, h5⟩ := ensure_bind_eq_ok H h4
  exact ⟨hl, beq_iff_eq.mp hfin, by rw [pure_eq_ok H h5, List.nil_append]⟩

end

section
variable [BaseField F] {EF : Type} [Challenge F EF]

/-! ### A query's batched quotient -/

/-- One opened value's term of the batched quotient: `acc + ap (pz - px) q`, and the next power
of `α`. -/
def ptBody {K : Type} [Challenge F K] (alpha q : K) (pp : F × K) (s : K × K) : K × K :=
  (s.1 * alpha, s.2 + s.1 * (pp.2 - Ext.ofBase pp.1) * q)

/-- The body of `reduceQuery`'s loop over a matrix's opening points. -/
def pointsBody {K : Type} [Challenge F K] (alpha : K) (row : Array F) (x : F) (zy : K × List K)
    (s : K × K) : M H (ForInStep (K × K)) := do
  ensure (zy.2.length == row.size) "opened width"
  ensure (zy.1 - Ext.ofBase x != 0) "opening point is the query point"
  let s ← forIn (row.toList.zip zy.2) s fun pp s ↦
    pure (ForInStep.yield (ptBody alpha (zy.1 - Ext.ofBase x)⁻¹ pp s))
  pure (ForInStep.yield (s.1, s.2))

/-- The body of `reduceQuery`'s loop over a batch's matrices. -/
def rowsBody {K : Type} [Challenge F K] (P : Params) (logMax index : Nat) (alpha : K)
    (x : Array F × Domain F × List (K × List K)) (ro : List (Nat × K × K)) :
    M H (ForInStep (List (Nat × K × K))) := do
  let logH := x.2.1.logSize + P.logBlowup
  let xpt := gen * powF (twoAdicGen logH) (reverseBits (index >>> (logMax - logH)) logH)
  let s ← forIn x.2.2 ((ro.lookup logH).getD (1, 0)) (pointsBody H alpha x.1 xpt)
  pure (ForInStep.yield ((logH, s.1, s.2) :: ro.filter (·.1 != logH)))

/-- The body of `reduceQuery`'s loop over the batches. -/
def batchBody {K : Type} [Challenge F K] (P : Params) (logMax index : Nat) (alpha : K)
    (x : List (Array F) × Round F K) (ro : List (Nat × K × K)) :
    M H (ForInStep (List (Nat × K × K))) := do
  let ro ← forIn (x.1.zip x.2.2) ro (rowsBody H P logMax index alpha)
  pure (ForInStep.yield ro)

/-- The opened values of a batch's matrices, each with its point, in `reduceQuery`'s order. -/
def batchTerms (rows : List (Array F × Domain F × List (EF × List EF))) : List ((F × EF) × EF) :=
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
    obtain ⟨-, h1⟩ := ensure_bind_eq_ok H h1
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

/-- `reduceQuery`'s state for a single height `logMax`: the lookup at `logMax` gives `s`, and
nothing else is pending. -/
def RoAt (logMax : Nat) (ro : List (Nat × EF × EF)) (s : EF × EF) : Prop :=
  (ro.lookup logMax).getD (1, 0) = s ∧ ro.filter (·.1 != logMax) = []

theorem rowsLoop_ok (P : Params) (logMax index : Nat) (alpha : EF) :
    ∀ (rows : List (Array F × Domain F × List (EF × List EF))) (ro : List (Nat × EF × EF))
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

/-- The opened values of a query's batches, in `reduceQuery`'s order. -/
def inputTerms (xs : List (List (Array F) × Round F EF)) : List ((F × EF) × EF) :=
  xs.flatMap fun x ↦ batchTerms (x.1.zip x.2.2)

theorem batchLoop_ok (P : Params) (logMax index : Nat) (alpha : EF)
    (body : List (Array F) × Round F EF → List (Nat × EF × EF) →
      M H (ForInStep (List (Nat × EF × EF))))
    (hbody : ∀ x ro, body x ro = batchBody H P logMax index alpha x ro) :
    ∀ (xs : List (List (Array F) × Round F EF)) (ro : List (Nat × EF × EF)) (s : EF × EF)
      (st : H.State) (r : List (Nat × EF × EF) × H.State),
      (∀ x ∈ xs, ∀ dp ∈ x.2.2, dp.1.logSize + P.logBlowup = logMax) →
      (∀ x ∈ xs, x.1.length = x.2.2.length ∧ x.2.2 ≠ []) → RoAt logMax ro s →
      forIn xs ro body st = .ok r →
        (∀ x ∈ xs, ∀ y ∈ x.1.zip x.2.2, ∀ zy ∈ y.2.2, zy.2.length = y.1.size) ∧ r.2 = st ∧
          RoAt logMax r.1 (accTerms alpha
            (gen * powF (twoAdicGen logMax) (reverseBits index logMax)) (inputTerms xs) s) ∧
          (xs ≠ [] → r.1 = [(logMax, accTerms alpha
            (gen * powF (twoAdicGen logMax) (reverseBits index logMax)) (inputTerms xs) s)])
  | [], ro, s, st, r, _, _, hro, h => by
    rw [List.forIn_nil] at h
    rw [pure_eq_ok H h]
    exact ⟨fun _ h ↦ absurd h List.not_mem_nil, rfl, hro, fun h ↦ absurd rfl h⟩
  | x :: xs, ro, s, st, r, hh, hrows, hro, h => by
    obtain ⟨step, st', h1, h2⟩ := forIn_cons_eq_ok H _ _ _ _ _ _ h
    rw [hbody] at h1
    have hx := hh x List.mem_cons_self
    obtain ⟨hlen, hne⟩ := hrows x List.mem_cons_self
    unfold batchBody at h1
    obtain ⟨ro', st2, h4, h5⟩ := bind_eq_ok H h1
    obtain ⟨hw, hst2, hro', hne'⟩ := rowsLoop_ok H P logMax index alpha _ ro s st _
      (fun y hy ↦ hx y.2 (List.of_mem_zip hy).2) hro h4
    simp only at hst2
    subst hst2
    obtain ⟨hs1, hs2⟩ := Prod.mk.inj (pure_eq_ok H h5)
    subst hs1 hs2
    have hvne : x.1.zip x.2.2 ≠ [] := by
      intro he
      rw [List.zip_eq_nil_iff] at he
      rcases he with he | he
      · rw [he, List.length_nil] at hlen
        exact hne (List.length_eq_zero_iff.mp hlen.symm)
      · exact hne he
    have hterms : inputTerms (x :: xs) =
        batchTerms (x.1.zip x.2.2) ++ inputTerms xs := List.flatMap_cons
    obtain ⟨hl, hst, hro'', hne''⟩ := batchLoop_ok P logMax index alpha body hbody xs _ _ _ r
      (fun y hy ↦ hh y (List.mem_cons_of_mem _ hy))
      (fun y hy ↦ hrows y (List.mem_cons_of_mem _ hy)) hro' h2
    refine ⟨fun y hy ↦ ?_, hst, ?_, fun _ ↦ ?_⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact hw
      · exact hl y hy
    · rw [hterms, accTerms, List.foldl_append]; exact hro''
    · rw [hterms, accTerms, List.foldl_append]
      cases xs with
      | nil =>
        dsimp only at h2
        rw [List.forIn_nil] at h2
        rw [pure_eq_ok H h2, hne' hvne]
        rfl
      | cons y ys => exact hne'' (List.cons_ne_nil _ _)

/-- **An accepting `reduceQuery`** on batches whose matrices all have height `2 ^ logMax`, above
the blowup, with a row per matrix: every opened point has a value per column, and the result is
the single reduced opening at `logMax`, the batched quotient over all opened values at the
query's point. -/
theorem reduceQuery_ok (P : Params) (logMax index : Nat) (alpha : EF) (rows : List (List (Array F)))
    (rounds : List (Round F EF)) (hb : logMax ≠ P.logBlowup) (hne : rows.zip rounds ≠ [])
    (hh : ∀ x ∈ rounds, ∀ dp ∈ x.2, dp.1.logSize + P.logBlowup = logMax)
    (hrows : ∀ x ∈ rows.zip rounds, x.1.length = x.2.2.length ∧ x.2.2 ≠ []) (st : H.State)
    (r : List (Nat × EF) × H.State)
    (h : reduceQuery H P logMax index alpha rows rounds st = .ok r) :
    (∀ x ∈ rows.zip rounds, ∀ y ∈ x.1.zip x.2.2, ∀ zy ∈ y.2.2, zy.2.length = y.1.size) ∧
      r = ([(logMax, (accTerms alpha (gen * powF (twoAdicGen logMax) (reverseBits index logMax))
        (inputTerms (rows.zip rounds)) (1, 0)).2)], st) := by
  unfold reduceQuery at h
  obtain ⟨ro, st', h1, h2⟩ := bind_eq_ok H h
  obtain ⟨hw, hst, -, hro⟩ := batchLoop_ok H P logMax index alpha _ (fun _ _ ↦ rfl) _ [] (1, 0)
    st _ (fun x hx ↦ hh x.2 (List.of_mem_zip hx).2) hrows ⟨rfl, rfl⟩ h1
  simp only at hst hro
  subst hst
  rw [hro hne] at h2
  simp only [List.lookup_cons, show (P.logBlowup == logMax) = false from
    beq_false_of_ne (Ne.symm hb), List.lookup_nil] at h2
  refine ⟨hw, ?_⟩
  rw [pure_eq_ok H h2, List.mergeSort_singleton]
  rfl

/-! ### The input multi-openings -/

/-- One batch of a query's input rows passes its checks at `index`: its matrices, all of height
`2 ^ logMax`, have an accepted opening of the rows at `index` against the batch's commitment, one
row per matrix, and every opened point has a value per column. -/
def BatchOk (logMax index : Nat) (x : List (Array F) × Round F EF) : Prop :=
  x.2.2 ≠ [] ∧
    (∃ path, verifyBatchH H x.2.1 (List.replicate x.2.2.length (2 ^ logMax)) index
      (x.1.map (·.toList)) path = true) ∧
    x.1.length = x.2.2.length ∧
    ∀ y ∈ x.1.zip x.2.2, ∀ zy ∈ y.2.2, zy.2.length = y.1.size

/-- An accepted input multi-opening of batch `x` at `indices`: its matrices, all of height
`2 ^ logMax`, are some, every query opens a row per matrix, and every query's rows have an
accepted single opening. -/
def InputOk (logMax : Nat) (indices : List Nat) (x : MultiOpening F × Round F EF) : Prop :=
  x.2.2 ≠ [] ∧ x.1.values.size = indices.length ∧
    (∀ v ∈ x.1.values, v.size = x.2.2.length) ∧
    ∀ j (hj : j < indices.length), ∃ path, verifyBatchH H x.2.1
      (List.replicate x.2.2.length (2 ^ logMax)) indices[j]
        ((x.1.values.getD j #[]).toList.map (·.toList)) path = true

/-- The body of `verifyInputs`'s loop. -/
def inputBody (P : Params) (logMax : Nat) (indices : List Nat) (x : MultiOpening F × Round F EF)
    (_ : PUnit) : M H (ForInStep PUnit) := do
  ensure (x.1.values.size == indices.length) "input queries"
  ensure (x.1.values.all (·.size == x.2.2.length)) "input rows"
  ensure (x.2.2.all (!·.2.isEmpty)) "matrix without opening points"
  let dims := x.2.2.map fun (d, pts) ↦
    (2 ^ (d.logSize + P.logBlowup), (pts.headD default).2.length)
  let logBatch := (x.2.2.map (·.1.logSize + P.logBlowup)).foldl max 0
  ensure (← checkMulti H x.2.1 dims (indices.map (· >>> (logMax - logBatch)))
    (x.1.values.toList.map fun r ↦ r.toList.map (·.toList)) x.1.siblings.toList) "input opening"
  pure (ForInStep.yield PUnit.unit)

theorem inputBody_ok (P : Params) (logMax : Nat) (indices : List Nat)
    (x : MultiOpening F × Round F EF) (hh : ∀ dp ∈ x.2.2, dp.1.logSize + P.logBlowup = logMax)
    (st : H.State) (r : ForInStep PUnit × H.State)
    (h : inputBody H P logMax indices x () st = .ok r) :
    InputOk H logMax indices x ∧ r = (.yield (), st) := by
  unfold inputBody at h
  obtain ⟨hq, h⟩ := ensure_bind_eq_ok H h
  obtain ⟨hrows, h⟩ := ensure_bind_eq_ok H h
  obtain ⟨-, h⟩ := ensure_bind_eq_ok H h
  rw [bind_ok_of H (checkMulti_eq H _ _ _ _ _ st)] at h
  obtain ⟨hv, h⟩ := ensure_bind_eq_ok H h
  have hdims : (x.2.2.map fun (dp : Domain F × List (EF × List EF)) ↦
      (2 ^ (dp.1.logSize + P.logBlowup), (dp.2.headD default).2.length)).map (·.1) =
      List.replicate x.2.2.length (2 ^ logMax) := by
    rw [List.eq_replicate_iff, List.length_map, List.length_map]
    refine ⟨rfl, fun b hb ↦ ?_⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    obtain ⟨dp, hdp, rfl⟩ := List.mem_map.mp hy
    rw [hh dp hdp]
  have hne : x.2.2 ≠ [] := by
    intro he
    simp only [he, List.map_nil, verifyMultiH, Merkle.verifyMultiM, Merkle.heightGroups,
      List.length_nil, List.range_zero, List.mergeSort_nil, List.foldr_nil] at hv
    exact Bool.false_ne_true hv
  have hbatch : (x.2.2.map (·.1.logSize + P.logBlowup)).foldl max 0 = logMax :=
    foldl_max_const logMax _ 0 (fun z hz ↦ by
      obtain ⟨dp, hdp, rfl⟩ := List.mem_map.mp hz; exact hh dp hdp)
      (by simpa only [ne_eq, List.map_eq_nil_iff] using hne) (Nat.zero_le _)
  rw [hbatch, Nat.sub_self] at hv
  simp only [Nat.shiftRight_zero, List.map_id'] at hv
  refine ⟨⟨hne, beq_iff_eq.mp hq, fun v hv' ↦ ?_, fun j hj ↦ ?_⟩, pure_eq_ok H h⟩
  · rw [Array.all_eq_true_iff_forall_mem] at hrows
    exact beq_iff_eq.mp (hrows v hv')
  · obtain ⟨path, hp⟩ := Merkle.verifyBatch_of_verifyMulti H.hash H.compress x.2.1 _ logMax
      (List.length_pos_of_ne_nil hne) _ hdims _ _ _ hv j hj
    refine ⟨path, ?_⟩
    rw [← hp]
    congr 1
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getD_eq_getD_getElem?,
      ← Array.getElem?_toList]
    cases x.1.values.toList[j]? <;> rfl

/-- **An accepting `verifyInputs`** on batches whose matrices all have height `2 ^ logMax`: a
multi-opening per batch, each accepted. -/
theorem verifyInputs_ok (P : Params) (logMax : Nat) (indices : List Nat)
    (inputs : List (MultiOpening F)) (rounds : List (Round F EF))
    (hh : ∀ x ∈ rounds, ∀ dp ∈ x.2, dp.1.logSize + P.logBlowup = logMax) (st : H.State)
    (r : Unit × H.State) (h : verifyInputs H P logMax indices inputs rounds st = .ok r) :
    inputs.length = rounds.length ∧ (∀ x ∈ inputs.zip rounds, InputOk H logMax indices x) ∧
      r = ((), st) := by
  unfold verifyInputs at h
  obtain ⟨hlen, h⟩ := ensure_bind_eq_ok H h
  obtain ⟨u, st', h1, h2⟩ := bind_eq_ok H h
  have hloop : ∀ (xs : List (MultiOpening F × Round F EF)) (st : H.State) (r : PUnit × H.State),
      (∀ x ∈ xs, ∀ dp ∈ x.2.2, dp.1.logSize + P.logBlowup = logMax) →
      forIn xs PUnit.unit (fun x _ ↦ inputBody H P logMax indices x ()) st = .ok r →
        (∀ x ∈ xs, InputOk H logMax indices x) ∧ r = ((), st) := by
    intro xs
    induction xs with
    | nil => intro st r _ h; rw [List.forIn_nil] at h; exact ⟨nofun, pure_eq_ok H h⟩
    | cons x xs ih =>
      intro st r hh h
      obtain ⟨step, st', h1, h2⟩ := forIn_cons_eq_ok H _ _ _ _ _ _ h
      obtain ⟨hok, hr⟩ := inputBody_ok H P logMax indices x (hh x List.mem_cons_self) st _ h1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
      obtain ⟨hl, hr⟩ := ih _ r (fun y hy ↦ hh y (List.mem_cons_of_mem _ hy)) h2
      exact ⟨fun y hy ↦ (List.mem_cons.mp hy).elim (fun e ↦ e ▸ hok) (hl y), hr⟩
  obtain ⟨hok, hr⟩ := hloop _ st _ (fun x hx ↦ hh x.2 (List.of_mem_zip hx).2) h1
  obtain ⟨-, rfl⟩ := Prod.mk.inj hr
  exact ⟨beq_iff_eq.mp hlen, hok, pure_eq_ok H h2⟩

end
/-! ### The challenger on pure primitives -/

/-- Observe a list of elements. -/
def obsList (s : H.State) (xs : List F) : H.State := xs.foldl H.observe s

/-- Sample `n` elements. -/
def smpList (s : H.State) : Nat → List F × H.State
  | 0 => ([], s)
  | n + 1 =>
    let a := H.sample s
    let r := smpList a.2 n
    (a.1 :: r.1, r.2)

theorem observe_eq (x : F) (s : H.State) : observe H x s = .ok ((), H.observe s x) := rfl

theorem observeList_eq (xs : List F) (s : H.State) :
    observeList H xs s = .ok ((), obsList H s xs) := rfl

theorem sample_eq (s : H.State) : sample H s = .ok (H.sample s) := rfl

theorem sampleList_eq : ∀ (n : Nat) (s : H.State), sampleList H n s = .ok (smpList H s n)
  | 0, _ => rfl
  | n + 1, s => by
    unfold sampleList
    rw [bind_ok_of H (sample_eq H s), bind_ok_of H (sampleList_eq n _)]
    rfl

/-- The challenger's states as it samples one element after another from `s`. -/
def sampleStates (s : H.State) : Nat → H.State
  | 0 => s
  | j + 1 => (H.sample (sampleStates s j)).2

theorem sampleStates_sample (s : H.State) :
    ∀ k, sampleStates H (H.sample s).2 k = sampleStates H s (k + 1)
  | 0 => rfl
  | k + 1 => by simp only [sampleStates, sampleStates_sample s k]

/-- An accepting `mapM` whose steps keep the state: every step accepts from the first state. -/
theorem mapM_eq_ok {α β : Type} (f : α → M H β) :
    ∀ (l : List α) (s : H.State) (r : List β × H.State),
      (∀ a ∈ l, ∀ s r, f a s = .ok r → r.2 = s) → l.mapM f s = .ok r →
        r.2 = s ∧ r.1.length = l.length ∧
          ∀ k (hk : k < l.length) (hk' : k < r.1.length), f l[k] s = .ok (r.1[k], s)
  | [], s, r, _, h => by
    rw [List.mapM_nil] at h
    rw [pure_eq_ok H h]
    exact ⟨rfl, rfl, fun k hk ↦ absurd hk (Nat.not_lt_zero _)⟩
  | a :: l, s, r, hf, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, s1, h1, hk⟩ := bind_eq_ok H h
    have hs1 := hf a List.mem_cons_self s _ h1
    simp only at hs1
    subst hs1
    obtain ⟨bs, s2, h2, h3⟩ := bind_eq_ok H hk
    obtain ⟨hs2, hlen, hks⟩ := mapM_eq_ok f l s1 _ (fun a' ha' ↦ hf a' (List.mem_cons_of_mem _ ha'))
      h2
    simp only at hs2
    subst hs2
    rw [pure_eq_ok H h3]
    refine ⟨rfl, by rw [List.length_cons, List.length_cons, hlen], fun k hk hk' ↦ ?_⟩
    cases k with
    | zero => exact h1
    | succ k =>
      exact hks k (Nat.lt_of_succ_lt_succ hk) (Nat.lt_of_succ_lt_succ hk')

variable [BaseField F] {EF : Type} [Challenge F EF]

/-- Observe extension elements, lowest coefficient first. -/
def obsExts (s : H.State) (xs : List EF) : H.State :=
  xs.foldl (fun s x ↦ (Ext.coeffs x).foldl H.observe s) s

/-- Sample an extension element, lowest coefficient first. -/
def smpExt (s : H.State) : EF × H.State :=
  let r := smpList H s (Challenge.d EF)
  (Challenge.ofCoeffs r.1, r.2)

/-- Sample the low `bits` bits of an element's canonical value. -/
def smpBits (bits : Nat) (s : H.State) : Nat × H.State :=
  (CompPoly.CanonicalNat.toNat (H.sample s).1 % 2 ^ bits, (H.sample s).2)

/-- Check a grinding witness: observe it and sample `bits` bits, which must vanish. -/
def chkWit (bits : Nat) (w : F) (s : H.State) : Bool × H.State :=
  if bits = 0 then (true, s) else
    let r := smpBits H bits (H.observe s w)
    (r.1 == 0, r.2)

theorem observeExts_eq (xs : List EF) (s : H.State) :
    observeExts H xs s = .ok ((), obsExts H s xs) := rfl

theorem sampleExt_eq (s : H.State) : (sampleExt H : M H EF) s = .ok (smpExt H s) := by
  unfold sampleExt
  rw [bind_ok_of H (sampleList_eq H _ s)]
  rfl

theorem sampleBits_eq (bits : Nat) (s : H.State) :
    sampleBits H bits s = .ok (smpBits H bits s) := by
  unfold sampleBits
  rw [bind_ok_of H (sample_eq H s)]
  rfl

theorem checkWitness_eq (bits : Nat) (w : F) (s : H.State) :
    checkWitness H bits w s = .ok (chkWit H bits w s) := by
  unfold checkWitness chkWit
  by_cases hb : bits = 0
  · simp only [hb, ↓reduceIte]; rfl
  · simp only [hb, ↓reduceIte]
    rw [bind_ok_of H (observe_eq H w s), bind_ok_of H (sampleBits_eq H bits _)]
    rfl

/-! ### FRI's verifier -/

/-- The body of `verifyFri`'s loop over the commitments. -/
def commitBody (P : Params) (cw : Digest F × F) (betas : Array EF) :
    M H (ForInStep (Array EF)) := do
  observeList H cw.1.toList
  ensure (← checkWitness H P.commitPowBits cw.2) "commit witness"
  pure (ForInStep.yield (betas.push (← sampleExt H)))

/-- The folding challenges the commit loop samples, and the challenger after it. -/
def commitReplay (P : Params) : List (Digest F × F) → H.State → List EF × H.State
  | [], s => ([], s)
  | cw :: cws, s =>
    let b := smpExt H (chkWit H P.commitPowBits cw.2 (obsList H s cw.1.toList)).2
    let r := commitReplay P cws b.2
    (b.1 :: r.1, r.2)

theorem length_commitReplay (P : Params) :
    ∀ (cws : List (Digest F × F)) (s : H.State), (commitReplay (EF := EF) H P cws s).1.length =
      cws.length
  | [], _ => rfl
  | cw :: cws, s => by
    simp only [commitReplay, List.length_cons, length_commitReplay P cws]

theorem commitLoop_ok (P : Params) (body : Digest F × F → Array EF → M H (ForInStep (Array EF)))
    (hbody : ∀ cw betas, body cw betas = commitBody H P cw betas) :
    ∀ (cws : List (Digest F × F)) (betas : Array EF) (s : H.State) (r : Array EF × H.State),
      forIn cws betas body s = .ok r →
        r.1.toList = betas.toList ++ (commitReplay H P cws s).1 ∧
          r.2 = (commitReplay (EF := EF) H P cws s).2
  | [], betas, s, r, h => by
    rw [List.forIn_nil] at h
    rw [pure_eq_ok H h]
    simp only [commitReplay, List.append_nil, and_self]
  | cw :: cws, betas, s, r, h => by
    obtain ⟨step, st', h1, h2⟩ := forIn_cons_eq_ok H _ _ _ _ _ _ h
    rw [hbody] at h1
    unfold commitBody at h1
    rw [bind_ok_of H (observeList_eq H _ s), bind_ok_of H (checkWitness_eq H _ _ _)] at h1
    obtain ⟨-, h1⟩ := ensure_bind_eq_ok H h1
    rw [bind_ok_of H (sampleExt_eq H _)] at h1
    obtain ⟨hs1, hs2⟩ := Prod.mk.inj (pure_eq_ok H h1)
    subst hs1 hs2
    obtain ⟨hr1, hr2⟩ := commitLoop_ok P body hbody cws _ _ r h2
    refine ⟨?_, hr2⟩
    rw [hr1, Array.toList_push, List.append_assoc]
    rfl

/-- The query indices: one sample's low bits each. -/
theorem indices_eq (bits : Nat) :
    ∀ {α : Type} (l : List α) (s : H.State), l.mapM (fun _ ↦ sampleBits H bits) s =
      .ok ((List.range l.length).map fun j ↦ (smpBits H bits (sampleStates H s j)).1,
        sampleStates H s l.length)
  | _, [], _ => rfl
  | _, a :: l, s => by
    rw [List.mapM_cons, bind_ok_of H (sampleBits_eq H bits s),
      bind_ok_of H (indices_eq bits l _)]
    simp only [smpBits, sampleStates_sample, List.length_cons, List.range_succ_eq_map,
      List.map_cons, List.map_map]
    rfl

/-- The body of `verifyFri`'s loop over the queries. -/
def queryBody (P : Params) (logMax : Nat) (alpha : EF) (rounds : List (Round F EF))
    (betas : List EF) (arities : List Nat) (folds : List (CommitOpening F EF))
    (inputs : List (MultiOpening F)) (finalPoly : Array EF) (x : Nat × Nat) :
    M H (List (Nat × List EF)) := do
  let ro ← reduceQuery H P logMax x.1 alpha (inputs.map fun b ↦ (b.values.getD x.2 #[]).toList)
    rounds
  let (eval, index, gs) ← foldQuery H P logMax x.1 x.2 betas arities folds ro
  let xpt := Ext.ofBase (powF (twoAdicGen logMax) (reverseBits index logMax))
  let expected := finalPoly.foldr (fun c acc ↦ acc * xpt + c) 0
  ensure (expected == eval) "final polynomial mismatch"
  return gs

/-- The batched quotient of query `q` at `index`. -/
def queryValue (logMax : Nat) (alpha : EF) (rounds : List (Round F EF))
    (inputs : List (MultiOpening F)) (q index : Nat) : EF :=
  (accTerms alpha (gen * powF (twoAdicGen logMax) (reverseBits index logMax))
    (inputTerms ((inputs.map fun b ↦ (b.values.getD q #[]).toList).zip rounds)) (1, 0)).2

/-- Query `q` at `index` passes the verifier's checks: its input rows open at `index`, its folds
from the batched quotient pass, end at the final height, and match the final polynomial. -/
def QueryOk (P : Params) (logMax : Nat) (alpha : EF) (rounds : List (Round F EF))
    (betas : List EF) (commits : List (Digest F)) (arities : List Nat)
    (folds : List (CommitOpening F EF)) (inputs : List (MultiOpening F)) (finalPoly : Array EF)
    (q index : Nat) : Prop :=
  let rows := inputs.map fun b ↦ (b.values.getD q #[]).toList
  let e0 := queryValue logMax alpha rounds inputs q index
  let l := betas.zip (querySteps q arities folds)
  let fin := foldState l (e0, index, logMax) l.length
  rows.length = rounds.length ∧ (∀ x ∈ rows.zip rounds, BatchOk H logMax index x) ∧
    (∀ (j : Nat) (x : EF × QueryFold EF), l[j]? = some x →
      StepOk H (commits.getD j 0) x (foldState l (e0, index, logMax) j)) ∧
    fin.2.2 = P.logBlowup + P.logFinalPolyLen ∧
    finalPoly.foldr (fun c acc ↦
      acc * Ext.ofBase (powF (twoAdicGen logMax) (reverseBits fin.2.1 logMax)) + c) 0 = fin.1


theorem queryBody_ok (P : Params) (logMax : Nat) (alpha : EF) (rounds : List (Round F EF))
    (betas : List EF) (arities : List Nat) (folds : List (CommitOpening F EF))
    (inputs : List (MultiOpening F)) (finalPoly : Array EF) (x : Nat × Nat)
    (hb : logMax ≠ P.logBlowup)
    (hne : (inputs.map fun b ↦ (b.values.getD x.2 #[]).toList).zip rounds ≠ [])
    (hh : ∀ y ∈ rounds, ∀ dp ∈ y.2, dp.1.logSize + P.logBlowup = logMax)
    (hrows : ∀ y ∈ (inputs.map fun b ↦ (b.values.getD x.2 #[]).toList).zip rounds,
      y.1.length = y.2.2.length ∧ y.2.2 ≠ [])
    (st : H.State) (r : List (Nat × List EF) × H.State)
    (h : queryBody H P logMax alpha rounds betas arities folds inputs finalPoly x st = .ok r) :
    let rows := inputs.map fun b ↦ (b.values.getD x.2 #[]).toList
    let e0 := queryValue logMax alpha rounds inputs x.2 x.1
    let l := betas.zip (querySteps x.2 arities folds)
    let fin := foldState l (e0, x.1, logMax) l.length
    (∀ y ∈ rows.zip rounds, ∀ z ∈ y.1.zip y.2.2, ∀ zy ∈ z.2.2, zy.2.length = z.1.size) ∧
      (∀ (j : Nat) (y : EF × QueryFold EF), l[j]? = some y →
        y.2.siblings.size = 2 ^ y.2.logArity - 1) ∧
      fin.2.2 = P.logBlowup + P.logFinalPolyLen ∧
      finalPoly.foldr (fun c acc ↦
        acc * Ext.ofBase (powF (twoAdicGen logMax) (reverseBits fin.2.1 logMax)) + c) 0 = fin.1 ∧
      r = (foldGroups l (e0, x.1, logMax), st) := by
  intro rows e0 l fin
  unfold queryBody at h
  obtain ⟨ro, st1, h1, hk1⟩ := bind_eq_ok H h
  obtain ⟨hw, hro⟩ := reduceQuery_ok H P logMax x.1 alpha _ rounds hb hne hh hrows st _ h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hro
  obtain ⟨res, st2, h2, hk2⟩ := bind_eq_ok H hk1
  obtain ⟨hsib, hfin, hres⟩ := foldQuery_ok H P logMax x.1 x.2 betas arities folds _ _ _ h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hres
  obtain ⟨hfp, hk3⟩ := ensure_bind_eq_ok H hk2
  exact ⟨hw, hsib, hfin, beq_iff_eq.mp hfp, pure_eq_ok H hk3⟩

/-- The body of `verifyFri`'s loop over the commit-phase multi-openings. -/
def phaseBody (groups : List (List (Nat × List EF)))
    (x : (Digest F × CommitOpening F EF) × Nat × Nat) (logH : Nat) : M H (ForInStep Nat) := do
  let logFolded := logH - x.2.1
  let gs := groups.map fun g ↦ g.getD x.2.2 (0, [])
  ensure (← checkMulti H x.1.1 [(2 ^ logFolded, Challenge.d EF * 2 ^ x.2.1)] (gs.map (·.1))
    (gs.map fun (_, evals) ↦ [evals.flatMap Ext.coeffs]) x.1.2.path.toList)
    "commit-phase opening"
  pure (ForInStep.yield logFolded)

/-- An accepting loop over the commit-phase multi-openings: each round's multi-opening of the
queries' groups is accepted, at the height the earlier rounds folded down to. -/
theorem phaseLoop_ok (groups : List (List (Nat × List EF)))
    (body : (Digest F × CommitOpening F EF) × Nat × Nat → Nat → M H (ForInStep Nat))
    (hbody : ∀ x logH, body x logH = phaseBody H groups x logH) :
    ∀ (xs : List ((Digest F × CommitOpening F EF) × Nat × Nat)) (logH : Nat) (st : H.State)
      (r : Nat × H.State), forIn xs logH body st = .ok r →
      ∀ k (hk : k < xs.length),
        let lh := logH - ((xs.take k).map (·.2.1)).sum
        let gs := groups.map fun g ↦ g.getD xs[k].2.2 (0, [])
        verifyMultiH H xs[k].1.1 [(2 ^ (lh - xs[k].2.1), Challenge.d EF * 2 ^ xs[k].2.1)]
          (gs.map (·.1)) (gs.map fun (_, evals) ↦ [evals.flatMap Ext.coeffs])
          xs[k].1.2.path.toList = true
  | [], _, _, _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | x :: xs, logH, st, r, h, k, hk => by
    obtain ⟨step, st', h1, h2⟩ := forIn_cons_eq_ok H _ _ _ _ _ _ h
    rw [hbody] at h1
    unfold phaseBody at h1
    rw [bind_ok_of H (checkMulti_eq H _ _ _ _ _ st)] at h1
    obtain ⟨hv, h1⟩ := ensure_bind_eq_ok H h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pure_eq_ok H h1)
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero, List.take_zero, List.map_nil, List.sum_nil,
        Nat.sub_zero]
      exact hv
    | succ k =>
      have := phaseLoop_ok groups body hbody xs _ _ r h2 k
        (by simp only [List.length_cons] at hk; omega)
      simp only [List.getElem_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons]
      rw [Nat.sub_add_eq]
      exact this


/-- **An accepting FRI verifier**, after the batching challenge `alpha`, on batches whose
matrices all have height `2 ^ logMax`, above the blowup: the proof has Plonky3's shape for the
fold schedule, the query grinding witness checks, and every query passes its checks at the index
it samples. The challenges are those the challenger returns after the domain separator: the
folding challenges of the commit loop (`commitReplay`), and the query indices after the grinding
check (`sampleStates`). -/
theorem verifyFri_ok (P : Params) (proof : FriProof F EF) (rounds : List (Round F EF))
    (alpha : EF) (logMax : Nat) (hb : logMax ≠ P.logBlowup)
    (hh : ∀ x ∈ rounds, ∀ dp ∈ x.2, dp.1.logSize + P.logBlowup = logMax)
    (s : H.State) (r : Unit × H.State) (h : verifyFri H P proof rounds alpha s = .ok r) :
    let ar := foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen) logMax [logMax]
    let cr := commitReplay H P (proof.commits.toList.zip proof.commitWitnesses.toList)
      (obsList H s (DomainSeparator.friSeed F EF ar (2 ^ P.logFinalPolyLen) P.commitPowBits
        P.queryPowBits P.numQueries logMax P.logBlowup P.maxLogArity))
    let w := chkWit H P.queryPowBits proof.queryWitness (obsExts H cr.2 proof.finalPoly.toList)
    0 < P.maxLogArity ∧ proof.folds.size = ar.length ∧ proof.commits.size = ar.length ∧
      proof.commitWitnesses.size = ar.length ∧ proof.finalPoly.size = 2 ^ P.logFinalPolyLen ∧
      w.1 = true ∧ cr.1.length = ar.length ∧
      ∀ j < P.numQueries, QueryOk H P logMax alpha rounds cr.1 proof.commits.toList ar
        proof.folds.toList proof.inputs.toList proof.finalPoly j
        (smpBits H logMax (sampleStates H w.2 j)).1 := by
  intro ar cr w
  unfold verifyFri at h
  obtain ⟨hpar, h⟩ := ensure_bind_eq_ok H h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpar
  obtain ⟨hany, h⟩ := ensure_bind_eq_ok H h
  have hheights : (((rounds.flatMap (·.2)).map (·.1.logSize + P.logBlowup)).mergeSort
      (fun a b ↦ b ≤ a)).dedup = [logMax] := by
    refine dedup_mergeSort_const _ _ _ (fun x hx ↦ ?_) ?_
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨r, hr, hy⟩ := List.mem_flatMap.mp hy
      exact hh r hr y hy
    · simp only [List.any_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        List.isEmpty_eq_false_iff] at hany
      obtain ⟨r, hr, hne⟩ := hany
      obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hne
      exact List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_flatMap.mpr ⟨r, hr, hy⟩))
  have hrne : rounds ≠ [] := by
    rintro rfl
    simp only [List.any_nil, Bool.false_eq_true] at hany
  simp only [hheights, List.headD_cons] at h
  obtain ⟨-, h⟩ := ensure_bind_eq_ok H h
  obtain ⟨hfolds, h⟩ := ensure_bind_eq_ok H h
  obtain ⟨-, h⟩ := ensure_bind_eq_ok H h
  obtain ⟨-, h⟩ := ensure_bind_eq_ok H h
  obtain ⟨-, h⟩ := ensure_bind_eq_ok H h
  obtain ⟨hfp, h⟩ := ensure_bind_eq_ok H h
  rw [bind_ok_of H (observeList_eq H _ s)] at h
  obtain ⟨hcs, h⟩ := ensure_bind_eq_ok H h
  simp only [Bool.and_eq_true, beq_iff_eq] at hcs
  obtain ⟨betas, st1, h1, h⟩ := bind_eq_ok H h
  obtain ⟨hb1, hb2⟩ := commitLoop_ok H P _ (fun _ _ ↦ rfl) _ _ _ _ h1
  simp only at hb2
  subst hb2
  have hbetas : betas.toList = cr.1 := by rw [hb1]; rfl
  rw [bind_ok_of H (observeExts_eq H _ _),
    bind_ok_of H (a := w.1) (s' := w.2) (checkWitness_eq H _ _ _)] at h
  obtain ⟨hw, h⟩ := ensure_bind_eq_ok H h
  set N := P.numQueries
  set idx : List Nat := (List.range N).map fun j ↦ (smpBits H logMax (sampleStates H w.2 j)).1
    with hidx
  obtain ⟨indices, st2, h2, h⟩ := bind_eq_ok H h
  rw [indices_eq, List.length_range] at h2
  obtain ⟨hi1, hi2⟩ : idx = indices ∧ sampleStates H w.2 N = st2 :=
    Prod.mk.inj (Except.ok.inj h2)
  subst hi1 hi2
  obtain ⟨u, st3, h3, h⟩ := bind_eq_ok H h
  obtain ⟨hinlen, hinok, hr3⟩ := verifyInputs_ok H P logMax _ _ rounds hh _ _ h3
  obtain ⟨-, rfl⟩ := Prod.mk.inj hr3
  have hidxlen : idx.length = N := by rw [hidx, List.length_map, List.length_range]
  -- every query's rows: one per matrix of every batch
  have hrowsq : ∀ q < N, ∀ y ∈ (proof.inputs.toList.map fun b ↦ (b.values.getD q #[]).toList).zip
      rounds, y.1.length = y.2.2.length ∧ y.2.2 ≠ [] := by
    intro q hq y hy
    rw [List.zip_map_left] at hy
    obtain ⟨⟨b, rd⟩, hbr, rfl⟩ := List.mem_map.mp hy
    obtain ⟨hne, hsz, hall, -⟩ := hinok _ hbr
    refine ⟨?_, hne⟩
    simp only [Prod.map, id, Array.length_toList]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hsz, hidxlen]; exact hq),
      Option.getD_some]
    exact hall _ (Array.getElem_mem _)
  have hzne : ∀ q, (proof.inputs.toList.map fun b ↦ (b.values.getD q #[]).toList).zip rounds ≠
      [] := by
    intro q he
    rw [List.zip_eq_nil_iff, List.map_eq_nil_iff] at he
    rcases he with he | he
    · rw [he, List.length_nil] at hinlen
      exact hrne (List.length_eq_zero_iff.mp hinlen.symm)
    · exact hrne he
  obtain ⟨groups, st4, h4, h⟩ := bind_eq_ok H h
  obtain ⟨hst4, hglen, hg⟩ := mapM_eq_ok H (fun x ↦ queryBody H P logMax alpha rounds
    betas.toList ar proof.folds.toList proof.inputs.toList proof.finalPoly x) idx.zipIdx _ _
    (fun x hx s r hr ↦ by
      have hq : x.2 < N := by
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
        rw [List.getElem_zipIdx, Nat.zero_add]
        rw [List.length_zipIdx, hidxlen] at hk
        exact hk
      exact congrArg Prod.snd ((queryBody_ok H P logMax alpha rounds _ ar _ _ _ x hb (hzne _) hh
        (hrowsq _ hq) s r hr).2.2.2.2)) h4
  simp only at hst4
  subst hst4
  rw [List.length_zipIdx] at hglen
  obtain ⟨lh, st5, h5, h6⟩ := bind_eq_ok H h
  have hphase := phaseLoop_ok H groups _ (fun _ _ ↦ rfl) _ _ _ _ h5
  simp only [beq_iff_eq] at hfolds hfp
  have hcrlen : cr.1.length = ar.length := by
    rw [length_commitReplay, List.length_zip, Array.length_toList, Array.length_toList, hcs.1,
      hcs.2, Nat.min_self]
  have hflen : proof.folds.toList.length = ar.length := by rw [Array.length_toList, hfolds]
  refine ⟨hpar.2, hfolds, hcs.1, hcs.2, hfp, hw, hcrlen, fun j hj ↦ ?_⟩
  have hjk : j < idx.zipIdx.length := by rw [List.length_zipIdx, hidxlen]; exact hj
  have hjg : j < groups.length := by rw [hglen, hidxlen]; exact hj
  have hq := hg j hjk hjg
  rw [List.getElem_zipIdx, Nat.zero_add, hbetas] at hq
  obtain ⟨hwid, hsib, hfin, hfinal, hres⟩ := queryBody_ok H P logMax alpha rounds _ ar _ _ _
    (idx[j]'(by rw [hidxlen]; exact hj), j) hb (hzne _) hh (hrowsq j hj) _ _ hq
  have hgj := congrArg Prod.fst hres
  dsimp only at hgj hwid hfin hfinal
  have hidxj : idx[j]'(by rw [hidxlen]; exact hj) =
      (smpBits H logMax (sampleStates H w.2 j)).1 := by
    simp only [hidx, List.getElem_map, List.getElem_range]
  rw [hidxj] at hgj hfin hfinal hsib
  set index := (smpBits H logMax (sampleStates H w.2 j)).1
  set l := cr.1.zip (querySteps j ar proof.folds.toList) with hl
  have hll : l.length = ar.length := by
    rw [hl, List.length_zip, hcrlen, length_querySteps _ _ _ hflen, Nat.min_self]
  have hlar : l.map (·.2.logArity) = ar := by
    have hsnd : l.map Prod.snd = querySteps j ar proof.folds.toList :=
      List.map_snd_zip (by rw [hcrlen, length_querySteps _ _ _ hflen])
    rw [show (l.map fun x : EF × QueryFold EF ↦ x.2.logArity) =
      (l.map Prod.snd).map (·.logArity) by rw [List.map_map]; rfl, hsnd,
      map_logArity_querySteps _ _ _ hflen]
  refine ⟨by rw [List.length_map, Array.length_toList]; exact hinlen, fun x hx ↦ ?_,
    fun i y hy ↦ ?_, hfin, hfinal⟩
  · -- the input rows
    have hx' := hx
    rw [List.zip_map_left] at hx'
    obtain ⟨⟨b, rd⟩, hbr, rfl⟩ := List.mem_map.mp hx'
    obtain ⟨hne, hsz, hall, hpath⟩ := hinok _ hbr
    obtain ⟨hlen, -⟩ := hrowsq j hj _ hx
    obtain ⟨path, hp⟩ := hpath j (by rw [hidxlen]; exact hj)
    refine ⟨hne, ⟨path, ?_⟩, hlen, hwid _ hx⟩
    rw [← hidxj]
    simpa only [Prod.map, id, List.map_map, Function.comp_def] using hp
  · -- the folds
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hy
    have hiar : i < ar.length := hll ▸ hi
    refine ⟨hsib i l[i] (List.getElem?_eq_getElem hi), ?_⟩
    set xs := (proof.commits.toList.zip proof.folds.toList).zip ar.zipIdx with hxs
    have hcl : proof.commits.toList.length = ar.length := by rw [Array.length_toList, hcs.1]
    have hxslen : xs.length = ar.length := by
      rw [hxs, List.length_zip, List.length_zip, List.length_zipIdx, hcl, hflen, Nat.min_self,
        Nat.min_self]
    have hxi : i < xs.length := hxslen ▸ hiar
    have hxsi : xs[i] = ((proof.commits.toList[i]'(hcl ▸ hiar),
        proof.folds.toList[i]'(hflen ▸ hiar)), (ar[i], i)) := by
      simp only [hxs, List.getElem_zip, List.getElem_zipIdx, Nat.zero_add]
    have hxsar : xs.map (·.2.1) = ar := by
      rw [hxs, show (fun x : (Digest F × CommitOpening F EF) × Nat × Nat ↦ x.2.1) =
        Prod.fst ∘ Prod.snd from rfl, ← List.map_map, List.map_snd_zip (by
          rw [List.length_zip, List.length_zipIdx, hcl, hflen, Nat.min_self]),
        List.zipIdx_map_fst]
    have hsum : ((l.take i).map (·.2.logArity)).sum = ((xs.take i).map (·.2.1)).sum := by
      rw [List.map_take, List.map_take, hlar, hxsar]
    have hla : l[i].2.logArity = ar[i] := by
      have h1 : (l.map (·.2.logArity))[i]'(by rw [List.length_map]; exact hi) = ar[i] := by
        simp only [hlar]
      rwa [List.getElem_map] at h1
    have hv := hphase i hxi
    rw [hxsi] at hv
    dsimp only at hv
    rw [← hsum, ← hla] at hv
    obtain ⟨path, hp⟩ := Merkle.verifyBatch_of_verifyMulti H.hash H.compress _ 1 _ Nat.one_pos _
      rfl _ _ _ hv j (by rw [List.length_map, List.length_map]; exact hjg)
    refine ⟨path, ?_⟩
    have hgi : (groups[j]'hjg).getD i (0, []) = foldGroup l[i]
        (foldState l (queryValue logMax alpha rounds proof.inputs.toList j index, index, logMax)
          i) := by
      rw [hgj, List.getD_eq_getElem _ _ (by rw [length_foldGroups]; exact hi),
        getElem_foldGroups l _ i hi]
    have hst2 : (foldState l (queryValue logMax alpha rounds proof.inputs.toList j index, index,
        logMax) i).2.2 = logMax - ((l.take i).map (·.2.logArity)).sum :=
      congrArg (·.2) (foldState_snd l _ _ _ i)
    rw [List.getD_eq_getElem _ _ (hcl ▸ hiar), hst2]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_map]; exact hjg),
      List.getElem_map, List.getElem_map, List.getElem_map, List.getElem_map, hgi] at hp
    exact hp

/-! ### The STARK verifier -/

/-- The challenger after observing every opened value of `rounds`, in `verifyPcs`'s order. -/
def obsOpened (s : H.State) (rounds : List (Round F EF)) : H.State :=
  rounds.foldl (fun s r ↦ r.2.foldl (fun s m ↦ m.2.foldl (fun s p ↦ obsExts H s p.2) s) s) s

/-- The PCS's challenger after its domain separator and the opened values of `rounds`. -/
def pcsState (P : Params) (rounds : List (Round F EF)) (s : H.State) : H.State :=
  obsOpened H (obsList H s (DomainSeparator.pcsSeed F EF (claimCounts rounds) P.batchPowBits))
    rounds

/-- **An accepting `verifyPcs`**: the batching grinding witness checks, and FRI accepts at the
batching challenge sampled after it. -/
theorem verifyPcs_ok (P : Params) (rounds : List (Round F EF)) (proof : FriProof F EF)
    (s : H.State) (r : Unit × H.State) (h : verifyPcs H P rounds proof s = .ok r) :
    let c := chkWit H P.batchPowBits proof.batchWitness (pcsState H P rounds s)
    (P.batchPowBits != 0 || proof.batchWitness == 0) = true ∧ c.1 = true ∧
      verifyFri H P proof rounds (smpExt H c.2).1 (smpExt (EF := EF) H c.2).2 = .ok r := by
  intro c
  unfold verifyPcs at h
  obtain ⟨hbw, h⟩ := ensure_bind_eq_ok H h
  rw [bind_ok_of H (observeList_eq H _ s)] at h
  obtain ⟨u, st1, h1, h⟩ := bind_eq_ok H h
  have hobs : forIn rounds PUnit.unit (fun r _ ↦ (do
      forIn r.2 PUnit.unit fun m _ ↦ (do
        forIn m.2 PUnit.unit fun p _ ↦ (do
          observeExts H p.2
          pure (ForInStep.yield PUnit.unit) : M H (ForInStep PUnit))
        pure (ForInStep.yield PUnit.unit) : M H (ForInStep PUnit))
      pure (ForInStep.yield PUnit.unit) : M H (ForInStep PUnit)))
        (obsList H s (DomainSeparator.pcsSeed F EF (claimCounts rounds) P.batchPowBits)) =
      .ok ((), pcsState H P rounds s) := by
    refine forIn_unit_state H _ _ (fun r s ↦ ?_) rounds _
    obtain ⟨cm, mats⟩ := r
    refine (bind_ok_of H (forIn_unit_state H _ _ (fun m s ↦ ?_) mats s)).trans rfl
    obtain ⟨d, pts⟩ := m
    refine (bind_ok_of H (forIn_unit_state H _ _ (fun p s ↦ ?_) pts s)).trans rfl
    obtain ⟨z, ys⟩ := p
    exact (bind_ok_of H (observeExts_eq H ys s)).trans rfl
  rw [hobs] at h1
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h1)
  rw [bind_ok_of H (a := c.1) (s' := c.2) (checkWitness_eq H _ _ _)] at h
  obtain ⟨hc, h⟩ := ensure_bind_eq_ok H h
  rw [bind_ok_of H (sampleExt_eq H _)] at h
  exact ⟨hbw, hc, h⟩

section States
variable (P : Params) (A : Air F) (vk : Option (PreprocessedKey F)) (proof : Proof F EF)
  (pis : List F)

/-- FRI's largest height on `proof`: the trace's extension. -/
abbrev friLogMax : Nat := proof.degreeBits + P.logBlowup

/-- FRI's fold schedule on `proof`. -/
abbrev friSchedule : List Nat :=
  foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen) (friLogMax P proof)
    [friLogMax P proof]

/-- FRI's domain separator on `proof`. -/
abbrev friSeedOf : List F :=
  DomainSeparator.friSeed F EF (friSchedule P proof) (2 ^ P.logFinalPolyLen) P.commitPowBits
    P.queryPowBits P.numQueries (friLogMax P proof) P.logBlowup P.maxLogArity

/-- The challenger after the domain separator, the trace and preprocessed commitments and the
public values. -/
abbrev stateAlpha : H.State :=
  obsList H (obsList H (obsList H (obsList H H.init (starkSeedOf EF P A proof.degreeBits))
    proof.traceCommit.toList) (preprocessedDigest vk)) pis

/-- The constraint-folding challenge `α`. -/
def alphaOf : EF := (smpExt H (stateAlpha H P A vk proof pis)).1

/-- The out-of-domain grinding check, after the quotient commitment. -/
abbrev oodCheck : Bool × H.State :=
  chkWit H P.oodPowBits proof.oodWitness
    (obsList H (smpExt (EF := EF) H (stateAlpha H P A vk proof pis)).2 proof.quotientCommit.toList)

/-- The out-of-domain point `ζ`. -/
def zetaOf : EF := (smpExt H (oodCheck (EF := EF) H P A vk proof pis).2).1

/-- The batching grinding check, after the PCS's domain separator and the opened values. -/
def batchCheck : Bool × H.State :=
  chkWit H P.batchPowBits proof.fri.batchWitness
    (pcsState H P (openingRounds A vk proof (zetaOf H P A vk proof pis))
    (smpExt (EF := EF) H (oodCheck (EF := EF) H P A vk proof pis).2).2)

/-- FRI's batching challenge. -/
def batchOf : EF := (smpExt H (batchCheck H P A vk proof pis).2).1

/-- The challenger when FRI starts, after the batching challenge. -/
def stateFri : H.State := (smpExt (EF := EF) H (batchCheck H P A vk proof pis).2).2

end States

theorem except_bind_ok {α : Type} (R : ExceptT String Id α) (p : α → Bool) (msg : String)
    (h : (R >>= fun x ↦ if p x = true then pure () else throw msg).run = .ok ()) :
    ∃ x, R = .ok x ∧ p x = true := by
  revert h
  match R with
  | .ok x =>
    intro h
    refine ⟨x, rfl, ?_⟩
    by_contra hp
    simp only [Bool.not_eq_true] at hp
    change (if p x = true then pure () else throw msg : ExceptT String Id Unit).run = _ at h
    rw [hp] at h
    exact absurd h (by intro h'; cases h')
  | .error e => intro h; exact absurd h (by intro h'; cases h')

/-- **An accepting STARK verifier** on pure primitives: the proof's shape checks, the grinding
witnesses check, `ζ` is off the trace domain, FRI accepts from the challenger after the batching
challenge, and the constraints hold at `ζ` with the challenger's `α` and `ζ`. -/
theorem verifyWith_ok (P : Params) (A : Air F) (vk : Option (PreprocessedKey F))
    (proof : Proof F EF) (pis : List F) (h : verifyWith H P A vk proof pis = .ok ()) :
    let o := proof.opened
    let zeta := zetaOf H P A vk proof pis
    o.traceLocal.size = A.width ∧ traceNextOk A o = true ∧
      o.quotientChunks.size = 2 ^ A.logQuotientChunks proof.degreeBits ∧
      (∀ ch ∈ o.quotientChunks, ch.size = Challenge.d EF) ∧
      preprocessedShapeOk A vk o proof.degreeBits = true ∧
      proof.degreeBits + A.logQuotientChunks proof.degreeBits ≤ twoAdicity F ∧
      pis.length = A.numPublicValues ∧
      (oodCheck (EF := EF) H P A vk proof pis).1 = true ∧
      (Ext.powTwo zeta proof.degreeBits - 1 != 0) = true ∧
      (batchCheck H P A vk proof pis).1 = true ∧
      (∃ st, verifyFri H P proof.fri (openingRounds A vk proof zeta) (batchOf H P A vk proof pis)
        (stateFri H P A vk proof pis) = .ok ((), st)) ∧
      checkConstraints A pis o proof.degreeBits zeta (alphaOf H P A vk proof pis)
        (recompose (chunkDomains proof.degreeBits (A.logQuotientChunks proof.degreeBits))
          o.quotientChunks.toList zeta) = true := by
  intro o zeta
  unfold verifyWith at h
  dsimp only at h
  by_cases hdeg : proof.degreeBits + A.logQuotientChunks proof.degreeBits ≤ twoAdicity F
  · rw [ite_eq_left hdeg] at h
    by_cases hper : A.periodicFits proof.degreeBits = true
    · rw [ite_eq_left hper] at h
      split at h
      · rename_i hpis
        split at h
        · rename_i hshape
          split at h
          · obtain ⟨x, hx, hc⟩ := except_bind_ok _ _ _ h
            unfold StateT.run at hx
            rw [bind_ok_of H (observeList_eq H _ _), bind_ok_of H (observeList_eq H _ _),
              bind_ok_of H (observeList_eq H _ _), bind_ok_of H (observeList_eq H _ _),
              bind_ok_of H (a := alphaOf H P A vk proof pis)
                (s' := (smpExt (EF := EF) H (stateAlpha H P A vk proof pis)).2) (sampleExt_eq H _),
              bind_ok_of H (observeList_eq H _ _),
              bind_ok_of H (a := (oodCheck (EF := EF) H P A vk proof pis).1)
                (s' := (oodCheck (EF := EF) H P A vk proof pis).2) (checkWitness_eq H _ _ _)] at hx
            obtain ⟨hood, hx⟩ := ensure_bind_eq_ok H hx
            rw [bind_ok_of H (a := zeta) (s' := (smpExt (EF := EF) H
              (oodCheck (EF := EF) H P A vk proof pis).2).2) (sampleExt_eq H _)] at hx
            obtain ⟨hz, hx⟩ := ensure_bind_eq_ok H hx
            obtain ⟨u, st, h3, h4⟩ := bind_eq_ok H hx
            obtain ⟨-, hbc, hfri⟩ := verifyPcs_ok H P _ proof.fri _ _ h3
            have hx' := pure_eq_ok H h4
            subst hx'
            simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at hshape
            obtain ⟨⟨⟨⟨h1a, h1b⟩, h1c⟩, h1d⟩, h1e⟩ := hshape
            exact ⟨h1a, h1b, h1c, h1d, h1e, hdeg, beq_iff_eq.mp hpis, hood, hz, hbc, ⟨_, hfri⟩,
              hc⟩
          · exact absurd h (by intro h'; cases h')
        · exact absurd h (by intro h'; cases h')
      · exact absurd h (by intro h'; cases h')
    · rw [ite_eq_right hper] at h
      exact absurd h (by intro h'; cases h')
  · rw [ite_eq_right hdeg] at h
    exact absurd h (by intro h'; cases h')

end CompStark.Ni
