/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BcsRun
public import CompStark.Merkle.MixedMulti

/-! # Accepting runs of the commitment scheme at mixed heights

`Ni/BcsRun.lean` reads an accepting run of the FRI verifier whose matrices all have the largest
height. Here the matrices have any heights, as in the batch STARK, whose instances have traces of
several lengths:

* `foldStepR`, `foldQuery_okR`: a query's folds add the reduced opening of each shorter height,
  times `β ^ 2 ^ a`, when they reach it.
* `reduceQuery_okR`: a query's reduced openings are one batched quotient per height, tallest
  first, each over the opened values of the matrices of that height, in the rounds' order.
* `verifyInputs_okR`: each round's multi-opening, of matrices of mixed heights, gives every query
  an accepted single opening of its rows (`Merkle.verifyBatch_of_verifyMulti_mixed`).
* `verifyFri_okR`: an accepting FRI verifier on rounds of any heights.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri

variable {F : Type} (H : Primitives F Id)

/-! ### A query's folds with injected reduced openings -/

section Folds
variable [BaseField F] {EF : Type} [Challenge F EF]

/-- One fold `x = (β, step)` of a query in state `(ro, eval, index, logH)`, the reduced openings
`ro` of the shorter heights pending: fold the group at `β`, shift the index and lower the height by
the arity, and add the next pending reduced opening times `β ^ 2 ^ a` if it has the folded
height. -/
def foldStepR (x : EF × QueryFold EF) (st : List (Nat × EF) × EF × Nat × Nat) :
    List (Nat × EF) × EF × Nat × Nat :=
  let a := x.2.logArity
  let e := foldRow (st.2.2.1 >>> a) (st.2.2.2 - a) a x.1 (groupOf x.2 st.2.2.1 st.2.1)
  match st.1 with
  | (h, r) :: rest =>
    if h == st.2.2.2 - a then (rest, e + Ext.powTwo x.1 a * r, st.2.2.1 >>> a, st.2.2.2 - a)
    else (st.1, e, st.2.2.1 >>> a, st.2.2.2 - a)
  | [] => ([], e, st.2.2.1 >>> a, st.2.2.2 - a)

/-- The state of a query before fold `j` of the folds `l`. -/
def foldStateR (l : List (EF × QueryFold EF)) (st0 : List (Nat × EF) × EF × Nat × Nat)
    (j : Nat) : List (Nat × EF) × EF × Nat × Nat :=
  (l.take j).foldl (fun st x ↦ foldStepR x st) st0

theorem foldStateR_zero (l : List (EF × QueryFold EF)) (st0 : List (Nat × EF) × EF × Nat × Nat) :
    foldStateR l st0 0 = st0 := by
  simp only [foldStateR, List.take_zero, List.foldl_nil]

theorem foldStateR_cons (x : EF × QueryFold EF) (l : List (EF × QueryFold EF))
    (st0 : List (Nat × EF) × EF × Nat × Nat) (j : Nat) :
    foldStateR (x :: l) st0 (j + 1) = foldStateR l (foldStepR x st0) j := by
  simp only [foldStateR, List.take_succ_cons, List.foldl_cons]

theorem foldStateR_succ (l : List (EF × QueryFold EF)) (st0 : List (Nat × EF) × EF × Nat × Nat)
    (j : Nat) (hj : j < l.length) :
    foldStateR l st0 (j + 1) = foldStepR l[j] (foldStateR l st0 j) := by
  simp only [foldStateR, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- A fold step lowers the index and height as without injections. -/
theorem foldStepR_snd (x : EF × QueryFold EF) (st : List (Nat × EF) × EF × Nat × Nat) :
    (foldStepR x st).2.2 = (st.2.2.1 >>> x.2.logArity, st.2.2.2 - x.2.logArity) := by
  unfold foldStepR
  dsimp only
  split
  · split <;> rfl
  · rfl

/-- The index and height before fold `j`: the arities before `j` shifted out. -/
theorem foldStateR_snd (l : List (EF × QueryFold EF)) :
    ∀ (ro : List (Nat × EF)) (e : EF) (i h j : Nat), (foldStateR l (ro, e, i, h) j).2.2 =
      (i >>> ((l.take j).map (·.2.logArity)).sum, h - ((l.take j).map (·.2.logArity)).sum) := by
  induction l with
  | nil => intro ro e i h j; simp only [foldStateR, List.take_nil, List.foldl_nil, List.map_nil,
      List.sum_nil, Nat.shiftRight_zero, Nat.sub_zero]
  | cons x l ih =>
    intro ro e i h j
    cases j with
    | zero => simp only [foldStateR_zero, List.take_zero, List.map_nil, List.sum_nil,
        Nat.shiftRight_zero, Nat.sub_zero]
    | succ j =>
      have hs : foldStepR x (ro, e, i, h) = ((foldStepR x (ro, e, i, h)).1,
          (foldStepR x (ro, e, i, h)).2.1, i >>> x.2.logArity, h - x.2.logArity) :=
        Prod.ext rfl (Prod.ext rfl (foldStepR_snd x _))
      rw [foldStateR_cons, hs, ih, List.take_succ_cons, List.map_cons, List.sum_cons,
        Nat.shiftRight_add,
        Nat.sub_add_eq]

/-- The groups the folds `l` open from the state `st`. -/
def foldGroupsR : List (EF × QueryFold EF) → List (Nat × EF) × EF × Nat × Nat →
    List (Nat × List EF)
  | [], _ => []
  | x :: l, st => foldGroup x st.2 :: foldGroupsR l (foldStepR x st)

theorem length_foldGroupsR : ∀ (l : List (EF × QueryFold EF))
    (st : List (Nat × EF) × EF × Nat × Nat), (foldGroupsR l st).length = l.length
  | [], _ => rfl
  | x :: l, st => by rw [foldGroupsR, List.length_cons, length_foldGroupsR l, List.length_cons]

theorem getElem_foldGroupsR : ∀ (l : List (EF × QueryFold EF))
    (st : List (Nat × EF) × EF × Nat × Nat) (j : Nat) (hj : j < l.length),
    (foldGroupsR l st)[j]'(by rw [length_foldGroupsR]; exact hj) =
      foldGroup l[j] (foldStateR l st j).2
  | [], _, _, hj => absurd hj (Nat.not_lt_zero _)
  | x :: l, st, 0, _ => by simp only [foldGroupsR, List.getElem_cons_zero, foldStateR_zero]
  | x :: l, st, j + 1, hj => by
    simp only [foldGroupsR, List.getElem_cons_succ, foldStateR_cons]
    exact getElem_foldGroupsR l _ j (by simp only [List.length_cons] at hj; omega)

theorem foldBody_okR (q : Nat) (beta : EF) (la : Nat) (o : CommitOpening F EF)
    (ro : List (Nat × EF)) (eval : EF) (index logH : Nat) (groups : List (Nat × List EF))
    (st : H.State)
    (r : ForInStep (List (Nat × EF) × EF × Nat × Nat × List (Nat × List EF)) × H.State)
    (h : foldBody H q beta la o ro eval index logH groups st = .ok r) :
    let x : EF × QueryFold EF := (beta, ⟨la, o.siblings.getD q #[]⟩)
    let s := foldStepR x (ro, eval, index, logH)
    x.2.siblings.size = 2 ^ la - 1 ∧
      r = (.yield (s.1, s.2.1, s.2.2.1, s.2.2.2, groups ++ [foldGroup x (eval, index, logH)]),
        st) := by
  intro x s
  unfold foldBody at h
  obtain ⟨h1, h⟩ := ensure_bind_eq_ok H h
  refine ⟨beq_iff_eq.mp h1, ?_⟩
  rcases ro with _ | ⟨⟨hh, rr⟩, rest⟩
  · exact (pure_eq_ok H h).trans rfl
  · dsimp only at h
    split at h
    · rename_i he
      rw [pure_eq_ok H h]
      simp only [s, foldStepR, x, he, ↓reduceIte]
      rfl
    · rename_i he
      rw [pure_eq_ok H h]
      simp only [s, foldStepR, x, he, ↓reduceIte, Bool.false_eq_true]
      rfl

/-- An accepting fold loop: every fold's sibling count checks, the loop ends in the last state,
and it adds every fold's group. -/
theorem foldLoop_okR (q : Nat) (body : (EF × Nat) × CommitOpening F EF →
      List (Nat × EF) × EF × Nat × Nat × List (Nat × List EF) →
        M H (ForInStep (List (Nat × EF) × EF × Nat × Nat × List (Nat × List EF))))
    (hbody : ∀ beta la o ro eval index logH groups,
      body ((beta, la), o) (ro, eval, index, logH, groups) =
        foldBody H q beta la o ro eval index logH groups) :
    ∀ (betas : List EF) (arities : List Nat) (folds : List (CommitOpening F EF))
      (st0 : List (Nat × EF) × EF × Nat × Nat) (g0 : List (Nat × List EF)) (st : H.State)
      (r : (List (Nat × EF) × EF × Nat × Nat × List (Nat × List EF)) × H.State),
      forIn ((betas.zip arities).zip folds) (st0.1, st0.2.1, st0.2.2.1, st0.2.2.2, g0) body st =
        .ok r →
        let l := betas.zip (querySteps q arities folds)
        let fin := foldStateR l st0 l.length
        (∀ (j : Nat) (x : EF × QueryFold EF), l[j]? = some x →
          x.2.siblings.size = 2 ^ x.2.logArity - 1) ∧
          r = ((fin.1, fin.2.1, fin.2.2.1, fin.2.2.2, g0 ++ foldGroupsR l st0), st)
  | [], _, _, st0, g0, st, r, h
  | _ :: _, [], _, st0, g0, st, r, h
  | _ :: _, _ :: _, [], st0, g0, st, r, h => by
    simp only [List.zip_nil_left, List.zip_nil_right, List.zip_cons_cons, List.forIn_nil,
      querySteps, List.map_nil] at h ⊢
    refine ⟨fun j x hx ↦ by simp only [List.getElem?_nil, reduceCtorEq] at hx, ?_⟩
    rw [pure_eq_ok H h]
    simp only [List.length_nil, foldStateR_zero, foldGroupsR, List.append_nil]
  | beta :: betas, la :: arities, o :: folds, (ro, eval, index, logH), g0, st, r, h => by
    simp only [List.zip_cons_cons] at h
    obtain ⟨step, st', h1, h2⟩ := forIn_cons_eq_ok H _ _ _ _ _ _ h
    rw [hbody] at h1
    obtain ⟨hok, hr⟩ := foldBody_okR H q beta la o ro eval index logH g0 st _ h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
    obtain ⟨hl, hr⟩ := foldLoop_okR q body hbody betas arities folds
      (foldStepR (beta, ⟨la, o.siblings.getD q #[]⟩) (ro, eval, index, logH)) _ _ r h2
    have hsteps : querySteps q (la :: arities) (o :: folds) =
        ⟨la, o.siblings.getD q #[]⟩ :: querySteps q arities folds := rfl
    simp only [hsteps, List.zip_cons_cons, List.length_cons, foldStateR_cons, foldGroupsR]
    refine ⟨fun j x hx ↦ ?_, by rw [hr, List.append_assoc]; rfl⟩
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      rw [← hx]
      exact hok
    | succ j =>
      rw [List.getElem?_cons_succ] at hx
      exact hl j x hx

/-- **An accepting `foldQuery`** of query `q` from the reduced openings `(logMax, e0) :: ro`:
every fold's sibling count checks, the folds end at the final height having added every pending
reduced opening, and the result is the last state's value and index and the groups the folds
open. -/
theorem foldQuery_okR (P : Params) (logMax index q : Nat) (betas : List EF) (arities : List Nat)
    (folds : List (CommitOpening F EF)) (e0 : EF) (ro : List (Nat × EF)) (st : H.State)
    (r : (EF × Nat × List (Nat × List EF)) × H.State)
    (h : foldQuery H P logMax index q betas arities folds ((logMax, e0) :: ro) st = .ok r) :
    let l := betas.zip (querySteps q arities folds)
    let fin := foldStateR l (ro, e0, index, logMax) l.length
    (∀ (j : Nat) (x : EF × QueryFold EF), l[j]? = some x →
      x.2.siblings.size = 2 ^ x.2.logArity - 1) ∧
      fin.2.2.2 = P.logBlowup + P.logFinalPolyLen ∧ fin.1 = [] ∧
      r = ((fin.2.1, fin.2.2.1, foldGroupsR l (ro, e0, index, logMax)), st) := by
  intro l fin
  unfold foldQuery at h
  simp only [pure_bind, List.tail_cons] at h
  obtain ⟨-, h1⟩ := ensure_bind_eq_ok H h
  obtain ⟨res, st2, hloop, h3⟩ := bind_eq_ok H h1
  obtain ⟨hl, hres⟩ := foldLoop_okR H q _ (fun _ _ _ _ _ _ _ _ ↦ rfl) betas arities folds
    (ro, e0, index, logMax) [] _ _ hloop
  obtain ⟨hr1, hr2⟩ := Prod.mk.inj hres
  rw [hr1, hr2] at h3
  obtain ⟨hfin, h4⟩ := ensure_bind_eq_ok H h3
  obtain ⟨hro, h5⟩ := ensure_bind_eq_ok H h4
  exact ⟨hl, beq_iff_eq.mp hfin, List.isEmpty_iff.mp hro,
    by rw [pure_eq_ok H h5, List.nil_append]⟩

end Folds

/-! ### A query's reduced openings at mixed heights -/

/-- Heights, distinct and tallest first, as the FRI verifier lists them. -/
def descHeights (l : List Nat) : List Nat := (l.mergeSort fun a b ↦ b ≤ a).dedup

theorem pairwise_descHeights (l : List Nat) : (descHeights l).Pairwise (· > ·) := by
  have hs := List.pairwise_mergeSort (le := fun a b : Nat ↦ decide (b ≤ a))
    (fun a b c h1 h2 ↦ by simp only [decide_eq_true_eq] at *; omega)
    (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  refine ((hs.sublist (List.dedup_sublist _)).and (List.nodup_dedup _)).imp fun {a b} h ↦ ?_
  obtain ⟨h1, h2⟩ := h
  simp only [decide_eq_true_eq] at h1
  omega

theorem mem_descHeights (l : List Nat) (a : Nat) : a ∈ descHeights l ↔ a ∈ l := by
  rw [descHeights, List.mem_dedup, List.mem_mergeSort]

theorem mem_keys_iff {β : Type} (a : Nat) : ∀ (ro : List (Nat × β)),
    a ∈ ro.map (·.1) ↔ (ro.lookup a).isSome
  | [] => by simp only [List.map_nil, List.not_mem_nil, List.lookup_nil, Option.isSome_none,
      Bool.false_eq_true]
  | (k, v) :: ro => by
    rw [List.map_cons, List.mem_cons, List.lookup_cons, mem_keys_iff a ro]
    by_cases h : a = k
    · simp only [h, beq_self_eq_true, Option.isSome_some, true_or]
    · simp only [h, beq_eq_false_iff_ne.mpr h, false_or]


section Reduce
variable [BaseField F] {EF : Type} [Challenge F EF]

theorem lookup_filter_ne {β : Type} (h0 : Nat) :
    ∀ (ro : List (Nat × β)) (h : Nat),
      (ro.filter (·.1 != h0)).lookup h = if h = h0 then none else ro.lookup h
  | [], h => by split <;> rfl
  | (k, v) :: ro, h => by
    by_cases hk : k = h0
    · subst hk
      rw [List.filter_cons_of_neg (by simp only [bne_self_eq_false, Bool.false_eq_true,
        not_false_eq_true]), lookup_filter_ne k ro h]
      by_cases hh : h = k
      · simp only [hh, ↓reduceIte]
      · simp only [hh, ↓reduceIte, List.lookup_cons, beq_eq_false_iff_ne.mpr hh]
    · rw [List.filter_cons_of_pos (by simp only [bne_iff_ne, ne_eq, hk, not_false_eq_true]),
        List.lookup_cons, List.lookup_cons, lookup_filter_ne h0 ro h]
      by_cases hh : h = h0
      · subst hh
        simp only [↓reduceIte, beq_eq_false_iff_ne.mpr (Ne.symm hk)]
      · simp only [hh, ↓reduceIte]

theorem lookup_of_mem {β : Type} : ∀ (ro : List (Nat × β)), (ro.map (·.1)).Nodup →
    ∀ e ∈ ro, ro.lookup e.1 = some e.2
  | [], _, _, he => absurd he List.not_mem_nil
  | (k, v) :: ro, hnd, e, he => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.lookup_cons]
    rcases List.mem_cons.mp he with rfl | he
    · simp only [beq_self_eq_true]
    · have hne : e.1 ≠ k := fun h ↦ hnd.1 (List.mem_map.mpr ⟨e, he, h⟩)
      simp only [beq_eq_false_iff_ne.mpr hne]
      exact lookup_of_mem ro hnd.2 e he

/-- The query's point at height `2 ^ h`: the point of index `index >>> (logMax - h)` of the
coset of that size, in bit-reversed order. -/
def pointAt (logMax index h : Nat) : F :=
  gen * powF (twoAdicGen h) (reverseBits (index >>> (logMax - h)) h)

/-- The batched quotient's running power of `α` and sum at height `2 ^ h`, over the opened values
of the matrices of `mats` of that height. -/
def reducedAt (P : Params) (logMax index : Nat) (alpha : EF)
    (mats : List (Array F × Domain F × List (EF × List EF))) (h : Nat) : EF × EF :=
  accTerms alpha (pointAt logMax index h)
    (batchTerms (mats.filter fun x ↦ x.2.1.logSize + P.logBlowup == h)) (1, 0)

/-- `reduceQuery`'s state after the matrices `mats`: one entry per height, the running power and
sum of that height's matrices. -/
def RoSpec (P : Params) (logMax index : Nat) (alpha : EF)
    (mats : List (Array F × Domain F × List (EF × List EF))) (ro : List (Nat × EF × EF)) :
    Prop :=
  (ro.map (·.1)).Nodup ∧ ∀ h, ro.lookup h =
    if mats.any (fun x ↦ x.2.1.logSize + P.logBlowup == h) then
      some (reducedAt P logMax index alpha mats h) else none

theorem roSpec_nil (P : Params) (logMax index : Nat) (alpha : EF) :
    RoSpec P logMax index alpha [] [] :=
  ⟨List.nodup_nil, fun _ ↦ rfl⟩

theorem roSpec_step (P : Params) (logMax index : Nat) (alpha : EF)
    (mats : List (Array F × Domain F × List (EF × List EF))) (ro : List (Nat × EF × EF))
    (hro : RoSpec P logMax index alpha mats ro) (x : Array F × Domain F × List (EF × List EF)) :
    let h0 := x.2.1.logSize + P.logBlowup
    let s := accTerms alpha (pointAt logMax index h0) (batchTerms [x])
      ((ro.lookup h0).getD (1, 0))
    RoSpec P logMax index alpha (mats ++ [x]) ((h0, s.1, s.2) :: ro.filter (·.1 != h0)) := by
  intro h0 s
  obtain ⟨hnd, hlk⟩ := hro
  have hstart : (ro.lookup h0).getD (1, 0) = reducedAt P logMax index alpha mats h0 := by
    rw [hlk]
    split
    · rfl
    · rename_i hany
      simp only [Option.getD_none, reducedAt]
      rw [List.filter_eq_nil_iff.mpr fun y hy hb ↦ hany (List.any_eq_true.mpr ⟨y, hy, hb⟩)]
      rfl
  refine ⟨?_, fun h ↦ ?_⟩
  · rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm ↦ ?_, hnd.sublist (List.Sublist.map _ List.filter_sublist)⟩
    obtain ⟨e, he, he1⟩ := List.mem_map.mp hm
    have := (List.mem_filter.mp he).2
    simp only [he1, bne_self_eq_false, Bool.false_eq_true] at this
  · have hterms : ∀ h', reducedAt P logMax index alpha (mats ++ [x]) h' =
        if h0 = h' then accTerms alpha (pointAt logMax index h') (batchTerms [x])
          (reducedAt P logMax index alpha mats h')
        else reducedAt P logMax index alpha mats h' := by
      intro h'
      by_cases he : h0 = h'
      · have hb : (x.2.1.logSize + P.logBlowup == h') = true := beq_iff_eq.mpr he
        simp only [reducedAt, List.filter_append, List.filter_cons, List.filter_nil, hb,
          ↓reduceIte, he, batchTerms, List.flatMap_append, accTerms, List.foldl_append,
          List.flatMap_cons, List.flatMap_nil, List.append_nil]
      · have hb : (x.2.1.logSize + P.logBlowup == h') = false := beq_eq_false_iff_ne.mpr he
        simp only [reducedAt, List.filter_append, List.filter_cons, List.filter_nil, hb,
          Bool.false_eq_true, ↓reduceIte, he, List.append_nil]
    by_cases hh : h = h0
    · subst hh
      rw [List.lookup_cons, beq_self_eq_true]
      dsimp only
      rw [List.any_append, List.any_cons, List.any_nil, beq_self_eq_true, Bool.true_or,
        Bool.or_true]
      simp only [↓reduceIte, hterms, s, hstart]
    · rw [List.lookup_cons, beq_eq_false_iff_ne.mpr hh]
      dsimp only
      rw [lookup_filter_ne, ite_eq_right_of_eq_false _ _ (eq_false hh), hlk, hterms,
        ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm hh)), List.any_append,
        List.any_cons, List.any_nil, beq_eq_false_iff_ne.mpr (Ne.symm hh), Bool.false_or,
        Bool.or_false]

theorem rowsLoop_okR (P : Params) (logMax index : Nat) (alpha : EF) :
    ∀ (rows : List (Array F × Domain F × List (EF × List EF)))
      (mats : List (Array F × Domain F × List (EF × List EF))) (ro : List (Nat × EF × EF))
      (st : H.State) (r : List (Nat × EF × EF) × H.State),
      RoSpec P logMax index alpha mats ro →
      forIn rows ro (rowsBody H P logMax index alpha) st = .ok r →
        (∀ x ∈ rows, ∀ zy ∈ x.2.2, zy.2.length = x.1.size) ∧ r.2 = st ∧
          RoSpec P logMax index alpha (mats ++ rows) r.1
  | [], mats, ro, st, r, hro, h => by
    rw [List.forIn_nil] at h
    rw [pure_eq_ok H h, List.append_nil]
    exact ⟨fun _ h ↦ absurd h List.not_mem_nil, rfl, hro⟩
  | x :: rows, mats, ro, st, r, hro, h => by
    obtain ⟨step, st', h1, h2⟩ := forIn_cons_eq_ok H _ _ _ _ _ _ h
    unfold rowsBody at h1
    obtain ⟨s', st'', h3, h4⟩ := bind_eq_ok H h1
    obtain ⟨hw, hr3⟩ := pointsLoop_ok H alpha x.1 _ x.2.2 _ st _ h3
    obtain ⟨hs1, hs2⟩ := Prod.mk.inj hr3
    subst hs1 hs2
    obtain ⟨hs3, hs4⟩ := Prod.mk.inj (pure_eq_ok H h4)
    subst hs3 hs4
    have hstep := roSpec_step P logMax index alpha mats ro hro x
    have hb : batchTerms [x] =
        x.2.2.flatMap fun zy ↦ (x.1.toList.zip zy.2).map fun pp ↦ (pp, zy.1) := by
      simp only [batchTerms, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [hb] at hstep
    dsimp only at h2
    obtain ⟨hl, hst, hro'⟩ := rowsLoop_okR P logMax index alpha rows (mats ++ [x]) _ _ r
      hstep h2
    refine ⟨fun y hy ↦ ?_, hst, by rw [List.append_cons]; exact hro'⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hw
    · exact hl y hy

/-- The matrices of a query's batches, each with its row, in `reduceQuery`'s order. -/
def queryMats (xs : List (List (Array F) × Round F EF)) :
    List (Array F × Domain F × List (EF × List EF)) :=
  xs.flatMap fun x ↦ x.1.zip x.2.2

theorem batchLoop_okR (P : Params) (logMax index : Nat) (alpha : EF)
    (body : List (Array F) × Round F EF → List (Nat × EF × EF) →
      M H (ForInStep (List (Nat × EF × EF))))
    (hbody : ∀ x ro, body x ro = batchBody H P logMax index alpha x ro) :
    ∀ (xs : List (List (Array F) × Round F EF))
      (mats : List (Array F × Domain F × List (EF × List EF))) (ro : List (Nat × EF × EF))
      (st : H.State) (r : List (Nat × EF × EF) × H.State),
      RoSpec P logMax index alpha mats ro → forIn xs ro body st = .ok r →
        (∀ x ∈ xs, ∀ y ∈ x.1.zip x.2.2, ∀ zy ∈ y.2.2, zy.2.length = y.1.size) ∧ r.2 = st ∧
          RoSpec P logMax index alpha (mats ++ queryMats xs) r.1
  | [], mats, ro, st, r, hro, h => by
    rw [List.forIn_nil] at h
    rw [pure_eq_ok H h, queryMats, List.flatMap_nil, List.append_nil]
    exact ⟨fun _ h ↦ absurd h List.not_mem_nil, rfl, hro⟩
  | x :: xs, mats, ro, st, r, hro, h => by
    obtain ⟨step, st', h1, h2⟩ := forIn_cons_eq_ok H _ _ _ _ _ _ h
    rw [hbody] at h1
    unfold batchBody at h1
    obtain ⟨ro', st2, h4, h5⟩ := bind_eq_ok H h1
    obtain ⟨hw, hst2, hro'⟩ := rowsLoop_okR H P logMax index alpha _ mats ro st _ hro h4
    simp only at hst2
    subst hst2
    obtain ⟨hs1, hs2⟩ := Prod.mk.inj (pure_eq_ok H h5)
    subst hs1 hs2
    obtain ⟨hl, hst, hro''⟩ := batchLoop_okR P logMax index alpha body hbody xs _ _ _ r hro' h2
    refine ⟨fun y hy ↦ ?_, hst, ?_⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact hw
      · exact hl y hy
    · rw [queryMats, List.flatMap_cons, ← List.append_assoc]
      exact hro''

/-- **An accepting `reduceQuery`** on rounds of any heights, a row per matrix: every opened point
has a value per column, and the result lists one reduced opening per height, tallest first, the
batched quotient over the opened values of that height's matrices at the query's point. -/
theorem reduceQuery_okR (P : Params) (logMax index : Nat) (alpha : EF)
    (rows : List (List (Array F))) (rounds : List (Round F EF)) (st : H.State)
    (r : List (Nat × EF) × H.State)
    (h : reduceQuery H P logMax index alpha rows rounds st = .ok r) :
    (∀ x ∈ rows.zip rounds, ∀ y ∈ x.1.zip x.2.2, ∀ zy ∈ y.2.2, zy.2.length = y.1.size) ∧
      r = ((descHeights ((queryMats (rows.zip rounds)).map fun x ↦
          x.2.1.logSize + P.logBlowup)).map fun h ↦
        (h, (reducedAt P logMax index alpha (queryMats (rows.zip rounds)) h).2), st) := by
  unfold reduceQuery at h
  obtain ⟨ro, st', h1, h2⟩ := bind_eq_ok H h
  obtain ⟨hw, hst, hro⟩ := batchLoop_okR H P logMax index alpha _ (fun _ _ ↦ rfl) _ []
    [] st _ (roSpec_nil P logMax index alpha) h1
  simp only at hst
  subst hst
  rw [List.nil_append] at hro
  set mats := queryMats (rows.zip rounds)
  obtain ⟨hnd, hlk⟩ := hro
  set hs := descHeights (mats.map fun x ↦ x.2.1.logSize + P.logBlowup)
  have hres : (ro.mergeSort fun a b ↦ b.1 ≤ a.1).map (fun e ↦ (e.1, e.2.2)) =
      hs.map fun h ↦ (h, (reducedAt P logMax index alpha mats h).2) := by
    set L := ro.mergeSort fun a b ↦ b.1 ≤ a.1
    have hperm : L.Perm ro := List.mergeSort_perm _ _
    have hval : ∀ e ∈ ro, e.2 = reducedAt P logMax index alpha mats e.1 := fun e he ↦ by
      have h1 := lookup_of_mem ro hnd e he
      rw [hlk] at h1
      split at h1
      · exact (Option.some.inj h1).symm
      · exact absurd h1 (by simp only [reduceCtorEq, not_false_eq_true])
    have hkeys : L.map (·.1) = hs := by
      have hs' := List.pairwise_mergeSort (le := fun a b : Nat × EF × EF ↦ decide (b.1 ≤ a.1))
        (fun a b c h1 h2 ↦ by simp only [decide_eq_true_eq] at *; omega)
        (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) ro
      have hge : (L.map (·.1)).Pairwise (· ≥ ·) :=
        List.pairwise_map.mpr (hs'.imp fun h ↦ by simpa only [decide_eq_true_eq] using h)
      have hnd' : (L.map (·.1)).Nodup := (hperm.map _).nodup_iff.mpr hnd
      refine List.Pairwise.eq_of_mem_iff (r := (· > ·))
        ((hge.and hnd').imp fun h ↦ lt_of_le_of_ne h.1 (Ne.symm h.2))
        (pairwise_descHeights _) fun a ↦ ?_
      rw [(hperm.map _).mem_iff, mem_keys_iff, hlk, mem_descHeights, List.mem_map]
      split
      · rename_i hany
        obtain ⟨x, hx, hxa⟩ := List.any_eq_true.mp hany
        simp only [Option.isSome_some, true_iff]
        exact ⟨x, hx, beq_iff_eq.mp hxa⟩
      · rename_i hany
        simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_exists, not_and]
        exact fun x hx hxa ↦ hany (List.any_eq_true.mpr ⟨x, hx, beq_iff_eq.mpr hxa⟩)
    rw [← hkeys, List.map_map]
    refine List.map_congr_left fun e he ↦ ?_
    simp only [Function.comp_apply, hval e (hperm.mem_iff.mp he)]
  refine ⟨hw, ?_⟩
  dsimp only at h2
  rcases hlook : List.lookup P.logBlowup ro with _ | ⟨fst, acc⟩
  · rw [hlook] at h2
    rw [pure_eq_ok H h2, ← hres]
  · rw [hlook] at h2
    obtain ⟨-, h2⟩ := ensure_bind_eq_ok H h2
    rw [pure_eq_ok H h2, ← hres]

end Reduce

/-! ### The input multi-openings at mixed heights -/

section Inputs
variable [BaseField F] {EF : Type} [Challenge F EF]

/-- The log height of a round's tallest matrix. -/
def logBatch (P : Params) (mats : List (Domain F × List (EF × List EF))) : Nat :=
  (mats.map (·.1.logSize + P.logBlowup)).foldl max 0

/-- The heights of a round's matrices' extensions. -/
def roundHeights (P : Params) (mats : List (Domain F × List (EF × List EF))) : List Nat :=
  mats.map fun x ↦ 2 ^ (x.1.logSize + P.logBlowup)

theorem le_foldl_max : ∀ (l : List Nat) (acc : Nat), acc ≤ l.foldl max acc ∧
    ∀ x ∈ l, x ≤ l.foldl max acc
  | [], _ => ⟨le_rfl, fun _ h ↦ absurd h List.not_mem_nil⟩
  | y :: l, acc => by
    obtain ⟨h1, h2⟩ := le_foldl_max l (max acc y)
    refine ⟨(le_max_left _ _).trans h1, fun x hx ↦ ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (le_max_right _ _).trans h1
    · exact h2 x hx

theorem foldl_max_mem : ∀ (l : List Nat) (acc : Nat), l.foldl max acc = acc ∨
    l.foldl max acc ∈ l
  | [], _ => Or.inl rfl
  | y :: l, acc => by
    rcases foldl_max_mem l (max acc y) with h | h
    · rw [List.foldl_cons, h]
      rcases Nat.le_total acc y with hy | hy
      · exact Or.inr (by rw [Nat.max_eq_right hy]; exact List.mem_cons_self)
      · exact Or.inl (Nat.max_eq_left hy)
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- The pure Merkle check of `H` of an opening at `index` of matrices of heights `heights`, the
tallest `2 ^ k`, against the cap `cap` of height `capHeight`: an accepted opening of the subtree
under the index's cap entry, the heights divided by the cap's width, at the index's low bits. -/
abbrev verifyCapMixedH (cap : Cap F) (capHeight : Nat) (heights : List Nat) (k index : Nat)
    (values : List (List F)) (path : List (Digest F)) : Bool :=
  verifyBatchH H (cap.toList.getD (index >>> (k - min capHeight k)) 0)
    (heights.map (· / 2 ^ min capHeight k)) (index % 2 ^ (k - min capHeight k)) values path

/-- One batch of a query's input rows passes its checks at `index` into the largest domain, of
log size `logMax`: its matrices are some, with an accepted opening of their rows at the index
shifted to the batch's tallest height against the batch's cap, one row per matrix, and every
opened point has a value per column. -/
def BatchOkR (P : Params) (logMax index : Nat) (x : List (Array F) × Round F EF) : Prop :=
  x.2.2 ≠ [] ∧ x.2.1.size = 2 ^ min P.capHeight (logBatch P x.2.2) ∧
    (∃ path, verifyCapMixedH H x.2.1 P.capHeight (roundHeights P x.2.2) (logBatch P x.2.2)
      (index >>> (logMax - logBatch P x.2.2)) (x.1.map (·.toList)) path = true) ∧
    x.1.length = x.2.2.length ∧
    ∀ y ∈ x.1.zip x.2.2, ∀ zy ∈ y.2.2, zy.2.length = y.1.size

/-- An accepted input multi-opening of batch `x` at `indices`: its matrices are some, every query
opens a row per matrix, and every query's rows have an accepted single opening. -/
def InputOkR (P : Params) (logMax : Nat) (indices : List Nat) (x : MultiOpening F × Round F EF) :
    Prop :=
  x.2.2 ≠ [] ∧ x.2.1.size = 2 ^ min P.capHeight (logBatch P x.2.2) ∧
    x.1.values.size = indices.length ∧ (∀ v ∈ x.1.values, v.size = x.2.2.length) ∧
    ∀ j (hj : j < indices.length), ∃ path, verifyCapMixedH H x.2.1 P.capHeight
      (roundHeights P x.2.2) (logBatch P x.2.2) (indices[j] >>> (logMax - logBatch P x.2.2))
        ((x.1.values.getD j #[]).toList.map (·.toList)) path = true

theorem inputBody_okR (P : Params) (logMax : Nat) (indices : List Nat)
    (x : MultiOpening F × Round F EF) (st : H.State) (r : ForInStep PUnit × H.State)
    (h : inputBody H P logMax indices x () st = .ok r) :
    InputOkR H P logMax indices x ∧ r = (.yield (), st) := by
  unfold inputBody at h
  obtain ⟨hq, h⟩ := ensure_bind_eq_ok H h
  obtain ⟨hrows, h⟩ := ensure_bind_eq_ok H h
  obtain ⟨-, h⟩ := ensure_bind_eq_ok H h
  rw [bind_ok_of H (checkMulti_eq H _ _ _ _ _ _ st)] at h
  obtain ⟨hv, h⟩ := ensure_bind_eq_ok H h
  have hne : x.2.2 ≠ [] := by
    intro he
    simp only [he, List.map_nil, verifyMultiH, Merkle.verifyMultiM, Merkle.heightGroups,
      List.length_nil, List.range_zero, List.mergeSort_nil, List.foldr_nil] at hv
    exact Bool.false_ne_true hv
  set k := logBatch P x.2.2
  have hdims : (x.2.2.map fun (dp : Domain F × List (EF × List EF)) ↦
      (2 ^ (dp.1.logSize + P.logBlowup), (dp.2.headD default).2.length)).map (·.1) =
      roundHeights P x.2.2 := by
    rw [List.map_map]; rfl
  have hpowD : ∀ y ∈ (x.2.2.map fun (dp : Domain F × List (EF × List EF)) ↦
      (2 ^ (dp.1.logSize + P.logBlowup), (dp.2.headD default).2.length)), ∃ j ≤ k, y.1 = 2 ^ j := by
    intro y hy
    obtain ⟨⟨d, pts⟩, hdp, rfl⟩ := List.mem_map.mp hy
    exact ⟨_, (le_foldl_max _ 0).2 _
      (List.mem_map_of_mem (f := fun y : Domain F × List (EF × List EF) ↦
        y.1.logSize + P.logBlowup) hdp), rfl⟩
  have htopD : ∃ y ∈ (x.2.2.map fun (dp : Domain F × List (EF × List EF)) ↦
      (2 ^ (dp.1.logSize + P.logBlowup), (dp.2.headD default).2.length)), y.1 = 2 ^ k := by
    rcases foldl_max_mem (x.2.2.map (·.1.logSize + P.logBlowup)) 0 with h0 | h0
    · obtain ⟨⟨d, pts⟩, hdp⟩ := List.exists_mem_of_ne_nil _ hne
      have hle := (le_foldl_max _ 0).2 _ (List.mem_map_of_mem
        (f := fun y : Domain F × List (EF × List EF) ↦ y.1.logSize + P.logBlowup) hdp)
      have hk0 : k = 0 := h0
      refine ⟨_, List.mem_map_of_mem hdp, ?_⟩
      change 2 ^ (d.logSize + P.logBlowup) = 2 ^ k
      change d.logSize + P.logBlowup ≤ k at hle
      congr 1
      omega
    · obtain ⟨⟨d, pts⟩, hdp, he⟩ := List.mem_map.mp h0
      refine ⟨_, List.mem_map_of_mem hdp, ?_⟩
      change 2 ^ (d.logSize + P.logBlowup) = 2 ^ k
      rw [he]; rfl
  have hcap := Merkle.length_cap_of_verifyMulti_mixed H.hash H.compress x.2.1.toList P.capHeight k
    _ hpowD htopD _ _ _ hv
  rw [Array.length_toList] at hcap
  refine ⟨⟨hne, hcap, beq_iff_eq.mp hq, fun v hv' ↦ ?_, fun j hj ↦ ?_⟩, pure_eq_ok H h⟩
  · rw [Array.all_eq_true_iff_forall_mem] at hrows
    exact beq_iff_eq.mp (hrows v hv')
  · obtain ⟨path, hp⟩ := Merkle.verifyBatch_of_verifyMulti_mixed H.hash H.compress x.2.1.toList
      P.capHeight k _ hpowD htopD
      _ _ _ hv j (by rw [List.length_map]; exact hj)
    refine ⟨path, ?_⟩
    rw [show ∀ c, (x.2.2.map fun (dp : Domain F × List (EF × List EF)) ↦
        (2 ^ (dp.1.logSize + P.logBlowup), (dp.2.headD default).2.length)).map (·.1 / 2 ^ c) =
        (roundHeights P x.2.2).map (· / 2 ^ c) from fun c ↦ by
        rw [← hdims]; simp only [List.map_map, Function.comp_def]]
      at hp
    rw [← hp, List.getElem_map]
    congr 1
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getD_eq_getD_getElem?,
      ← Array.getElem?_toList]
    cases x.1.values.toList[j]? <;> rfl

/-- **An accepting `verifyInputs`** on rounds of any heights: a multi-opening per round, each
accepted. -/
theorem verifyInputs_okR (P : Params) (logMax : Nat) (indices : List Nat)
    (inputs : List (MultiOpening F)) (rounds : List (Round F EF)) (st : H.State)
    (r : Unit × H.State) (h : verifyInputs H P logMax indices inputs rounds st = .ok r) :
    inputs.length = rounds.length ∧ (∀ x ∈ inputs.zip rounds, InputOkR H P logMax indices x) ∧
      r = ((), st) := by
  unfold verifyInputs at h
  obtain ⟨hlen, h⟩ := ensure_bind_eq_ok H h
  obtain ⟨u, st', h1, h2⟩ := bind_eq_ok H h
  have hloop : ∀ (xs : List (MultiOpening F × Round F EF)) (st : H.State) (r : PUnit × H.State),
      forIn xs PUnit.unit (fun x _ ↦ inputBody H P logMax indices x ()) st = .ok r →
        (∀ x ∈ xs, InputOkR H P logMax indices x) ∧ r = ((), st) := by
    intro xs
    induction xs with
    | nil => intro st r h; rw [List.forIn_nil] at h; exact ⟨nofun, pure_eq_ok H h⟩
    | cons x xs ih =>
      intro st r h
      obtain ⟨step, st', h1, h2⟩ := forIn_cons_eq_ok H _ _ _ _ _ _ h
      obtain ⟨hok, hr⟩ := inputBody_okR H P logMax indices x st _ h1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
      obtain ⟨hl, hr⟩ := ih _ r h2
      exact ⟨fun y hy ↦ (List.mem_cons.mp hy).elim (fun e ↦ e ▸ hok) (hl y), hr⟩
  obtain ⟨hok, hr⟩ := hloop _ st _ h1
  obtain ⟨-, rfl⟩ := Prod.mk.inj hr
  exact ⟨beq_iff_eq.mp hlen, hok, pure_eq_ok H h2⟩

end Inputs

/-! ### FRI's verifier at mixed heights -/

section Heights
variable {EF : Type}

/-- The log heights of the rounds' matrices' extensions. -/
def matHeights (P : Params) (rounds : List (Round F EF)) : List Nat :=
  (rounds.flatMap (·.2)).map (·.1.logSize + P.logBlowup)

/-- A query's matrices, with a row each, have the rounds' heights. -/
theorem map_queryMats (P : Params) :
    ∀ (rows : List (List (Array F))) (rounds : List (Round F EF)),
      rows.length = rounds.length → (∀ x ∈ rows.zip rounds, x.1.length = x.2.2.length) →
      (queryMats (rows.zip rounds)).map (fun x ↦ x.2.1.logSize + P.logBlowup) =
        matHeights P rounds
  | [], [], _, _ => rfl
  | b :: rows, rd :: rounds, hl, hx => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have h1 := hx _ List.mem_cons_self
    have ih := map_queryMats P rows rounds hl fun y hy ↦ hx y (List.mem_cons_of_mem _ hy)
    simp only [queryMats, matHeights, List.zip_cons_cons, List.flatMap_cons, List.map_append]
      at ih ⊢
    rw [ih]
    congr 1
    dsimp only at h1
    clear ih hx
    induction b generalizing rd with
    | nil =>
      rcases rd with ⟨c, _ | ⟨m, ms⟩⟩
      · rfl
      · simp only [List.length_nil, List.length_cons] at h1; omega
    | cons a b ihb =>
      rcases rd with ⟨c, _ | ⟨m, ms⟩⟩
      · simp only [List.length_cons, List.length_nil] at h1; omega
      · simp only [List.length_cons, Nat.add_right_cancel_iff] at h1
        simp only [List.zip_cons_cons, List.map_cons]
        exact congrArg _ (ihb (c, ms) h1)

end Heights

section Fri
variable [BaseField F] {EF : Type} [Challenge F EF]

/-- Query `q` at `index` passes the verifier's checks on rounds of any heights: its input rows
open at `index`, its folds from the reduced opening of the largest height pass, adding every
shorter height's when they reach it, end at the final height, and match the final polynomial. -/
def QueryOkR (P : Params) (logMax : Nat) (alpha : EF) (rounds : List (Round F EF))
    (betas : List EF) (commits : List (Cap F)) (arities : List Nat)
    (folds : List (CommitOpening F EF)) (inputs : List (MultiOpening F)) (finalPoly : Array EF)
    (q index : Nat) : Prop :=
  let rows := inputs.map fun b ↦ (b.values.getD q #[]).toList
  let mats := queryMats (rows.zip rounds)
  let e0 := (reducedAt P logMax index alpha mats logMax).2
  let ro := (descHeights (matHeights P rounds)).tail.map fun h ↦
    (h, (reducedAt P logMax index alpha mats h).2)
  let l := betas.zip (querySteps q arities folds)
  let fin := foldStateR l (ro, e0, index, logMax) l.length
  rows.length = rounds.length ∧ (∀ x ∈ rows.zip rounds, BatchOkR H P logMax index x) ∧
    (∀ (j : Nat) (x : EF × QueryFold EF), l[j]? = some x →
      StepOk H P.capHeight (commits.getD j #[]) x (foldStateR l (ro, e0, index, logMax) j).2) ∧
    fin.2.2.2 = P.logBlowup + P.logFinalPolyLen ∧ fin.1 = [] ∧
    finalPoly.foldr (fun c acc ↦
      acc * Ext.ofBase (powF (twoAdicGen logMax) (reverseBits fin.2.2.1 logMax)) + c) 0 = fin.2.1

/-- A query that passes its checks opens every round's cap and every fold's at its size. -/
theorem size_caps_of_queryOkR (P : Params) (logMax : Nat) (alpha : EF)
    (rounds : List (Round F EF)) (betas : List EF) (commits : List (Cap F)) (arities : List Nat)
    (folds : List (CommitOpening F EF)) (inputs : List (MultiOpening F)) (finalPoly : Array EF)
    (q index : Nat) (hb : betas.length = arities.length) (hf : folds.length = arities.length)
    (h : QueryOkR H P logMax alpha rounds betas commits arities folds inputs finalPoly q index) :
    (∀ x ∈ rounds, x.2 ≠ [] ∧ x.1.size = 2 ^ min P.capHeight (logBatch P x.2)) ∧
      ∀ i < arities.length, (commits.getD i #[]).size =
        2 ^ min P.capHeight (logMax - (arities.take (i + 1)).sum) := by
  obtain ⟨hrl, hbatch, hsteps, -⟩ := h
  refine ⟨fun x hx ↦ ?_, fun i hi ↦ ?_⟩
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    have hk' : k < ((inputs.map fun b ↦ (b.values.getD q #[]).toList).zip rounds).length := by
      rw [List.length_zip, hrl, Nat.min_self]; exact hk
    have := hbatch _ (List.getElem_mem hk')
    rw [List.getElem_zip] at this
    exact ⟨this.1, this.2.1⟩
  · set l := betas.zip (querySteps q arities folds) with hl
    have hll : l.length = arities.length := by
      rw [hl, List.length_zip, hb, length_querySteps _ _ _ hf, Nat.min_self]
    have hli : i < l.length := by omega
    have hlar : l.map (·.2.logArity) = arities := by
      have hsnd : l.map Prod.snd = querySteps q arities folds :=
        List.map_snd_zip (by rw [hb, length_querySteps _ _ _ hf])
      rw [show (l.map fun x : EF × QueryFold EF ↦ x.2.logArity) =
        (l.map Prod.snd).map (·.logArity) by rw [List.map_map]; rfl, hsnd,
        map_logArity_querySteps _ _ _ hf]
    have hst := (hsteps i l[i] (List.getElem?_eq_getElem hli)).2.1
    rw [foldStateR_snd] at hst
    dsimp only at hst
    rw [hst, ← hlar, List.sum_take_succ _ _ (by rw [List.length_map]; exact hli),
      List.getElem_map, Nat.sub_sub, List.map_take]

theorem queryBody_okR (P : Params) (alpha : EF) (rounds : List (Round F EF))
    (betas : List EF) (arities : List Nat) (folds : List (CommitOpening F EF))
    (inputs : List (MultiOpening F)) (finalPoly : Array EF) (x : Nat × Nat)
    (hlen : (inputs.map fun b ↦ (b.values.getD x.2 #[]).toList).length = rounds.length)
    (hrows : ∀ y ∈ (inputs.map fun b ↦ (b.values.getD x.2 #[]).toList).zip rounds,
      y.1.length = y.2.2.length)
    (hne : matHeights P rounds ≠ [])
    (st : H.State) (r : List (Nat × List EF) × H.State)
    (h : queryBody H P ((descHeights (matHeights P rounds)).headD 0) alpha rounds betas arities
      folds inputs finalPoly x st = .ok r) :
    let logMax := (descHeights (matHeights P rounds)).headD 0
    let rows := inputs.map fun b ↦ (b.values.getD x.2 #[]).toList
    let mats := queryMats (rows.zip rounds)
    let e0 := (reducedAt P logMax x.1 alpha mats logMax).2
    let ro := (descHeights (matHeights P rounds)).tail.map fun h ↦
      (h, (reducedAt P logMax x.1 alpha mats h).2)
    let l := betas.zip (querySteps x.2 arities folds)
    let fin := foldStateR l (ro, e0, x.1, logMax) l.length
    (∀ y ∈ rows.zip rounds, ∀ z ∈ y.1.zip y.2.2, ∀ zy ∈ z.2.2, zy.2.length = z.1.size) ∧
      (∀ (j : Nat) (y : EF × QueryFold EF), l[j]? = some y →
        y.2.siblings.size = 2 ^ y.2.logArity - 1) ∧
      fin.2.2.2 = P.logBlowup + P.logFinalPolyLen ∧ fin.1 = [] ∧
      finalPoly.foldr (fun c acc ↦
        acc * Ext.ofBase (powF (twoAdicGen logMax) (reverseBits fin.2.2.1 logMax)) + c) 0 =
          fin.2.1 ∧
      r = (foldGroupsR l (ro, e0, x.1, logMax), st) := by
  intro logMax rows mats e0 ro l fin
  unfold queryBody at h
  obtain ⟨ro', st1, h1, hk1⟩ := bind_eq_ok H h
  obtain ⟨hw, hro⟩ := reduceQuery_okR H P logMax x.1 alpha _ rounds st _ h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hro
  have hmh := map_queryMats P rows rounds hlen hrows
  rw [hmh] at hk1
  obtain ⟨hd, tl, hds⟩ : ∃ hd tl, descHeights (matHeights P rounds) = hd :: tl := by
    cases hD : descHeights (matHeights P rounds) with
    | nil =>
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne
      have := (mem_descHeights _ a).mpr ha
      rw [hD] at this
      exact absurd this List.not_mem_nil
    | cons hd tl => exact ⟨hd, tl, rfl⟩
  have hlm : logMax = hd := by
    show (descHeights (matHeights P rounds)).headD 0 = hd
    rw [hds]
    rfl
  rw [hds, List.map_cons, ← hlm] at hk1
  obtain ⟨res, st2, h2, hk2⟩ := bind_eq_ok H hk1
  have hro_eq : ro = tl.map fun h ↦ (h, (reducedAt P logMax x.1 alpha mats h).2) := by
    simp only [ro, hds, List.tail_cons]
  rw [← hro_eq] at h2
  obtain ⟨hsib, hfin, hnil, hres⟩ := foldQuery_okR H P logMax x.1 x.2 betas arities folds _ _ _
    _ h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hres
  obtain ⟨hfp, hk3⟩ := ensure_bind_eq_ok H hk2
  exact ⟨hw, hsib, hfin, hnil, beq_iff_eq.mp hfp, pure_eq_ok H hk3⟩

/-- **An accepting FRI verifier** on rounds of any heights, after the batching challenge
`alpha`: the proof has Plonky3's shape for the fold schedule of the rounds' heights, the query
grinding witness checks, and every query passes its checks at the index it samples. -/
theorem verifyFri_okR (P : Params) (proof : FriProof F EF) (rounds : List (Round F EF))
    (alpha : EF) (s : H.State) (r : Unit × H.State)
    (h : verifyFri H P proof rounds alpha s = .ok r) :
    let hs := descHeights (matHeights P rounds)
    let logMax := hs.headD 0
    let ar := foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen) logMax hs
    let cr := commitReplay H P (proof.commits.toList.zip proof.commitWitnesses.toList)
      (obsList H s (DomainSeparator.friSeed F EF ar (2 ^ P.logFinalPolyLen) P.commitPowBits
        P.queryPowBits P.numQueries logMax P.logBlowup P.maxLogArity))
    let w := chkWit H P.queryPowBits proof.queryWitness (obsExts H cr.2 proof.finalPoly.toList)
    0 < P.numQueries ∧ 0 < P.maxLogArity ∧ matHeights P rounds ≠ [] ∧ logMax ≤ twoAdicity F ∧
      proof.folds.size = ar.length ∧ proof.commits.size = ar.length ∧
      proof.commitWitnesses.size = ar.length ∧ proof.finalPoly.size = 2 ^ P.logFinalPolyLen ∧
      w.1 = true ∧ cr.1.length = ar.length ∧
      ∀ j < P.numQueries, QueryOkR H P logMax alpha rounds cr.1 proof.commits.toList ar
        proof.folds.toList proof.inputs.toList proof.finalPoly j
        (smpBits H logMax (sampleStates H w.2 j)).1 := by
  intro hs logMax ar cr w
  unfold verifyFri at h
  obtain ⟨hpar, h⟩ := ensure_bind_eq_ok H h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpar
  obtain ⟨hany, h⟩ := ensure_bind_eq_ok H h
  have hne : matHeights P rounds ≠ [] := by
    simp only [List.any_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.isEmpty_eq_false_iff] at hany
    obtain ⟨r, hr, hne⟩ := hany
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hne
    exact List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_flatMap.mpr ⟨r, hr, hy⟩))
  dsimp only at h
  obtain ⟨hlt, h⟩ := ensure_bind_eq_ok H h
  simp only [decide_eq_true_eq] at hlt
  obtain ⟨hfolds, h⟩ := ensure_bind_eq_ok H h
  obtain ⟨-, h⟩ := ensure_bind_eq_ok H h
  obtain ⟨-, h⟩ := ensure_bind_eq_ok H h
  obtain ⟨-, h⟩ := ensure_bind_eq_ok H h
  obtain ⟨hfp, h⟩ := ensure_bind_eq_ok H h
  rw [bind_ok_of H (observeList_eq H _ s)] at h
  obtain ⟨hcs, h⟩ := ensure_bind_eq_ok H h
  simp only [Bool.and_eq_true, beq_iff_eq] at hcs
  replace hcs := hcs.1
  change proof.commits.size = ar.length ∧ proof.commitWitnesses.size = ar.length at hcs
  obtain ⟨betas, st1, h1, h⟩ := bind_eq_ok H h
  obtain ⟨hb1, hb2⟩ := commitLoop_ok H P _ (fun _ _ ↦ rfl) _ _ _ _ h1
  simp only at hb2
  subst hb2
  have hbetas : betas.toList = cr.1 := by rw [hb1]; rfl
  rw [bind_ok_of H (observeExts_eq H _ _),
    bind_ok_of H (checkWitness_eq H _ _ _)] at h
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
  obtain ⟨hinlen, hinok, hr3⟩ := verifyInputs_okR H P logMax _ _ rounds _ _ h3
  obtain ⟨-, rfl⟩ := Prod.mk.inj hr3
  have hidxlen : idx.length = N := by rw [hidx, List.length_map, List.length_range]
  -- every query's rows: one per matrix of every round
  have hrowsq : ∀ q < N, ∀ y ∈ (proof.inputs.toList.map fun b ↦ (b.values.getD q #[]).toList).zip
      rounds, y.1.length = y.2.2.length := by
    intro q hq y hy
    rw [List.zip_map_left] at hy
    obtain ⟨⟨b, rd⟩, hbr, rfl⟩ := List.mem_map.mp hy
    obtain ⟨-, -, hsz, hall, -⟩ := hinok _ hbr
    simp only [Prod.map, id, Array.length_toList]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hsz, hidxlen]; exact hq),
      Option.getD_some]
    exact hall _ (Array.getElem_mem _)
  have hlenq : ∀ q, (proof.inputs.toList.map fun b ↦ (b.values.getD q #[]).toList).length =
      rounds.length := fun q ↦ by rw [List.length_map, Array.length_toList]; exact hinlen
  obtain ⟨groups, st4, h4, h⟩ := bind_eq_ok H h
  obtain ⟨hst4, hglen, hg⟩ := mapM_eq_ok H (fun x ↦ queryBody H P logMax alpha rounds
    betas.toList ar proof.folds.toList proof.inputs.toList proof.finalPoly x) idx.zipIdx _ _
    (fun x hx s r hr ↦ by
      have hq : x.2 < N := by
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
        rw [List.getElem_zipIdx, Nat.zero_add]
        rw [List.length_zipIdx, hidxlen] at hk
        exact hk
      exact congrArg Prod.snd ((queryBody_okR H P alpha rounds _ ar _ _ _ x (hlenq _)
        (hrowsq _ hq) hne s r hr).2.2.2.2.2)) h4
  simp only at hst4
  subst hst4
  rw [List.length_zipIdx] at hglen
  obtain ⟨lh, st5, h5, h6⟩ := bind_eq_ok H h
  have hphase := phaseLoop_ok H P.capHeight groups _ (fun _ _ ↦ rfl) _ _ _ _ h5
  simp only [beq_iff_eq] at hfolds hfp
  change proof.folds.size = ar.length at hfolds
  have hcrlen : cr.1.length = ar.length := by
    rw [length_commitReplay, List.length_zip, Array.length_toList, Array.length_toList, hcs.1,
      hcs.2, Nat.min_self]
  have hflen : proof.folds.toList.length = ar.length := by rw [Array.length_toList, hfolds]
  refine ⟨hpar.1.1, hpar.2, hne, hlt, hfolds, hcs.1, hcs.2, hfp, hw, hcrlen, fun j hj ↦ ?_⟩
  have hjk : j < idx.zipIdx.length := by rw [List.length_zipIdx, hidxlen]; exact hj
  have hjg : j < groups.length := by rw [hglen, hidxlen]; exact hj
  have hq := hg j hjk hjg
  rw [List.getElem_zipIdx, Nat.zero_add, hbetas] at hq
  obtain ⟨hwid, hsib, hfin, hnil, hfinal, hres⟩ := queryBody_okR H P alpha rounds _ ar _ _ _
    (idx[j]'(by rw [hidxlen]; exact hj), j) (hlenq _) (hrowsq j hj) hne _ _ hq
  have hgj := congrArg Prod.fst hres
  dsimp only at hgj hwid hfin hfinal hnil
  have hidxj : idx[j]'(by rw [hidxlen]; exact hj) =
      (smpBits H logMax (sampleStates H w.2 j)).1 := by
    simp only [hidx, List.getElem_map, List.getElem_range]
  rw [hidxj] at hgj hfin hfinal hsib hnil
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
    fun i y hy ↦ ?_, hfin, hnil, hfinal⟩
  · -- the input rows
    have hx' := hx
    rw [List.zip_map_left] at hx'
    obtain ⟨⟨b, rd⟩, hbr, rfl⟩ := List.mem_map.mp hx'
    obtain ⟨hne', hcsz, hsz, hall, hpath⟩ := hinok _ hbr
    have hlen := hrowsq j hj _ hx
    obtain ⟨path, hp⟩ := hpath j (by rw [hidxlen]; exact hj)
    refine ⟨hne', hcsz, ⟨path, ?_⟩, hlen, hwid _ hx⟩
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
      rw [hxs, show (fun x : (Cap F × CommitOpening F EF) × Nat × Nat ↦ x.2.1) =
        Prod.fst ∘ Prod.snd from rfl, ← List.map_map, List.map_snd_zip (by
          rw [List.length_zip, List.length_zipIdx, hcl, hflen, Nat.min_self]),
        List.zipIdx_map_fst]
    have hsum : ((l.take i).map (·.2.logArity)).sum = ((xs.take i).map (·.2.1)).sum := by
      rw [List.map_take, List.map_take, hlar, hxsar]
    have hla : l[i].2.logArity = ar[i] := by
      have h1 : (l.map (·.2.logArity))[i]'(by rw [List.length_map]; exact hi) = ar[i] := by
        simp only [hlar]
      rwa [List.getElem_map] at h1
    have hv : let lh := logMax - ((xs.take i).map (·.2.1)).sum
        let gs := groups.map fun g ↦ g.getD xs[i].2.2 (0, [])
        verifyMultiH H xs[i].1.1 P.capHeight
          [(2 ^ (lh - xs[i].2.1), Challenge.d EF * 2 ^ xs[i].2.1)]
          (gs.map (·.1)) (gs.map fun (_, evals) ↦ [evals.flatMap Ext.coeffs])
          xs[i].1.2.path.toList = true := hphase i hxi
    rw [hxsi] at hv
    dsimp only at hv
    rw [← hsum, ← hla] at hv
    obtain ⟨path, hp⟩ := Merkle.verifyBatch_of_verifyMulti H.hash H.compress _ P.capHeight 1 _
      Nat.one_pos _ rfl _ _ _ hv j (by rw [List.length_map, List.length_map]; exact hjg)
    have hcap := Merkle.length_cap_of_verifyMulti_replicate H.hash H.compress _ P.capHeight 1 _
      Nat.one_pos _ rfl _ _ _ hv
    rw [Array.length_toList] at hcap
    set st0 := ((descHeights (matHeights P rounds)).tail.map fun h ↦
      (h, (reducedAt P logMax index alpha (queryMats ((proof.inputs.toList.map fun b ↦
        (b.values.getD j #[]).toList).zip rounds)) h).2),
      (reducedAt P logMax index alpha (queryMats ((proof.inputs.toList.map fun b ↦
        (b.values.getD j #[]).toList).zip rounds)) logMax).2, index, logMax)
    have hgi : (groups[j]'hjg).getD i (0, []) = foldGroup l[i] (foldStateR l st0 i).2 := by
      rw [hgj, List.getD_eq_getElem _ _ (by rw [length_foldGroupsR]; exact hi),
        getElem_foldGroupsR l _ i hi]
    have hst2 : (foldStateR l st0 i).2.2.2 = logMax - ((l.take i).map (·.2.logArity)).sum :=
      congrArg (·.2) (foldStateR_snd l _ _ _ _ i)
    rw [List.getD_eq_getElem _ _ (hcl ▸ hiar), hst2]
    rw [List.getD_eq_getElem _ [] (by rw [List.length_map, List.length_map]; exact hjg),
      List.getElem_map, List.getElem_map, List.getElem_map, List.getElem_map, hgi] at hp
    exact ⟨hcap, path, hp⟩

end Fri

end CompStark.Ni
