/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.ProgAlloc

/-! # The compiled programs compute the constraints

The schedule of `buildAll` computes the nodes in order, each item's after the earlier ones, and
accumulates each item's nodes after them (`SchedInv`), so it is a schedule the register
allocation runs correctly (`SchedOk`). Hence the compiled programs (`compile`, `compileExt`,
`compileOuts`), run on a row, accumulate their constraints' values with their weights and output
their expressions' values.
-/

@[expose] public section
namespace CompStark.Stark.Prog

variable {F : Type}

/-- The node steps among the first `t` steps. -/
def countNodes (steps : Array Step) : Nat → Nat
  | 0 => 0
  | t + 1 => countNodes steps t + match steps[t]? with
    | some (.node _) => 1
    | _ => 0

/-- A schedule built by `schedule`: every node step computes the next node, the node steps
compute the first `done` nodes, and every accumulation reads a node computed before it. -/
structure SchedInv (sc : Sched) : Prop where
  node : ∀ (t i : Nat), sc.steps[t]? = some (Step.node i) → i = countNodes sc.steps t
  total : countNodes sc.steps sc.steps.size = sc.done
  acc : ∀ (t i w : Nat), sc.steps[t]? = some (Step.acc i w) → i < countNodes sc.steps t

theorem countNodes_push (steps : Array Step) (x : Step) :
    ∀ t ≤ steps.size, countNodes (steps.push x) t = countNodes steps t
  | 0, _ => rfl
  | t + 1, ht => by
    simp only [countNodes]
    rw [countNodes_push steps x t (by omega), Array.getElem?_push, ite_eq_right (by omega)]

theorem countNodes_le (steps : Array Step) :
    ∀ t t', t ≤ t' → countNodes steps t ≤ countNodes steps t'
  | t, t', h => by
    induction t' with
    | zero => rw [Nat.le_zero.mp h]
    | succ t' ih =>
      rcases Nat.lt_or_ge t (t' + 1) with h' | h'
      · have := ih (by omega); simp only [countNodes]; omega
      · rw [Nat.le_antisymm h h']

theorem SchedInv.empty : SchedInv ⟨#[], 0⟩ :=
  ⟨fun t i h ↦ by simp only [Array.getElem?_empty, reduceCtorEq] at h, rfl,
    fun t i w h ↦ by simp only [Array.getElem?_empty, reduceCtorEq] at h⟩

/-- Pushing a step keeps the earlier steps. -/
theorem getElem?_push_lt (steps : Array Step) (x : Step) (t : Nat) (ht : t < steps.size) :
    (steps.push x)[t]? = steps[t]? := by
  rw [Array.getElem?_push, ite_eq_right (by omega)]

theorem SchedInv.push_node {sc : Sched} (h : SchedInv sc) :
    SchedInv ⟨sc.steps.push (.node sc.done), sc.done + 1⟩ := by
  refine ⟨fun t i ht ↦ ?_, ?_, fun t i w ht ↦ ?_⟩
  · simp only [Array.getElem?_push] at ht
    split at ht
    · rename_i e
      simp only [Option.some.injEq, Step.node.injEq] at ht
      subst e ht
      rw [countNodes_push _ _ _ (Nat.le_refl _), h.total]
    · rw [countNodes_push _ _ _ (by
        rcases Nat.lt_or_ge t sc.steps.size with h' | h'
        · omega
        · rw [Array.getElem?_eq_none h'] at ht; exact absurd ht (by simp only [reduceCtorEq,
            not_false_eq_true]))]
      exact h.node t i ht
  · simp only [Array.size_push, countNodes, Array.getElem?_push, ite_true]
    rw [countNodes_push _ _ _ (Nat.le_refl _), h.total]
  · simp only [Array.getElem?_push] at ht
    split at ht
    · simp only [Option.some.injEq, reduceCtorEq] at ht
    · have hlt : t < sc.steps.size := by
        rcases Nat.lt_or_ge t sc.steps.size with h' | h'
        · exact h'
        · rw [Array.getElem?_eq_none h'] at ht; exact absurd ht (by simp only [reduceCtorEq,
            not_false_eq_true])
      rw [countNodes_push _ _ _ (by omega)]
      exact h.acc t i w ht

theorem SchedInv.push_acc {sc : Sched} (h : SchedInv sc) (i w : Nat) (hi : i < sc.done) :
    SchedInv ⟨sc.steps.push (.acc i w), sc.done⟩ := by
  refine ⟨fun t j ht ↦ ?_, ?_, fun t j v ht ↦ ?_⟩
  · simp only [Array.getElem?_push] at ht
    split at ht
    · simp only [Option.some.injEq, reduceCtorEq] at ht
    · have hlt : t < sc.steps.size := by
        rcases Nat.lt_or_ge t sc.steps.size with h' | h'
        · exact h'
        · rw [Array.getElem?_eq_none h'] at ht; exact absurd ht (by simp only [reduceCtorEq,
            not_false_eq_true])
      rw [countNodes_push _ _ _ (by omega)]
      exact h.node t j ht
  · simp only [Array.size_push, countNodes, Array.getElem?_push, ite_true]
    rw [countNodes_push _ _ _ (Nat.le_refl _), h.total, Nat.add_zero]
  · simp only [Array.getElem?_push] at ht
    split at ht
    · rename_i e
      simp only [Option.some.injEq, Step.acc.injEq] at ht
      obtain ⟨rfl, -⟩ := ht
      subst e
      rw [countNodes_push _ _ _ (Nat.le_refl _), h.total]
      exact hi
    · have hlt : t < sc.steps.size := by
        rcases Nat.lt_or_ge t sc.steps.size with h' | h'
        · exact h'
        · rw [Array.getElem?_eq_none h'] at ht; exact absurd ht (by simp only [reduceCtorEq,
            not_false_eq_true])
      rw [countNodes_push _ _ _ (by omega)]
      exact h.acc t j v ht

/-- `schedule` keeps the invariant, its node steps computing all of `g`'s nodes. -/
theorem SchedInv.schedule [DecidableEq F] [Hashable F] [Field F] {sc : Sched} (h : SchedInv sc)
    (g : Dag F)
    (hd : sc.done ≤ g.nodes.size) (accs : List (Nat × Nat))
    (ha : ∀ p ∈ accs, p.1 < g.nodes.size) :
    SchedInv (schedule g accs sc) ∧ (schedule g accs sc).done = g.nodes.size := by
  obtain ⟨steps, done⟩ := sc
  dsimp only at hd
  unfold Prog.schedule
  dsimp only
  -- The node steps.
  have hn : ∀ m ≤ g.nodes.size - done, SchedInv ⟨(List.range' done m).foldl
      (fun s i ↦ s.push (.node i)) steps, done + m⟩ := by
    intro m hm
    induction m with
    | zero => exact h
    | succ m ih =>
      rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.one_mul,
        ← Nat.add_assoc]
      exact (ih (by omega)).push_node
  have h1 := hn (g.nodes.size - done) (Nat.le_refl _)
  rw [Nat.add_sub_cancel' hd] at h1
  generalize (List.range' done (g.nodes.size - done)).foldl _ steps = S at h1
  refine ⟨?_, rfl⟩
  -- The accumulations.
  suffices hacc : ∀ (l : List (Nat × Nat)) (S : Array Step), (∀ p ∈ l, p.1 < g.nodes.size) →
      SchedInv ⟨S, g.nodes.size⟩ →
      SchedInv ⟨l.foldl (fun s (i, w) ↦ if g.constAt i = some 0 then s else s.push (.acc i w)) S,
        g.nodes.size⟩ from hacc accs S ha h1
  intro l
  induction l with
  | nil => intro S _ hS; exact hS
  | cons p l ih =>
    intro S hl hS
    rw [List.foldl_cons]
    apply ih _ (fun q hq ↦ hl q (List.mem_cons_of_mem _ hq))
    obtain ⟨i, w⟩ := p
    dsimp only
    split
    · exact hS
    · exact hS.push_acc i w (hl (i, w) List.mem_cons_self)

/-- A node computed before step `t` is one of the first `countNodes t`. -/
theorem SchedInv.computed_iff {sc : Sched} (h : SchedInv sc) (t j : Nat) :
    Computed sc.steps t j ↔ j < countNodes sc.steps t := by
  constructor
  · rintro ⟨t', ht', hj⟩
    have := h.node t' j hj
    have hle := countNodes_le sc.steps (t' + 1) t ht'
    simp only [countNodes, hj] at hle
    omega
  · induction t with
    | zero => intro hj; exact absurd hj (Nat.not_lt_zero j)
    | succ t ih =>
      intro hj
      simp only [countNodes] at hj
      split at hj
      · rename_i i hi
        rcases Nat.lt_or_ge j (countNodes sc.steps t) with h' | h'
        · obtain ⟨t', h1, h2⟩ := ih h'
          exact ⟨t', by omega, h2⟩
        · have := h.node t i hi
          exact ⟨t, by omega, by rw [hi]; congr 2; omega⟩
      · obtain ⟨t', h1, h2⟩ := ih (by omega)
        exact ⟨t', by omega, h2⟩

/-- The node steps compute the nodes in order. -/
theorem SchedInv.node_lt {sc : Sched} (h : SchedInv sc) (t i : Nat)
    (hi : sc.steps[t]? = some (Step.node i)) : i < sc.done := by
  have ht : t < sc.steps.size := by
    rcases Nat.lt_or_ge t sc.steps.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hi; exact absurd hi (by simp only [reduceCtorEq,
        not_false_eq_true])
  have := h.node t i hi
  have hle := countNodes_le sc.steps (t + 1) sc.steps.size ht
  simp only [countNodes, hi, h.total] at hle
  omega

/-- A schedule built by `schedule` on a well-formed graph whose nodes it computes all, with
outputs among the nodes, is one the allocation runs. -/
theorem SchedInv.ok [DecidableEq F] [Hashable F] {sc : Sched} (h : SchedInv sc) (g : Dag F)
    (hg : g.Ok) (hd : sc.done = g.nodes.size) (outs : Array Nat)
    (ho : ∀ j ∈ outs, j < g.nodes.size) : SchedOk g.nodes sc.steps outs := by
  refine ⟨fun t i hi ↦ hd ▸ h.node_lt t i hi, fun t i hi hc ↦ ?_, fun t j hj ↦ ?_,
    fun i n hn ↦ hg.before i n hn⟩
  · rw [h.computed_iff] at hc
    have := h.node t i hi
    omega
  · unfold readsAt at hj
    split at hj
    · rename_i ht
      have hget : sc.steps[t]? = some sc.steps[t] := Array.getElem?_eq_getElem ht
      generalize sc.steps[t] = st at hj hget
      cases st with
      | node i =>
        have hi := h.node t i hget
        have hlt := h.node_lt t i hget
        simp only [Step.reads] at hj
        obtain ⟨n, hn⟩ : ∃ n, g.nodes[i]? = some n :=
          ⟨_, Array.getElem?_eq_getElem (by omega)⟩
        rw [hn] at hj
        cases n with
        | bin o a b =>
          have hb := hg.before i _ hn
          simp only [Option.map_some, Option.getD_some, Node.regArgs, List.mem_cons,
            List.not_mem_nil, or_false] at hj
          simp only [Node.Before] at hb
          rw [h.computed_iff]
          rcases hj with rfl | rfl <;> exact ⟨by omega, fun _ ↦ by omega⟩
        | _ => simp only [Option.map_some, Option.getD_some, Node.regArgs, List.not_mem_nil] at hj
      | acc i w =>
        simp only [Step.reads, List.mem_singleton] at hj
        subst hj
        have := h.acc t _ w hget
        have hle := countNodes_le sc.steps t sc.steps.size (by omega)
        rw [h.computed_iff]
        exact ⟨by rw [h.total, hd] at hle; omega, fun _ ↦ this⟩
    · split at hj
      · rename_i ht
        subst ht
        have := ho j (Array.mem_def.mpr hj)
        rw [h.computed_iff, h.total, hd]
        exact ⟨this, fun _ ↦ this⟩
      · exact absurd hj List.not_mem_nil

/-! ### Leaves of the programs -/

/-- A node's column satisfies `cq` and its load `lq`. -/
def Node.LeafOk (cq : Nat → Prop) (lq : Src → Prop) : Node F → Prop
  | .cur c => cq c
  | .load s => lq s
  | _ => True

/-- An operand's column satisfies `cq`. -/
def Opd.LeafOk (cq : Nat → Prop) : Opd F → Prop
  | .cur c => cq c
  | _ => True

/-- An instruction's columns satisfy `cq` and its load `lq`. -/
def Instr.LeafOk (cq : Nat → Prop) (lq : Src → Prop) : Instr F → Prop
  | .load _ s => lq s
  | .scalar _ _ => True
  | .bin _ _ a b => a.LeafOk cq ∧ b.LeafOk cq
  | .acc a _ => a.LeafOk cq

theorem Alloc.releaseLast_code (last : Array Nat) (t : Nat) :
    ∀ (js : List Nat) (s : Alloc F), (Alloc.releaseLast last t s js).code = s.code
  | [], _ => rfl
  | j :: js, s => by
    simp only [Alloc.releaseLast, List.foldl_cons]
    rw [← Alloc.releaseLast.eq_1, Alloc.releaseLast_code last t js]
    split
    · exact Alloc.release_code s j
    · rfl

theorem Alloc.opd_leafOk (nodes : Array (Node F)) (s : Alloc F) (j : Nat) (cq : Nat → Prop)
    (lq : Src → Prop) (hn : ∀ (i : Nat) (n : Node F), nodes[i]? = some n → n.LeafOk cq lq) :
    (Alloc.opd nodes s j).LeafOk cq := by
  unfold Alloc.opd
  split
  · rename_i c h; exact hn j _ h
  · trivial
  · trivial

/-- The allocation's outputs' leaves are the nodes'. -/
theorem allocate_outs_leafOk (nodes : Array (Node F)) (steps : Array Step) (outs : Array Nat)
    (cq : Nat → Prop) (lq : Src → Prop)
    (hn : ∀ (i : Nat) (n : Node F), nodes[i]? = some n → n.LeafOk cq lq) :
    ∀ o ∈ (allocate nodes steps outs).outs, o.LeafOk cq := by
  intro o ho
  simp only [allocate, Array.mem_map] at ho
  obtain ⟨i, -, rfl⟩ := ho
  unfold Alloc.opd
  split
  · rename_i c h
    exact hn i _ h
  · trivial
  · trivial

/-- The allocation emits instructions whose leaves are the nodes'. -/
theorem allocate_leafOk (nodes : Array (Node F)) (steps : Array Step) (outs : Array Nat)
    (cq : Nat → Prop) (lq : Src → Prop)
    (hn : ∀ (i : Nat) (n : Node F), nodes[i]? = some n → n.LeafOk cq lq) :
    ∀ ins ∈ (allocate nodes steps outs).code, ins.LeafOk cq lq := by
  have hstep : ∀ (s : Alloc F) (last : Array Nat) (t : Nat) (st : Step),
      (∀ ins ∈ s.code, ins.LeafOk cq lq) → ∀ ins ∈ (s.step nodes last t st).code,
        ins.LeafOk cq lq := by
    intro s last t st hs ins hm
    have hcomp : ∀ (i : Nat) (args : List Nat) (f : Nat → Instr F),
        (∀ r, (f r).LeafOk cq lq) → ins ∈ (Alloc.compute last t s i args f).code →
          ins.LeafOk cq lq := by
      intro i args f hf hm
      unfold Alloc.compute at hm
      dsimp only at hm
      split at hm
      · rw [Alloc.release_code] at hm
        rw [Alloc.emit_code, Alloc.take_code, Alloc.releaseLast_code] at hm
        rcases Array.mem_push.mp hm with hm | hm
        · exact hs ins hm
        · rw [hm]; exact hf _
      · rw [Alloc.emit_code, Alloc.take_code, Alloc.releaseLast_code] at hm
        rcases Array.mem_push.mp hm with hm | hm
        · exact hs ins hm
        · rw [hm]; exact hf _
    cases st with
    | node i =>
      simp only [Alloc.step] at hm
      split at hm
      · rename_i src h
        exact hcomp _ _ (fun r ↦ .load r src) (fun _ ↦ hn i _ h) hm
      · rename_i k h
        exact hcomp _ _ (fun r ↦ .scalar r k) (fun _ ↦ trivial) hm
      · rename_i o a b h
        exact hcomp _ _ (fun r ↦ .bin o r (Alloc.opd nodes s a) (Alloc.opd nodes s b))
          (fun _ ↦ ⟨Alloc.opd_leafOk nodes s _ cq lq hn, Alloc.opd_leafOk nodes s _ cq lq hn⟩) hm
      · exact hs ins hm
    | acc i w =>
      unfold Alloc.step at hm
      rw [Alloc.releaseLast_code, Alloc.emit_code] at hm
      rcases Array.mem_push.mp hm with hm | hm
      · exact hs ins hm
      · rw [hm]; exact Alloc.opd_leafOk nodes s _ cq lq hn
  unfold allocate
  dsimp only
  generalize List.range steps.size = l
  suffices h : ∀ (l : List Nat) (s : Alloc F), (∀ ins ∈ s.code, ins.LeafOk cq lq) →
      ∀ ins ∈ (l.foldl (fun s t ↦ s.step nodes (outs.foldl (fun l j ↦ l.set! j steps.size)
        (lastUses nodes steps)) t steps[t]!) s).code, ins.LeafOk cq lq from
    h l _ fun ins hm ↦ absurd hm (by simp only [Array.not_mem_empty, not_false_eq_true])
  intro l
  induction l with
  | nil => intro s hs; exact hs
  | cons t l ih => intro s hs; exact ih _ (hstep s _ t _ hs)

/-- A loaded column lies below the widths: the trace's next row below `wn`, the preprocessed
trace's below `pw` and `pwn`, the permutation trace's below `rw`. -/
def Src.Below (wn pw pwn rw : Nat) : Src → Prop
  | .next c => c < wn
  | .prepCur c => c < pw
  | .prepNext c => c < pwn
  | .permCur c | .permNext c => c < rw
  | _ => True

theorem colsBelow_pubBelow [Field F] (np w wn pw pwn : Nat) :
    ∀ e : Expr F, (Dag.pubBelow np e).colsBelow w wn pw pwn = e.colsBelow w wn pw pwn
  | .add a b => by
    rw [Dag.pubBelow, Expr.colsBelow, Expr.colsBelow, colsBelow_pubBelow np w wn pw pwn a,
      colsBelow_pubBelow np w wn pw pwn b]
  | .sub a b => by
    rw [Dag.pubBelow, Expr.colsBelow, Expr.colsBelow, colsBelow_pubBelow np w wn pw pwn a,
      colsBelow_pubBelow np w wn pw pwn b]
  | .mul a b => by
    rw [Dag.pubBelow, Expr.colsBelow, Expr.colsBelow, colsBelow_pubBelow np w wn pw pwn a,
      colsBelow_pubBelow np w wn pw pwn b]
  | .pub j => by
    simp only [Dag.pubBelow]
    split <;> rfl
  | .cur _ | .next _ | .prepCur _ | .prepNext _ | .periodic _ | .const _ | .isFirstRow
  | .isLastRow | .isTransition => rfl

section LeafDag
variable [DecidableEq F] [Hashable F]

/-- Every node's column satisfies `cq` and its load `lq`. -/
def Dag.LeafOk (cq : Nat → Prop) (lq : Src → Prop) (g : Dag F) : Prop :=
  ∀ (i : Nat) (n : Node F), g.nodes[i]? = some n → n.LeafOk cq lq

theorem Dag.intern_leafOk {cq : Nat → Prop} {lq : Src → Prop} (g : Dag F) (h : g.LeafOk cq lq)
    (n : Node F) (hn : n.LeafOk cq lq) : (g.intern n).1.LeafOk cq lq := by
  unfold Dag.intern
  split
  · exact h
  · obtain ⟨nodes, index⟩ := g
    intro i m hm
    dsimp only at hm
    rw [Array.getElem?_push] at hm
    split at hm
    · simp only [Option.some.injEq] at hm; subst hm; exact hn
    · exact h i m hm

theorem Dag.op_leafOk [Field F] {cq : Nat → Prop} {lq : Src → Prop} (g : Dag F)
    (h : g.LeafOk cq lq) (o : Op) (a b : Nat) : (g.op o a b).1.LeafOk cq lq := by
  unfold Dag.op
  split <;> (try split) <;> (try split) <;>
    first
    | exact h
    | exact g.intern_leafOk h _ trivial

theorem Dag.ofExpr_leafOk [Field F] {w wn pw pwn rw : Nat} (e : Expr F)
    (he : e.colsBelow w wn pw pwn = true) (g : Dag F)
    (h : g.LeafOk (· < w) (Src.Below wn pw pwn rw)) :
    (Dag.ofExpr e g).1.LeafOk (· < w) (Src.Below wn pw pwn rw) := by
  induction e generalizing g with
  | add a b iha ihb =>
    simp only [Expr.colsBelow, Bool.and_eq_true] at he
    exact Dag.op_leafOk _ (ihb he.2 _ (iha he.1 g h)) _ _ _
  | sub a b iha ihb =>
    simp only [Expr.colsBelow, Bool.and_eq_true] at he
    exact Dag.op_leafOk _ (ihb he.2 _ (iha he.1 g h)) _ _ _
  | mul a b iha ihb =>
    simp only [Expr.colsBelow, Bool.and_eq_true] at he
    exact Dag.op_leafOk _ (ihb he.2 _ (iha he.1 g h)) _ _ _
  | cur c =>
    simp only [Expr.colsBelow, decide_eq_true_eq] at he
    exact g.intern_leafOk h _ he
  | next c =>
    simp only [Expr.colsBelow, decide_eq_true_eq] at he
    exact g.intern_leafOk h (.load (.next c)) he
  | prepCur c =>
    simp only [Expr.colsBelow, decide_eq_true_eq] at he
    exact g.intern_leafOk h (.load (.prepCur c)) he
  | prepNext c =>
    simp only [Expr.colsBelow, decide_eq_true_eq] at he
    exact g.intern_leafOk h (.load (.prepNext c)) he
  | periodic i => exact g.intern_leafOk h (.load (.periodic i)) trivial
  | pub i => exact g.intern_leafOk h (.scalar i) trivial
  | const x => exact g.intern_leafOk h (.const x) trivial
  | isFirstRow => exact g.intern_leafOk h (.load .isFirstRow) trivial
  | isLastRow => exact g.intern_leafOk h (.load .isLastRow) trivial
  | isTransition => exact g.intern_leafOk h (.load .isTransition) trivial

theorem Dag.ofTree_leafOk [Field F] {cq : Nat → Prop} {lq : Src → Prop} :
    ∀ (t : Dag.Tree) (g : Dag F), g.LeafOk cq lq → (g.ofTree t).1.LeafOk cq lq
  | .leaf _, _, h => h
  | .op o a b, g, h => by
    simp only [Dag.ofTree]
    exact Dag.op_leafOk _ (Dag.ofTree_leafOk b _ (Dag.ofTree_leafOk a g h)) _ _ _

theorem Dag.ofExt_leafOk [Field F] {w wn pw pwn pmw rw : Nat} (W : F) (np : Nat)
    (hrw : 4 * pmw ≤ rw) (e : Lookup.ExtExpr F) (he : e.colsBelow w wn pw pwn pmw = true)
    (g : Dag F) (h : g.LeafOk (· < w) (Src.Below wn pw pwn rw)) :
    (Dag.ofExt W np e g).1.LeafOk (· < w) (Src.Below wn pw pwn rw) := by
  induction e generalizing g with
  | base e =>
    simp only [Dag.ofExt]
    exact Dag.intern_leafOk _ (Dag.ofExpr_leafOk _ (by rwa [colsBelow_pubBelow]) g h) (.const 0)
      trivial
  | perm c =>
    simp only [Lookup.ExtExpr.colsBelow, decide_eq_true_eq] at he
    simp only [Dag.ofExt]
    refine Dag.intern_leafOk _ (Dag.intern_leafOk _ (Dag.intern_leafOk _
      (Dag.intern_leafOk _ h _ ?_) _ ?_) _ ?_) _ ?_ <;>
      simp only [Node.LeafOk, Src.Below] <;> omega
  | permNext c =>
    simp only [Lookup.ExtExpr.colsBelow, decide_eq_true_eq] at he
    simp only [Dag.ofExt]
    refine Dag.intern_leafOk _ (Dag.intern_leafOk _ (Dag.intern_leafOk _
      (Dag.intern_leafOk _ h _ ?_) _ ?_) _ ?_) _ ?_ <;>
      simp only [Node.LeafOk, Src.Below] <;> omega
  | challenge i =>
    simp only [Dag.ofExt]
    exact Dag.intern_leafOk _ (Dag.intern_leafOk _ (Dag.intern_leafOk _
      (Dag.intern_leafOk _ h (.scalar _) trivial) (.scalar _) trivial) (.scalar _) trivial)
      (.scalar _) trivial
  | terminal =>
    simp only [Dag.ofExt]
    exact Dag.intern_leafOk _ (Dag.intern_leafOk _ (Dag.intern_leafOk _
      (Dag.intern_leafOk _ h (.scalar _) trivial) (.scalar _) trivial) (.scalar _) trivial)
      (.scalar _) trivial
  | add a b iha ihb =>
    simp only [Lookup.ExtExpr.colsBelow, Bool.and_eq_true] at he
    simp only [Dag.ofExt, Dag.op4]
    exact Dag.op_leafOk _ (Dag.op_leafOk _ (Dag.op_leafOk _ (Dag.op_leafOk _
      (ihb he.2 _ (iha he.1 g h)) _ _ _) _ _ _) _ _ _) _ _ _
  | sub a b iha ihb =>
    simp only [Lookup.ExtExpr.colsBelow, Bool.and_eq_true] at he
    simp only [Dag.ofExt, Dag.op4]
    exact Dag.op_leafOk _ (Dag.op_leafOk _ (Dag.op_leafOk _ (Dag.op_leafOk _
      (ihb he.2 _ (iha he.1 g h)) _ _ _) _ _ _) _ _ _) _ _ _
  | mul a b iha ihb =>
    simp only [Lookup.ExtExpr.colsBelow, Bool.and_eq_true] at he
    simp only [Dag.ofExt, Dag.mul4]
    exact Dag.ofTree_leafOk _ _ (Dag.ofTree_leafOk _ _ (Dag.ofTree_leafOk _ _
      (Dag.ofTree_leafOk _ _ (Dag.intern_leafOk _ (ihb he.2 _ (iha he.1 g h)) (.const W)
        trivial))))

end LeafDag

/-! ### Accumulations of a schedule -/

section Acc
variable [Field F] (ctx : Ctx F)

theorem accTo_push (nodes : Array (Node F)) (steps : Array Step) (x : Step) (a0 : Nat → F) :
    ∀ t ≤ steps.size, accTo ctx nodes (steps.push x) a0 t = accTo ctx nodes steps a0 t
  | 0, _ => rfl
  | t + 1, ht => by
    simp only [accTo]
    rw [getElem?_push_lt _ _ _ (by omega), accTo_push nodes steps x a0 t (by omega)]

theorem accTo_push_node (nodes : Array (Node F)) (steps : Array Step) (i : Nat) (a0 : Nat → F) :
    accTo ctx nodes (steps.push (.node i)) a0 (steps.size + 1) =
      accTo ctx nodes steps a0 steps.size := by
  simp only [accTo, Array.getElem?_push, ite_true]
  rw [accTo_push _ _ _ _ _ _ (Nat.le_refl _)]

theorem accTo_push_acc (nodes : Array (Node F)) (steps : Array Step) (i w : Nat) (a0 : Nat → F) :
    accTo ctx nodes (steps.push (.acc i w)) a0 (steps.size + 1) =
      fun k ↦ accTo ctx nodes steps a0 steps.size k + val ctx nodes i * ctx.weight w k := by
  simp only [accTo, Array.getElem?_push, ite_true]
  rw [accTo_push _ _ _ _ _ _ (Nat.le_refl _)]

/-- The accumulations depend on the nodes they read only. -/
theorem accTo_congr (nodes nodes' : Array (Node F)) (steps : Array Step) (a0 : Nat → F) (N : Nat)
    (hn : ∀ j < N, nodes'[j]? = nodes[j]?)
    (ha : ∀ (t i w : Nat), steps[t]? = some (Step.acc i w) → i < N) :
    ∀ t, accTo ctx nodes' steps a0 t = accTo ctx nodes steps a0 t
  | 0 => rfl
  | t + 1 => by
    simp only [accTo]
    split
    · rename_i i w hi
      rw [accTo_congr nodes nodes' steps a0 N hn ha t,
        val_congr ctx nodes nodes' N hn i (ha t i w hi)]
    · rw [accTo_congr nodes nodes' steps a0 N hn ha t]

/-- `schedule` accumulates the accumulations' nodes with their weights, a constant zero
skipped. -/
theorem accTo_schedule [DecidableEq F] [Hashable F] (sc : Sched) (g : Dag F) (hg : g.Ok)
    (accs : List (Nat × Nat)) (a0 : Nat → F) (nodes : Array (Node F))
    (hn : ∀ j < g.nodes.size, nodes[j]? = g.nodes[j]?)
    (ha : ∀ p ∈ accs, p.1 < g.nodes.size) :
    accTo ctx nodes (schedule g accs sc).steps a0 (schedule g accs sc).steps.size =
      fun k ↦ accs.foldl (fun s p ↦ s + val ctx g.nodes p.1 * ctx.weight p.2 k)
        (accTo ctx nodes sc.steps a0 sc.steps.size k) := by
  obtain ⟨steps, done⟩ := sc
  unfold Prog.schedule
  dsimp only
  have hnodes : ∀ (l : List Nat) (S : Array Step),
      accTo ctx nodes (l.foldl (fun s i ↦ s.push (.node i)) S) a0
        (l.foldl (fun s i ↦ s.push (.node i)) S).size = accTo ctx nodes S a0 S.size := by
    intro l
    induction l with
    | nil => intro S; rfl
    | cons i l ih =>
      intro S
      rw [List.foldl_cons, ih, Array.size_push, accTo_push_node]
  have hS := hnodes (List.range' done (g.nodes.size - done)) steps
  generalize (List.range' done (g.nodes.size - done)).foldl _ steps = S at hS ⊢
  rw [← hS]
  clear hS
  induction accs generalizing S with
  | nil => rfl
  | cons p accs ih =>
    simp only [List.foldl_cons]
    obtain ⟨i, w⟩ := p
    dsimp only
    split
    · rename_i h0
      rw [ih (fun q hq ↦ ha q (List.mem_cons_of_mem _ hq)) S]
      funext k
      rw [g.constAt_val hg i 0 h0 ctx, zero_mul, add_zero]
    · rw [ih (fun q hq ↦ ha q (List.mem_cons_of_mem _ hq)) _, Array.size_push, accTo_push_acc,
        val_congr ctx g.nodes nodes g.nodes.size hn i (ha (i, w) List.mem_cons_self)]

end Acc

/-! ### Building all items -/

section BuildAll
variable [DecidableEq F] [Hashable F] [Field F]

/-- The invariant of building items: a well-formed graph, a schedule computing all its nodes, and
accumulations `T` read on any nodes extending the graph's. -/
def BuildInv (g : Dag F) (sc : Sched) (T : Ctx F → (Nat → F) → Nat → F) : Prop :=
  g.Ok ∧ SchedInv sc ∧ sc.done = g.nodes.size ∧ ∀ (nodes : Array (Node F)),
    (∀ j < g.nodes.size, nodes[j]? = g.nodes[j]?) →
      ∀ ctx a0 j, accTo ctx nodes sc.steps a0 sc.steps.size j = T ctx a0 j

theorem build_step {α : Type} (f : Nat → α → Dag F → Dag F × List (Nat × Nat))
    (spec : Nat → α → Ctx F → Nat → F)
    (hf : ∀ k x g, g.Ok → (f k x g).1.Ok ∧ g.Ext (f k x g).1 ∧
      (∀ p ∈ (f k x g).2, p.1 < (f k x g).1.nodes.size) ∧
      ∀ ctx j s, (f k x g).2.foldl (fun s p ↦ s + val ctx (f k x g).1.nodes p.1 * ctx.weight p.2 j)
        s = s + spec k x ctx j)
    (k : Nat) (x : α) {g : Dag F} {sc : Sched} {T : Ctx F → (Nat → F) → Nat → F}
    (h : BuildInv g sc T) :
    BuildInv (f k x g).1 (schedule (f k x g).1 (f k x g).2 sc)
      fun ctx a0 j ↦ T ctx a0 j + spec k x ctx j := by
  obtain ⟨hg, hs, hd, hT⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := hf k x g hg
  obtain ⟨hs', hd'⟩ := hs.schedule (f k x g).1 (by rw [hd]; exact h2.1) _ h3
  refine ⟨h1, hs', hd', fun nodes hn ctx a0 j ↦ ?_⟩
  rw [accTo_schedule ctx sc _ h1 _ a0 nodes hn h3]
  dsimp only
  rw [hT nodes (fun i hi ↦ by rw [hn i (by have := h2.1; omega), h2.2 i hi]) ctx a0 j, h4]

theorem buildAll_spec {α : Type} (f : Nat → α → Dag F → Dag F × List (Nat × Nat))
    (spec : Nat → α → Ctx F → Nat → F)
    (hf : ∀ k x g, g.Ok → (f k x g).1.Ok ∧ g.Ext (f k x g).1 ∧
      (∀ p ∈ (f k x g).2, p.1 < (f k x g).1.nodes.size) ∧
      ∀ ctx j s, (f k x g).2.foldl (fun s p ↦ s + val ctx (f k x g).1.nodes p.1 * ctx.weight p.2 j)
        s = s + spec k x ctx j)
    (xs : List α) :
    BuildInv (buildAll f xs).1 (buildAll f xs).2
      fun ctx a0 j ↦ (xs.zipIdx.map fun (x, k) ↦ spec k x ctx j).foldl (· + ·) (a0 j) := by
  suffices hgen : ∀ (xs : List α) (g : Dag F) (sc : Sched) (k : Nat)
      (T : Ctx F → (Nat → F) → Nat → F), BuildInv g sc T →
      BuildInv (xs.foldl (fun (g, sc, k) x ↦
          let (g, accs) := f k x g
          (g, schedule g accs sc, k + 1)) (g, sc, k)).1
        (xs.foldl (fun (g, sc, k) x ↦
          let (g, accs) := f k x g
          (g, schedule g accs sc, k + 1)) (g, sc, k)).2.1
        fun ctx a0 j ↦ ((xs.zipIdx k).map fun (x, i) ↦ spec i x ctx j).foldl (· + ·)
          (T ctx a0 j) by
    exact hgen xs Dag.empty ⟨#[], 0⟩ 0 (fun _ a0 j ↦ a0 j)
      ⟨Dag.empty_ok, SchedInv.empty, rfl, fun _ _ _ _ _ ↦ rfl⟩
  intro xs
  induction xs with
  | nil => intro g sc k T h; exact h
  | cons x xs ih =>
    intro g sc k T h
    rw [List.foldl_cons]
    have := ih _ _ (k + 1) _ (build_step f spec hf k x h)
    simp only [List.zipIdx_cons, List.map_cons, List.foldl_cons]
    exact this

end BuildAll

/-! ### The compiled programs -/

section Compiled
variable [DecidableEq F] [Hashable F] [Field F]

/-- **The compiled constraints**: on a row, the program accumulates `∑ₖ cₖ · weight k` and its
registers are below its count. -/
theorem compile_run (cs : List (Expr F)) (ctx : Ctx F) (st0 : St F) :
    (run (fieldMachine ctx) (compile cs).code st0).acc = (fun j ↦
      (cs.zipIdx.map fun (c, k) ↦ c.eval ctx.env * ctx.weight k j).foldl (· + ·) (st0.acc j)) ∧
    ∀ ins ∈ (compile cs).code, ins.RegsLt (compile cs).regs := by
  have hb := buildAll_spec (fun k c g ↦ ((Dag.ofExpr c g).1, [((Dag.ofExpr c g).2, k)]))
    (fun k c ctx j ↦ c.eval ctx.env * ctx.weight k j) (fun k c g hg ↦ by
      have b := Dag.ofExpr_built c g hg
      refine ⟨b.ok, b.ext, fun p hp ↦ ?_, fun ctx j s ↦ ?_⟩
      · simp only [List.mem_singleton] at hp; subst hp; exact b.lt
      · simp only [List.foldl_cons, List.foldl_nil]; rw [b.value]) cs
  have hc : compile cs = allocate (buildAll (fun k c g ↦ ((Dag.ofExpr c g).1,
      [((Dag.ofExpr c g).2, k)])) cs).1.nodes (buildAll (fun k c g ↦ ((Dag.ofExpr c g).1,
      [((Dag.ofExpr c g).2, k)])) cs).2.steps #[] := rfl
  rw [hc]
  generalize buildAll (F := F) (fun k c g ↦ ((Dag.ofExpr c g).1, [((Dag.ofExpr c g).2, k)])) cs =
    r at hb ⊢
  obtain ⟨hg, hs, hd, hT⟩ := hb
  obtain ⟨a, -, w⟩ := allocate_run ctx r.1.nodes r.2.steps #[]
    (hs.ok r.1 hg hd #[] fun j hj ↦ absurd hj (by simp only [Array.not_mem_empty,
      not_false_eq_true])) st0
  refine ⟨?_, w⟩
  rw [a]
  funext j
  exact hT r.1.nodes (fun _ _ ↦ rfl) ctx st0.acc j

/-- An extension value's coordinates weighted by `weight (4 k + i)`. -/
def extTerm (ctx : Ctx F) {W : F} (k : Nat) (v : Coords F W) (j : Nat) : F :=
  v.c0 * ctx.weight (4 * k) j + v.c1 * ctx.weight (4 * k + 1) j +
    v.c2 * ctx.weight (4 * k + 2) j + v.c3 * ctx.weight (4 * k + 3) j

/-- **The compiled extension constraints** over `X⁴ = W` with `np` public values: on a row, the
program accumulates every constraint's coordinates `i` with the weights `4 k + i`, and its
registers are below its count. -/
theorem compileExt_run (W : F) (np : Nat) (cs : List (Lookup.ExtExpr F)) (ctx : Ctx F)
    (st0 : St F) :
    (run (fieldMachine ctx) (compileExt W np cs).code st0).acc = (fun j ↦
      (cs.zipIdx.map fun (c, k) ↦ extTerm ctx k (c.eval (ctx.envQ W np) (ctx.auxQ W np)) j).foldl
        (· + ·) (st0.acc j)) ∧
    ∀ ins ∈ (compileExt W np cs).code, ins.RegsLt (compileExt W np cs).regs := by
  let f : Nat → Lookup.ExtExpr F → Dag F → Dag F × List (Nat × Nat) := fun k c g ↦
    ((Dag.ofExt W np c g).1, [((Dag.ofExt W np c g).2.1, 4 * k),
      ((Dag.ofExt W np c g).2.2.1, 4 * k + 1), ((Dag.ofExt W np c g).2.2.2.1, 4 * k + 2),
      ((Dag.ofExt W np c g).2.2.2.2, 4 * k + 3)])
  have hb := buildAll_spec f
    (fun k c ctx j ↦ extTerm ctx k (c.eval (ctx.envQ W np) (ctx.auxQ W np)) j) (fun k c g hg ↦ by
      have b := Dag.ofExt_built W np c g hg
      refine ⟨b.ok, b.ext, fun p hp ↦ ?_, fun ctx j s ↦ ?_⟩
      · simp only [f, List.mem_cons, List.not_mem_nil, or_false] at hp
        obtain ⟨l0, l1, l2, l3⟩ := b.lt
        rcases hp with rfl | rfl | rfl | rfl <;> assumption
      · simp only [f, List.foldl_cons, List.foldl_nil]
        rw [← b.value ctx]
        simp only [extTerm]
        ring) cs
  have hc : compileExt W np cs = allocate (buildAll f cs).1.nodes (buildAll f cs).2.steps #[] :=
    rfl
  rw [hc]
  generalize buildAll f cs = r at hb ⊢
  obtain ⟨hg, hs, hd, hT⟩ := hb
  obtain ⟨a, -, w⟩ := allocate_run ctx r.1.nodes r.2.steps #[]
    (hs.ok r.1 hg hd #[] fun j hj ↦ absurd hj (by simp only [Array.not_mem_empty,
      not_false_eq_true])) st0
  refine ⟨?_, w⟩
  rw [a]
  funext j
  exact hT r.1.nodes (fun _ _ ↦ rfl) ctx st0.acc j

/-- Building expressions one after another: their nodes in order after the given ones. -/
theorem foldl_ofExpr (l : List (Expr F)) :
    ∀ (g : Dag F) (outs : Array Nat), g.Ok →
      let r := l.foldl (fun (gs : Dag F × Array Nat) e ↦
        ((Dag.ofExpr e gs.1).1, gs.2.push (Dag.ofExpr e gs.1).2)) (g, outs)
      r.1.Ok ∧ g.Ext r.1 ∧ r.2.size = outs.size + l.length ∧
        (∀ k < outs.size, r.2.getD k 0 = outs.getD k 0) ∧
        ∀ k (hk : k < l.length), r.2.getD (outs.size + k) 0 < r.1.nodes.size ∧
          ∀ ctx, val ctx r.1.nodes (r.2.getD (outs.size + k) 0) = l[k].eval ctx.env := by
  induction l with
  | nil =>
    intro g outs hg
    exact ⟨hg, Dag.Ext.refl g, rfl, fun _ _ ↦ rfl, fun k hk ↦ absurd hk (Nat.not_lt_zero k)⟩
  | cons e l ih =>
    intro g outs hg
    have b := Dag.ofExpr_built e g hg
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih (Dag.ofExpr e g).1 (outs.push (Dag.ofExpr e g).2) b.ok
    rw [List.foldl_cons]
    dsimp only at h1 h2 h3 h4 h5 ⊢
    refine ⟨h1, b.ext.trans h2, by rw [h3, Array.size_push, List.length_cons]; omega,
      fun k hk ↦ ?_, fun k hk ↦ ?_⟩
    · rw [h4 k (by rw [Array.size_push]; omega), Alloc.getD_push, ite_eq_right (by omega)]
    · rcases k with _ | k
      · rw [Nat.add_zero, h4 _ (by rw [Array.size_push]; omega), Alloc.getD_push, ite_eq_left rfl]
        refine ⟨by have := h2.1; have := b.lt; omega, fun ctx ↦ ?_⟩
        rw [b.mono h2 ctx]
        rfl
      · have := h5 k (by simp only [List.length_cons] at hk; omega)
        rw [Array.size_push, show outs.size + 1 + k = outs.size + (k + 1) by omega] at this
        exact this

/-- **The compiled outputs**: on a row, output `k` of the program is expression `k`'s value, and
its registers are below its count. -/
theorem compileOuts_run (es : List (Expr F)) (ctx : Ctx F) (st0 : St F) :
    (compileOuts es).outs.size = es.length ∧ (∀ k (hk : k < es.length),
      ((compileOuts es).outs.getD k (.reg 0)).val ctx
        (run (fieldMachine ctx) (compileOuts es).code st0) = es[k].eval ctx.env ∧
      ((compileOuts es).outs.getD k (.reg 0)).RegsLt (compileOuts es).regs) ∧
    ∀ ins ∈ (compileOuts es).code, ins.RegsLt (compileOuts es).regs := by
  obtain ⟨hg, -, hsz, -, hv⟩ := foldl_ofExpr es Dag.empty #[] Dag.empty_ok
  have hc : compileOuts es = allocate (es.foldl (fun (gs : Dag F × Array Nat) e ↦
      ((Dag.ofExpr e gs.1).1, gs.2.push (Dag.ofExpr e gs.1).2)) (Dag.empty, #[])).1.nodes
      (schedule (es.foldl (fun (gs : Dag F × Array Nat) e ↦
        ((Dag.ofExpr e gs.1).1, gs.2.push (Dag.ofExpr e gs.1).2)) (Dag.empty, #[])).1 []
        ⟨#[], 0⟩).steps
      (es.foldl (fun (gs : Dag F × Array Nat) e ↦
        ((Dag.ofExpr e gs.1).1, gs.2.push (Dag.ofExpr e gs.1).2)) (Dag.empty, #[])).2 := rfl
  rw [hc]
  generalize es.foldl (fun (gs : Dag F × Array Nat) e ↦
    ((Dag.ofExpr e gs.1).1, gs.2.push (Dag.ofExpr e gs.1).2)) (Dag.empty, #[]) = r at hg hsz hv ⊢
  simp only [Array.size_empty, Nat.zero_add] at hsz hv
  obtain ⟨hs, hd⟩ := SchedInv.empty.schedule r.1 (Nat.zero_le _) [] fun p hp ↦
    absurd hp List.not_mem_nil
  have ho : ∀ j ∈ r.2, j < r.1.nodes.size := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hj
    have := (hv k (by omega)).1
    rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some] at this
  obtain ⟨-, o, w⟩ := allocate_run ctx r.1.nodes _ r.2 (hs.ok r.1 hg hd r.2 ho) st0
  refine ⟨by simp only [allocate, Array.size_map]; exact hsz, fun k hk ↦ ?_, w⟩
  obtain ⟨o1, o2⟩ := o k (by omega)
  rw [o1]
  exact ⟨(hv k hk).2 ctx, o2⟩

theorem buildAll_leafOk {α : Type} {cq : Nat → Prop} {lq : Src → Prop}
    (f : Nat → α → Dag F → Dag F × List (Nat × Nat)) (xs : List α)
    (hf : ∀ k, ∀ x ∈ xs, ∀ g, g.LeafOk cq lq → (f k x g).1.LeafOk cq lq) :
    (buildAll f xs).1.LeafOk cq lq := by
  suffices h : ∀ (l : List α) (g : Dag F) (sc : Sched) (k : Nat), (∀ x ∈ l, x ∈ xs) →
      g.LeafOk cq lq → (l.foldl (fun (g, sc, k) x ↦
          let (g, accs) := f k x g
          (g, schedule g accs sc, k + 1)) (g, sc, k)).1.LeafOk cq lq from
    h xs Dag.empty ⟨#[], 0⟩ 0 (fun _ h ↦ h) fun i n hn ↦ by
      simp only [Dag.empty, Array.getElem?_empty, reduceCtorEq] at hn
  intro l
  induction l with
  | nil => intro g _ _ _ h; exact h
  | cons x l ih =>
    intro g sc k hl h
    rw [List.foldl_cons]
    exact ih _ _ _ (fun y hy ↦ hl y (List.mem_cons_of_mem _ hy))
      (hf k x (hl x List.mem_cons_self) g h)

/-- The compiled constraints read the columns their expressions read. -/
theorem compile_leafOk (cs : List (Expr F)) (w wn pw pwn rw : Nat)
    (hc : ∀ c ∈ cs, c.colsBelow w wn pw pwn = true) :
    ∀ ins ∈ (compile cs).code, ins.LeafOk (· < w) (Src.Below wn pw pwn rw) := by
  let f : Nat → Expr F → Dag F → Dag F × List (Nat × Nat) := fun k c g ↦
    ((Dag.ofExpr c g).1, [((Dag.ofExpr c g).2, k)])
  have he : compile cs = allocate (buildAll f cs).1.nodes (buildAll f cs).2.steps #[] := rfl
  rw [he]
  exact allocate_leafOk _ _ _ _ _ (buildAll_leafOk f cs fun k c hcm g hg ↦
    Dag.ofExpr_leafOk c (hc c hcm) g hg)

/-- The compiled extension constraints read the columns their expressions read. -/
theorem compileExt_leafOk (W : F) (np : Nat) (cs : List (Lookup.ExtExpr F))
    (w wn pw pwn pmw rw : Nat) (hrw : 4 * pmw ≤ rw)
    (hc : ∀ c ∈ cs, c.colsBelow w wn pw pwn pmw = true) :
    ∀ ins ∈ (compileExt W np cs).code, ins.LeafOk (· < w) (Src.Below wn pw pwn rw) := by
  let f : Nat → Lookup.ExtExpr F → Dag F → Dag F × List (Nat × Nat) := fun k c g ↦
    ((Dag.ofExt W np c g).1, [((Dag.ofExt W np c g).2.1, 4 * k),
      ((Dag.ofExt W np c g).2.2.1, 4 * k + 1), ((Dag.ofExt W np c g).2.2.2.1, 4 * k + 2),
      ((Dag.ofExt W np c g).2.2.2.2, 4 * k + 3)])
  have he : compileExt W np cs = allocate (buildAll f cs).1.nodes (buildAll f cs).2.steps #[] :=
    rfl
  rw [he]
  exact allocate_leafOk _ _ _ _ _ (buildAll_leafOk f cs fun k c hcm g hg ↦
    Dag.ofExt_leafOk W np hrw c (hc c hcm) g hg)

/-- The compiled outputs read the columns their expressions read, and so do the outputs. -/
theorem compileOuts_leafOk (es : List (Expr F)) (w wn pw pwn rw : Nat)
    (hc : ∀ e ∈ es, e.colsBelow w wn pw pwn = true) :
    (∀ ins ∈ (compileOuts es).code, ins.LeafOk (· < w) (Src.Below wn pw pwn rw)) ∧
      ∀ o ∈ (compileOuts es).outs, o.LeafOk (· < w) := by
  have he : compileOuts es = allocate (es.foldl (fun (gs : Dag F × Array Nat) e ↦
      ((Dag.ofExpr e gs.1).1, gs.2.push (Dag.ofExpr e gs.1).2)) (Dag.empty, #[])).1.nodes
      (schedule (es.foldl (fun (gs : Dag F × Array Nat) e ↦
        ((Dag.ofExpr e gs.1).1, gs.2.push (Dag.ofExpr e gs.1).2)) (Dag.empty, #[])).1 []
        ⟨#[], 0⟩).steps
      (es.foldl (fun (gs : Dag F × Array Nat) e ↦
        ((Dag.ofExpr e gs.1).1, gs.2.push (Dag.ofExpr e gs.1).2)) (Dag.empty, #[])).2 := rfl
  rw [he]
  suffices h : ∀ (l : List (Expr F)) (g : Dag F) (outs : Array Nat), (∀ e ∈ l, e ∈ es) →
      g.LeafOk (· < w) (Src.Below wn pw pwn rw) →
      (l.foldl (fun (gs : Dag F × Array Nat) e ↦
        ((Dag.ofExpr e gs.1).1, gs.2.push (Dag.ofExpr e gs.1).2)) (g, outs)).1.LeafOk (· < w)
        (Src.Below wn pw pwn rw) by
    have hd := h es Dag.empty #[] (fun _ h ↦ h) fun i n hn ↦ by
      simp only [Dag.empty, Array.getElem?_empty, reduceCtorEq] at hn
    exact ⟨allocate_leafOk _ _ _ _ _ hd, allocate_outs_leafOk _ _ _ _ _ hd⟩
  intro l
  induction l with
  | nil => intro g _ _ h; exact h
  | cons e l ih =>
    intro g outs hl h
    rw [List.foldl_cons]
    exact ih _ _ (fun y hy ↦ hl y (List.mem_cons_of_mem _ hy))
      (Dag.ofExpr_leafOk e (hc e (hl e List.mem_cons_self)) g h)

end Compiled

end CompStark.Stark.Prog
