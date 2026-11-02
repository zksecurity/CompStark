/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Prog
public import CompPoly.Fields.Extension.Bridge
public import Mathlib.Tactic.Ring

/-! # The compiled program computes the constraints

On a row's values (`Ctx`), every node of a graph has a value (`val`): a column, a constant, a
loaded column or a scalar, or the operation on its operands' values. Building the graph keeps it
well formed (`Dag.Ok`: operands before their node, the index pointing at its node) and only adds
nodes (`Dag.Ext`), so a node keeps its value; the node of an expression has the expression's value
(`ofExpr_val`), and the coordinates of an extension expression its coordinates (`ofExt_val`).

The register allocation keeps every node that a later step reads in a register of its own
(`Alloc.Inv`), so the program's run on a row (`fieldMachine`) accumulates the scheduled nodes'
values with their weights (`allocate_run`); hence `compile_run`: the accumulators gain
`∑ₖ cₖ · weight k`.
-/

@[expose] public section
namespace CompStark.Stark.Prog

variable {F : Type}

/-! ### Values of nodes -/

section Values
variable [Field F]

/-- The value of a node from its operands' values `v`. -/
def Node.value (ctx : Ctx F) (v : Nat → F) : Node F → F
  | .cur c => ctx.cur c
  | .const x => x
  | .load s => ctx.src s
  | .scalar i => ctx.scalar i
  | .bin o a b => o.eval (v a) (v b)

/-- The value of node `i`: of an operation, on its earlier operands. -/
def val (ctx : Ctx F) (nodes : Array (Node F)) (i : Nat) : F :=
  match nodes[i]? with
  | some (.bin o a b) =>
    if _h : a < i ∧ b < i then o.eval (val ctx nodes a) (val ctx nodes b) else 0
  | some n => n.value ctx fun _ ↦ 0
  | none => 0
termination_by i
decreasing_by all_goals omega

/-- The operands of a node come before it. -/
def Node.Before (i : Nat) : Node F → Prop
  | .bin _ a b => a < i ∧ b < i
  | _ => True

theorem val_eq (ctx : Ctx F) (nodes : Array (Node F)) (i : Nat) (n : Node F)
    (h : nodes[i]? = some n) (hb : n.Before i) : val ctx nodes i = n.value ctx (val ctx nodes) := by
  rw [val, h]
  cases n with
  | bin o a b =>
    simp only [Node.Before] at hb
    simp only [hb, and_self, dite_true, Node.value]
  | _ => rfl

/-- Nodes agreeing below `N` give the nodes below `N` the same values. -/
theorem val_congr (ctx : Ctx F) (nodes nodes' : Array (Node F)) (N : Nat)
    (h : ∀ j < N, nodes'[j]? = nodes[j]?) : ∀ i < N, val ctx nodes' i = val ctx nodes i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rw [val, val, h i hi]
    split
    · split
      · rename_i hab
        rw [ih _ hab.1 (by omega), ih _ hab.2 (by omega)]
      · rfl
    · rfl
    · rfl

end Values

/-! ### Building the graph -/

section Build

/-- A well-formed graph: every node's operands come before it, and the index points at its
nodes. -/
structure Dag.Ok [DecidableEq F] [Hashable F] (g : Dag F) : Prop where
  before : ∀ i (n : Node F), g.nodes[i]? = some n → n.Before i
  index : ∀ (n : Node F) i, g.index[n]? = some i → g.nodes[i]? = some n

/-- `g'` extends `g`: its nodes start with `g`'s. -/
def Dag.Ext [DecidableEq F] [Hashable F] (g g' : Dag F) : Prop :=
  g.nodes.size ≤ g'.nodes.size ∧ ∀ j < g.nodes.size, g'.nodes[j]? = g.nodes[j]?

theorem Dag.Ext.refl [DecidableEq F] [Hashable F] (g : Dag F) : g.Ext g :=
  ⟨Nat.le_refl _, fun _ _ ↦ rfl⟩

theorem Dag.Ext.trans [DecidableEq F] [Hashable F] {g g' g'' : Dag F} (h1 : g.Ext g')
    (h2 : g'.Ext g'') : g.Ext g'' :=
  ⟨Nat.le_trans h1.1 h2.1, fun j hj ↦ by rw [h2.2 j (by have := h1.1; omega), h1.2 j hj]⟩

theorem Dag.Ext.val_eq [DecidableEq F] [Hashable F] [Field F] {g g' : Dag F} (h : g.Ext g')
    (ctx : Ctx F) (i : Nat) (hi : i < g.nodes.size) : val ctx g'.nodes i = val ctx g.nodes i :=
  val_congr ctx g.nodes g'.nodes g.nodes.size h.2 i hi

/-- Every operand of a node is below `N`. -/
def Node.Below (N : Nat) : Node F → Prop
  | .bin _ a b => a < N ∧ b < N
  | _ => True

theorem Node.Below.before {n : Node F} {i : Nat} (h : n.Below i) : n.Before i := by
  cases n with
  | bin o a b => exact h
  | _ => trivial

theorem Node.Below.mono {n : Node F} {N N' : Nat} (h : n.Below N) (hN : N ≤ N') : n.Below N' := by
  cases n with
  | bin o a b => exact ⟨by have := h.1; omega, by have := h.2; omega⟩
  | _ => trivial

theorem Dag.empty_ok [DecidableEq F] [Hashable F] : (Dag.empty : Dag F).Ok :=
  ⟨fun i n h ↦ by simp only [Dag.empty, Array.getElem?_empty, reduceCtorEq] at h,
    fun n i h ↦ by simp only [Dag.empty, Std.HashMap.getElem?_empty, reduceCtorEq] at h⟩

/-- Interning a node whose operands are nodes keeps the graph well formed, extends it, and gives
the index of a node equal to it. -/
theorem Dag.intern_spec [DecidableEq F] [Hashable F] (g : Dag F) (hg : g.Ok) (n : Node F)
    (hn : n.Below g.nodes.size) :
    (g.intern n).1.Ok ∧ g.Ext (g.intern n).1 ∧ (g.intern n).2 < (g.intern n).1.nodes.size ∧
      (g.intern n).1.nodes[(g.intern n).2]? = some n := by
  unfold Dag.intern
  split
  · rename_i i hi
    have := hg.index n i hi
    refine ⟨hg, Dag.Ext.refl g, ?_, this⟩
    rcases Nat.lt_or_ge i g.nodes.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at this
      exact absurd this (by simp only [reduceCtorEq, not_false_eq_true])
  · rename_i hnone
    obtain ⟨nodes, index⟩ := g
    dsimp only at hn hnone hg ⊢
    refine ⟨⟨fun i m h ↦ ?_, fun m i h ↦ ?_⟩, ⟨by simp only [Array.size_push]; omega,
      fun j hj ↦ by
        simp only [Array.getElem?_push]
        exact ite_eq_right_iff.mpr fun h ↦ absurd h (by simp only at hj; omega)⟩,
      by simp only [Array.size_push]; omega,
      by simp only [Array.getElem?_push, ite_true]⟩
    · simp only [Array.getElem?_push] at h
      split at h
      · rename_i hi
        simp only [Option.some.injEq] at h
        subst h hi
        exact hn.before
      · exact hg.before i m h
    · simp only [Array.getElem?_push]
      rw [Std.HashMap.getElem?_insert] at h
      split at h
      · rename_i heq
        simp only [Option.some.injEq] at h
        subst h
        simp only [ite_true]
        exact congrArg some (eq_of_beq heq)
      · have := hg.index m i h
        rw [ite_eq_right_iff.mpr]
        · exact this
        · intro hi
          subst hi
          rw [Array.getElem?_eq_none (Nat.le_refl _)] at this
          exact absurd this (by simp only [reduceCtorEq, not_false_eq_true])

/-- `r` is built on `g`: a well-formed extension of it with a node of value `v` on every row. -/
structure Built [DecidableEq F] [Hashable F] [Field F] (g : Dag F) (r : Dag F × Nat)
    (v : Ctx F → F) : Prop where
  ok : r.1.Ok
  ext : g.Ext r.1
  lt : r.2 < r.1.nodes.size
  value : ∀ ctx, val ctx r.1.nodes r.2 = v ctx

theorem Built.mono [DecidableEq F] [Hashable F] [Field F] {g : Dag F} {r : Dag F × Nat}
    {v : Ctx F → F} (h : Built g r v) {g' : Dag F} (h' : r.1.Ext g') (ctx : Ctx F) :
    val ctx g'.nodes r.2 = v ctx := by
  rw [h'.val_eq ctx _ h.lt, h.value]

theorem Dag.intern_built [DecidableEq F] [Hashable F] [Field F] (g : Dag F) (hg : g.Ok)
    (n : Node F) (hn : n.Below g.nodes.size) :
    Built g (g.intern n) fun ctx ↦ n.value ctx (val ctx g.nodes) := by
  obtain ⟨h1, h2, h3, h4⟩ := g.intern_spec hg n hn
  refine ⟨h1, h2, h3, fun ctx ↦ ?_⟩
  rw [val_eq ctx _ _ n h4 (h1.before _ _ h4)]
  cases n with
  | bin o a b =>
    simp only [Node.value]
    rw [h2.val_eq ctx a hn.1, h2.val_eq ctx b hn.2]
  | _ => rfl

theorem Dag.constAt_val [DecidableEq F] [Hashable F] [Field F] (g : Dag F) (hg : g.Ok) (i : Nat)
    (x : F) (h : g.constAt i = some x) (ctx : Ctx F) : val ctx g.nodes i = x := by
  unfold Dag.constAt at h
  split at h
  · rename_i y hy
    simp only [Option.some.injEq] at h
    subst h
    rw [val_eq ctx _ _ _ hy (hg.before _ _ hy)]
    rfl
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

theorem Built.of_eq [DecidableEq F] [Hashable F] [Field F] {g : Dag F} {r : Dag F × Nat}
    {v w : Ctx F → F} (h : Built g r v) (e : ∀ ctx, v ctx = w ctx) : Built g r w :=
  ⟨h.ok, h.ext, h.lt, fun ctx ↦ by rw [h.value, e]⟩

/-- An operation on nodes `a` and `b`, folded, is a node of the operation's value. -/
theorem Dag.op_built [DecidableEq F] [Hashable F] [Field F] (g : Dag F) (hg : g.Ok) (o : Op)
    (a b : Nat) (ha : a < g.nodes.size) (hb : b < g.nodes.size) :
    Built g (g.op o a b) fun ctx ↦ o.eval (val ctx g.nodes a) (val ctx g.nodes b) := by
  have hself (i : Nat) (hi : i < g.nodes.size) (w : Ctx F → F)
      (hw : ∀ ctx, val ctx g.nodes i = w ctx) : Built g (g, i) w :=
    ⟨hg, Dag.Ext.refl g, hi, hw⟩
  have hint (n : Node F) (hn : n.Below g.nodes.size) (w : Ctx F → F)
      (hw : ∀ ctx, n.value ctx (val ctx g.nodes) = w ctx) : Built g (g.intern n) w :=
    (g.intern_built hg n hn).of_eq hw
  have hmin : min a b < g.nodes.size := by omega
  have hmax : max a b < g.nodes.size := by omega
  have hsort (f : F → F → F) (hc : ∀ x y, f x y = f y x) (ctx : Ctx F) :
      f (val ctx g.nodes (min a b)) (val ctx g.nodes (max a b)) =
        f (val ctx g.nodes a) (val ctx g.nodes b) := by
    rcases Nat.le_total a b with h | h
    · rw [Nat.min_eq_left h, Nat.max_eq_right h]
    · rw [Nat.min_eq_right h, Nat.max_eq_left h, hc]
  have hbin (o' : Op) (a' b' : Nat) (h' : a' < g.nodes.size ∧ b' < g.nodes.size)
      (w : Ctx F → F) (hw : ∀ ctx, o'.eval (val ctx g.nodes a') (val ctx g.nodes b') = w ctx) :
      Built g (g.intern (.bin o' a' b')) w := hint (.bin o' a' b') h' w hw
  have hconst (x : F) (w : Ctx F → F) (hw : ∀ ctx, x = w ctx) :
      Built g (g.intern (.const x)) w := hint (.const x) trivial w hw
  have hadd := hbin .add (min a b) (max a b) ⟨hmin, hmax⟩
    (fun ctx ↦ Op.eval .add (val ctx g.nodes a) (val ctx g.nodes b))
    fun ctx ↦ by simp only [Op.eval]; exact hsort (· + ·) add_comm ctx
  have hmul := hbin .mul (min a b) (max a b) ⟨hmin, hmax⟩
    (fun ctx ↦ Op.eval .mul (val ctx g.nodes a) (val ctx g.nodes b))
    fun ctx ↦ by simp only [Op.eval]; exact hsort (· * ·) mul_comm ctx
  have hsub := hbin .sub a b ⟨ha, hb⟩
    (fun ctx ↦ Op.eval .sub (val ctx g.nodes a) (val ctx g.nodes b)) fun _ ↦ rfl
  cases hca : g.constAt a with
  | some x =>
    have vx := g.constAt_val hg a x hca
    cases hcb : g.constAt b with
    | some y =>
      have vy := g.constAt_val hg b y hcb
      cases o <;> simp only [Dag.op, hca, hcb] <;>
        exact hconst _ _ fun ctx ↦ by rw [vx, vy]
    | none =>
      cases o <;> simp only [Dag.op, hca, hcb]
      · split
        · rename_i h0
          exact hself b hb _ fun ctx ↦ by simp only [Op.eval]; rw [vx, h0, zero_add]
        · exact hadd
      · exact if hab : a = b then by
            simp only [hab, ite_true]
            exact hconst _ _ fun ctx ↦ by simp only [Op.eval, sub_self]
          else by
            simp only [hab, ite_false]
            exact hsub
      · split
        · rename_i h0
          exact hconst _ _ fun ctx ↦ by simp only [Op.eval]; rw [vx, h0, zero_mul]
        · split
          · rename_i h1
            exact hself b hb _ fun ctx ↦ by simp only [Op.eval]; rw [vx, h1, one_mul]
          · split
            · rename_i h2
              exact hbin .add b b ⟨hb, hb⟩ _ fun ctx ↦ by
                simp only [Op.eval]; rw [vx, h2, two_mul]
            · exact hmul
  | none =>
    cases hcb : g.constAt b with
    | some y =>
      have vy := g.constAt_val hg b y hcb
      cases o <;> simp only [Dag.op, hca, hcb]
      · split
        · rename_i h0
          exact hself a ha _ fun ctx ↦ by simp only [Op.eval]; rw [vy, h0, add_zero]
        · exact hadd
      · split
        · rename_i h0
          exact hself a ha _ fun ctx ↦ by simp only [Op.eval]; rw [vy, h0, sub_zero]
        · exact hsub
      · split
        · rename_i h0
          exact hconst _ _ fun ctx ↦ by simp only [Op.eval]; rw [vy, h0, mul_zero]
        · split
          · rename_i h1
            exact hself a ha _ fun ctx ↦ by simp only [Op.eval]; rw [vy, h1, mul_one]
          · split
            · rename_i h2
              exact hbin .add a a ⟨ha, ha⟩ _ fun ctx ↦ by
                simp only [Op.eval]; rw [vy, h2, mul_two]
            · exact hmul
    | none =>
      cases o <;> simp only [Dag.op, hca, hcb]
      · exact hadd
      · exact if hab : a = b then by
            simp only [hab, ite_true]
            exact hconst _ _ fun ctx ↦ by simp only [Op.eval, sub_self]
          else by
            simp only [hab, ite_false]
            exact hsub
      · exact hmul

theorem Built.trans [DecidableEq F] [Hashable F] [Field F] {g : Dag F} {r r' : Dag F × Nat}
    {v w : Ctx F → F} (h : Built g r v) (h' : Built r.1 r' w) : Built g r' w :=
  ⟨h'.ok, h.ext.trans h'.ext, h'.lt, h'.value⟩

/-- An operation on the nodes of two built values, in order. -/
theorem Built.op [DecidableEq F] [Hashable F] [Field F] {g : Dag F} {r1 r2 : Dag F × Nat}
    {v1 v2 : Ctx F → F} (h1 : Built g r1 v1) (h2 : Built r1.1 r2 v2) (o : Op) :
    Built g (r2.1.op o r1.2 r2.2) fun ctx ↦ o.eval (v1 ctx) (v2 ctx) :=
  (h1.trans h2).trans ((r2.1.op_built h2.ok o r1.2 r2.2 (by have := h2.ext.1; have := h1.lt; omega)
    h2.lt).of_eq fun ctx ↦ by rw [h1.mono h2.ext ctx, h2.value])

/-- A row's values as an environment of constraint expressions: the trace's next row, the
preprocessed trace, the periodic columns and the selectors loaded, the public values the
scalars. -/
def Ctx.env (ctx : Ctx F) : Expr.Env F F where
  cur := ctx.cur
  next c := ctx.src (.next c)
  prepCur c := ctx.src (.prepCur c)
  prepNext c := ctx.src (.prepNext c)
  periodic i := ctx.src (.periodic i)
  pub := ctx.scalar
  const x := x
  isFirstRow := ctx.src .isFirstRow
  isLastRow := ctx.src .isLastRow
  isTransition := ctx.src .isTransition

/-- The node of an expression has the expression's value. -/
theorem Dag.ofExpr_built [DecidableEq F] [Hashable F] [Field F] (e : Expr F) (g : Dag F)
    (hg : g.Ok) : Built g (Dag.ofExpr e g) fun ctx ↦ e.eval ctx.env := by
  induction e generalizing g with
  | add a b iha ihb =>
    have h1 := iha g hg
    exact h1.op (ihb _ h1.ok) .add
  | sub a b iha ihb =>
    have h1 := iha g hg
    exact h1.op (ihb _ h1.ok) .sub
  | mul a b iha ihb =>
    have h1 := iha g hg
    exact h1.op (ihb _ h1.ok) .mul
  | _ => exact g.intern_built hg _ trivial

/-- An expression over nodes evaluated on node values `v`. -/
def Dag.Tree.eval [Field F] (v : Nat → F) : Dag.Tree → F
  | .leaf i => v i
  | .op o a b => o.eval (a.eval v) (b.eval v)

/-- Every leaf of an expression over nodes is below `N`. -/
def Dag.Tree.Below (N : Nat) : Dag.Tree → Prop
  | .leaf i => i < N
  | .op _ a b => a.Below N ∧ b.Below N

theorem Dag.Tree.eval_congr [Field F] (v v' : Nat → F) (N : Nat) (h : ∀ i < N, v' i = v i) :
    ∀ t : Dag.Tree, t.Below N → t.eval v' = t.eval v
  | .leaf i, ht => h i ht
  | .op o a b, ht => by
    simp only [Dag.Tree.eval]
    rw [Dag.Tree.eval_congr v v' N h a ht.1, Dag.Tree.eval_congr v v' N h b ht.2]

theorem Dag.Tree.Below.mono {t : Dag.Tree} {N N' : Nat} (h : t.Below N) (hN : N ≤ N') :
    t.Below N' := by
  induction t with
  | leaf i => exact Nat.lt_of_lt_of_le h hN
  | op o a b iha ihb => exact ⟨iha h.1, ihb h.2⟩

/-- The node of an expression over nodes has its value. -/
theorem Dag.ofTree_built [DecidableEq F] [Hashable F] [Field F] (g : Dag F) (hg : g.Ok) :
    ∀ t : Dag.Tree, t.Below g.nodes.size →
      Built g (g.ofTree t) fun ctx ↦ t.eval (val ctx g.nodes)
  | .leaf i, ht => ⟨hg, Dag.Ext.refl g, ht, fun _ ↦ rfl⟩
  | .op o a b, ht => by
    have h1 := g.ofTree_built hg a ht.1
    have h2 := (g.ofTree a).1.ofTree_built h1.ok b (ht.2.mono h1.ext.1)
    refine (h1.op h2 o).of_eq fun ctx ↦ ?_
    simp only [Dag.Tree.eval]
    rw [Dag.Tree.eval_congr (val ctx g.nodes) (val ctx (g.ofTree a).1.nodes) g.nodes.size
      (fun i hi ↦ h1.ext.val_eq ctx i hi) b ht.2]

end Build

/-! ### Extension expressions -/

open CompPoly.Extension

/-- A row's values as an environment of extension expressions' base expressions over the extension
`P`, with `np` public values: the base embedding of `Ctx.env`, public values from `np` on zero. -/
def Ctx.envQ [Field F] (P : ExtensionParams F) (np : Nat) (ctx : Ctx F) : Expr.Env F (Ext P) where
  cur c := CompPoly.Extension.Ext.ofBase (ctx.env.cur c)
  next c := CompPoly.Extension.Ext.ofBase (ctx.env.next c)
  prepCur c := CompPoly.Extension.Ext.ofBase (ctx.env.prepCur c)
  prepNext c := CompPoly.Extension.Ext.ofBase (ctx.env.prepNext c)
  periodic i := CompPoly.Extension.Ext.ofBase (ctx.env.periodic i)
  pub i := CompPoly.Extension.Ext.ofBase (if i < np then ctx.env.pub i else 0)
  const x := CompPoly.Extension.Ext.ofBase x
  isFirstRow := CompPoly.Extension.Ext.ofBase ctx.env.isFirstRow
  isLastRow := CompPoly.Extension.Ext.ofBase ctx.env.isLastRow
  isTransition := CompPoly.Extension.Ext.ofBase ctx.env.isTransition

/-- The extension element of the `d` scalars from `k`. -/
def Ctx.scalarsExt [Field F] (P : ExtensionParams F) (ctx : Ctx F) (k : Nat) : Ext P :=
  CompPoly.Extension.Ext.ofFn fun j ↦ ctx.scalar (k + j)

/-- A row's permutation trace, challenges and terminal over the extension `P` of degree `d`, with
`np` public values: column `c` from the loaded permutation columns `d c, …, d c + d - 1`, the
terminal's coordinates the scalars from `np`, challenge `i`'s from `np + d (i + 1)`. -/
def Ctx.auxQ [Field F] (P : ExtensionParams F) (np : Nat) (ctx : Ctx F) :
    Lookup.ExtExpr.Env (Ext P) where
  perm c := CompPoly.Extension.Ext.ofFn fun j ↦ ctx.src (.permCur (P.d * c + j))
  permNext c := CompPoly.Extension.Ext.ofFn fun j ↦ ctx.src (.permNext (P.d * c + j))
  challenge i := ctx.scalarsExt P (np + P.d * (i + 1))
  terminal := ctx.scalarsExt P np

/-- Evaluating a base expression over the extension with `np` public values embeds the value of
its public values below `np` (`Dag.pubBelow`). -/
theorem Expr.eval_envQ [Field F] (P : ExtensionParams F) (np : Nat) (ctx : Ctx F) :
    ∀ e : Expr F, e.eval (ctx.envQ P np) = CompPoly.Extension.Ext.ofBase ((Dag.pubBelow np e).eval
        ctx.env)
  | .add a b => by
    rw [show Dag.pubBelow np (.add a b) = .add (Dag.pubBelow np a) (Dag.pubBelow np b) from rfl]
    simp only [Expr.eval]
    rw [Expr.eval_envQ P np ctx a, Expr.eval_envQ P np ctx b]
    exact (map_add (CompPoly.Extension.Ext.ofBaseRingHom P) _ _).symm
  | .sub a b => by
    rw [show Dag.pubBelow np (.sub a b) = .sub (Dag.pubBelow np a) (Dag.pubBelow np b) from rfl]
    simp only [Expr.eval]
    rw [Expr.eval_envQ P np ctx a, Expr.eval_envQ P np ctx b]
    exact (map_sub (CompPoly.Extension.Ext.ofBaseRingHom P) _ _).symm
  | .mul a b => by
    rw [show Dag.pubBelow np (.mul a b) = .mul (Dag.pubBelow np a) (Dag.pubBelow np b) from rfl]
    simp only [Expr.eval]
    rw [Expr.eval_envQ P np ctx a, Expr.eval_envQ P np ctx b]
    exact (map_mul (CompPoly.Extension.Ext.ofBaseRingHom P) _ _).symm
  | .pub i => by
    simp only [Expr.eval, Dag.pubBelow]
    by_cases h : i < np
    · simp only [h, ite_true, Expr.eval]
      show CompPoly.Extension.Ext.ofBase (if i < np then ctx.env.pub i else 0) = _
      rw [ite_eq_left h]
    · simp only [h, ite_false, Expr.eval]
      show CompPoly.Extension.Ext.ofBase (if i < np then ctx.env.pub i else 0) = _
      rw [ite_eq_right h]
      rfl
  | .cur _ | .next _ | .prepCur _ | .prepNext _ | .periodic _ | .const _ | .isFirstRow
  | .isLastRow | .isTransition => rfl

section BuildExt
variable [DecidableEq F] [Hashable F] [Field F]

/-- `r` is built on `g`: a well-formed extension of it with `n` nodes, coordinate `i` of value
`v · i` on every row. -/
structure BuiltL (g : Dag F) (r : Dag F × List Nat) (n : Nat) (v : Ctx F → Nat → F) : Prop where
  ok : r.1.Ok
  ext : g.Ext r.1
  len : r.2.length = n
  lt : ∀ i < n, r.2.getD i 0 < r.1.nodes.size
  value : ∀ ctx, ∀ i < n, val ctx r.1.nodes (r.2.getD i 0) = v ctx i

theorem BuiltL.of_eq {g : Dag F} {r : Dag F × List Nat} {n : Nat} {v w : Ctx F → Nat → F}
    (h : BuiltL g r n v) (e : ∀ ctx, ∀ i < n, v ctx i = w ctx i) : BuiltL g r n w :=
  ⟨h.ok, h.ext, h.len, h.lt, fun ctx i hi ↦ by rw [h.value ctx i hi, e ctx i hi]⟩

theorem BuiltL.mono {g : Dag F} {r : Dag F × List Nat} {n : Nat} {v : Ctx F → Nat → F}
    (h : BuiltL g r n v) {g' : Dag F} (h' : r.1.Ext g') (ctx : Ctx F) (i : Nat) (hi : i < n) :
    val ctx g'.nodes (r.2.getD i 0) = v ctx i := by
  rw [h'.val_eq ctx _ (h.lt i hi), h.value ctx i hi]

/-- A leaf node interned. -/
theorem Dag.leaf_built (g : Dag F) (hg : g.Ok) (n : Node F) (hn : n.Below 0) :
    Built g (g.intern n) fun ctx ↦ n.value ctx fun _ ↦ 0 :=
  (g.intern_built hg n (hn.mono (Nat.zero_le _))).of_eq fun ctx ↦ by
    cases n with
    | bin o a b => exact absurd hn.1 (Nat.not_lt_zero a)
    | _ => rfl

/-- Leaf nodes interned in order. -/
theorem Dag.internAll_built (ns : List (Node F)) (hns : ∀ n ∈ ns, n.Below 0) :
    ∀ (g : Dag F), g.Ok → BuiltL g (g.internAll ns) ns.length fun ctx i ↦
      (ns.getD i (.const 0)).value ctx fun _ ↦ 0 := by
  induction ns with
  | nil =>
    intro g hg
    exact ⟨hg, Dag.Ext.refl g, rfl, fun i hi ↦ absurd hi (Nat.not_lt_zero _),
      fun _ i hi ↦ absurd hi (Nat.not_lt_zero _)⟩
  | cons n ns ih =>
    intro g hg
    have b0 := g.leaf_built hg n (hns n List.mem_cons_self)
    have b1 := ih (fun m hm ↦ hns m (List.mem_cons_of_mem _ hm)) _ b0.ok
    unfold Dag.internAll
    generalize g.intern n = q0 at b0 b1 ⊢
    obtain ⟨g1, c⟩ := q0
    dsimp only at b0 b1 ⊢
    generalize g1.internAll ns = q1 at b1 ⊢
    obtain ⟨g2, cs⟩ := q1
    refine ⟨b1.ok, b0.ext.trans b1.ext, by simp only [List.length_cons, b1.len], fun i hi ↦ ?_,
      fun ctx i hi ↦ ?_⟩
    · rcases i with _ | i
      · simp only [List.getD_cons_zero]; have := b1.ext.1; have := b0.lt; dsimp only at *; omega
      · simp only [List.getD_cons_succ]
        exact b1.lt i (by simp only [List.length_cons] at hi; omega)
    · rcases i with _ | i
      · simp only [List.getD_cons_zero]
        exact b0.mono b1.ext ctx
      · simp only [List.getD_cons_succ]
        exact b1.value ctx i (by simp only [List.length_cons] at hi; omega)

/-- Coordinatewise operations on two lists of nodes. -/
theorem Dag.opN_built (o : Op) :
    ∀ (xs ys : List Nat) (g : Dag F), g.Ok → xs.length = ys.length →
      (∀ i < xs.length, xs.getD i 0 < g.nodes.size) →
      (∀ i < xs.length, ys.getD i 0 < g.nodes.size) →
      BuiltL g (g.opN o xs ys) xs.length fun ctx i ↦
        o.eval (val ctx g.nodes (xs.getD i 0)) (val ctx g.nodes (ys.getD i 0))
  | [], _, g, hg, _, _, _ =>
    ⟨hg, Dag.Ext.refl g, rfl, fun i hi ↦ absurd hi (Nat.not_lt_zero _),
      fun _ i hi ↦ absurd hi (Nat.not_lt_zero _)⟩
  | x :: xs, [], g, _, hl, _, _ => absurd hl (by simp)
  | x :: xs, y :: ys, g, hg, hl, hx, hy => by
    have hx0 := hx 0 (by simp)
    have hy0 := hy 0 (by simp)
    simp only [List.getD_cons_zero] at hx0 hy0
    have b0 := g.op_built hg o x y hx0 hy0
    have b1 := Dag.opN_built o xs ys _ b0.ok (by simpa using hl)
      (fun i hi ↦ by
        have := hx (i + 1) (by simp only [List.length_cons]; omega)
        simp only [List.getD_cons_succ] at this; have := b0.ext.1; omega)
      (fun i hi ↦ by
        have := hy (i + 1) (by simp only [List.length_cons]; omega)
        simp only [List.getD_cons_succ] at this; have := b0.ext.1; omega)
    unfold Dag.opN
    generalize g.op o x y = q0 at b0 b1 ⊢
    obtain ⟨g1, c⟩ := q0
    dsimp only at b0 b1 ⊢
    generalize g1.opN o xs ys = q1 at b1 ⊢
    obtain ⟨g2, cs⟩ := q1
    refine ⟨b1.ok, b0.ext.trans b1.ext, by simp only [List.length_cons, b1.len],
      fun i hi ↦ ?_, fun ctx i hi ↦ ?_⟩
    · rcases i with _ | i
      · simp only [List.getD_cons_zero]; have := b1.ext.1; have := b0.lt; dsimp only at *; omega
      · simp only [List.getD_cons_succ]
        exact b1.lt i (by simp only [List.length_cons] at hi; omega)
    · rcases i with _ | i
      · simp only [List.getD_cons_zero]
        exact b0.mono b1.ext ctx
      · simp only [List.getD_cons_succ]
        have hi' : i < xs.length := by simp only [List.length_cons] at hi; omega
        have hxi := hx (i + 1) (by simp only [List.length_cons]; omega)
        have hyi := hy (i + 1) (by simp only [List.length_cons]; omega)
        simp only [List.getD_cons_succ] at hxi hyi
        rw [b1.value ctx i hi', b0.ext.val_eq ctx _ hxi, b0.ext.val_eq ctx _ hyi]

omit [DecidableEq F] [Hashable F] in
/-- The sum of trees is the sum of their values, the node `z`'s for none. -/
theorem sumTree_eval (z : Nat) (v : Nat → F) (hz : v z = 0) :
    ∀ ts : List Dag.Tree, (Dag.sumTree z ts).eval v = (ts.map (·.eval v)).sum
  | [] => by simp only [Dag.sumTree, Dag.Tree.eval, hz, List.map_nil, List.sum_nil]
  | t :: ts => by
    simp only [Dag.sumTree, List.map_cons, List.sum_cons]
    suffices ∀ acc : Dag.Tree, (ts.foldl (fun acc u ↦ .op .add acc u) acc).eval v =
        acc.eval v + (ts.map (·.eval v)).sum from this t
    induction ts with
    | nil => intro acc; simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
    | cons u ts ih =>
      intro acc
      rw [List.foldl_cons, ih]
      simp only [Dag.Tree.eval, Op.eval, List.map_cons, List.sum_cons, add_assoc]

omit [DecidableEq F] [Hashable F] in
theorem sumTree_below (z N : Nat) (hz : z < N) :
    ∀ ts : List Dag.Tree, (∀ t ∈ ts, t.Below N) → (Dag.sumTree z ts).Below N
  | [], _ => hz
  | t :: ts, h => by
    simp only [Dag.sumTree]
    suffices ∀ acc : Dag.Tree, acc.Below N →
        (ts.foldl (fun acc u ↦ .op .add acc u) acc).Below N from
      this t (h t List.mem_cons_self)
    have h' : ∀ u ∈ ts, u.Below N := fun u hu ↦ h u (List.mem_cons_of_mem _ hu)
    clear h
    induction ts with
    | nil => intro acc ha; exact ha
    | cons u ts ih =>
      intro acc ha
      rw [List.foldl_cons]
      exact ih (fun w hw ↦ h' w (List.mem_cons_of_mem _ hw)) _ ⟨ha, h' u List.mem_cons_self⟩

omit [DecidableEq F] [Hashable F] in
theorem sum_filterMap_ite {α : Type} (l : List α) (c : α → Prop) [DecidablePred c]
    (gt : α → Dag.Tree) (e : Dag.Tree → F) :
    ((l.filterMap fun i ↦ if c i then some (gt i) else none).map e).sum =
      (l.map fun i ↦ if c i then e (gt i) else 0).sum := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    by_cases h : c i
    · simp only [List.filterMap_cons, h, ite_true, List.map_cons, List.sum_cons, ih]
    · simp only [List.filterMap_cons, h, ite_false, List.map_cons, List.sum_cons, ih, zero_add]

omit [DecidableEq F] [Hashable F] in
theorem convTree_below (z d : Nat) (x y : List Nat) (k N : Nat) (hz : z < N)
    (hx : ∀ i < d, x.getD i 0 < N) (hy : ∀ i < d, y.getD i 0 < N) :
    (Dag.convTree z d x y k).Below N := by
  refine sumTree_below z N hz _ fun t ht ↦ ?_
  obtain ⟨i, hi, he⟩ := List.mem_filterMap.mp ht
  split at he
  · rename_i hc
    simp only [Option.some.injEq] at he
    subst he
    exact ⟨hx i (List.mem_range.mp hi), hy _ hc.2⟩
  · exact absurd he (by simp)

omit [DecidableEq F] [Hashable F] in
/-- The convolution tree's value is the unreduced product's coefficient. -/
theorem convTree_eval (P : CompPoly.Extension.ExtensionParams F) (z : Nat) (x y : List Nat)
    (k : Nat) (v : Nat → F) (hz : v z = 0) :
    (Dag.convTree z P.d x y k).eval v = CompPoly.Extension.Ext.conv
      (CompPoly.Extension.Ext.ofFn fun i : Fin P.d ↦ v (x.getD i 0))
      (CompPoly.Extension.Ext.ofFn fun i : Fin P.d ↦ v (y.getD i 0)) k := by
  rw [Dag.convTree, sumTree_eval z v hz, sum_filterMap_ite, CompPoly.Extension.Ext.conv,
    ← CompPoly.Extension.Ext.sum_range_eq_list_sum, ← Fin.sum_univ_eq_sum_range (fun i ↦
      if i ≤ k ∧ k - i < P.d then
        (Dag.Tree.op .mul (.leaf (x.getD i 0)) (.leaf (y.getD (k - i) 0))).eval v else 0)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases h : (i : ℕ) ≤ k ∧ k - (i : ℕ) < P.d
  · rw [ite_eq_left h, dite_eq_left h]
    simp only [Dag.Tree.eval, Op.eval, CompPoly.Extension.Ext.coeff_ofFn]
  · rw [ite_eq_right h, dite_eq_right h]

/-- A coordinate of a product of coordinate nodes: the convolution `m` plus the higher
convolutions times the table's entries `t k`. -/
theorem Dag.mulCoord_built (g : Dag F) (hg : g.Ok) (z d : Nat) (x y : List Nat) (t : Nat → F)
    (m : Nat) (hz : z < g.nodes.size) (hx : ∀ i < d, x.getD i 0 < g.nodes.size)
    (hy : ∀ i < d, y.getD i 0 < g.nodes.size) :
    Built g (g.mulCoord z d x y t m) fun ctx ↦ (Dag.convTree z d x y m).eval (val ctx g.nodes) +
      ((List.range' d (d - 1)).map fun k ↦
        t k * (Dag.convTree z d x y k).eval (val ctx g.nodes)).sum := by
  have hc (k : Nat) := convTree_below z d x y k _ hz hx hy
  have hcv (g' : Dag F) (e : g.Ext g') (k : Nat) (ctx : Ctx F) :
      (Dag.convTree z d x y k).eval (val ctx g'.nodes) =
        (Dag.convTree z d x y k).eval (val ctx g.nodes) :=
    Dag.Tree.eval_congr _ _ _ (fun i hi ↦ e.val_eq ctx i hi) _ (hc k)
  have key : ∀ (l : List Nat) (g' : Dag F) (tr : Dag.Tree), g'.Ok → g.Ext g' →
      tr.Below g'.nodes.size →
      let r := l.foldl (Dag.mulStep z d x y t) (g', tr)
      r.1.Ok ∧ g.Ext r.1 ∧ r.2.Below r.1.nodes.size ∧ ∀ ctx, r.2.eval (val ctx r.1.nodes) =
        tr.eval (val ctx g'.nodes) + (l.map fun k ↦
          t k * (Dag.convTree z d x y k).eval (val ctx g.nodes)).sum := by
    intro l
    induction l with
    | nil =>
      intro g' tr hg' e htr
      exact ⟨hg', e, htr, fun ctx ↦ by simp only [List.foldl_nil, List.map_nil, List.sum_nil,
        add_zero]⟩
    | cons k l ih =>
      intro g' tr hg' e htr
      rw [List.foldl_cons]
      by_cases h0 : t k = 0
      · rw [show Dag.mulStep z d x y t (g', tr) k = (g', tr) by
          simp only [Dag.mulStep, h0, ite_true]]
        obtain ⟨r1, r2, r3, r4⟩ := ih g' tr hg' e htr
        refine ⟨r1, r2, r3, fun ctx ↦ ?_⟩
        rw [r4 ctx]
        simp only [List.map_cons, List.sum_cons, h0, zero_mul, zero_add]
      · by_cases h1 : t k = -1
        · rw [show Dag.mulStep z d x y t (g', tr) k = (g', .op .sub tr (Dag.convTree z d x y k)) by
            simp [Dag.mulStep, h1]]
          obtain ⟨r1, r2, r3, r4⟩ := ih g' (.op .sub tr (Dag.convTree z d x y k)) hg' e
            ⟨htr, (hc k).mono e.1⟩
          refine ⟨r1, r2, r3, fun ctx ↦ ?_⟩
          rw [r4 ctx]
          simp only [Dag.Tree.eval, Op.eval, hcv g' e, List.map_cons, List.sum_cons, h1]
          ring
        · rw [show Dag.mulStep z d x y t (g', tr) k = ((g'.intern (.const (t k))).1,
              .op .add tr (.op .mul (.leaf (g'.intern (.const (t k))).2)
                (Dag.convTree z d x y k))) by
            simp only [Dag.mulStep, h0, h1, ite_false]]
          have b := g'.leaf_built hg' (.const (t k)) trivial
          generalize g'.intern (.const (t k)) = q at b ⊢
          obtain ⟨g'', c⟩ := q
          dsimp only at b ⊢
          obtain ⟨r1, r2, r3, r4⟩ := ih g''
            (.op .add tr (.op .mul (.leaf c) (Dag.convTree z d x y k))) b.ok (e.trans b.ext)
            ⟨htr.mono b.ext.1, b.lt, (hc k).mono (e.trans b.ext).1⟩
          refine ⟨r1, r2, r3, fun ctx ↦ ?_⟩
          rw [r4 ctx]
          simp only [Dag.Tree.eval, Op.eval, hcv g'' (e.trans b.ext), List.map_cons,
            List.sum_cons]
          rw [Dag.Tree.eval_congr _ _ _ (fun i hi ↦ b.ext.val_eq ctx i hi) _ htr, b.value]
          simp only [Node.value]
          ring
  unfold Dag.mulCoord
  obtain ⟨r1, r2, r3, r4⟩ := key (List.range' d (d - 1)) g (Dag.convTree z d x y m) hg
    (Dag.Ext.refl g) (hc m)
  generalize List.foldl _ _ _ = r at r1 r2 r3 r4 ⊢
  obtain ⟨g', tr⟩ := r
  dsimp only at r1 r2 r3 r4 ⊢
  have b := g'.ofTree_built r1 tr r3
  exact ⟨b.ok, r2.trans b.ext, b.lt, fun ctx ↦ by rw [b.value, r4 ctx]⟩

/-- The extension element with the values of coordinate nodes. -/
def extOf (P : CompPoly.Extension.ExtensionParams F) (ctx : Ctx F) (nodes : Array (Node F))
    (x : List Nat) : CompPoly.Extension.Ext P :=
  CompPoly.Extension.Ext.ofFn fun i ↦ val ctx nodes (x.getD i 0)

/-- **The product of coordinate nodes** over the extension `P`, reduced by its table. -/
theorem Dag.mulN_built (P : CompPoly.Extension.ExtensionParams F) (g : Dag F) (hg : g.Ok)
    (x y : List Nat) (hx : ∀ i < P.d, x.getD i 0 < g.nodes.size)
    (hy : ∀ i < P.d, y.getD i 0 < g.nodes.size) :
    BuiltL g (g.mulN P x y) P.d fun ctx m ↦
      CompPoly.Extension.Ext.coeffNat (extOf P ctx g.nodes x * extOf P ctx g.nodes y) m := by
  unfold Dag.mulN
  have b0 := g.leaf_built hg (.const 0) trivial
  generalize g.intern (.const 0) = q at b0 ⊢
  obtain ⟨g1, z⟩ := q
  dsimp only at b0 ⊢
  have hz0 (g' : Dag F) (e : g1.Ext g') (ctx : Ctx F) : val ctx g'.nodes z = 0 := by
    rw [b0.mono e ctx]; rfl
  have hxv (g' : Dag F) (e : g.Ext g') (ctx : Ctx F) (i : Nat) (hi : i < P.d) :
      val ctx g'.nodes (x.getD i 0) = val ctx g.nodes (x.getD i 0) := e.val_eq ctx _ (hx i hi)
  have hyv (g' : Dag F) (e : g.Ext g') (ctx : Ctx F) (i : Nat) (hi : i < P.d) :
      val ctx g'.nodes (y.getD i 0) = val ctx g.nodes (y.getD i 0) := e.val_eq ctx _ (hy i hi)
  let tbl := (CompPoly.Extension.Ext.red P).toArray
  let R : Nat → Dag F × List Nat := fun n ↦
    (List.range n).foldl (Dag.mulNStep P z x y tbl) (g1, [])
  have key : ∀ n ≤ P.d,
      (R n).1.Ok ∧ g1.Ext (R n).1 ∧ (R n).2.length = n ∧
        (∀ i < n, (R n).2.getD i 0 < (R n).1.nodes.size) ∧
        ∀ ctx, ∀ i < n, val ctx (R n).1.nodes ((R n).2.getD i 0) =
          CompPoly.Extension.Ext.coeffNat (extOf P ctx g.nodes x * extOf P ctx g.nodes y) i := by
    intro n hn
    induction n with
    | zero =>
      exact ⟨b0.ok, Dag.Ext.refl _, rfl, fun i hi ↦ absurd hi (Nat.not_lt_zero _),
        fun _ i hi ↦ absurd hi (Nat.not_lt_zero _)⟩
    | succ n ih =>
      obtain ⟨r1, r2, r3, r4, r5⟩ := ih (by omega)
      have hR : R (n + 1) = Dag.mulNStep P z x y tbl (R n) n := by
        simp only [R, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hR]
      generalize R n = r at r1 r2 r3 r4 r5 ⊢
      obtain ⟨g', out⟩ := r
      dsimp only at r1 r2 r3 r4 r5 b0 ⊢
      unfold Dag.mulNStep
      have e : g.Ext g' := b0.ext.trans r2
      have bm := g'.mulCoord_built r1 z P.d x y
        (fun k ↦ CompPoly.Extension.Ext.coeffNat (tbl.getD k 0) n) n
        (by have := b0.lt; have := r2.1; dsimp only at *; omega)
        (fun i hi ↦ by have := hx i hi; have := e.1; omega)
        (fun i hi ↦ by have := hy i hi; have := e.1; omega)
      generalize g'.mulCoord z P.d x y _ n = q at bm ⊢
      obtain ⟨g'', c⟩ := q
      dsimp only at bm ⊢
      have hlt (i : Nat) (hi : i < n) : out.getD i 0 < g'.nodes.size := r4 i hi
      refine ⟨bm.ok, r2.trans bm.ext, by rw [List.length_append, r3, List.length_singleton],
        fun i hi ↦ ?_, fun ctx i hi ↦ ?_⟩
      · rcases Nat.lt_or_ge i n with h | h
        · rw [List.getD_append _ _ _ _ (by omega)]
          have := hlt i h; have := bm.ext.1; dsimp only at *; omega
        · obtain rfl : i = n := by omega
          rw [List.getD_append_right _ _ _ _ (by omega), r3, Nat.sub_self]
          exact bm.lt
      · rcases Nat.lt_or_ge i n with h | h
        · rw [List.getD_append _ _ _ _ (by omega), bm.ext.val_eq ctx _ (hlt i h), r5 ctx i h]
        · obtain rfl : i = n := by omega
          rw [List.getD_append_right _ _ _ _ (by omega), r3, Nat.sub_self, List.getD_cons_zero,
            bm.value]
          have hv : ∀ k, (Dag.convTree z P.d x y k).eval (val ctx g'.nodes) =
              CompPoly.Extension.Ext.conv (extOf P ctx g.nodes x) (extOf P ctx g.nodes y) k := by
            intro k
            rw [convTree_eval P z x y k _ (hz0 g' r2 ctx)]
            congr 2 <;> funext j
            · exact hxv g' e ctx j j.isLt
            · exact hyv g' e ctx j j.isLt
          simp only [hv]
          rw [CompPoly.Extension.Ext.coeffNat_of_lt _ (by omega),
            CompPoly.Extension.Ext.coeff_mul_reduce]
          refine congrArg₂ (· + ·) rfl (congrArg List.sum (List.map_congr_left fun k hk ↦ ?_))
          rw [List.mem_range'_1] at hk
          have hk2 : k < 2 * P.d - 1 := by omega
          rw [mul_comm]
          congr 1
          have hkt : k < tbl.size := by simp only [tbl, Vector.size_toArray]; omega
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hkt, Option.getD_some, Vector.getElem_toArray, CompPoly.Extension.Ext.red_getElem hk2,
            CompPoly.Extension.Ext.coeffNat_of_lt _ (by omega)]
  obtain ⟨r1, r2, r3, r4, r5⟩ := key P.d le_rfl
  exact ⟨r1, b0.ext.trans r2, r3, r4, r5⟩

/-- Built coordinates of an element are its coordinate nodes. -/
theorem BuiltL.extOf_eq {P : CompPoly.Extension.ExtensionParams F} {g : Dag F}
    {r : Dag F × List Nat} {v : Ctx F → CompPoly.Extension.Ext P}
    (h : BuiltL g r P.d fun ctx i ↦ CompPoly.Extension.Ext.coeffNat (v ctx) i) {g' : Dag F}
    (e : r.1.Ext g') (ctx : Ctx F) : extOf P ctx g'.nodes r.2 = v ctx := by
  ext i
  rw [extOf, CompPoly.Extension.Ext.coeff_ofFn, h.mono e ctx i i.isLt,
    CompPoly.Extension.Ext.coeffNat_coe]

omit [DecidableEq F] [Hashable F] in
theorem coeffNat_ofFn {P : CompPoly.Extension.ExtensionParams F} (f : Fin P.d → F) (i : Nat)
    (hi : i < P.d) : CompPoly.Extension.Ext.coeffNat (CompPoly.Extension.Ext.ofFn f) i = f ⟨i, hi⟩
    := by
  rw [CompPoly.Extension.Ext.coeffNat_of_lt _ hi, CompPoly.Extension.Ext.coeff_ofFn]

/-- Leaves of `d` loaded or scalar nodes. -/
theorem Dag.internAll_range_built (P : CompPoly.Extension.ExtensionParams F) (g : Dag F)
    (hg : g.Ok) (n : Nat → Node F) (hn : ∀ j, (n j).Below 0) :
    BuiltL g (g.internAll ((List.range P.d).map n)) P.d fun ctx i ↦
      CompPoly.Extension.Ext.coeffNat (CompPoly.Extension.Ext.ofFn (P := P) fun j ↦
        (n j).value ctx fun _ ↦ 0) i := by
  have b := Dag.internAll_built ((List.range P.d).map n) (fun m hm ↦ by
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hm; exact hn j) g hg
  rw [List.length_map, List.length_range] at b
  refine b.of_eq fun ctx i hi ↦ ?_
  rw [coeffNat_ofFn _ i hi, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi]
  rfl

/-- **The coordinates of an extension expression** have its value over the extension `P`. -/
theorem Dag.ofExt_built (P : CompPoly.Extension.ExtensionParams F) (np : Nat)
    (e : Lookup.ExtExpr F) (g : Dag F) (hg : g.Ok) :
    BuiltL g (Dag.ofExt P np e g) P.d fun ctx i ↦
      CompPoly.Extension.Ext.coeffNat (e.eval (ctx.envQ P np) (ctx.auxQ P np)) i := by
  induction e generalizing g with
  | base e =>
    unfold Dag.ofExt
    have b0 := Dag.ofExpr_built (Dag.pubBelow np e) g hg
    generalize Dag.ofExpr (Dag.pubBelow np e) g = q0 at b0 ⊢
    obtain ⟨g1, i⟩ := q0
    dsimp only at b0 ⊢
    have b1 := g1.leaf_built b0.ok (.const 0) trivial
    generalize g1.intern (.const 0) = q1 at b1 ⊢
    obtain ⟨g2, z⟩ := q1
    dsimp only at b0 b1 ⊢
    have hd := P.d_pos
    have hlen : (i :: List.replicate (P.d - 1) z).length = P.d := by
      simp only [List.length_cons, List.length_replicate]; omega
    refine ⟨b1.ok, b0.ext.trans b1.ext, hlen, fun j hj ↦ ?_, fun ctx j hj ↦ ?_⟩
    · rcases j with _ | j
      · simp only [List.getD_cons_zero]; have := b0.lt; have := b1.ext.1; dsimp only at *; omega
      · have hrep : (List.replicate (P.d - 1) z).getD j 0 = z := by
          simp [List.getD_eq_getElem?_getD, show j < P.d - 1 by omega]
        simp only [List.getD_cons_succ, hrep]
        exact b1.lt
    · simp only [Lookup.ExtExpr.eval, Expr.eval_envQ, CompPoly.Extension.Ext.ofBase,
        coeffNat_ofFn _ j hj]
      rcases j with _ | j
      · simp only [List.getD_cons_zero, ite_true]
        exact b0.mono b1.ext ctx
      · have hrep : (List.replicate (P.d - 1) z).getD j 0 = z := by
          simp [List.getD_eq_getElem?_getD, show j < P.d - 1 by omega]
        simp only [List.getD_cons_succ, hrep, Nat.add_one_ne_zero, ite_false]
        rw [b1.value]; rfl
  | perm c =>
    unfold Dag.ofExt
    exact (Dag.internAll_range_built P g hg (fun j ↦ .load (.permCur (P.d * c + j)))
      fun _ ↦ trivial).of_eq fun ctx i hi ↦ rfl
  | permNext c =>
    unfold Dag.ofExt
    exact (Dag.internAll_range_built P g hg (fun j ↦ .load (.permNext (P.d * c + j)))
      fun _ ↦ trivial).of_eq fun ctx i hi ↦ rfl
  | challenge k =>
    unfold Dag.ofExt
    refine (Dag.internAll_range_built P g hg (fun j ↦ .scalar (np + P.d * (k + 1) + j))
      fun _ ↦ trivial).of_eq fun ctx i hi ↦ ?_
    simp only [Lookup.ExtExpr.eval, Ctx.auxQ, Ctx.scalarsExt, Node.value]
  | terminal =>
    unfold Dag.ofExt
    exact (Dag.internAll_range_built P g hg (fun j ↦ .scalar (np + j))
      fun _ ↦ trivial).of_eq fun ctx i hi ↦ rfl
  | add a b iha ihb =>
    unfold Dag.ofExt
    have b1 := iha g hg
    generalize Dag.ofExt P np a g = q1 at b1 ⊢
    obtain ⟨g1, xs⟩ := q1
    dsimp only at b1 ⊢
    have b2 := ihb g1 b1.ok
    generalize Dag.ofExt P np b g1 = q2 at b2 ⊢
    obtain ⟨g2, ys⟩ := q2
    dsimp only at b1 b2 ⊢
    have b3 := g2.opN_built .add xs ys b2.ok (by rw [b1.len, b2.len])
      (fun i hi ↦ by
        rw [b1.len] at hi; have := b1.lt i hi; have := b2.ext.1; dsimp only at *; omega)
      (fun i hi ↦ by rw [b1.len] at hi; exact b2.lt i hi)
    rw [b1.len] at b3
    refine ⟨b3.ok, b1.ext.trans (b2.ext.trans b3.ext), b3.len, b3.lt, fun ctx i hi ↦ ?_⟩
    rw [b3.value ctx i hi, b1.mono b2.ext ctx i hi, b2.value ctx i hi]
    simp only [Lookup.ExtExpr.eval, Op.eval, CompPoly.Extension.Ext.coeffNat_of_lt _ hi,
      CompPoly.Extension.Ext.coeff_add]
  | sub a b iha ihb =>
    unfold Dag.ofExt
    have b1 := iha g hg
    generalize Dag.ofExt P np a g = q1 at b1 ⊢
    obtain ⟨g1, xs⟩ := q1
    dsimp only at b1 ⊢
    have b2 := ihb g1 b1.ok
    generalize Dag.ofExt P np b g1 = q2 at b2 ⊢
    obtain ⟨g2, ys⟩ := q2
    dsimp only at b1 b2 ⊢
    have b3 := g2.opN_built .sub xs ys b2.ok (by rw [b1.len, b2.len])
      (fun i hi ↦ by
        rw [b1.len] at hi; have := b1.lt i hi; have := b2.ext.1; dsimp only at *; omega)
      (fun i hi ↦ by rw [b1.len] at hi; exact b2.lt i hi)
    rw [b1.len] at b3
    refine ⟨b3.ok, b1.ext.trans (b2.ext.trans b3.ext), b3.len, b3.lt, fun ctx i hi ↦ ?_⟩
    rw [b3.value ctx i hi, b1.mono b2.ext ctx i hi, b2.value ctx i hi]
    simp only [Lookup.ExtExpr.eval, Op.eval, CompPoly.Extension.Ext.coeffNat_of_lt _ hi,
      CompPoly.Extension.Ext.coeff_sub]
  | mul a b iha ihb =>
    unfold Dag.ofExt
    have b1 := iha g hg
    generalize Dag.ofExt P np a g = q1 at b1 ⊢
    obtain ⟨g1, xs⟩ := q1
    dsimp only at b1 ⊢
    have b2 := ihb g1 b1.ok
    generalize Dag.ofExt P np b g1 = q2 at b2 ⊢
    obtain ⟨g2, ys⟩ := q2
    dsimp only at b1 b2 ⊢
    have b3 := g2.mulN_built P b2.ok xs ys
      (fun i hi ↦ by have := b1.lt i hi; have := b2.ext.1; dsimp only at *; omega)
      (fun i hi ↦ b2.lt i hi)
    refine ⟨b3.ok, b1.ext.trans (b2.ext.trans b3.ext), b3.len, b3.lt, fun ctx i hi ↦ ?_⟩
    rw [b3.value ctx i hi, b1.extOf_eq b2.ext ctx, b2.extOf_eq (Dag.Ext.refl _) ctx]
    rfl

end BuildExt

end CompStark.Stark.Prog
