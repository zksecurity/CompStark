/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Prog
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

/-- Four coordinates over the binomial extension `X⁴ = W`. -/
structure Coords (F : Type) (W : F) where
  c0 : F
  c1 : F
  c2 : F
  c3 : F

namespace Coords

variable [Field F] {W : F}

instance : Add (Coords F W) :=
  ⟨fun x y ↦ ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2, x.c3 + y.c3⟩⟩

instance : Sub (Coords F W) :=
  ⟨fun x y ↦ ⟨x.c0 - y.c0, x.c1 - y.c1, x.c2 - y.c2, x.c3 - y.c3⟩⟩

instance : Mul (Coords F W) :=
  ⟨fun x y ↦ ⟨x.c0 * y.c0 + W * ((x.c1 * y.c3 + x.c2 * y.c2) + x.c3 * y.c1),
    (x.c0 * y.c1 + x.c1 * y.c0) + W * (x.c2 * y.c3 + x.c3 * y.c2),
    ((x.c0 * y.c2 + x.c1 * y.c1) + x.c2 * y.c0) + W * (x.c3 * y.c3),
    ((x.c0 * y.c3 + x.c1 * y.c2) + x.c2 * y.c1) + x.c3 * y.c0⟩⟩

/-- An element of the base field. -/
def base (x : F) : Coords F W := ⟨x, 0, 0, 0⟩

end Coords

/-- A row's values as an environment of extension expressions' base expressions, over `X⁴ = W`
with `np` public values: the base embedding of `Ctx.env`, public values from `np` on zero. -/
def Ctx.envQ [Field F] (W : F) (np : Nat) (ctx : Ctx F) : Expr.Env F (Coords F W) where
  cur c := .base (ctx.env.cur c)
  next c := .base (ctx.env.next c)
  prepCur c := .base (ctx.env.prepCur c)
  prepNext c := .base (ctx.env.prepNext c)
  periodic i := .base (ctx.env.periodic i)
  pub i := .base (if i < np then ctx.env.pub i else 0)
  const x := .base x
  isFirstRow := .base ctx.env.isFirstRow
  isLastRow := .base ctx.env.isLastRow
  isTransition := .base ctx.env.isTransition

/-- The coordinates of four scalars from `k`. -/
def Ctx.scalars4 [Field F] (W : F) (ctx : Ctx F) (k : Nat) : Coords F W :=
  ⟨ctx.scalar k, ctx.scalar (k + 1), ctx.scalar (k + 2), ctx.scalar (k + 3)⟩

/-- A row's permutation trace, challenges and terminal over `X⁴ = W`, with `np` public values:
column `c` from the loaded permutation columns `4 c, …, 4 c + 3`, the terminal's coordinates the
scalars from `np`, challenge `i`'s from `np + 4 (i + 1)`. -/
def Ctx.auxQ [Field F] (W : F) (np : Nat) (ctx : Ctx F) : Lookup.ExtExpr.Env (Coords F W) where
  perm c := ⟨ctx.src (.permCur (4 * c)), ctx.src (.permCur (4 * c + 1)),
    ctx.src (.permCur (4 * c + 2)), ctx.src (.permCur (4 * c + 3))⟩
  permNext c := ⟨ctx.src (.permNext (4 * c)), ctx.src (.permNext (4 * c + 1)),
    ctx.src (.permNext (4 * c + 2)), ctx.src (.permNext (4 * c + 3))⟩
  challenge i := ctx.scalars4 W (np + 4 * (i + 1))
  terminal := ctx.scalars4 W np

/-- Evaluating a base expression over `X⁴ = W` with `np` public values embeds the value of its
public values below `np` (`Dag.pubBelow`). -/
theorem Expr.eval_envQ [Field F] (W : F) (np : Nat) (ctx : Ctx F) :
    ∀ e : Expr F, e.eval (ctx.envQ W np) = .base ((Dag.pubBelow np e).eval ctx.env)
  | .add a b => by
    simp only [Expr.eval, Dag.pubBelow]
    rw [Expr.eval_envQ W np ctx a, Expr.eval_envQ W np ctx b]
    show (⟨_, _, _, _⟩ : Coords F W) = ⟨_, _, _, _⟩
    simp only [Coords.base, add_zero]
  | .sub a b => by
    simp only [Expr.eval, Dag.pubBelow]
    rw [Expr.eval_envQ W np ctx a, Expr.eval_envQ W np ctx b]
    show (⟨_, _, _, _⟩ : Coords F W) = ⟨_, _, _, _⟩
    simp only [Coords.base, sub_zero]
  | .mul a b => by
    simp only [Expr.eval, Dag.pubBelow]
    rw [Expr.eval_envQ W np ctx a, Expr.eval_envQ W np ctx b]
    show (⟨_, _, _, _⟩ : Coords F W) = ⟨_, _, _, _⟩
    simp only [Coords.base, mul_zero, zero_mul, add_zero]
  | .pub i => by
    simp only [Expr.eval, Dag.pubBelow]
    by_cases h : i < np
    · simp only [h, ite_true, Expr.eval]
      show Coords.base (if i < np then ctx.env.pub i else 0) = _
      rw [ite_eq_left h]
    · simp only [h, ite_false, Expr.eval]
      show Coords.base (if i < np then ctx.env.pub i else 0) = _
      rw [ite_eq_right h]
      rfl
  | .cur _ | .next _ | .prepCur _ | .prepNext _ | .periodic _ | .const _ | .isFirstRow
  | .isLastRow | .isTransition => rfl

section BuildExt
variable [DecidableEq F] [Hashable F] [Field F]

/-- `r` is built on `g`: a well-formed extension of it with four nodes, the coordinates `v` on
every row. -/
structure Built4 {W : F} (g : Dag F) (r : Dag F × Dag.Quad) (v : Ctx F → Coords F W) :
    Prop where
  ok : r.1.Ok
  ext : g.Ext r.1
  lt : r.2.1 < r.1.nodes.size ∧ r.2.2.1 < r.1.nodes.size ∧ r.2.2.2.1 < r.1.nodes.size ∧
    r.2.2.2.2 < r.1.nodes.size
  value : ∀ ctx, (⟨val ctx r.1.nodes r.2.1, val ctx r.1.nodes r.2.2.1,
    val ctx r.1.nodes r.2.2.2.1, val ctx r.1.nodes r.2.2.2.2⟩ : Coords F W) = v ctx

theorem Built4.of_eq {W : F} {g : Dag F} {r : Dag F × Dag.Quad} {v w : Ctx F → Coords F W}
    (h : Built4 g r v) (e : ∀ ctx, v ctx = w ctx) : Built4 g r w :=
  ⟨h.ok, h.ext, h.lt, fun ctx ↦ by rw [h.value, e]⟩

/-- Four nodes built one after another. -/
theorem Built4.of_built {W : F} {g : Dag F} {r0 r1 r2 r3 : Dag F × Nat}
    {v0 v1 v2 v3 : Ctx F → F} (h0 : Built g r0 v0) (h1 : Built r0.1 r1 v1)
    (h2 : Built r1.1 r2 v2) (h3 : Built r2.1 r3 v3) :
    Built4 (W := W) g (r3.1, (r0.2, r1.2, r2.2, r3.2))
      fun ctx ↦ ⟨v0 ctx, v1 ctx, v2 ctx, v3 ctx⟩ := by
  have e01 := h1.ext
  have e12 := h2.ext
  have e23 := h3.ext
  refine ⟨h3.ok, h0.ext.trans (e01.trans (e12.trans e23)), ⟨?_, ?_, ?_, h3.lt⟩, fun ctx ↦ ?_⟩
  · have := h0.lt; have := e01.1; have := e12.1; have := e23.1; dsimp only; omega
  · have := h1.lt; have := e12.1; have := e23.1; dsimp only; omega
  · have := h2.lt; have := e23.1; dsimp only; omega
  · dsimp only
    rw [h0.mono (e01.trans (e12.trans e23)) ctx, h1.mono (e12.trans e23) ctx, h2.mono e23 ctx,
      h3.value]

/-- A leaf node interned. -/
theorem Dag.leaf_built (g : Dag F) (hg : g.Ok) (n : Node F) (hn : n.Below 0) :
    Built g (g.intern n) fun ctx ↦ n.value ctx fun _ ↦ 0 :=
  (g.intern_built hg n (hn.mono (Nat.zero_le _))).of_eq fun ctx ↦ by
    cases n with
    | bin o a b => exact absurd hn.1 (Nat.not_lt_zero a)
    | _ => rfl

/-- Coordinatewise operations on two built quadruples. -/
theorem Built4.op4 {W : F} {g : Dag F} {r1 r2 : Dag F × Dag.Quad} {v1 v2 : Ctx F → Coords F W}
    (h1 : Built4 g r1 v1) (h2 : Built4 r1.1 r2 v2) (o : Op)
    (hc : ∀ x y : Coords F W, (⟨o.eval x.c0 y.c0, o.eval x.c1 y.c1, o.eval x.c2 y.c2,
      o.eval x.c3 y.c3⟩ : Coords F W) = o.eval x y) :
    Built4 g (r2.1.op4 o r1.2 r2.2) fun ctx ↦ o.eval (v1 ctx) (v2 ctx) := by
  have e12 := h1.ext.trans h2.ext
  obtain ⟨g2, x0, x1, x2, x3⟩ := r2
  obtain ⟨g1, y0, y1, y2, y3⟩ := r1
  obtain ⟨l0, l1, l2, l3⟩ := h1.lt
  obtain ⟨m0, m1, m2, m3⟩ := h2.lt
  dsimp only at *
  have hs : g1.nodes.size ≤ g2.nodes.size := h2.ext.1
  unfold Dag.op4
  have b0 := g2.op_built h2.ok o y0 x0 (by omega) m0
  generalize g2.op o y0 x0 = q0 at b0 ⊢
  obtain ⟨g3, c0⟩ := q0
  dsimp only
  have s0 : g2.nodes.size ≤ g3.nodes.size := b0.ext.1
  have b1 := g3.op_built b0.ok o y1 x1 (by omega) (by omega)
  generalize g3.op o y1 x1 = q1 at b1 ⊢
  obtain ⟨g4, c1⟩ := q1
  dsimp only
  have s1 : g3.nodes.size ≤ g4.nodes.size := b1.ext.1
  have b2 := g4.op_built b1.ok o y2 x2 (by omega) (by omega)
  generalize g4.op o y2 x2 = q2 at b2 ⊢
  obtain ⟨g5, c2⟩ := q2
  dsimp only
  have s2 : g4.nodes.size ≤ g5.nodes.size := b2.ext.1
  have b3 := g5.op_built b2.ok o y3 x3 (by omega) (by omega)
  generalize g5.op o y3 x3 = q3 at b3 ⊢
  obtain ⟨g6, c3⟩ := q3
  dsimp only at b0 b1 b2 b3 ⊢
  have s3 : g5.nodes.size ≤ g6.nodes.size := b3.ext.1
  have e3 := b1.ext.trans (b2.ext.trans b3.ext)
  have t0 : c0 < g3.nodes.size := b0.lt
  have t1 : c1 < g4.nodes.size := b1.lt
  have t2 : c2 < g5.nodes.size := b2.lt
  refine ⟨b3.ok, e12.trans (b0.ext.trans e3), ⟨show c0 < g6.nodes.size by omega,
    show c1 < g6.nodes.size by omega, show c2 < g6.nodes.size by omega, b3.lt⟩, fun ctx ↦ ?_⟩
  · have ev (g' : Dag F) (e : g2.Ext g') (i : Nat) (hi : i < g2.nodes.size) :
        val ctx g'.nodes i = val ctx g2.nodes i := e.val_eq ctx i hi
    have e1 := b0.ext.trans b1.ext
    have e2 := e1.trans b2.ext
    rw [b0.mono e3 ctx, b1.mono (b2.ext.trans b3.ext) ctx, b2.mono b3.ext ctx, b3.value,
      ev _ b0.ext, ev _ b0.ext, ev _ e1, ev _ e1, ev _ e2, ev _ e2,
      h2.ext.val_eq ctx y0 l0, h2.ext.val_eq ctx y1 l1, h2.ext.val_eq ctx y2 l2,
      h2.ext.val_eq ctx y3 l3, ← hc]
    all_goals try omega
    have hv1 := h1.value ctx
    have hv2 := h2.value ctx
    dsimp only at hv1 hv2
    rw [← hv1, ← hv2]

/-- An expression over nodes built on an extension `g'` of `g` with its leaves `g`'s nodes, valued
on `g`'s nodes. -/
theorem Dag.ofTree_built' {g g' : Dag F} (e : g.Ext g') (hg' : g'.Ok) (t : Dag.Tree)
    (ht : t.Below g.nodes.size) :
    Built g' (g'.ofTree t) fun ctx ↦ t.eval (val ctx g.nodes) :=
  (g'.ofTree_built hg' t (ht.mono e.1)).of_eq fun ctx ↦
    Dag.Tree.eval_congr _ _ g.nodes.size (fun i hi ↦ e.val_eq ctx i hi) t ht

/-- The product of two built quadruples over `X⁴ = W`, `w` a node of value `W`. -/
theorem Dag.mul4_built {W : F} (g : Dag F) (hg : g.Ok) (w : Nat) (hw : w < g.nodes.size)
    (hwv : ∀ ctx, val ctx g.nodes w = W) (x y : Dag.Quad) (hx : x.1 < g.nodes.size ∧
      x.2.1 < g.nodes.size ∧ x.2.2.1 < g.nodes.size ∧ x.2.2.2 < g.nodes.size)
    (hy : y.1 < g.nodes.size ∧ y.2.1 < g.nodes.size ∧ y.2.2.1 < g.nodes.size ∧
      y.2.2.2 < g.nodes.size) :
    Built4 g (g.mul4 w x y) fun ctx ↦
      (⟨val ctx g.nodes x.1, val ctx g.nodes x.2.1, val ctx g.nodes x.2.2.1,
        val ctx g.nodes x.2.2.2⟩ : Coords F W) *
      ⟨val ctx g.nodes y.1, val ctx g.nodes y.2.1, val ctx g.nodes y.2.2.1,
        val ctx g.nodes y.2.2.2⟩ := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  obtain ⟨y0, y1, y2, y3⟩ := y
  obtain ⟨hx0, hx1, hx2, hx3⟩ := hx
  obtain ⟨hy0, hy1, hy2, hy3⟩ := hy
  dsimp only at *
  unfold Dag.mul4
  dsimp only
  have b0 := Dag.ofTree_built' (Dag.Ext.refl g) hg
    (.op .add (.op .mul (.leaf x0) (.leaf y0)) (.op .mul (.leaf w) (.op .add (.op .add
      (.op .mul (.leaf x1) (.leaf y3)) (.op .mul (.leaf x2) (.leaf y2)))
      (.op .mul (.leaf x3) (.leaf y1)))))
    ⟨⟨hx0, hy0⟩, hw, ⟨⟨hx1, hy3⟩, hx2, hy2⟩, hx3, hy1⟩
  generalize Dag.ofTree g _ = q0 at b0 ⊢
  obtain ⟨g1, c0⟩ := q0
  dsimp only at b0 ⊢
  have b1 := Dag.ofTree_built' b0.ext b0.ok
    (.op .add (.op .add (.op .mul (.leaf x0) (.leaf y1)) (.op .mul (.leaf x1) (.leaf y0)))
      (.op .mul (.leaf w) (.op .add (.op .mul (.leaf x2) (.leaf y3))
        (.op .mul (.leaf x3) (.leaf y2)))))
    ⟨⟨⟨hx0, hy1⟩, hx1, hy0⟩, hw, ⟨hx2, hy3⟩, hx3, hy2⟩
  generalize Dag.ofTree g1 _ = q1 at b1 ⊢
  obtain ⟨g2, c1⟩ := q1
  dsimp only at b1 ⊢
  have b2 := Dag.ofTree_built' (b0.ext.trans b1.ext) b1.ok
    (.op .add (.op .add (.op .add (.op .mul (.leaf x0) (.leaf y2)) (.op .mul (.leaf x1) (.leaf y1)))
      (.op .mul (.leaf x2) (.leaf y0))) (.op .mul (.leaf w) (.op .mul (.leaf x3) (.leaf y3))))
    ⟨⟨⟨⟨hx0, hy2⟩, hx1, hy1⟩, hx2, hy0⟩, hw, hx3, hy3⟩
  generalize Dag.ofTree g2 _ = q2 at b2 ⊢
  obtain ⟨g3, c2⟩ := q2
  dsimp only at b2 ⊢
  have b3 := Dag.ofTree_built' (b0.ext.trans (b1.ext.trans b2.ext)) b2.ok
    (.op .add (.op .add (.op .add (.op .mul (.leaf x0) (.leaf y3)) (.op .mul (.leaf x1) (.leaf y2)))
      (.op .mul (.leaf x2) (.leaf y1))) (.op .mul (.leaf x3) (.leaf y0)))
    ⟨⟨⟨⟨hx0, hy3⟩, hx1, hy2⟩, hx2, hy1⟩, hx3, hy0⟩
  generalize Dag.ofTree g3 _ = q3 at b3 ⊢
  obtain ⟨g4, c3⟩ := q3
  dsimp only at b3 ⊢
  have s1 : g1.nodes.size ≤ g2.nodes.size := b1.ext.1
  have s2 : g2.nodes.size ≤ g3.nodes.size := b2.ext.1
  have s3 : g3.nodes.size ≤ g4.nodes.size := b3.ext.1
  have t0 : c0 < g1.nodes.size := b0.lt
  have t1 : c1 < g2.nodes.size := b1.lt
  have t2 : c2 < g3.nodes.size := b2.lt
  refine ⟨b3.ok, b0.ext.trans (b1.ext.trans (b2.ext.trans b3.ext)),
    ⟨show c0 < g4.nodes.size by omega, show c1 < g4.nodes.size by omega,
      show c2 < g4.nodes.size by omega, b3.lt⟩, fun ctx ↦ ?_⟩
  rw [b0.mono (b1.ext.trans (b2.ext.trans b3.ext)) ctx, b1.mono (b2.ext.trans b3.ext) ctx,
    b2.mono b3.ext ctx, b3.value]
  simp only [Dag.Tree.eval, Op.eval, hwv]
  rfl

/-- The coordinates of an extension expression have its value over `X⁴ = W`. -/
theorem Dag.ofExt_built (W : F) (np : Nat) (e : Lookup.ExtExpr F) (g : Dag F) (hg : g.Ok) :
    Built4 g (Dag.ofExt W np e g) fun ctx ↦ e.eval (ctx.envQ W np) (ctx.auxQ W np) := by
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
    dsimp only at b1 ⊢
    have t0 : i < g1.nodes.size := b0.lt
    have s1 : g1.nodes.size ≤ g2.nodes.size := b1.ext.1
    refine ⟨b1.ok, b0.ext.trans b1.ext, ⟨show i < g2.nodes.size by omega, b1.lt, b1.lt, b1.lt⟩,
      fun ctx ↦ ?_⟩
    rw [b0.mono b1.ext ctx, b1.value]
    simp only [Lookup.ExtExpr.eval, Expr.eval_envQ, Node.value]
    rfl
  | perm c =>
    unfold Dag.ofExt
    have b0 := g.leaf_built hg (.load (.permCur (4 * c))) trivial
    generalize g.intern (.load (.permCur (4 * c))) = q0 at b0 ⊢
    obtain ⟨g1, c0⟩ := q0
    dsimp only at b0 ⊢
    have b1 := g1.leaf_built b0.ok (.load (.permCur (4 * c + 1))) trivial
    generalize g1.intern (.load (.permCur (4 * c + 1))) = q1 at b1 ⊢
    obtain ⟨g2, c1⟩ := q1
    dsimp only at b1 ⊢
    have b2 := g2.leaf_built b1.ok (.load (.permCur (4 * c + 2))) trivial
    generalize g2.intern (.load (.permCur (4 * c + 2))) = q2 at b2 ⊢
    obtain ⟨g3, c2⟩ := q2
    dsimp only at b2 ⊢
    have b3 := g3.leaf_built b2.ok (.load (.permCur (4 * c + 3))) trivial
    generalize g3.intern (.load (.permCur (4 * c + 3))) = q3 at b3 ⊢
    obtain ⟨g4, c3⟩ := q3
    dsimp only at b3 ⊢
    exact (Built4.of_built b0 b1 b2 b3).of_eq fun _ ↦ rfl
  | permNext c =>
    unfold Dag.ofExt
    have b0 := g.leaf_built hg (.load (.permNext (4 * c))) trivial
    generalize g.intern (.load (.permNext (4 * c))) = q0 at b0 ⊢
    obtain ⟨g1, c0⟩ := q0
    dsimp only at b0 ⊢
    have b1 := g1.leaf_built b0.ok (.load (.permNext (4 * c + 1))) trivial
    generalize g1.intern (.load (.permNext (4 * c + 1))) = q1 at b1 ⊢
    obtain ⟨g2, c1⟩ := q1
    dsimp only at b1 ⊢
    have b2 := g2.leaf_built b1.ok (.load (.permNext (4 * c + 2))) trivial
    generalize g2.intern (.load (.permNext (4 * c + 2))) = q2 at b2 ⊢
    obtain ⟨g3, c2⟩ := q2
    dsimp only at b2 ⊢
    have b3 := g3.leaf_built b2.ok (.load (.permNext (4 * c + 3))) trivial
    generalize g3.intern (.load (.permNext (4 * c + 3))) = q3 at b3 ⊢
    obtain ⟨g4, c3⟩ := q3
    dsimp only at b3 ⊢
    exact (Built4.of_built b0 b1 b2 b3).of_eq fun _ ↦ rfl
  | challenge i =>
    unfold Dag.ofExt
    have b0 := g.leaf_built hg (.scalar (np + 4 * (i + 1))) trivial
    generalize g.intern (.scalar (np + 4 * (i + 1))) = q0 at b0 ⊢
    obtain ⟨g1, c0⟩ := q0
    dsimp only at b0 ⊢
    have b1 := g1.leaf_built b0.ok (.scalar (np + 4 * (i + 1) + 1)) trivial
    generalize g1.intern (.scalar (np + 4 * (i + 1) + 1)) = q1 at b1 ⊢
    obtain ⟨g2, c1⟩ := q1
    dsimp only at b1 ⊢
    have b2 := g2.leaf_built b1.ok (.scalar (np + 4 * (i + 1) + 2)) trivial
    generalize g2.intern (.scalar (np + 4 * (i + 1) + 2)) = q2 at b2 ⊢
    obtain ⟨g3, c2⟩ := q2
    dsimp only at b2 ⊢
    have b3 := g3.leaf_built b2.ok (.scalar (np + 4 * (i + 1) + 3)) trivial
    generalize g3.intern (.scalar (np + 4 * (i + 1) + 3)) = q3 at b3 ⊢
    obtain ⟨g4, c3⟩ := q3
    dsimp only at b3 ⊢
    exact (Built4.of_built b0 b1 b2 b3).of_eq fun _ ↦ rfl
  | terminal =>
    unfold Dag.ofExt
    have b0 := g.leaf_built hg (.scalar (np)) trivial
    generalize g.intern (.scalar (np)) = q0 at b0 ⊢
    obtain ⟨g1, c0⟩ := q0
    dsimp only at b0 ⊢
    have b1 := g1.leaf_built b0.ok (.scalar (np + 1)) trivial
    generalize g1.intern (.scalar (np + 1)) = q1 at b1 ⊢
    obtain ⟨g2, c1⟩ := q1
    dsimp only at b1 ⊢
    have b2 := g2.leaf_built b1.ok (.scalar (np + 2)) trivial
    generalize g2.intern (.scalar (np + 2)) = q2 at b2 ⊢
    obtain ⟨g3, c2⟩ := q2
    dsimp only at b2 ⊢
    have b3 := g3.leaf_built b2.ok (.scalar (np + 3)) trivial
    generalize g3.intern (.scalar (np + 3)) = q3 at b3 ⊢
    obtain ⟨g4, c3⟩ := q3
    dsimp only at b3 ⊢
    exact (Built4.of_built b0 b1 b2 b3).of_eq fun _ ↦ rfl
  | add a b iha ihb =>
    unfold Dag.ofExt
    have b0 := iha g hg
    generalize Dag.ofExt W np a g = q0 at b0 ⊢
    obtain ⟨g1, x⟩ := q0
    dsimp only at b0 ⊢
    have b1 := ihb g1 b0.ok
    generalize Dag.ofExt W np b g1 = q1 at b1 ⊢
    obtain ⟨g2, y⟩ := q1
    dsimp only at b1 ⊢
    exact Built4.op4 b0 b1 .add fun _ _ ↦ rfl
  | sub a b iha ihb =>
    unfold Dag.ofExt
    have b0 := iha g hg
    generalize Dag.ofExt W np a g = q0 at b0 ⊢
    obtain ⟨g1, x⟩ := q0
    dsimp only at b0 ⊢
    have b1 := ihb g1 b0.ok
    generalize Dag.ofExt W np b g1 = q1 at b1 ⊢
    obtain ⟨g2, y⟩ := q1
    dsimp only at b1 ⊢
    exact Built4.op4 b0 b1 .sub fun _ _ ↦ rfl
  | mul a b iha ihb =>
    unfold Dag.ofExt
    have b0 := iha g hg
    generalize Dag.ofExt W np a g = q0 at b0 ⊢
    obtain ⟨g1, x⟩ := q0
    dsimp only at b0 ⊢
    have b1 := ihb g1 b0.ok
    generalize Dag.ofExt W np b g1 = q1 at b1 ⊢
    obtain ⟨g2, y⟩ := q1
    dsimp only at b1 ⊢
    have b2 := g2.leaf_built b1.ok (.const W) trivial
    generalize g2.intern (.const W) = q2 at b2 ⊢
    obtain ⟨g3, w⟩ := q2
    dsimp only at b2 ⊢
    have e12 : g1.Ext g3 := b1.ext.trans b2.ext
    have s2 : g2.nodes.size ≤ g3.nodes.size := b2.ext.1
    have s1 : g1.nodes.size ≤ g2.nodes.size := b1.ext.1
    obtain ⟨x0, x1, x2, x3⟩ := x
    obtain ⟨y0, y1, y2, y3⟩ := y
    obtain ⟨hx0, hx1, hx2, hx3⟩ := b0.lt
    obtain ⟨hy0, hy1, hy2, hy3⟩ := b1.lt
    have b3 := g3.mul4_built (W := W) b2.ok w b2.lt (fun ctx ↦ b2.value ctx)
      (x0, x1, x2, x3) (y0, y1, y2, y3)
      (by dsimp only at *; omega) (by dsimp only at *; omega)
    refine ⟨b3.ok, b0.ext.trans (b1.ext.trans (b2.ext.trans b3.ext)), b3.lt, fun ctx ↦ ?_⟩
    rw [b3.value, Lookup.ExtExpr.eval, ← b0.value ctx, ← b1.value ctx]
    dsimp only at *
    rw [e12.val_eq ctx x0 hx0, e12.val_eq ctx x1 hx1, e12.val_eq ctx x2 hx2,
      e12.val_eq ctx x3 hx3, b2.ext.val_eq ctx y0 hy0, b2.ext.val_eq ctx y1 hy1,
      b2.ext.val_eq ctx y2 hy2, b2.ext.val_eq ctx y3 hy3]

end BuildExt

end CompStark.Stark.Prog
