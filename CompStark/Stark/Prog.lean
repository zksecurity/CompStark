/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Lookup.LogUp
public import CompPoly.Fields.Extension.Arithmetic
public import Std.Data.HashMap.Basic

/-! # Straight-line programs for constraints

A program (`Prog`) evaluates constraints on one row: straight-line code over registers whose
instructions load a column into a register, combine two operands, or add an operand times a weight
to the accumulators, one per coordinate of the weights. An operand is a register, a column of the
trace at the current or next row, read where it is, or a constant. Run on a block of rows, every
instruction is one vectorized pass over the block.

`compile` builds a program from constraints:

* hash-consing: every subexpression is a node of a graph (`Dag`) with its operands as nodes, and
  equal nodes are one, with the operands of sums and products in order;
* constant folding: an operation on constants is a constant, and adding zero, subtracting zero,
  subtracting a node from itself and multiplying by zero or one simplify;
* the nodes in order, each constraint's accumulation after its nodes, then register allocation:
  a node gets a free register when it is computed and frees it at its last use.

An extension expression (`Lookup.ExtExpr`) is `d` nodes, its coordinates over an extension
`F[X] / f` of degree `d` (`CompPoly.Extension.ExtensionParams`), products reduced by the table of
`X^k mod f`; its challenges and terminal are scalars of the run, as public values are.

`Prog.run` runs a program on any `Machine`: the field's values row by row (`fieldMachine`), or
blocks of packed words.
-/

@[expose] public section
namespace CompStark.Stark.Prog

/-- A column a program loads into a register: the trace's at the next row, the preprocessed
trace's or the permutation trace's at the current or next row, a periodic column, or a row
selector. -/
inductive Src where
  | next (c : Nat)
  | prepCur (c : Nat)
  | prepNext (c : Nat)
  | permCur (c : Nat)
  | permNext (c : Nat)
  | periodic (i : Nat)
  | isFirstRow
  | isLastRow
  | isTransition
  deriving DecidableEq, Hashable

/-- An operand: a register, column `c` of the trace at the current row, or a constant. -/
inductive Opd (F : Type) where
  | reg (r : Nat)
  | cur (c : Nat)
  | const (x : F)
  deriving DecidableEq

/-- A binary operation. -/
inductive Op where
  | add
  | sub
  | mul
  deriving DecidableEq, Hashable

/-- The operation on values. -/
def Op.eval {α : Type*} [Add α] [Sub α] [Mul α] : Op → α → α → α
  | add, x, y => x + y
  | sub, x, y => x - y
  | mul, x, y => x * y

/-- An instruction: register `d` gets a loaded column (`load`), a scalar of the run (`scalar`) or
an operation on two operands (`bin`); or the accumulators get an operand times the weight `w` of
the run (`acc`). -/
inductive Instr (F : Type) where
  | load (d : Nat) (s : Src)
  | scalar (d i : Nat)
  | bin (op : Op) (d : Nat) (a b : Opd F)
  | acc (a : Opd F) (w : Nat)
  deriving DecidableEq

/-- A program: its code on the registers `0, …, regs - 1`, and its outputs. -/
structure _root_.CompStark.Stark.Prog (F : Type) where
  code : Array (Instr F)
  regs : Nat
  outs : Array (Opd F)

/-! ### Running a program -/

/-- What a program runs on: a state and the effect of every kind of instruction on it. -/
structure Machine (F σ : Type) where
  load : Nat → Src → σ → σ
  scalar : Nat → Nat → σ → σ
  bin : Op → Nat → Opd F → Opd F → σ → σ
  acc : Opd F → Nat → σ → σ

/-- One instruction on a machine. -/
@[inline] def Instr.exec {F σ : Type} (M : Machine F σ) : Instr F → σ → σ
  | load d s => M.load d s
  | scalar d i => M.scalar d i
  | bin op d a b => M.bin op d a b
  | acc a w => M.acc a w

/-- Run code on a machine from a state. -/
@[inline] def run {F σ : Type} (M : Machine F σ) (code : Array (Instr F)) (s : σ) : σ :=
  code.foldl (fun s i ↦ i.exec M s) s

/-- A row's values for a program: the trace's current row, the loaded columns, the scalars, and
the four coordinates `weight w j` of every weight. -/
structure Ctx (F : Type) where
  cur : Nat → F
  src : Src → F
  scalar : Nat → F
  weight : Nat → Nat → F

/-- The state of a program on a row: its registers and four accumulators. -/
structure St (F : Type) where
  reg : Nat → F
  acc : Nat → F

variable {F : Type}

/-- An operand's value on a row. -/
def Opd.val [Zero F] (ctx : Ctx F) (s : St F) : Opd F → F
  | .reg r => s.reg r
  | .cur c => ctx.cur c
  | .const x => x

/-- A program on the field's values of one row. -/
def fieldMachine [Field F] (ctx : Ctx F) : Machine F (St F) where
  load d src s := { s with reg := Function.update s.reg d (ctx.src src) }
  scalar d i s := { s with reg := Function.update s.reg d (ctx.scalar i) }
  bin op d a b s := { s with reg := Function.update s.reg d (op.eval (a.val ctx s) (b.val ctx s)) }
  acc a w s := { s with acc := fun j ↦ s.acc j + a.val ctx s * ctx.weight w j }

/-! ### The graph of a program -/

/-- A node: a column of the trace at the current row, a constant, a loaded column, a scalar, or an
operation on two earlier nodes. -/
inductive Node (F : Type) where
  | cur (c : Nat)
  | const (x : F)
  | load (s : Src)
  | scalar (i : Nat)
  | bin (op : Op) (a b : Nat)
  deriving DecidableEq, Hashable

/-- Hash-consed nodes: every node once, with its index. -/
structure Dag (F : Type) [DecidableEq F] [Hashable F] where
  nodes : Array (Node F)
  index : Std.HashMap (Node F) Nat

namespace Dag

variable [DecidableEq F] [Hashable F]

/-- No nodes. -/
def empty : Dag F := ⟨#[], ∅⟩

/-- The index of a node, added if new. -/
def intern (g : Dag F) (n : Node F) : Dag F × Nat :=
  match g.index[n]? with
  | some i => (g, i)
  | none =>
    let ⟨nodes, index⟩ := g
    let i := nodes.size
    (⟨nodes.push n, index.insert n i⟩, i)

/-- The constant of node `i`, if it is one. -/
def constAt (g : Dag F) (i : Nat) : Option F :=
  match g.nodes[i]? with
  | some (.const x) => some x
  | _ => none

/-- The node of an operation on nodes `a` and `b`, folded: constants combined, zero added or
subtracted, a node subtracted from itself, and a product with zero or one simplified; a sum's or
product's operands in order. -/
def op [Field F] (g : Dag F) (o : Op) (a b : Nat) : Dag F × Nat :=
  match o, g.constAt a, g.constAt b with
  | o, some x, some y => g.intern (.const (o.eval x y))
  | .add, some x, none => if x = 0 then (g, b) else g.intern (.bin .add (min a b) (max a b))
  | .add, none, some y => if y = 0 then (g, a) else g.intern (.bin .add (min a b) (max a b))
  | .add, none, none => g.intern (.bin .add (min a b) (max a b))
  | .sub, _, some y => if y = 0 then (g, a) else g.intern (.bin .sub a b)
  | .sub, _, none => if a = b then g.intern (.const 0) else g.intern (.bin .sub a b)
  | .mul, some x, none =>
    if x = 0 then g.intern (.const 0) else if x = 1 then (g, b)
    else if x = 2 then g.intern (.bin .add b b)
    else g.intern (.bin .mul (min a b) (max a b))
  | .mul, none, some y =>
    if y = 0 then g.intern (.const 0) else if y = 1 then (g, a)
    else if y = 2 then g.intern (.bin .add a a)
    else g.intern (.bin .mul (min a b) (max a b))
  | .mul, none, none => g.intern (.bin .mul (min a b) (max a b))

variable [Field F]

/-- The node of a constraint expression; the public value `i` is the scalar `i`. -/
def ofExpr : Expr F → Dag F → Dag F × Nat
  | .cur c, g => g.intern (.cur c)
  | .next c, g => g.intern (.load (.next c))
  | .prepCur c, g => g.intern (.load (.prepCur c))
  | .prepNext c, g => g.intern (.load (.prepNext c))
  | .periodic i, g => g.intern (.load (.periodic i))
  | .pub i, g => g.intern (.scalar i)
  | .const x, g => g.intern (.const x)
  | .isFirstRow, g => g.intern (.load .isFirstRow)
  | .isLastRow, g => g.intern (.load .isLastRow)
  | .isTransition, g => g.intern (.load .isTransition)
  | .add a b, g =>
    let (g, i) := ofExpr a g
    let (g, j) := ofExpr b g
    g.op .add i j
  | .sub a b, g =>
    let (g, i) := ofExpr a g
    let (g, j) := ofExpr b g
    g.op .sub i j
  | .mul a b, g =>
    let (g, i) := ofExpr a g
    let (g, j) := ofExpr b g
    g.op .mul i j

/-- Nodes interned in order. -/
def internAll (g : Dag F) : List (Node F) → Dag F × List Nat
  | [] => (g, [])
  | n :: ns =>
    let (g, i) := g.intern n
    let (g, is) := g.internAll ns
    (g, i :: is)

/-- Coordinatewise operation on lists of nodes. -/
def opN (g : Dag F) (o : Op) : List Nat → List Nat → Dag F × List Nat
  | x :: xs, y :: ys =>
    let (g, c) := g.op o x y
    let (g, cs) := g.opN o xs ys
    (g, c :: cs)
  | _, _ => (g, [])

/-- An expression over nodes. -/
inductive Tree where
  | leaf (i : Nat)
  | op (o : Op) (a b : Tree)

/-- The node of an expression over nodes. -/
def ofTree (g : Dag F) : Tree → Dag F × Nat
  | .leaf i => (g, i)
  | .op o a b =>
    let (g, i) := g.ofTree a
    let (g, j) := g.ofTree b
    g.op o i j

/-- The sum of expressions over nodes from the first, the node `z` for none. -/
def sumTree (z : Nat) : List Tree → Tree
  | [] => .leaf z
  | t :: ts => ts.foldl (fun acc u ↦ .op .add acc u) t

/-- Coefficient `k` of the unreduced product of the coordinate nodes `x` and `y` of degree `d`,
`∑_{i + j = k} xᵢ yⱼ`, the node `z` for none. -/
def convTree (z d : Nat) (x y : List Nat) (k : Nat) : Tree :=
  sumTree z ((List.range d).filterMap fun i ↦ if i ≤ k ∧ k - i < d then
    some (.op .mul (.leaf (x.getD i 0)) (.leaf (y.getD (k - i) 0))) else none)

/-- One higher convolution `k` of the coordinate nodes `x` and `y` of degree `d` added to the
expression `gt.2` with the table's entry `t k`: nothing for `0`, a difference for `-1`, else a
product by the entry as a constant node of `gt.1`. -/
def mulStep (z d : Nat) (x y : List Nat) (t : Nat → F) (gt : Dag F × Tree) (k : Nat) :
    Dag F × Tree :=
  if t k = 0 then gt
  else if t k = -1 then (gt.1, .op .sub gt.2 (convTree z d x y k))
  else
    let (g, c) := gt.1.intern (.const (t k))
    (g, .op .add gt.2 (.op .mul (.leaf c) (convTree z d x y k)))

/-- Coordinate `m` of the product of the coordinate nodes `x` and `y` of degree `d`, with the
entries `t k` of coordinate `m` of the reduction table: the convolution `m` plus the higher
convolutions `k ≥ d` times the nonzero entries (`mulStep`). -/
def mulCoord (g : Dag F) (z d : Nat) (x y : List Nat) (t : Nat → F) (m : Nat) : Dag F × Nat :=
  let (g, tr) := (List.range' d (d - 1)).foldl (mulStep z d x y t) (g, convTree z d x y m)
  g.ofTree tr

/-- Coordinate `m` of the product of the coordinate nodes `x` and `y` over the extension `P`,
appended to the coordinates `gs.2`, with the table `tbl` of `X^k mod f`. -/
def mulNStep (P : CompPoly.Extension.ExtensionParams F) (z : Nat) (x y : List Nat)
    (tbl : Array (CompPoly.Extension.Ext P)) (gs : Dag F × List Nat) (m : Nat) :
    Dag F × List Nat :=
  let (g, c) := mulCoord gs.1 z P.d x y
    (fun k ↦ CompPoly.Extension.Ext.coeffNat (tbl.getD k 0) m) m
  (g, gs.2 ++ [c])

/-- The product of the coordinate nodes `x` and `y` over the extension `P`, reduced by the table
`Ext.red P` of `X^k mod f` (`Ext.coeff_mul_reduce`). -/
def mulN (P : CompPoly.Extension.ExtensionParams F) (g : Dag F) (x y : List Nat) :
    Dag F × List Nat :=
  let (g, z) := g.intern (.const 0)
  (List.range P.d).foldl (mulNStep P z x y (CompPoly.Extension.Ext.red P).toArray) (g, [])

/-- `e` with every public value from `np` on the constant `0`. -/
def pubBelow (np : Nat) : Expr F → Expr F
  | .pub j => if j < np then .pub j else .const 0
  | .add a b => .add (pubBelow np a) (pubBelow np b)
  | .sub a b => .sub (pubBelow np a) (pubBelow np b)
  | .mul a b => .mul (pubBelow np a) (pubBelow np b)
  | e => e

/-- The `d` coordinates of an extension expression over the extension `P` of degree `d` as nodes.
With `np` public values, public value `i` is scalar `i`, the terminal's coordinates are the scalars
from `np` and challenge `i`'s those from `np + d (i + 1)`; permutation column `c`'s coordinates are
the loaded columns from `d c`. -/
def ofExt (P : CompPoly.Extension.ExtensionParams F) (np : Nat) :
    Lookup.ExtExpr F → Dag F → Dag F × List Nat
  | .base e, g =>
    let (g, i) := ofExpr (pubBelow np e) g
    let (g, z) := g.intern (.const 0)
    (g, i :: List.replicate (P.d - 1) z)
  | .perm c, g => g.internAll ((List.range P.d).map fun j ↦ .load (.permCur (P.d * c + j)))
  | .permNext c, g => g.internAll ((List.range P.d).map fun j ↦ .load (.permNext (P.d * c + j)))
  | .challenge i, g => g.internAll ((List.range P.d).map fun j ↦ .scalar (np + P.d * (i + 1) + j))
  | .terminal, g => g.internAll ((List.range P.d).map fun j ↦ .scalar (np + j))
  | .add a b, g =>
    let (g, x) := ofExt P np a g
    let (g, y) := ofExt P np b g
    g.opN .add x y
  | .sub a b, g =>
    let (g, x) := ofExt P np a g
    let (g, y) := ofExt P np b g
    g.opN .sub x y
  | .mul a b, g =>
    let (g, x) := ofExt P np a g
    let (g, y) := ofExt P np b g
    g.mulN P x y

end Dag

/-! ### Register allocation -/

/-- A step of the program's schedule: compute node `i`, or accumulate node `i` with weight `w`. -/
inductive Step where
  | node (i : Nat)
  | acc (i w : Nat)
  deriving Inhabited

/-- The nodes a node reads from registers. -/
def Node.regArgs : Node F → List Nat
  | .bin _ a b => [a, b]
  | _ => []

/-- The nodes a step reads. -/
def Step.reads (nodes : Array (Node F)) : Step → List Nat
  | .node i => ((nodes[i]?).map Node.regArgs).getD []
  | .acc i _ => [i]

/-- The last step reading each node, or the step computing it if none does. -/
def lastUses (nodes : Array (Node F)) (steps : Array Step) : Array Nat :=
  (List.range steps.size).foldl (fun last t ↦
    let last := match steps[t]! with
      | .node i => last.set! i t
      | .acc _ _ => last
    (steps[t]!.reads nodes).foldl (fun l j ↦ l.set! j t) last) (Array.replicate nodes.size 0)

/-- The register allocator's state: the node each register holds, the free registers, each
node's register, and the code so far. -/
structure Alloc (F : Type) where
  owner : Array (Option Nat)
  free : List Nat
  loc : Array Nat
  code : Array (Instr F)

namespace Alloc

/-- Release node `j`'s register if it holds `j`. -/
def release (s : Alloc F) (j : Nat) : Alloc F :=
  let ⟨owner, free, loc, code⟩ := s
  let r := loc[j]!
  if owner[r]? = some (some j) then ⟨owner.set! r none, r :: free, loc, code⟩
  else ⟨owner, free, loc, code⟩

/-- A free register for node `i`, now holding it. -/
def take (s : Alloc F) (i : Nat) : Alloc F × Nat :=
  let ⟨owner, free, loc, code⟩ := s
  match free with
  | r :: rest => (⟨owner.set! r (some i), rest, loc.set! i r, code⟩, r)
  | [] =>
    let r := owner.size
    (⟨owner.push (some i), [], loc.set! i r, code⟩, r)

/-- Append an instruction. -/
def emit (s : Alloc F) (ins : Instr F) : Alloc F :=
  let ⟨owner, free, loc, code⟩ := s
  ⟨owner, free, loc, code.push ins⟩

/-- The operand of node `i`: the trace's column or the constant it is, or its register. -/
def opd (nodes : Array (Node F)) (s : Alloc F) (i : Nat) : Opd F :=
  match nodes[i]? with
  | some (.cur c) => .cur c
  | some (.const x) => .const x
  | _ => .reg s.loc[i]!

/-- Release the registers of the nodes `js` whose last step is `t`. -/
def releaseLast (last : Array Nat) (t : Nat) (s : Alloc F) (js : List Nat) : Alloc F :=
  js.foldl (fun s j ↦ if last[j]! = t then s.release j else s) s

/-- Compute node `i` at step `t` into a register, with the instruction `ins` of the register,
reading the nodes `args`: their registers released first if this is their last step, so that the
result may take one of them. -/
def compute (last : Array Nat) (t : Nat) (s : Alloc F) (i : Nat) (args : List Nat)
    (ins : Nat → Instr F) : Alloc F :=
  let s := releaseLast last t s args
  let (s, r) := s.take i
  let s := s.emit (ins r)
  if last[i]! = t then s.release i else s

/-- Step `t` of the schedule. -/
def step (nodes : Array (Node F)) (last : Array Nat) (s : Alloc F) (t : Nat) :
    Step → Alloc F
  | .node i =>
    match nodes[i]? with
    | some (.load src) => compute last t s i [] fun r ↦ .load r src
    | some (.scalar k) => compute last t s i [] fun r ↦ .scalar r k
    | some (.bin o a b) =>
      let x := opd nodes s a
      let y := opd nodes s b
      compute last t s i [a, b] fun r ↦ .bin o r x y
    | _ => s
  | .acc i w =>
    let x := opd nodes s i
    releaseLast last t (s.emit (.acc x w)) [i]

end Alloc

/-- The program of a schedule of the nodes with the given outputs, registers allocated. -/
def allocate (nodes : Array (Node F)) (steps : Array Step) (outs : Array Nat) : Prog F :=
  let last := lastUses nodes steps
  -- Outputs are read after the last step.
  let last := outs.foldl (fun l j ↦ l.set! j steps.size) last
  let s0 : Alloc F := ⟨#[], [], Array.replicate nodes.size 0, #[]⟩
  let s := (List.range steps.size).foldl (fun s t ↦ s.step nodes last t steps[t]!) s0
  ⟨s.code, s.owner.size, outs.map (Alloc.opd nodes s)⟩

/-! ### Compiling constraints -/

variable [DecidableEq F] [Hashable F] [Field F]

/-- A schedule: its steps, and the number of nodes they compute, the first ones. -/
structure Sched where
  steps : Array Step
  done : Nat

/-- The nodes not yet computed, then the accumulations `accs` of nodes other than zero. -/
def schedule (g : Dag F) (accs : List (Nat × Nat)) (s : Sched) : Sched :=
  let ⟨steps, done⟩ := s
  let n := g.nodes.size
  let steps := (List.range' done (n - done)).foldl (fun s i ↦ s.push (.node i)) steps
  ⟨accs.foldl (fun s (i, w) ↦ if g.constAt i = some 0 then s else s.push (.acc i w)) steps, n⟩

/-- The graph and the schedule of items built one after another: item `k`'s nodes (`f k`) and
then its accumulations. -/
@[inline] def buildAll {α : Type} (f : Nat → α → Dag F → Dag F × List (Nat × Nat))
    (xs : List α) : Dag F × Sched :=
  let (g, sc, _) := xs.foldl (fun (g, sc, k) x ↦
    let (g, accs) := f k x g
    (g, schedule g accs sc, k + 1)) ((Dag.empty : Dag F), (⟨#[], 0⟩ : Sched), 0)
  (g, sc)

/-- The program accumulating the constraints `cs`, constraint `k` with weight `k`: on a row its
accumulators gain `∑ₖ cₖ · weight k`. -/
def compile (cs : List (Expr F)) : Prog F :=
  let (g, sc) := buildAll (fun k c g ↦
    let (g, i) := Dag.ofExpr c g
    (g, [(i, k)])) cs
  allocate g.nodes sc.steps #[]

/-- The program accumulating the extension constraints `cs` over the extension `P` of degree `d`
with `np` public values (`Dag.ofExt`), coordinate `j` of constraint `k` with weight `d k + j`. -/
def compileExt (P : CompPoly.Extension.ExtensionParams F) (np : Nat)
    (cs : List (Lookup.ExtExpr F)) : Prog F :=
  let (g, sc) := buildAll (fun k c g ↦
    let (g, xs) := Dag.ofExt P np c g
    (g, xs.zipIdx.map fun (x, j) ↦ (x, P.d * k + j))) cs
  allocate g.nodes sc.steps #[]

/-- The program whose outputs are the expressions `es`. -/
def compileOuts (es : List (Expr F)) : Prog F :=
  let (g, outs) := es.foldl (fun (g, outs) e ↦
    let (g, i) := Dag.ofExpr e g
    (g, outs.push i)) ((Dag.empty : Dag F), (#[] : Array Nat))
  allocate g.nodes (schedule g [] ⟨#[], 0⟩).steps outs

end CompStark.Stark.Prog
