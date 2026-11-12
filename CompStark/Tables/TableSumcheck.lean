/-
Copyright (c) 2026 zkSecurity.
Adapted from Verified-zkEVM/leanerVM (Apache-2.0), revision a9d42bfdae8081a4e16aef1cd8526cdaa2a8f4d6:
LeanerVM.Protocol.TableSumcheck.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.TablePoly
public import CompStark.Tables.BusProtocol

/-! The table sumcheck over the tables the bus does not open directly.

After the bus, the verifier draws `ξ` and batches every active table's constraints, with powers
`ξ ^ 0, ξ ^ 1, …` in table order, and the three bus debts, with the next three powers, into one
sumcheck over the tallest active table's variables, highest first. Each table weighs its rows by
the equality weight at the bus point on its own variables and by the product of the variables
above its height. The rounds send compressed messages of degree one more than the largest
constraint or tuple degree; at the end the prover sends every active table's transmitted
columns at the final point. -/

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

@[expose] public section

namespace CompStark.Stark.Expr

/-- The expression reads committed column `c` of the current row. -/
def readsCol {F : Type} (c : ℕ) : Expr F → Bool
  | cur c' => c' == c
  | add a b | sub a b | mul a b => readsCol c a || readsCol c b
  | _ => false

/-- A column an expression reads is below its column bound. -/
theorem readsCol_lt {F : Type} {w wNext pw pwNext c : ℕ} (e : Expr F)
    (h : e.colsBelow w wNext pw pwNext = true) (hr : e.readsCol c = true) : c < w := by
  induction e with
  | cur c' =>
    simp only [readsCol, beq_iff_eq] at hr
    simp only [colsBelow, decide_eq_true_eq] at h
    exact hr ▸ h
  | add a b ha hb | sub a b ha hb | mul a b ha hb =>
    simp only [colsBelow, Bool.and_eq_true] at h
    simp only [readsCol, Bool.or_eq_true] at hr
    exact hr.elim (ha h.1) (hb h.2)
  | _ => simp only [readsCol, Bool.false_eq_true] at hr

open CompStark.BinaryFields in
/-- An expression's value depends only on the columns it reads and the preprocessed values. -/
theorem eval_envE_congr (e : Expr K) (v v' p p' : ℕ → E) (hv : ∀ c, e.readsCol c = true → v c = v' c)
    (hp : ∀ c, p c = p' c) :
    e.eval (CompStark.Tables.System.envE v p) = e.eval (CompStark.Tables.System.envE v' p') := by
  induction e with
  | cur c => exact hv c (by simp only [readsCol, beq_self_eq_true])
  | prepCur c => exact hp c
  | add a b ha hb | sub a b ha hb | mul a b ha hb =>
    simp only [eval]
    rw [ha fun c h ↦ hv c (by simp only [readsCol, h, Bool.true_or]),
      hb fun c h ↦ hv c (by simp only [readsCol, h, Bool.or_true])]
  | _ => rfl

open CompStark.BinaryFields in
/-- An expression's polynomial depends only on the columns it reads and the preprocessed
variables. -/
theorem toPoly_eval_congr (width : ℕ) (e : Expr K) (v v' : ℕ → E)
    (hv : ∀ c, e.readsCol c = true → v c = v' c) (hp : ∀ c, v (width + c) = v' (width + c)) :
    MvPolynomial.eval v (toPoly width e) = MvPolynomial.eval v' (toPoly width e) := by
  induction e with
  | cur c => simpa only [toPoly, MvPolynomial.eval_X] using hv c (by simp only [readsCol, beq_self_eq_true])
  | prepCur c => simpa only [toPoly, MvPolynomial.eval_X] using hp c
  | const c => simp only [toPoly, MvPolynomial.eval_C]
  | add a b ha hb | sub a b ha hb | mul a b ha hb =>
    simp only [toPoly, map_add, map_sub, map_mul]
    rw [ha fun c h ↦ hv c (by simp only [readsCol, h, Bool.true_or]),
      hb fun c h ↦ hv c (by simp only [readsCol, h, Bool.or_true])]
  | _ => simp only [toPoly, map_zero]

end CompStark.Stark.Expr

namespace CompStark.Tables.TableSumcheck

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System
open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp MvPolynomial
open Sumcheck.Interaction.MultivariateRound

variable (S : System K) (L : Layout S.tables.length) (k : ℕ)

/-- The tables the table sumcheck covers: those the bus does not open directly. -/
abbrev Active := {t : Fin S.tables.length // S.Direct L t = false}

/-- The sumcheck's number of variables: the tallest active table's. -/
def maxHeight : ℕ := Finset.univ.sup fun t : Active S L ↦ L.logHeight t.1

/-- Every active table fits the sumcheck's variables. -/
theorem height_le_maxHeight (t : Active S L) : L.logHeight t.1 ≤ maxHeight S L :=
  Finset.le_sup (f := fun t : Active S L ↦ L.logHeight t.1) (Finset.mem_univ t)

/-- The number of constraints of table `t`. -/
abbrev constraintLength (t : Fin S.tables.length) : ℕ := (S.table t).air.constraints.length

/-- The number of constraints of the tables before `t`; directly opened tables have none, so this
counts the active tables' constraints in table order. -/
def constraintOffset (t : Fin S.tables.length) : ℕ :=
  ∑ j : Fin t.val, constraintLength S (Fin.castLE t.isLt.le j)

/-- The number of constraints of all tables. -/
def constraintCount : ℕ := ∑ t : Fin S.tables.length, constraintLength S t

/-- The largest individual degree of a constraint or tuple entry of an active table, at least
one. -/
def degree : ℕ :=
  max 1 (Finset.univ.sup fun t : Active S L ↦ max (S.tupleDegree t.1)
    (((S.table t.1).air.constraints.map Expr.degree).foldl max 0))

/-- The columns a table's constraints, tuples or nonzero checks read: those the table phase
transmits. -/
def transmitted (t : Fin S.tables.length) : List ℕ :=
  (List.range (S.table t).air.width).filter fun c ↦
    (S.table t).air.constraints.any (Expr.readsCol c) ||
      ((S.table t).interactions.any fun I ↦ I.tuple.any (Expr.readsCol c)) ||
      (S.table t).nonzero.contains c

/-- Row `i`'s value of variable `c` of table `t`: committed below the width, preprocessed above. -/
def cell (w : Witness K S.tables.length) (t : Fin S.tables.length) (i c : ℕ) : K :=
  if c < (S.table t).air.width then ((w t).getD i #[]).getD c 0
  else (S.table t).air.preprocessed.getD
    (i * (S.table t).air.preprocessedWidth + (c - (S.table t).air.width)) 0

/-- The extension of variable `c` of table `t` at a point. -/
def cellColumn (w : Witness K S.tables.length) (t : Fin S.tables.length) (c : ℕ) (z : List E) : E :=
  mle (L.logHeight t) (fun i ↦ ofK (cell S w t i c)) z

/-- Each active table's transmitted column values. -/
abbrev Values := (t : Active S L) → Fin (transmitted S t.1).length → E

/-- Variable `c` of an active table at the final point: a transmitted value below the width, the
preprocessed column's extension above. -/
def valuesAt (vals : Values S L) (t : Active S L) (z : List E) (c : ℕ) : E :=
  if c < (S.table t.1).air.width then ((transmitted S t.1).finIdxOf? c).elim 0 (vals t)
  else S.prepColumn L t.1 (c - (S.table t.1).air.width) z

/-- One active table's batched row formula: its constraints and its three bus forms. -/
noncomputable def rowValue (o : Bus.Output S L k) (ξ : E) (t : Active S L) (v : ℕ → E) : E :=
  (∑ i : Fin (constraintLength S t.1), ξ ^ (constraintOffset S t.1 + i.val) *
    MvPolynomial.eval v (Expr.toPoly (S.table t.1).air.width (S.table t.1).air.constraints[i])) +
  ∑ s : Fin 3, ξ ^ (constraintCount S + s.val) *
    S.tableForm L k o.alpha o.beta (Bus.μ S L) s t.1 o.point v
      (fun c ↦ v ((S.table t.1).air.width + c))

/-- An active table's weight: the equality weight at the bus point on its variables, times the
variables above its height. -/
def tableWeight (o : Bus.Output S L k) (t : Active S L) (z : List E) : E :=
  (∏ a : Fin (L.logHeight t.1), eqFactor (o.point.getD a.val 0) (z.getD a.val 0)) *
    ∏ a : Fin (maxHeight S L - L.logHeight t.1), z.getD (L.logHeight t.1 + a.val) 0

/-- The verifier's terminal formula from the transmitted values. -/
noncomputable def formula (o : Bus.Output S L k) (ξ : E) (z : List E) (vals : Values S L) : E :=
  ∑ t : Active S L, tableWeight S L k o t z *
    rowValue S L k o ξ t (valuesAt S L vals t (z.take (L.logHeight t.1)))

/-- The summand at a point, from the witness. -/
noncomputable def summandValue (o : Bus.Output S L k) (ξ : E) (w : Witness K S.tables.length)
    (z : List E) : E :=
  ∑ t : Active S L, tableWeight S L k o t z *
    rowValue S L k o ξ t (fun c ↦ cellColumn S L w t.1 c (z.take (L.logHeight t.1)))

/-- The verifier's target: the three bus debts batched by `ξ`. -/
def target (o : Bus.Output S L k) (ξ : E) : E :=
  ∑ s : Fin 3, ξ ^ (constraintCount S + s.val) * o.remainders s

/-- Reversing the challenge vector recovers a physical coordinate. -/
theorem reversed_getD {m : ℕ} (r : Fin m → E) (j : ℕ) (hj : j < m) :
    (List.ofFn r).reverse.getD j 0 = r ⟨m - 1 - j, by omega⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_reverse, List.length_ofFn] using hj)]
  simp only [List.getElem_reverse, List.length_ofFn, List.getElem_ofFn]

/-- A low-coordinate claim reads the same reversed challenge coordinate. -/
theorem reversed_take_getD {m h : ℕ} (r : Fin m → E) (hh : h ≤ m) (j : ℕ) (hj : j < h) :
    ((List.ofFn r).reverse.take h).getD j 0 = r ⟨m - 1 - j, by omega⟩ := by
  simp only [List.getD, List.getElem?_take_of_lt hj]
  exact reversed_getD r j (hj.trans_le hh)

/-- Products with distinct assigned variables are multilinear. -/
theorem prod_degree_one {ι σ : Type} [Fintype ι] [DecidableEq σ]
    (f : ι → σ) (hinj : Function.Injective f)
    (p : ι → MvPolynomial σ E) (j : σ)
    (hp : ∀ a, (p a).degreeOf j ≤ if j = f a then 1 else 0) :
    (∏ a, p a).degreeOf j ≤ 1 := by
  classical
  refine (degreeOf_prod_le j _ _).trans ?_
  apply le_trans (Finset.sum_le_sum fun a _ ↦ hp a)
  rw [Finset.sum_boole]
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact hinj (((Finset.mem_filter.mp ha).2).symm.trans (Finset.mem_filter.mp hb).2)

/-- Boolean basis factors use only their assigned variable. -/
theorem basis_degree {σ : Type} [DecidableEq σ] (j i : σ) (b : Bool) :
    (if b then (X i : MvPolynomial σ E) else 1 - X i).degreeOf j ≤ if j = i then 1 else 0 := by
  cases b
  · exact (degreeOf_sub_le j _ _).trans (by simp only [degreeOf_one, degreeOf_X]; split_ifs <;> omega)
  · simp only [↓reduceIte, degreeOf_X, le_refl]

/-- A table variable's extension in reversed sumcheck variables. -/
noncomputable def columnPolynomial (w : Witness K S.tables.length) (t : Active S L) (c : ℕ) :
    MvPolynomial (Fin (maxHeight S L)) E :=
  ∑ i : Fin (2 ^ L.logHeight t.1),
    MvPolynomial.C (ofK (cell S w t.1 i.val c)) *
      ∏ a : Fin (L.logHeight t.1),
        let x : MvPolynomial (Fin (maxHeight S L)) E :=
          .X ⟨maxHeight S L - 1 - a.val, by have := height_le_maxHeight S L t; omega⟩
        if i.val.testBit a.val then x else 1 - x

/-- Every table variable has individual degree at most one. -/
theorem columnPolynomial_degree (w : Witness K S.tables.length) (t : Active S L) (c : ℕ)
    (j : Fin (maxHeight S L)) : (columnPolynomial S L w t c).degreeOf j ≤ 1 := by
  classical
  unfold columnPolynomial
  refine (MvPolynomial.degreeOf_sum_le j _ _).trans (Finset.sup_le fun i _ ↦ ?_)
  refine (MvPolynomial.degreeOf_mul_le j _ _).trans ?_
  rw [MvPolynomial.degreeOf_C, zero_add]
  apply prod_degree_one
    (fun a : Fin (L.logHeight t.1) ↦ (⟨maxHeight S L - 1 - a.val, by
      have := height_le_maxHeight S L t; omega⟩ : Fin (maxHeight S L)))
  · intro a b hab
    apply Fin.ext
    have hv := congrArg Fin.val hab
    dsimp only at hv
    have := a.isLt
    have := b.isLt
    have := height_le_maxHeight S L t
    omega
  · intro a
    exact basis_degree j _ _

/-- The reversed column polynomial evaluates to the variable's extension. -/
theorem columnPolynomial_eval (w : Witness K S.tables.length) (t : Active S L) (c : ℕ)
    (r : Fin (maxHeight S L) → E) :
    MvPolynomial.eval r (columnPolynomial S L w t c) =
      cellColumn S L w t.1 c ((List.ofFn r).reverse.take (L.logHeight t.1)) := by
  simp only [columnPolynomial, cellColumn, mle, map_sum, map_mul, MvPolynomial.eval_C, map_prod]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun x : E ↦ ofK (cell S w t.1 i.val c) * x)
  apply Finset.prod_congr rfl
  intro a _
  rw [reversed_take_getD r (height_le_maxHeight S L t) a.val a.isLt]
  by_cases hi : i.val.testBit a.val = true <;>
    simp only [hi, Bool.false_eq_true, ↓reduceIte, MvPolynomial.eval_X, map_sub, map_one, eqFactor, bit,
      sub_zero, sub_self, mul_one, mul_zero, zero_add, add_zero]

/-- The table weight as a polynomial in reversed sumcheck variables. -/
noncomputable def weightPolynomial (o : Bus.Output S L k) (t : Active S L) :
    MvPolynomial (Fin (maxHeight S L)) E :=
  ((∏ a : Fin (L.logHeight t.1),
      let x : MvPolynomial (Fin (maxHeight S L)) E :=
        .X ⟨maxHeight S L - 1 - a.val, by have := height_le_maxHeight S L t; omega⟩
      (1 - MvPolynomial.C (o.point.getD a.val 0)) * (1 - x) + MvPolynomial.C (o.point.getD a.val 0) * x) *
    ∏ a : Fin (maxHeight S L - L.logHeight t.1),
      MvPolynomial.X ⟨maxHeight S L - 1 - (L.logHeight t.1 + a.val), by have := a.isLt; omega⟩)

/-- The table weight uses each variable at most once. -/
theorem weightPolynomial_degree (o : Bus.Output S L k) (t : Active S L) (j : Fin (maxHeight S L)) :
    (weightPolynomial S L k o t).degreeOf j ≤ 1 := by
  classical
  have hle := height_le_maxHeight S L t
  let f : Fin (L.logHeight t.1) ⊕ Fin (maxHeight S L - L.logHeight t.1) → Fin (maxHeight S L) :=
    Sum.elim (fun a ↦ ⟨maxHeight S L - 1 - a.val, by omega⟩)
      (fun a ↦ ⟨maxHeight S L - 1 - (L.logHeight t.1 + a.val), by have := a.isLt; omega⟩)
  have hf : Function.Injective f := by
    intro a b hab
    have hv := congrArg Fin.val hab
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        apply congrArg Sum.inl; apply Fin.ext
        have := a.isLt; have := b.isLt
        dsimp only [f, Sum.elim_inl] at hv; omega
      | inr b =>
        have := a.isLt; have := b.isLt
        dsimp only [f, Sum.elim_inl, Sum.elim_inr] at hv; omega
    | inr a =>
      cases b with
      | inl b =>
        have := a.isLt; have := b.isLt
        dsimp only [f, Sum.elim_inl, Sum.elim_inr] at hv; omega
      | inr b =>
        apply congrArg Sum.inr; apply Fin.ext
        have := a.isLt; have := b.isLt
        dsimp only [f, Sum.elim_inr] at hv; omega
  let p : Fin (L.logHeight t.1) ⊕ Fin (maxHeight S L - L.logHeight t.1) →
      MvPolynomial (Fin (maxHeight S L)) E :=
    Sum.elim (fun a ↦ singleEqPolynomial (o.point.getD a.val 0) (X (f (.inl a))))
      (fun a ↦ X (f (.inr a)))
  have h := prod_degree_one f hf p j (by
    intro a
    cases a with
    | inl a => exact singleEqPolynomial_degreeOf _ j _
    | inr a => simp only [p, Sum.elim_inr, degreeOf_X, le_refl])
  simpa only [p, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, f,
    weightPolynomial, singleEqPolynomial] using h

/-- A table's selector-weighted bus form as a polynomial in its row values. -/
noncomputable def formSum (μ : ℕ) (α : Fin k → E) (β : E) (ζ : List E) (t : Fin S.tables.length) :
    List (Block S.tables.length) → ℕ → MvPolynomial ℕ E
  | [], _ => 0
  | b :: rest, offset =>
      MvPolynomial.C (selectorWeight μ (Block.height S L b) offset ζ) *
          (if Block.table S b = t then S.formPoly k α β b else 0) +
        formSum μ α β ζ t rest (offset + 2 ^ Block.height S L b)

/-- The selector-weighted bus form of table `t` on a side, as a polynomial. -/
noncomputable def tableFormPolynomial (o : Bus.Output S L k) (side : Fin 3) (t : Fin S.tables.length) :
    MvPolynomial ℕ E :=
  formSum S L k (Bus.μ S L) o.alpha o.beta o.point t (S.sortedBlocks L side) 0

/-- The bus form polynomial evaluates to the bus form at a row's variables. -/
theorem tableForm_eq_eval (hT : ∀ t, (S.table t).WellFormed) (o : Bus.Output S L k) (side : Fin 3)
    (t : Fin S.tables.length) (v : ℕ → E) :
    S.tableForm L k o.alpha o.beta (Bus.μ S L) side t o.point v
        (fun c ↦ v ((S.table t).air.width + c)) =
      MvPolynomial.eval v (tableFormPolynomial S L k o side t) := by
  have hv : S.cellValue t v (fun c ↦ v ((S.table t).air.width + c)) = v := by
    funext c
    unfold cellValue
    split_ifs with h
    · rfl
    · show v (_ + _) = v c
      rw [Nat.add_sub_cancel' (by omega)]
  have go : ∀ (bs : List (Block S.tables.length)) (offset : ℕ), (∀ b ∈ bs,
      (∀ t c, b = .nonzero t c → c ∈ (S.table t).nonzero) ∧
        ∀ t I, b = .interaction t I → I ∈ (S.table t).interactions) →
      S.sumBlocks L (Bus.μ S L) o.point (fun b ↦ if Block.table S b = t then
          S.formE k o.alpha o.beta b v (fun c ↦ v ((S.table t).air.width + c)) else 0) bs offset =
        MvPolynomial.eval v (formSum S L k (Bus.μ S L) o.alpha o.beta o.point t bs offset) := by
    intro bs
    induction bs with
    | nil => intro _ _; simp only [sumBlocks, formSum, map_zero]
    | cons b bs ih =>
      intro offset hmem
      simp only [sumBlocks, formSum, map_add, map_mul, MvPolynomial.eval_C]
      rw [ih _ fun x hx ↦ hmem x (List.mem_cons_of_mem _ hx)]
      by_cases hb : Block.table S b = t
      · have h := S.formPoly_eval k o.alpha o.beta hT b (hmem b (List.mem_cons_self ..)).1
          (hmem b (List.mem_cons_self ..)).2 v (fun c ↦ v ((S.table t).air.width + c))
        rw [hb, hv] at h
        simp only [hb, ↓reduceIte, h]
      · simp only [hb, ↓reduceIte, map_zero]
  exact go _ 0 (S.mem_sortedBlocks L side)

/-- Substituting multilinear values into a table's bus form keeps every degree at most the
table's tuple degree, and at least one. -/
theorem tableForm_substitute_degree {σ : Type} (o : Bus.Output S L k) (side : Fin 3)
    (t : Fin S.tables.length) (P : ℕ → MvPolynomial σ E) (j : σ) (hP : ∀ c, (P c).degreeOf j ≤ 1) :
    (MvPolynomial.bind₁ P (tableFormPolynomial S L k o side t)).degreeOf j ≤
      max 1 (S.tupleDegree t) := by
  have go : ∀ (bs : List (Block S.tables.length)) (offset : ℕ), (∀ b ∈ bs,
      ∀ t I, b = .interaction t I → I ∈ (S.table t).interactions) →
      (MvPolynomial.bind₁ P (formSum S L k (Bus.μ S L) o.alpha o.beta o.point t bs offset)).degreeOf j ≤
        max 1 (S.tupleDegree t) := by
    intro bs
    induction bs with
    | nil => intro _ _; simp only [formSum, map_zero, degreeOf_zero, Nat.zero_le]
    | cons b bs ih =>
      intro offset hmem
      simp only [formSum, map_add, map_mul, MvPolynomial.bind₁_C_right]
      refine (degreeOf_add_le j _ _).trans (max_le ?_ (ih _ fun x hx ↦ hmem x (List.mem_cons_of_mem _ hx)))
      refine (degreeOf_mul_le j _ _).trans ?_
      rw [degreeOf_C, zero_add]
      split_ifs with hb
      · have h := S.formPoly_bind_degreeOf k o.alpha o.beta b (hmem b (List.mem_cons_self ..)) P j hP
        rwa [hb] at h
      · simp only [map_zero, degreeOf_zero, Nat.zero_le]
  exact go _ 0 fun b hb ↦ (S.mem_sortedBlocks L side b hb).2

/-- An active table's constraint degrees are at most the sumcheck degree. -/
theorem constraint_degree_le (t : Active S L) (e : Expr K) (he : e ∈ (S.table t.1).air.constraints) :
    e.degree ≤ degree S L := by
  have bound (xs : List ℕ) (a x : ℕ) (hx : x ≤ a ∨ x ∈ xs) : x ≤ xs.foldl max a := by
    induction xs generalizing a with
    | nil => exact hx.resolve_right (List.not_mem_nil)
    | cons y xs ih =>
      apply ih
      rcases hx with h | h
      · exact Or.inl (h.trans (le_max_left _ _))
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inl (le_max_right _ _)
        · exact Or.inr h
  refine (bound _ 0 _ (Or.inr (List.mem_map.mpr ⟨e, he, rfl⟩))).trans ?_
  refine (le_max_right (S.tupleDegree t.1) _).trans ?_
  refine (Finset.le_sup (f := fun t : Active S L ↦ max (S.tupleDegree t.1)
    (((S.table t.1).air.constraints.map Expr.degree).foldl max 0)) (Finset.mem_univ t)).trans ?_
  exact le_max_right _ _

/-- An active table's tuple degree, at least one, is at most the sumcheck degree. -/
theorem tupleDegree_le (t : Active S L) : max 1 (S.tupleDegree t.1) ≤ degree S L :=
  max_le_max le_rfl ((le_max_left _ _).trans (Finset.le_sup (f := fun t : Active S L ↦
    max (S.tupleDegree t.1) (((S.table t.1).air.constraints.map Expr.degree).foldl max 0))
    (Finset.mem_univ t)))

/-- The summand polynomial: every active table's weight times its batched row formula, in reversed
variables. -/
noncomputable def polynomial (o : Bus.Output S L k) (ξ : E) (w : Witness K S.tables.length) :
    MvPolynomial (Fin (maxHeight S L)) E :=
  ∑ t : Active S L, weightPolynomial S L k o t *
    ((∑ i : Fin (constraintLength S t.1),
      MvPolynomial.C (ξ ^ (constraintOffset S t.1 + i.val)) *
        MvPolynomial.bind₁ (columnPolynomial S L w t)
          (Expr.toPoly (S.table t.1).air.width (S.table t.1).air.constraints[i])) +
      ∑ side : Fin 3, MvPolynomial.C (ξ ^ (constraintCount S + side.val)) *
        MvPolynomial.bind₁ (columnPolynomial S L w t) (tableFormPolynomial S L k o side t.1))

/-- Every variable's degree is at most one more than the sumcheck degree. -/
theorem polynomial_degree (o : Bus.Output S L k) (ξ : E) (w : Witness K S.tables.length) :
    polynomial S L k o ξ w ∈ MvPolynomial.restrictDegree (Fin (maxHeight S L)) E (degree S L + 1) := by
  classical
  rw [mem_restrictDegree_iff_degreeOf_le]
  intro j
  unfold polynomial
  refine (degreeOf_sum_le j _ _).trans (Finset.sup_le fun t _ ↦ ?_)
  refine (degreeOf_mul_le j _ _).trans ?_
  have hair : (∑ i : Fin (constraintLength S t.1),
      C (ξ ^ (constraintOffset S t.1 + i.val)) *
        bind₁ (columnPolynomial S L w t)
          (Expr.toPoly (S.table t.1).air.width (S.table t.1).air.constraints[i])).degreeOf j ≤
        degree S L := by
    refine (degreeOf_sum_le j _ _).trans (Finset.sup_le fun i _ ↦ ?_)
    refine (degreeOf_mul_le j _ _).trans ?_
    rw [degreeOf_C, zero_add]
    exact (Expr.toPoly_bind_degreeOf _ _ _ j (fun c ↦ columnPolynomial_degree S L w t c j)).trans
      (constraint_degree_le S L t _ (List.getElem_mem _))
  have hbus : (∑ side : Fin 3, C (ξ ^ (constraintCount S + side.val)) *
      bind₁ (columnPolynomial S L w t) (tableFormPolynomial S L k o side t.1)).degreeOf j ≤
        degree S L := by
    refine (degreeOf_sum_le j _ _).trans (Finset.sup_le fun side _ ↦ ?_)
    refine (degreeOf_mul_le j _ _).trans ?_
    rw [degreeOf_C, zero_add]
    exact (tableForm_substitute_degree S L k o side t.1 _ j
      (fun c ↦ columnPolynomial_degree S L w t c j)).trans (tupleDegree_le S L t)
  exact (Nat.add_le_add (weightPolynomial_degree S L k o t j)
    ((degreeOf_add_le j _ _).trans (max_le hair hbus))).trans (by omega)

/-- The summand as a bounded-degree sumcheck statement. -/
noncomputable def summand (o : Bus.Output S L k) (ξ : E) (w : Witness K S.tables.length) :
    Sumcheck.Spec.OracleStatement E (maxHeight S L) (degree S L + 1) () :=
  ⟨polynomial S L k o ξ w, polynomial_degree S L k o ξ w⟩

/-- In reversed challenges, the summand evaluates to the witness's summand value. -/
theorem summand_eval (hT : ∀ t, (S.table t).WellFormed) (o : Bus.Output S L k) (ξ : E)
    (w : Witness K S.tables.length) (r : Fin (maxHeight S L) → E) :
    (summand S L k o ξ w).val.eval r = summandValue S L k o ξ w (List.ofFn r).reverse := by
  classical
  change MvPolynomial.eval r (polynomial S L k o ξ w) = _
  have hb (t : Active S L) (P : MvPolynomial ℕ E) :
      MvPolynomial.eval r (MvPolynomial.bind₁ (columnPolynomial S L w t) P) =
        MvPolynomial.eval (fun c ↦ cellColumn S L w t.1 c
          ((List.ofFn r).reverse.take (L.logHeight t.1))) P :=
    (MvPolynomial.eval₂Hom_bind₁ (RingHom.id E) r _ P).trans
      (congrArg (fun f ↦ MvPolynomial.eval f P) (funext fun c ↦ columnPolynomial_eval S L w t c r))
  simp only [polynomial, summandValue, rowValue, map_sum, map_mul, map_add,
    MvPolynomial.eval_C, hb, tableForm_eq_eval S L k hT]
  apply Finset.sum_congr rfl
  intro t _
  apply congrArg (· * _)
  unfold tableWeight weightPolynomial
  rw [map_mul, map_prod, map_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro a _
    simp only [map_add, map_mul, map_sub, map_one, MvPolynomial.eval_C,
      MvPolynomial.eval_X, eqFactor, reversed_getD r a.val (a.isLt.trans_le (height_le_maxHeight S L t))]
  · apply Finset.prod_congr rfl
    intro a _
    rw [MvPolynomial.eval_X, reversed_getD r (L.logHeight t.1 + a.val) (by have := a.isLt; omega)]

/-- The transmitted values are the transmitted columns' extensions at the final point. -/
def ValuesHold (w : Witness K S.tables.length) (z : List E) (vals : Values S L) : Prop :=
  ∀ t (i : Fin (transmitted S t.1).length),
    vals t i = S.column L w t.1 (transmitted S t.1)[i] (z.take (L.logHeight t.1))

/-- A transmitted column is a committed column. -/
theorem lt_of_mem_transmitted (t : Fin S.tables.length) (c : ℕ) (hc : c ∈ transmitted S t) :
    c < (S.table t).air.width :=
  List.mem_range.mp (List.mem_filter.mp hc).1

/-- True transmitted values give every variable a formula reads. -/
theorem valuesAt_eq_cellColumn (w : Witness K S.tables.length) (z : List E) (vals : Values S L)
    (hvals : ValuesHold S L w z vals) (t : Active S L) (c : ℕ)
    (hc : c < (S.table t.1).air.width → c ∈ transmitted S t.1) :
    valuesAt S L vals t (z.take (L.logHeight t.1)) c =
      cellColumn S L w t.1 c (z.take (L.logHeight t.1)) := by
  unfold valuesAt
  split_ifs with hw
  · have hm := hc hw
    cases hi : (transmitted S t.1).finIdxOf? c with
    | none => exact absurd hm (List.finIdxOf?_eq_none_iff.mp hi)
    | some i =>
      have hget := (List.finIdxOf?_eq_some_iff.mp hi).1
      simp only [Option.elim_some]
      rw [hvals t i, hget]
      simp only [column, cellColumn, cell, hw, ↓reduceIte]
  · simp only [prepColumn, cellColumn, cell, hw, ↓reduceIte]

/-- A transmitted column: one a table's constraints, tuples or nonzero checks read. -/
theorem mem_transmitted (t : Fin S.tables.length) (c : ℕ) (hc : c < (S.table t).air.width) :
    c ∈ transmitted S t ↔
      ((S.table t).air.constraints.any (Expr.readsCol c) ||
        ((S.table t).interactions.any fun I ↦ I.tuple.any (Expr.readsCol c)) ||
        (S.table t).nonzero.contains c) = true := by
  simp only [transmitted, List.mem_filter, List.mem_range, hc, true_and]

/-- A table's bus form depends only on its transmitted columns and its preprocessed values. -/
theorem tableForm_congr (hT : ∀ t, (S.table t).WellFormed) (α : Fin k → E) (β : E) (μ : ℕ)
    (side : Fin 3) (t : Fin S.tables.length) (ζ : List E) (v v' p p' : ℕ → E)
    (agree : ∀ c ∈ transmitted S t, v c = v' c) (hp : ∀ c, p c = p' c) :
    S.tableForm L k α β μ side t ζ v p = S.tableForm L k α β μ side t ζ v' p' := by
  unfold tableForm
  apply S.sumBlocks_congr L _ _ _ _ _ 0
  intro b hb
  obtain ⟨hnz, hint⟩ := S.mem_sortedBlocks L side b hb
  split_ifs with htb
  · cases b with
    | nonzero t' c =>
      have hc := hnz t' c rfl
      simp only [Block.table] at htb
      subst htb
      have hlt := (hT t').2.2.2.2.2.1 c hc
      simp only [formE]
      exact agree c ((mem_transmitted S t' c hlt).mpr (by
        simp only [Bool.or_eq_true, List.contains_iff_mem]
        exact Or.inr hc))
    | interaction t' I =>
      have hI := hint t' I rfl
      simp only [Block.table] at htb
      subst htb
      simp only [formE]
      refine congrArg (fun l ↦ β - fingerprintE k α (encodeE k (S.busIndex I.bus) l))
        (List.map_congr_left fun e he ↦ ?_)
      have hwf := (hT t').2.2.2.2.1 I hI e he
      apply Expr.eval_envE_congr e _ _ _ _ _ hp
      intro c hr
      have hlt := Expr.readsCol_lt e hwf.2 hr
      exact agree c ((mem_transmitted S t' c hlt).mpr (by
        simp only [Bool.or_eq_true, List.any_eq_true]
        exact Or.inl (Or.inr ⟨I, hI, e, he, hr⟩)))
  · rfl

/-- An active table's batched row formula depends only on the variables it reads. -/
theorem rowValue_congr (hT : ∀ t, (S.table t).WellFormed) (o : Bus.Output S L k) (ξ : E)
    (t : Active S L) (v v' : ℕ → E)
    (agree : ∀ c, (c < (S.table t.1).air.width → c ∈ transmitted S t.1) → v c = v' c) :
    rowValue S L k o ξ t v = rowValue S L k o ξ t v' := by
  have hpre : ∀ c, v ((S.table t.1).air.width + c) = v' ((S.table t.1).air.width + c) :=
    fun c ↦ agree _ fun h ↦ absurd h (by omega)
  unfold rowValue
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i _
    apply congrArg (ξ ^ (constraintOffset S t.1 + i.val) * ·)
    have he := List.getElem_mem (l := (S.table t.1).air.constraints) i.isLt
    apply Expr.toPoly_eval_congr _ _ v v' _ hpre
    intro c hr
    have hlt := Expr.readsCol_lt _ ((hT t.1).2.2.2.1 _ he).2 hr
    exact agree c fun _ ↦ (mem_transmitted S t.1 c hlt).mpr (by
      simp only [Bool.or_eq_true, List.any_eq_true]
      exact Or.inl (Or.inl ⟨_, he, hr⟩))
  · apply Finset.sum_congr rfl
    intro s _
    rw [tableForm_congr S L k hT _ _ _ s t.1 _ v v' _ _ (fun c hc ↦ agree c fun _ ↦ hc) hpre]

/-- With true transmitted values, the verifier's formula is the witness's summand value. -/
theorem formula_eq_summandValue (hT : ∀ t, (S.table t).WellFormed) (w : Witness K S.tables.length)
    (o : Bus.Output S L k) (ξ : E) (z : List E) (vals : Values S L) (hvals : ValuesHold S L w z vals) :
    formula S L k o ξ z vals = summandValue S L k o ξ w z := by
  unfold formula summandValue
  apply Finset.sum_congr rfl
  intro t _
  rw [rowValue_congr S L k hT o ξ t _ _ (valuesAt_eq_cellColumn S L w z vals hvals t)]

/-- A round message: the constant coefficient and those of degree two to `degree + 1`. -/
abbrev Message := Sumcheck.CompressedMessage E (degree S L)

/-- The compressed message operations; the running sum fixes the linear coefficient. -/
def messageOps : Sumcheck.MessageOps E (Message S L) := Sumcheck.compressedOps (degree S L)

/-- The table sumcheck's Boolean domain. -/
def booleanDomain : Fin 2 ↪ E := ⟨![0, 1], by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact (zero_ne_one (show (0 : E) = 1 from h)).elim
  · exact (one_ne_zero (show (1 : E) = 0 from h)).elim
  · rfl⟩

/-- The compressed message model on that Boolean domain. -/
noncomputable def messageModel :
    Sumcheck.MessageModel (Finset.univ.map booleanDomain) (messageOps S L) (degree S L + 1) where
  interpret := Sumcheck.compressed
  evaluate_eq := Sumcheck.compressed_evaluate_eq
  accept_iff c m := by
    have hD : Finset.univ.map booleanDomain = ({0, 1} : Finset E) := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
        fin_cases i
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · intro hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_map.mpr ⟨0, Finset.mem_univ _, rfl⟩
        · exact Finset.mem_map.mpr ⟨1, Finset.mem_univ _, rfl⟩
    rw [hD]
    exact (Sumcheck.compressedModel (R := E) (degree S L)).accept_iff c m

/-- The committed witness fixes the summand before any sumcheck challenge. -/
theorem bindsSummand (o : Bus.Output S L k) (ξ : E) (w₀ : Witness K S.tables.length) :
    Sumcheck.Interaction.Knowledge.BindsSummand (fun w ↦ w = w₀)
      (summand S L k o ξ) (summand S L k o ξ w₀) := by
  intro w hw
  exact congrArg (summand S L k o ξ) hw

/-- The sumcheck's initial statement: the batched target. -/
def initialStatement (o : Bus.Output S L k) (ξ : E) :
    Sumcheck.Spec.StatementRound E (maxHeight S L) ⟨0, by omega⟩ :=
  ⟨target S L k o ξ, Fin.elim0⟩

/-- ArkLib's sumcheck knowledge certificate for the table summand, the witness retained. -/
noncomputable def coreCertificate (o : Bus.Output S L k) (ξ : E) (w₀ : Witness K S.tables.length) :=
  Sumcheck.Interaction.Knowledge.certificate (messageOps S L) booleanDomain (messageModel S L)
    (fun w ↦ w = w₀) (summand S L k o ξ) (summand S L k o ξ w₀) (bindsSummand S L k o ξ w₀)
    (maxHeight S L) 0 (by omega) (initialStatement S L k o ξ) o.active

/-- The table sumcheck's output: the bus output, the final point and the transmitted values. -/
structure Output where
  /-- The bus output the table sumcheck reduces. -/
  bus : Bus.Output S L k
  /-- The final sumcheck point, low variable first. -/
  point : List E
  /-- The transmitted columns' values at the point. -/
  values : Values S L
  /-- Whether every public check passed. -/
  active : Bool

/-- The bus's shape and boundary claims, which the table sumcheck carries through. -/
def sideRelation (o : Bus.Output S L k) (w : Witness K S.tables.length) : Prop :=
  S.Shaped L w ∧ o.point.length = Bus.μ S L ∧
    ∀ p ∈ S.boundaryColumns L, S.boundaryValue L o.boundary p.1 p.2 =
      S.column L w p.1 p.2 (o.point.take (L.logHeight p.1))

/-- The endpoint: the bus's boundary claims and the transmitted values. -/
def Terminal (o : Output S L k) (w : Witness K S.tables.length) : Prop :=
  o.active = true ∧ sideRelation S L k o.bus w ∧ ValuesHold S L w o.point o.values

/-- The running claim after the challenges `χ`, highest variable first. -/
def reduced (o : Bus.Output S L k) (ξ : E) (χ : List E) (current : E)
    (w : Witness K S.tables.length) : Prop :=
  current = ∑ i : Fin (2 ^ (maxHeight S L - χ.length)),
    summandValue S L k o ξ w
      ((χ ++ List.ofFn (fun a : Fin (maxHeight S L - χ.length) ↦ bit i.val a.val)).reverse)

/-- The relation at a round. -/
def roundRelation (o : Bus.Output S L k) (ξ : E) (χ : List E) (current : E) (active : Bool)
    (w : Witness K S.tables.length) : Prop :=
  active = true ∧ sideRelation S L k o w ∧ reduced S L k o ξ χ current w

/-- The final message: the transmitted values. -/
def terminalProtocol : Protocol := .public .sender (Values S L) fun _ ↦ .done

/-- The sumcheck rounds, then the transmitted values. -/
def roundsProtocol : ℕ → Protocol
  | 0 => terminalProtocol S L
  | n + 1 => .oracleWith (Message S L) (Sumcheck.Interaction.Knowledge.messageInterface (messageOps S L))
      (.public .receiver (Option E) fun | none => .done | some _ => roundsProtocol n)

/-- The batching draw `ξ`, then one sumcheck over the tallest active table's variables. -/
def protocol : Protocol := .public .receiver E fun _ ↦ roundsProtocol S L (maxHeight S L)

/-- Prefix predicates on the rounds, the witness fixed throughout. -/
def roundsLabels (o : Bus.Output S L k) (ξ : E) :
    (n : ℕ) → List E → E → Bool → Retained.Labels (Witness K S.tables.length) (roundsProtocol S L n).tree
  | 0, χ, current, active =>
      ⟨roundRelation S L k o ξ χ current active, fun vals ↦
        Terminal S L k ⟨o, χ.reverse, vals,
          active && decide (formula S L k o ξ χ.reverse vals = current)⟩⟩
  | n + 1, χ, current, active =>
      ⟨roundRelation S L k o ξ χ current active, fun message ↦
        ⟨roundRelation S L k o ξ χ current active, fun
          | none => fun _ ↦ False
          | some r => roundsLabels o ξ n (χ ++ [r])
              ((messageOps S L).evaluate current message r)
              (active && (messageOps S L).accept current message)⟩⟩

/-- Prefix predicates on the table sumcheck, starting at the bus's endpoint. -/
def labels (o : Bus.Output S L k) : Retained.Labels (Witness K S.tables.length) (protocol S L).tree :=
  ⟨Bus.Terminal S L k o, fun ξ ↦ roundsLabels S L k o ξ (maxHeight S L) [] (target S L k o ξ) o.active⟩

/-- The extractor keeps the committed witness throughout. -/
def extractor (o : Bus.Output S L k) (w₀ : Witness K S.tables.length) :
    RoundExtractor (protocol S L).tree (Retained.state w₀ (Bus.Terminal S L k o)) :=
  Retained.extractor w₀ (labels S L k o)

/-- The rounds' draws, as in ArkLib's sumcheck certificate. -/
noncomputable def roundsChallenges : (n : ℕ) → E → RoundExtractor.ChallengeSchedule
    (roundsProtocol S L n).tree (roundsProtocol S L n).roles
  | 0, _ => ⟨PUnit.unit, fun _ ↦ PUnit.unit⟩
  | n + 1, current => fun message ↦
      ⟨⟨Sumcheck.Interaction.Knowledge.nextChallenge (messageOps S L) current message,
          overE (degree S L + 1)⟩, fun
        | none => PUnit.unit
        | some r => roundsChallenges n ((messageOps S L).evaluate current message r)⟩

/-- The `ξ` draw batches `constraintCount + 3` claims in a polynomial of degree
`constraintCount + 2`; each round's message has degree `degree + 1`. -/
noncomputable def challenges (o : Bus.Output S L k) :
    RoundExtractor.ChallengeSchedule (protocol S L).tree (protocol S L).roles :=
  ⟨⟨$ᵗ E, overE (constraintCount S + 2)⟩, fun ξ ↦ roundsChallenges S L (maxHeight S L) (target S L k o ξ)⟩

/-- The rounds' output from the messages and the transmitted values. -/
noncomputable def roundsOutput (o : Bus.Output S L k) (ξ : E) :
    (n : ℕ) → List E → E → Bool → (roundsProtocol S L n).tree.ExecutionPath → Option (Output S L k)
  | 0, χ, current, active, path => some
      ⟨o, χ.reverse, path.1, active && decide (formula S L k o ξ χ.reverse path.1 = current)⟩
  | n + 1, χ, current, active, path => match path with
    | ⟨_, none, _⟩ => none
    | ⟨message, some r, rest⟩ => roundsOutput o ξ n (χ ++ [r])
        ((messageOps S L).evaluate current message r)
        (active && (messageOps S L).accept current message) rest

/-- The table sumcheck's output on a path. -/
noncomputable def outputClaim (o : Bus.Output S L k) (path : (protocol S L).tree.ExecutionPath) :
    Option (Output S L k) :=
  roundsOutput S L k o path.1 (maxHeight S L) [] (target S L k o path.1) o.active path.2

/-- The output claim family. -/
def claimFamily : ClaimFamily Unit := ⟨fun _ ↦ Option (Output S L k)⟩

/-- The terminal problem, bound to the committed witness. -/
def terminalProblem (w₀ : Witness K S.tables.length) : Problem (claimFamily S L k) where
  Witness _ _ := Witness K S.tables.length
  admissible _ _ := True
  rel _ claim w := w = w₀ ∧ match claim with | none => False | some o => Terminal S L k o w
  rel_admissible := by intros; trivial

/-- The rounds' terminal knowledge is the terminal problem at their output. -/
theorem rounds_terminal_iff (o : Bus.Output S L k) (w₀ : Witness K S.tables.length)
    (ξ : E) (n : ℕ) (χ : List E) (current : E) (active : Bool)
    (path : (roundsProtocol S L n).tree.ExecutionPath)
    (w : ((Retained.extractor w₀ (roundsLabels S L k o ξ n χ current active)).terminalState path).Witness) :
    ((Retained.extractor w₀ (roundsLabels S L k o ξ n χ current active)).terminalState path).holds w ↔
      (terminalProblem S L k w₀).rel () (roundsOutput S L k o ξ n χ current active path)
        (Retained.terminalEquiv w₀ (roundsLabels S L k o ξ n χ current active) path w) := by
  induction n generalizing χ current active with
  | zero => rfl
  | succ n ih =>
    rcases path with ⟨message, choice, path⟩
    cases choice with
    | none =>
        change (_ ∧ False) ↔ (_ ∧ False)
        rfl
    | some r => exact ih _ _ _ path w

/-- The extractor's terminal knowledge is the terminal problem at the output claim. -/
def terminalRelation (o : Bus.Output S L k) (w₀ : Witness K S.tables.length) :
    TerminalRelation (extractor S L k o w₀) (terminalProblem S L k w₀) (fun _ ↦ ())
      (outputClaim S L k o) where
  witnessEquiv := Retained.terminalEquiv w₀ (labels S L k o)
  knowledge_iff path witness := rounds_terminal_iff S L k o w₀ path.1 (maxHeight S L) []
    (target S L k o path.1) o.active path.2 witness

/-- A sum over the cube's indices is a sum over an embedded Boolean domain's points. -/
theorem sum_embedded_cube {M : Type} [AddCommMonoid M] (n : ℕ)
    (D : Fin 2 ↪ E) (hD : ∀ i, D i = if i.val = 1 then 1 else 0)
    (f : (Fin n → E) → M) :
    (∑ i : Fin (2 ^ n), f (fun a ↦ bit i.val a.val)) = ∑ x ∈ (Finset.univ.map D) ^ᶠ n, f x := by
  classical
  have he (i : Fin (2 ^ n)) :
      (fun a : Fin n ↦ bit i.val a.val) = D ∘ finFunctionFinEquiv.symm i := by
    funext a
    rw [Function.comp_apply, hD]
    change (if i.val.testBit a.val then (1 : E) else 0) =
      if i.val / 2 ^ a.val % 2 = 1 then 1 else 0
    rw [Nat.testBit_eq_decide_div_mod_eq]
    simp only [decide_eq_true_eq]
  simp_rw [he]
  rw [show (∑ i : Fin (2 ^ n), f (D ∘ finFunctionFinEquiv.symm i)) =
    ∑ g : Fin n → Fin 2, f (D ∘ g) from finFunctionFinEquiv.symm.sum_comp (fun g ↦ f (D ∘ g))]
  apply Finset.sum_bij (fun g _ ↦ D ∘ g)
  · intro g _
    apply Fintype.mem_piFinset.mpr
    intro a
    exact Finset.mem_map.mpr ⟨g a, Finset.mem_univ _, rfl⟩
  · intro a _ b _ hab
    funext x
    exact D.injective (congrFun hab x)
  · intro x hx
    have hx := Fintype.mem_piFinset.mp hx
    have hx : ∀ a, ∃ c : Fin 2, D c = x a := fun a ↦ by
      obtain ⟨c, _, hc⟩ := Finset.mem_map.mp (hx a)
      exact ⟨c, hc⟩
    choose g hg using hx
    exact ⟨g, Finset.mem_univ _, funext hg⟩
  · intro _ _
    rfl

/-- The Boolean domain's points. -/
theorem booleanDomain_apply (i : Fin 2) : booleanDomain i = if i.val = 1 then 1 else 0 := by
  fin_cases i <;> rfl

/-- A list's entries recover the list. -/
theorem ofFn_getD (χ : List E) : List.ofFn (fun a : Fin χ.length ↦ χ.getD a.val 0) = χ := by
  have h : (fun a : Fin χ.length ↦ χ.getD a.val 0) = fun a : Fin χ.length ↦ χ[a.val] := by
    funext a
    exact List.getD_eq_getElem _ _ a.isLt
  rw [h, List.ofFn_getElem]

/-- Evaluation through the sumcheck oracle is polynomial evaluation. -/
theorem behavior_eval (n d : ℕ) (p : Sumcheck.Spec.OracleStatement E n d ()) (r : Fin n → E) :
    (polynomialFamily E n d).behaviorOfRealizations (fun _ ↦ p) ⟨(), r⟩ =
      MvPolynomial.eval r p.val := by rfl

/-- The running claim is ArkLib's closed polynomial claim. -/
theorem reduced_core_iff (hT : ∀ t, (S.table t).WellFormed) (o : Bus.Output S L k) (ξ : E)
    (w : Witness K S.tables.length) (χ : List E) (hlen : χ.length ≤ maxHeight S L) (current : E) :
    reduced S L k o ξ χ current w ↔
      closedRelation E (maxHeight S L) (degree S L + 1) booleanDomain ⟨χ.length, by omega⟩
        ⟨⟨current, fun a ↦ χ.getD a.val 0⟩,
          (polynomialFamily E (maxHeight S L) (degree S L + 1)).behaviorOfRealizations
            (fun _ ↦ summand S L k o ξ w)⟩ := by
  classical
  unfold reduced closedRelation
  simp only [behavior_eval]
  rw [← sum_embedded_cube (maxHeight S L - χ.length) booleanDomain booleanDomain_apply]
  rw [eq_comm]
  apply (fun (a b : E) (h : a = b) ↦ show a = current ↔ b = current from h ▸ Iff.rfl)
  apply Finset.sum_congr rfl
  intro a _
  rw [summand_eval S L k hT]
  congr 1
  congr 1
  rw [List.ofFn_congr (by omega : maxHeight S L = χ.length + (maxHeight S L - χ.length))]
  simp only [Function.comp_def, Fin.cast_cast, Fin.cast_refl, id_eq, List.ofFn_fin_append, ofFn_getD]

/-- The running claim is ArkLib's closed claim at a statement's challenges. -/
theorem reduced_core_ofFn_iff (hT : ∀ t, (S.table t).WellFormed) (o : Bus.Output S L k) (ξ : E)
    (w : Witness K S.tables.length) (i : Fin (maxHeight S L + 1))
    (stmt : Sumcheck.Spec.StatementRound E (maxHeight S L) i) :
    reduced S L k o ξ (List.ofFn stmt.challenges) stmt.target w ↔
      closedRelation E (maxHeight S L) (degree S L + 1) booleanDomain i
        ⟨stmt, (polynomialFamily E (maxHeight S L) (degree S L + 1)).behaviorOfRealizations
          (fun _ ↦ summand S L k o ξ w)⟩ := by
  have h := reduced_core_iff S L k hT o ξ w (List.ofFn stmt.challenges)
    (by simp only [List.length_ofFn]; omega) stmt.target
  have hi : (⟨(List.ofFn stmt.challenges).length, by simp only [List.length_ofFn]; omega⟩ :
      Fin (maxHeight S L + 1)) = i := Fin.ext List.length_ofFn
  have he (j : Fin (maxHeight S L + 1)) (hj : j = i) (p : Fin j.val → E)
      (hp : ∀ a : Fin j.val, p a = stmt.challenges ⟨a.val, by
        have := a.isLt; have := congrArg Fin.val hj; omega⟩) :
      closedRelation E (maxHeight S L) (degree S L + 1) booleanDomain j
        ⟨⟨stmt.target, p⟩, (polynomialFamily E (maxHeight S L) (degree S L + 1)).behaviorOfRealizations
          (fun _ ↦ summand S L k o ξ w)⟩ ↔
      closedRelation E (maxHeight S L) (degree S L + 1) booleanDomain i
        ⟨stmt, (polynomialFamily E (maxHeight S L) (degree S L + 1)).behaviorOfRealizations
          (fun _ ↦ summand S L k o ξ w)⟩ := by
    subst j
    have hfun : p = stmt.challenges := funext hp
    rw [hfun]
  exact h.trans (he _ hi _ (fun a ↦ by
    rw [List.getD_eq_getElem _ _ a.isLt, List.getElem_ofFn]))

/-- Boolean cube coordinates, low first. -/
def cubeList {n : ℕ} (x : Fin n → Fin 2) : List E := List.ofFn fun a ↦ (x a).val

/-- Reversing the coordinates permutes the cube. -/
def reverseCube (n : ℕ) : (Fin n → Fin 2) ≃ (Fin n → Fin 2) where
  toFun x a := x a.rev
  invFun x a := x a.rev
  left_inv x := funext fun a ↦ by dsimp only; rw [Fin.rev_rev]
  right_inv x := funext fun a ↦ by dsimp only; rw [Fin.rev_rev]

/-- A cube index's coordinates are its bits. -/
theorem cubeList_index (n : ℕ) (i : Fin (2 ^ n)) :
    cubeList (finFunctionFinEquiv.symm i) = List.ofFn (fun a : Fin n ↦ bit i.val a.val) := by
  apply congrArg List.ofFn
  funext a
  exact finFunction_bits n i a

/-- Reversing a coordinate list applies the cube permutation. -/
theorem cubeList_reverse (n : ℕ) (x : Fin n → Fin 2) :
    (cubeList x).reverse = cubeList (reverseCube n x) := by
  apply List.ext_getElem
  · simp only [List.length_reverse, cubeList, List.length_ofFn]
  · intro i hi hj
    simp only [cubeList, List.getElem_reverse, List.length_ofFn, List.getElem_ofFn,
      reverseCube, Equiv.coe_fn_mk, Fin.rev]
    apply congrArg (fun j : Fin n ↦ ((x j).val : E))
    apply Fin.ext
    change n - 1 - i = n - (i + 1)
    omega

/-- Reversing the coordinates permutes a Boolean sum. -/
theorem sum_bits_reverse (n : ℕ) (f : List E → E) :
    (∑ i : Fin (2 ^ n), f (List.ofFn (fun a : Fin n ↦ bit i.val a.val)).reverse) =
      ∑ i : Fin (2 ^ n), f (List.ofFn (fun a : Fin n ↦ bit i.val a.val)) := by
  simp_rw [← cubeList_index]
  rw [finFunctionFinEquiv.symm.sum_comp (fun x ↦ f (cubeList x).reverse),
    finFunctionFinEquiv.symm.sum_comp (fun x ↦ f (cubeList x))]
  simp_rw [cubeList_reverse]
  exact (reverseCube n).sum_comp (fun x ↦ f (cubeList x))

/-- The low coordinates of a split cube point are the low cube point. -/
theorem bits_cubeIndex_take (h m : ℕ) (i : Fin (2 ^ h)) (j : Fin (2 ^ m)) :
    (List.ofFn fun a : Fin (h + m) ↦ bit (Algebra.cubeIndex i j).val a.val).take h =
      List.ofFn fun a : Fin h ↦ bit i.val a.val := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_ofFn]; omega
  · intro a ha hb
    simp only [List.getElem_take, List.getElem_ofFn, bit, Algebra.testBit_cubeIndex,
      show a < h from by simpa only [List.length_ofFn] using hb, ↓reduceIte]

/-- The all-ones weight on the high coordinates sums to one. -/
theorem sum_high_bits (m : ℕ) : (∑ j : Fin (2 ^ m), ∏ a : Fin m, bit j.val a.val) = (1 : E) := by
  have h := mle_const m (1 : E) (List.replicate m 1)
  have hz (a : Fin m) : (List.replicate m (1 : E)).getD a.val 0 = 1 := by
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_replicate] using a.isLt),
      List.getElem_replicate]
  unfold mle at h
  simp_rw [hz] at h
  simpa only [eqFactor, sub_self, zero_mul, one_mul, zero_add] using h

/-- Summing out the high coordinates leaves the low equality-weighted extension. -/
theorem backload_sum (h m : ℕ) (ζ : List E) (f : List E → E) :
    (∑ x : Fin (2 ^ (h + m)),
      ((∏ a : Fin h, eqFactor (ζ.getD a.val 0) (bit x.val a.val)) *
        ∏ a : Fin m, bit x.val (h + a.val)) *
          f ((List.ofFn fun a : Fin (h + m) ↦ bit x.val a.val).take h)) =
      mle h (fun i ↦ f (List.ofFn fun a : Fin h ↦ bit i a.val)) ζ := by
  rw [Algebra.sum_cube_split]
  simp_rw [bits_cubeIndex_take]
  have hlo (i : Fin (2 ^ h)) (j : Fin (2 ^ m)) (a : Fin h) :
      bit (Algebra.cubeIndex i j).val a.val = bit i.val a.val := by
    simp only [bit, Algebra.testBit_cubeIndex, a.isLt, ↓reduceIte]
  have hhi (i : Fin (2 ^ h)) (j : Fin (2 ^ m)) (a : Fin m) :
      bit (Algebra.cubeIndex i j).val (h + a.val) = bit j.val a.val := by
    simp only [bit, Algebra.testBit_cubeIndex, Nat.not_lt.mpr (Nat.le_add_right _ _),
      ↓reduceIte, Nat.add_sub_cancel_left]
  simp_rw [hlo, hhi]
  rw [Finset.sum_comm]
  unfold mle
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_high_bits, mul_one]
  exact mul_comm _ _

/-- The high-coordinate product. -/
def highBits (h m i : ℕ) : E := ∏ a : Fin m, bit i (h + a.val)

/-- A table's equality and high-coordinate weights on the ambient cube. -/
def backloadCube (m h : ℕ) (ζ : List E) (f : List E → E) : E :=
  ∑ x : Fin (2 ^ m),
    ((∏ a : Fin h, eqFactor (ζ.getD a.val 0) (bit x.val a.val)) * highBits h (m - h) x.val) *
      f ((List.ofFn fun a : Fin m ↦ bit x.val a.val).take h)

/-- Summing out works at every table height below the ambient one. -/
theorem backloadCube_eq (m h : ℕ) (hh : h ≤ m) (ζ : List E) (f : List E → E) :
    backloadCube m h ζ f = mle h (fun i ↦ f (List.ofFn fun a : Fin h ↦ bit i a.val)) ζ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hh
  unfold backloadCube
  rw [Nat.add_sub_cancel_left]
  exact backload_sum h d ζ f

/-- An active table's share of the cube sum is the extension of its rows' formulas. -/
theorem table_cube_sum (o : Bus.Output S L k) (ξ : E) (w : Witness K S.tables.length)
    (t : Active S L) :
    (∑ i : Fin (2 ^ maxHeight S L),
      tableWeight S L k o t (List.ofFn fun a : Fin (maxHeight S L) ↦ bit i.val a.val) *
        rowValue S L k o ξ t (fun c ↦ cellColumn S L w t.1 c
          ((List.ofFn fun a : Fin (maxHeight S L) ↦ bit i.val a.val).take (L.logHeight t.1)))) =
      mle (L.logHeight t.1) (fun i ↦ rowValue S L k o ξ t (fun c ↦ ofK (cell S w t.1 i c))) o.point := by
  have hle := height_le_maxHeight S L t
  have hw (i : Fin (2 ^ maxHeight S L)) :
      tableWeight S L k o t (List.ofFn fun a : Fin (maxHeight S L) ↦ bit i.val a.val) =
        (∏ a : Fin (L.logHeight t.1), eqFactor (o.point.getD a.val 0) (bit i.val a.val)) *
          highBits (L.logHeight t.1) (maxHeight S L - L.logHeight t.1) i.val := by
    unfold tableWeight highBits
    apply congrArg₂ (fun a b : E ↦ a * b)
    · apply Finset.prod_congr rfl
      intro a _
      rw [List.getD_eq_getElem (List.ofFn fun a : Fin (maxHeight S L) ↦ bit i.val a.val) 0
        (by simpa only [List.length_ofFn] using a.isLt.trans_le hle), List.getElem_ofFn]
    · apply Finset.prod_congr rfl
      intro a _
      rw [List.getD_eq_getElem (List.ofFn fun a : Fin (maxHeight S L) ↦ bit i.val a.val) 0
        (by have := a.isLt; simp only [List.length_ofFn]; omega), List.getElem_ofFn]
  simp_rw [hw]
  rw [show (∑ i : Fin (2 ^ maxHeight S L),
      ((∏ a : Fin (L.logHeight t.1), eqFactor (o.point.getD a.val 0) (bit i.val a.val)) *
        highBits (L.logHeight t.1) (maxHeight S L - L.logHeight t.1) i.val) *
      rowValue S L k o ξ t (fun c ↦ cellColumn S L w t.1 c
        ((List.ofFn fun a : Fin (maxHeight S L) ↦ bit i.val a.val).take (L.logHeight t.1)))) =
      backloadCube (maxHeight S L) (L.logHeight t.1) o.point
        (fun z ↦ rowValue S L k o ξ t (fun c ↦ cellColumn S L w t.1 c z)) from rfl,
    backloadCube_eq _ _ hle]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun x : E ↦ x * ∏ a : Fin (L.logHeight t.1), eqFactor (o.point.getD a.val 0) (bit i.val a.val))
  apply congrArg (rowValue S L k o ξ t)
  funext c
  exact mle_bits _ _ i

/-- The summand's cube sum is the sum of the active tables' row-formula extensions. -/
theorem summand_cube_sum (o : Bus.Output S L k) (ξ : E) (w : Witness K S.tables.length) :
    (∑ i : Fin (2 ^ maxHeight S L),
      summandValue S L k o ξ w (List.ofFn (fun a : Fin (maxHeight S L) ↦ bit i.val a.val)).reverse) =
      ∑ t : Active S L, mle (L.logHeight t.1)
        (fun i ↦ rowValue S L k o ξ t (fun c ↦ ofK (cell S w t.1 i c))) o.point := by
  rw [sum_bits_reverse]
  unfold summandValue
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ ↦ table_cube_sum S L k o ξ w t

end CompStark.Tables.TableSumcheck
