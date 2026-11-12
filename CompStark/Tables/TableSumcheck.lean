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

end CompStark.Stark.Expr

namespace CompStark.Tables.TableSumcheck

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System
open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp MvPolynomial
open Sumcheck.Interaction.MultivariateRound

variable (S : System K) (L : Layout S.tables.length) (k : ℕ)

/-- The tables the table sumcheck covers: those the bus does not open directly. -/
abbrev Active := {t : Fin S.tables.length // S.Direct L t = false}

/-- The active tables in table order. -/
def activeList : List (Active S L) :=
  (List.finRange S.tables.length).filterMap fun t ↦
    if h : S.Direct L t = false then some ⟨t, h⟩ else none

/-- The sumcheck's number of variables: the tallest active table's. -/
def maxHeight : ℕ := Finset.univ.sup fun t : Active S L ↦ L.logHeight t.1

/-- Every active table fits the sumcheck's variables. -/
theorem height_le_maxHeight (t : Active S L) : L.logHeight t.1 ≤ maxHeight S L :=
  Finset.le_sup (f := fun t : Active S L ↦ L.logHeight t.1) (Finset.mem_univ t)

/-- An active table's constraints as polynomials in its row values. -/
noncomputable def constraints (t : Active S L) : List (MvPolynomial ℕ E) :=
  (S.table t.1).air.constraints.map (Expr.toPoly (S.table t.1).air.width)

/-- The number of constraints of the active tables before `t`, in table order. -/
def constraintOffset (t : Active S L) : ℕ :=
  (((activeList S L).takeWhile (· ≠ t)).map fun s ↦ (S.table s.1).air.constraints.length).sum

/-- The number of constraints of all active tables. -/
def constraintCount : ℕ :=
  ((activeList S L).map fun s ↦ (S.table s.1).air.constraints.length).sum

/-- The largest individual degree of a constraint or tuple entry of an active table, at least
one. -/
def degree : ℕ :=
  max 1 (Finset.univ.sup fun t : Active S L ↦ max (S.tupleDegree t.1)
    (((S.table t.1).air.constraints.map Expr.degree).foldl max 0))

/-- The columns a table's constraints or tuples read: those the table phase transmits. -/
def transmitted (t : Fin S.tables.length) : List ℕ :=
  (List.range (S.table t).air.width).filter fun c ↦
    (S.table t).air.constraints.any (Expr.readsCol c) ||
      (S.table t).interactions.any fun I ↦ I.tuple.any (Expr.readsCol c)

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
  (∑ i : Fin (constraints S L t).length,
    ξ ^ (constraintOffset S L t + i.val) * MvPolynomial.eval v (constraints S L t)[i]) +
  ∑ s : Fin 3, ξ ^ (constraintCount S L + s.val) *
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
  ∑ s : Fin 3, ξ ^ (constraintCount S L + s.val) * o.remainders s

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
    ((∑ i : Fin (constraints S L t).length,
      MvPolynomial.C (ξ ^ (constraintOffset S L t + i.val)) *
        MvPolynomial.bind₁ (columnPolynomial S L w t) (constraints S L t)[i]) +
      ∑ side : Fin 3, MvPolynomial.C (ξ ^ (constraintCount S L + side.val)) *
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
  have hair : (∑ i : Fin (constraints S L t).length,
      C (ξ ^ (constraintOffset S L t + i.val)) *
        bind₁ (columnPolynomial S L w t) (constraints S L t)[i]).degreeOf j ≤ degree S L := by
    refine (degreeOf_sum_le j _ _).trans (Finset.sup_le fun i _ ↦ ?_)
    refine (degreeOf_mul_le j _ _).trans ?_
    rw [degreeOf_C, zero_add]
    obtain ⟨e, he, hpoly⟩ := List.mem_map.mp (List.getElem_mem (l := constraints S L t) i.isLt)
    simp only [Fin.getElem_fin]
    rw [← hpoly]
    exact (Expr.toPoly_bind_degreeOf _ e _ j (fun c ↦ columnPolynomial_degree S L w t c j)).trans
      (constraint_degree_le S L t e he)
  have hbus : (∑ side : Fin 3, C (ξ ^ (constraintCount S L + side.val)) *
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

end CompStark.Tables.TableSumcheck
