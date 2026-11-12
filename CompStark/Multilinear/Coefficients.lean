/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Multilinear.Basic

/-! Univariate polynomials as coefficient lists, constant term first: sums, scalings, products and
their evaluations, and Lagrange interpolation at distinct points with its uniqueness among
polynomials of bounded degree (`lagrange_eq`). -/

@[expose] public section

namespace CompStark.Multilinear

open CompStark.BinaryFields

/-- A coefficient list's value at a point, constant term first. -/
def evalCoeffs (p : List E) (x : E) : E := p.foldr (fun c acc ↦ c + x * acc) 0

/-- The sum of two coefficient lists. -/
def addCoeffs : List E → List E → List E
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: addCoeffs p q

/-- A coefficient list scaled by a constant. -/
def scaleCoeffs (c : E) (p : List E) : List E := p.map (c * ·)

/-- The product of two coefficient lists. -/
def mulCoeffs : List E → List E → List E
  | [], _ => []
  | a :: p, q => addCoeffs (scaleCoeffs a q) (0 :: mulCoeffs p q)

/-- Sums of coefficient lists evaluate to sums. -/
theorem evalCoeffs_add (p q : List E) (x : E) :
    evalCoeffs (addCoeffs p q) x = evalCoeffs p x + evalCoeffs q x := by
  induction p generalizing q with
  | nil => simp only [addCoeffs, evalCoeffs, List.foldr_nil, zero_add]
  | cons a p ih =>
    cases q with
    | nil => simp only [addCoeffs, evalCoeffs, List.foldr_nil, add_zero]
    | cons b q =>
      simp only [addCoeffs, evalCoeffs, List.foldr_cons] at ih ⊢
      rw [ih]
      ring

/-- Scaled coefficient lists evaluate to scaled values. -/
theorem evalCoeffs_scale (c : E) (p : List E) (x : E) :
    evalCoeffs (scaleCoeffs c p) x = c * evalCoeffs p x := by
  induction p with
  | nil => simp only [scaleCoeffs, evalCoeffs, List.map_nil, List.foldr_nil, mul_zero]
  | cons a p ih =>
    simp only [scaleCoeffs, evalCoeffs, List.map_cons, List.foldr_cons] at ih ⊢
    rw [ih]
    ring

/-- Products of coefficient lists evaluate to products. -/
theorem evalCoeffs_mul (p q : List E) (x : E) :
    evalCoeffs (mulCoeffs p q) x = evalCoeffs p x * evalCoeffs q x := by
  induction p with
  | nil => simp only [mulCoeffs, evalCoeffs, List.foldr_nil, zero_mul]
  | cons a p ih =>
    simp only [mulCoeffs, evalCoeffs_add, evalCoeffs_scale]
    simp only [evalCoeffs, List.foldr_cons] at ih ⊢
    rw [ih]
    ring

/-- A sum has the length of its longer operand. -/
theorem length_addCoeffs (p q : List E) : (addCoeffs p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp only [addCoeffs, List.length_nil, Nat.zero_max]
  | cons a p ih =>
    cases q with
    | nil => simp only [addCoeffs, List.length_cons, List.length_nil, Nat.max_zero]
    | cons b q => simp only [addCoeffs, List.length_cons, ih, Nat.succ_max_succ]

/-- A product with a nonempty list has at most one less than the sum of the lengths. -/
theorem length_mulCoeffs_le (p q : List E) (hq : q ≠ []) :
    (mulCoeffs p q).length ≤ p.length + q.length - 1 := by
  have hq' : 0 < q.length := List.length_pos_iff.mpr hq
  induction p with
  | nil => simp only [mulCoeffs, List.length_nil, Nat.zero_le]
  | cons a p ih =>
    simp only [mulCoeffs, length_addCoeffs, scaleCoeffs, List.length_map, List.length_cons]
    omega

/-- A sum of coefficient lists over a list of indices. -/
def sumCoeffs {ι : Type} (l : List ι) (f : ι → List E) : List E :=
  l.foldr (fun i acc ↦ addCoeffs (f i) acc) []

/-- A product of coefficient lists over a list of indices. -/
def prodCoeffs {ι : Type} (l : List ι) (f : ι → List E) : List E :=
  l.foldr (fun i acc ↦ mulCoeffs (f i) acc) [1]

/-- Sums over an index list evaluate to sums. -/
theorem evalCoeffs_sum {ι : Type} (l : List ι) (f : ι → List E) (x : E) :
    evalCoeffs (sumCoeffs l f) x = (l.map fun i ↦ evalCoeffs (f i) x).sum := by
  induction l with
  | nil => simp only [sumCoeffs, evalCoeffs, List.foldr_nil, List.map_nil, List.sum_nil]
  | cons i l ih =>
    simp only [sumCoeffs, List.foldr_cons, evalCoeffs_add, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

/-- Products over an index list evaluate to products. -/
theorem evalCoeffs_prod {ι : Type} (l : List ι) (f : ι → List E) (x : E) :
    evalCoeffs (prodCoeffs l f) x = (l.map fun i ↦ evalCoeffs (f i) x).prod := by
  induction l with
  | nil =>
    simp only [prodCoeffs, evalCoeffs, List.foldr_nil, List.foldr_cons, mul_zero, add_zero,
      List.map_nil, List.prod_nil]
  | cons i l ih =>
    simp only [prodCoeffs, List.foldr_cons, evalCoeffs_mul, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]

/-- A sum's length is at most the bound of its terms. -/
theorem length_sumCoeffs_le {ι : Type} (l : List ι) (f : ι → List E) (d : ℕ)
    (h : ∀ i ∈ l, (f i).length ≤ d) : (sumCoeffs l f).length ≤ d := by
  induction l with
  | nil => simp only [sumCoeffs, List.foldr_nil, List.length_nil, Nat.zero_le]
  | cons i l ih =>
    simp only [sumCoeffs, List.foldr_cons, length_addCoeffs] at ih ⊢
    exact max_le (h i (List.mem_cons_self ..)) (ih fun j hj ↦ h j (List.mem_cons_of_mem _ hj))

/-- A product with a nonempty first factor is nonempty. -/
theorem mulCoeffs_ne_nil (p q : List E) (hp : p ≠ []) : mulCoeffs p q ≠ [] := by
  cases p with
  | nil => exact absurd rfl hp
  | cons a p =>
    intro h
    have := congrArg List.length h
    simp only [mulCoeffs, length_addCoeffs, List.length_cons, List.length_nil] at this
    omega

/-- A product of nonempty affine factors is nonempty with at most one more coefficient than
factors. -/
theorem length_prodCoeffs_le {ι : Type} (l : List ι) (f : ι → List E)
    (h : ∀ i ∈ l, (f i).length ≤ 2 ∧ f i ≠ []) :
    (prodCoeffs l f).length ≤ l.length + 1 ∧ prodCoeffs l f ≠ [] := by
  induction l with
  | nil => simp only [prodCoeffs, List.foldr_nil, List.length_cons, List.length_nil, le_refl,
      ne_eq, List.cons_ne_nil, not_false_eq_true, and_self]
  | cons i l ih =>
    obtain ⟨hl, hne⟩ := ih fun j hj ↦ h j (List.mem_cons_of_mem _ hj)
    obtain ⟨hf, hfne⟩ := h i (List.mem_cons_self ..)
    simp only [prodCoeffs, List.foldr_cons] at hl hne ⊢
    refine ⟨?_, mulCoeffs_ne_nil _ _ hfne⟩
    have := length_mulCoeffs_le (f i) _ hne
    simp only [List.length_cons]
    omega

/-- The polynomial of a coefficient list. -/
noncomputable def coeffsPoly : List E → Polynomial E
  | [] => 0
  | a :: p => Polynomial.C a + Polynomial.X * coeffsPoly p

/-- A coefficient list's polynomial evaluates as the list. -/
theorem coeffsPoly_eval (p : List E) (x : E) : (coeffsPoly p).eval x = evalCoeffs p x := by
  induction p with
  | nil => simp only [coeffsPoly, Polynomial.eval_zero, evalCoeffs, List.foldr_nil]
  | cons a p ih =>
    simp only [coeffsPoly, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X, ih]
    simp only [evalCoeffs, List.foldr_cons]

/-- A coefficient list's polynomial has the list's coefficients. -/
theorem coeffsPoly_coeff (p : List E) (i : ℕ) : (coeffsPoly p).coeff i = p.getD i 0 := by
  induction p generalizing i with
  | nil => simp only [coeffsPoly, Polynomial.coeff_zero, List.getD_nil]
  | cons a p ih =>
    cases i with
    | zero => simp only [coeffsPoly, Polynomial.coeff_add, Polynomial.coeff_C_zero,
        Polynomial.coeff_X_mul_zero, add_zero, List.getD_cons_zero]
    | succ i =>
      simp only [coeffsPoly, Polynomial.coeff_add, Polynomial.coeff_C_succ, Polynomial.coeff_X_mul,
        zero_add, ih, List.getD_cons_succ]

/-- A coefficient list's polynomial has degree below the list's length. -/
theorem coeffsPoly_natDegree_lt (p : List E) (hp : p ≠ []) :
    (coeffsPoly p).natDegree < p.length := by
  have hlen : 0 < p.length := List.length_pos_iff.mpr hp
  apply Nat.lt_of_le_of_lt _ (Nat.sub_lt hlen Nat.one_pos)
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeffsPoly_coeff, List.getD_eq_default _ _ (by
    have : p.length - 1 < i := by exact_mod_cast hi
    omega)]

/-- The Lagrange interpolant of the values `y` at the distinct points `x`, as coefficients. -/
def lagrangeCoeffs {n : ℕ} (x y : Fin n → E) : List E :=
  sumCoeffs (List.finRange n) fun j ↦
    scaleCoeffs (y j * ((((List.finRange n).filter (· ≠ j)).map fun m ↦ x j - x m).prod)⁻¹)
      (prodCoeffs ((List.finRange n).filter (· ≠ j)) fun m ↦ [-x m, 1])

/-- The Lagrange interpolant takes the prescribed values at the distinct points. -/
theorem evalCoeffs_lagrange {n : ℕ} (x y : Fin n → E) (hx : Function.Injective x) (i : Fin n) :
    evalCoeffs (lagrangeCoeffs x y) (x i) = y i := by
  unfold lagrangeCoeffs
  rw [evalCoeffs_sum, ← List.ofFn_eq_map, List.sum_ofFn, Finset.sum_eq_single i]
  · rw [evalCoeffs_scale, evalCoeffs_prod]
    have hfac : (((List.finRange n).filter (· ≠ i)).map fun m ↦ evalCoeffs [-x m, 1] (x i)) =
        (((List.finRange n).filter (· ≠ i)).map fun m ↦ x i - x m) := by
      apply List.map_congr_left
      intro m _
      simp only [evalCoeffs, List.foldr_cons, List.foldr_nil, mul_zero, add_zero, mul_one]
      ring
    rw [hfac]
    have hne : (((List.finRange n).filter (· ≠ i)).map fun m ↦ x i - x m).prod ≠ 0 := by
      intro h0
      obtain ⟨m, hm, hmz⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp h0)
      have hmi : m ≠ i := by simpa only [List.mem_filter, List.mem_finRange, true_and,
        decide_eq_true_eq] using hm
      exact sub_ne_zero.mpr (fun h ↦ hmi (hx h).symm) hmz
    rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
  · intro j _ hj
    rw [evalCoeffs_scale, evalCoeffs_prod]
    apply mul_eq_zero_of_right
    apply List.prod_eq_zero
    apply List.mem_map.mpr
    refine ⟨i, ?_, ?_⟩
    · simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
      exact fun h ↦ hj h.symm
    · simp only [evalCoeffs, List.foldr_cons, List.foldr_nil, mul_zero, add_zero, mul_one]
      ring
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The Lagrange interpolant of `n` points has at most `n` coefficients. -/
theorem length_lagrange_le {n : ℕ} (x y : Fin n → E) : (lagrangeCoeffs x y).length ≤ n := by
  apply length_sumCoeffs_le
  intro j _
  simp only [scaleCoeffs, List.length_map]
  have h := (length_prodCoeffs_le ((List.finRange n).filter (· ≠ j)) (fun m ↦ [-x m, 1])
    (fun _ _ ↦ by simp only [List.length_cons, List.length_nil, le_refl, ne_eq, List.cons_ne_nil,
      not_false_eq_true, and_self])).1
  have hf : ((List.finRange n).filter (· ≠ j)).length = n - 1 := by
    have he : (List.finRange n).filter (fun m ↦ decide (m ≠ j)) = (List.finRange n).erase j := by
      rw [(List.nodup_finRange n).erase_eq_filter]
      apply List.filter_congr
      intro m _
      simp only [ne_eq, decide_not, bne_iff_ne]
      rfl
    rw [he, List.length_erase_of_mem (List.mem_finRange j), List.length_finRange]
  have hn : 1 ≤ n := by have := j.isLt; omega
  omega

/-- A polynomial of degree below `n` is the Lagrange interpolant of its values at `n` distinct
points. -/
theorem coeffsPoly_lagrange {n : ℕ} (x : Fin n → E) (hx : Function.Injective x) (q : Polynomial E)
    (hq : q.natDegree < n) : coeffsPoly (lagrangeCoeffs x fun i ↦ q.eval (x i)) = q := by
  classical
  apply Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq (Finset.univ.image x)
  · rw [Finset.card_image_of_injective _ hx, Finset.card_univ, Fintype.card_fin]
    apply lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
    apply max_lt
    · by_cases hl : lagrangeCoeffs x (fun i ↦ q.eval (x i)) = []
      · rw [hl]
        simp only [coeffsPoly, Polynomial.degree_zero]
        exact WithBot.bot_lt_coe _
      · exact (Polynomial.degree_le_natDegree).trans_lt (by
          exact_mod_cast (coeffsPoly_natDegree_lt _ hl).trans_le (length_lagrange_le _ _))
    · exact (Polynomial.degree_le_natDegree).trans_lt (by exact_mod_cast hq)
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    rw [coeffsPoly_eval, evalCoeffs_lagrange x _ hx]

end CompStark.Multilinear
