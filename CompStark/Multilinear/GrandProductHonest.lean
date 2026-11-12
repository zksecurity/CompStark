/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Multilinear.GrandProduct

/-! The honest prover of the grand-product GKR, computed from coefficient lists, and its
completeness: against every sequence of verifier coins the parsed result is the true final claim,
accepted (`result_honest`).

A round message is the tail of the weighted partial cofactor, a product of affine child factors
summed over the remaining Boolean coordinates; `honestMessage_evaluate` proves it decodes at the
true running claim to the next partial sum, as `partialMessage` does. -/

@[expose] public section

namespace CompStark.Multilinear.GrandProduct

open CompStark.BinaryFields
open Interaction Interaction.Oracle

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

/-- The affine interpolation of two endpoint values as coefficients. -/
def affineCoeffs (a b : E) : List E := [a, b - a]

/-- The affine coefficients evaluate to the affine interpolation. -/
theorem evalCoeffs_affine (a b x : E) :
    evalCoeffs (affineCoeffs a b) x = (affinePolynomial a b).eval x := by
  simp only [affineCoeffs, evalCoeffs, List.foldr_cons, List.foldr_nil, mul_zero, add_zero,
    affinePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
  ring

/-- The honest cofactor with the remaining coordinates fixed, as coefficients. -/
def cofactorCoeffs (μ m ρ : ℕ) (leaves : Fin 3 → ℕ → E) (lam : E) (χ v : List E) : List E :=
  sumCoeffs (List.finRange 3) fun s ↦ scaleCoeffs (lam ^ s.val)
    (prodCoeffs (List.finRange (2 ^ ρ)) fun a ↦
      affineCoeffs (childValue μ m ρ leaves s a.val (χ ++ [0] ++ v))
        (childValue μ m ρ leaves s a.val (χ ++ [1] ++ v)))

/-- The honest weighted partial cofactor at a prefix, as coefficients. -/
def partialCoeffs (μ m ρ : ℕ) (leaves : Fin 3 → ℕ → E) (lam : E) (point χ : List E) : List E :=
  sumCoeffs (List.finRange (2 ^ (m - (χ.length + 1)))) fun i ↦
    scaleCoeffs (∏ k : Fin (m - (χ.length + 1)),
        eqFactor (point.getD (χ.length + 1 + k.val) 0) (bit i.val k.val))
      (cofactorCoeffs μ m ρ leaves lam χ (List.ofFn fun k : Fin (m - (χ.length + 1)) ↦ bit i.val k.val))

/-- The partial coefficients evaluate to the honest partial polynomial. -/
theorem evalCoeffs_partial (μ m ρ : ℕ) (leaves : Fin 3 → ℕ → E) (lam : E) (point χ : List E)
    (x : E) :
    evalCoeffs (partialCoeffs μ m ρ leaves lam point χ) x =
      (partialPolynomial μ m ρ leaves lam point χ).eval x := by
  simp only [partialCoeffs, cofactorCoeffs, evalCoeffs_sum, evalCoeffs_scale, evalCoeffs_prod,
    evalCoeffs_affine, partialPolynomial, cofactorPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (_ * ·)
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro s _
  rw [← List.ofFn_eq_map, List.prod_ofFn]

/-- The partial coefficients have at most `2 ^ ρ + 1` entries. -/
theorem length_partialCoeffs_le (μ m ρ : ℕ) (leaves : Fin 3 → ℕ → E) (lam : E) (point χ : List E) :
    (partialCoeffs μ m ρ leaves lam point χ).length ≤ 2 ^ ρ + 1 := by
  apply length_sumCoeffs_le
  intro i _
  simp only [scaleCoeffs, List.length_map, cofactorCoeffs]
  apply length_sumCoeffs_le
  intro s _
  simp only [scaleCoeffs, List.length_map]
  have := (length_prodCoeffs_le (List.finRange (2 ^ ρ)) (fun a ↦
      affineCoeffs (childValue μ m ρ leaves s a.val (χ ++ [0] ++ (List.ofFn fun k : Fin (m - (χ.length + 1)) ↦ bit i.val k.val)))
        (childValue μ m ρ leaves s a.val (χ ++ [1] ++ (List.ofFn fun k : Fin (m - (χ.length + 1)) ↦ bit i.val k.val))))
    (fun _ _ ↦ by simp only [affineCoeffs, List.length_cons, List.length_nil, le_refl, ne_eq,
      List.cons_ne_nil, not_false_eq_true, and_self])).1
  simpa only [List.length_finRange] using this

/-- A short coefficient list read as a full coefficient vector evaluates the same. -/
theorem evaluateCoefficients_getD (d : ℕ) (p : List E) (hp : p.length ≤ d + 1) (x : E) :
    evaluateCoefficients d (fun j ↦ p.getD j.val 0) x = evalCoeffs p x := by
  induction p generalizing d with
  | nil =>
    simp only [evaluateCoefficients, List.getD_nil, zero_mul, Finset.sum_const_zero, evalCoeffs,
      List.foldr_nil]
  | cons a p ih =>
    cases d with
    | zero =>
      have hp0 : p = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hp; omega)
      subst hp0
      rw [evaluateCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero]
      simp only [Fin.val_zero, List.getD_cons_zero, pow_zero, mul_one, add_zero, evalCoeffs,
        List.foldr_cons, List.foldr_nil, mul_zero]
    | succ d =>
      rw [evaluateCoefficients, Fin.sum_univ_succ]
      have h := ih d (by simp only [List.length_cons] at hp; omega)
      rw [evaluateCoefficients] at h
      have hs : (∑ j : Fin (d + 1), (a :: p).getD j.succ.val 0 * x ^ j.succ.val) =
          x * ∑ j : Fin (d + 1), p.getD j.val 0 * x ^ j.val := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [Fin.val_succ, List.getD_cons_succ, pow_succ]
        ring
      rw [hs, h]
      simp only [Fin.val_zero, List.getD_cons_zero, pow_zero, mul_one, evalCoeffs, List.foldr_cons]

/-- The honest round message: the partial cofactor's coefficients of degrees one to `2 ^ ρ`. -/
def honestMessage (μ m ρ : ℕ) (leaves : Fin 3 → ℕ → E) (lam : E) (point χ : List E) :
    Message (2 ^ ρ) :=
  let p := partialCoeffs μ m ρ leaves lam point χ
  fun j ↦ p.getD (j.val + 1) 0

/-- At the true running claim, the honest message decodes to the next partial sum. -/
theorem honestMessage_evaluate (μ m ρ n : ℕ) (leaves : Fin 3 → ℕ → E) (lam : E)
    (point χ : List E) (hχ : χ.length + (n + 1) = m) (x : E) :
    evaluate (2 ^ ρ) (point.getD χ.length 0)
      (weightedPartial m (cofactor μ m ρ leaves lam) point χ)
      (honestMessage μ m ρ leaves lam point χ) x =
        weightedPartial m (cofactor μ m ρ leaves lam) point (χ ++ [x]) := by
  set p := partialCoeffs μ m ρ leaves lam point χ with hp
  have hlen := length_partialCoeffs_le μ m ρ leaves lam point χ
  have heval (y : E) : evaluateCoefficients (2 ^ ρ) (fun j ↦ p.getD j.val 0) y =
      weightedPartial m (cofactor μ m ρ leaves lam) point (χ ++ [y]) := by
    rw [evaluateCoefficients_getD _ p hlen, hp, evalCoeffs_partial,
      partialPolynomial_eval μ m ρ leaves lam point χ (by omega) y]
  have hdecode : decode (2 ^ ρ) (point.getD χ.length 0)
      (weightedPartial m (cofactor μ m ρ leaves lam) point χ)
      (honestMessage μ m ρ leaves lam point χ) = fun j ↦ p.getD j.val 0 := by
    have hsum := weightedPartial_snoc m n (cofactor μ m ρ leaves lam) point χ hχ
    rw [← heval 0, ← heval 1, evaluateCoefficients_zero, evaluateCoefficients_one] at hsum
    funext j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · rw [decode_zero, hsum]
      simp only [honestMessage, Fin.val_zero, Fin.val_succ, ← hp]
      ring
    · exact decode_succ _ _ _ _ k
  rw [evaluate, hdecode, heval]

/-- The verifier's coins of the descent: per layer its combiner, its round challenges and its child
coordinates. -/
def Coins : List ℕ → ℕ → Type
  | [], _ => PUnit
  | ρ :: rest, m => E × (Fin m → E) × (Fin ρ → E) × Coins rest (m + ρ)

variable (μ : ℕ) (leaves : Fin 3 → ℕ → E)

/-- The honest normalized rounds, then the continuation at the full prefix. -/
def honestRounds (m ρ : ℕ) (lam : E) (point : List E) (tail : Protocol)
    (after : List E → tail.tree.ExecutionPath) :
    (n : ℕ) → List E → (Fin n → E) → (roundsProtocol (2 ^ ρ) tail n).tree.ExecutionPath
  | 0, χ, _ => after χ
  | n + 1, χ, rs => ⟨honestMessage μ m ρ leaves lam point χ, some (rs 0),
      honestRounds m ρ lam point tail after n (χ ++ [rs 0]) (Fin.tail rs)⟩

/-- The child coordinates, then the continuation at the full child point. -/
def honestInterpolation (tail : Protocol) (after : List E → tail.tree.ExecutionPath) :
    (n : ℕ) → List E → (Fin n → E) → (interpolationProtocol tail n).tree.ExecutionPath
  | 0, u, _ => after u
  | n + 1, u, us => ⟨us 0, honestInterpolation tail after n (u ++ [us 0]) (Fin.tail us)⟩

/-- The honest child values at a full sumcheck prefix. -/
def honestChildren (m ρ : ℕ) (χ : List E) : Fin 3 → Fin (2 ^ ρ) → E :=
  fun s a ↦ childValue μ m ρ leaves s a.val χ

/-- The honest descent from a layer claim, then the terminal protocol at the final claim. -/
def honestPath (tail : Protocol) (tailPath : Claim → tail.tree.ExecutionPath) :
    (steps : List ℕ) → (m : ℕ) → Claim → Coins steps m → (protocol tail steps m).tree.ExecutionPath
  | [], _, c, _ => tailPath c
  | ρ :: rest, m, c, ⟨lam, rs, us, coins⟩ =>
      ⟨lam, honestRounds μ leaves m ρ lam c.point
        (.public .sender (Fin 3 → Fin (2 ^ ρ) → E) fun _ ↦ interpolationProtocol (protocol tail rest (m + ρ)) ρ)
        (fun χ ↦ ⟨honestChildren μ leaves m ρ χ,
          honestInterpolation (protocol tail rest (m + ρ))
            (fun u ↦ honestPath tail tailPath rest (m + ρ)
              ⟨u ++ χ, fun s ↦ interpolated ρ (honestChildren μ leaves m ρ χ) u s 0⟩ coins) ρ [] us⟩)
        m [] rs⟩

/-- Honest rounds parse to the full prefix and the true partial sum, keeping the flag. -/
theorem roundsResult_honest (m ρ : ℕ) (lam : E) (point : List E) (tail : Protocol)
    (after : List E → tail.tree.ExecutionPath) (n : ℕ) (χ : List E) (rs : Fin n → E) (active : Bool)
    (hχ : χ.length + n = m) :
    roundsResult (2 ^ ρ) point tail n χ (weightedPartial m (cofactor μ m ρ leaves lam) point χ) active
        (honestRounds μ leaves m ρ lam point tail after n χ rs) =
      some (χ ++ List.ofFn rs, weightedPartial m (cofactor μ m ρ leaves lam) point (χ ++ List.ofFn rs),
        active, after (χ ++ List.ofFn rs)) := by
  induction n generalizing χ active with
  | zero => simp only [roundsResult, honestRounds, List.ofFn_zero, List.append_nil]
  | succ n ih =>
    simp only [roundsResult, honestRounds]
    rw [honestMessage_evaluate μ m ρ n leaves lam point χ (by omega) (rs 0)]
    rw [ih (χ ++ [rs 0]) (Fin.tail rs) _ (by simp only [List.length_append, List.length_singleton]; omega)]
    simp only [check_eq_true, Bool.and_true, List.ofFn_succ, List.append_assoc, List.singleton_append]
    rfl

/-- Honest child coordinates parse to the interpolated claim at the full child point. -/
theorem interpolationResult_honest (ρ : ℕ) (χ : List E) (children : Fin 3 → Fin (2 ^ ρ) → E)
    (tail : Protocol) (after : List E → tail.tree.ExecutionPath) (n : ℕ) (u : List E)
    (us : Fin n → E) :
    interpolationResult ρ χ children tail n u (honestInterpolation tail after n u us) =
      (⟨(u ++ List.ofFn us) ++ χ, fun s ↦ interpolated ρ children (u ++ List.ofFn us) s 0⟩,
        after (u ++ List.ofFn us)) := by
  induction n generalizing u with
  | zero => simp only [interpolationResult, honestInterpolation, List.ofFn_zero, List.append_nil]
  | succ n ih =>
    simp only [interpolationResult, honestInterpolation]
    rw [ih]
    simp only [List.ofFn_succ, List.append_assoc, List.singleton_append]
    rfl

/-- The honest children's interpolation is the next layer's true claim. -/
theorem honest_next_holds (m ρ : ℕ) (χ u : List E) (hχ : χ.length = m) (hu : u.length = ρ) :
    (⟨u ++ χ, fun s ↦ interpolated ρ (honestChildren μ leaves m ρ χ) u s 0⟩ : Claim).Holds μ (m + ρ)
      leaves := by
  refine ⟨by simp only [List.length_append, hχ, hu]; omega, fun s ↦ ?_⟩
  show interpolated ρ (honestChildren μ leaves m ρ χ) u s 0 = mle (m + ρ) (level μ (m + ρ) leaves s) (u ++ χ)
  rw [childValue_interpolation μ m ρ leaves s χ u hχ hu]
  unfold interpolated
  apply mle_congr_values
  intro i hi
  simp only [honestChildren, Nat.mul_zero, Nat.add_zero]
  rw [Nat.mod_eq_of_lt (by rw [← hu]; exact hi)]

/-- Completeness of the descent: from a true layer claim, against every coin sequence, the honest
transcript parses to a true final claim with every check passed. -/
theorem result_honest (tail : Protocol) (tailPath : Claim → tail.tree.ExecutionPath)
    (steps : List ℕ) (m : ℕ) (c : Claim) (coins : Coins steps m)
    (hdepth : m + steps.sum = μ) (hc : c.Holds μ m leaves) :
    ∃ c', c'.Holds μ μ leaves ∧
      result tail steps m c true (honestPath μ leaves tail tailPath steps m c coins) =
        some (c', true, tailPath c') := by
  induction steps generalizing m c with
  | nil =>
    simp only [List.sum_nil, Nat.add_zero] at hdepth
    subst hdepth
    exact ⟨c, hc, rfl⟩
  | cons ρ rest ih =>
    obtain ⟨lam, rs, us, coins⟩ := coins
    simp only [List.sum_cons] at hdepth
    have hinit : batch lam c.values = weightedPartial m (cofactor μ m ρ leaves lam) c.point [] := by
      rw [weightedPartial_initial μ m ρ leaves lam c.point (by omega)]
      apply congrArg (batch lam)
      funext s
      exact hc.2 s
    have hrounds := roundsResult_honest μ leaves m ρ lam c.point
        (.public .sender (Fin 3 → Fin (2 ^ ρ) → E) fun _ ↦ interpolationProtocol (protocol tail rest (m + ρ)) ρ)
        (fun χ ↦ ⟨honestChildren μ leaves m ρ χ,
          honestInterpolation (protocol tail rest (m + ρ))
            (fun u ↦ honestPath μ leaves tail tailPath rest (m + ρ)
              ⟨u ++ χ, fun s ↦ interpolated ρ (honestChildren μ leaves m ρ χ) u s 0⟩ coins) ρ [] us⟩)
        m [] rs true (by simp only [List.length_nil, Nat.zero_add])
    simp only [List.nil_append] at hrounds
    have hlen : (List.ofFn rs).length = m := List.length_ofFn
    have hfull : weightedPartial m (cofactor μ m ρ leaves lam) c.point (List.ofFn rs) =
        ∑ s : Fin 3, lam ^ s.val * ∏ a : Fin (2 ^ ρ), honestChildren μ leaves m ρ (List.ofFn rs) s a := by
      rw [weightedPartial_full m _ c.point _ hlen]
      rfl
    have hnext := honest_next_holds μ leaves m ρ (List.ofFn rs) (List.ofFn us) hlen List.length_ofFn
    obtain ⟨c', hc', hres⟩ := ih (m + ρ) _ coins (by omega) hnext
    refine ⟨c', hc', ?_⟩
    unfold result
    change Option.bind (roundsResult (2 ^ ρ) c.point
      (.public .sender (Fin 3 → Fin (2 ^ ρ) → E) fun _ ↦
        interpolationProtocol (protocol tail rest (m + ρ)) ρ)
      m [] (batch lam c.values) true (honestRounds μ leaves m ρ lam c.point
        (.public .sender (Fin 3 → Fin (2 ^ ρ) → E) fun _ ↦ interpolationProtocol (protocol tail rest (m + ρ)) ρ)
        (fun χ ↦ ⟨honestChildren μ leaves m ρ χ,
          honestInterpolation (protocol tail rest (m + ρ))
            (fun u ↦ honestPath μ leaves tail tailPath rest (m + ρ)
              ⟨u ++ χ, fun s ↦ interpolated ρ (honestChildren μ leaves m ρ χ) u s 0⟩ coins) ρ [] us⟩)
        m [] rs)) _ = _
    rw [hinit, hrounds, Option.bind_some]
    change result tail rest (m + ρ)
      (interpolationResult ρ (List.ofFn rs) (honestChildren μ leaves m ρ (List.ofFn rs))
        (protocol tail rest (m + ρ)) ρ []
        (honestInterpolation (protocol tail rest (m + ρ))
          (fun u ↦ honestPath μ leaves tail tailPath rest (m + ρ)
            ⟨u ++ List.ofFn rs, fun s ↦ interpolated ρ (honestChildren μ leaves m ρ (List.ofFn rs)) u s 0⟩
              coins) ρ [] us)).1
      (true && decide (weightedPartial m (cofactor μ m ρ leaves lam) c.point (List.ofFn rs) =
        ∑ s : Fin 3, lam ^ s.val * ∏ a : Fin (2 ^ ρ), honestChildren μ leaves m ρ (List.ofFn rs) s a))
      (interpolationResult ρ (List.ofFn rs) (honestChildren μ leaves m ρ (List.ofFn rs))
        (protocol tail rest (m + ρ)) ρ []
        (honestInterpolation (protocol tail rest (m + ρ))
          (fun u ↦ honestPath μ leaves tail tailPath rest (m + ρ)
            ⟨u ++ List.ofFn rs, fun s ↦ interpolated ρ (honestChildren μ leaves m ρ (List.ofFn rs)) u s 0⟩
              coins) ρ [] us)).2 = _
    rw [interpolationResult_honest, hfull]
    simpa only [List.nil_append, decide_true, Bool.and_self] using hres

end CompStark.Multilinear.GrandProduct
