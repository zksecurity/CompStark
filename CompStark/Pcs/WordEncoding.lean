/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.Evaluated

/-! Shared word subspace recurrences for additive-domain query weights. -/

set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 30000

@[expose] public section
namespace CompStark.Pcs
open CompStark.BinaryFields BF64

/-- Tensor factors whose preparation and scalar evaluations retain the word carrier. -/
def EvaluatedWeight.wordFactors {n : Nat} (factors : Vector (WordExt3 × WordExt3) n) :
    EvaluatedWeight n :=
  { table := fun u => ∏ i, if u i then (factors[i].2).toField else (factors[i].1).toField
    wordEvaluate := fun point => ∏ i, (factors[i].1 + sparseProduct (point i) (factors[i].2-factors[i].1))
    wordEvaluate_eq := fun point => by
      change WordExt3.ringEquiv _ = _
      simp only [map_prod, map_add, sparseProduct_eq, map_mul, map_sub]
      simp only [show ∀ w, WordExt3.ringEquiv w = WordExt3.toField w from fun _ => rfl]
      rw [mle_factors (fun i => ((factors[i].1).toField, (factors[i].2).toField))]
      apply Finset.prod_congr rfl
      intro i _
      change _ = (1 - (point i).toField) * _ + (point i).toField * _
      ring }

/-- Advance the unnormalized binary subspace recurrence through a fixed number of stages. -/
def recurrence (constants : Nat → Word) (x : Word) : Nat → Word
  | 0 => x
  | n+1 => let a := recurrence constants x n; a * (a + constants n)
termination_by structural n => n

/-- Materialize every prefix of one subspace recurrence, sharing the preceding word. -/
def recurrenceTower (constants : Nat → Word) (x : Word) : (n : Nat) → Vector Word (n+1)
  | 0 => #v[x]
  | n+1 =>
    let previous := recurrenceTower constants x n
    previous.push (previous[n] * (previous[n] + constants n))
termination_by structural n => n

/-- A shared recurrence prefix equals independent evaluation at its index. -/
theorem recurrenceTower_get (constants : Nat → Word) (x : Word) (n : Nat) (i : Fin (n+1)) :
    (recurrenceTower constants x n)[i] = recurrence constants x i.val := by
  induction n with
  | zero =>
    have hi : i.val = 0 := by omega
    simp only [Fin.getElem_fin, hi, recurrenceTower.eq_1, recurrence.eq_1]
    rfl
  | succ n ih =>
    by_cases low : i.val < n+1
    · simp only [Fin.getElem_fin]
      rw [recurrenceTower.eq_2, Vector.getElem_push_lt low]
      exact ih ⟨i.val,low⟩
    · have last : i.val = n+1 := by omega
      simp only [Fin.getElem_fin, last, recurrenceTower.eq_2, Vector.getElem_push_eq, recurrence.eq_2]
      rw [show (recurrenceTower constants x n)[n] = recurrence constants x n from ih ⟨n,by omega⟩]

/-- A normalized stage retains its subspace constant and denominator inverse as words. -/
def queryStage (i : Fin 64) : Word × Word :=
  let plan := normalizedFactorPlan i
  (Word.ofField (AdditiveNTT.evalWAtCachedConstants plan.1 (basis i)), Word.ofField plan.2)

/-- The prepared recurrence constant is the exact subspace polynomial at its basis vector. -/
theorem queryStage_constant (i : Fin 64) :
    (queryStage i).1.toField = (AdditiveNTT.W (ZMod 2) basis i).eval (basis i) := by
  simp only [queryStage, normalizedFactorPlan, Word.toField_ofField]
  exact AdditiveNTT.evalWAtCachedConstants_subspacePolynomialConstantsArray_eq_W
    (𝔽q := ZMod 2) (β := basis) (ℓ := 0) (R_rate := 0) i (basis i)

/-- Correct prefix constants make the word recurrence equal the mathematical subspace value. -/
theorem recurrence_eq (constants : Nat → Word) (x : K) (i : Fin 64)
    (correct : ∀ k, (hk : k < i.val) → (constants k).toField =
      (AdditiveNTT.W (ZMod 2) basis ⟨k,by omega⟩).eval (basis ⟨k,by omega⟩)) :
    (recurrence constants (Word.ofField x) i.val).toField =
      (AdditiveNTT.W (ZMod 2) basis i).eval x := by
  obtain ⟨i,hi⟩ := i
  change ∀ k, (hk : k < i) → _ at correct
  induction i with
  | zero =>
    change (Word.ofField x).toField = (AdditiveNTT.W (ZMod 2) basis 0).eval x
    rw [Word.toField_ofField, AdditiveNTT.W₀_eq_X, Polynomial.eval_X]
  | succ i ih =>
    change Word.ringEquiv (_ * _) = _
    rw [map_mul, map_add]
    change (recurrence constants (Word.ofField x) i).toField *
      ((recurrence constants (Word.ofField x) i).toField + (constants i).toField) = _
    rw [ih (by omega) (by intro k hk; exact correct k (by omega)), correct i (by omega)]
    have next : (⟨i,by omega⟩ : Fin 64) + 1 = ⟨i+1,hi⟩ := by
      ext
      exact Fin.val_add_one' (h_a_add_1 := hi)
    simpa only [next] using
      (AdditiveNTT.W_eval_succ_eq_mul_add (𝔽q := ZMod 2) (β := basis)
        (i := ⟨i,by omega⟩) (h_i_add_1 := by omega) (x := x)).symm

/-- Decode an additive-domain index with its certified flat basis words. -/
def queryDomain {dim : Nat} (h : dim ≤ 64) (column : Fin (2^dim)) : K :=
  ∑ i : Fin dim, if column.val.testBit i.val then basisWord (Fin.castLE h i) else 0

/-- The word-domain sum is the encoder's exact ordered additive point. -/
theorem queryDomain_eq {dim : Nat} (h : dim ≤ 64) (column : Fin (2^dim)) :
    queryDomain h column = domain h column := by
  simp only [queryDomain, ← basis_word]
  rfl

/-- Query encoders share one word recurrence tower across all normalized coordinates. -/
def evaluatedEncoding (vars rate : Nat) (h : vars+rate ≤ 64) : EvaluatedEncoding vars :=
  let stages := Vector.ofFn fun i : Fin vars => queryStage ⟨i.val,by omega⟩
  let constants := fun j => ((stages.toArray[j]?).getD (0,0)).1
  { encoding := encoding vars rate h
    query := fun column =>
      let raw := recurrenceTower constants (Word.ofField (queryDomain h column)) vars
      .wordFactors (Vector.ofFn fun i : Fin vars =>
        (1, ⟨raw[i.val] * stages[i].2, 0, 0⟩))
    query_table := fun column => by
      funext u
      simp only [EvaluatedWeight.wordFactors, Fin.getElem_fin, Vector.getElem_ofFn, queryDomain_eq]
      change (∏ i : Fin vars, if u i then
        WordExt3.toField ⟨(recurrenceTower constants (Word.ofField (domain h column)) vars)[i.val] *
          stages[i].2, 0, 0⟩ else WordExt3.toField 1) =
        (algebraMap K E) (∏ i : Fin vars, if u i then
          Whir.normalizedSubspaceValue basis ⟨i.val,by omega⟩ (domain h column) else 1)
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro i _
      split_ifs
      · have embed (a : Word) : WordExt3.toField ⟨a,0,0⟩ = ofK a.toField := by
          rw [ofK_eq_ofLimbs]
          rfl
        have rawLaw := recurrenceTower_get constants (Word.ofField (domain h column)) vars ⟨i.val,by omega⟩
        simp only [Fin.getElem_fin] at rawLaw
        rw [embed, rawLaw]
        have stageLaw : stages[i].2 = (queryStage ⟨i.val,by omega⟩).2 := by
          simp only [stages, Fin.getElem_fin, Vector.getElem_ofFn]
        rw [stageLaw]
        change ofK (Word.ringEquiv (_ * _)) = _
        rw [map_mul]
        change ofK ((recurrence constants (Word.ofField (domain h column)) i.val).toField *
          (queryStage ⟨i.val,by omega⟩).2.toField) = _
        rw [recurrence_eq constants _ ⟨i.val,by omega⟩ (by
          intro k hk
          change k < i.val at hk
          have inside : k < vars := by omega
          have sized : k < stages.toArray.size := by simpa only [Vector.size_toArray] using inside
          change (stages.toArray[k]?.getD (0,0)).1.toField = _
          rw [Array.getElem?_eq_getElem sized]
          simp only [Option.getD_some, Vector.getElem_toArray, stages, Vector.getElem_ofFn]
          exact queryStage_constant ⟨k,by omega⟩)]
        simp only [queryStage, normalizedFactorPlan, Word.toField_ofField]
        rw [← AdditiveNTT.evalWAtCachedConstants_subspacePolynomialConstantsArray_eq_W
          (𝔽q := ZMod 2) (β := basis) (ℓ := 0) (R_rate := 0) ⟨i.val,by omega⟩]
        rw [← div_eq_mul_inv]
        exact congrArg ofK (normalizedValueFast_eq ⟨i.val,by omega⟩ (domain h column))
      · rfl }

/-- Shared query towers retain the exact normalized-novel weight and its word evaluator. -/
theorem evaluatedEncoding_encoding (vars rate : Nat) (h : vars+rate ≤ 64) :
    (evaluatedEncoding vars rate h).encoding = encoding vars rate h := rfl

end CompStark.Pcs
