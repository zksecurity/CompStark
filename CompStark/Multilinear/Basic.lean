/-
Copyright (c) 2026 zkSecurity.
Adapted from Verified-zkEVM/leanerVM (Apache-2.0), revision a9d42bfdae8081a4e16aef1cd8526cdaa2a8f4d6:
LeanerVM.Protocol.Fingerprint, Bus, BusSecurity, and TableSumcheck.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.BinaryFields.WordProduct
public import ArkLib.Data.MvPolynomial.Multilinear
public import CompStark.Multilinear.Algebra.GrandProduct
public import ArkLib.ProofSystem.Sumcheck.Interaction.Knowledge

/-! The challenge field's sampling and error unit, and low-bit-first multilinear extensions of tables over it with their word-level evaluators. -/

@[expose] public section

namespace CompStark.Multilinear

open CompStark.BinaryFields
open OracleComp

noncomputable section

/-- Proof-only finite enumeration of the extension field. -/
instance : Fintype E := Fintype.ofFinite E

/-- Uniform extension-field challenges, independent at each authored verifier prefix. -/
instance : SampleableType E := SampleableType.ofFintype E

/-- An error numerator divided by the cardinality of the extension field. -/
def overE (n : ℕ) : ENNReal := (n : ENNReal) / Fintype.card E

/-- Error numerators add over the common challenge field. -/
theorem overE_add (a b : ℕ) : overE (a + b) = overE a + overE b := by
  simp only [overE, Nat.cast_add, ENNReal.add_div]

/-- A zero error numerator contributes no probability. -/
theorem overE_zero : overE 0 = 0 := by simp only [overE, Nat.cast_zero, ENNReal.zero_div]

/-- Equality-kernel factor on two field coordinates. -/
def eqFactor (a b : E) : E := (1 - a) * (1 - b) + a * b

/-- Low-bit-first Boolean coordinate of an integer. -/
def bit (i k : ℕ) : E := if i.testBit k then 1 else 0

/-- Multilinear extension in low-bit-first order; points are stored in coordinate order. -/
def mle (n : ℕ) (values : ℕ → E) (z : List E) : E :=
  ∑ i : Fin (2 ^ n), values i.val * ∏ k : Fin n, eqFactor (z.getD k.val 0) (bit i.val k.val)

/-- The list-point extension agrees with CompPoly's low-bit-first evaluator. -/
theorem mle_eq_evalMle (n : ℕ) (values : ℕ → E) (z : List E) :
    mle n values z = CompPoly.CMlPolynomialEval.evalMle
      (Vector.ofFn fun i : Fin (2 ^ n) ↦ values i.val)
      (Vector.ofFn fun k : Fin n ↦ z.getD k.val 0) := by
  rw [mle, Algebra.evalMle_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  rw [Algebra.lagrangeBasis_getElem_nat]
  apply congrArg (fun v : E ↦ values i.val * v)
  apply Finset.prod_congr rfl
  intro k _
  dsimp only [eqFactor, bit]
  split <;> simp only [Fin.getElem_fin, Vector.getElem_ofFn, sub_zero, sub_self,
    mul_one, mul_zero, zero_add, add_zero]

/-- Array folding evaluates a list-point multilinear extension without enumerating its basis products. -/
def mleFast (n : ℕ) (values : ℕ → E) (z : List E) : E :=
  CompPoly.CMlPolynomialEval.evalMle
    (Vector.ofFn fun i : Fin (2 ^ n) ↦ values i.val)
    (Vector.ofFn fun k : Fin n ↦ z.getD k.val 0)

/-- Compiled list-point evaluation uses the exactly equal folding evaluator. -/
@[csimp] theorem mle_code : mle = mleFast := by
  funext n values z
  exact mle_eq_evalMle n values z

/-- Boolean evaluation reads the indexed committed value. -/
theorem mle_bits (n : ℕ) (values : ℕ → E) (i : Fin (2 ^ n)) :
    mle n values (List.ofFn fun k : Fin n ↦ bit i.val k.val) = values i.val := by
  rw [mle_eq_evalMle]
  have hp : (Vector.ofFn fun k : Fin n ↦
      (List.ofFn fun j : Fin n ↦ bit i.val j.val).getD k.val 0) = Algebra.boolVec i := by
    apply Vector.ext
    intro k hk
    simp only [Vector.getElem_ofFn, Algebra.boolVec]
    erw [List.getD_eq_getElem _ 0 (by simpa only [List.length_ofFn] using hk), List.getElem_ofFn]
    rfl
  rw [hp, Algebra.evalMle_boolVec]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]

/-- Extension values depend only on the coordinates used by the table. -/
theorem mle_congr (n : ℕ) (values : ℕ → E) (z z' : List E)
    (h : ∀ k < n, z.getD k 0 = z'.getD k 0) : mle n values z = mle n values z' := by
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun x : E ↦ values i.val * x)
  exact Finset.prod_congr rfl fun k _ ↦ congrArg (fun x ↦ eqFactor x (bit i.val k.val)) (h k k.isLt)

/-- Extensions agree when their values agree on the cube. -/
theorem mle_congr_values (n : ℕ) (f g : ℕ → E) (z : List E) (h : ∀ i < 2 ^ n, f i = g i) :
    mle n f z = mle n g z := by
  unfold mle
  exact Finset.sum_congr rfl fun i _ ↦ by rw [h i i.isLt]

/-- List coordinates of a vector recover its multilinear evaluation. -/
theorem mle_toList (n : ℕ) (values : ℕ → E) (z : Vector E n) :
    mle n values z.toList = CompPoly.CMlPolynomialEval.evalMle
      (Vector.ofFn fun i : Fin (2 ^ n) ↦ values i.val) z := by
  rw [mle_eq_evalMle]
  congr 1
  apply Vector.ext
  intro k hk
  simp only [Vector.getElem_ofFn, List.getD, Vector.getElem_toList, List.getElem?_eq_getElem,
    Vector.length_toList, hk, Option.getD_some]

/-- Multilinear extension is affine in each used coordinate. -/
theorem mle_set (n : ℕ) (values : ℕ → E) (z : List E) (hz : z.length = n)
    (k : ℕ) (hk : k < n) (r : E) :
    mle n values (z.set k r) =
      (1 - r) * mle n values (z.set k 0) + r * mle n values (z.set k 1) := by
  let v : Vector E n := ⟨z.toArray, by simpa only [List.size_toArray] using hz⟩
  have hv : v.toList = z := by simp only [v, Vector.toList_mk]
  have hs (a : E) : (v.set k a).toList = z.set k a := by
    simp only [Vector.toList_set, hv]
  rw [← hs r, ← hs 0, ← hs 1, mle_toList, mle_toList, mle_toList]
  exact Algebra.evalMle_set _ v hk r

/-- Appending one coordinate interpolates the two contiguous halves of the table. -/
theorem mle_snoc (values : ℕ → E) (u : List E) (r : E) :
    mle (u.length + 1) values (u ++ [r]) =
      (1 - r) * mle u.length values u +
        r * mle u.length (fun i ↦ values (i + 2 ^ u.length)) u := by
  let v : Vector E u.length := ⟨u.toArray, by simp only [List.size_toArray]⟩
  have hv : v.toList = u := by simp only [v, Vector.toList_mk]
  have hpoint : (v ++ #v[r]).toList = u ++ [r] := by
    simp only [Vector.toList_append, hv, Vector.toList_mk]
  let T := Vector.ofFn fun i : Fin (2 ^ (u.length + 1)) ↦ values i.val
  have hs (j : Fin (2 ^ 1)) : Algebra.slice T j =
      Vector.ofFn (fun i : Fin (2 ^ u.length) ↦ values (i.val + 2 ^ u.length * j.val)) := by
    apply Vector.ext
    intro k hk
    simp only [Algebra.slice, T, Fin.getElem_fin, Vector.getElem_ofFn, Algebra.cubeIndex]
  have he (j : Fin (2 ^ 1)) : CompPoly.CMlPolynomialEval.evalMle (Algebra.slice T j) v =
      mle u.length (fun i ↦ values (i + 2 ^ u.length * j.val)) u := by
    rw [hs]
    exact (mle_toList u.length (fun i ↦ values (i + 2 ^ u.length * j.val)) v).symm.trans
      (congrArg (mle u.length _) hv)
  have hw0 : (CompPoly.CMlPolynomialEval.lagrangeBasis #v[r])[(0 : Fin 2)] = 1 - r := by
    simp only [Fin.getElem_fin]
    rw [Algebra.lagrangeBasis_getElem_nat]
    simp only [Fin.prod_univ_one]
    rfl
  have hw1 : (CompPoly.CMlPolynomialEval.lagrangeBasis #v[r])[(1 : Fin 2)] = r := by
    simp only [Fin.getElem_fin]
    rw [Algebra.lagrangeBasis_getElem_nat]
    simp only [Fin.prod_univ_one]
    rfl
  rw [← hpoint, mle_toList, Algebra.evalMle_split]
  change (∑ j : Fin 2, (CompPoly.CMlPolynomialEval.lagrangeBasis #v[r])[j] *
    CompPoly.CMlPolynomialEval.evalMle (Algebra.slice T j) v) = _
  rw [Fin.sum_univ_two, he, he, hw0, hw1]
  simp only [Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.mul_one, Nat.add_zero]

/-- Materializing the used coordinates preserves the exact extension. -/
theorem mle_ofFn_point (n : Nat) (values : Nat → E) (point : List E) :
    mle n values (List.ofFn fun k : Fin n => point.getD k.val 0) = mle n values point := by
  apply mle_congr
  intro k bound
  rw [List.getD_eq_getElem _ 0 (by simpa only [List.length_ofFn] using bound), List.getElem_ofFn]
/-- The last used coordinate interpolates the two contiguous table halves. -/
theorem mle_succ_last (n : Nat) (values : Nat → E) (point : List E) :
    mle (n+1) values point =
      (1-point.getD n 0) * mle n values point +
        point.getD n 0 * mle n (fun i => values (i+2^n)) point := by
  rw [← mle_ofFn_point (n+1) values point, List.ofFn_succ']
  rw [List.concat_eq_append]
  simp only [Fin.val_castSucc, Fin.val_last]
  have split := mle_snoc values (List.ofFn fun k : Fin n => point.getD k.val 0) (point.getD n 0)
  simpa only [List.length_ofFn, mle_ofFn_point] using split

/-- Prune Boolean coordinates while retaining interpolation arithmetic in the word carrier. -/
def mlePrunedWord : (n : Nat) → (Nat → E) → List E → BF64.WordExt3
  | 0, values, _ => BF64.WordExt3.ofField (values 0)
  | n+1, values, point =>
    let r := BF64.WordExt3.ofField (point.getD n 0)
    if r = 0 then mlePrunedWord n values point
    else if r = 1 then mlePrunedWord n (fun i => values (i+2^n)) point
    else
      let low := mlePrunedWord n values point
      let high := mlePrunedWord n (fun i => values (i+2^n)) point
      low + r * (high-low)
/-- Pruned word interpolation evaluates the exact multilinear extension at every point. -/
theorem mlePrunedWord_eq (n : Nat) (values : Nat → E) (point : List E) :
    (mlePrunedWord n values point).toField = mle n values point := by
  induction n generalizing values with
  | zero =>
    simp only [mlePrunedWord, BF64.WordExt3.toField_ofField, mle, Fin.prod_univ_zero, mul_one]
    change values 0 = ∑ i : Fin 1, values i.val
    rw [Fin.sum_univ_one]
    rfl
  | succ n ih =>
    rw [mlePrunedWord]
    dsimp only
    split_ifs with zero one
    · have hz : point.getD n 0 = 0 := by
        simpa only [BF64.WordExt3.toField_ofField, show BF64.WordExt3.toField 0 = 0 from rfl] using
          congrArg BF64.WordExt3.toField zero
      rw [ih, mle_succ_last, hz]
      simp only [sub_zero, one_mul, zero_mul, add_zero]
    · have ho : point.getD n 0 = 1 := by
        simpa only [BF64.WordExt3.toField_ofField, show BF64.WordExt3.toField 1 = 1 from rfl] using
          congrArg BF64.WordExt3.toField one
      rw [ih, mle_succ_last, ho]
      simp only [sub_self, zero_mul, one_mul, zero_add]
    · change BF64.WordExt3.ringEquiv (_ + _ * (_-_)) = _
      rw [map_add, map_mul, map_sub]
      change (mlePrunedWord n values point).toField +
        (BF64.WordExt3.ofField (point.getD n 0)).toField *
          ((mlePrunedWord n (fun i => values (i+2^n)) point).toField -
            (mlePrunedWord n values point).toField) = _
      rw [BF64.WordExt3.toField_ofField, ih, ih, mle_succ_last]
      ring

/-- Evaluate only the table slices selected by Boolean coordinates. -/
def mleSparse (n : Nat) (values : Nat → E) (point : List E) : E :=
  (mlePrunedWord n values point).toField

/-- Compiled list-point evaluation prunes Boolean slices and retains word interpolation. -/
@[csimp] theorem mleFast_code : mleFast = mleSparse := by
  funext n values point
  rw [← mle_code]
  exact (mlePrunedWord_eq n values point).symm

end
end CompStark.Multilinear
