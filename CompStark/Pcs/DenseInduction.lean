/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Algorithms derived from succinctlabs/flock (flock-core), MIT OR Apache-2.0.
Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum.
Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang.
-/
module
public import CompStark.Pcs.Induction
public import CompPoly.Fields.Binary.AdditiveNTT.Correctness

/-! Split novel-basis query tensors for dense induction. -/
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
@[expose] public section
namespace CompStark.Pcs
open BF64 AdditiveNTT

noncomputable local instance : Fintype Word := Fintype.ofFinite Word

/-- The native binary-domain point selected by a numeric query. -/
def inductionPoint {d : Nat} (hd : d < 64) (q : Fin (2^d)) : Word :=
  ∑ k : Fin d, if Nat.getBit k.val q.val = 1 then Packed.flatBasis ⟨k.val, by omega⟩ else 0

/-- Cached subspace constants and normalization inverses for every message bit. -/
def inductionConstants (ell : Nat) (h : ell < 64) : Vector (Array Word × Word) ell :=
  Vector.ofFn fun i =>
    let constants := subspacePolynomialConstantsArray (ℓ := 0) (R_rate := 0)
      Packed.flatBasis ⟨i.val, by omega⟩
    (constants, (evalWAtCachedConstants constants (Packed.flatBasis ⟨i.val, by omega⟩))⁻¹)

/-- Each query's normalized subspace-polynomial factors, shared by its two tensors. -/
def inductionFactors {ell d : Nat} (_hell : ell < 64) (hd : d < 64)
    (constants : Vector (Array Word × Word) ell) (q : Fin (2^d)) : Vector Word ell :=
  let x := inductionPoint hd q
  constants.map fun c => evalWAtCachedConstants c.1 x * c.2

/-- A tensor of binary monomials, extending only its newly occupied half at each bit. -/
def novelTensor : (n : Nat) → Vector Word n → Vector Word (2^n)
  | 0, _ => #v[1]
  | n+1, factors =>
    let tail := novelTensor n (Vector.ofFn fun i => factors[i.val+1])
    Vector.ofFn fun i =>
      let a := tail[i.val/2]'(by have := i.isLt; simp only [pow_succ] at this; omega)
      if i.val%2 = 0 then a else a*factors[0]

/-- Tensor lookup is the product of exactly the factors selected by the coefficient's bits. -/
theorem novelTensor_get (n : Nat) (factors : Vector Word n) (i : Fin (2^n)) :
    (novelTensor n factors)[i] = ∏ k : Fin n, factors[k]^(Nat.getBit k.val i.val) := by
  induction n with
  | zero =>
    have : i = 0 := Fin.eq_zero i
    subst i
    rfl
  | succ n ih =>
    let tailIndex : Fin (2^n) := ⟨i.val/2, by have := i.isLt; simp only [pow_succ] at this; omega⟩
    rw [novelTensor]
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    change (if i.val%2 = 0 then (novelTensor n (Vector.ofFn fun j => factors[j.val+1]))[tailIndex]
      else (novelTensor n (Vector.ofFn fun j => factors[j.val+1]))[tailIndex]*factors[0]) = _
    rw [ih, Fin.prod_univ_succ]
    have bits (k : Fin n) : Nat.getBit (k.val+1) i.val = Nat.getBit k.val (i.val/2) := by
      simpa only [Nat.add_sub_cancel] using
        (Nat.getBit_eq_pred_getBit_of_div_two (n := i.val) (k := k.val+1) (by omega))
    simp only [Vector.getElem_ofFn, Fin.getElem_fin, Fin.val_zero, Fin.val_succ, bits, tailIndex]
    have low : Nat.getBit 0 i.val = i.val%2 := by
      simp only [Nat.getBit, Nat.shiftRight_zero, Nat.and_one_is_mod]
    rw [low]
    split
    · rename_i even
      simp only [even, pow_zero, one_mul]
    · rename_i odd
      have : i.val%2 = 1 := by omega
      rw [this, pow_one]
      exact mul_comm _ _

/-- Natural-index lookup of the cached binary monomial tensor. -/
theorem novelTensor_getNat (n : Nat) (factors : Vector Word n) (i : Nat) (bound : i < 2^n) :
    (novelTensor n factors)[i] = ∏ k : Fin n, factors[k]^(Nat.getBit k.val i) :=
  novelTensor_get n factors ⟨i, bound⟩

/-- The executable point is the generic additive encoder's evaluation point. -/
theorem inductionPoint_eq {ell rate : Nat} (hd : ell+rate < 64)
    (q : Fin (2^(ell+rate))) :
    inductionPoint hd q = evaluationPointω (ZMod 2) Packed.flatBasis hd
      (i := 0) (by simp only [Fin.val_zero]; omega) q := by
  have normalized : normalizedW (ZMod 2) Packed.flatBasis (0 : Fin 64) = Polynomial.X := by
    rw [normalizedW₀_eq_1_div_β₀ (𝔽q := ZMod 2)]
    simp only [show Packed.flatBasis 0 = 1 from rfl, div_one, Polynomial.C_1, mul_one]
  unfold inductionPoint evaluationPointω
  simp only [Fin.val_zero, Nat.sub_zero, Nat.zero_add]
  simp only [show (⟨0, by omega⟩ : Fin 64) = 0 from rfl, normalized, Polynomial.eval_X]

/-- Normalized factor evaluation agrees with the mathematical subspace polynomials. -/
theorem inductionFactors_get {ell d : Nat} (hell : ell < 64) (hd : d < 64)
    (q : Fin (2^d)) (i : Fin ell) :
    (inductionFactors hell hd (inductionConstants ell hell) q)[i] =
      (normalizedW (ZMod 2) Packed.flatBasis ⟨i.val, by omega⟩).eval (inductionPoint hd q) := by
  simp only [inductionFactors, inductionConstants, Fin.getElem_fin,
    Vector.getElem_map, Vector.getElem_ofFn]
  rw [evalWAtCachedConstants_subspacePolynomialConstantsArray_eq_W (𝔽q := ZMod 2),
    evalWAtCachedConstants_subspacePolynomialConstantsArray_eq_W (𝔽q := ZMod 2)]
  rw [normalizedW, Polynomial.eval_mul, Polynomial.eval_C]
  simp only [one_div, mul_comm]

/-- The complete query tensor is exactly the novel basis evaluated at its domain point. -/
theorem queryTensor_eval {ell rate : Nat} (hd : ell+rate < 64)
    (q : Fin (2^(ell+rate))) (i : Fin (2^ell)) :
    (novelTensor ell (inductionFactors (by omega) hd (inductionConstants ell (by omega)) q))[i] =
      (Xⱼ (ZMod 2) Packed.flatBasis ell (by omega) i).eval (inductionPoint hd q) := by
  rw [novelTensor_get, Xⱼ, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro k _
  rw [Polynomial.eval_pow, inductionFactors_get]
  rfl

/-- Every encoded lane is the weighted sum of the query's native novel-basis tensor. -/
theorem encodeRows_query {ell rate : Nat} (hd : ell+rate < 64)
    (plan : Packed.FlatPlan (ell+rate) hd) (lanes : Nat)
    (message : BF64.Packed.Buffer (2^ell*lanes)) (c : Fin lanes)
    (q : Fin (2^(ell+rate))) :
    Packed.laneView (Packed.forward plan ell (by omega) lanes
      (Packed.tileRows ell rate lanes message)) c q =
      ∑ j : Fin (2^ell), Packed.laneView message c j *
        (novelTensor ell (inductionFactors (by omega) hd (inductionConstants ell (by omega)) q))[j] := by
  rw [Packed.laneView_encodeRows (F := ZMod 2), computableAdditiveNTT_eq_additiveNTT]
  rw [additiveNTT_correctness (ZMod 2) Packed.flatBasis hd (by omega) _ _ rfl q]
  change Polynomial.eval (evaluationPointω (ZMod 2) Packed.flatBasis hd 0 _ q) _ = _
  rw [← inductionPoint_eq hd q]
  simp only [polynomialFromNovelCoeffs, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, queryTensor_eval hd]

/-- Split a binary monomial tensor at an arbitrary bit boundary. -/
theorem novelTensor_split (lo hi : Nat) (factors : Vector Word (lo+hi))
    (i : Fin (2^(lo+hi))) :
    (novelTensor (lo+hi) factors)[i] =
      (novelTensor lo (Vector.ofFn fun k => factors[k.val]))[i.val%2^lo]'(Nat.mod_lt _ (Nat.two_pow_pos _)) *
      (novelTensor hi (Vector.ofFn fun k => factors[lo+k.val]'(by have := k.isLt; omega)))[i.val/2^lo]'(by
        have := i.isLt; simp only [pow_add] at this; exact Nat.div_lt_of_lt_mul this) := by
  simp only [Fin.getElem_fin, novelTensor_getNat]
  rw [Fin.prod_univ_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro k _
    simp only [Vector.getElem_ofFn, Fin.val_castAdd]
    rw [← Nat.getLowBits_eq_mod_two_pow, Nat.getBit_of_lowBits]
    simp only [k.isLt, ↓reduceIte]
  · apply Finset.prod_congr rfl
    intro k _
    simp only [Vector.getElem_ofFn, Fin.val_natAdd]
    rw [← Nat.shiftRight_eq_div_pow, Nat.getBit_of_shiftRight]
    simp only [Nat.add_comm]

/-- Reconstruct dense query weights from the two retained small matrices. -/
def splitDotRows (lo hi lanes count : Nat)
    (low : Vector (Vector Word (2^lo)) count)
    (scaled : Vector (Vector (Vector Word lanes) count) (2^hi)) :
    BF64.Packed.Buffer (2^(lo+hi)*lanes) :=
  Packed.tabulate _ fun i =>
    let row : Fin (2^(lo+hi)) := i.divNat
    let h : Fin (2^hi) := ⟨row.val/2^lo, by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
      simpa only [pow_add, Nat.mul_comm] using row.isLt⟩
    let l : Fin (2^lo) := ⟨row.val%2^lo, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
    let c : Fin lanes := i.modNat
    ∑ q : Fin count, scaled[h][q][c]*low[q][l]


/-- Matrix reconstruction addresses the same row and lane as its packed output. -/
theorem read_splitDotRows (lo hi lanes count : Nat)
    (low : Vector (Vector Word (2^lo)) count)
    (scaled : Vector (Vector (Vector Word lanes) count) (2^hi))
    (row : Fin (2^(lo+hi))) (c : Fin lanes) :
    BF64.Packed.read (splitDotRows lo hi lanes count low scaled) (finProdFinEquiv (row,c)) =
      ∑ q : Fin count,
        scaled[(⟨row.val/2^lo, (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
          (by simpa only [pow_add, Nat.mul_comm] using row.isLt)⟩ : Fin (2^hi))][q][c] *
        low[q][(⟨row.val%2^lo, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : Fin (2^lo))] := by
  unfold splitDotRows
  rw [Packed.read_tabulate]
  have div : (finProdFinEquiv (row,c)).divNat = row :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply _)
  have mod : (finProdFinEquiv (row,c)).modNat = c :=
    congrArg Prod.snd (finProdFinEquiv.symm_apply_apply _)
  simp only [div, mod]

/-- Dense induction shares a low tensor and scales a high tensor once per query and limb. -/
def induceSplitRows (lo hi rate : Nat) (hd : lo+hi+rate < 64) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2^(lo+hi+rate))) count) (values : Fin count → Fin lanes → Word) :
    BF64.Packed.Buffer (2^(lo+hi)*lanes) :=
  let constants := inductionConstants (lo+hi) (by omega)
  let factors := positions.map (inductionFactors (by omega) hd constants)
  let low := factors.map fun f => novelTensor lo (Vector.ofFn fun k => f[k.val])
  let high := factors.map fun f => novelTensor hi (Vector.ofFn fun k => f[lo+k.val]'(by have := k.isLt; omega))
  let scaled := Vector.ofFn fun h : Fin (2^hi) => Vector.ofFn fun q : Fin count =>
    Vector.ofFn fun c : Fin lanes => values q c * high[q][h]
  splitDotRows lo hi lanes count low scaled

attribute [local irreducible] inductionConstants inductionFactors novelTensor inductionPoint

/-- A unit coefficient in one lane evaluates to its novel tensor and vanishes in every other lane. -/
theorem encodeRows_unit {ell rate : Nat} (hd : ell+rate < 64)
    (plan : Packed.FlatPlan (ell+rate) hd) (lanes : Nat)
    (row : Fin (2^ell)) (source c : Fin lanes) (q : Fin (2^(ell+rate))) :
    BF64.Packed.read (Packed.forward plan ell (by omega) lanes
      (Packed.tileRows ell rate lanes (unitRows _ (finProdFinEquiv (row, source)))))
      (finProdFinEquiv (q, c)) =
      if c = source then
        (novelTensor ell (inductionFactors (by omega) hd (inductionConstants ell (by omega)) q))[row]
      else 0 := by
  change Packed.laneView _ c q = _
  rw [encodeRows_query]
  simp only [Packed.laneView, unitRows, Packed.read_tabulate,
    Equiv.apply_eq_iff_eq, Prod.mk.injEq,
    show (Word.mk 1) = (1 : Word) from rfl, show (Word.mk 0) = (0 : Word) from rfl]
  by_cases same : c = source
  · subst c
    simp only [and_true, ↓reduceIte, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ]
  · simp only [same, and_false, ↓reduceIte, zero_mul, Finset.sum_const_zero]

set_option maxHeartbeats 50000 in
set_option maxRecDepth 8192 in
/-- Dense split lookup retains the complete ordered sum, including repeated positions. -/
theorem induceSplitRows_coordinate (lo hi rate : Nat) (hd : lo+hi+rate < 64)
    (lanes : Nat) {count : Nat} (positions : Vector (Fin (2^(lo+hi+rate))) count)
    (values : Fin count → Fin lanes → Word) (row : Fin (2^(lo+hi))) (c : Fin lanes) :
    BF64.Packed.read (induceSplitRows lo hi rate hd lanes positions values) (finProdFinEquiv (row,c)) =
      ∑ q : Fin count, values q c *
        (novelTensor (lo+hi) (inductionFactors (by omega) hd (inductionConstants (lo+hi) (by omega)) positions[q]))[row] := by
  unfold induceSplitRows
  conv_lhs => rw [read_splitDotRows]
  apply Finset.sum_congr rfl
  intro q _
  have split := novelTensor_split lo hi
    (inductionFactors (by omega) hd (inductionConstants (lo+hi) (by omega)) positions[q]) row
  conv_rhs => rw [split]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_map]
  simp only [Fin.eta]
  rw [mul_assoc]
  congr 1
  exact mul_comm _ _

/-- Split-tensor dense induction equals every coordinate of the certified encoder transpose. -/
theorem induceSplitRows_refines (lo hi rate : Nat) (hd : lo+hi+rate < 64)
    (plan : Packed.FlatPlan (lo+hi+rate) hd) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2^(lo+hi+rate))) count) (values : Fin count → Fin lanes → Word)
    (i : Fin (2^(lo+hi)*lanes)) :
    BF64.Packed.read (induceSplitRows lo hi rate hd lanes positions values) i =
      BF64.Packed.read (induceRows hd plan lanes positions values) i := by
  obtain ⟨⟨row,c⟩,rfl⟩ := finProdFinEquiv.surjective i
  apply Word.toField_injective
  rw [induceSplitRows_coordinate, induceRows_coordinate]
  have address (q : Fin (2^(lo+hi+rate))) (l : Fin lanes) :
      (⟨q.val*lanes+l.val, by have := q.isLt; have := l.isLt; nlinarith⟩ : Fin (2^(lo+hi+rate)*lanes)) =
        finProdFinEquiv (q,l) := by
    apply Fin.ext
    change q.val*lanes+l.val = l.val+lanes*q.val
    simp only [Nat.mul_comm, Nat.add_comm]
  simp only [address, encodeRows_unit hd plan lanes row c]
  change Word.ringEquiv (∑ q : Fin count, values q c * _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_mul]
  simp only [apply_ite, show (0 : Word).toField = 0 from rfl, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact mul_comm _ _

end CompStark.Pcs
