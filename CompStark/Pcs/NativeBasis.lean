/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.Basis
public import CompStark.Pcs.NativeRound

/-! Row-major projected lane matrices and the final shared-factor weight lift. -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace CompStark.Pcs
open BF64
attribute [local irreducible] WordExt3.toField Word.toField WordExt3.mulScalar

/-- A row-major address with a statically bounded row and column. -/
@[inline] def basisAddress {rows cols : Nat} (row : Fin rows) (col : Fin cols) : Fin (rows*cols) :=
  ⟨row.val*cols+col.val, by have := row.isLt; have := col.isLt; nlinarith⟩

/-- Interpret a row-major witness in lane-first Boolean coordinates. -/
def basisTable {F : Type} {lanes vars : Nat} (f : Vector F (2^lanes*2^vars)) :
    Whir.Table F (lanes+vars) := fun u =>
  f[basisAddress (vertexIndex lanes (fun i => u (Fin.castAdd vars i)))
    (vertexIndex vars (fun i => u (Fin.natAdd lanes i)))]

/-- Interpret one column of a row-major term matrix as a lane table. -/
def basisLaneTable {F : Type} {lanes terms : Nat} (a : Vector F (2^lanes*terms))
    (t : Fin terms) : Whir.Table F lanes := fun l => a[basisAddress (vertexIndex lanes l) t]

/-- Interpret the shared numeric column factors as Boolean tables. -/
def basisKernelTable {F : Type} {vars terms : Nat} (k : Vector (Vector F (2^vars)) terms)
    (t : Fin terms) : Whir.Table F vars := fun x => k[t][vertexIndex vars x]

/-- Project base-field witness rows once onto each shared column factor. -/
def projectBasis (lanes cols terms : Nat) (f : Vector Word (lanes*cols))
    (k : Vector (Vector WordExt3 cols) terms) : Vector WordExt3 (lanes*terms) :=
  Vector.ofFn fun i =>
    let row : Fin lanes := i.divNat
    let term : Fin terms := i.modNat
    sumWords (List.ofFn fun x : Fin cols => WordExt3.mulScalar k[term][x] f[basisAddress row x])

/-- Each native projection is the exact shared-factor weighted row sum. -/
theorem projectBasis_refines (lanes cols terms : Nat) (f : Vector Word (lanes*cols))
    (k : Vector (Vector WordExt3 cols) terms) (row : Fin lanes) (term : Fin terms) :
    (projectBasis lanes cols terms f k)[basisAddress row term].toField =
      ∑ x : Fin cols, k[term][x].toField *
        (algebraMap BF64 BF64.Ext3) f[basisAddress row x].toField := by
  have positive : 0 < terms := by have := term.isLt; omega
  have quotient : (row.val*terms+term.val)/terms = row.val := by
    rw [Nat.mul_comm row.val, Nat.mul_add_div positive, Nat.div_eq_of_lt term.isLt, Nat.add_zero]
  have remainder : (row.val*terms+term.val)%terms = term.val := Nat.mul_add_mod_of_lt term.isLt
  simp only [projectBasis, Fin.getElem_fin, Vector.getElem_ofFn, Fin.divNat, Fin.modNat,
    basisAddress, quotient, remainder, sumWords_refines, List.map_ofFn, Function.comp_apply,
    WordExt3.toField_mulScalar, Algebra.smul_def, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro x _
  exact mul_comm _ _

/-- Numeric projections are the mathematical projections in lane-first coordinates. -/
theorem projectBasis_table (lanes vars terms : Nat) (f : Vector Word (2^lanes*2^vars))
    (k : Vector (Vector WordExt3 (2^vars)) terms) (term : Fin terms) :
    basisLaneTable ((projectBasis (2^lanes) (2^vars) terms f k).map WordExt3.toField) term =
      basisProjection (basisTable (f.map fun x => (algebraMap BF64 BF64.Ext3) x.toField))
        (basisKernelTable (k.map fun row => row.map WordExt3.toField)) term := by
  funext l
  change ((projectBasis (2^lanes) (2^vars) terms f k).map WordExt3.toField)[(basisAddress (vertexIndex lanes l) term).val] = _
  rw [Vector.getElem_map]
  change (projectBasis (2^lanes) (2^vars) terms f k)[basisAddress (vertexIndex lanes l) term].toField = _
  rw [projectBasis_refines]
  unfold basisProjection
  rw [← (vertexEquiv vars).sum_comp]
  simp only [basisTable, basisKernelTable, Fin.addCases_left, Fin.addCases_right,
    Fin.getElem_fin, Vector.getElem_map, vertexEquiv, Equiv.coe_fn_mk]
  have inverse (x : Fin (2^vars)) : vertexIndex vars (vertex vars x) = x :=
    (vertexEquiv vars).left_inv x
  simp only [inverse]
  apply Finset.sum_congr rfl
  intro x _
  exact mul_comm _ _

/-- Lift the last lane coefficient row into its shared column factors. -/
def liftBasis (cols terms : Nat) (a : Vector WordExt3 terms)
    (k : Vector (Vector WordExt3 cols) terms) : Vector WordExt3 cols :=
  Vector.ofFn fun x => sumWords (List.ofFn fun t : Fin terms => WordExt3.mul a[t] k[t][x])

/-- The final native lift is exactly the factored lane weight's contraction. -/
theorem liftBasis_refines (cols terms : Nat) (a : Vector WordExt3 terms)
    (k : Vector (Vector WordExt3 cols) terms) (x : Fin cols) :
    (liftBasis cols terms a k)[x].toField =
      ∑ t : Fin terms, a[t].toField * k[t][x].toField := by
  simp only [liftBasis, Fin.getElem_fin, Vector.getElem_ofFn, sumWords_refines,
    List.map_ofFn, Function.comp_apply, WordExt3.toField_mul, List.sum_ofFn]

/-- Consing a Boolean coordinate places it in the least significant numeric bit. -/
theorem vertexIndex_cons (n : Nat) (b : Bool) (u : Whir.Cube n) :
    (vertexIndex (n+1) (Fin.cons b u)).val = b.toNat + 2*(vertexIndex n u).val := by
  let index := vertexIndex n u
  have bound : Nat.bit b index.val < 2^(n+1) := by
    have := index.isLt
    cases b <;> simp only [Nat.bit_false, Nat.bit_true, pow_succ] <;> omega
  have same : vertexIndex (n+1) (Fin.cons b u) = ⟨Nat.bit b index.val, bound⟩ := by
    apply vertex_injective
    rw [vertex_vertexIndex]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, vertex, Fin.val_zero, Nat.testBit_bit_zero]
    · simp only [Fin.cons_succ, vertex, Fin.val_succ, Nat.testBit_bit_succ]
      exact (congrFun (vertex_vertexIndex n u) j).symm
  rw [same]
  change Nat.bit b index.val = b.toNat + 2*index.val
  cases b <;> simp only [Nat.bit_false, Nat.bit_true, Bool.toNat_false, Bool.toNat_true] <;> omega

/-- A complete projected lane matrix's compressed native message. -/
def basisRound (lanes terms : Nat) (a p : Vector WordExt3 (2^(lanes+1)*terms)) :
    Vector WordExt3 2 :=
  roundCoefficients (2^lanes) terms
    (p.cast (by rw [pow_succ]; ac_rfl)) (a.cast (by rw [pow_succ]; ac_rfl))

/-- Projection matrices transmit the sum of their lane-wise honest quadratic coefficients. -/
theorem basisRound_refines (lanes terms : Nat) (a p : Vector WordExt3 (2^(lanes+1)*terms)) :
    ((basisRound lanes terms a p)[0].toField,
      fun _ : Fin 1 => (basisRound lanes terms a p)[1].toField) =
      (∑ t : Fin terms, (honestRound (vars := 0)
        (basisLaneTable (a.map WordExt3.toField) t)
        (basisLaneTable (p.map WordExt3.toField) t)).1,
      fun i => ∑ t : Fin terms, (honestRound (vars := 0)
        (basisLaneTable (a.map WordExt3.toField) t)
        (basisLaneTable (p.map WordExt3.toField) t)).2 i) := by
  have inverse (x : Fin (2^lanes)) : vertexIndex lanes (vertex lanes x) = x :=
    (vertexEquiv lanes).left_inv x
  have coord (x : Fin (2^lanes)) (b : Bool) :
      (vertexIndex (lanes+1) (Fin.cons b (vertex lanes x))).val = b.toNat + 2*x.val := by
    rw [vertexIndex_cons, inverse]
  apply Prod.ext
  · rw [basisRound, roundCoefficients_constant]
    simp only [honestRound, Whir.castTable, Nat.add_zero, basis_lane_cons]
    conv_rhs =>
      arg 2
      ext t
      rw [← (vertexEquiv lanes).sum_comp]
    rw [Finset.sum_comm]
    rw [← (finProdFinEquiv : Fin (2^lanes) × Fin terms ≃ Fin (2^lanes*terms)).sum_comp,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro row _
    apply Finset.sum_congr rfl
    intro t _
    have quot : (t.val+terms*row.val)/terms = row.val := by
      rw [Nat.add_comm, Nat.mul_add_div (by have := t.isLt; omega),
        Nat.div_eq_of_lt t.isLt, Nat.add_zero]
    have rem : (t.val+terms*row.val)%terms = t.val := by
      rw [Nat.add_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt t.isLt]
    simp only [roundLow, basisLaneTable, basisAddress, Fin.getElem_fin,
      Vector.getElem_cast, Vector.getElem_map, vertexEquiv, Equiv.coe_fn_mk,
      finProdFinEquiv, quot, rem, coord, Bool.toNat_false, Nat.zero_add]
    simp only [Nat.mul_comm, Nat.add_comm]
    exact mul_comm _ _
  · funext i
    rw [basisRound, roundCoefficients_quadratic]
    simp only [honestRound, Whir.castTable, Nat.add_zero, basis_lane_cons]
    conv_rhs =>
      arg 2
      ext t
      rw [← (vertexEquiv lanes).sum_comp]
    rw [Finset.sum_comm]
    rw [← (finProdFinEquiv : Fin (2^lanes) × Fin terms ≃ Fin (2^lanes*terms)).sum_comp,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro row _
    apply Finset.sum_congr rfl
    intro t _
    have quot : (t.val+terms*row.val)/terms = row.val := by
      rw [Nat.add_comm, Nat.mul_add_div (by have := t.isLt; omega),
        Nat.div_eq_of_lt t.isLt, Nat.add_zero]
    have rem : (t.val+terms*row.val)%terms = t.val := by
      rw [Nat.add_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt t.isLt]
    simp only [roundLow, roundHigh, basisLaneTable, basisAddress, Fin.getElem_fin,
      Vector.getElem_cast, Vector.getElem_map, vertexEquiv, Equiv.coe_fn_mk,
      finProdFinEquiv, quot, rem, coord, Bool.toNat_false, Bool.toNat_true,
      Nat.zero_add, CharTwo.sub_eq_add]
    simp only [Nat.mul_comm, Nat.add_comm]
    ring

/-- Restrict both projected lane matrices using the shared prepared challenge. -/
def foldBasis (lanes terms : Nat) (a : Vector WordExt3 (2^(lanes+1)*terms))
    (r : WordExt3) : Vector WordExt3 (2^lanes*terms) :=
  CompStark.Sumcheck.fold (CompStark.Sumcheck.prepare r) (2^lanes) terms
    (a.cast (by rw [pow_succ]; ac_rfl))

/-- Native matrix folding is the same lane restriction used by the honest strategy. -/
theorem foldBasis_refines (lanes terms : Nat) (a : Vector WordExt3 (2^(lanes+1)*terms))
    (r : WordExt3) (t : Fin terms) :
    basisLaneTable ((foldBasis lanes terms a r).map WordExt3.toField) t =
      Whir.foldMessageOne (lanes := lanes) (vars := 0)
        (basisLaneTable (a.map WordExt3.toField) t) r.toField := by
  funext l
  have positive : 0 < terms := by have := t.isLt; omega
  have quot : ((vertexIndex lanes l).val*terms+t.val)/terms = (vertexIndex lanes l).val := by
    rw [Nat.mul_comm (vertexIndex lanes l).val, Nat.mul_add_div positive,
      Nat.div_eq_of_lt t.isLt, Nat.add_zero]
  have rem : ((vertexIndex lanes l).val*terms+t.val)%terms = t.val :=
    Nat.mul_add_mod_of_lt t.isLt
  change ((foldBasis lanes terms a r).map WordExt3.toField)[(basisAddress (vertexIndex lanes l) t).val] = _
  rw [Vector.getElem_map]
  change (CompStark.Sumcheck.fold (CompStark.Sumcheck.prepare r) (2^lanes) terms
    (a.cast (by rw [pow_succ]; ac_rfl)))[basisAddress (vertexIndex lanes l) t].toField = _
  rw [CompStark.Sumcheck.fold_refines]
  simp only [basisAddress, quot, rem, Vector.getElem_cast, Whir.foldMessageOne_apply,
    Whir.castTable, Nat.add_zero, basis_lane_cons, basisLaneTable, Fin.getElem_fin,
    Vector.getElem_map, vertexIndex_cons, Bool.toNat_false, Bool.toNat_true, Nat.zero_add,
    CharTwo.sub_eq_add]
  simp only [Nat.mul_comm, Nat.add_comm]

/-- Matrix contraction gives the honest round of the full factored physical weight. -/
theorem basisRound_projected (lanes vars terms : Nat)
    (a : Vector WordExt3 (2^(lanes+1)*terms))
    (f : Vector Word (2^(lanes+1)*2^vars)) (k : Vector (Vector WordExt3 (2^vars)) terms) :
    ((basisRound lanes terms a (projectBasis (2^(lanes+1)) (2^vars) terms f k))[0].toField,
      fun _ : Fin 1 =>
        (basisRound lanes terms a (projectBasis (2^(lanes+1)) (2^vars) terms f k))[1].toField) =
      honestRound (basisWeight (basisLaneTable (a.map WordExt3.toField))
        (basisKernelTable (k.map fun row => row.map WordExt3.toField)))
        (basisTable (f.map fun x => (algebraMap BF64 BF64.Ext3) x.toField)) := by
  rw [basisRound_refines, basis_honestRound]
  simp only [projectBasis_table]

end CompStark.Pcs
