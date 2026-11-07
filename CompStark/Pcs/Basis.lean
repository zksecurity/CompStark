/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.HonestRound
public import CompStark.Pcs.CoordinateMap

/-! Factored opening weights and projections for the initial lane sumcheck. -/
@[expose] public section
namespace CompStark.Pcs
open Interaction Interaction.Oracle

/-- A sum of lane factors times shared column factors, without its Cartesian product. -/
def basisWeight {F : Type} [CommSemiring F] {lanes vars terms : Nat}
    (a : Fin terms → Whir.Table F lanes) (k : Fin terms → Whir.Table F vars) :
    Whir.Table F (lanes+vars) := fun u =>
  ∑ t, a t (fun i => u (Fin.castAdd vars i)) * k t (fun i => u (Fin.natAdd lanes i))

/-- Project each witness lane onto the shared column factors. -/
def basisProjection {F : Type} [CommSemiring F] {lanes vars terms : Nat}
    (f : Whir.Table F (lanes+vars)) (k : Fin terms → Whir.Table F vars) :
    Fin terms → Whir.Table F lanes := fun t l =>
  ∑ x, f (Fin.addCases l x) * k t x

/-- Projection replaces the full witness in every inner product against the factored weight. -/
theorem basis_dot {F : Type} [CommSemiring F] {lanes vars terms : Nat}
    (a : Fin terms → Whir.Table F lanes) (k : Fin terms → Whir.Table F vars)
    (f : Whir.Table F (lanes+vars)) :
    dot (basisWeight a k) f = ∑ t, dot (a t) (basisProjection f k t) := by
  unfold dot basisWeight basisProjection
  rw [← (Whir.splitCubeEquiv lanes vars).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Whir.splitCubeEquiv, Equiv.coe_fn_symm_mk, Fin.addCases_left, Fin.addCases_right,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext l
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Consing a lane coordinate commutes with the lane/column split. -/
theorem basis_cons_split (lanes vars : Nat) (b : Bool) (u : Whir.Cube (lanes+vars)) :
    ((Fin.addCases (fun _ : Fin 1 => b) u : Whir.Cube (1+(lanes+vars))) ∘
      Fin.cast (show (lanes+1)+vars = 1+(lanes+vars) by omega)) =
    Fin.addCases (Fin.cons b (fun i => u (Fin.castAdd vars i)))
      (fun i => u (Fin.natAdd lanes i)) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · have pos : Fin.cast (show (lanes+1)+vars = 1+(lanes+vars) by omega)
          (Fin.castAdd vars j.succ) = Fin.natAdd 1 (Fin.castAdd vars j) := by
        apply Fin.ext
        simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_succ, Fin.val_natAdd]
        omega
      simp only [Function.comp_apply, pos, Fin.addCases_right, Fin.addCases_left, Fin.cons_succ]
  · have pos : Fin.cast (show (lanes+1)+vars = 1+(lanes+vars) by omega)
        (Fin.natAdd (lanes+1) j) = Fin.natAdd 1 (Fin.natAdd lanes j) := by
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_natAdd]
      omega
    simp only [Function.comp_apply, pos, Fin.addCases_right]

/-- Transporting a first lane slice produces the ordinary Boolean cons. -/
theorem basis_lane_cons (lanes : Nat) (b : Bool) (u : Whir.Cube lanes) :
    ((Fin.addCases (fun _ : Fin 1 => b) u : Whir.Cube (1+lanes)) ∘
      Fin.cast (show lanes+1 = 1+lanes by omega)) = Fin.cons b u := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · have pos : Fin.cast (show lanes+1 = 1+lanes by omega) j.succ = Fin.natAdd 1 j :=
      Fin.ext (by simp only [Fin.val_cast, Fin.val_succ, Fin.val_natAdd]; omega)
    simp only [Function.comp_apply, pos, Fin.addCases_right, Fin.cons_succ]

/-- Restrict the lane factors while retaining their shared column factors. -/
theorem basisWeight_fold {F : Type} [CommRing F] {lanes vars terms : Nat}
    (a : Fin terms → Whir.Table F (lanes+1)) (k : Fin terms → Whir.Table F vars) (r : F) :
    Whir.foldMessageOne (lanes := lanes) (vars := vars) (basisWeight a k) r =
      basisWeight (fun t => Whir.foldMessageOne (lanes := lanes) (vars := 0) (a t) r) k := by
  funext u
  rw [Whir.foldMessageOne_apply]
  simp only [Whir.castTable, basis_cons_split, basisWeight, Fin.addCases_left, Fin.addCases_right,
    Whir.foldMessageOne_apply, Whir.castTable, Nat.add_zero, basis_lane_cons,
    Finset.mul_sum, add_mul, mul_assoc, Finset.sum_add_distrib]

/-- Projecting a restricted witness is the restriction of its projected lanes. -/
theorem basisProjection_fold {F : Type} [CommRing F] {lanes vars terms : Nat}
    (f : Whir.Table F ((lanes+1)+vars)) (k : Fin terms → Whir.Table F vars) (r : F) :
    basisProjection (lanes := lanes) (Whir.foldMessageOne (lanes := lanes) (vars := vars) f r) k =
      fun t => Whir.foldMessageOne (lanes := lanes) (vars := 0)
        (basisProjection (lanes := lanes+1) f k t) r := by
  funext t l
  simp only [basisProjection, Whir.foldMessageOne_apply, Whir.castTable, basis_cons_split,
    Nat.add_zero, basis_lane_cons, Fin.addCases_left, Fin.addCases_right,
    add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

/-- Restrict the first lane to one Boolean endpoint. -/
def basisSlice {F : Type} {lanes vars : Nat}
    (f : Whir.Table F ((lanes+1)+vars)) (b : Bool) : Whir.Table F (lanes+vars) :=
  fun u => f ((Fin.addCases (fun _ : Fin 1 => b) u) ∘
    Fin.cast (show (lanes+1)+vars = 1+(lanes+vars) by omega))

/-- A sliced weight retains its shared column factors. -/
theorem basisWeight_slice {F : Type} [CommSemiring F] {lanes vars terms : Nat}
    (a : Fin terms → Whir.Table F (lanes+1)) (k : Fin terms → Whir.Table F vars) (b : Bool) :
    basisSlice (basisWeight a k) b =
      basisWeight (fun t l => a t (Fin.cons b l)) k := by
  funext u
  simp only [basisSlice, basis_cons_split, basisWeight, Fin.addCases_left, Fin.addCases_right]

/-- Witness projection commutes with taking a lane endpoint. -/
theorem basisProjection_slice {F : Type} [CommSemiring F] {lanes vars terms : Nat}
    (f : Whir.Table F ((lanes+1)+vars)) (k : Fin terms → Whir.Table F vars) (b : Bool) :
    basisProjection (basisSlice f b) k = fun t l => basisProjection f k t (Fin.cons b l) := by
  funext t l
  simp only [basisProjection, basisSlice, basis_cons_split, Fin.addCases_left, Fin.addCases_right]

/-- Shared-factor projection is linear in the witness. -/
theorem basisProjection_sub {F : Type} [CommRing F] {lanes vars terms : Nat}
    (f g : Whir.Table F (lanes+vars)) (k : Fin terms → Whir.Table F vars) :
    basisProjection (fun u => f u - g u) k =
      fun t l => basisProjection f k t l - basisProjection g k t l := by
  funext t l
  simp only [basisProjection, sub_mul, Finset.sum_sub_distrib]

/-- Shared-factor weights are linear in their lane coefficients. -/
theorem basisWeight_sub {F : Type} [CommRing F] {lanes vars terms : Nat}
    (a b : Fin terms → Whir.Table F lanes) (k : Fin terms → Whir.Table F vars) :
    basisWeight (fun t l => a t l - b t l) k = fun u => basisWeight a k u - basisWeight b k u := by
  funext u
  simp only [basisWeight, sub_mul, Finset.sum_sub_distrib]

/-- Both compressed coefficients are contractions of the two small lane matrices. -/
theorem basis_honestRound {F : Type} [CommRing F] {lanes vars terms : Nat}
    (a : Fin terms → Whir.Table F (lanes+1)) (k : Fin terms → Whir.Table F vars)
    (f : Whir.Table F ((lanes+1)+vars)) :
    honestRound (basisWeight a k) f =
      (∑ t, (honestRound (vars := 0) (a t) (basisProjection f k t)).1,
        fun i => ∑ t, (honestRound (vars := 0) (a t) (basisProjection f k t)).2 i) := by
  have constant := basis_dot (fun t l => a t (Fin.cons false l)) k (basisSlice f false)
  have quadratic := basis_dot
    (fun t l => a t (Fin.cons true l) - a t (Fin.cons false l)) k
    (fun u => basisSlice f true u - basisSlice f false u)
  rw [basisProjection_sub, basisProjection_slice, basisProjection_slice] at quadratic
  rw [basisProjection_slice] at constant
  apply Prod.ext
  · simpa only [honestRound, Whir.castTable, basis_cons_split, basisWeight,
      Fin.addCases_left, Fin.addCases_right, dot, Nat.add_zero, basis_lane_cons, basisSlice]
      using constant
  · funext i
    have difference :
        (fun u => basisWeight a k
          ((Fin.addCases (fun _ : Fin 1 => true) u) ∘
            Fin.cast (show (lanes+1)+vars = 1+(lanes+vars) by omega)) -
          basisWeight a k
          ((Fin.addCases (fun _ : Fin 1 => false) u) ∘
            Fin.cast (show (lanes+1)+vars = 1+(lanes+vars) by omega))) =
        basisWeight (fun t l => a t (Fin.cons true l) - a t (Fin.cons false l)) k := by
      rw [basisWeight_sub]
      exact congrArg₂ (fun x y => fun u => x u - y u)
        (basisWeight_slice a k true) (basisWeight_slice a k false)
    change dot _ _ = _
    simp only [Whir.castTable]
    rw [difference]
    simpa only [honestRound, Whir.castTable, dot, Nat.add_zero, basis_lane_cons, basisSlice] using quadratic

/-- Binary-linear maps admit one shared column factor per physical binary coordinate. -/
theorem basis_mapped_product (stages : List (Nat × BF64.Ext3))
    (x y : BF64.WordExt3) :
    frobeniusMap stages (x.toField * y.toField) =
      ∑ i : Fin 192,
        (if packedBit (mapLimb x ⟨i.val / 64, by omega⟩).val ⟨i.val % 64, by omega⟩
          then 1 else 0) *
        frobeniusMap stages ((coordinateBasis i).toField * y.toField) := by
  rw [coordinateExpansion x, Finset.sum_mul]
  change (frobeniusAddHom stages) _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp only [one_mul, zero_mul, map_zero]
  rfl

end CompStark.Pcs
