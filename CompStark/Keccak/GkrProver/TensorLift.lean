/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.TensorInterpolation

/-! Boolean-vertex semantics of the multilinear factor lift used by tensor interpolation. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators

/-- Lifting commutes with every additive interpretation of the Boolean table. -/
theorem ternaryLift_map {F G : Type*} [AddCommMonoid F] [AddCommMonoid G]
    (f : F →+ G) (n : Nat) (values : Nat → F) (row : Nat) :
    ternaryLift n (fun i => f (values i)) row = f (ternaryLift n values row) := by
  induction n generalizing values row with
  | zero => rfl
  | succ n ih =>
    rw [ternaryLift,ternaryLift]
    split
    · exact ih _ _
    · split
      · exact ih _ _
      · simp only [← map_add]
        exact ih _ _

/-- A lifted zero factor is zero at every ternary assignment. -/
theorem ternaryLift_zero_table {F : Type*} [AddCommMonoid F] (n row : Nat) :
    ternaryLift n (fun _ => (0 : F)) row = 0 := by
  induction n generalizing row with
  | zero => rfl
  | succ n ih =>
    rw [ternaryLift]
    split
    · exact ih _
    · split
      · exact ih _
      · simpa only [zero_add] using ih (row/3)

/-- The factor lift at a fixed ternary assignment is an additive map on Boolean tables. -/
def ternaryLiftHom (n row : Nat) : (Nat → W) →+ W where
  toFun := fun values => ternaryLift n values row
  map_zero' := ternaryLift_zero_table n row
  map_add' := fun a b => ternaryLift_add n a b row

/-- The factor lift commutes with multiplication by one field scalar. -/
theorem ternaryLift_scale (n : Nat) (values : Nat → W) (scale : W) (row : Nat) :
    ternaryLift n (fun i => scale*values i) row = scale*ternaryLift n values row := by
  induction n generalizing values row with
  | zero => rfl
  | succ n ih =>
    rw [ternaryLift,ternaryLift]
    split
    · exact ih _ _
    · split
      · exact ih _ _
      · simp only [← mul_add]
        exact ih _ _

/-- A bounded ternary assignment only reads its original Boolean block. -/
theorem ternaryLift_congr {F : Type*} [Add F] (n q : Nat) (hq : q < 3^n)
    (a b : Nat → F) (h : ∀ i, i < 2^n → a i = b i) :
    ternaryLift n a q = ternaryLift n b q := by
  induction n generalizing q a b with
  | zero =>
    have hq0 : q = 0 := by simpa only [pow_zero,Nat.lt_one_iff] using hq
    exact h q (by rw [hq0]; decide)
  | succ n ih =>
    have htail : q/3 < 3^n := by
      rw [pow_succ] at hq
      omega
    have heven (i : Nat) (hi : i < 2^n) : a (2*i) = b (2*i) :=
      h _ (by rw [pow_succ]; omega)
    have hodd (i : Nat) (hi : i < 2^n) : a (2*i+1) = b (2*i+1) :=
      h _ (by rw [pow_succ]; omega)
    rw [ternaryLift,ternaryLift]
    split
    · exact ih _ htail _ _ heven
    · split
      · exact ih _ htail _ _ hodd
      · exact ih _ htail _ _ (fun i hi => congrArg₂ (·+·) (heven i hi) (hodd i hi))

/-- The Boolean factor lift uses XOR for addition of infinity endpoints. -/
def ternaryLiftBool (n : Nat) (values : Nat → Bool) (row : Nat) : Bool :=
  @ternaryLift Bool ⟨Bool.xor⟩ n values row

/-- Casting a Boolean factor lift into the word field preserves its complete endpoint sum. -/
theorem ternaryLiftBool_word (n : Nat) (values : Nat → Bool) (row : Nat) :
    ternaryLift n (fun i => if values i then (1 : W) else 0) row =
      if ternaryLiftBool n values row then 1 else 0 := by
  induction n generalizing values row with
  | zero => rfl
  | succ n ih =>
    simp only [ternaryLiftBool,ternaryLift]
    split
    · exact ih _ _
    · split
      · exact ih _ _
      · have hfun : (fun i => (if values (2*i) then (1 : W) else 0)+
            (if values (2*i+1) then 1 else 0)) =
            (fun i => if values (2*i) ^^ values (2*i+1) then 1 else 0) := by
          funext i
          cases values (2*i) <;> cases values (2*i+1) <;>
            simp only [Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true,
              Bool.false_eq_true,ite_false,ite_true,add_zero,zero_add,CharTwo.add_self_eq_zero]
        rw [hfun]
        exact ih _ _

/-- The binary coefficient of a lifted basis vector is the native plan's vertex selector. -/
theorem ternaryLift_basis : ∀ q : Fin 81, ∀ b : Fin 16,
    ternaryLiftBool 4 (fun k => decide (k = b.val)) q.val = ternarySelect q.val b.val := by
  decide

/-- The selector certificate transfers from binary bits to the prover's word extension field. -/
theorem ternaryLift_basis_word (q : Fin 81) (b : Fin 16) :
    ternaryLift 4 (fun k => if k = b.val then (1 : W) else 0) q.val =
      if ternarySelect q.val b.val then 1 else 0 := by
  have h := ternaryLiftBool_word 4 (fun k => decide (k = b.val)) q.val
  simpa only [decide_eq_true_eq,ternaryLift_basis q b] using h

/-- The native selected-vertex sum is exactly the lifted multilinear factor at every ternary assignment. -/
theorem ternaryLift_eq_value (values : Nat → W) (q : Fin 81) :
    ternaryLift 4 values q.val = ternaryValue (fun b => values b.val) q.val := by
  have hrep : ternaryLift 4 values q.val = ternaryLift 4
      (fun k => ∑ b : Fin 16, if k = b.val then values b.val else 0) q.val := by
    apply ternaryLift_congr 4 q.val q.isLt
    intro k hk
    have hsum := Finset.sum_ite_eq' (Finset.univ : Finset (Fin 16)) ⟨k,hk⟩
      (fun b : Fin 16 => values b.val)
    simpa only [Fin.ext_iff,Finset.mem_univ,ite_true,eq_comm] using hsum.symm
  rw [hrep]
  have hfun : (fun k => ∑ b : Fin 16, if k = b.val then values b.val else 0) =
      ∑ b : Fin 16, (fun k => if k = b.val then values b.val else 0) := by
    funext k
    simp only [Finset.sum_apply]
  rw [hfun]
  change ternaryLiftHom 4 q.val (∑ b : Fin 16, _) = _
  rw [map_sum]
  unfold ternaryValue
  apply Finset.sum_congr rfl
  intro b _
  change ternaryLift 4 (fun k => if k = b.val then values b.val else 0) q.val = _
  have hbfun : (fun k => if k = b.val then values b.val else 0) =
      (fun k => values b.val*(if k = b.val then (1 : W) else 0)) := by
    funext k
    split <;> simp only [mul_one,mul_zero]
  rw [hbfun,ternaryLift_scale,ternaryLift_basis_word]
  split <;> simp only [mul_one,mul_zero]

/-- A ternary assignment is finite when none of its bound digits is infinity. -/
def ternaryIsFinite : Nat → Nat → Bool
  | 0, _ => true
  | n+1, q => decide (q%3 ≠ 2) && ternaryIsFinite n (q/3)

/-- The native binary-row flag is precisely the absence of infinity digits. -/
theorem ternaryPlan_finite : ∀ q : Fin 81,
    ((ternaryPlan[q.val]!).2 = 81) ↔ ternaryIsFinite 4 q.val = true := by
  intro q
  simp only [ternaryPlan,getElem!_pos,Array.size_ofFn,Fin.isLt,Array.getElem_ofFn,
    Std.Legacy.Range.forIn_eq_forIn_range']
  revert q
  decide

/-- Degree-one tensor data vanishes at infinity and agrees with the factor lift at finite vertices. -/
theorem ternaryLinearLift_eq (n : Nat) (values : Nat → W) (row : Nat) :
    ternaryLinearLift n values row =
      if ternaryIsFinite n row then ternaryLift n values row else 0 := by
  induction n generalizing values row with
  | zero => rfl
  | succ n ih =>
    rw [ternaryLinearLift,ternaryIsFinite,ternaryLift]
    by_cases hz : row%3 = 0
    · simp only [hz,ne_eq,Nat.reduceEqDiff,not_false_eq_true,decide_true,Bool.true_and,ite_true,ih]
    · rw [ite_eq_right hz,ite_eq_right hz]
      by_cases ho : row%3 = 1
      · rw [ite_eq_left ho,ite_eq_left ho,ih]
        simp only [ho,ne_eq,Nat.reduceEqDiff,not_false_eq_true,decide_true,Bool.true_and]
      · rw [ite_eq_right ho,ite_eq_right ho]
        have hi : row%3 = 2 := by omega
        simp only [hi,ne_eq,not_true_eq_false,decide_false,Bool.false_and,Bool.false_eq_true,ite_false]

end CompStark.Keccak.GkrProver
