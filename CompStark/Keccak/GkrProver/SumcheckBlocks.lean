/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.FieldTransport

/-! Composition of consecutive honest sumcheck blocks. -/

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr
open scoped BigOperators

/-- Concatenate low and high coordinates with the low dimension in the structural recursion position. -/
def joinPoint {F : Type} {a b : Nat} (low : Fin a → F) (high : Fin b → F) : Fin (b+a) → F :=
  fun i => if h : i.val < a then low ⟨i.val,h⟩ else high ⟨i.val-a,by omega⟩

/-- An empty low block leaves the high coordinates unchanged. -/
theorem joinPoint_zero {F : Type} {b : Nat} (low : Fin 0 → F) (high : Fin b → F) :
    joinPoint low high = high := by
  funext i
  simp only [joinPoint,Nat.not_lt_zero,dite_false,Nat.sub_zero]
  rfl

/-- Exposing the first low coordinate commutes with concatenating the remaining blocks. -/
theorem joinPoint_cons {F : Type} {a b : Nat} (r : F) (low : Fin a → F) (high : Fin b → F) :
    joinPoint (Fin.cons r low) high = Fin.cons r (joinPoint low high) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · change (if h : 0 < a+1 then (Fin.cons r low : Fin (a+1) → F) ⟨0,h⟩ else _) = r
    rw [dite_eq_left (by omega)]
    rfl
  · simp only [joinPoint,Fin.val_succ,Fin.cons_succ,Nat.add_lt_add_iff_right,Nat.add_sub_add_right]
    split <;> rfl

/-- Low and high Boolean assignments enumerate each full Boolean assignment exactly once. -/
def booleanJoinEquiv (a b : Nat) :
    ((Fin a → Fin 2) × (Fin b → Fin 2)) ≃ (Fin (b+a) → Fin 2) where
  toFun pair := joinPoint pair.1 pair.2
  invFun point := (fun i => point ⟨i.val,by omega⟩,fun i => point ⟨a+i.val,by omega⟩)
  left_inv pair := by
    apply Prod.ext
    · funext i
      simp only [joinPoint,i.isLt,dite_true]
    · funext i
      simp only [joinPoint,show ¬a+i.val < a by omega,dite_false,Nat.add_sub_cancel_left]
  right_inv point := by
    funext i
    dsimp only [joinPoint]
    split
    · rfl
    · rename_i h
      apply congrArg point
      apply Fin.ext
      dsimp only
      omega

/-- Summing a cube is the iterated Boolean sum of its low and high blocks. -/
theorem booleanSum_join {F : Type} [CommRing F] {a b : Nat}
    (f : (Fin (b+a) → F) → F) :
    booleanSum f = booleanSum (fun low => booleanSum (fun high => f (joinPoint low high))) := by
  unfold booleanSum
  rw [← (booleanJoinEquiv a b).sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro low _
  apply Finset.sum_congr rfl
  intro high _
  congr 1
  funext i
  change ((joinPoint low high i).val : F) =
    joinPoint (fun j => ((low j).val : F)) (fun j => ((high j).val : F)) i
  unfold joinPoint
  split <;> rfl

/-- Prefix messages equal the honest strategy obtained by summing out the later Boolean block. -/
theorem honestCompressedRounds_prefix {F : Type} [CommRing F] [IsDomain F] [Fintype F]
    {a b degree : Nat} (f : (Fin (b+a) → F) → F) (g : (Fin a → F) → F)
    (hf : CoordinateDegree f (degree+1)) (hg : CoordinateDegree g (degree+1))
    (h : ∀ low,g low = booleanSum (fun high => f (joinPoint low high)))
    (hcard : degree+1 < Fintype.card F) (low : Fin a → F) (high : Fin b → F) (i : Fin a) :
    honestCompressedRounds f hf (joinPoint low high) ⟨i.val,by omega⟩ =
      honestCompressedRounds g hg low i := by
  induction a with
  | zero => exact i.elim0
  | succ a ih =>
    have hp : joinPoint low high = Fin.cons (low 0) (joinPoint (fun i => low i.succ) high) := by
      conv_lhs => rw [← Fin.cons_self_tail low]
      exact joinPoint_cons _ _ _
    rw [hp]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.val_zero,honestCompressedRounds,Fin.cons_zero]
      apply congrArg Sumcheck.compress
      apply firstHonestPolynomial_eq f hf hcard (firstHonestPolynomial g hg)
      intro r
      rw [firstHonestPolynomial_eval]
      trans booleanSum (fun rest : Fin a → F =>
        booleanSum (fun later : Fin b → F => f (Fin.cons r (joinPoint rest later))))
      · apply congrArg booleanSum
        funext rest
        rw [h]
        apply congrArg booleanSum
        funext later
        rw [joinPoint_cons]
      · exact (booleanSum_join (a := a) (b := b) (fun rest => f (Fin.cons r rest))).symm
    · simp only [Fin.val_succ,honestCompressedRounds,Fin.cons_succ]
      apply ih
      intro point
      rw [h]
      apply congrArg booleanSum
      funext rest
      rw [joinPoint_cons]
      rfl

/-- Suffix messages equal the honest strategy with every earlier coordinate bound to its actual challenge. -/
theorem honestCompressedRounds_suffix {F : Type} [CommRing F] {a b degree : Nat}
    (f : (Fin (b+a) → F) → F) (g : (Fin b → F) → F)
    (hf : CoordinateDegree f (degree+1)) (hg : CoordinateDegree g (degree+1))
    (low : Fin a → F) (high : Fin b → F) (h : ∀ point,f (joinPoint low point) = g point) (i : Fin b) :
    honestCompressedRounds f hf (joinPoint low high) ⟨a+i.val,by omega⟩ =
      honestCompressedRounds g hg high i := by
  induction a with
  | zero =>
    have hfg : f = g := by funext point; simpa only [joinPoint_zero] using h point
    subst g
    simp only [joinPoint_zero,Nat.zero_add]
    rfl
  | succ a ih =>
    have hp : joinPoint low high = Fin.cons (low 0) (joinPoint (fun i => low i.succ) high) := by
      conv_lhs => rw [← Fin.cons_self_tail low]
      exact joinPoint_cons _ _ _
    rw [hp]
    have hi : (⟨a+1+i.val,by omega⟩ : Fin (b+(a+1))) =
        (⟨a+i.val,by omega⟩ : Fin (b+a)).succ := Fin.ext (by simp only [Fin.val_succ]; omega)
    rw [hi]
    simp only [honestCompressedRounds,Fin.cons_succ]
    apply ih
    intro point
    have hh := h point
    rw [← Fin.cons_self_tail low,joinPoint_cons] at hh
    exact hh

end CompStark.Keccak.GkrProver
