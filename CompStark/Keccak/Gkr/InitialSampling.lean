/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.InitialBoundary
public import CompStark.Keccak.Gkr.ExecutionBounds
public import Mathlib.Tactic.LinearCombination

/-! # Initial sampling of the committed Keccak discrepancies -/

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
@[expose] public section
open Polynomial OracleComp
open scoped BigOperators ENNReal
namespace CompStark.Keccak.Gkr

/-- The fixed discrepancy cube, with instance bits, segment bit, then lane bits. -/
def initialTable {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p) (w : Fin (2^(p+10))) : E :=
  initialError x output q ⟨w.val%2^(p+4),Nat.mod_lt _ (by positivity)⟩
    ⟨w.val/2^(p+4),by
      apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
      simpa only [show p+10=p+4+6 by omega,pow_add,show (2^6 : Nat)=64 by decide,Nat.mul_comm] using w.isLt⟩

/-- Subtraction of tables commutes with multilinear evaluation. -/
theorem mle_sub {E : Type*} [CommRing E] {n : Nat}
    (a b : Fin (2^n) → E) (r : Fin n → E) :
    mle (fun i => a i-b i) r = mle a r-mle b r := by
  simp only [mle,mul_sub,Finset.sum_sub_distrib]

/-- A one-bit interpolation is the affine combination of its two entries. -/
theorem mle_one {E : Type*} [CommRing E] (a : Fin 2 → E) (s : E) :
    mle a (fun _ : Fin 1 => s) = (1-s)*a 0+s*a 1 := by
  simp [mle,eqWeight,Fin.sum_univ_two]

/-- A segment-first six-coordinate interpolation separates its segment and lane blocks. -/
theorem mle_segment_lane {E : Type*} [CommRing E]
    (a : Fin 2 → Fin 32 → E) (s : E) (r : Fin 5 → E) :
    mle (fun slot : Fin 64 => a ⟨slot.val%2,Nat.mod_lt _ (by decide)⟩ ⟨slot.val/2,by omega⟩)
      (Fin.cons s r) = ∑ l : Fin 32, eqWeight r l.val * ((1-s)*a 0 l+s*a 1 l) := by
  have h := mle_split (a := 1) (b := 5) a (Fin.cons s r)
  have hlo : (fun i : Fin 1 => (Fin.cons s r : Fin 6 → E) (Fin.castAdd 5 i)) = (fun _ : Fin 1 => s) := by
    funext i; have hi : i = 0 := Subsingleton.elim _ _; subst i; rfl
  have hhi : (fun i : Fin 5 => (Fin.cons s r : Fin 6 → E) (Fin.natAdd 1 i)) = r := by
    funext i
    have he : Fin.natAdd 1 i = i.succ := by
      apply Fin.ext; simp only [Fin.val_natAdd,Fin.val_succ]; omega
    rw [he,Fin.cons_succ]
  simp only [hlo,hhi,mle_one,pow_one] at h
  convert h using 1

/-- The flattened initial challenge point preserves the instance coordinate block. -/
theorem initialPoint_instances {E : Type} {p : Nat} (t : Transcript E p) :
    (fun i : Fin (p+4) => initialPoint t ⟨i.val,by omega⟩) = t.instancePoint := by
  funext i
  simp only [initialPoint,i.isLt,dite_true]

/-- The six high initial coordinates are the segment followed by the five lane coordinates. -/
theorem initialPoint_slots {E : Type} {p : Nat} (t : Transcript E p) :
    (fun i : Fin 6 => initialPoint t ⟨p+4+i.val,by omega⟩) = Fin.cons t.segment t.lanePoint := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.val_zero,Nat.add_zero,initialPoint,lt_self_iff_false,dite_false,dite_true,Fin.cons_zero]
  · simp only [Fin.val_succ,initialPoint,show ¬p+4+(j.val+1)<p+4 by omega,
      dite_false,show ¬p+4+(j.val+1)=p+4 by omega,dite_false,Fin.cons_succ]
    congr 1
    apply Fin.ext
    dsimp only
    omega

/-- The initial discrepancy polynomial is exactly the weighted mismatch of the two segment tables. -/
theorem initial_table_identity {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p) (t : Transcript E p) :
    mle (initialTable x output q) (initialPoint t) =
      (1-t.segment) * ∑ l : Fin 25, eqWeight t.lanePoint l.val *
        (middleWord x q t ⟨25+l.val,by omega⟩ - mle (fun b => segmentLane x q b 0 l) t.instancePoint) +
      t.segment * ∑ l : Fin 25, eqWeight t.lanePoint l.val *
        (mle (fun b => output b l) t.instancePoint - mle (fun b => segmentLane x q b 1 l) t.instancePoint) := by
  have hi := mle_blocks (n := p+10) (a := p+4) (b := 6) (by omega)
    (initialError x output q) (initialPoint t)
  change mle (initialTable x output q) (initialPoint t) = _ at hi
  rw [initialPoint_instances,initialPoint_slots] at hi
  rw [hi]
  change mle (fun slot => mle (fun b => initialError x output q b slot) t.instancePoint)
    (Fin.cons t.segment t.lanePoint) = _
  let a : Fin 2 → Fin 32 → E := fun m l =>
    mle (fun b => initialError x output q b ⟨m.val+2*l.val,by omega⟩) t.instancePoint
  have ha : (fun slot : Fin 64 => a ⟨slot.val%2,Nat.mod_lt _ (by decide)⟩ ⟨slot.val/2,by omega⟩) =
      (fun slot => mle (fun b => initialError x output q b slot) t.instancePoint) := by
    funext slot
    have he : (⟨slot.val%2+2*(slot.val/2),by omega⟩ : Fin 64) = slot := by
      apply Fin.ext; dsimp only; omega
    dsimp only [a]
    rw [he]
  have hstart := congrArg (fun f : Fin 64 → E => mle f (Fin.cons t.segment t.lanePoint)) ha
  change mle (fun slot : Fin 64 => a ⟨slot.val%2,Nat.mod_lt _ (by decide)⟩ ⟨slot.val/2,by omega⟩)
    (Fin.cons t.segment t.lanePoint) = _ at hstart
  refine hstart.symm.trans ?_
  rw [mle_segment_lane,Fin.sum_univ_add (a := 25) (b := 7)]
  have hreal (m : Fin 2) (l : Fin 25) : a m (Fin.castAdd 7 l) =
      if m.val = 0 then middleWord x q t ⟨25+l.val,by omega⟩ - mle (fun b => segmentLane x q b 0 l) t.instancePoint
      else mle (fun b => output b l) t.instancePoint - mle (fun b => segmentLane x q b 1 l) t.instancePoint := by
    dsimp only [a]
    have he (b : Fin (2^(p+4))) := initialError_at x output q b m l
    simp only [Fin.val_castAdd] at *
    simp_rw [he]
    split <;> simp only [mle_sub,middleWord]
  have hpad (m : Fin 2) (l : Fin 7) : a m (Fin.natAdd 25 l) = 0 := by
    have hl : ¬(m.val+2*(25+l.val))/2 < 25 := by omega
    simp only [a,Fin.val_natAdd,initialError,hl,dite_false,mle,mul_zero,Finset.sum_const_zero]
  simp only [hreal,hpad,Fin.val_zero,Fin.val_one,ite_true,one_ne_zero,ite_false,
    mul_zero,add_zero,Finset.sum_const_zero,Fin.val_castAdd,Finset.mul_sum]
  simp only [mul_add,Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro l _ <;> ring

/-- A correct sampled first claim and middle claim force the initial mismatch polynomial to vanish. -/
theorem initial_claim_zero {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p) (t : Transcript E p)
    (middle : MiddleHolds x q t) (claim : ClaimHolds q 0 (firstClaim x output t)) :
    mle (initialTable x output q) (initialPoint t) = 0 := by
  rw [initial_table_identity]
  have h := (first_claim_identity x output q t).mp claim
  dsimp only [firstClaim,outputClaimAt] at h
  rw [middle] at h
  simp only [mul_sub,Finset.sum_sub_distrib,mul_sub] at h ⊢
  linear_combination h

/-- Sampling a false committed discrepancy table loses at most one root per initial coordinate. -/
theorem initial_sampling_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (hx : IndependentLanePowers x) (output : Fin (2^(p+4)) → Fin 25 → E)
    (q : Witness p) (wrong : ¬ InputRelation x output q) :
    Pr{let r ← runCoordinates E (p+10)}[mle (initialTable x output q) r = 0] ≤
      (p+10 : ENNReal) / Fintype.card E := by
  have hd : CoordinateDegree (mle (initialTable x output q)) 1 := by
    simpa only [mle_eq_eval] using coordinateDegree_eval (MvPolynomial.MLE' (initialTable x output q))
      (tablePolynomial_degree (initialTable x output q))
  obtain ⟨b,slot,he⟩ := initialError_nonzero x hx output q wrong
  let w : Fin (2^(p+10)) := ⟨b.val+2^(p+4)*slot.val,by
    have h := (finProdFinEquiv (slot,b)).isLt
    change b.val+2^(p+4)*slot.val < 64*2^(p+4) at h
    simpa only [show p+10=p+4+6 by omega,pow_add,show (2^6 : Nat)=64 by decide,
      Nat.mul_comm,Nat.add_comm] using h⟩
  have hw : initialTable x output q w = initialError x output q b slot := by
    dsimp only [initialTable,w]
    have hm : (b.val+2^(p+4)*slot.val)%2^(p+4) = b.val := by
      simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt b.isLt]
    have hd : (b.val+2^(p+4)*slot.val)/2^(p+4) = slot.val := by
      rw [Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt b.isLt,Nat.zero_add]
    simp only [hm,hd,Fin.eta]
  have hn : ∃ r, mle (initialTable x output q) r ≠ 0 :=
    ⟨cubePoint w,by rw [mle_cubePoint,hw]; exact he⟩
  simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,mul_one] using runCoordinates_zero_bound (p+10) 1 _ hd hn

end CompStark.Keccak.Gkr
