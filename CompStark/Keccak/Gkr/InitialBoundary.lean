/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.OpeningBoundaries

/-! # The initial random identity and the two Keccak output tables -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
@[expose] public section
open Polynomial
open scoped BigOperators
namespace CompStark.Keccak.Gkr

/-- Decomposing an instance into low four bits and a pack index preserves its index. -/
theorem packInstance_recompose {p : Nat} (w : Fin (2^(p+4))) :
    packInstance ⟨w.val%16,Nat.mod_lt _ (by decide)⟩
      ⟨w.val/16,by
        apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
        simpa only [pow_add, show (2^4 : Nat)=16 by decide, Nat.mul_comm] using w.isLt⟩ = w := by
  apply Fin.ext
  exact Nat.mod_add_div w.val 16

/-- Multilinear evaluation of instances splits into low-four and pack weights. -/
theorem mle_packs {E : Type*} [CommRing E] {p : Nat}
    (a : Fin (2^(p+4)) → E) (r : Fin (p+4) → E) :
    mle a r = ∑ b : Fin (2^p), ∑ low : Fin 16,
      eqWeight (fun i : Fin p => r ⟨i.val+4,by omega⟩) b.val *
      eqWeight (fun i : Fin 4 => r ⟨i.val,by omega⟩) low.val * a (packInstance low b) := by
  have h := mle_blocks (n := p+4) (a := 4) (b := p) (by omega)
    (fun low b => a (packInstance low b)) r
  simp only [show (2^4 : Nat)=16 by decide, packInstance_recompose, mle, Finset.mul_sum] at h
  have hi : (fun i : Fin p => r ⟨4+i.val,by omega⟩) = (fun i : Fin p => r ⟨i.val+4,by omega⟩) := by
    funext i; exact congrArg r (Fin.ext (Nat.add_comm 4 i.val))
  rw [hi] at h
  convert h using 1
  · rfl
  · simp only [mul_assoc]
    rfl

/-- A lane after the twelve rounds of one committed segment. -/
def segmentLane {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (q : Witness p) (b : Fin (2^(p+4))) (m : Fin 2) (l : Fin 25) : E :=
  laneValue x (fun z => segmentState q b m 12 (by omega) ⟨64*l.val+z.val,by omega⟩)

/-- The unsegmented first-claim sum is the multilinear batch of actual segment output lanes. -/
theorem first_segment_pairing {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (q : Witness p) (t : Transcript E p) (m : Fin 2) :
    (∑ b : Fin (2^p), ∑ low : Fin 16, ∑ j : Fin 1600,
      eqWeight (fun i : Fin p => t.instancePoint ⟨i.val+4,by omega⟩) b.val *
      eqWeight (fun i : Fin 4 => t.instancePoint ⟨i.val,by omega⟩) low.val *
      (eqWeight t.lanePoint (j.val/64)*x^(j.val%64)) *
      ZMod.castHom (dvd_refl 2) E
        (segmentState q (packInstance low b) m 12 (by omega) j)) =
      ∑ l : Fin 25, eqWeight t.lanePoint l.val * mle (fun b => segmentLane x q b m l) t.instancePoint := by
  simp_rw [position_sum]
  have hdiv (l : Fin 25) (z : Fin 64) : (64*l.val+z.val)/64 = l.val := by omega
  have hmod (l : Fin 25) (z : Fin 64) : (64*l.val+z.val)%64 = z.val := by omega
  simp only [hdiv,hmod,mle_packs,segmentLane,laneValue,Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 16))) (t := (Finset.univ : Finset (Fin 25)))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro low _
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- The first layer claim is the weighted pair of true segment outputs. -/
theorem first_claim_identity {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p) (t : Transcript E p) :
    ClaimHolds q 0 (firstClaim x output t) ↔
      (firstClaim x output t).value =
        (1-t.segment) * ∑ l : Fin 25, eqWeight t.lanePoint l.val *
          mle (fun b => segmentLane x q b 0 l) t.instancePoint +
        t.segment * ∑ l : Fin 25, eqWeight t.lanePoint l.val *
          mle (fun b => segmentLane x q b 1 l) t.instancePoint := by
  unfold ClaimHolds
  simp only [Fin.val_zero, Nat.sub_zero, firstClaim, eqWeight_last,
    Fin.lastCases_last, Fin.lastCases_castSucc]
  apply (congrArg (fun v : E => (firstClaim x output t).value = v) ?_).to_iff
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, ite_true, one_ne_zero, ite_false]
  have h0 := first_segment_pairing x q t 0
  have h1 := first_segment_pairing x q t 1
  rw [← h0,← h1]
  simp only [Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro b _ <;>
    apply Finset.sum_congr rfl <;> intro low _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

/-- Independent lane powers make the bit-to-lane encoding injective. -/
theorem laneValue_injective {E : Type*} [CommRing E] [CharP E 2] (x : E)
    (hx : IndependentLanePowers x) : Function.Injective (laneValue x) := by
  intro a b hab
  have hz : laneValue x (fun z => a z-b z) = 0 := by
    simp only [laneValue,map_sub,sub_mul,Finset.sum_sub_distrib,sub_eq_zero]
    exact hab
  have h := hx _ hz
  funext z
  exact sub_eq_zero.mp (h z)

/-- One of the fifty initial discrepancies; the segment is the low slot bit. -/
def initialError {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p)
    (b : Fin (2^(p+4))) (slot : Fin 64) : E :=
  if h : slot.val/2 < 25 then
    if slot.val%2 = 0 then laneValue x (q b ⟨25+slot.val/2,by omega⟩) - segmentLane x q b 0 ⟨slot.val/2,h⟩
    else output b ⟨slot.val/2,h⟩ - segmentLane x q b 1 ⟨slot.val/2,h⟩
  else 0

/-- The error table at an actual segment and lane has its stated semantic discrepancy. -/
theorem initialError_at {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p)
    (b : Fin (2^(p+4))) (m : Fin 2) (l : Fin 25) :
    initialError x output q b ⟨m.val+2*l.val,by omega⟩ =
      if m.val = 0 then laneValue x (q b ⟨25+l.val,by omega⟩) - segmentLane x q b 0 l
      else output b l - segmentLane x q b 1 l := by
  have hd : (m.val+2*l.val)/2 = l.val := by omega
  have hm : (m.val+2*l.val)%2 = m.val := by omega
  simp only [initialError,hd,hm,l.isLt,dite_true,Fin.eta]

/-- False output or chain tables give a nonzero entry before any challenge is drawn. -/
theorem initialError_nonzero {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (hx : IndependentLanePowers x) (output : Fin (2^(p+4)) → Fin 25 → E)
    (q : Witness p) (wrong : ¬ InputRelation x output q) :
    ∃ b slot, initialError x output q b slot ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply wrong
  constructor
  · intro b j
    let l : Fin 25 := ⟨j.val/64,by omega⟩
    have hh := h b ⟨2*l.val,by omega⟩
    have he := initialError_at x output q b 0 l
    simp only [Fin.val_zero, Nat.zero_add, ite_true] at he
    rw [he] at hh
    have hh' := sub_eq_zero.mp hh
    unfold segmentLane at hh'
    have lanes := @laneValue_injective E _ _ x hx (q b ⟨25+l.val,by omega⟩)
      (fun z => segmentState q b 0 12 (by omega) ⟨64*l.val+z.val,by omega⟩) hh'
    have bits := congrFun lanes (⟨j.val%64,by omega⟩ : Fin 64)
    have hj : (⟨64*l.val+j.val%64,by omega⟩ : Fin 1600) = j := by
      apply Fin.ext
      dsimp only [l]
      omega
    change q b ⟨25+l.val,by omega⟩ ⟨j.val%64,by omega⟩ =
      segmentState q b 0 12 (by omega) ⟨64*l.val+j.val%64,by omega⟩ at bits
    rw [hj] at bits
    exact bits.symm

  · intro b l
    have hh := h b ⟨1+2*l.val,by omega⟩
    have he := initialError_at x output q b 1 l
    simp only [Fin.val_one] at he
    rw [he] at hh
    simpa only [Fin.val_one, one_ne_zero, ite_false, segmentLane, Nat.add_comm] using sub_eq_zero.mp hh

end CompStark.Keccak.Gkr
