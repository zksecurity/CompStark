/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.LayerExecution

/-! # Adaptive union bound through consecutive Keccak layers -/

set_option maxHeartbeats 800000
@[expose] public section
open OracleComp
open scoped BigOperators ENNReal
namespace CompStark.Keccak.Gkr

/-- The claim at one boundary of a consecutive sequence of layer transcripts. -/
noncomputable def sequenceClaim {E : Type} [CommRing E] [CharP E 2] {p n : Nat}
    (c : Claim E p) (ts : Fin n → LayerTranscript E p) (i : Fin (n+1)) : Claim E p :=
  if h : i.val = 0 then c else nextClaim (ts ⟨i.val-1,by omega⟩)

/-- The first boundary is the supplied entering claim. -/
theorem sequenceClaim_zero {E : Type} [CommRing E] [CharP E 2] {p n : Nat}
    (c : Claim E p) (ts : Fin n → LayerTranscript E p) : sequenceClaim c ts 0 = c := rfl

/-- Removing the first layer leaves exactly the next layer's entering claim. -/
theorem sequenceClaim_cons_succ {E : Type} [CommRing E] [CharP E 2] {p n : Nat}
    (c : Claim E p) (t : LayerTranscript E p) (ts : Fin n → LayerTranscript E p) (i : Fin (n+1)) :
    sequenceClaim c (Fin.cons t ts) i.succ = sequenceClaim (nextClaim t) ts i := by
  unfold sequenceClaim
  simp only [Fin.val_succ, show i.val+1 ≠ 0 by omega, dite_false, Nat.add_sub_cancel]
  by_cases h : i.val = 0
  · simp only [h,dite_true]
    have hi : i = 0 := Fin.ext h
    subst i
    rfl
  · simp only [h,dite_false]
    have hi : (⟨i.val,by omega⟩ : Fin (n+1)) = (⟨i.val-1,by omega⟩ : Fin n).succ := by
      apply Fin.ext; simp only [Fin.val_succ]; omega
    rw [hi,Fin.cons_succ]

/-- The checks on a consecutive sequence retain each exact entering claim. -/
noncomputable def SequenceValid {E : Type} [CommRing E] [CharP E 2] {p n : Nat}
    (start : Nat) (h : start+n ≤ 12) (c : Claim E p) (ts : Fin n → LayerTranscript E p) : Prop :=
  ∀ i : Fin n, layerValid ⟨start+i.val,by omega⟩ (sequenceClaim c ts i.castSucc) (ts i)

/-- Sequence checks split into the first layer and its remaining adaptive layers. -/
theorem sequenceValid_cons {E : Type} [CommRing E] [CharP E 2] {p n : Nat}
    (start : Nat) (h : start+(n+1) ≤ 12) (c : Claim E p)
    (t : LayerTranscript E p) (ts : Fin n → LayerTranscript E p) :
    SequenceValid start h c (Fin.cons t ts) ↔
      layerValid ⟨start,by omega⟩ c t ∧
        SequenceValid (start+1) (by omega) (nextClaim t) ts := by
  rw [SequenceValid,Fin.forall_fin_succ]
  simp only [Fin.val_zero,Nat.add_zero,Fin.cons_zero,Fin.castSucc_zero,sequenceClaim_zero,
    Fin.cons_succ,Fin.val_succ]
  apply and_congr Iff.rfl
  unfold SequenceValid
  apply forall_congr'
  intro i
  have he : i.succ.castSucc = i.castSucc.succ := rfl
  rw [he,sequenceClaim_cons_succ]
  have hd : (⟨start+(i.val+1),by omega⟩ : Fin 12) = ⟨start+1+i.val,by omega⟩ := by
    apply Fin.ext; dsimp only; omega
  rw [hd]

/-- Wire messages for a consecutive sequence of complete layer transcripts. -/
def sequenceMessages {E : Type} {p n : Nat} (ts : Fin n → LayerTranscript E p) : List (List E) :=
  (List.ofFn fun i => layerMessages (ts i)).flatten

/-- The first layer's messages precede every message of the remaining layers. -/
theorem sequenceMessages_cons {E : Type} {p n : Nat} (t : LayerTranscript E p)
    (ts : Fin n → LayerTranscript E p) :
    sequenceMessages (Fin.cons t ts) = layerMessages t ++ sequenceMessages ts := by
  simp only [sequenceMessages,List.ofFn_succ,Fin.cons_zero,Fin.cons_succ,List.flatten_cons]

/-- Execute consecutive layers, retaining the full wire history for every later prover message. -/
noncomputable def runLayerSequence (E : Type) [Fintype E] [Nonempty E] [Zero E] (p : Nat)
    (prover : Prover E) : (n : Nat) → List (List E) → ProbComp (Fin n → LayerTranscript E p)
  | 0, _ => pure Fin.elim0
  | n+1, history => do
      let t ← runLayer E p prover history
      let tail ← runLayerSequence E p prover n (history ++ layerMessages t)
      pure (Fin.cons t tail)

/-- Consecutive adaptive layers lose the sum of their concrete phase numerators. -/
theorem runLayerSequence_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (q : Witness p) (prover : Prover E) (n start : Nat) (h : start+n ≤ 12)
    (history : List (List E)) (c : Claim E p)
    (wrong : ¬ ClaimHolds q ⟨start,by omega⟩ c) :
    Pr{let ts ← runLayerSequence E p prover n history}[
      SequenceValid start h c ts ∧ ClaimHolds q ⟨start+n,by omega⟩ (sequenceClaim c ts (Fin.last n))] ≤
      (n*(3*p+84) : ENNReal) / Fintype.card E := by
  induction n generalizing start history c with
  | zero =>
    simp only [runLayerSequence,sequenceClaim,Fin.val_last,dite_true,Nat.add_zero]
    simp only [wrong,and_false,Nat.cast_zero,zero_mul,ENNReal.zero_div,prEvent_false,zero_le]
  | succ n ih =>
    let event := fun t : LayerTranscript E p => layerValid ⟨start,by omega⟩ c t ∧
      ClaimHolds q ⟨start+1,by omega⟩ (nextClaim t)
    have hfirst := runLayer_bound q ⟨start,by omega⟩ c prover history wrong
    have hb := prEvent_bind_le_prEvent_add_of_support (runLayer E p prover history)
      (fun t => Fin.cons t <$> runLayerSequence E p prover n (history ++ layerMessages t)) event
      (fun ts => SequenceValid start h c ts ∧
        ClaimHolds q ⟨start+(n+1),by omega⟩ (sequenceClaim c ts (Fin.last (n+1))))
      (ε := (n*(3*p+84) : ENNReal) / Fintype.card E) (by
        intro t _ bad
        rw [prEvent_map]
        by_cases valid : layerValid ⟨start,by omega⟩ c t
        · have hw : ¬ ClaimHolds q ⟨start+1,by omega⟩ (nextClaim t) := fun good => bad ⟨valid,good⟩
          have ht := ih (start+1) (by omega) (history ++ layerMessages t) (nextClaim t) hw
          have hn : (⟨start+(n+1),by omega⟩ : Fin 13) = ⟨start+1+n,by omega⟩ := by
            apply Fin.ext; dsimp only; omega
          simpa only [sequenceValid_cons,valid,true_and,show Fin.last (n+1) = (Fin.last n).succ from rfl,
            sequenceClaim_cons_succ,hn] using ht
        · simp only [sequenceValid_cons,valid,false_and,prEvent_false,zero_le])
    have hrun : runLayerSequence E p prover (n+1) history =
        (runLayer E p prover history >>= fun t => Fin.cons t <$>
          runLayerSequence E p prover n (history ++ layerMessages t)) := by
      simp only [runLayerSequence,map_eq_bind_pure_comp,Function.comp_def]
    rw [hrun]
    refine (hb.trans (add_le_add hfirst le_rfl)).trans ?_
    rw [← ENNReal.add_div]
    have he : (3*p+84 : ENNReal)+n*(3*p+84) = (n+1)*(3*p+84) := by ring
    simpa only [Nat.cast_add,Nat.cast_one] using le_of_eq (congrArg (fun v : ENNReal => v / Fintype.card E) he)

end CompStark.Keccak.Gkr
