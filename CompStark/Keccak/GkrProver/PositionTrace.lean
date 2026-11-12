/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.PositionHonest

/-! Structural trace and honest-message invariants for the native position sumcheck loop. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr BF64

/-- The native position accumulator always returns the three transmitted cubic coefficients. -/
theorem positionRows_size (weights : Array W) (t : Array (Array W)) (kappa : W) (row : Nat)
    (z0 z1 z2 q0 q1 q2 c0 c1 c2 : UInt64) :
    (positionRows weights t kappa row z0 z1 z2 q0 q1 q2 c0 c1 c2).size = 3 := by
  rw [positionRows]
  split
  · apply positionRows_size
  · rfl
termination_by weights.size/2-row

/-- Every native position message has one constant and two retained higher coefficients. -/
theorem positionRound_size (weights : Array W) (t : Array (Array W)) (kappa : W) :
    (positionRound weights t kappa).size = 3 := positionRows_size ..

/-- Interpret the transmitted native position coefficients in the specification's compressed format. -/
def positionMessageOfArray (message : Array W) : Sumcheck.CompressedMessage W 2 :=
  (message[0]!,fun k => message[k.val+1]!)

/-- Scaling the actual native position coefficient array gives the exact honest first message. -/
theorem positionMessageOfArray_honest (weights : Array W) (t : Array (Array W)) (n : Nat)
    (scale kappa : W) (hw : weights.size = 2^(n+1))
    (ht : ∀ k : Fin 3,(t[k.val]!).size = 2^(n+1))
    (hf : CoordinateDegree (positionTableSummand weights t (n+1) scale kappa) 3) :
    positionMessageOfArray ((positionRound weights t kappa).map (scale*·)) =
      Sumcheck.compress (firstHonestPolynomial (positionTableSummand weights t (n+1) scale kappa) hf) := by
  rw [← positionRound_honest weights t n scale kappa hw ht hf]
  apply Prod.ext
  · change ((positionRound weights t kappa).map (scale*·))[0]! = _
    rw [getElem!_pos _ _ (by rw [Array.size_map,positionRound_size]; decide),Array.getElem_map,
      ← getElem!_pos _ _ (by rw [positionRound_size]; decide)]
  · funext k
    change ((positionRound weights t kappa).map (scale*·))[k.val+1]! = _
    rw [getElem!_pos _ _ (by rw [Array.size_map,positionRound_size]; have := k.isLt; omega),
      Array.getElem_map,← getElem!_pos _ _ (by rw [positionRound_size]; have := k.isLt; omega)]

/-- Retained factors, coordinates, messages and duplex state of the native position loop. -/
structure PositionResult where
  /-- Multilinear position weights. -/
  weights : Array W
  /-- The three shifted position-factor tables. -/
  factors : Array (Array W)
  /-- Sampled low-to-high position coordinates. -/
  point : Array W
  /-- Transmitted compressed cubic coefficient arrays. -/
  messages : Array (Array W)
  /-- Duplex state after the final sampled coordinate. -/
  writer : Writer

/-- One native position transition with both shared-map folding branches normalized. -/
def positionStep (scale kappa : W) (state : PositionResult) : PositionResult :=
  let message := (positionRound state.weights state.factors kappa).map (scale*·)
  let (r,writer) := (state.writer.writeAll message).sample
  ⟨fold state.weights 1 r,state.factors.map (fun a => fold a 1 r),
    state.point.push r,state.messages.push message,writer⟩

/-- Structural iteration of the native position message-and-fold transition. -/
def positionRun (scale kappa : W) (initial : PositionResult) : Nat → PositionResult
  | 0 => initial
  | n+1 => positionStep scale kappa (positionRun scale kappa initial n)

/-- The production position-loop body, including its shared prepared-map folding branches. -/
def positionLoop (writer : Writer) (weights : Array W) (factors : Array (Array W))
    (scale kappa : W) (rounds : Nat) : PositionResult := Id.run do
  let mut weights := weights
  let mut factors := factors
  let mut writer := writer
  let mut point := #[]
  let mut messages := #[]
  for _ in [:rounds] do
    let message := (positionRound weights factors kappa).map (scale*·)
    let (r,next) := (writer.writeAll message).sample
    writer := next
    messages := messages.push message
    point := point.push r
    if 1024 ≤ weights.size then
      let map := CompStark.Sumcheck.prepare r
      weights := foldArrayShared weights 1 map
      factors := factors.map fun a => foldArrayShared a 1 map
    else
      weights := fold weights 1 r
      factors := factors.map fun a => fold a 1 r
  return ⟨weights,factors,point,messages,writer⟩

/-- A structural position run is its exact natural-range transition fold. -/
theorem positionRun_eq_fold (scale kappa : W) (initial : PositionResult) (n : Nat) :
    positionRun scale kappa initial n =
      (List.range n).foldl (fun state _ => positionStep scale kappa state) initial := by
  induction n with
  | zero => rfl
  | succ n ih => rw [positionRun,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,ih]

/-- The production position-loop body is the complete structurally recursive message-and-fold run. -/
theorem positionLoop_eq_run (writer : Writer) (weights : Array W) (factors : Array (Array W))
    (scale kappa : W) (rounds : Nat) :
    positionLoop writer weights factors scale kappa rounds =
      positionRun scale kappa ⟨weights,factors,#[],#[],writer⟩ rounds := by
  rw [positionRun_eq_fold]
  simp only [positionLoop,foldArrayShared_eq,ite_self,Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure,Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range']
  let view (state : Array W × Array (Array W) × Writer × Array W × Array (Array W)) : PositionResult :=
    ⟨state.1,state.2.1,state.2.2.2.1,state.2.2.2.2,state.2.2.1⟩
  change view _ = _
  symm
  apply List.foldl_hom view (init := (weights,factors,writer,#[],#[]))
  intro state i
  rfl

/-- Position iteration can expose its first transition before the remaining recursive run. -/
theorem positionRun_succ_first (scale kappa : W) (initial : PositionResult) (n : Nat) :
    positionRun scale kappa initial (n+1) = positionRun scale kappa (positionStep scale kappa initial) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [positionRun,ih,positionRun]

/-- Every native position transition appends exactly one message and one sampled coordinate. -/
theorem positionRun_lengths (scale kappa : W) (initial : PositionResult) (n : Nat) :
    (positionRun scale kappa initial n).point.size = initial.point.size+n ∧
      (positionRun scale kappa initial n).messages.size = initial.messages.size+n := by
  induction n with
  | zero => exact ⟨(Nat.add_zero _).symm,(Nat.add_zero _).symm⟩
  | succ n ih =>
    simp only [positionRun,positionStep,Array.size_push,ih.1,ih.2,Nat.add_assoc]
    trivial

/-- The position run preserves all coordinates and messages already in its entering prefix. -/
theorem positionRun_prefix (scale kappa : W) (initial : PositionResult) (n : Nat) :
    (∀ i,i < initial.point.size → (positionRun scale kappa initial n).point[i]! = initial.point[i]!) ∧
      (∀ i,i < initial.messages.size → (positionRun scale kappa initial n).messages[i]! = initial.messages[i]!) := by
  induction n with
  | zero => exact ⟨fun _ _ => rfl,fun _ _ => rfl⟩
  | succ n ih =>
    constructor
    · intro i hi
      rw [positionRun]
      dsimp only [positionStep]
      rw [array_push_get_old _ _ _ (by rw [(positionRun_lengths scale kappa initial n).1]; omega),ih.1 i hi]
    · intro i hi
      rw [positionRun]
      dsimp only [positionStep]
      rw [array_push_get_old _ _ _ (by rw [(positionRun_lengths scale kappa initial n).2]; omega),ih.2 i hi]

/-- Every position message follows the honest cubic strategy of the entering native factor buffers. -/
theorem positionRun_honest (initial : PositionResult) (scale kappa : W) (n : Nat)
    (hw : initial.weights.size = 2^n) (hs : initial.factors.size = 3)
    (ht : ∀ k : Fin 3,(initial.factors[k.val]!).size = 2^n) (i : Fin n) :
    positionMessageOfArray (positionRun scale kappa initial n).messages[initial.messages.size+i.val]! =
      honestCompressedRounds (positionTableSummand initial.weights initial.factors n scale kappa)
        (positionTableSummand_degree initial.weights initial.factors n scale kappa)
        (fun j => (positionRun scale kappa initial n).point[initial.point.size+j.val]!) i := by
  induction n generalizing initial with
  | zero => exact i.elim0
  | succ n ih =>
    let next := positionStep scale kappa initial
    let r := ((initial.writer.writeAll
      ((positionRound initial.weights initial.factors kappa).map (scale*·))).sample).1
    have hnw : next.weights.size = 2^n := fold_size _ hw r
    have hns : next.factors.size = 3 := by dsimp only [next,positionStep]; rw [Array.size_map,hs]
    have hget (k : Nat) (hk : k < 3) : next.factors[k]! = fold initial.factors[k]! 1 r := by
      dsimp only [next,positionStep]
      rw [getElem!_pos _ _ (by rw [Array.size_map,hs]; exact hk),Array.getElem_map,
        ← getElem!_pos initial.factors _ (by rw [hs]; exact hk)]
    have hnt (k : Fin 3) : (next.factors[k.val]!).size = 2^n := by
      rw [hget k.val k.isLt]
      exact fold_size _ (ht k) r
    have hpoint : (positionRun scale kappa next n).point[initial.point.size]! = r := by
      rw [(positionRun_prefix scale kappa next n).1 _ (by
        dsimp only [next,positionStep]; rw [Array.size_push]; omega)]
      dsimp only [next,positionStep]
      exact array_push_get_last _ _
    rw [positionRun_succ_first]
    change positionMessageOfArray (positionRun scale kappa next n).messages[initial.messages.size+i.val]! = _
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.val_zero,Nat.add_zero]
      rw [(positionRun_prefix scale kappa next n).2 _ (by
        dsimp only [next,positionStep]; rw [Array.size_push]; omega)]
      dsimp only [next,positionStep]
      rw [array_push_get_last,honestCompressedRounds,Fin.cons_zero]
      exact positionMessageOfArray_honest initial.weights initial.factors n scale kappa hw ht _
    · rw [honestCompressedRounds,Fin.cons_succ]
      have heq :
          (fun rest => positionTableSummand initial.weights initial.factors (n+1) scale kappa
            (Fin.cons ((positionRun scale kappa next n).point[initial.point.size+0]!) rest)) =
          positionTableSummand next.weights next.factors n scale kappa := by
        funext rest
        simp only [Nat.add_zero]
        rw [hpoint]
        exact (positionTableSummand_fold initial.weights initial.factors n scale kappa r hw ht rest).symm
      have hh := ih next hnw hns hnt j
      have hcongr := honestCompressedRounds_congr
        ((positionTableSummand_degree initial.weights initial.factors (n+1) scale kappa).tail
          (positionRun scale kappa next n).point[initial.point.size+0]!)
        (positionTableSummand_degree next.weights next.factors n scale kappa) heq
        (fun k : Fin n => (positionRun scale kappa next n).point[initial.point.size+k.succ.val]!)
        (fun k : Fin n => (positionRun scale kappa next n).point[next.point.size+k.val]!) (by
          funext k
          dsimp only [next,positionStep]
          simp only [Array.size_push,Fin.val_succ,Nat.add_assoc,Nat.add_comm 1])
      trans honestCompressedRounds (positionTableSummand next.weights next.factors n scale kappa)
        (positionTableSummand_degree next.weights next.factors n scale kappa)
        (fun k => (positionRun scale kappa next n).point[next.point.size+k.val]!) j
      · simpa only [next,positionStep,Array.size_push,Fin.val_succ,Nat.add_assoc,Nat.add_comm 1] using hh
      · exact (congrFun hcongr j).symm

/-- The actual position-loop body emits the honest cubic strategy for its supplied factor buffers. -/
theorem positionLoop_honest (writer : Writer) (weights : Array W) (factors : Array (Array W))
    (scale kappa : W) (n : Nat) (hw : weights.size = 2^n) (hs : factors.size = 3)
    (ht : ∀ k : Fin 3,(factors[k.val]!).size = 2^n) :
    let final := positionLoop writer weights factors scale kappa n
    (fun i : Fin n => positionMessageOfArray final.messages[i.val]!) =
      honestCompressedRounds (positionTableSummand weights factors n scale kappa)
        (positionTableSummand_degree weights factors n scale kappa) (fun i => final.point[i.val]!) := by
  rw [positionLoop_eq_run]
  funext i
  simpa only [Array.size_empty,Nat.zero_add] using
    positionRun_honest ⟨weights,factors,#[],#[],writer⟩ scale kappa n hw hs ht i

end CompStark.Keccak.GkrProver
