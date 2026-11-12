/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.PackBoundary
public import CompStark.Keccak.GkrProver.PositionTerminal

/-! Structural remaining-sum invariants for the retained-table pack rounds. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr BF64
open scoped BigOperators

/-- Retained table, running claim and transcript data of a native pack-round suffix. -/
structure PackResult where
  /-- Remaining row-major RMFE factor table. -/
  table : PackedE
  /-- Product of already bound equality-coordinate factors. -/
  scale : W
  /-- Exact equality-weighted remaining cofactor sum. -/
  value : W
  /-- Sampled pack coordinates. -/
  point : Array W
  /-- Transmitted cofactor-tail arrays. -/
  messages : Array (Array W)
  /-- Duplex state after the most recent sampled coordinate. -/
  writer : Writer

/-- One native retained-table pack transition, including claim reconstruction, sampling and folding. -/
def latePackStep (weights suffix : Array W) (kappa entering : W) (state : PackResult) : PackResult :=
  let coefficients := packRoundFromClaim state.table weights (packConstants weights kappa)
    (eqTable suffix) entering state.scale state.value
  let message := #[coefficients[1]!,coefficients[2]!]
  let (r,writer) := (state.writer.writeAll message).sample
  ⟨foldPacked state.table 1600 r,state.scale*(1+entering+r),
    (1+entering+r)*(coefficients[0]!+r*(coefficients[1]!+r*coefficients[2]!)),
    state.point.push r,state.messages.push message,writer⟩

/-- Structural iteration over the entering equality coordinates of the retained-table pack rounds. -/
def latePackRun (weights : Array W) (kappa : W) : List W → PackResult → PackResult
  | [],state => state
  | entering::suffix,state => latePackRun weights kappa suffix
      (latePackStep weights suffix.toArray kappa entering state)

/-- Little-endian coordinates of a list split into its head and its remaining suffix. -/
theorem listPoint_cons (entering : W) (suffix : List W) :
    (fun k : Fin (entering::suffix).length => (entering::suffix)[k.val]!) =
      Fin.cons entering (fun k : Fin suffix.length => suffix[k.val]!) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp only [Fin.val_zero,List.getElem!_cons_zero,Fin.cons_zero]
  · simp only [Fin.val_succ,List.getElem!_cons_succ,Fin.cons_succ]

/-- The exact remaining Boolean sum represented by a retained native pack state. -/
noncomputable def packRemainingValue (weights : Array W) (kappa : W) (point : List W) (state : PackResult) : W :=
  booleanSum (fun rest => eqEval (fun k : Fin point.length => point[k.val]!) rest *
    packTableCofactor state.table weights point.length state.scale kappa rest)

/-- A native retained-table pack step preserves its exact remaining-sum invariant and row dimension. -/
theorem latePackStep_invariant (weights : Array W) (kappa entering : W) (suffix : List W) (state : PackResult)
    (ht : state.table.size = 2^(suffix.length+1)*1600)
    (hv : state.value = packRemainingValue weights kappa (entering::suffix) state) :
    let next := latePackStep weights suffix.toArray kappa entering state
    next.table.size = 2^suffix.length*1600 ∧ next.value = packRemainingValue weights kappa suffix next := by
  have hvcons := hv
  unfold packRemainingValue at hvcons
  rw [listPoint_cons] at hvcons
  have hv' : state.value = booleanSum (fun rest =>
      eqEval (Fin.cons entering (fun k : Fin suffix.toArray.size => suffix.toArray[k.val]!)) rest *
        packTableCofactor state.table weights (suffix.toArray.size+1) state.scale kappa rest) := by
    convert hvcons using 1
    simp only [List.getElem!_toArray,List.length_cons]
    congr 1
  have ht' : state.table.size = 2^(suffix.toArray.size+1)*1600 := by
    simpa only [List.size_toArray] using ht
  constructor
  · dsimp only [latePackStep]
    rw [foldPacked_size,ht,pow_succ]
    omega
  · have hh := packRoundFromClaim_update state.table weights suffix.toArray entering state.scale kappa
      state.value ((latePackStep weights suffix.toArray kappa entering state).point.back!) ht' hv'
    have hr : (latePackStep weights suffix.toArray kappa entering state).point.back! =
        ((state.writer.writeAll
          #[(packRoundFromClaim state.table weights (packConstants weights kappa) (eqTable suffix.toArray)
            entering state.scale state.value)[1]!,
            (packRoundFromClaim state.table weights (packConstants weights kappa) (eqTable suffix.toArray)
              entering state.scale state.value)[2]!]).sample).1 := by
      dsimp only [latePackStep]
      rw [Array.back!,Array.size_push,Nat.add_sub_cancel,array_push_get_last]
    rw [hr] at hh
    simp only [List.getElem!_toArray] at hh
    dsimp only [latePackStep,packRemainingValue]
    rw [hh]
    rw [mul_comm (1+entering+_) state.scale]
    congr 1

/-- Every retained-table pack round preserves the complete remaining-sum invariant through the terminal row. -/
theorem latePackRun_invariant (weights : Array W) (kappa : W) (point : List W) (state : PackResult)
    (ht : state.table.size = 2^point.length*1600)
    (hv : state.value = packRemainingValue weights kappa point state) :
    let final := latePackRun weights kappa point state
    final.table.size = 1600 ∧ final.value = packRemainingValue weights kappa [] final := by
  induction point generalizing state with
  | nil => exact ⟨ht,hv⟩
  | cons entering suffix ih =>
    have hh := latePackStep_invariant weights kappa entering suffix state ht hv
    exact ih _ hh.1 hh.2

/-- A retained-table pack run appends exactly one sampled point and one message per entering coordinate. -/
theorem latePackRun_lengths (weights : Array W) (kappa : W) (point : List W) (state : PackResult) :
    (latePackRun weights kappa point state).point.size = state.point.size+point.length ∧
      (latePackRun weights kappa point state).messages.size = state.messages.size+point.length := by
  induction point generalizing state with
  | nil => exact ⟨(Nat.add_zero _).symm,(Nat.add_zero _).symm⟩
  | cons entering suffix ih =>
    rw [latePackRun]
    obtain ⟨hp,hm⟩ := ih (latePackStep weights suffix.toArray kappa entering state)
    have hpoint : (latePackStep weights suffix.toArray kappa entering state).point.size = state.point.size+1 :=
      Array.size_push ..
    have hmessage : (latePackStep weights suffix.toArray kappa entering state).messages.size = state.messages.size+1 :=
      Array.size_push ..
    rw [hpoint] at hp
    rw [hmessage] at hm
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using And.intro hp hm

/-- A retained-table pack run preserves all coordinates and messages already in its entering prefix. -/
theorem latePackRun_prefix (weights : Array W) (kappa : W) (point : List W) (state : PackResult) :
    (∀ i,i < state.point.size → (latePackRun weights kappa point state).point[i]! = state.point[i]!) ∧
      (∀ i,i < state.messages.size → (latePackRun weights kappa point state).messages[i]! = state.messages[i]!) := by
  induction point generalizing state with
  | nil => exact ⟨fun _ _ => rfl,fun _ _ => rfl⟩
  | cons entering suffix ih =>
    let next := latePackStep weights suffix.toArray kappa entering state
    have hh := ih next
    constructor
    · intro i hi
      rw [latePackRun,hh.1 i (by dsimp only [next,latePackStep]; rw [Array.size_push]; omega)]
      dsimp only [next,latePackStep]
      exact array_push_get_old _ _ _ hi
    · intro i hi
      rw [latePackRun,hh.2 i (by dsimp only [next,latePackStep]; rw [Array.size_push]; omega)]
      dsimp only [next,latePackStep]
      exact array_push_get_old _ _ _ hi

/-- Interpret the two native pack-tail scalars as the protocol's cofactor message. -/
def cofactorMessageOfArray (message : Array W) : CofactorMessage W :=
  (message[0]!,fun _ => message[1]!)

/-- The native retained-table pack transition transmits the exact honest cofactor message. -/
theorem latePackStep_honest (weights suffix : Array W) (kappa entering : W) (state : PackResult)
    (ht : state.table.size = 2^(suffix.size+1)*1600)
    (hv : state.value = booleanSum (fun rest =>
      eqEval (Fin.cons entering (fun k : Fin suffix.size => suffix[k.val]!)) rest *
        packTableCofactor state.table weights (suffix.size+1) state.scale kappa rest)) :
    cofactorMessageOfArray (latePackStep weights suffix kappa entering state).messages[state.messages.size]! =
      let P := honestCofactorPolynomial (packTableCofactor state.table weights (suffix.size+1) state.scale kappa)
        (packTableCofactor_degree state.table weights (suffix.size+1) state.scale kappa)
        (fun k : Fin suffix.size => suffix[k.val]!)
      (P.val.coeff 1,fun _ => P.val.coeff 2) := by
  dsimp only [latePackStep]
  rw [array_push_get_last,packRoundPolynomial_honest state.table weights suffix state.scale kappa ht,
    packRoundFromClaim_refines state.table weights suffix entering state.scale kappa state.value ht hv]
  have hget (k : Nat) (hk : k < 3) :
      ((packRound state.table weights (packConstants weights kappa) (eqTable suffix)).map (state.scale*·))[k]! =
        state.scale*(packRound state.table weights (packConstants weights kappa) (eqTable suffix))[k]! := by
    rw [getElem!_pos _ _ (by rw [Array.size_map,packRound_size]; exact hk),Array.getElem_map,
      ← getElem!_pos _ _ (by rw [packRound_size]; exact hk)]
  simp only [hget 1 (by decide),hget 2 (by decide)]
  change (state.scale*(packRound state.table weights (packConstants weights kappa) (eqTable suffix))[1]!,
    fun _ => state.scale*(packRound state.table weights (packConstants weights kappa) (eqTable suffix))[2]!) = _
  have h1 := packRoundPolynomial_coeff state.table weights suffix state.scale kappa (1 : Fin 3)
  have h2 := packRoundPolynomial_coeff state.table weights suffix state.scale kappa (2 : Fin 3)
  simp only [Fin.val_one,show (2 : Fin 3).val = 2 from rfl] at h1 h2
  rw [h1,h2]

/-- Honest cofactor strategies agree under equal summands, entering points and sampled points. -/
theorem honestCofactorRounds_congr {n : Nat} {f g : (Fin n → W) → W}
    (hf : CoordinateDegree f 2) (hg : CoordinateDegree g 2) (hfg : f = g)
    (point other sampled otherSampled : Fin n → W) (hp : point = other) (hs : sampled = otherSampled) :
    honestCofactorRounds f hf point sampled = honestCofactorRounds g hg other otherSampled := by
  subst g
  subst other
  subst otherSampled
  rfl

/-- A complete retained-table pack run transmits the honest cofactor strategy at every sampled coordinate. -/
theorem latePackRun_honest (weights : Array W) (kappa : W) (point : List W) (state : PackResult)
    (ht : state.table.size = 2^point.length*1600)
    (hv : state.value = packRemainingValue weights kappa point state) (i : Fin point.length) :
    cofactorMessageOfArray (latePackRun weights kappa point state).messages[state.messages.size+i.val]! =
      honestCofactorRounds (packTableCofactor state.table weights point.length state.scale kappa)
        (packTableCofactor_degree state.table weights point.length state.scale kappa)
        (fun j => point[j.val]!)
        (fun j => (latePackRun weights kappa point state).point[state.point.size+j.val]!) i := by
  induction point generalizing state with
  | nil => exact i.elim0
  | cons entering suffix ih =>
    let next := latePackStep weights suffix.toArray kappa entering state
    let r := ((state.writer.writeAll
      #[(packRoundFromClaim state.table weights (packConstants weights kappa) (eqTable suffix.toArray)
        entering state.scale state.value)[1]!,
        (packRoundFromClaim state.table weights (packConstants weights kappa) (eqTable suffix.toArray)
          entering state.scale state.value)[2]!]).sample).1
    have hn := latePackStep_invariant weights kappa entering suffix state ht hv
    have hpoint : (latePackRun weights kappa suffix next).point[state.point.size]! = r := by
      rw [(latePackRun_prefix weights kappa suffix next).1 _ (by
        dsimp only [next,latePackStep]; rw [Array.size_push]; omega)]
      dsimp only [next,latePackStep]
      exact array_push_get_last _ _
    rw [latePackRun,listPoint_cons]
    change cofactorMessageOfArray (latePackRun weights kappa suffix next).messages[state.messages.size+i.val]! = _
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.val_zero,Nat.add_zero]
      rw [(latePackRun_prefix weights kappa suffix next).2 _ (by
        dsimp only [next,latePackStep]; rw [Array.size_push]; omega)]
      rw [honestCofactorRounds,Fin.cons_zero]
      have hv' : state.value = booleanSum (fun rest =>
          eqEval (Fin.cons entering (fun k : Fin suffix.toArray.size => suffix.toArray[k.val]!)) rest *
            packTableCofactor state.table weights (suffix.toArray.size+1) state.scale kappa rest) := by
        unfold packRemainingValue at hv
        rw [listPoint_cons] at hv
        convert hv using 1
        simp only [List.getElem!_toArray,List.length_cons]
        congr 1
      have hh := latePackStep_honest weights suffix.toArray kappa entering state
        (by simpa only [List.size_toArray,List.length_cons] using ht) hv'
      simp only [List.getElem!_toArray,Fin.cons_succ] at hh ⊢
      convert hh using 1
    · rw [honestCofactorRounds,Fin.cons_succ]
      have heq :
          (fun rest => (1+entering+(latePackRun weights kappa suffix next).point[state.point.size+0]!)*
            packTableCofactor state.table weights (suffix.length+1) state.scale kappa
              (Fin.cons ((latePackRun weights kappa suffix next).point[state.point.size+0]!) rest)) =
          packTableCofactor next.table weights suffix.length next.scale kappa := by
        funext rest
        simp only [Nat.add_zero,hpoint]
        dsimp only [next,latePackStep]
        rw [packTableCofactor_fold state.table weights suffix.length _ _ r ht,
          mul_comm state.scale (1+entering+r),packTableCofactor_scale]
      have hh := ih next hn.1 hn.2 j
      have hcongr := honestCofactorRounds_congr
        (coordinateDegree_scale_tail
          (packTableCofactor state.table weights (suffix.length+1) state.scale kappa)
          (packTableCofactor_degree state.table weights (suffix.length+1) state.scale kappa)
          (1+entering+(latePackRun weights kappa suffix next).point[state.point.size+0]!)
          (latePackRun weights kappa suffix next).point[state.point.size+0]!)
        (packTableCofactor_degree next.table weights suffix.length next.scale kappa) heq
        (fun k => suffix[k.val]!) (fun k => suffix[k.val]!)
        (fun k : Fin suffix.length => (latePackRun weights kappa suffix next).point[state.point.size+k.succ.val]!)
        (fun k : Fin suffix.length => (latePackRun weights kappa suffix next).point[next.point.size+k.val]!) rfl (by
          funext k
          dsimp only [next,latePackStep]
          simp only [Array.size_push,Fin.val_succ,Nat.add_assoc,Nat.add_comm 1])
      trans honestCofactorRounds (packTableCofactor next.table weights suffix.length next.scale kappa)
        (packTableCofactor_degree next.table weights suffix.length next.scale kappa)
        (fun k => suffix[k.val]!)
        (fun k => (latePackRun weights kappa suffix next).point[next.point.size+k.val]!) j
      · simpa only [next,latePackStep,Array.size_push,Fin.val_succ,Nat.add_assoc,Nat.add_comm 1] using hh
      · exact (congrFun hcongr j).symm

/-- The retained pack run returns the exact factor MLEs and complete equality-kernel scale. -/
theorem latePackRun_terminal (weights : Array W) (kappa : W) (point : List W) (state : PackResult)
    (ht : state.table.size = 2^point.length*1600) :
    let final := latePackRun weights kappa point state
    final.scale = state.scale*eqEval (fun k : Fin point.length => point[k.val]!)
      (fun k => final.point[state.point.size+k.val]!) ∧
      ∀ j : Fin 1600,final.table.toArray[j.val]! =
        mle (fun row : Fin (2^point.length) => state.table.toArray[row.val*1600+j.val]!)
          (fun k => final.point[state.point.size+k.val]!) := by
  induction point generalizing state with
  | nil =>
    constructor
    · simp only [List.length_nil,latePackRun,eqEval,Fin.prod_univ_zero,mul_one]
    · intro j
      rw [mle_no_coordinates]
      simp only [latePackRun,Fin.val_zero,Nat.zero_mul,Nat.zero_add]
  | cons entering suffix ih =>
    let next := latePackStep weights suffix.toArray kappa entering state
    let r := ((state.writer.writeAll
      #[(packRoundFromClaim state.table weights (packConstants weights kappa) (eqTable suffix.toArray)
        entering state.scale state.value)[1]!,
        (packRoundFromClaim state.table weights (packConstants weights kappa) (eqTable suffix.toArray)
          entering state.scale state.value)[2]!]).sample).1
    have hnt : next.table.size = 2^suffix.length*1600 := by
      dsimp only [next,latePackStep]
      rw [foldPacked_size,ht,List.length_cons,pow_succ]
      omega
    have hpoint : (latePackRun weights kappa suffix next).point[state.point.size]! = r := by
      rw [(latePackRun_prefix weights kappa suffix next).1 _ (by
        dsimp only [next,latePackStep]; rw [Array.size_push]; omega)]
      dsimp only [next,latePackStep]
      exact array_push_get_last _ _
    have hvector :
        (fun k : Fin (suffix.length+1) => (latePackRun weights kappa suffix next).point[state.point.size+k.val]!) =
          Fin.cons r (fun k : Fin suffix.length => (latePackRun weights kappa suffix next).point[next.point.size+k.val]!) := by
      funext k
      refine Fin.cases ?_ (fun k => ?_) k
      · simp only [Fin.val_zero,Nat.add_zero,Fin.cons_zero,hpoint]
      · dsimp only [next,latePackStep]
        simp only [Fin.val_succ,Fin.cons_succ,Array.size_push,Nat.add_assoc,Nat.add_comm 1]
    have hh := ih next hnt
    rw [latePackRun]
    change (latePackRun weights kappa suffix next).scale =
      state.scale*eqEval (fun k : Fin (suffix.length+1) => (entering::suffix)[k.val]!)
        (fun k => (latePackRun weights kappa suffix next).point[state.point.size+k.val]!) ∧
      ∀ j : Fin 1600,(latePackRun weights kappa suffix next).table.toArray[j.val]! =
        mle (fun row : Fin (2^(suffix.length+1)) => state.table.toArray[row.val*1600+j.val]!)
          (fun k => (latePackRun weights kappa suffix next).point[state.point.size+k.val]!)
    constructor
    · have hcons : (fun k : Fin (suffix.length+1) => (entering::suffix)[k.val]!) =
          Fin.cons entering (fun k : Fin suffix.length => suffix[k.val]!) := by
        convert listPoint_cons entering suffix using 1
      rw [hh.1,hcons,hvector,eqEval_cons]
      dsimp only [next,latePackStep]
      rw [mul_assoc]
    · intro j
      rw [hh.2 j,hvector]
      exact foldPacked_column_mle state.table ht r _ j

end CompStark.Keccak.GkrProver
