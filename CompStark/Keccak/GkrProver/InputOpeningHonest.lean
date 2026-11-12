/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.InputOpeningSemantics

/-! Exact ten-round honest input-opening messages of the production prover. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr CompStark.BinaryFields BF64

/-- A bounded coordinate in the left array retains its value under concatenation. -/
theorem arrayAppend_get_left {A : Type} [Inhabited A] (a b : Array A) (i : Nat) (hi : i < a.size) :
    (a++b)[i]! = a[i]! := by
  rw [getElem!_pos _ _ (by rw [Array.size_append]; omega),Array.getElem_append_left hi,
    ← getElem!_pos a i hi]

/-- A bounded coordinate in the right array is offset by precisely the left array's length. -/
theorem arrayAppend_get_right {A : Type} [Inhabited A] (a b : Array A) (i : Nat) (hi : i < b.size) :
    (a++b)[a.size+i]! = b[i]! := by
  rw [getElem!_pos _ _ (by rw [Array.size_append]; omega),Array.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  exact (getElem!_pos b i hi).symm

/-- The actual concatenated input-opening point is its low block followed by its slot block. -/
theorem openingRuns_join (writer : Writer) (committed : Array UInt64) (n : Nat)
    (words wordWeights : Array W) (middle : W) (claim : Claim) :
    let runs := openingRuns writer committed n words wordWeights middle claim
    (fun i : Fin 10 => (runs.low.point++runs.slot.point)[i.val]!) =
      joinPoint (fun i : Fin 4 => runs.low.point[i.val]!) (fun i : Fin 6 => runs.slot.point[i.val]!) := by
  dsimp only
  let runs := openingRuns writer committed n words wordWeights middle claim
  have hl : runs.low.point.size = 4 := (openingRuns_lengths writer committed n words wordWeights middle claim).2.2.1
  have hs : runs.slot.point.size = 6 := (openingRuns_lengths writer committed n words wordWeights middle claim).2.2.2.2.1
  funext i
  unfold joinPoint
  split
  · rename_i hi
    exact arrayAppend_get_left runs.low.point runs.slot.point i.val (by rw [hl]; exact hi)
  · rename_i hi
    have he : i.val = runs.low.point.size+(i.val-4) := by rw [hl]; omega
    exact (congrArg (fun j => (runs.low.point++runs.slot.point)[j]!) he).trans
      (arrayAppend_get_right runs.low.point runs.slot.point (i.val-4) (by rw [hs]; have := i.isLt; omega))

attribute [local irreducible] inputBits eqTable proveQuadratics openingPerInstance openingAtInstance

/-- The two native input runs author the single honest ten-round strategy of their retained buffers. -/
theorem openingRuns_input_honest (writer : Writer) (committed : Array UInt64) (n : Nat)
    (words wordWeights : Array W) (middle : W) (claim : Claim)
    (hmu : claim.mu.size = 16)
    (hf : CoordinateDegree
      (inputBufferSummand (inputBits committed n (claim.point.extract 0 (claim.point.size-1)))
        (inputWeights claim) claim.mu) 2) :
    let runs := openingRuns writer committed n words wordWeights middle claim
    (fun i : Fin 10 => quadraticMessageOfArray (runs.low.messages++runs.slot.messages)[i.val]!) =
      honestCompressedRounds
        (inputBufferSummand (inputBits committed n (claim.point.extract 0 (claim.point.size-1)))
          (inputWeights claim) claim.mu) hf
        (fun i => (runs.low.point++runs.slot.point)[i.val]!) := by
  let : Fintype Ext3 := Fintype.ofFinite Ext3
  let : Fintype W := Fintype.ofEquiv Ext3 WordExt3.ringEquiv.toEquiv.symm
  have hcard : 2 < Fintype.card W := by
    rw [Fintype.card_congr WordExt3.ringEquiv.toEquiv,BF64.card_ext3]
    decide
  let runs := openingRuns writer committed n words wordWeights middle claim
  let folded := inputBits committed n (claim.point.extract 0 (claim.point.size-1))
  let weights := inputWeights claim
  have hlp : runs.low.point.size = 4 := (openingRuns_lengths writer committed n words wordWeights middle claim).2.2.1
  have hlm : runs.low.messages.size = 4 := (openingRuns_lengths writer committed n words wordWeights middle claim).2.2.2.1
  have hsm : runs.slot.messages.size = 6 := (openingRuns_lengths writer committed n words wordWeights middle claim).2.2.2.2.2
  have hlowrun : runs.low = proveQuadratics
      ((proveQuadratics writer words wordWeights 1 1 middle 6).writer.write
        (proveQuadratics writer words wordWeights 1 1 middle 6).a[0]!)
      (openingPerInstance folded weights) claim.mu 1 1 claim.value 4 := by
    dsimp only [runs,openingRuns,folded,weights]
  have hslotrun : runs.slot = proveQuadratics runs.low.writer (openingAtInstance folded runs.low.point)
      weights 64 runs.low.b[0]! runs.low.value 6 := by
    dsimp only [runs,openingRuns,folded,weights]
  have hlow : (fun i : Fin 4 => quadraticMessageOfArray runs.low.messages[i.val]!) =
      honestCompressedRounds (quadraticSummand (openingPerInstance folded weights) claim.mu 1 4 1)
        (quadraticSummand_degree (openingPerInstance folded weights) claim.mu 1 4 1)
        (fun i => runs.low.point[i.val]!) := by
    rw [hlowrun]
    apply proveQuadratics_honest
    · decide
    · rw [openingPerInstance_size]; rfl
    · rw [openingPerInstance_size,hmu]
  have hslot : (fun i : Fin 6 => quadraticMessageOfArray runs.slot.messages[i.val]!) =
      honestCompressedRounds (quadraticSummand (openingAtInstance folded runs.low.point) weights 64 6 runs.low.b[0]!)
        (quadraticSummand_degree (openingAtInstance folded runs.low.point) weights 64 6 runs.low.b[0]!)
        (fun i => runs.slot.point[i.val]!) := by
    rw [hslotrun]
    apply proveQuadratics_honest
    · decide
    · rw [openingAtInstance_size]; rfl
    · rw [openingAtInstance_size,inputWeights_size]
  have hmuValue : runs.low.b[0]! = mle (fun inst : Fin 16 => claim.mu[inst.val]!)
      (fun i : Fin 4 => runs.low.point[i.val]!) := by
    have hh := proveQuadratics_terminal
      ((proveQuadratics writer words wordWeights 1 1 middle 6).writer.write
        (proveQuadratics writer words wordWeights 1 1 middle 6).a[0]!)
      (openingPerInstance folded weights) claim.mu 1 1 claim.value 4 (by decide)
      (by rw [openingPerInstance_size]; rfl) (by rw [openingPerInstance_size,hmu])
    rw [hlowrun]
    have h0 := hh.2.2.2 (0 : Fin 1)
    simp only [Fin.val_zero,Nat.mul_one,Nat.add_zero] at h0
    convert h0 using 1
  dsimp only
  rw [openingRuns_join]
  funext i
  by_cases hi : i.val < 4
  · rw [arrayAppend_get_left runs.low.messages runs.slot.messages i.val (by rw [hlm]; exact hi)]
    have hh := congrFun hlow ⟨i.val,hi⟩
    exact hh.trans (honestCompressedRounds_prefix (a := 4) (b := 6) (degree := 1)
      (inputBufferSummand folded weights claim.mu)
      (quadraticSummand (openingPerInstance folded weights) claim.mu 1 4 1) hf
      (quadraticSummand_degree _ _ _ _ _) (inputBufferSummand_low folded weights claim.mu)
      hcard (fun i => runs.low.point[i.val]!) (fun i => runs.slot.point[i.val]!) ⟨i.val,hi⟩).symm
  · have hj : i.val-4 < 6 := by have := i.isLt; omega
    have he : i.val = runs.low.messages.size+(i.val-4) := by rw [hlm]; omega
    rw [he,arrayAppend_get_right runs.low.messages runs.slot.messages (i.val-4) (by rw [hsm]; exact hj)]
    have hh := congrFun hslot ⟨i.val-4,hj⟩
    have hsuffix := honestCompressedRounds_suffix (a := 4) (b := 6) (degree := 1)
      (inputBufferSummand folded weights claim.mu)
      (quadraticSummand (openingAtInstance folded runs.low.point) weights 64 6 runs.low.b[0]!) hf
      (quadraticSummand_degree _ _ _ _ _) (fun i => runs.low.point[i.val]!)
      (fun i => runs.slot.point[i.val]!) (by
        intro high
        rw [inputBufferSummand_slot folded weights claim.mu runs.low.point hlp high,hmuValue]) ⟨i.val-4,hj⟩
    have hind : (⟨4+(i.val-4),by omega⟩ : Fin 10) = i := Fin.ext (by change 4+(i.val-4) = i.val; omega)
    rw [hind] at hsuffix
    exact hh.trans hsuffix.symm

/-- Every native input-opening message is the specification's honest message in the verifier's field. -/
theorem proveOpenings_input_honest (writer : Writer) (committed : Array UInt64)
    (words wordWeights : Array W) (middle : W) (claim : Claim) (p : Nat)
    (hp : 3 ≤ p) (hc : claim.point.size = p+1) (hmu : claim.mu.size = 16) (t : Transcript E p)
    (hclaim : nextClaim (t.layers (Fin.last 11)) = claim.toProtocol p)
    (hpoint : t.openings.inputPoint = fun i =>
      (proveOpenings writer committed (2^(p+4)) words wordWeights middle claim).1.inputPoint[i.val]!.toField) :
    let result := (proveOpenings writer committed (2^(p+4)) words wordWeights middle claim).1
    (fun i : Fin 10 => ((result.inputMessages[i.val]!)[0]!.toField,
      fun _ : Fin 1 => (result.inputMessages[i.val]!)[1]!.toField)) =
      honestInputRounds (committedWitness p committed) t := by
  let : Fintype E := Fintype.ofFinite E
  have hcard : 2 < Fintype.card E := by rw [BF64.card_ext3]; decide
  let f := inputBufferSummand
    (inputBits committed (2^(p+4)) (claim.point.extract 0 (claim.point.size-1))) (inputWeights claim) claim.mu
  let g := inputSummand (committedWitness p committed) t
  have hg : CoordinateDegree g 2 := inputCoordinateDegree _ _
  have hrel : ∀ point,WordExt3.ringEquiv (f point) = g (fun i => WordExt3.ringEquiv (point i)) :=
    inputBufferSummand_protocol_toField committed claim p hp hc t hclaim
  have hback : ∀ point,WordExt3.ringEquiv.symm (g point) =
      f (fun i => WordExt3.ringEquiv.symm (point i)) := by
    intro point
    have hh := congrArg WordExt3.ringEquiv.symm
      (hrel (fun i => WordExt3.ringEquiv.symm (point i)))
    simpa only [RingEquiv.symm_apply_apply,RingEquiv.apply_symm_apply] using hh.symm
  have hf : CoordinateDegree f 2 := coordinateDegree_equiv WordExt3.ringEquiv.symm g f hback hg
  have hh := openingRuns_input_honest writer committed (2^(p+4)) words wordWeights middle claim hmu hf
  dsimp only
  rw [proveOpenings_eq_runs] at hpoint ⊢
  unfold honestInputRounds
  rw [hpoint]
  funext i
  change ((quadraticMessageOfArray
    ((openingRuns writer committed (2^(p+4)) words wordWeights middle claim).low.messages++
      (openingRuns writer committed (2^(p+4)) words wordWeights middle claim).slot.messages)[i.val]!).1.toField,
    fun k : Fin 1 => ((quadraticMessageOfArray
      ((openingRuns writer committed (2^(p+4)) words wordWeights middle claim).low.messages++
        (openingRuns writer committed (2^(p+4)) words wordWeights middle claim).slot.messages)[i.val]!).2 k).toField) = _
  rw [congrFun hh i]
  exact honestCompressedRounds_equiv (n := 10) (degree := 1) WordExt3.ringEquiv f g hf hg hrel hcard _ i

end CompStark.Keccak.GkrProver
