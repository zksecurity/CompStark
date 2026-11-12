/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.InputOpeningHonest
public import CompStark.Keccak.GkrProver.WordOpeningSemantics

/-! Committed-witness opening semantics of the complete native reduction. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr CompStark.BinaryFields BF64

attribute [local irreducible] proveLayerM proveOpenings Writer.sample Writer.sampleMany outputWords eqTable dot
  prepareRmfeProducts

/-- The complete native reduction invokes the certified opening prover with its actual retained setup and terminal claim. -/
theorem prove_openings_eq (writer : Writer) (w : SlicedWitness) (committed : Array UInt64)
    (batch output : Array W) :
    let result := prove writer w committed batch output
    ∃ finalWriter, result.openings =
      (proveOpenings finalWriter committed (2^w.nLog) (outputWords committed (2^w.nLog) batch)
        (wordOpeningWeights result.segment result.lanes) result.middle result.finalClaim).1 := by
  have hbind {A B : Type} (a : Id A) (f : A → Id B) : a >>= f = f a := rfl
  simp only [prove,proveM,wordOpeningWeights,Std.Legacy.Range.forIn_eq_forIn_range',
    hbind,List.forIn_pure_yield_eq_foldl,Id.run_pure]
  exact ⟨_,rfl⟩

/-- All four specification opening obligations follow from the actual native opening call and terminal-claim agreement. -/
theorem Reduction.openings_honest (result : Reduction) (p : Nat) (hp : 3 ≤ p)
    (height : result.layers.size = 12) (writer : Writer) (committed : Array UInt64)
    (hb : result.batchPoint.size = p+4) (hl : result.lanes.size = 5)
    (hc : committed.size/(2^(p+4)) = 64)
    (hpoint : result.finalClaim.point.size = p+1) (hmu : result.finalClaim.mu.size = 16)
    (hopening : result.openings =
      (proveOpenings writer committed (2^(p+4)) (outputWords committed (2^(p+4)) result.batchPoint)
        (wordOpeningWeights result.segment result.lanes) result.middle result.finalClaim).1)
    (hclaim : nextClaim ((result.toProtocol p height).layers (Fin.last 11)) = result.finalClaim.toProtocol p) :
    let t := result.toProtocol p height
    t.openings.outputPolys = honestWordRounds (ofK g) (committedWitness p committed) t ∧
      t.openings.outputValue = mle (middleWord (ofK g) (committedWitness p committed) t) t.openings.outputPoint ∧
      t.openings.inputPolys = honestInputRounds (committedWitness p committed) t ∧
      ∀ z,t.openings.slices z =
        mle (fun slot => mle (fun b => ZMod.castHom (dvd_refl 2) E (committedWitness p committed b slot z))
          (inputInstancePoint (nextClaim (t.layers (Fin.last 11))) t.openings.inputPoint))
          (inputSlotPoint t.openings.inputPoint) := by
  let t := result.toProtocol p height
  let words := outputWords committed (2^(p+4)) result.batchPoint
  let weights := wordOpeningWeights result.segment result.lanes
  have hwp : t.openings.outputPoint = fun i =>
      (proveOpenings writer committed (2^(p+4)) words weights result.middle result.finalClaim).1.outputPoint[i.val]!.toField := by
    simp only [t,Reduction.toProtocol,hopening]
    rfl
  have hip : t.openings.inputPoint = fun i =>
      (proveOpenings writer committed (2^(p+4)) words weights result.middle result.finalClaim).1.inputPoint[i.val]!.toField := by
    simp only [t,Reduction.toProtocol,hopening]
    rfl
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · have hh := proveOpenings_word_honest writer committed result.batchPoint result.lanes result.segment result.middle
      result.finalClaim p hb hl hc t rfl rfl rfl hwp
    change (fun i : Fin 6 => ((result.openings.outputMessages[i.val]!)[0]!.toField,
      fun _ : Fin 1 => (result.openings.outputMessages[i.val]!)[1]!.toField)) = _
    rw [hopening]
    exact hh
  · change result.openings.outputValue.toField = _
    rw [hopening]
    exact proveOpenings_wordValue writer committed result.batchPoint weights result.middle result.finalClaim p hb hc
      (wordOpeningWeights_size _ _) t rfl hwp
  · have hh := proveOpenings_input_honest writer committed words weights result.middle result.finalClaim p hp
      hpoint hmu t hclaim hip
    change (fun i : Fin 10 => ((result.openings.inputMessages[i.val]!)[0]!.toField,
      fun _ : Fin 1 => (result.openings.inputMessages[i.val]!)[1]!.toField)) = _
    rw [hopening]
    exact hh
  · intro z
    change result.openings.slices[z.val]!.toField = _
    have hh := proveOpenings_input_slices_toField writer committed words weights result.middle result.finalClaim p hp hpoint z
    rw [hclaim]
    simp only [Reduction.toProtocol,hopening]
    exact hh

end CompStark.Keccak.GkrProver
