/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.NativeInitialClaim

/-! Whole-native transcript refinement and deterministic completeness transfer. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak CompStark.Keccak.Gkr CompStark.BinaryFields BF64

/-- A default layer is used only to state structural prefix lookups. -/
local instance : Inhabited Layer := ⟨⟨#[],0,#[],#[],#[],#[],#[],0⟩⟩

/-- Interpreting a stored native layer agrees with defaulting lookup at a valid index. -/
theorem Reduction.layer_get! (result : Reduction) (p : Nat) (height : result.layers.size=12) (d : Fin 12) :
    (result.toProtocol p height).layers d=result.layers[d.val]!.toProtocol p := by
  rw [getElem!_pos _ _ (by rw [height]; exact d.isLt)]
  rfl

/-- The structural predecessor claim is exactly the protocol's entering claim. -/
theorem storedClaim_claimAt (result : Reduction) (p : Nat) (height : result.layers.size=12)
    (x : E) (out : Fin (2^(p+4)) → Fin 25 → E) (d : Fin 12) :
    storedClaim p (firstClaim x out (result.toProtocol p height)) result.layers d.val =
      claimAt x out (result.toProtocol p height) d.castSucc := by
  unfold storedClaim claimAt
  simp only [Fin.val_castSucc]
  split
  · rfl
  · rw [Reduction.layer_get!]

attribute [local irreducible] proveLayerM proveOpenings Writer.sampleMany outputWords dot prepareRmfeProducts

/-- The full native reduction retains its structural setup scalars and complete layer fold. -/
theorem prove_setup_fold (writer : Writer) (w : SlicedWitness) (committed : Array UInt64) (batch output : Array W) :
    let setup := nativeSetup writer w committed batch output
    let result := prove writer w committed batch output
    result.batchPoint=batch ∧ result.segment=setup.segment ∧ result.lanes=setup.lanes ∧
      result.middle=setup.middle ∧ result.layers=
        ((List.range 12).foldl (nativeLayerStateStep w prepareRmfeProducts) (setup.claim,setup.writer,#[])).2.2 := by
  rw [prove_eq_fold]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Every layer of the complete native prover follows the honest strategy at its actual entering claim. -/
theorem prove_layers_honest (writer : Writer) (w : SlicedWitness) (committed : Array UInt64)
    (batch output : Array W) {h : Nat} (hn : w.nLog=h+8) (hb : batch.size=h+8)
    (hw : PreChiRefines w (committedWitness (h+4) committed))
    (hbound : 1600*(2^w.nLog/64)≤USize.size)
    (out : Fin (2^(h+8)) → Fin 25 → E)
    (ho : ∀ l : Fin 25,output[l.val]!.toField=mle (fun b => out b l) (fun i : Fin (h+8) => batch[i.val]!.toField)) :
    let result := prove writer w committed batch output
    let t := result.toProtocol (h+4) (prove_layers_size ..)
    ∀ d,t.layers d=honestLayer (committedWitness (h+4) committed) d (claimAt (ofK g) out t d.castSucc)
      (t.layers d).point (t.layers d).packPoint (t.layers d).positionPoint (t.layers d).beta := by
  let setup := nativeSetup writer w committed batch output
  let result := prove writer w committed batch output
  let t := result.toProtocol (h+4) (prove_layers_size ..)
  have hs := prove_setup_fold writer w committed batch output
  have hlanes : setup.lanes.size=5 := Writer.sampleMany_size _ _
  have hbatch : t.instancePoint=fun i => batch[i.val]!.toField := by
    change (fun i : Fin (h+8) => result.batchPoint[i.val]!.toField)=_
    rw [hs.1]
  have hinitial : setup.claim.toProtocol (h+4)=firstClaim (ofK g) out t := by
    apply nativeInitialClaim_toProtocol batch output setup.segment setup.lanes setup.middle (h+4) hb hlanes out t hbatch
    · exact congrArg WordExt3.toField hs.2.1
    · change (fun i : Fin 5 => result.lanes[i.val]!.toField)=_
      rw [hs.2.2.1]
    · exact congrArg WordExt3.toField hs.2.2.2.1
    · intro l
      rw [hbatch]
      exact ho l
  have hshape := nativeInitialClaim_shape batch output setup.segment setup.lanes setup.middle (h+4) hb
  have hfold := nativeLayerFold_honest w (committedWitness (h+4) committed) hn hw hbound
    setup.claim setup.writer hshape.1 hshape.2 12 (by decide)
  have hh : StoredLayersHonest (committedWitness (h+4) committed) (firstClaim (ofK g) out t) result.layers := by
    rw [hs.2.2.2.2,← hinitial]
    exact hfold.2.2.2.1
  dsimp only
  intro d
  have hd := hh d (by rw [prove_layers_size]; exact d.isLt)
  rw [storedClaim_claimAt] at hd
  simpa only [← Reduction.layer_get! result (h+4) (prove_layers_size ..)] using hd

/-- The complete native transcript is specification-honest for a certified sliced witness and supplied output evaluations. -/
theorem prove_specificationHonest (writer : Writer) (w : SlicedWitness) (committed : Array UInt64)
    (batch output : Array W) {h : Nat} (hn : w.nLog=h+8) (hb : batch.size=h+8)
    (hc : committed.size/(2^(h+8))=64)
    (hw : PreChiRefines w (committedWitness (h+4) committed))
    (hbound : 1600*(2^w.nLog/64)≤USize.size)
    (out : Fin (2^(h+8)) → Fin 25 → E)
    (ho : ∀ l : Fin 25,output[l.val]!.toField=mle (fun b => out b l) (fun i : Fin (h+8) => batch[i.val]!.toField)) :
    SpecificationHonest (ofK g) out (committedWitness (h+4) committed)
      ((prove writer w committed batch output).toProtocol (h+4) (prove_layers_size ..)) := by
  have hopen := prove_openings_honest writer w committed batch output (h+4) (by omega) hn hb hc
  exact ⟨prove_middle writer w committed batch output (h+4) hn hb hc,
    prove_layers_honest writer w committed batch output hn hb hw hbound out ho,
    hopen.1,hopen.2.1,hopen.2.2.1,hopen.2.2.2⟩

/-- The actual complete native prover equals the specification prover at every retained verifier challenge. -/
theorem prove_eq_specificationTranscript (writer : Writer) (w : SlicedWitness) (committed : Array UInt64)
    (batch output : Array W) {h : Nat} (hn : w.nLog=h+8) (hb : batch.size=h+8)
    (hc : committed.size/(2^(h+8))=64)
    (hw : PreChiRefines w (committedWitness (h+4) committed))
    (hbound : 1600*(2^w.nLog/64)≤USize.size)
    (out : Fin (2^(h+8)) → Fin 25 → E)
    (ho : ∀ l : Fin 25,output[l.val]!.toField=mle (fun b => out b l) (fun i : Fin (h+8) => batch[i.val]!.toField)) :
    let t := (prove writer w committed batch output).toProtocol (h+4) (prove_layers_size ..)
    t=specificationTranscript (ofK g) out (committedWitness (h+4) committed) (Challenges.ofTranscript t) :=
  (prove_specificationHonest writer w committed batch output hn hb hc hw hbound out ho).eq_specificationTranscript

/-- The native prover inherits acceptance and terminal-opening completeness from its specification. -/
theorem prove_complete (writer : Writer) (w : SlicedWitness) (committed : Array UInt64)
    (batch output : Array W) {h : Nat} (hn : w.nLog=h+8) (hb : batch.size=h+8)
    (hc : committed.size/(2^(h+8))=64)
    (hw : PreChiRefines w (committedWitness (h+4) committed))
    (hbound : 1600*(2^w.nLog/64)≤USize.size)
    (out : Fin (2^(h+8)) → Fin 25 → E)
    (ho : ∀ l : Fin 25,output[l.val]!.toField=mle (fun b => out b l) (fun i : Fin (h+8) => batch[i.val]!.toField))
    (relation : InputRelation (ofK g) out (committedWitness (h+4) committed)) :
    let t := (prove writer w committed batch output).toProtocol (h+4) (prove_layers_size ..)
    Accepts (ofK g) out t ∧ TerminalRelation (ofK g) (committedWitness (h+4) committed) t :=
  (prove_specificationHonest writer w committed batch output hn hb hc hw hbound out ho).complete relation

end CompStark.Keccak.GkrProver
