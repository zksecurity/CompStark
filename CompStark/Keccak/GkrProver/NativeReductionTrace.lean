/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.NativeLayerHonest

/-! Structural layer invariants for the complete native reduction. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak CompStark.Keccak.Gkr BF64

/-- The exact initial weighted claim constructed by the production setup. -/
def nativeInitialClaim (batch output : Array W) (segment : W) (lanes : Array W) (middle : W) : Claim :=
  ⟨middle+segment*dot ((eqTable lanes).extract 0 25) output,
    eqTable (batch.extract 0 4),(batch.extract 4 batch.size).push segment,
    Array.ofFn fun j : Fin 1600 => WordExt3.mulScalar (eqTable lanes)[j.val/64]! ⟨1 <<< (j.val%64).toUInt64⟩⟩

/-- Setup values retained before the twelve production layers. -/
structure NativeSetup where
  /-- Sampled segment coordinate. -/
  segment : W
  /-- Sampled lane coordinates. -/
  lanes : Array W
  /-- Committed middle-state scalar. -/
  middle : W
  /-- Initial weighted claim. -/
  claim : Claim
  /-- Writer after emitting the middle scalar. -/
  writer : Writer

/-- Structural expression of the production setup before its layer fold. -/
def nativeSetup (writer : Writer) (w : SlicedWitness) (committed : Array UInt64) (batch output : Array W) : NativeSetup :=
  let seg := writer.sampleMany 1
  let lanes := seg.2.sampleMany 5
  let middle := dot (outputWords committed (2^w.nLog) batch) (wordOpeningWeights seg.1[0]! lanes.1)
  ⟨seg.1[0]!,lanes.1,middle,nativeInitialClaim batch output seg.1[0]! lanes.1 middle,lanes.2.write middle⟩

attribute [local irreducible] proveLayerM proveOpenings Writer.sampleMany outputWords dot prepareRmfeProducts

/-- The complete production reduction is its setup, structural layer fold, and terminal opening call. -/
theorem prove_eq_fold (writer : Writer) (w : SlicedWitness) (committed : Array UInt64) (batch output : Array W) :
    let setup := nativeSetup writer w committed batch output
    let final := (List.range 12).foldl (nativeLayerStateStep w prepareRmfeProducts) (setup.claim,setup.writer,#[])
    prove writer w committed batch output =
      ⟨batch,setup.segment,setup.lanes,setup.middle,final.2.2,final.1,
        (proveOpenings final.2.1 committed (2^w.nLog) (outputWords committed (2^w.nLog) batch)
          (wordOpeningWeights setup.segment setup.lanes) setup.middle final.1).1,
        (proveOpenings final.2.1 committed (2^w.nLog) (outputWords committed (2^w.nLog) batch)
          (wordOpeningWeights setup.segment setup.lanes) setup.middle final.1).2⟩ := by
  have hbind {A B : Type} (a : Id A) (f : A → Id B) : a >>= f = f a := rfl
  have hpure {A : Type} (a : A) : (pure a : Id A)=a := rfl
  simp only [prove,proveM,nativeSetup,nativeInitialClaim,wordOpeningWeights,
    Std.Legacy.Range.forIn_eq_forIn_range',hbind,
    Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range',hpure]
  rfl

/-- A harmless default layer is used only for intermediate structural statements. -/
local instance : Inhabited Layer := ⟨⟨#[],0,#[],#[],#[],#[],#[],0⟩⟩

/-- The entering protocol claim of a stored layer, taken from the initial claim or its predecessor. -/
noncomputable def storedClaim (p : Nat) (initial : Gkr.Claim CompStark.BinaryFields.E p) (layers : Array Layer) (d : Nat) :
    Gkr.Claim CompStark.BinaryFields.E p :=
  if d=0 then initial else nextClaim (layers[d-1]!.toProtocol p)

/-- All stored production layers follow the specification at their exact predecessor claims. -/
def StoredLayersHonest {p : Nat} (q : Witness p) (initial : Gkr.Claim CompStark.BinaryFields.E p)
    (layers : Array Layer) : Prop :=
  ∀ d : Fin 12,d.val<layers.size →
    layers[d.val]!.toProtocol p = honestLayer q d (storedClaim p initial layers d.val)
      (layers[d.val]!.toProtocol p).point (layers[d.val]!.toProtocol p).packPoint
      (layers[d.val]!.toProtocol p).positionPoint (layers[d.val]!.toProtocol p).beta

attribute [local irreducible] product nativePackRun positionLoop earlyValues prepareWeightMaps
  binaryValues Writer.sample Writer.writeAll instanceWeights sum evaluate eqTable transposeWeights

/-- Appending a layer preserves the predecessor claim of every earlier stored layer. -/
theorem storedClaim_push_old (p : Nat) (initial : Gkr.Claim CompStark.BinaryFields.E p) (layers : Array Layer)
    (layer : Layer) (d : Nat) (hd : d<layers.size) :
    storedClaim p initial (layers.push layer) d=storedClaim p initial layers d := by
  unfold storedClaim
  split
  · rfl
  · rw [array_push_get_old _ _ _ (by omega)]

/-- The claim at a newly appended layer is the entering state claim when the prefix invariant holds. -/
theorem storedClaim_push_last (p : Nat) (initial : Gkr.Claim CompStark.BinaryFields.E p) (state : NativeLayerState)
    (layer : Layer) (hclaim : state.1.toProtocol p=storedClaim p initial state.2.2 state.2.2.size) :
    storedClaim p initial (state.2.2.push layer) state.2.2.size=state.1.toProtocol p := by
  rw [hclaim]
  unfold storedClaim
  split
  · rfl
  · rw [array_push_get_old _ _ _ (by omega)]

/-- A production layer appends the honest strategy and establishes the exact next entering claim. -/
theorem nativeLayerStateStep_honest (w : SlicedWitness) {h : Nat} (q : Witness (h+4))
    (hn : w.nLog=h+8) (hw : PreChiRefines w q) (hbound : 1600*(2^w.nLog/64)≤USize.size)
    (initial : Gkr.Claim CompStark.BinaryFields.E (h+4)) (state : NativeLayerState) (d : Fin 12)
    (hlen : state.2.2.size=d.val) (hc : state.1.point.size=h+5) (hweights : state.1.weights.size=1600)
    (hclaim : state.1.toProtocol (h+4)=storedClaim (h+4) initial state.2.2 state.2.2.size)
    (honest : StoredLayersHonest q initial state.2.2) :
    let final := nativeLayerStateStep w prepareRmfeProducts state d.val
    StoredLayersHonest q initial final.2.2 ∧
      final.1.toProtocol (h+4)=storedClaim (h+4) initial final.2.2 final.2.2.size := by
  let result := Id.run (proveLayerM (M := Id) (fun _ _ => pure ()) state.2.1 w d.val state.1 prepareRmfeProducts)
  change StoredLayersHonest q initial (state.2.2.push result.1) ∧
    result.2.1.toProtocol (h+4)=storedClaim (h+4) initial (state.2.2.push result.1) (state.2.2.push result.1).size
  constructor
  · intro i hi
    rw [Array.size_push,hlen] at hi
    by_cases hold : i.val<d.val
    · have hget : (state.2.2.push result.1)[i.val]! =state.2.2[i.val]! :=
        array_push_get_old _ _ _ (by omega)
      rw [hget,storedClaim_push_old _ _ _ _ _ (by omega)]
      exact honest i (by omega)
    · have hid : i=d := Fin.ext (by omega)
      subst i
      rw [← hlen,array_push_get_last,storedClaim_push_last _ _ state result.1 hclaim]
      exact proveLayerM_honest state.2.1 w q hn hw d state.1 hc hweights hbound
  · rw [Array.size_push]
    unfold storedClaim
    rw [ite_eq_right (by omega),Nat.add_sub_cancel,array_push_get_last]
    exact proveLayerM_nextClaim state.2.1 w d.val state.1 prepareRmfeProducts (h+4)

/-- Every prefix of the full native layer fold preserves honest layers, exact batching, and dimensions. -/
theorem nativeLayerFold_honest (w : SlicedWitness) {h : Nat} (q : Witness (h+4))
    (hn : w.nLog=h+8) (hw : PreChiRefines w q) (hbound : 1600*(2^w.nLog/64)≤USize.size)
    (initial : Claim) (writer : Writer) (hc : initial.point.size=h+5) (hweights : initial.weights.size=1600)
    (n : Nat) (hn12 : n≤12) :
    let final := (List.range n).foldl (nativeLayerStateStep w prepareRmfeProducts) (initial,writer,#[])
    final.2.2.size=n ∧ final.1.point.size=h+5 ∧ final.1.weights.size=1600 ∧
      StoredLayersHonest q (initial.toProtocol (h+4)) final.2.2 ∧
      final.1.toProtocol (h+4)=storedClaim (h+4) (initial.toProtocol (h+4)) final.2.2 final.2.2.size := by
  induction n with
  | zero =>
    change (#[].size=0 ∧ initial.point.size=h+5 ∧ initial.weights.size=1600 ∧
      StoredLayersHonest q (initial.toProtocol (h+4)) #[] ∧ _)
    exact ⟨rfl,hc,hweights,fun d hd => False.elim (Nat.not_lt_zero _ hd),rfl⟩
  | succ n ih =>
    have prev := ih (by omega)
    rw [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    let state := (List.range n).foldl (nativeLayerStateStep w prepareRmfeProducts) (initial,writer,#[])
    have hs := proveLayerM_claim_shape state.2.1 w n state.1 prepareRmfeProducts
    have hh := nativeLayerStateStep_honest w q hn hw hbound (initial.toProtocol (h+4)) state
      ⟨n,by omega⟩ prev.1 prev.2.1 prev.2.2.1 prev.2.2.2.2 prev.2.2.2.1
    exact ⟨(Array.size_push ..).trans (congrArg (·+1) prev.1),hs.1.trans prev.2.1,hs.2.2,hh⟩

end CompStark.Keccak.GkrProver
