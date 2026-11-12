/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.OpeningTrace
public import CompStark.Keccak.GkrProver.FieldTransport

/-! Specification semantics of all native committed-word opening messages. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr CompStark.BinaryFields BF64
open scoped BigOperators

/-- Native weights for the middle segment's twenty-five committed lanes. -/
def wordOpeningWeights (segment : W) (lanes : Array W) : Array W :=
  Array.ofFn fun slot : Fin 64 =>
    if 25 ≤ slot.val && slot.val < 50 then (1+segment)*(eqTable lanes)[slot.val-25]! else 0

attribute [local irreducible] eqTable proveQuadratics outputWords proveOpenings

/-- Native word-opening weights have exactly one coordinate per committed slot. -/
theorem wordOpeningWeights_size (segment : W) (lanes : Array W) :
    (wordOpeningWeights segment lanes).size = 64 := Array.size_ofFn ..

/-- Equality-table coordinates retain an explicitly certified protocol dimension under field transport. -/
theorem eqTable_dimension_toField (point : Array W) (n : Nat) (hn : point.size = n) (i : Fin (2^n)) :
    (eqTable point)[i.val]!.toField = eqWeight (fun k : Fin n => point[k.val]!.toField) i.val := by
  rw [eqTable_get_dimension point n hn i]
  exact eqWeight_map WordExt3.ringEquiv.toRingHom (fun k : Fin n => point[k.val]!) i.val

/-- Each native word-opening weight is the protocol's segment-and-lane coefficient. -/
theorem wordOpeningWeights_toField (segment : W) (lanes : Array W) (hl : lanes.size = 5)
    (slot : Fin 64) :
    (wordOpeningWeights segment lanes)[slot.val]!.toField =
      if 25 ≤ slot.val ∧ slot.val < 50 then
        (1-segment.toField)*eqWeight (fun i : Fin 5 => lanes[i.val]!.toField) (slot.val-25) else 0 := by
  rw [getElem!_pos _ _ (by rw [wordOpeningWeights_size]; exact slot.isLt)]
  simp only [wordOpeningWeights,Array.getElem_ofFn,Bool.and_eq_true,decide_eq_true_eq]
  split
  · rename_i h
    change WordExt3.ringEquiv ((1+segment)*(eqTable lanes)[slot.val-25]!) = _
    rw [map_mul,map_add,map_one]
    change (1+segment.toField)*(eqTable lanes)[slot.val-25]!.toField = _
    rw [eqTable_dimension_toField lanes 5 hl ⟨slot.val-25,by omega⟩]
    rw [CharTwo.sub_eq_add]
  · exact WordExt3.ringEquiv.map_zero

/-- A complete native word buffer contains every committed slot. -/
theorem outputWords_size (committed : Array UInt64) (n : Nat) (point : Array W) :
    (outputWords committed n point).size = committed.size/n := by
  unfold outputWords
  exact Array.size_ofFn ..

/-- Native committed words are exactly the specification's middle-word table at the external point. -/
theorem outputWords_middleWord (committed : Array UInt64) (batch : Array W) (p : Nat)
    (hb : batch.size = p+4) (hc : committed.size/(2^(p+4)) = 64) (t : Transcript E p)
    (htb : t.instancePoint = fun i => batch[i.val]!.toField) (slot : Fin 64) :
    (outputWords committed (2^(p+4)) batch)[slot.val]!.toField =
      middleWord (ofK g) (fun b slot z => sliceBit committed[slot.val*2^(p+4)+b.val]! z) t slot := by
  have h := outputWords_toField committed batch slot.val (by rw [hb,hc]; exact slot.isLt)
  rw [hb] at h
  rw [h]
  simp only [middleWord,htb]

/-- Native word quadratic factors evaluate to the concrete protocol word-opening summand. -/
theorem wordQuadratic_toField (committed : Array UInt64) (batch lanes : Array W)
    (segment : W) (p : Nat) (hb : batch.size = p+4) (hl : lanes.size = 5)
    (hc : committed.size/(2^(p+4)) = 64) (t : Transcript E p)
    (htb : t.instancePoint = fun i => batch[i.val]!.toField)
    (htl : t.lanePoint = fun i => lanes[i.val]!.toField) (hts : t.segment = segment.toField)
    (point : Fin 6 → W) :
    (quadraticSummand (outputWords committed (2^(p+4)) batch)
      (wordOpeningWeights segment lanes) 1 6 1 point).toField =
      wordSummand (CompStark.BinaryFields.ofK CompStark.BinaryFields.g)
        (fun b slot z => sliceBit committed[slot.val*2^(p+4)+b.val]! z) t (fun i => (point i).toField) := by
  have hw := outputWords_middleWord committed batch p hb hc t htb
  simp only [quadraticSummand,Fin.sum_univ_one,Nat.mul_one,Fin.val_zero,Nat.add_zero,one_mul]
  change WordExt3.ringEquiv (_*_) = _
  rw [map_mul]
  have hmap (table : Fin 64 → W) :
      WordExt3.ringEquiv (mle table point) =
        mle (fun i => (table i).toField) (fun i => (point i).toField) :=
    mle_map (n := 6) WordExt3.ringEquiv.toRingHom table point
  rw [hmap,hmap]
  simp only [hw]
  unfold wordSummand
  rw [htl,hts]
  simp only [wordOpeningWeights_toField segment lanes hl]
  exact mul_comm _ _

/-- The actual native word-opening messages are the protocol's honest quadratic messages. -/
theorem proveOpenings_word_honest (writer : Writer) (committed : Array UInt64) (batch lanes : Array W)
    (segment middle : W) (claim : Claim) (p : Nat) (hb : batch.size = p+4) (hl : lanes.size = 5)
    (hc : committed.size/(2^(p+4)) = 64) (t : Transcript E p)
    (htb : t.instancePoint = fun i => batch[i.val]!.toField)
    (htl : t.lanePoint = fun i => lanes[i.val]!.toField) (hts : t.segment = segment.toField)
    (htp : t.openings.outputPoint = fun i =>
      (proveOpenings writer committed (2^(p+4)) (outputWords committed (2^(p+4)) batch)
        (wordOpeningWeights segment lanes) middle claim).1.outputPoint[i.val]!.toField) :
    let result := (proveOpenings writer committed (2^(p+4)) (outputWords committed (2^(p+4)) batch)
      (wordOpeningWeights segment lanes) middle claim).1
    (fun i : Fin 6 => ((result.outputMessages[i.val]!)[0]!.toField,
      fun _ : Fin 1 => (result.outputMessages[i.val]!)[1]!.toField)) =
      honestWordRounds (CompStark.BinaryFields.ofK CompStark.BinaryFields.g)
        (fun b slot z => sliceBit committed[slot.val*2^(p+4)+b.val]! z) t := by
  let : Fintype E := Fintype.ofFinite E
  have hcard : 2 < Fintype.card E := by rw [BF64.card_ext3]; decide
  let words := outputWords committed (2^(p+4)) batch
  let weights := wordOpeningWeights segment lanes
  have hwords : words.size = 64 := by rw [outputWords_size]; exact hc
  have hweights : weights.size = 64 := wordOpeningWeights_size segment lanes
  have hh := proveQuadratics_honest writer words weights 1 1 middle 6
    (by decide) (by simpa only [Nat.reducePow,Nat.mul_one] using hwords) (hwords.trans hweights.symm)
  dsimp only
  rw [proveOpenings_eq_runs] at htp ⊢
  dsimp only [openingRuns] at htp ⊢
  change (fun i : Fin 6 =>
    ((quadraticMessageOfArray (proveQuadratics writer words weights 1 1 middle 6).messages[i.val]!).1.toField,
      fun k : Fin 1 => ((quadraticMessageOfArray
        (proveQuadratics writer words weights 1 1 middle 6).messages[i.val]!).2 k).toField)) = _
  unfold honestWordRounds
  rw [htp]
  funext i
  rw [congrFun hh i]
  apply honestCompressedRounds_equiv WordExt3.ringEquiv _ _ _ _ _ hcard
  intro point
  exact wordQuadratic_toField committed batch lanes segment p hb hl hc t htb htl hts point

/-- The native terminal word value is the verifier-field interpolation of the complete committed word table. -/
theorem proveOpenings_wordValue (writer : Writer) (committed : Array UInt64) (batch : Array W)
    (wordWeights : Array W) (middle : W) (claim : Claim) (p : Nat) (hb : batch.size = p+4)
    (hc : committed.size/(2^(p+4)) = 64) (hw : wordWeights.size = 64) (t : Transcript E p)
    (htb : t.instancePoint = fun i => batch[i.val]!.toField)
    (htp : t.openings.outputPoint = fun i =>
      (proveOpenings writer committed (2^(p+4)) (outputWords committed (2^(p+4)) batch)
        wordWeights middle claim).1.outputPoint[i.val]!.toField) :
    (proveOpenings writer committed (2^(p+4)) (outputWords committed (2^(p+4)) batch)
      wordWeights middle claim).1.outputValue.toField =
      mle (middleWord (ofK g) (fun b slot z => sliceBit committed[slot.val*2^(p+4)+b.val]! z) t)
        t.openings.outputPoint := by
  rw [proveOpenings_outputValue writer committed (2^(p+4))
    (outputWords committed (2^(p+4)) batch) wordWeights middle claim
    (by rw [outputWords_size]; exact hc) hw]
  have hmap := mle_map (n := 6) WordExt3.ringEquiv.toRingHom
    (fun slot : Fin 64 => (outputWords committed (2^(p+4)) batch)[slot.val]!)
    (fun i : Fin 6 => (proveOpenings writer committed (2^(p+4))
      (outputWords committed (2^(p+4)) batch) wordWeights middle claim).1.outputPoint[i.val]!)
  change WordExt3.ringEquiv.toRingHom (mle (n := 6) _ _) = _
  rw [hmap,htp]
  apply congrArg (fun table : Fin 64 → E => mle (n := 6) table
    (fun i : Fin 6 => (proveOpenings writer committed (2^(p+4))
      (outputWords committed (2^(p+4)) batch) wordWeights middle claim).1.outputPoint[i.val]!.toField))
  funext slot
  exact outputWords_middleWord committed batch p hb hc t htb slot

end CompStark.Keccak.GkrProver
