/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.EarlyPackTrace

/-! Committed-witness interpretation of both blocks of the complete native pack strategy. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak CompStark.Keccak.Gkr BF64
open scoped BigOperators

/-- The native entering high pack coordinates retain their direct claim-array indices. -/
theorem packHigh_get (claim : Claim) {h : Nat} (hc : claim.point.size=h+5) (i : Fin (h+1)) :
    (claim.point.extract 4 claim.point.size)[i.val]! = claim.point[4+i.val]! := by
  have hs : (claim.point.extract 4 claim.point.size).size=h+1 := by
    rw [Array.size_extract,Nat.min_self,hc]; omega
  rw [getElem!_pos _ _ (by rw [hs]; exact i.isLt),Array.getElem_extract,
    ← getElem!_pos claim.point _ (by have := i.isLt; omega)]

/-- The committed cofactor after summing its high equality-weighted pack coordinates. -/
noncomputable def packLowCofactor {h : Nat} (q : Witness (h+4)) (d : Fin 12) (claim : Claim) (s : W)
    (low : Fin 4 → W) : W :=
  booleanSum (fun high : Fin (h+1) → W => eqEval (fun i => claim.point[4+i.val]!) high *
    MvPolynomial.eval (joinPoint (a := 4) (b := h+1) low high)
      (packCofactorPolynomial q d (claim.toWordProtocol (h+4)) s))

/-- The projected committed pack cofactor has degree at most two in each of its four coordinates. -/
theorem packLowCofactor_degree {h : Nat} (q : Witness (h+4)) (d : Fin 12) (claim : Claim) (s : W) :
    CoordinateDegree (packLowCofactor q d claim s) 2 :=
  coordinateDegree_project_low (a := 4) (b := h+1) _
    (coordinateDegree_eval _ (packCofactorPolynomial_degree q d (claim.toWordProtocol (h+4)) s)) (fun high => eqEval (fun i => claim.point[4+i.val]!) high)

/-- The production tensor is the projected committed pack cofactor at every four-coordinate point. -/
theorem nativeEarlyFunction_protocol (w : SlicedWitness) {h : Nat} (q : Witness (h+4))
    (hn : w.nLog=h+8) (hw : PreChiRefines w q) (d : Fin 12) (claim : Claim)
    (hc : claim.point.size=h+5) (hbound : 1600*(2^w.nLog/64)≤USize.size) (s : W) (low : Fin 4 → W) :
    let values := earlyValues w d.val claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
      prepareRmfeProducts (binaryValues (product w d.val claim prepareRmfeProducts).packs claim.point (CompStark.Sumcheck.prepare s))
    tensorInterpolate (List.ofFn low) (fun i => values[i]!) 0=packLowCofactor q d claim s low := by
  have hh := earlyValues_interpolate w (by omega) d.val claim s (Array.ofFn low) (Array.size_ofFn ..)
  rw [Array.toList_ofFn] at hh
  dsimp only
  rw [hh,nativeTensorValue_protocol w q hn hw d s claim hc hbound (Array.ofFn low) (Array.size_ofFn ..)]
  unfold packLowCofactor
  apply congrArg booleanSum
  funext high
  have he : (fun i : Fin (h+1) => (claim.point.extract 4 claim.point.size)[i.val]!) =
      (fun i : Fin (h+1) => claim.point[4+i.val]!) := funext (packHigh_get claim hc)
  rw [he]
  simp only [ofFn_get!]

/-- The complete native run retains the four coordinates and messages authored by its early prefix. -/
theorem nativePackRun_prefix_four (w : SlicedWitness) (d : Nat) (claim : Claim) (s : W) (values : Array W)
    (writer : Writer) (value : W) (hc : 4≤claim.point.size) (i : Fin 4) :
    let boundary := (List.range 4).foldl (nativePackStep w d claim s values)
      ⟨PackedE.zeros 0,lane 1,value,#[],#[],writer⟩
    let final := nativePackRun w d claim s values writer value
    final.messages[i.val]! = boundary.messages[i.val]! ∧ final.point[i.val]! = boundary.point[i.val]! := by
  dsimp only
  rw [nativePackRun_suffix w d claim s values writer value hc]
  have hl := nativePackFold_lengths w d claim s values (List.range 4)
    ⟨PackedE.zeros 0,lane 1,value,#[],#[],writer⟩
  simp only [List.length_range,Array.size_empty,Nat.zero_add] at hl
  exact ⟨(latePackRun_prefix _ _ _ _).2 i.val (by rw [hl.2]; exact i.isLt),
    (latePackRun_prefix _ _ _ _).1 i.val (by rw [hl.1]; exact i.isLt)⟩

/-- The four early native pack messages are the projected committed cofactor's honest strategy. -/
theorem nativePackRun_low_honest (w : SlicedWitness) {h : Nat} (q : Witness (h+4))
    (hn : w.nLog=h+8) (hw : PreChiRefines w q) (d : Fin 12) (claim : Claim)
    (hc : claim.point.size=h+5) (hbound : 1600*(2^w.nLog/64)≤USize.size) (s : W)
    (writer : Writer) (value : W) (i : Fin 4) :
    let values := earlyValues w d.val claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
      prepareRmfeProducts (binaryValues (product w d.val claim prepareRmfeProducts).packs claim.point (CompStark.Sumcheck.prepare s))
    let final := nativePackRun w d.val claim s values writer value
    cofactorMessageOfArray final.messages[i.val]! = honestCofactorRounds (packLowCofactor q d claim s)
      (packLowCofactor_degree q d claim s) (fun k : Fin 4 => claim.point[k.val]!)
      (fun k : Fin 4 => final.point[k.val]!) i := by
  dsimp only
  let values := earlyValues w d.val claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
    prepareRmfeProducts (binaryValues (product w d.val claim prepareRmfeProducts).packs claim.point (CompStark.Sumcheck.prepare s))
  have hv : values.size=81 := by
    dsimp only [values]
    rw [earlyValues_eq_nativeTensor w (by omega),Array.size_ofFn]
  have hh := earlyPackRun_honest w d.val claim s values hv (by omega) 4
    ⟨PackedE.zeros 0,lane 1,value,#[],#[],writer⟩ rfl i
  rw [← nativePackBoundary_eq_early] at hh
  simp only [Array.size_empty,Nat.zero_add] at hh
  have hp := nativePackRun_prefix_four w d.val claim s values writer value (by omega) i
  rw [hp.1]
  refine hh.trans (congrFun (honestCofactorRounds_congr _ (packLowCofactor_degree q d claim s) ?_ _ _ _ _ rfl ?_) i)
  · funext low
    simpa only [values,Array.toList_empty,List.nil_append,show lane 1=(1 : W) from rfl,one_mul] using
      nativeEarlyFunction_protocol w q hn hw d claim hc hbound s low
  · funext k
    exact (nativePackRun_prefix_four w d.val claim s values writer value (by omega) k).2.symm

/-- Splitting defaulting array coordinates into low and high blocks preserves the complete point. -/
theorem arrayPoint_join {F : Type} [Inhabited F] (point : Array F) (a b : Nat) :
    (fun i : Fin (b+a) => point[i.val]!) = joinPoint
      (fun i : Fin a => point[i.val]!) (fun i : Fin b => point[a+i.val]!) := by
  funext i
  dsimp only [joinPoint]
  split
  · rfl
  · rename_i hi
    congr 1
    omega

/-- The retained native cofactor strategy uses any explicitly identified suffix dimension. -/
theorem nativePackRun_late_honest_dimension (w : SlicedWitness) (hn : 8≤w.nLog) (d : Nat) (claim : Claim)
    (hc : claim.point.size=w.nLog-3) (hbound : 1600*(2^w.nLog/64)≤USize.size)
    (s : W) (writer : Writer) (value : W) (n : Nat)
    (hs : (claim.point.extract 4 claim.point.size).toList.length=n) (i : Fin n) :
    let values := earlyValues w d claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
      prepareRmfeProducts (binaryValues (product w d claim prepareRmfeProducts).packs claim.point (CompStark.Sumcheck.prepare s))
    let boundary := (List.range 4).foldl (nativePackStep w d claim s values)
      ⟨PackedE.zeros 0,lane 1,value,#[],#[],writer⟩
    let final := nativePackRun w d claim s values writer value
    cofactorMessageOfArray final.messages[4+i.val]! =
      honestCofactorRounds (packTableCofactor boundary.table claim.weights n boundary.scale (sum (instanceWeights s)))
        (packTableCofactor_degree boundary.table claim.weights n boundary.scale (sum (instanceWeights s)))
        (fun k : Fin n => (claim.point.extract 4 claim.point.size).toList[k.val]!)
        (fun k : Fin n => final.point[4+k.val]!) i := by
  subst n
  exact nativePackRun_late_honest w hn d claim hc hbound s writer value i

/-- Both blocks of the actual native pack loop author the complete committed protocol cofactor strategy. -/
theorem nativePackRun_honest (w : SlicedWitness) {h : Nat} (q : Witness (h+4))
    (hn : w.nLog=h+8) (hw : PreChiRefines w q) (d : Fin 12) (claim : Claim)
    (hc : claim.point.size=h+5) (hbound : 1600*(2^w.nLog/64)≤USize.size) (s : W)
    (writer : Writer) (value : W) (i : Fin (h+5)) :
    let values := earlyValues w d.val claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
      prepareRmfeProducts (binaryValues (product w d.val claim prepareRmfeProducts).packs claim.point (CompStark.Sumcheck.prepare s))
    let final := nativePackRun w d.val claim s values writer value
    cofactorMessageOfArray final.messages[i.val]! =
      honestPackRounds q d (claim.toWordProtocol (h+4)) s (fun k : Fin (h+5) => final.point[k.val]!) i := by
  let : Fintype Ext3 := Fintype.ofFinite Ext3
  let : Fintype W := Fintype.ofEquiv Ext3 WordExt3.ringEquiv.toEquiv.symm
  have hcard : 2<Fintype.card W := by
    rw [Fintype.card_congr WordExt3.ringEquiv.toEquiv,BF64.card_ext3]
    decide
  dsimp only
  let values := earlyValues w d.val claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
    prepareRmfeProducts (binaryValues (product w d.val claim prepareRmfeProducts).packs claim.point (CompStark.Sumcheck.prepare s))
  let final := nativePackRun w d.val claim s values writer value
  let f := fun point => MvPolynomial.eval point (packCofactorPolynomial q d (claim.toWordProtocol (h+4)) s)
  have hf : CoordinateDegree f 2 := coordinateDegree_eval _ (packCofactorPolynomial_degree q d (claim.toWordProtocol (h+4)) s)
  by_cases hi : i.val<4
  · have hl := nativePackRun_low_honest w q hn hw d claim hc hbound s writer value ⟨i.val,hi⟩
    have hh := honestCofactorRounds_prefix (a := 4) (b := h+1) f (packLowCofactor q d claim s)
      hf (packLowCofactor_degree q d claim s) (fun k : Fin 4 => claim.point[k.val]!)
      (fun k : Fin (h+1) => claim.point[4+k.val]!) (fun k : Fin 4 => final.point[k.val]!)
      (fun k : Fin (h+1) => final.point[4+k.val]!) (fun _ => rfl) hcard ⟨i.val,hi⟩
    rw [← arrayPoint_join claim.point 4 (h+1),← arrayPoint_join final.point 4 (h+1)] at hh
    exact hl.trans hh.symm
  · let k : Fin (h+1) := ⟨i.val-4,by have := i.isLt; omega⟩
    let boundary := (List.range 4).foldl (nativePackStep w d.val claim s values)
      ⟨PackedE.zeros 0,lane 1,value,#[],#[],writer⟩
    have hl := nativePackFold_lengths w d.val claim s values (List.range 4)
      ⟨PackedE.zeros 0,lane 1,value,#[],#[],writer⟩
    have hp : boundary.point.size=4 := by
      simpa only [boundary,List.length_range,Array.size_empty,Nat.zero_add] using hl.1
    have hsize : (claim.point.extract 4 claim.point.size).toList.length=h+1 := by
      rw [Array.length_toList,Array.size_extract,Nat.min_self,hc]; omega
    have hscale : boundary.scale=eqEval (fun k : Fin 4 => claim.point[k.val]!)
        (fun k : Fin 4 => boundary.point[k.val]!) := nativePackPrefix_scale w d.val claim s values writer value 4
    have hlow : (fun k : Fin 4 => boundary.point[k.val]!) = (fun k : Fin 4 => final.point[k.val]!) := by
      funext k
      exact (nativePackRun_prefix_four w d.val claim s values writer value (by omega) k).2.symm
    have hsem : ∀ high : Fin (h+1) → W,
        packTableCofactor boundary.table claim.weights (h+1) boundary.scale (sum (instanceWeights s)) high =
          eqEval (fun k : Fin 4 => claim.point[k.val]!) (fun k : Fin 4 => final.point[k.val]!)*
            f (joinPoint (a := 4) (b := h+1) (fun k => final.point[k.val]!) high) := by
      intro high
      rw [nativePackBoundary_table,packTableCofactor_protocol w q hn hw d s boundary.scale claim boundary.point hp,
        hscale,hlow]
    have hh := honestCofactorRounds_suffix (a := 4) (b := h+1) f
      (packTableCofactor boundary.table claim.weights (h+1) boundary.scale (sum (instanceWeights s))) hf
      (packTableCofactor_degree boundary.table claim.weights (h+1) boundary.scale (sum (instanceWeights s)))
      (fun k : Fin 4 => claim.point[k.val]!) (fun k : Fin (h+1) => claim.point[4+k.val]!)
      (fun k : Fin 4 => final.point[k.val]!) (fun k : Fin (h+1) => final.point[4+k.val]!) hsem k
    rw [← arrayPoint_join claim.point 4 (h+1),← arrayPoint_join final.point 4 (h+1)] at hh
    have ht := nativePackRun_late_honest_dimension w (by omega) d.val claim (by omega) hbound s writer value
      (h+1) hsize k
    have henter : (fun k : Fin (h+1) => (claim.point.extract 4 claim.point.size).toList[k.val]!) =
        (fun k : Fin (h+1) => claim.point[4+k.val]!) := by
      funext k
      rw [Array.getElem!_toList,packHigh_get claim hc k]
    rw [henter] at ht
    have hi' : (⟨4+k.val,by omega⟩ : Fin (h+5))=i := Fin.ext (by dsimp only [k]; omega)
    rw [hi'] at hh
    have hindex : 4+k.val=i.val := by dsimp only [k]; omega
    rw [hindex] at ht
    exact ht.trans hh.symm

end CompStark.Keccak.GkrProver
