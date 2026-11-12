/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.PackHonest

/-! Exact claim transfer from the four early pack coordinates to the retained native pack table. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 100000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak BF64
open scoped BigOperators

attribute [local irreducible] eqTable packedTable nativeTensorValue

/-- The complete early tensor value is the weighted Boolean sum of the retained pack-table cofactors. -/
theorem nativeTensorValue_packTable (w : SlicedWitness) (d : Nat) (claim : Claim) (s : W)
    (point : Array W) (hp : point.size = 4)
    (hrows : 2^(claim.point.extract 4 claim.point.size).size = 2*(2^(w.nLog-4)/16))
    (haddr : ∀ (b : Nat), b < 2^(w.nLog-4)/16 → ∀ (j : Fin 1600) (q : Fin 16),
      j.val*(2^w.nLog/64)+4*b+q.val/4 < USize.size) :
    nativeTensorValue w d claim s point =
      Gkr.booleanSum (fun rest =>
        Gkr.eqEval (fun k : Fin (claim.point.extract 4 claim.point.size).size =>
          (claim.point.extract 4 claim.point.size)[k.val]!) rest *
        packTableCofactor (packedTable w d (instanceWeights s) point) claim.weights
          (claim.point.extract 4 claim.point.size).size 1 (sum (instanceWeights s)) rest) := by
  let suffix := claim.point.extract 4 claim.point.size
  let rows := 2^(w.nLog-4)/16
  let table := packedTable w d (instanceWeights s) point
  have hsize : table.size = 2*rows*1600 := packedTable_size w d _ point
  rw [booleanSum_eq_residual _ (fun _ => 0),Gkr.residualSum_zero]
  simp only [packTableCofactor,Gkr.mle_cubePoint,Gkr.eqEval_cubePoint,one_mul]
  rw [Fin.sum_univ_eq_sum_range (fun row =>
    Gkr.eqWeight (fun k : Fin suffix.size => suffix[k.val]!) row *
      ∑ j : Fin 1600,claim.weights[j.val]! *
        ((sum (instanceWeights s))*table.toArray[row*1600+j.val]! +
          ((sum (instanceWeights s))+table.toArray[row*1600+shift j.val 1]!)*
            table.toArray[row*1600+shift j.val 2]!)) (2^suffix.size),hrows,range_sum_blocks]
  unfold nativeTensorValue
  apply Finset.sum_congr rfl
  intro m hm
  have hm := Finset.mem_range.mp hm
  apply Finset.sum_congr rfl
  intro b hb
  have hb := Finset.mem_range.mp hb
  have hb' : b < rows := hb
  have hmrows := Nat.mul_le_mul_right rows (show m ≤ 1 by omega)
  have hblock : m*rows+b < 2*rows := by omega
  have hi : rows*m+b < 2^suffix.size := by
    rw [hrows,Nat.mul_comm rows m]
    exact hblock
  rw [← eqTable_get suffix _ hi]
  have hindex : rows*m+b = m*rows+b := by rw [Nat.mul_comm rows m]
  rw [hindex]
  apply congrArg (fun value : W => (eqTable suffix)[m*rows+b]!*value)
  apply Finset.sum_congr rfl
  intro j _
  have hget (j : Fin 1600) : table.toArray[(m*rows+b)*1600+j.val]! =
      binaryInterpolate point.toList
        (tensorFactor s w.layers[12*(m+1)-d]! (2^w.nLog/64) (16*b) j) 0 := by
    rw [PackedE.get_toArray _ _ (by rw [hsize]; exact row_index_lt j.isLt ⟨m*rows+b,hblock⟩)]
    exact packedTable_get_binaryInterpolate w d s point hp ⟨m,hm⟩ b hb j (haddr b hb j)
  rw [hget j,hget ⟨shift j.val 1,(Gkr.along j 1).isLt⟩,
    hget ⟨shift j.val 2,(Gkr.along j 2).isLt⟩]
  rfl

/-- The fourth actual early-pack polynomial evaluates the complete native chi expression at the new point. -/
theorem earlyRound_last (w : SlicedWitness) (hn : 8 ≤ w.nLog) (d : Nat) (claim : Claim)
    (s : W) (bound : Array W) (hb : bound.size = 3) (r : W) :
    let values := earlyValues w d claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
      prepareRmfeProducts (binaryValues (product w d claim prepareRmfeProducts).packs claim.point
        (CompStark.Sumcheck.prepare s))
    (earlyRound values claim.point bound)[0]!+
      r*((earlyRound values claim.point bound)[1]!+r*(earlyRound values claim.point bound)[2]!) =
        nativeTensorValue w d claim s (bound.push r) := by
  dsimp only
  rw [earlyRound_native_evaluate w hn d claim s bound (by omega) r]
  have hs : claim.point.extract (bound.size+1) 4 = #[] := by
    apply Array.toList_inj.mp
    rw [Array.toList_extract]
    simp only [List.extract,hb,Nat.reduceAdd,Nat.sub_self,List.take_zero]
  rw [hs]
  have he : (eqTable (#[] : Array W)).size = 1 := by rw [eqTable_size]; rfl
  rw [he]
  change (∑ row ∈ Finset.range 1,(eqTable #[])[row]!*nativeTensorValue w d claim s
    (earlyFullPoint bound r row)) = _
  rw [Finset.sum_range_one]
  have hw : (eqTable (#[] : Array W))[0]! = 1 := by unfold eqTable; rfl
  rw [hw,one_mul]
  have hp : earlyFullPoint bound r 0 = bound.push r := by
    simp only [earlyFullPoint,hb,Nat.sub_self,booleanSuffix,List.append_nil]
    exact Array.toList_inj.mp (by simp only [Array.toList_push])
  rw [hp]

/-- A well-shaped entering claim leaves exactly the retained native table's high pack coordinates. -/
theorem packBoundary_rows (w : SlicedWitness) (hn : 8 ≤ w.nLog) (claim : Claim)
    (hc : claim.point.size = w.nLog-3) :
    2^(claim.point.extract 4 claim.point.size).size = 2*(2^(w.nLog-4)/16) := by
  have hs : (claim.point.extract 4 claim.point.size).size = w.nLog-7 := by
    rw [Array.size_extract,Nat.min_self,hc]
    omega
  rw [hs,show w.nLog-4 = (w.nLog-8)+4 by omega,pow_add]
  rw [show 2^4 = (16 : Nat) from rfl,Nat.mul_div_cancel _ (by decide),
    show w.nLog-7 = (w.nLog-8)+1 by omega,pow_succ]
  omega

/-- The retained block's machine addresses follow from the complete sliced layer's allocation bound. -/
theorem packBoundary_address (w : SlicedWitness) (hn : 8 ≤ w.nLog)
    (hbound : 1600*(2^w.nLog/64) ≤ USize.size)
    (b : Nat) (hb : b < 2^(w.nLog-4)/16) (j : Fin 1600) (q : Fin 16) :
    j.val*(2^w.nLog/64)+4*b+q.val/4 < USize.size := by
  have hgroups : 2^w.nLog/64 = 4*(2^(w.nLog-4)/16) := by
    rw [show w.nLog = (w.nLog-8)+8 by omega,pow_add,
      show (w.nLog-8)+8-4 = (w.nLog-8)+4 by omega,pow_add]
    norm_num
    omega
  have hg : 4*b+q.val/4 < 2^w.nLog/64 := by rw [hgroups]; have := q.isLt; omega
  have h := lt_of_lt_of_le (row_index_lt hg j) hbound
  simpa only [Nat.add_assoc] using h

/-- Scaling an actual early cofactor array preserves its three complete transmitted coefficients. -/
theorem earlyRound_map_get (values entering bound : Array W) (scale : W) (k : Nat) (hk : k < 3) :
    ((earlyRound values entering bound).map (scale*·))[k]! = scale*(earlyRound values entering bound)[k]! := by
  have hs : (earlyRound values entering bound).size = 3 := by rw [earlyRound_eq]; rfl
  rw [getElem!_pos _ _ (by rw [Array.size_map,hs]; exact hk),Array.getElem_map,
    ← getElem!_pos _ _ (by rw [hs]; exact hk)]

/-- The actual fourth early transition initializes the full remaining-sum invariant used by native pack reconstruction. -/
theorem packBoundary_running_sum (w : SlicedWitness) (hn : 8 ≤ w.nLog) (d : Nat) (claim : Claim)
    (hc : claim.point.size = w.nLog-3) (hbound : 1600*(2^w.nLog/64) ≤ USize.size)
    (s : W) (bound : Array W) (hb : bound.size = 3) (scale r : W) :
    let values := earlyValues w d claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
      prepareRmfeProducts (binaryValues (product w d claim prepareRmfeProducts).packs claim.point
        (CompStark.Sumcheck.prepare s))
    let coefficients := (earlyRound values claim.point bound).map (scale*·)
    (1+claim.point[3]!+r)*(coefficients[0]!+r*(coefficients[1]!+r*coefficients[2]!)) =
      Gkr.booleanSum (fun rest =>
        Gkr.eqEval (fun k : Fin (claim.point.extract 4 claim.point.size).size =>
          (claim.point.extract 4 claim.point.size)[k.val]!) rest *
        packTableCofactor (packedTable w d (instanceWeights s) (bound.push r)) claim.weights
          (claim.point.extract 4 claim.point.size).size (scale*(1+claim.point[3]!+r))
            (sum (instanceWeights s)) rest) := by
  dsimp only
  simp only [earlyRound_map_get _ _ _ _ 0 (by decide),earlyRound_map_get _ _ _ _ 1 (by decide),
    earlyRound_map_get _ _ _ _ 2 (by decide)]
  let values := earlyValues w d claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
    prepareRmfeProducts (binaryValues (product w d claim prepareRmfeProducts).packs claim.point
      (CompStark.Sumcheck.prepare s))
  have hfactor :
      (1+claim.point[3]!+r)*(scale*(earlyRound values claim.point bound)[0]!+
        r*(scale*(earlyRound values claim.point bound)[1]!+r*(scale*(earlyRound values claim.point bound)[2]!))) =
      (scale*(1+claim.point[3]!+r))*((earlyRound values claim.point bound)[0]!+
        r*((earlyRound values claim.point bound)[1]!+r*(earlyRound values claim.point bound)[2]!)) := by ring
  rw [hfactor,earlyRound_last w hn d claim s bound hb r,
    nativeTensorValue_packTable w d claim s (bound.push r) (by rw [Array.size_push,hb])
      (packBoundary_rows w hn claim hc) (packBoundary_address w hn hbound)]
  have hscale (point : Fin (claim.point.extract 4 claim.point.size).size → W) :
      packTableCofactor (packedTable w d (instanceWeights s) (bound.push r)) claim.weights
        (claim.point.extract 4 claim.point.size).size (scale*(1+claim.point[3]!+r)) (sum (instanceWeights s)) point =
      (scale*(1+claim.point[3]!+r))*packTableCofactor
        (packedTable w d (instanceWeights s) (bound.push r)) claim.weights
        (claim.point.extract 4 claim.point.size).size 1 (sum (instanceWeights s)) point := by
    simpa only [mul_one] using packTableCofactor_scale
      (packedTable w d (instanceWeights s) (bound.push r)) claim.weights
      (claim.point.extract 4 claim.point.size).size (scale*(1+claim.point[3]!+r)) 1
      (sum (instanceWeights s)) point
  simp only [Gkr.booleanSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro point _
  rw [hscale]
  ring

end CompStark.Keccak.GkrProver
