/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.FoldedPackMaps
public import CompStark.Keccak.GkrProver.PackedBlocks

/-! Exact retained pack-table factor values and their production row traversal. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 100000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators

/-- The production sixteen-pack byte-map accumulation for one retained row column. -/
def packedTableValue (w : SlicedWitness) (d : Nat) (mu point : Array W) (m b j : Nat) : W := Id.run do
  let maps := foldedPackMaps mu point
  let state := w.layers[12*(m+1)-d]!
  let groups := 2^w.nLog/64
  let mut value := lane 0
  for q in [:16] do
    let bits := state[j*groups+4*b+q/4]! >>> (16*(q%4)).toUInt64
    let (low,high) := maps[q]!
    value := WordExt3.add value (WordExt3.add low[(bits &&& 255).toNat]!
      high[((bits >>> 8) &&& 255).toNat]!)
  return value

/-- Each retained production cell is the exact sum of its sixteen byte-map pairs. -/
theorem packedTableValue_sum (w : SlicedWitness) (d : Nat) (mu point : Array W) (m b j : Nat) :
    packedTableValue w d mu point m b j =
      ∑ q : Fin 16,
        let bits := (w.layers[12*(m+1)-d]!)[j*(2^w.nLog/64)+4*b+q.val/4]! >>> (16*(q.val%4)).toUInt64
        let maps := (foldedPackMaps mu point)[q.val]!
        maps.1[(bits &&& 255).toNat]!+maps.2[((bits >>> 8) &&& 255).toNat]! := by
  let term (q : Nat) :=
    let bits := (w.layers[12*(m+1)-d]!)[j*(2^w.nLog/64)+4*b+q/4]! >>> (16*(q%4)).toUInt64
    let maps := (foldedPackMaps mu point)[q]!
    maps.1[(bits &&& 255).toNat]!+maps.2[((bits >>> 8) &&& 255).toNat]!
  have hf := foldl_value_sum id (fun value q => value+term q) term (fun _ _ => rfl)
    (List.range 16) (0 : W)
  simp only [id_eq,list_range_sum,zero_add] at hf
  simp only [packedTableValue,Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure,Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range']
  change (List.range 16).foldl (fun value q => value+term q) 0 = _
  rw [hf]
  exact (Fin.sum_univ_eq_sum_range term 16).symm

/-- Each retained production cell is its exact equality-weighted sum of sixteen native RMFE factors. -/
theorem packedTableValue_rmfe (w : SlicedWitness) (d : Nat) (s : W) (point : Array W) (m b j : Nat) :
    packedTableValue w d (instanceWeights s) point m b j =
      ∑ q : Fin 16, (eqTable point)[q.val]! *
        rmfeValue s (lane ((w.layers[12*(m+1)-d]!)[j*(2^w.nLog/64)+4*b+q.val/4]!
          >>> (16*(q.val%4)).toUInt64)) := by
  rw [packedTableValue_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact foldedPackMaps_lookup s point q _

/-- The native retained-table loop is two consecutive structural segment-row fills. -/
theorem packedTable_eq_rows (w : SlicedWitness) (d : Nat) (mu point : Array W) :
    let rows := 2^(w.nLog-4)/16
    packedTable w d mu point =
      writePackedRows
        (writePackedRows (PackedE.zeros (2*rows*1600)) 0 rows 1600
          (packedTableValue w d mu point 0))
        (rows*1600) rows 1600 (packedTableValue w d mu point 1) := by
  simp only [packedTable,writePackedRows,writePackedBlock,packedTableValue,
    Std.Legacy.Range.forIn_eq_forIn_range',List.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure,
    Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range']
  simp only [show List.range 2 = [0,1] from rfl,List.foldl_cons,List.foldl_nil,
    Nat.zero_add,Nat.zero_mul,Nat.one_mul,Nat.add_mul]

/-- The retained native table has one sixteen-pack block per segment and one column per Keccak position. -/
theorem packedTable_size (w : SlicedWitness) (d : Nat) (mu point : Array W) :
    (packedTable w d mu point).size = 2*(2^(w.nLog-4)/16)*1600 := by
  rw [packedTable_eq_rows]
  rw [writePackedRows_size _ _ _ _ _ (by
    rw [writePackedRows_size _ _ _ _ _ (by dsimp only [PackedE.zeros]; omega)]
    dsimp only [PackedE.zeros]
    omega)]
  rw [writePackedRows_size _ _ _ _ _ (by dsimp only [PackedE.zeros]; omega)]
  rfl

/-- Every retained production table cell contains the precise value authored for its segment, block and position. -/
theorem packedTable_get (w : SlicedWitness) (d : Nat) (mu point : Array W)
    (m : Fin 2) (b : Nat) (hb : b < 2^(w.nLog-4)/16) (j : Fin 1600) :
    (packedTable w d mu point).get ((m.val*(2^(w.nLog-4)/16)+b)*1600+j.val) =
      packedTableValue w d mu point m.val b j.val := by
  let rows := 2^(w.nLog-4)/16
  let out := writePackedRows (PackedE.zeros (2*rows*1600)) 0 rows 1600
    (packedTableValue w d mu point 0)
  have hs : out.size = 2*rows*1600 :=
    writePackedRows_size _ _ _ _ _ (by dsimp only [PackedE.zeros]; omega)
  rw [packedTable_eq_rows]
  change (writePackedRows out (rows*1600) rows 1600 (packedTableValue w d mu point 1)).get
    ((m.val*rows+b)*1600+j.val) = _
  have hj := j.isLt
  have hb' : b < rows := hb
  fin_cases m
  · simp only [Nat.zero_mul,Nat.zero_add]
    rw [writePackedRows_prefix _ _ _ _ _ (by rw [hs]; omega) _ (by omega)]
    have hget := writePackedRows_get (PackedE.zeros (2*rows*1600)) 0 rows 1600
      (packedTableValue w d mu point 0) (by dsimp only [PackedE.zeros]; omega)
      b j.val hj (by dsimp only [PackedE.zeros]; omega)
    simpa only [Nat.zero_add,ite_eq_left hb'] using hget
  · simp only [Nat.one_mul]
    rw [show (rows+b)*1600+j.val = rows*1600+b*1600+j.val by ring]
    rw [writePackedRows_get _ _ _ _ _ (by rw [hs]; omega) b j.val hj (by rw [hs]; omega),
      ite_eq_left hb']

/-- The actual retained packed table stores exactly the equality-weighted RMFE factor interpolation. -/
theorem packedTable_get_rmfe (w : SlicedWitness) (d : Nat) (s : W) (point : Array W)
    (m : Fin 2) (b : Nat) (hb : b < 2^(w.nLog-4)/16) (j : Fin 1600) :
    (packedTable w d (instanceWeights s) point).get ((m.val*(2^(w.nLog-4)/16)+b)*1600+j.val) =
      ∑ q : Fin 16, (eqTable point)[q.val]! *
        rmfeValue s (lane ((w.layers[12*(m.val+1)-d]!)[j.val*(2^w.nLog/64)+4*b+q.val/4]!
          >>> (16*(q.val%4)).toUInt64)) := by
  rw [packedTable_get w d _ point m b hb j,packedTableValue_rmfe]

end CompStark.Keccak.GkrProver
