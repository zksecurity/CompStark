/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.TensorRmfe

/-! Extension-coordinate invariants for the native position evaluation maps. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators

/-- Interpret three successive scalar buffer words as one extension-field value. -/
def tripleValue (out : FixedWords n) (i : Nat) : W :=
  ⟨⟨readWord out (3*i)⟩,⟨readWord out (3*i+1)⟩,⟨readWord out (3*i+2)⟩⟩

/-- Store all three coordinates of one extension value in a scalar buffer. -/
def storeTriple (out : FixedWords n) (i : Nat) (v : W) : FixedWords n :=
  writeWord (writeWord (writeWord out (3*i) v.c0.val) (3*i+1) v.c1.val) (3*i+2) v.c2.val

/-- A complete triple store changes exactly its selected extension coordinate. -/
theorem tripleValue_store (out : FixedWords n) (i j : Nat) (v : W)
    (hi : 3*i+2 < n) (hj : 3*j+2 < n) :
    tripleValue (storeTriple out i v) j = if j = i then v else tripleValue out j := by
  unfold tripleValue storeTriple
  by_cases he : j = i
  · subst j
    simp (disch := omega) only [readWord_writeWord,ite_eq_right]
    cases v
    rfl
  · simp (disch := omega) only [readWord_writeWord,ite_eq_right]

/-- Triple-coordinate reads of a zero scalar buffer give the zero extension value. -/
theorem tripleValue_zero (n : Nat) (hn : n < 2^29) (i : Nat) (hi : 3*i+2 < n) :
    tripleValue (zeroWords n hn) i = 0 := by
  have hz (k : Nat) (hk : k < n) : readWord (zeroWords n hn) k = 0 := by
    change readUWord (zeroWords n hn) k.toUSize = 0
    rw [← getUWord_eq_readUWord _ _ ((zeroWords n hn).index_bound k hk)]
    exact getUWord_zeroWords _ _ _ _
  unfold tripleValue
  rw [hz _ (by omega),hz _ (by omega),hz _ (by omega)]
  rfl

/-- The natural-coordinate form of duplicating a subset prefix by one new basis value. -/
def extendMap : Nat → Nat → Nat → W → FixedWords (1600*6*256*3) → FixedWords (1600*6*256*3)
  | 0, _, _, _, out => out
  | count+1, source, target, v, out =>
      extendMap count source target v (storeTriple out (target+count) (tripleValue out (source+count)+v))

/-- A descending subset extension fills its complete target interval and retains every other value. -/
theorem extendMap_get (count source target : Nat) (v : W)
    (out : FixedWords (1600*6*256*3)) (j : Nat)
    (ht : 3*(target+count) ≤ 7372800) (hj : 3*j+2 < 7372800)
    (hs : source+count ≤ target) :
    tripleValue (extendMap count source target v out) j =
      if target ≤ j ∧ j < target+count then tripleValue out (source+(j-target))+v
      else tripleValue out j := by
  induction count generalizing out with
  | zero => rw [extendMap,ite_eq_right (by omega)]
  | succ count ih =>
    rw [extendMap,ih _ (by omega) (by omega)]
    by_cases htail : target ≤ j ∧ j < target+count
    · rw [ite_eq_left htail,ite_eq_left (by omega),tripleValue_store _ _ _ _ (by omega) (by omega),
        ite_eq_right (by omega)]
    · rw [ite_eq_right htail,tripleValue_store _ _ _ _ (by omega) hj]
      by_cases he : j = target+count
      · rw [ite_eq_left he,ite_eq_left (by omega)]
        congr 2
        omega
      · rw [ite_eq_right he,ite_eq_right (by omega)]

/-- The machine-address subset recursion equals duplication of complete extension values. -/
theorem extendWeightByteSpec_eq_map (count source target : Nat) (v : W)
    (out : FixedWords (1600*6*256*3))
    (hs : 3*(source+count) ≤ 7372800) (ht : 3*(target+count) ≤ 7372800) :
    extendWeightByteSpec count (3*source).toUSize (3*target).toUSize
      v.c0.val v.c1.val v.c2.val out = extendMap count source target v out := by
  induction count generalizing out with
  | zero => rfl
  | succ count ih =>
    rw [extendWeightByteSpec,extendMap,ih _ (by omega) (by omega)]
    have h1 (v0 : UInt64) :
        readWord (writeWord out (3*(target+count)) v0) (3*(source+count)+1) =
          readWord out (3*(source+count)+1) := by
      rw [readWord_writeWord _ _ _ (by omega) (by omega),ite_eq_right (by omega)]
    have h2 (v0 v1 : UInt64) :
        readWord (writeWord (writeWord out (3*(target+count)) v0)
          (3*(target+count)+1) v1) (3*(source+count)+2) =
          readWord out (3*(source+count)+2) := by
      rw [readWord_writeWord _ _ _ (by omega) (by omega),ite_eq_right (by omega),
        readWord_writeWord _ _ _ (by omega) (by omega),ite_eq_right (by omega)]
    have htarget : (3*(target+count)).toUSize = (3*target).toUSize+3*count.toUSize := by
      rw [Nat.mul_add]
      simp only [Nat.toUSize,USize.ofNat_add,USize.ofNat_mul]
      rfl
    have hsource : (3*(source+count)).toUSize = (3*source).toUSize+3*count.toUSize := by
      rw [Nat.mul_add]
      simp only [Nat.toUSize,USize.ofNat_add,USize.ofNat_mul]
      rfl
    simp only [readWord,writeWord,Nat.toUSize,USize.ofNat_add] at h1 h2
    simp only [storeTriple,tripleValue]
    change extendMap count source target v
      (writeUWord (writeUWord (writeUWord out ((3*target).toUSize+3*count.toUSize)
        (readUWord out ((3*source).toUSize+3*count.toUSize) ^^^ v.c0.val))
        ((3*target).toUSize+3*count.toUSize+1) _)
        ((3*target).toUSize+3*count.toUSize+2) _) = _
    simp only [readWord,writeWord,Nat.toUSize,USize.ofNat_add,
      show USize.ofNat 1 = (1 : USize) from rfl,
      show USize.ofNat 2 = (2 : USize) from rfl] at htarget hsource h1 h2 ⊢
    rw [htarget,hsource] at h1 h2 ⊢
    rw [h1,h2]
    rfl

/-- The subset sum of the first basis coefficients selected by a byte prefix. -/
def byteSubset (basis : Nat → W) (bits value : Nat) : W :=
  ∑ k ∈ Finset.range bits, if value.testBit k then basis k else 0

/-- Adding a zero high bit retains the lower-prefix subset sum. -/
theorem byteSubset_low (basis : Nat → W) (bits value : Nat) (hv : value < 2^bits) :
    byteSubset basis (bits+1) value = byteSubset basis bits value := by
  rw [byteSubset,Finset.sum_range_succ,Nat.testBit_eq_false_of_lt hv,ite_eq_right (by decide),add_zero]
  rfl

/-- Adding the new high bit appends exactly its new basis coefficient. -/
theorem byteSubset_high (basis : Nat → W) (bits value : Nat) (hv : value < 2^bits) :
    byteSubset basis (bits+1) (2^bits+value) = byteSubset basis bits value+basis bits := by
  rw [byteSubset,Finset.sum_range_succ,Nat.testBit_two_pow_add_eq,
    Nat.testBit_eq_false_of_lt hv,Bool.not_false]
  simp only [ite_true]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.testBit_two_pow_add_gt (Finset.mem_range.mp hk)]

/-- Construct one complete position-byte subset table by successive prefix duplication. -/
def buildWeightByte (source : Nat) (basis : Nat → W) : Nat →
    FixedWords (1600*6*256*3) → FixedWords (1600*6*256*3)
  | 0, out => out
  | bits+1, out => extendMap (2^bits) source (source+2^bits) (basis bits)
      (buildWeightByte source basis bits out)

/-- A byte builder retains every value outside its newly written nonzero subset cells. -/
theorem buildWeightByte_other (source : Nat) (basis : Nat → W) (bits : Nat)
    (out : FixedWords (1600*6*256*3)) (j : Nat)
    (ht : 3*(source+2^bits) ≤ 7372800) (hj : 3*j+2 < 7372800)
    (hother : j ≤ source ∨ source+2^bits ≤ j) :
    tripleValue (buildWeightByte source basis bits out) j = tripleValue out j := by
  induction bits with
  | zero => rfl
  | succ bits ih =>
    rw [buildWeightByte,extendMap_get _ _ _ _ _ j (by rw [pow_succ] at ht; omega) hj (by omega),
      ite_eq_right (by rw [pow_succ] at hother; have hp := Nat.two_pow_pos bits; omega)]
    apply ih (by rw [pow_succ] at ht; omega)
    rw [pow_succ] at hother
    omega

/-- Every constructed byte prefix is its exact basis subset sum. -/
theorem buildWeightByte_get (source : Nat) (basis : Nat → W) (bits : Nat)
    (out : FixedWords (1600*6*256*3)) (value : Nat) (hv : value < 2^bits)
    (ht : 3*(source+2^bits) ≤ 7372800) (hz : tripleValue out source = 0) :
    tripleValue (buildWeightByte source basis bits out) (source+value) = byteSubset basis bits value := by
  induction bits generalizing value with
  | zero =>
    have hv0 : value = 0 := by simpa only [pow_zero,Nat.lt_one_iff] using hv
    rw [hv0,Nat.add_zero,buildWeightByte,hz]
    rfl
  | succ bits ih =>
    rw [buildWeightByte,extendMap_get _ _ _ _ _ (source+value)
      (by rw [pow_succ] at ht; omega) (by rw [pow_succ] at ht hv; omega) (by omega)]
    by_cases hlow : value < 2^bits
    · rw [ite_eq_right (by omega),ih value hlow (by rw [pow_succ] at ht; omega),byteSubset_low _ _ _ hlow]
    · have hhigh : value-2^bits < 2^bits := by rw [pow_succ] at hv; omega
      rw [ite_eq_left (by rw [pow_succ] at hv; omega),
        show source+(source+value-(source+2^bits)) = source+(value-2^bits) by omega,
        ih (value-2^bits) hhigh (by rw [pow_succ] at ht; omega)]
      conv_rhs => rw [show value = 2^bits+(value-2^bits) by omega,byteSubset_high _ _ _ hhigh]

/-- The byte builder is the same structural fold as the native eight-bit prefix loop. -/
theorem buildWeightByte_eq_fold (source : Nat) (basis : Nat → W) (bits : Nat)
    (out : FixedWords (1600*6*256*3)) :
    buildWeightByte source basis bits out =
      (List.range bits).foldl (fun out bit =>
        extendMap (2^bit) source (source+2^bit) (basis bit) out) out := by
  induction bits with
  | zero => rfl
  | succ bits ih =>
    rw [buildWeightByte,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,ih]

/-- Natural-coordinate construction of every position-byte evaluation table. -/
def prepareWeightMapsReference (weights : Array W) (s : W) : FixedWords (1600*6*256*3) :=
  (List.range 1600).foldl (fun out j =>
    (List.range 6).foldl (fun out byte =>
      buildWeightByte (1536*j+256*byte) (fun bit => weights[j]!*s^(8*byte+bit)) 8 out) out)
    (zeroWords (1600*6*256*3))

/-- The native prepared-map loops agree with complete structural byte-prefix construction. -/
theorem prepareWeightMaps_eq_reference (weights : Array W) (s : W) :
    prepareWeightMaps weights (CompStark.Sumcheck.prepare s) = prepareWeightMapsReference weights s := by
  simp (disch := first | exact Membership.mem.upper ‹_› | omega) only
    [prepareWeightMaps,extendWeightByte_eq,weightWidth_eq,weightSource_eq,successiveWeights_eq]
  simp only [forIn'_eq_forIn,Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure,Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range']
  unfold prepareWeightMapsReference
  apply List.foldl_rel (r := Eq) rfl
  intro j hj out other hout
  subst other
  have hj : j < 1600 := List.mem_range.mp hj
  apply List.foldl_rel (r := Eq) rfl
  intro byte hb out other hout
  subst other
  have hb : byte < 6 := List.mem_range.mp hb
  rw [buildWeightByte_eq_fold]
  apply List.foldl_rel (r := Eq) rfl
  intro bit hbit out other hout
  subst other
  have hbit : bit < 8 := List.mem_range.mp hbit
  have hp : 2^bit ≤ 128 := by
    change 2^bit ≤ 2^7
    exact Nat.pow_le_pow_right (by decide) (show bit ≤ 7 by omega)
  have hval : (List.ofFn (fun i : Fin 48 => weights[j]!*s^i.val)).toArray[8*byte+bit]! =
      weights[j]!*s^(8*byte+bit) := by
    rw [List.toArray_ofFn,getElem!_pos _ _ (by simp only [Array.size_ofFn]; omega),Array.getElem_ofFn]
  rw [hval,usize_small (2^bit) (by omega)]
  have htarget : (3*(1536*j+256*byte)).toUSize+3*(2^bit).toUSize =
      (3*(1536*j+256*byte+2^bit)).toUSize := by
    rw [show 3*(1536*j+256*byte+2^bit) = 3*(1536*j+256*byte)+3*2^bit by omega]
    simp only [Nat.toUSize,USize.ofNat_add,USize.ofNat_mul]
    rfl
  rw [htarget,extendWeightByteSpec_eq_map _ _ _ _ _ (by omega) (by omega)]

/-- Every byte table retains its zero subset at the first cell of its block. -/
def WeightMapBasesZero (out : FixedWords (1600*6*256*3)) : Prop :=
  ∀ cell, cell < 9600 → tripleValue out (256*cell) = 0

/-- Building any complete byte table preserves all zero-subset base cells. -/
theorem buildWeightByte_bases (out : FixedWords (1600*6*256*3)) (hz : WeightMapBasesZero out)
    (cell : Nat) (hc : cell < 9600) (basis : Nat → W) :
    WeightMapBasesZero (buildWeightByte (256*cell) basis 8 out) := by
  intro query hq
  rw [buildWeightByte_other _ _ _ _ (256*query) (by omega) (by omega) (by omega),hz query hq]

/-- Building one byte table changes its own block to its basis subset sums and retains other blocks. -/
theorem buildWeightByte_effect (out : FixedWords (1600*6*256*3)) (hz : WeightMapBasesZero out)
    (cell : Nat) (hc : cell < 9600) (basis : Nat → W)
    (query : Nat) (hq : query < 9600) (value : Nat) (hv : value < 256) :
    tripleValue (buildWeightByte (256*cell) basis 8 out) (256*query+value) =
      if cell = query then byteSubset basis 8 value else tripleValue out (256*query+value) := by
  by_cases he : cell = query
  · subst cell
    rw [ite_eq_left rfl,buildWeightByte_get _ _ _ _ value hv (by omega) (hz query hq)]
  · rw [ite_eq_right he,buildWeightByte_other _ _ _ _ (256*query+value)
      (by omega) (by omega) (by omega)]

/-- A list of byte-block updates has the exact selected-block semantics and retains every zero subset. -/
theorem buildWeightMaps_fold (cells : List Nat) (hcell : ∀ c ∈ cells, c < 9600)
    (basis : Nat → Nat → W) (out : FixedWords (1600*6*256*3)) (hz : WeightMapBasesZero out)
    (query : Nat) (hq : query < 9600) (value : Nat) (hv : value < 256) :
    let result := cells.foldl (fun out cell => buildWeightByte (256*cell) (basis cell) 8 out) out
    WeightMapBasesZero result ∧ tripleValue result (256*query+value) =
      if query ∈ cells then byteSubset (basis query) 8 value else tripleValue out (256*query+value) := by
  induction cells generalizing out with
  | nil => exact ⟨hz,rfl⟩
  | cons cell cells ih =>
    dsimp only
    rw [List.foldl_cons]
    have hc : cell < 9600 := hcell cell List.mem_cons_self
    obtain ⟨hb,hget⟩ := ih (fun c hm => hcell c (List.mem_cons_of_mem cell hm))
      (buildWeightByte (256*cell) (basis cell) 8 out) (buildWeightByte_bases out hz cell hc _)
    refine ⟨hb,?_⟩
    rw [hget]
    by_cases ht : query ∈ cells
    · rw [ite_eq_left ht,ite_eq_left (List.mem_cons_of_mem cell ht)]
    · rw [ite_eq_right ht,buildWeightByte_effect out hz cell hc _ query hq value hv]
      by_cases he : cell = query
      · subst cell
        rw [ite_eq_left rfl,ite_eq_left List.mem_cons_self]
      · rw [ite_eq_right he,ite_eq_right (by simp only [List.mem_cons,ht,or_false]; exact Ne.symm he)]

/-- Byte blocks enumerate the position-major and byte-minor map layout. -/
def weightMapCells : List Nat := (List.range 1600).flatMap (fun j => (List.range 6).map (fun byte => 6*j+byte))

/-- Every enumerated position-byte block is inside the complete evaluation map. -/
theorem weightMapCells_bound (cell : Nat) (hc : cell ∈ weightMapCells) : cell < 9600 := by
  obtain ⟨j,hj,hmem⟩ := List.mem_flatMap.mp hc
  obtain ⟨b,hb,he⟩ := List.mem_map.mp hmem
  have hj := List.mem_range.mp hj
  have hb := List.mem_range.mp hb
  omega

/-- Every position-byte block occurs in the structural map construction. -/
theorem weightMapCells_mem (cell : Nat) (hc : cell < 9600) : cell ∈ weightMapCells := by
  apply List.mem_flatMap.mpr
  refine ⟨cell/6,List.mem_range.mpr (by omega),?_⟩
  apply List.mem_map.mpr
  exact ⟨cell%6,List.mem_range.mpr (by omega),by omega⟩

/-- Structural position-byte loops are the fold over their complete position-major block enumeration. -/
theorem prepareWeightMapsReference_eq_fold (weights : Array W) (s : W) :
    prepareWeightMapsReference weights s = weightMapCells.foldl
      (fun out cell => buildWeightByte (256*cell)
        (fun bit => weights[cell/6]!*s^(8*(cell%6)+bit)) 8 out)
      (zeroWords (1600*6*256*3)) := by
  unfold prepareWeightMapsReference weightMapCells
  rw [List.foldl_flatMap]
  apply List.foldl_rel (r := Eq) rfl
  intro j _ out other hout
  subst other
  rw [List.foldl_map]
  apply List.foldl_rel (r := Eq) rfl
  intro byte hb out other hout
  subst other
  have hb : byte < 6 := List.mem_range.mp hb
  rw [show (6*j+byte)/6 = j by omega,show (6*j+byte)%6 = byte by omega,
    show 256*(6*j+byte) = 1536*j+256*byte by omega]

/-- Every prepared native position-byte table is the exact subset sum of its weighted challenge powers. -/
theorem prepareWeightMaps_get (weights : Array W) (s : W)
    (j : Fin 1600) (byte : Fin 6) (value : Fin 256) :
    tripleValue (prepareWeightMaps weights (CompStark.Sumcheck.prepare s))
      (1536*j.val+256*byte.val+value.val) =
      byteSubset (fun bit => weights[j.val]!*s^(8*byte.val+bit)) 8 value.val := by
  rw [prepareWeightMaps_eq_reference,prepareWeightMapsReference_eq_fold]
  have hz : WeightMapBasesZero (zeroWords (1600*6*256*3)) := by
    intro cell hc
    exact tripleValue_zero _ (by decide) _ (by omega)
  have hq : 6*j.val+byte.val < 9600 := by have := j.isLt; have := byte.isLt; omega
  have hf := buildWeightMaps_fold weightMapCells weightMapCells_bound
    (fun cell bit => weights[cell/6]!*s^(8*(cell%6)+bit))
    (zeroWords (1600*6*256*3)) hz (6*j.val+byte.val) hq value.val value.isLt
  rw [ite_eq_left (weightMapCells_mem _ hq)] at hf
  have hd : (6*j.val+byte.val)/6 = j.val := by have := byte.isLt; omega
  have hm : (6*j.val+byte.val)%6 = byte.val := by have := byte.isLt; omega
  simpa only [hd,hm,show 256*(6*j.val+byte.val) = 1536*j.val+256*byte.val by omega] using hf.2

end CompStark.Keccak.GkrProver
