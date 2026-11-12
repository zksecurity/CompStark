/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.Native
public import CompStark.Keccak.GkrProver.RmfeProofs
public import CompStark.Keccak.GkrProver.PackedProofs
public import CompStark.Keccak.GkrProver.Honest
public import CompStark.Pcs.Bits
import Init.Data.Array.Monadic
import Mathlib.Data.List.Induction

/-! Protocol interpretations and proved word-level coefficient operations. -/

set_option maxRecDepth 32768

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak CompStark.BinaryFields BF64
open scoped BigOperators

/-- The word extension inherits the specification's characteristic. -/
instance : CharP W 2 := WordExt3.ringEquiv.toRingHom.charP WordExt3.ringEquiv.injective 2

/-- Materialized rotations preserve every protocol lookup. -/
theorem rotations_eq (l : Fin 25) : rotations[l.val]! = Gkr.rho l := by
  simp only [rotations, getElem!_pos, Array.getElem_ofFn, Array.size_ofFn, Fin.isLt]

/-- Every source round constant fits in one machine word. -/
theorem constant_bound : ∀ r : Fin 24, Gkr.roundConstants r < 2^64 := by decide

/-- Materialized constants preserve all 64 public iota bits. -/
theorem constants_eq (r : Fin 24) : constants[r.val]!.toNat = Gkr.roundConstants r := by
  simp only [constants, getElem!_pos, Array.getElem_ofFn, Array.size_ofFn, Fin.isLt, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (constant_bound r)]

/-- Interpret one simultaneous lane of a sliced word as a Boolean field element. -/
def sliceBit (word : UInt64) (b : Fin 64) : ZMod 2 :=
  if word.toBitVec.getLsbD b.val then 1 else 0

/-- Slicing commutes with XOR addition. -/
theorem sliceBit_xor (a c : UInt64) (b : Fin 64) :
    sliceBit (a ^^^ c) b = sliceBit a b + sliceBit c b := by
  simp only [sliceBit, UInt64.toBitVec_xor, BitVec.getLsbD_xor]
  cases a.toBitVec.getLsbD b.val <;> cases c.toBitVec.getLsbD b.val <;> decide

/-- Slicing commutes with the complete chi gate. -/
theorem sliceBit_chi (a c d : UInt64) (b : Fin 64) :
    sliceBit (a ^^^ (~~~c &&& d)) b = sliceBit a b + (1+sliceBit c b)*sliceBit d b := by
  simp only [sliceBit, UInt64.toBitVec_xor, UInt64.toBitVec_and, UInt64.toBitVec_not,
    BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, b.isLt]
  cases a.toBitVec.getLsbD b.val <;> cases c.toBitVec.getLsbD b.val <;>
    cases d.toBitVec.getLsbD b.val <;> decide

/-- The packed byte transpose sends each source row bit to its corresponding column. -/
theorem transposeByte_bit (x : UInt64) (i j : Fin 8) :
    (transposeByte x).toBitVec.getLsbD (8*i.val+j.val) =
      x.toBitVec.getLsbD (8*j.val+i.val) := by
  fin_cases i <;> fin_cases j <;>
    simp [transposeByte, UInt64.toBitVec_xor, UInt64.toBitVec_and,
      UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, UInt64.toBitVec_ofNat,
      BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', Bool.xor_left_comm]

/-- Transposing a packed byte matrix twice preserves all sixty-four input bits. -/
theorem transposeByte_involutive (x : UInt64) : transposeByte (transposeByte x) = x := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let row : Fin 8 := ⟨i/8, by omega⟩
  let col : Fin 8 := ⟨i%8, Nat.mod_lt _ (by decide)⟩
  have h := (transposeByte_bit (transposeByte x) row col).trans (transposeByte_bit x col row)
  simpa only [row, col, show 8*(i/8)+i%8 = i by omega] using h

/-- Byte transposition commutes with the Boolean witness interpretation. -/
theorem sliceBit_transposeByte (x : UInt64) (i j : Fin 8) :
    sliceBit (transposeByte x) ⟨8*i.val+j.val, by omega⟩ =
      sliceBit x ⟨8*j.val+i.val, by omega⟩ := by
  simp only [sliceBit, transposeByte_bit]

/-- Word instance weights are exactly the certified RMFE column evaluations. -/
theorem instanceWeights_eq (s : W) (i : Fin 16) :
    (instanceWeights s)[i.val]! = Gkr.muAt s i := by
  simpa only [instanceWeights, embeddingColumns, getElem!_pos, Array.getElem_ofFn, Array.size_ofFn,
    Fin.isLt, wordPower_eq, wordSum_eq, mu, show lane 0 = (0 : W) from rfl] using mu_eq s i

/-- RMFE column evaluation commutes with the proven word-field isomorphism. -/
theorem mu_toField (s : W) (i : Fin 16) :
    (mu s i).toField = Gkr.muAt s.toField i := by
  rw [← mu_eq]
  change WordExt3.ringEquiv (mu s i) = mu (WordExt3.ringEquiv s) i
  simp only [mu, map_sum]
  apply Finset.sum_congr rfl
  intro c _
  split <;> simp only [map_pow, map_zero]

/-- Interpret every authored layer coordinate as the protocol's concrete extension field. -/
def Layer.toProtocol (p : Nat) (layer : Layer) : Gkr.LayerTranscript E p where
  product i := layer.product[i.val]!.toField
  point := layer.s.toField
  packPolys i := ((layer.packMessages[i.val]!)[0]!.toField,
    fun _ => (layer.packMessages[i.val]!)[1]!.toField)
  packPoint i := layer.packPoint[i.val]!.toField
  positionPolys i := ((layer.positionMessages[i.val]!)[0]!.toField,
    fun k => (layer.positionMessages[i.val]!)[k.val+1]!.toField)
  positionPoint i := layer.positionPoint[i.val]!.toField
  evaluations i := layer.evaluations[i.val]!.toField
  beta := layer.beta.toField

/-- Interpret the complete authored transcript in the model used by the knowledge certificate. -/
def Reduction.toProtocol (p : Nat) (result : Reduction) (height : result.layers.size = 12) :
    Gkr.Transcript E p where
  instancePoint i := result.batchPoint[i.val]!.toField
  segment := result.segment.toField
  lanePoint i := result.lanes[i.val]!.toField
  middleValue := result.middle.toField
  layers i := (result.layers[i.val]'(by rw [height]; exact i.isLt)).toProtocol p
  openings := {
    outputPolys i := ((result.openings.outputMessages[i.val]!)[0]!.toField,
      fun _ => (result.openings.outputMessages[i.val]!)[1]!.toField)
    outputPoint i := result.openings.outputPoint[i.val]!.toField
    outputValue := result.openings.outputValue.toField
    inputPolys i := ((result.openings.inputMessages[i.val]!)[0]!.toField,
      fun _ => (result.openings.inputMessages[i.val]!)[1]!.toField)
    inputPoint i := result.openings.inputPoint[i.val]!.toField
    slices i := result.openings.slices[i.val]!.toField }

/-- Word interpolation preserves the precise extension-field affine expression. -/
theorem line_toField (a b r : W) :
    (line a b r).toField = (1-r.toField)*a.toField+r.toField*b.toField := by
  rw [line_eq]
  change WordExt3.ringEquiv ((1-r)*a+r*b) = _
  rw [map_add, map_mul, map_mul, map_sub, map_one]
  rfl

/-- A position-major row and its in-row group form an in-bounds array coordinate. -/
theorem row_index_lt {n groups g : Nat} (hg : g < groups) (j : Fin n) :
    j.val*groups+g < n*groups := by
  calc
    _ < j.val*groups+groups := Nat.add_lt_add_left hg _
    _ = (j.val+1)*groups := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ n*groups := Nat.mul_le_mul_right groups (by omega)

/-- Numeric row decoding preserves the position and the simultaneous-instance group. -/
theorem row_div {groups g : Nat} (hg : g < groups) (j : Nat) :
    (j*groups+g)/groups = j := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hg, Nat.zero_add]

/-- Numeric row decoding preserves the in-row group. -/
theorem row_mod {groups g : Nat} (hg : g < groups) (j : Nat) :
    (j*groups+g)%groups = g := by
  rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hg]

/-- Complementing all simultaneous bits adds the Boolean field identity. -/
theorem sliceBit_not (a : UInt64) (b : Fin 64) : sliceBit (~~~a) b = 1+sliceBit a b := by
  simp only [sliceBit, UInt64.toBitVec_not, BitVec.getLsbD_not, b.isLt]
  cases a.toBitVec.getLsbD b.val <;> decide

/-- Numeric row shifts implement the protocol's five-column chi permutation. -/
theorem shift_eq (j : Fin 1600) (k : Nat) : shift j.val k = (Gkr.along j k).val := rfl

/-- Every bit of the executable chi/iota layer is the protocol's nonlinear gate and public constant. -/
theorem chiSlices_eq (state : Array UInt64) {groups g : Nat} (hg : g < groups)
    (r : Fin 24) (j : Fin 1600) (b : Fin 64) :
    sliceBit (chiSlices state groups r.val)[j.val*groups+g]! b =
      sliceBit state[j.val*groups+g]! b +
        (1+sliceBit state[(Gkr.along j 1).val*groups+g]! b)*
          sliceBit state[(Gkr.along j 2).val*groups+g]! b +
        if j.val < 64 ∧ (Gkr.roundConstants r).testBit j.val then 1 else 0 := by
  have bound := row_index_lt hg j
  rw [getElem!_pos (chiSlices state groups r.val) _ (by
    simpa only [chiSlices, Array.size_ofFn] using bound)]
  simp only [chiSlices, Array.getElem_ofFn, row_div hg, row_mod hg, Nat.mod_eq_of_lt r.isLt, constants_eq,
    shift_eq]
  split <;> rename_i h
  · rw [sliceBit_not, sliceBit_chi]
    have h' : j.val < 64 ∧ (Gkr.roundConstants r).testBit j.val := by simpa using h
    rw [ite_eq_left h']
    ring
  · rw [sliceBit_chi]
    have h' : ¬(j.val < 64 ∧ (Gkr.roundConstants r).testBit j.val) := by simpa using h
    rw [ite_eq_right h', add_zero]

/-- The executable pairwise fold has the exact suffix-cube length. -/
theorem fold_size {F : Type*} [CommRing F] [Inhabited F] {n : Nat}
    (table : Array F) (shape : table.size = 2^(n+1)) (r : F) :
    (fold table 1 r).size = 2^n := by
  simp only [fold, Array.size_ofFn, shape, mul_one, pow_succ, Nat.mul_div_cancel (2^n) (by decide : 0 < 2)]

/-- Every actual array-fold cell is the corresponding typed multilinear fold. -/
theorem fold_get {F : Type*} [CommRing F] [Inhabited F] {n : Nat}
    (table : Array F) (shape : table.size = 2^(n+1)) (r : F) (i : Fin (2^n)) :
    (fold table 1 r)[i.val]! = foldCube (fun j => table[j.val]!) r i := by
  have bound : i.val < table.size/(2*1)*1 := by
    simpa only [shape, mul_one, pow_succ, Nat.mul_div_cancel (2^n) (by decide : 0 < 2)] using i.isLt
  rw [getElem!_pos (fold table 1 r) _ (by
    simpa only [fold, Array.size_ofFn] using bound)]
  simp only [fold, Array.getElem_ofFn, Nat.div_one, Nat.mod_one, mul_one, Nat.add_zero, foldCube]

/-- The runtime array fold preserves evaluation at the remaining suffix coordinates. -/
theorem fold_mle {F : Type*} [CommRing F] [CharP F 2] [Inhabited F] {n : Nat}
    (table : Array F) (shape : table.size = 2^(n+1)) (r : F) (point : Fin n → F) :
    Gkr.mle (fun i : Fin (2^n) => (fold table 1 r)[i.val]!) point =
      Gkr.mle (fun i : Fin (2^(n+1)) => table[i.val]!) (Fin.cons r point) := by
  simp only [fold_get table shape]
  exact foldCube_mle _ _ _

/-- Reading a materialized row-major table agrees with its dimension-indexed constructor. -/
theorem row_ofFn {A : Type*} [Inhabited A] {n groups g : Nat} (hg : g < groups)
    (f : Fin (n*groups) → A) (j : Fin n) :
    (Array.ofFn f)[j.val*groups+g]! = f ⟨j.val*groups+g, row_index_lt hg j⟩ := by
  rw [getElem!_pos (Array.ofFn f) _ (by
    simpa only [Array.size_ofFn] using row_index_lt hg j)]
  exact Array.getElem_ofFn _

/-- Sliced column parity is the sum of its five underlying Boolean coordinates. -/
theorem columnSlices_eq (state : Array UInt64) {groups g : Nat} (hg : g < groups)
    (c : Fin 320) (b : Fin 64) :
    sliceBit ((Array.ofFn fun i : Fin (320*groups) =>
      let k := i.val/groups
      let h := i.val%groups
      state[k*groups+h]! ^^^ state[(k+320)*groups+h]! ^^^ state[(k+640)*groups+h]! ^^^
        state[(k+960)*groups+h]! ^^^ state[(k+1280)*groups+h]!)[c.val*groups+g]!) b =
      ∑ y : Fin 5, sliceBit state[(c.val+320*y.val)*groups+g]! b := by
  rw [row_ofFn hg]
  simp only [row_div hg, row_mod hg, sliceBit_xor]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  norm_num only [Nat.reduceAdd, Nat.reduceMul, Nat.mul_one, add_assoc, add_zero]

/-- Every simultaneous bit of the executable theta/rho/pi layer is the protocol's linear map. -/
theorem linearSlices_eq (state : Array UInt64) {groups g : Nat} (hg : g < groups)
    (j : Fin 1600) (b : Fin 64) :
    sliceBit (linearSlices state groups)[j.val*groups+g]! b =
      Gkr.linear (fun k => sliceBit state[k.val*groups+g]! b) j := by
  unfold linearSlices
  rw [row_ofFn hg]
  simp only [row_div hg, row_mod hg, rotations_eq, sliceBit_xor]
  let l := Gkr.inversePi (j.val/64)
  let z := (j.val%64+64-Gkr.rho l)%64
  have hz : z < 64 := Nat.mod_lt _ (by decide)
  have hm : 64*((l.val%5+4)%5)+z < 320 := by omega
  have hp : 64*((l.val%5+1)%5)+(z+63)%64 < 320 := by omega
  rw [columnSlices_eq state hg ⟨_, hm⟩ b, columnSlices_eq state hg ⟨_, hp⟩ b]
  unfold Gkr.linear
  change _ = sliceBit state[(64*l.val+z)*groups+g]! b +
    (∑ y : Fin 5, sliceBit state[(64*((l.val%5+4)%5+5*y.val)+z)*groups+g]! b) +
    (∑ y : Fin 5, sliceBit state[(64*((l.val%5+1)%5+5*y.val)+(z+63)%64)*groups+g]! b)
  have index (x t y : Nat) : 64*x+t+320*y = 64*(x+5*y)+t := by omega
  simp only [index]
  rfl

/-- A complete sliced round refines the exact bit-level round in the GKR protocol. -/
theorem roundSlices_eq (state : Array UInt64) {groups g : Nat} (hg : g < groups)
    (r : Fin 24) (j : Fin 1600) (b : Fin 64) :
    sliceBit (chiSlices (linearSlices state groups) groups r.val)[j.val*groups+g]! b =
      Gkr.round r (fun k => sliceBit state[k.val*groups+g]! b) j := by
  rw [chiSlices_eq _ hg]
  simp only [linearSlices_eq _ hg]
  rfl

/-- Every retained column of a row-major runtime fold binds the same low cube coordinate. -/
theorem fold_column_get {F : Type*} [CommRing F] [Inhabited F] {n width : Nat}
    (table : Array F) (shape : table.size = 2^(n+1)*width) (r : F)
    (i : Fin (2^n)) (c : Fin width) :
    (fold table width r)[i.val*width+c.val]! =
      foldCube (fun j => table[j.val*width+c.val]!) r i := by
  have hw : 0 < width := by have := c.isLt; omega
  have length : table.size/(2*width)*width = 2^n*width := by
    rw [shape, pow_succ, Nat.mul_assoc, Nat.mul_div_cancel _ (by omega)]
  rw [getElem!_pos (fold table width r) _ (by
    simpa only [fold, Array.size_ofFn, length] using row_index_lt c.isLt i)]
  simp only [fold, Array.getElem_ofFn, row_div c.isLt, row_mod c.isLt, foldCube]

/-- Row-major folding preserves each column's suffix multilinear evaluation. -/
theorem fold_column_mle {F : Type*} [CommRing F] [CharP F 2] [Inhabited F] {n width : Nat}
    (table : Array F) (shape : table.size = 2^(n+1)*width) (r : F)
    (point : Fin n → F) (c : Fin width) :
    Gkr.mle (fun i : Fin (2^n) => (fold table width r)[i.val*width+c.val]!) point =
      Gkr.mle (fun i : Fin (2^(n+1)) => table[i.val*width+c.val]!) (Fin.cons r point) := by
  simp only [fold_column_get table shape]
  exact foldCube_mle _ _ _

/-- Native row-major folding preserves the protocol's multilinear evaluation in every retained column. -/
theorem foldPacked_column_mle {n width : Nat} (table : PackedE)
    (shape : table.size = 2^(n+1)*width) (r : W) (point : Fin n → W) (c : Fin width) :
    Gkr.mle (fun i : Fin (2^n) => (foldPacked table width r).toArray[i.val*width+c.val]!) point =
      Gkr.mle (fun i : Fin (2^(n+1)) => table.toArray[i.val*width+c.val]!) (Fin.cons r point) := by
  rw [foldPacked_toArray]
  apply fold_column_mle
  simpa only [PackedE.toArray, Array.size_ofFn] using shape

/-- Prepared equality expansion computes the same shared-scalar products as the word kernel. -/
theorem eqTablePreparedLoop_eq (table : Array W) (r : W) (n : Nat) (out : Array W) :
    eqTablePreparedLoop table (CompStark.Sumcheck.prepare r) n out = eqTableStepLoop table r n out := by
  induction n generalizing out with
  | zero => rfl
  | succ n ih => rw [eqTablePreparedLoop,eqTableStepLoop,CompStark.Sumcheck.prepared_mul_eq,ih]

/-- Equality expansion preserves its allocated buffer length. -/
theorem eqTableStepLoop_size (table : Array W) (r : W) (n : Nat) (out : Array W) :
    (eqTableStepLoop table r n out).size = out.size := by
  induction n generalizing out with
  | zero => rfl
  | succ n ih => rw [eqTableStepLoop,ih,Array.size_set!,Array.size_set!]

/-- Equality expansion writes the low and high prefixes and preserves every other entry. -/
theorem eqTableStepLoop_get (table : Array W) (r : W) (n : Nat) (out : Array W)
    (hn : n ≤ table.size) (ho : 2*table.size ≤ out.size) (i : Nat) (hi : i < out.size) :
    (eqTableStepLoop table r n out)[i]! =
      if i < n then table[i]!+r*table[i]!
      else if table.size ≤ i ∧ i < table.size+n then r*table[i-table.size]! else out[i]! := by
  induction n generalizing out with
  | zero => simp only [eqTableStepLoop,Nat.not_lt_zero,Nat.add_zero,ite_false,
      show ¬(table.size ≤ i ∧ i < table.size) by omega]
  | succ n ih =>
    rw [eqTableStepLoop,ih _ (by omega) (by simpa only [Array.size_set!] using ho)
      (by simpa only [Array.size_set!] using hi)]
    by_cases he : i = n
    · subst i
      rw [ite_eq_right (by omega),ite_eq_right (by omega),
        Array.getElem!_set!_ne _ _ _ _ (by omega),Array.getElem!_set!_self _ _ _ (by omega),
        ite_eq_left (by omega)]
      rfl
    · by_cases hh : i = table.size+n
      · subst i
        rw [ite_eq_right (by omega),ite_eq_right (by omega),
          Array.getElem!_set!_self _ _ _ (by simp only [Array.size_set!]; omega),
          ite_eq_right (by omega),ite_eq_left (by omega)]
        rw [Nat.add_sub_cancel_left]
        rfl
      · have hl : (i < n) = (i < n+1) := propext (by omega)
        have hh' : (table.size ≤ i ∧ i < table.size+n) =
            (table.size ≤ i ∧ i < table.size+(n+1)) := propext (by omega)
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hh),
          Array.getElem!_set!_ne _ _ _ _ (Ne.symm he)]
        simp only [hl,hh']

/-- One-product equality expansion is exactly the low and high Boolean equality blocks. -/
theorem eqTableStep_eq (table : Array W) (r : W) :
    eqTableStep table r = table.map (fun a => a*(1+r)) ++ table.map (fun a => a*r) := by
  unfold eqTableStep
  split <;> simp only [eqTablePreparedLoop_eq]
  all_goals
    apply Array.ext
    · simp only [eqTableStepLoop_size,Array.size_replicate,Array.size_append,Array.size_map]
      omega
    · intro i hi hj
      have hb : i < 2*table.size := by
        simpa only [eqTableStepLoop_size,Array.size_replicate] using hi
      rw [← getElem!_pos _ i hi,eqTableStepLoop_get _ _ _ _ (by omega)
        (by simp only [Array.size_replicate]; omega) i (by simpa only [Array.size_replicate] using hb)]
      by_cases hl : i < table.size
      · rw [ite_eq_left hl,Array.getElem_append_left (by simpa only [Array.size_map] using hl),
          Array.getElem_map,getElem!_pos _ i hl]
        change table[i]+r*table[i] = table[i]*(1+r)
        ring
      · rw [ite_eq_right hl,ite_eq_left (by omega),
          Array.getElem_append_right (by simp only [Array.size_map]; omega)]
        simp only [Array.size_map,Array.getElem_map]
        rw [getElem!_pos _ _ (by omega)]
        change r*table[i-table.size] = table[i-table.size]*r
        exact mul_comm _ _

/-- Appending a challenge appends its low and high Boolean-cube blocks. -/
theorem eqTable_push (point : Array W) (r : W) : eqTable (point.push r) =
    (eqTable point).map (fun a => a*(1+r)) ++ (eqTable point).map (fun a => a*r) := by
  simp only [eqTable, Array.forIn_pure_yield_eq_foldl, pure_bind, Array.foldl_push]
  exact eqTableStep_eq _ _

/-- The actual native equality table has one entry for each Boolean assignment. -/
theorem eqTable_size (point : Array W) : (eqTable point).size = 2^point.size := by
  rcases point with ⟨xs⟩
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs r ih =>
    have he : ({toList := xs ++ [r]} : Array W) = xs.toArray.push r := by
      apply Array.toList_inj.mp
      simp only [Array.toList_push]
    rw [he]
    rw [eqTable_push]
    simp only [Array.size_append, Array.size_map, Array.size_push, pow_succ]
    change (eqTable xs.toArray).size+(eqTable xs.toArray).size = 2^xs.toArray.size*2
    rw [ih]
    simp only [Array.size]
    omega

/-- A native equality-table block binds exactly the highest Boolean coordinate. -/
theorem eqTable_push_get (point : Array W) (r : W) (i : Fin (2^point.size)) (m : Fin 2) :
    (eqTable (point.push r))[i.val+2^point.size*m.val]! =
      (eqTable point)[i.val]! * (if m.val=0 then 1+r else r) := by
  have hsize := eqTable_size point
  have hi := i.isLt
  rw [eqTable_push]
  fin_cases m
  · simp only [Nat.mul_zero, Nat.add_zero, ite_true]
    rw [getElem!_pos _ _ (by simp only [Array.size_append, Array.size_map, hsize]; omega)]
    rw [Array.getElem_append_left (by simpa only [Array.size_map, hsize] using hi), Array.getElem_map,
      getElem!_pos _ _ (by omega)]
  · simp only [Nat.mul_one, Nat.one_ne_zero, ite_false]
    rw [getElem!_pos _ _ (by simp only [Array.size_append, Array.size_map, hsize]; omega)]
    rw [Array.getElem_append_right (by simp only [Array.size_map, hsize]; omega)]
    simp only [Array.size_map, hsize, Nat.add_sub_cancel_right, Array.getElem_map]
    rw [getElem!_pos (eqTable point) i.val (by omega)]

/-- Induction on arrays by appending their final coordinate. -/
private theorem arrayPushInduction {A : Type} (P : Array A → Prop) (empty : P #[])
    (push : ∀ point r, P point → P (point.push r)) (point : Array A) : P point := by
  rcases point with ⟨xs⟩
  induction xs using List.reverseRecOn with
  | nil => exact empty
  | append_singleton xs r ih =>
    have he : ({toList := xs ++ [r]} : Array A) = ({toList := xs} : Array A).push r := by
      apply Array.toList_inj.mp
      simp only [Array.toList_push]
    rw [he]
    exact push _ _ ih

/-- Protocol equality weights split at an appended array challenge. -/
theorem eqWeight_array_push (point : Array W) (r : W) (b : Fin (2^point.size)) (m : Fin 2) :
    Gkr.eqWeight (fun j : Fin (point.push r).size => (point.push r)[j.val]!) (b.val+2^point.size*m.val) =
      Gkr.eqWeight (fun j : Fin point.size => point[j.val]!) b.val * (if m.val=0 then 1+r else r) := by
  have h := Gkr.eqWeight_last (fun j : Fin (point.size+1) => (point.push r)[j.val]!) b m
  rw [Array.size_push]
  rw [h]
  have low : (fun j : Fin point.size => (point.push r)[j.castSucc.val]!) =
      (fun j : Fin point.size => point[j.val]!) := by
    funext j
    simp only [Fin.val_castSucc]
    rw [getElem!_pos _ _ (by rw [Array.size_push]; have := j.isLt; omega),
      Array.getElem_push_lt j.isLt, getElem!_pos point j.val j.isLt]
  rw [low]
  have high : (point.push r)[(Fin.last point.size).val]! = r := by
    rw [Fin.val_last, getElem!_pos _ _ (by rw [Array.size_push]; omega), Array.getElem_push_eq]
  rw [high, CharTwo.sub_eq_add]

/-- Every native equality-table entry is the protocol Boolean-cube weight. -/
theorem eqTable_get (point : Array W) : ∀ (i : Nat), i < 2^point.size →
    (eqTable point)[i]! = Gkr.eqWeight (fun j : Fin point.size => point[j.val]!) i := by
  induction point using arrayPushInduction with
  | empty =>
    intro i hi
    have hi : i < 1 := by simpa only [Array.size_empty, pow_zero] using hi
    have hi : i=0 := by omega
    subst i
    simp only [eqTable, Gkr.eqWeight]
    rfl
  | push point r ih =>
    intro i hi
    have hp := Nat.two_pow_pos point.size
    have hi' : i < 2^point.size*2 := by simpa only [Array.size_push, pow_succ] using hi
    let b : Fin (2^point.size) := ⟨i % 2^point.size, Nat.mod_lt _ hp⟩
    let m : Fin 2 := ⟨i / 2^point.size, (Nat.div_lt_iff_lt_mul hp).mpr (by simpa only [Nat.mul_comm] using hi')⟩
    have index : i = b.val+2^point.size*m.val := by dsimp only [b,m]; exact (Nat.mod_add_div _ _).symm
    rw [index, eqTable_push_get, eqWeight_array_push, ih b.val b.isLt]

/-- Native equality-table weights commute with the certified word-field isomorphism. -/
theorem eqTable_get_toField (point : Array W) (i : Nat) (hi : i < 2^point.size) :
    ((eqTable point)[i]!).toField = Gkr.eqWeight (fun j : Fin point.size => point[j.val]!.toField) i := by
  rw [eqTable_get point i hi]
  change WordExt3.ringEquiv (Gkr.eqWeight _ i) = _
  simp only [Gkr.eqWeight, map_prod]
  apply Finset.prod_congr rfl
  intro j _
  split
  · rfl
  · rw [map_sub, map_one]
    rfl


/-- Checked natural-index specification of one position-map subset extension. -/
def extendWeightByteSpec : Nat → USize → USize → UInt64 → UInt64 → UInt64 →
    FixedWords (1600*6*256*3) → FixedWords (1600*6*256*3)
  | 0, _, _, _, _, _, out => out
  | n+1, source, target, c0, c1, c2, out =>
    let offset := 3*n.toUSize
    let out := writeUWord out (target+offset) (readUWord out (source+offset) ^^^ c0)
    let out := writeUWord out (target+offset+1) (readUWord out (source+offset+1) ^^^ c1)
    let out := writeUWord out (target+offset+2) (readUWord out (source+offset+2) ^^^ c2)
    extendWeightByteSpec n source target c0 c1 c2 out
/-- Machine-index subset extension equals the checked natural recursion. -/
theorem extendWeightByte_eq (n source target : USize) (c0 c1 c2 : UInt64)
    (out : FixedWords (1600*6*256*3))
    (hs : source.toNat+3*n.toNat ≤ 7372800)
    (ht : target.toNat+3*n.toNat ≤ 7372800) :
    extendWeightByte n source target c0 c1 c2 out hs ht =
      extendWeightByteSpec n.toNat source target c0 c1 c2 out := by
  induction hcount : n.toNat generalizing n out with
  | zero =>
    have hn : n = 0 := USize.toNat_inj.mp hcount
    subst n
    rw [extendWeightByte]
    simp only [dite_true, extendWeightByteSpec]
  | succ k ih =>
    have hn : n ≠ 0 := by intro h; subst n; simp only [USize.toNat_zero] at hcount; omega
    have hn1 : (1 : USize) ≤ n := by
      rw [USize.le_iff_toNat_le, USize.toNat_one, hcount]
      omega
    have hk : (n-1).toNat = k := by
      rw [USize.toNat_sub_of_le _ _ hn1, USize.toNat_one, hcount]
      omega
    have he : n-1 = k.toUSize := by
      rw [← hk, Nat.toUSize, USize.ofNat_toNat]
    rw [extendWeightByte]
    simp only [hn, dite_false]
    rw [ih _ _ _ _ hk]
    simp only [getUWord_eq_readUWord, setUWord_eq_writeUWord, he, add_zero,
      extendWeightByteSpec]

/-- Prepared packed Horner evaluation retains the full polynomial and arbitrary suffix. -/
theorem evaluatePackedLoop_eq (coeffs : PackedE) (s : W) (n : Nat) (acc : W) :
    evaluatePackedLoop coeffs (CompStark.Sumcheck.prepare s) n acc =
      (∑ i ∈ Finset.range n, coeffs.get i * s^i) + s^n*acc := by
  induction n generalizing acc with
  | zero => simp only [evaluatePackedLoop, Finset.range_zero, Finset.sum_empty, pow_zero, one_mul, zero_add]
  | succ n ih =>
    rw [evaluatePackedLoop, ih, Finset.sum_range_succ, CompStark.Sumcheck.prepared_mul_eq]
    change (∑ i ∈ Finset.range n, coeffs.get i * s^i) + s^n*(coeffs.get n+s*acc) = _
    rw [pow_succ]
    ring

/-- Native packed Horner evaluation is precisely the protocol coefficient evaluation. -/
theorem evaluatePackedLoop_polyEval (coeffs : PackedE) (s : W) :
    evaluatePackedLoop coeffs (CompStark.Sumcheck.prepare s) coeffs.size 0 =
      CompStark.Keccak.Gkr.polyEval (fun i : Fin coeffs.size => coeffs.get i.val) s := by
  rw [evaluatePackedLoop_eq, mul_zero, add_zero]
  exact (Fin.sum_univ_eq_sum_range (fun i => coeffs.get i*s^i) coeffs.size).symm

/-- The bit-packed chi payload at one position of a simultaneous witness row. -/
def productCell (state : Array UInt64) (groups offset : USize) (bits : UInt64)
    (maps : RmfeProducts) (j : Nat) : UInt64 :=
  let k := j.toUSize
  let a := (state[(k*groups+offset).toNat]! >>> bits) &&& 65535
  let b := (state[(shiftU k 1*groups+offset).toNat]! >>> bits) &&& 65535
  let c := (state[(shiftU k 2*groups+offset).toNat]! >>> bits) &&& 65535
  maps.ones (a ^^^ c) ^^^ maps.mul b c

/-- The entire payload loop computes every selected position and preserves its prefix. -/
theorem productPayload_get (state : Array UInt64) (groups offset : USize) (bits : UInt64)
    (maps : RmfeProducts) (start : Nat) (out : FixedWords 1600) (i : Nat) (hi : i < 1600) :
    readWord (productPayload state groups offset bits maps start out) i =
      if start ≤ i then productCell state groups offset bits maps i else readWord out i := by
  rw [productPayload]
  split
  · rename_i hstart
    rw [productPayload_get state groups offset bits maps (start+1) _ i hi]
    by_cases h : start+1 ≤ i
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h]
      change readWord (writeWord out start (productCell state groups offset bits maps start)) i = _
      rw [readWord_writeWord _ start i hstart hi]
      by_cases he : start=i
      · subst i; simp only [ite_true, le_refl]
      · rw [ite_eq_right he, ite_eq_right (by omega)]
  · rename_i hstart
    rw [ite_eq_right (by omega)]
termination_by 1600-start

/-- Evaluation of the three native cofactor coefficients. -/
def RowCoefficients.eval (cs : RowCoefficients) (r : W) : W :=
  cs.zero+r*(cs.linear+r*cs.infinity)

/-- A retained pair of rows contributes one weighted product of affine factors. -/
def packCell (table : PackedE) (weights constants : Array W) (row j : Nat) (r : W) : W :=
  (weights[j]! * line (table.get (3200*row+shift j 1))
    (table.get (3200*row+1600+shift j 1)) r + constants[j]!) *
  line (table.get (3200*row+shift j 2)) (table.get (3200*row+1600+shift j 2)) r

/-- Native cofactor accumulation evaluates to the complete sum of row contributions. -/
theorem packRow_eval (table : PackedE) (weights constants : Array W) (row j : Nat)
    (z0 z1 z2 l0 l1 l2 i0 i1 i2 : UInt64) (r : W) :
    (packRow table weights constants row j z0 z1 z2 l0 l1 l2 i0 i1 i2).eval r =
      (⟨⟨z0⟩,⟨z1⟩,⟨z2⟩⟩ : W)+r*((⟨⟨l0⟩,⟨l1⟩,⟨l2⟩⟩ : W)+r*(⟨⟨i0⟩,⟨i1⟩,⟨i2⟩⟩ : W)) +
      ∑ k ∈ Finset.range (1600-j), packCell table weights constants row (j+k) r := by
  rw [packRow]
  split
  · rename_i hj
    rw [packRow_eval]
    have hn : 1600-j = (1600-(j+1))+1 := by omega
    rw [hn, Finset.sum_range_succ']
    simp only [Nat.add_zero]
    have hsum : (∑ k ∈ Finset.range (1600-(j+1)), packCell table weights constants row (j+1+k) r) =
        ∑ k ∈ Finset.range (1600-(j+1)), packCell table weights constants row (j+(k+1)) r := by
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      omega
    rw [hsum]
    let b := table.get (3200*row+shift j 1)
    let db := b+table.get (3200*row+1600+shift j 1)
    let c := table.get (3200*row+shift j 2)
    let dc := c+table.get (3200*row+1600+shift j 2)
    let w := weights[j]!
    let a := constants[j]!
    let q0 := w*b+a
    let q1 := w*db
    let p0 := q0*c
    let p2 := q1*dc
    let p1 := (q0+q1)*(c+dc)+(p0+p2)
    let z : W := ⟨⟨z0⟩,⟨z1⟩,⟨z2⟩⟩
    let l : W := ⟨⟨l0⟩,⟨l1⟩,⟨l2⟩⟩
    let i : W := ⟨⟨i0⟩,⟨i1⟩,⟨i2⟩⟩
    let rest := ∑ k ∈ Finset.range (1600-(j+1)), packCell table weights constants row (j+(k+1)) r
    change (z+p0)+r*((l+p1)+r*(i+p2))+rest =
      z+r*(l+r*i)+(rest+(w*(b+r*db)+a)*(c+r*dc))
    dsimp only [p0,p1,p2,q0,q1]
    ring_nf
    have htwo : (2 : W) = 0 := CharP.cast_eq_zero W 2
    simp only [htwo, mul_zero, add_zero]
  · rename_i hj
    have hn : 1600-j = 0 := by omega
    simp only [RowCoefficients.eval, hn, Finset.range_zero, Finset.sum_empty, add_zero]
termination_by 1600-j
/-- The three native coefficients evaluate to the weighted sum of row cofactors. -/
theorem packRound_eval (table : PackedE) (weights constants eq : Array W) (r : W) :
    CompStark.Keccak.Gkr.polyEval (fun i : Fin 3 => (packRound table weights constants eq)[i.val]!) r =
      ∑ row ∈ Finset.range (table.size/3200), eq[row]! *
        (packRow table weights constants row 0 0 0 0 0 0 0 0 0 0).eval r := by
  simp only [packRound, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    pure_bind, Id.run_pure]
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    ← List.range_eq_range']
  let cs (row : Nat) := packRow table weights constants row 0 0 0 0 0 0 0 0 0 0
  let step (acc : W × W × W) (row : Nat) :=
    (acc.1+eq[row]!*(cs row).zero, acc.2.1+eq[row]!*(cs row).linear,
      acc.2.2+eq[row]!*(cs row).infinity)
  let ev (acc : W × W × W) := acc.1+r*(acc.2.1+r*acc.2.2)
  have heval (a b c : W) : CompStark.Keccak.Gkr.polyEval
      (fun i : Fin 3 => (#[a,b,c])[i.val]!) r = a+r*(b+r*c) := by
    simp only [CompStark.Keccak.Gkr.polyEval, Fin.sum_univ_succ, Fin.sum_univ_zero]
    norm_num
    ring
  rw [heval]
  change ev ((List.range (table.size/3200)).foldl step (0,0,0)) = _
  have hstep (acc : W × W × W) (row : Nat) :
      ev (step acc row) = ev acc+eq[row]!*(cs row).eval r := by
    dsimp only [ev,step,RowCoefficients.eval]
    ring
  have hf (xs : List Nat) (acc : W × W × W) : ev (xs.foldl step acc) =
      ev acc+(xs.map fun row => eq[row]!*(cs row).eval r).sum := by
    induction xs generalizing acc with
    | nil => simp only [List.foldl_nil,List.map_nil,List.sum_nil,add_zero]
    | cons a xs ih =>
      rw [List.foldl_cons, ih, hstep, List.map_cons, List.sum_cons, add_assoc]
  rw [hf]
  change (0+r*(0+r*0)) + _ = _
  simp only [mul_zero,add_zero,zero_add]
  have hsum (f : Nat → W) (n : Nat) :
      ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
        List.sum_singleton, Finset.sum_range_succ, ih]
  exact hsum _ _

/-- Endpoint-only accumulation preserves both corresponding full-cofactor coefficients. -/
theorem packRowEndpoints_eq (table : PackedE) (weights constants : Array W) (row j : Nat)
    (z0 z1 z2 i0 i1 i2 l0 l1 l2 : UInt64) :
    packRowEndpoints table weights constants row j z0 z1 z2 i0 i1 i2 =
      ((packRow table weights constants row j z0 z1 z2 l0 l1 l2 i0 i1 i2).zero,
       (packRow table weights constants row j z0 z1 z2 l0 l1 l2 i0 i1 i2).infinity) := by
  rw [packRowEndpoints,packRow]
  split
  · apply packRowEndpoints_eq
  · rfl
termination_by 1600-j

/-- The machine-indexed tail row is exactly the complete endpoint accumulator. -/
theorem packRowEndpointsNative_eq (table : PackedE) (weights constants : Array W) (row : Nat)
    (bound : 3200*row+3200 ≤ table.size) (j : USize)
    (z0 z1 z2 i0 i1 i2 : UInt64) :
    packRowEndpointsNative table weights constants row bound j z0 z1 z2 i0 i1 i2 =
      packRowEndpoints table weights constants row j.toNat z0 z1 z2 i0 i1 i2 := by
  rw [packRowEndpointsNative,packRowEndpoints]
  have hn : (1600 : USize).toNat = 1600 :=
    USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)
  by_cases hj : j.toNat < 1600
  · have hj' : j < 1600 := by simpa only [USize.lt_iff_toNat_lt,hn] using hj
    rw [dite_eq_left hj',dite_eq_left hj]
    simp only [packShifts,Array.uget,Array.getElem_ofFn]
    have hs (k : Nat) : shift j.toNat k < 1600 := (Gkr.along ⟨j.toNat,hj⟩ k).isLt
    have h0 : 3200*row+shift j.toNat 1 < table.size := by have := hs 1; omega
    have h1 : 3200*row+1600+shift j.toNat 1 < table.size := by have := hs 1; omega
    have h2 : 3200*row+shift j.toNat 2 < table.size := by have := hs 2; omega
    have h3 : 3200*row+1600+shift j.toNat 2 < table.size := by have := hs 2; omega
    simp only [PackedE.get,h0,h1,h2,h3,dite_eq_left]
    rw [packRowEndpointsNative_eq]
    have next : (j+1).toNat = j.toNat+1 := by
      rw [USize.toNat_add,USize.toNat_one]
      change (j.toNat+1)%USize.size = j.toNat+1
      rw [Nat.mod_eq_of_lt (by have := USize.le_size; omega)]
    rw [next]
  · have hj' : ¬j < 1600 := by simpa only [USize.lt_iff_toNat_lt,hn] using hj
    rw [dite_eq_right hj',dite_eq_right hj]
termination_by 1600-j.toNat
decreasing_by
  rw [USize.toNat_add,USize.toNat_one]
  change 1600-((j.toNat+1)%USize.size) < 1600-j.toNat
  rw [Nat.mod_eq_of_lt (by have := USize.le_size; omega)]
  omega

/-- The complete endpoint loop is the projection of the full coefficient loop. -/
theorem packEndpoints_eq (table : PackedE) (weights constants eq : Array W) :
    packEndpoints table weights constants eq =
      ((packRound table weights constants eq)[0]!, (packRound table weights constants eq)[2]!) := by
  simp only [packEndpoints, packRowEndpointsNative_eq, forIn'_eq_forIn, packRound, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, pure_bind, Id.run_pure]
  let full (acc : W × W × W) (row : Nat) :=
    let cs := packRow table weights constants row 0 0 0 0 0 0 0 0 0 0
    (acc.1+eq[row]!*cs.zero, acc.2.1+eq[row]!*cs.linear, acc.2.2+eq[row]!*cs.infinity)
  let small (acc : W × W) (row : Nat) :=
    let cs := packRowEndpoints table weights constants row 0 0 0 0 0 0 0
    (acc.1+eq[row]!*cs.1, acc.2+eq[row]!*cs.2)
  change (List.range' 0 [:table.size/3200].size).foldl small (0,0) =
    (((List.range' 0 [:table.size/3200].size).foldl full (0,0,0)).1,
      ((List.range' 0 [:table.size/3200].size).foldl full (0,0,0)).2.2)
  apply List.foldl_hom (fun acc : W × W × W => (acc.1,acc.2.2)) (g₁ := full)
    (g₂ := small) (init := (0,0,0))
  intro acc row
  dsimp only [small,full]
  rw [packRowEndpoints_eq table weights constants row 0 0 0 0 0 0 0 0 0 0]

/-- Recovering a cofactor tail is exact whenever its equality coordinate is nonzero. -/
theorem reconstructPackLinear (a b c scale entering : W) (hne : entering ≠ 0) :
    ((scale*a+entering*(scale*b+scale*c)+scale*a)*entering⁻¹)+scale*c = scale*b := by
  have h : scale*a+entering*(scale*b+scale*c)+scale*a = entering*(scale*b+scale*c) := by
    have htwo := CharTwo.add_self_eq_zero (scale*a)
    linear_combination htwo
  rw [h, mul_comm entering, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  have htwo := CharTwo.add_self_eq_zero (scale*c)
  linear_combination htwo
/-- The full pack kernel always retains all three cofactor coefficients. -/
theorem packRound_size (table : PackedE) (weights constants eq : Array W) :
    (packRound table weights constants eq).size = 3 := by
  simp only [packRound, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, pure_bind, Id.run_pure]
  rfl

/-- Claim-based reconstruction preserves every scaled cofactor coefficient, including zero equality coordinates. -/
theorem packRoundFromClaim_eq (table : PackedE) (weights constants eq : Array W)
    (entering scale value : W)
    (hvalue : value = scale*(packRound table weights constants eq)[0]! +
      entering*(scale*(packRound table weights constants eq)[1]!+scale*(packRound table weights constants eq)[2]!)) :
    packRoundFromClaim table weights constants eq entering scale value =
      (packRound table weights constants eq).map (scale*·) := by
  rw [packRoundFromClaim]
  split
  · rfl
  · rename_i hne
    have hne : entering ≠ 0 := hne
    rw [packEndpoints_eq]
    have hlinear := reconstructPackLinear (packRound table weights constants eq)[0]!
      (packRound table weights constants eq)[1]! (packRound table weights constants eq)[2]! scale entering hne
    rw [hvalue]
    change #[scale*(packRound table weights constants eq)[0]!,
      (scale*(packRound table weights constants eq)[0]! +
        entering*(scale*(packRound table weights constants eq)[1]!+scale*(packRound table weights constants eq)[2]!) +
        scale*(packRound table weights constants eq)[0]!)*entering⁻¹+scale*(packRound table weights constants eq)[2]!,
      scale*(packRound table weights constants eq)[2]!] = _
    rw [hlinear]
    apply Array.ext
    · simp only [Array.size_map,packRound_size]
      rfl
    · intro i hi _
      have hi : i < 3 := hi
      have hbound : i < (packRound table weights constants eq).size := by rw [packRound_size]; exact hi
      rw [Array.getElem_map]
      have hval := getElem!_pos (packRound table weights constants eq) i hbound
      interval_cases i <;> exact congrArg (scale*·) hval

/-- Shifting both factors preserves their position sum. -/
theorem shifted_product_sum {F : Type*} [CommRing F] (w f : Fin 1600 → F) :
    (∑ j, w (Gkr.along j 2)*f (Gkr.along j 2)) = ∑ j, w j*f j := by
  exact (Gkr.alongEquiv 2).sum_comp (fun j => w j*f j)

/-- Moving the affine chi input onto the third factor preserves the full weighted gate sum. -/
theorem pack_factor_sum {F : Type*} [CommRing F] (w f : Fin 1600 → F) (k : F) :
    (∑ j, (w j*f (Gkr.along j 1)+k*(w j+w (Gkr.along j 2)))*f (Gkr.along j 2)) =
      ∑ j, w j*(k*f j+(k+f (Gkr.along j 1))*f (Gkr.along j 2)) := by
  have h := shifted_product_sum w f
  calc
    _ = (∑ j, (w j*f (Gkr.along j 1)*f (Gkr.along j 2)+k*w j*f (Gkr.along j 2))) +
        k*∑ j, w (Gkr.along j 2)*f (Gkr.along j 2) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [h, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The complete native row cofactor is exactly the weighted chi summand on its affine table. -/
theorem packRow_chi (table : PackedE) (weights : Array W) (kappa : W) (row : Nat) (r : W) :
    (packRow table weights (packConstants weights kappa) row 0 0 0 0 0 0 0 0 0 0).eval r =
      ∑ j : Fin 1600, weights[j.val]! *
        (kappa*line (table.get (3200*row+j.val)) (table.get (3200*row+1600+j.val)) r +
          (kappa+line (table.get (3200*row+shift j.val 1)) (table.get (3200*row+1600+shift j.val 1)) r)*
            line (table.get (3200*row+shift j.val 2)) (table.get (3200*row+1600+shift j.val 2)) r) := by
  rw [packRow_eval]
  change (0+r*(0+r*0)) + _ = _
  simp only [mul_zero,add_zero,zero_add,Nat.sub_zero]
  rw [← Fin.sum_univ_eq_sum_range]
  refine Eq.trans ?_ (pack_factor_sum (fun j => weights[j.val]!)
    (fun j => line (table.get (3200*row+j.val)) (table.get (3200*row+1600+j.val)) r) kappa)
  apply Finset.sum_congr rfl
  intro j _
  simp only [packCell,packConstants, getElem!_pos, Array.size_ofFn, Fin.isLt, Array.getElem_ofFn,
    shift_eq]
  rfl

/-- The prepared array loop preserves its allocated result length. -/
theorem foldArrayLoop_size (table : Array W) (width : Nat) (map : CompStark.Sumcheck.Prepared)
    (n : Nat) (out : Array W) : (foldArrayLoop table width map n out).size = out.size := by
  induction n generalizing out with
  | zero => rfl
  | succ n ih => rw [foldArrayLoop,ih,Array.size_set!]

/-- The prepared array loop writes exactly its selected prefix. -/
theorem foldArrayLoop_get (table : Array W) (width : Nat) (map : CompStark.Sumcheck.Prepared)
    (n : Nat) (out : Array W) (hn : n ≤ out.size) (i : Nat) (hi : i < out.size) :
    (foldArrayLoop table width map n out)[i]! =
      if i < n then foldArrayCell table width map i else out[i]! := by
  induction n generalizing out with
  | zero => simp only [foldArrayLoop,Nat.not_lt_zero,ite_false]
  | succ n ih =>
    rw [foldArrayLoop,ih _ (by rw [Array.size_set!]; omega) (by rw [Array.size_set!]; exact hi)]
    by_cases h : i < n
    · rw [ite_eq_left h,ite_eq_left (by omega)]
    · rw [ite_eq_right h]
      by_cases he : i=n
      · subst i
        rw [Array.getElem!_set!_self _ _ _ (by omega),ite_eq_left (by omega)]
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm he),ite_eq_right (by omega)]

/-- Sharing a prepared challenge across arrays retains the exact specification fold. -/
theorem foldArrayShared_eq (table : Array W) (width : Nat) (r : W) :
    foldArrayShared table width (CompStark.Sumcheck.prepare r) = fold table width r := by
  apply Array.ext
  · simp only [foldArrayShared,foldArrayLoop_size,Array.size_replicate,fold,Array.size_ofFn]
  · intro i hi hj
    have hb : i < table.size/(2*width)*width := by
      simpa only [foldArrayShared,foldArrayLoop_size,Array.size_replicate] using hi
    rw [← getElem!_pos _ i hi, ← getElem!_pos _ i hj]
    rw [foldArrayShared,foldArrayLoop_get _ _ _ _ _ (by rw [Array.size_replicate]) i
      (by simpa only [Array.size_replicate] using hb),ite_eq_left hb]
    rw [getElem!_pos _ i hj]
    simp only [fold,Array.getElem_ofFn,foldArrayCell,CompStark.Sumcheck.prepared_mul_eq,line]
    have hindex : 2*(i/width)*width+i%width+width = (2*(i/width)+1)*width+i%width := by
      rw [Nat.add_mul,Nat.one_mul]
      omega
    rw [hindex]
    rfl

/-- One zero-padded pair's position cubic in the protocol coefficient convention. -/
def positionCell (weights : Array W) (t : Array (Array W)) (kappa : W) (row : Nat) : Fin 4 → W :=
  let offset := 2*row
  cubic (F := W) weights[offset]! (weights[offset]!+weights[offset+1]!)
    (t[0]!)[offset]! ((t[0]!)[offset]!+(t[0]!)[offset+1]!)
    (t[1]!)[offset]! ((t[1]!)[offset]!+(t[1]!)[offset+1]!)
    (t[2]!)[offset]! ((t[2]!)[offset]!+(t[2]!)[offset+1]!) kappa

/-- Every scalar accumulator retains the exact sum of its transmitted position coefficient. -/
theorem positionRows_eq (weights : Array W) (t : Array (Array W)) (kappa : W) (row : Nat)
    (z0 z1 z2 q0 q1 q2 c0 c1 c2 : UInt64) (i : Fin 3) :
    (positionRows weights t kappa row z0 z1 z2 q0 q1 q2 c0 c1 c2)[i.val]! =
      (#[⟨⟨z0⟩,⟨z1⟩,⟨z2⟩⟩,⟨⟨q0⟩,⟨q1⟩,⟨q2⟩⟩,⟨⟨c0⟩,⟨c1⟩,⟨c2⟩⟩] : Array W)[i.val]! +
        ∑ k ∈ Finset.range (weights.size/2-row), positionCell weights t kappa (row+k) (positionCoefficient i) := by
  rw [positionRows]
  split
  · rename_i hrow
    rw [positionRows_eq]
    have hn : weights.size/2-row = (weights.size/2-(row+1))+1 := by omega
    rw [hn, Finset.sum_range_succ']
    simp only [Nat.add_zero]
    have hs : (∑ k ∈ Finset.range (weights.size/2-(row+1)),
        positionCell weights t kappa (row+(k+1)) (positionCoefficient i)) =
        ∑ k ∈ Finset.range (weights.size/2-(row+1)),
          positionCell weights t kappa (row+1+k) (positionCoefficient i) := by
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      omega
    rw [hs]
    fin_cases i
    · change ((⟨⟨z0⟩,⟨z1⟩,⟨z2⟩⟩ : W)+positionCell weights t kappa row 0)+_ =
        (⟨⟨z0⟩,⟨z1⟩,⟨z2⟩⟩ : W)+(_+positionCell weights t kappa row 0)
      ac_rfl
    · change ((⟨⟨q0⟩,⟨q1⟩,⟨q2⟩⟩ : W)+positionCell weights t kappa row 2)+_ =
        (⟨⟨q0⟩,⟨q1⟩,⟨q2⟩⟩ : W)+(_+positionCell weights t kappa row 2)
      ac_rfl
    · change ((⟨⟨c0⟩,⟨c1⟩,⟨c2⟩⟩ : W)+positionCell weights t kappa row 3)+_ =
        (⟨⟨c0⟩,⟨c1⟩,⟨c2⟩⟩ : W)+(_+positionCell weights t kappa row 3)
      ac_rfl
  · rename_i hrow
    have hn : weights.size/2-row = 0 := by omega
    simp only [hn,Finset.range_zero,Finset.sum_empty,add_zero]
termination_by weights.size/2-row

/-- The native position message is the full protocol sum at precisely the transmitted coefficients. -/
theorem positionRound_eq (weights : Array W) (t : Array (Array W)) (kappa : W) (i : Fin 3) :
    (positionRound weights t kappa)[i.val]! =
      ∑ row ∈ Finset.range (weights.size/2), positionCell weights t kappa row (positionCoefficient i) := by
  rw [positionRound,positionRows_eq]
  simp only [Nat.sub_zero,Nat.zero_add]
  fin_cases i <;> change (0 : W)+_ = _ <;> exact zero_add _

section
attribute [local irreducible] proveLayerM proveOpenings Writer.sample Writer.sampleMany outputWords eqTable dot prepareRmfeProducts
set_option maxHeartbeats 1000000 in
/-- The production prover retains exactly the twelve backwards protocol layers. -/
theorem prove_layers_size (writer : Writer) (w : SlicedWitness) (committed : Array UInt64)
    (batchPoint output : Array W) : (prove writer w committed batchPoint output).layers.size = 12 := by
  have hbind {A B : Type} (a : Id A) (f : A → Id B) : a >>= f = f a := rfl
  simp only [prove,proveM,Std.Legacy.Range.forIn_eq_forIn_range',
    hbind,List.forIn_pure_yield_eq_foldl,Id.run_pure]
  let step (state : Claim × Writer × Array Layer) (d : Nat) :=
    let result := proveLayerM (M := Id) (fun _ _ => pure ()) state.2.1 w d state.1 prepareRmfeProducts
    (result.2.1,result.2.2,state.2.2.push result.1)
  have hlength (xs : List Nat) (state : Claim × Writer × Array Layer) :
      (xs.foldl step state).2.2.size = state.2.2.size+xs.length := by
    induction xs generalizing state with
    | nil => simp only [List.foldl_nil,List.length_nil,Nat.add_zero]
    | cons d xs ih =>
      rw [List.foldl_cons,ih]
      change (state.2.2.push _).size+xs.length = _
      rw [Array.size_push,List.length_cons]
      omega
  change ((List.range' 0 12).foldl step _).2.2.size = 12
  rw [hlength]
  rfl


end

/-- Interpret the production prover in the protocol using its certified layer count. -/
def nativeTranscript (writer : Writer) (w : SlicedWitness) (committed : Array UInt64)
    (batchPoint output : Array W) : Gkr.Transcript E (w.nLog-4) :=
  (prove writer w committed batchPoint output).toProtocol (w.nLog-4)
    (prove_layers_size writer w committed batchPoint output)

/-- The sliced native bit is the committed field word's polynomial-basis coordinate. -/
theorem sliceBit_wordBits (word : UInt64) (bit : Fin 64) :
    sliceBit word bit = CompStark.Pcs.wordBits (Word.toField ⟨word⟩) bit := by
  simp only [sliceBit,CompStark.Pcs.wordBits,Word.toField,BF64.toBitVec_ofBitVec]
  rw [BitVec.getLsbD_eq_getElem (h := bit.isLt)]
  rfl

/-- Recombining all sliced native bits gives the exact native word in the protocol field. -/
theorem lane_toField (word : UInt64) :
    (lane word).toField = CompStark.Keccak.Gkr.laneValue
      (CompStark.BinaryFields.ofK CompStark.BinaryFields.g) (sliceBit word) := by
  have h := CompStark.Pcs.wordBits_laneValue (Word.toField ⟨word⟩)
  have hb : sliceBit word = CompStark.Pcs.wordBits (Word.toField ⟨word⟩) :=
    funext fun bit => sliceBit_wordBits word bit
  rw [hb,h]
  rfl

/-- Folding committed words at an external point is the exact weighted native word sum. -/
theorem outputWords_get (committed : Array UInt64) (n : Nat) (point : Array W)
    (slot : Nat) (hs : slot < committed.size/n) :
    (outputWords committed n point)[slot]! =
      ∑ b ∈ Finset.range n, WordExt3.mulScalar (eqTable point)[b]! ⟨committed[slot*n+b]!⟩ := by
  rw [getElem!_pos _ slot (by simpa only [outputWords,Array.size_ofFn] using hs)]
  simp only [outputWords,Array.getElem_ofFn,Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure]
  simp only [Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range']
  let term (b : Nat) := WordExt3.mulScalar (eqTable point)[b]! ⟨committed[slot*n+b]!⟩
  have hfold (xs : List Nat) (a : W) :
      xs.foldl (fun acc b => acc+term b) a = a+(xs.map term).sum := by
    induction xs generalizing a with
    | nil => simp only [List.foldl_nil,List.map_nil,List.sum_nil,add_zero]
    | cons b xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,add_assoc]
  rw [hfold,zero_add]
  have hsum (n : Nat) : ((List.range n).map term).sum = ∑ b ∈ Finset.range n, term b := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ,List.map_append,List.sum_append,List.map_singleton,
        List.sum_singleton,ih,Finset.sum_range_succ]
  exact hsum n
/-- Native committed-word folding equals the protocol multilinear word opening. -/
theorem outputWords_toField (committed : Array UInt64) (point : Array W)
    (slot : Nat) (hs : slot < committed.size/(2^point.size)) :
    ((outputWords committed (2^point.size) point)[slot]!).toField =
      CompStark.Keccak.Gkr.mle
        (fun b : Fin (2^point.size) => CompStark.Keccak.Gkr.laneValue
          (CompStark.BinaryFields.ofK CompStark.BinaryFields.g)
          (sliceBit committed[slot*2^point.size+b.val]!))
        (fun i : Fin point.size => point[i.val]!.toField) := by
  rw [outputWords_get committed _ point slot hs]
  change WordExt3.ringEquiv (∑ b ∈ Finset.range (2^point.size),
    WordExt3.mulScalar (eqTable point)[b]! ⟨committed[slot*2^point.size+b]!⟩) = _
  rw [map_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  unfold CompStark.Keccak.Gkr.mle
  apply Finset.sum_congr rfl
  intro b _
  change (WordExt3.mulScalar (eqTable point)[b.val]! ⟨committed[slot*2^point.size+b.val]!⟩).toField = _
  rw [WordExt3.toField_mulScalar,eqTable_get_toField point b.val b.isLt]
  dsimp only
  rw [← lane_toField]
  rw [Algebra.smul_def]
  exact mul_comm _ _


/-- Packed 32-bit assignments preserve the low polynomial bits of a word-width tensor. -/
def DWordRefines (a : FixedDWords n) (b : FixedWords n) : Prop :=
  ∀ i, readUDWord a i = (readUWord b i).toUInt32

/-- Storing an assignment preserves the pointwise refinement of the entire tensor buffer. -/
theorem writeUDWord_refines (a : FixedDWords n) (b : FixedWords n) (h : DWordRefines a b)
    (i : USize) (v : UInt64) :
    DWordRefines (writeUDWord a i v.toUInt32) (writeUWord b i v) := by
  by_cases hi : i < n.toUSize
  · simp only [writeUDWord,writeUWord,hi,dite_eq_left]
    intro j
    by_cases hj : j < n.toUSize
    · rw [← getUDWord_eq_readUDWord _ j hj,← getUWord_eq_readUWord _ j hj,
        getUDWord_setUDWord,getUWord_setUWord]
      by_cases he : i = j
      · rw [ite_eq_left he,ite_eq_left he]
      · rw [ite_eq_right he,ite_eq_right he]
        simpa only [getUDWord_eq_readUDWord,getUWord_eq_readUWord] using h j
    · simp only [readUDWord,readUWord,hj]
      rfl
  · simp only [writeUDWord,writeUWord,hi]
    exact h

/-- Word-width interpretation of one complete ternary-assignment row. -/
def mixedRowReference (state : Array UInt64) (groups offset : USize) (bits : UInt64)
    (lo hi target : USize) (binary : Bool) (j : USize) (out : FixedWords (81*1600)) : FixedWords (81*1600) :=
  if _h : j < 1600 then
    let value := if binary then
      (state[(j*groups+offset).toNat]! >>> bits) &&& 65535
    else readUWord out (lo+j) ^^^ readUWord out (hi+j)
    mixedRowReference state groups offset bits lo hi target binary (j+1) (writeUWord out (target+j) value)
  else out
termination_by 1600-j.toNat
decreasing_by
  have hj : j.toNat < 1600 := by simpa only [USize.lt_iff_toNat_lt, USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide : 1600 < 2^32) USize.le_size)] using _h
  rw [USize.toNat_add]
  have hs := USize.le_size
  have hn : (1 : USize).toNat = 1 := USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)
  rw [hn]
  change 1600-((j.toNat+1)%USize.size) < 1600-j.toNat
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- The complete compact ternary-row loop preserves the polynomial bits of the word-width loop. -/
theorem mixedRow_refines (state : Array UInt64) (groups offset : USize) (bits : UInt64)
    (lo hi target : USize) (binary : Bool) (j : USize)
    (a : FixedDWords (81*1600)) (b : FixedWords (81*1600)) (h : DWordRefines a b) :
    DWordRefines (mixedRow state groups offset bits lo hi target binary j a)
      (mixedRowReference state groups offset bits lo hi target binary j b) := by
  rw [mixedRow,mixedRowReference]
  split
  · rename_i _hj
    apply mixedRow_refines
    have hv : (if binary then ((state[(j*groups+offset).toNat]! >>> bits) &&& 65535).toUInt32
        else readUDWord a (lo+j) ^^^ readUDWord a (hi+j)) =
        (if binary then (state[(j*groups+offset).toNat]! >>> bits) &&& 65535
        else readUWord b (lo+j) ^^^ readUWord b (hi+j)).toUInt32 := by
      cases binary <;> simp only [Bool.false_eq_true,ite_false,ite_true,h (lo+j),h (hi+j),UInt64.toUInt32_xor]
    rw [hv]
    exact writeUDWord_refines a b h _ _
  · exact h
termination_by 1600-j.toNat
decreasing_by
  have _hj : j.toNat < 1600 := by
    simpa only [USize.lt_iff_toNat_lt,USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide : 1600 < 2^32) USize.le_size)] using (show j < 1600 by assumption)
  rw [USize.toNat_add,USize.toNat_one]
  change 1600-((j.toNat+1)%USize.size) < 1600-j.toNat
  rw [Nat.mod_eq_of_lt (by have := USize.le_size; omega)]
  omega

/-- Zero-filled compact and word-width tensors represent the same polynomial assignments. -/
theorem zeroDWords_refines (n : Nat) (hn : n < 2^29) :
    DWordRefines (zeroDWords n (lt_trans hn (by decide))) (zeroWords n hn) := by
  intro i
  by_cases hi : i < n.toUSize
  · rw [← getUDWord_eq_readUDWord _ i hi,← getUWord_eq_readUWord _ i hi,
      getUDWord_zeroDWords,getUWord_zeroWords]
    rfl
  · simp only [readUDWord,readUWord,hi]
    rfl

/-- Word-width interpretation of the complete four-coordinate ternary tensor. -/
def mixedEmbeddingsReference (state : Array UInt64) (groups base : Nat) : FixedWords (81*1600) := Id.run do
  let mut out := zeroWords (81*1600)
  for q in [:81] do
    let (lo,hi) := ternaryPlan[q]!
    let b := base+lo
    out := mixedRowReference state groups.toUSize (b/4).toUSize (16*(b%4)).toUInt64
      (1600*lo).toUSize (1600*hi).toUSize (1600*q).toUSize (hi==81) 0 out
  return out

/-- The compact production tensor preserves every polynomial assignment of the word-width tensor. -/
theorem mixedEmbeddings_refines (state : Array UInt64) (groups base : Nat) :
    DWordRefines (mixedEmbeddings state groups base) (mixedEmbeddingsReference state groups base) := by
  simp only [mixedEmbeddings,mixedEmbeddingsReference,Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure]
  apply List.foldl_rel (r := DWordRefines) (zeroDWords_refines _ (by decide))
  intro q _ a b h
  exact mixedRow_refines _ _ _ _ _ _ _ _ _ a b h

/-- Interpret a native running claim in the verifier's protocol dimensions. -/
def Claim.toProtocol (claim : Claim) (p : Nat) : Gkr.Claim E p where
  value := claim.value.toField
  mu i := claim.mu[i.val]!.toField
  point i := claim.point[i.val]!.toField
  weights j := claim.weights[j.val]!.toField

/-- Native input-opening weights are exactly the committed-slot protocol weights. -/
theorem inputWeights_toField {p : Nat} (claim : Claim) (shape : claim.point.size = p+1)
    (slot z : Fin 64) :
    ((inputWeights claim)[64*slot.val+z.val]!).toField = Gkr.inputWeight (claim.toProtocol p) slot z := by
  have hd : (64*slot.val+z.val)/64 = slot.val := by omega
  have hm : (64*slot.val+z.val)%64 = z.val := by omega
  have hi : 64*slot.val+z.val < 4096 := by have := slot.isLt; have := z.isLt; omega
  rw [getElem!_pos _ _ (by simpa only [inputWeights,Array.size_ofFn] using hi)]
  simp only [inputWeights,Array.getElem_ofFn,hd,hm,Gkr.inputWeight,Claim.toProtocol,Fin.val_last]
  by_cases hs : slot.val < 50
  · rw [ite_eq_left hs,dite_eq_left hs]
    change WordExt3.ringEquiv ((if slot.val < 25 then 1+claim.point.back! else claim.point.back!)*_) = _
    rw [map_mul]
    by_cases hl : slot.val < 25
    · rw [ite_eq_left hl,ite_eq_left hl]
      rw [map_add,map_one]
      simp only [Array.back!,shape,Nat.add_sub_cancel]
      change (1+claim.point[p]!.toField)*_ = (1-claim.point[p]!.toField)*_
      rw [CharTwo.sub_eq_add]
      rfl
    · rw [ite_eq_right hl,ite_eq_right hl]
      simp only [Array.back!,shape,Nat.add_sub_cancel]
      rfl
  · rw [ite_eq_right hs,dite_eq_right hs]
    exact WordExt3.ringEquiv.map_zero

end CompStark.Keccak.GkrProver
