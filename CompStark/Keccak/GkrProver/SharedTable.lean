/-
Copyright (c) 2026 zkSecurity.
Adapted from leanEthereum/leanMultisig (Apache-2.0), revision 9d8bce818aa7c7e18e67026e522a9b1539d0a57d.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Keccak.GkrProver.PackedWords
public import CompStark.Keccak.GkrProver.PackedProofs
public import CompStark.Keccak.GkrProver.PackedTableValues
public import CompStark.Keccak.GkrProver.PackedAccumulation
public import CompStark.Keccak.GkrProver.ConstantBlocks
import all CompPoly.Fields.Binary.BF64.WordExt3Dot

/-! Shared retained rows and direct packed table materialization. -/
@[expose] public section
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
namespace CompStark.Keccak.GkrProver
open BF64
/-- Complete extension reads determine every byte of a packed extension table. -/
theorem PackedE.ext_get (a b : PackedE) (size : a.size = b.size)
    (same : ∀ i, i < a.size → a.get i = b.get i) : a = b := by
  rcases a with ⟨n,⟨a,ha⟩⟩
  rcases b with ⟨m,⟨b,hb⟩⟩
  change n = m at size
  subst m
  suffices a = b by subst b; rfl
  apply packed_ext a b (by omega)
  intro i
  have hin : i.val/3 < n := by have := i.isLt; omega
  have hs := same (i.val/3) hin
  simp only [PackedE.get,hin,dite_eq_left,WordExt3.read,Packed.read] at hs
  have hrem : i.val%3 = 0 ∨ i.val%3 = 1 ∨ i.val%3 = 2 := by omega
  rcases hrem with hr | hr | hr
  · have offset : i.val = 3*(i.val/3) := by omega
    have h := congrArg WordExt3.c0 hs
    convert h using 1 <;> congr 1 <;> apply Fin.ext <;> exact offset
  · have offset : i.val = 3*(i.val/3)+1 := by omega
    have h := congrArg WordExt3.c1 hs
    convert h using 1 <;> congr 1 <;> apply Fin.ext <;> exact offset
  · have offset : i.val = 3*(i.val/3)+2 := by omega
    have h := congrArg WordExt3.c2 hs
    convert h using 1 <;> congr 1 <;> apply Fin.ext <;> exact offset
end CompStark.Keccak.GkrProver
namespace CompStark.Keccak.GkrProver
open BF64
/-- A generated row retained together with the key that determines every byte. -/
structure RowCache {Key Value : Type} (generate : Key → Value) where
  /-- Exact source key. -/
  key : Key
  /-- Generated value shared by equal consecutive keys. -/
  row : Value
  /-- Agreement with generation from the retained key. -/
  valid : row = generate key
/-- Reuse the preceding row buffer for equal source blocks. -/
@[specialize] def reuseRow {Key Value : Type} [BEq Key] [LawfulBEq Key] (generate : Key → Value)
    (previous : Option (RowCache generate)) (key : Key) : RowCache generate :=
  match previous with
  | none => ⟨key,generate key,rfl⟩
  | some cached => if same : key == cached.key then
      ⟨key,cached.row,by rw [cached.valid,eq_of_beq same]⟩
    else ⟨key,generate key,rfl⟩
/-- Every reused row retains the requested block key. -/
theorem reuseRow_key {Key Value : Type} [BEq Key] [LawfulBEq Key] (generate : Key → Value)
    (previous : Option (RowCache generate)) (key : Key) : (reuseRow generate previous key).key = key := by
  cases previous with
  | none => rfl
  | some cached => simp only [reuseRow]; split <;> rfl
/-- Generate an ordered row sequence while sharing each repeated source block's buffer. -/
@[specialize] def shareRowsLoop {Key Value : Type} [BEq Key] [LawfulBEq Key] (key : Nat → Key) (generate : Key → Value) :
    List Nat → Option (RowCache generate) → Array Value → Array Value
  | [],_,out => out
  | i::indices,previous,out =>
    let cached := reuseRow generate previous (key i)
    shareRowsLoop key generate indices (some cached) (out.push cached.row)
/-- Sharing row buffers preserves the entire ordered array of generated rows. -/
theorem shareRowsLoop_eq {Key Value : Type} [BEq Key] [LawfulBEq Key] (key : Nat → Key) (generate : Key → Value)
    (indices : List Nat) (previous : Option (RowCache generate)) (out : Array Value) :
    shareRowsLoop key generate indices previous out = out ++ (indices.map fun i => generate (key i)).toArray := by
  induction indices generalizing previous out with
  | nil => simp only [shareRowsLoop,List.map_nil,Array.append_empty]
  | cons i indices ih =>
    rw [shareRowsLoop,ih,(reuseRow generate previous (key i)).valid,reuseRow_key]
    simp only [List.map_cons,List.push_append_toArray]
/-- Repeated block keys occupy one physical row buffer throughout an ordered generation pass. -/
@[specialize] def shareRows {Key Value : Type} [BEq Key] [LawfulBEq Key] (key : Nat → Key) (generate : Key → Value)
    (count : Nat) : Array Value := shareRowsLoop key generate (List.range count) none #[]
/-- Complete row sharing equals direct generation at every logical row. -/
theorem shareRows_eq {Key Value : Type} [BEq Key] [LawfulBEq Key] (key : Nat → Key) (generate : Key → Value)
    (count : Nat) : shareRows key generate count = Array.ofFn (fun i : Fin count => generate (key i.val)) := by
  rw [shareRows,shareRowsLoop_eq,Array.empty_append]
  apply Array.ext
  · simp only [List.size_toArray,List.length_map,List.length_range,Array.size_ofFn]
  · intro i hi hj
    simp only [List.getElem_toArray,List.getElem_map,List.getElem_range,Array.getElem_ofFn]
end CompStark.Keccak.GkrProver
namespace CompStark.Keccak.GkrProver
open BF64
/-- Expand shared physical row buffers only at a protocol boundary. -/
def expandRows (rows : Array PackedE) : PackedE :=
  PackedE.ofArray (Array.ofFn fun i : Fin (rows.size*1600) => (rows[i.val/1600]!).get (i.val%1600))
/-- Expansion has the complete logical row-major length. -/
theorem expandRows_size (rows : Array PackedE) : (expandRows rows).size = rows.size*1600 := by
  simp only [expandRows,PackedE.ofArray,Array.size_ofFn]
/-- Expansion reads each logical position directly from its shared row buffer. -/
theorem expandRows_get (rows : Array PackedE) (i : Nat) (hi : i < rows.size*1600) :
    (expandRows rows).get i = (rows[i/1600]!).get (i%1600) := by
  rw [expandRows,PackedE.get_ofArray _ _ (by simpa only [Array.size_ofFn] using hi),Array.getElem_ofFn]
end CompStark.Keccak.GkrProver
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators
/-- Four bitsliced words per position determine one retained sixteen-pack block. -/
def blockWords (w : SlicedWitness) (d m b : Nat) : Array UInt64 :=
  Array.ofFn fun i : Fin 6400 => (w.layers[12*(m+1)-d]!)[i.val/4*(2^w.nLog/64)+4*b+i.val%4]!
/-- One extension coordinate reconstructed from the source block's sixteen binary packs. -/
def blockValue (maps : Array (Array W × Array W)) (bits : Array UInt64) (j : Nat) : W := Id.run do
  let mut value := lane 0
  for q in [:16] do
    let word := bits[j*4+q/4]! >>> (16*(q%4)).toUInt64
    let (low,high) := maps[q]!
    value := WordExt3.add value (WordExt3.add low[(word &&& 255).toNat]!
      high[((word >>> 8) &&& 255).toNat]!)
  return value
/-- Block reconstruction is the exact sum of its sixteen byte-map pairs. -/
theorem blockValue_sum (maps : Array (Array W × Array W)) (bits : Array UInt64) (j : Nat) :
    blockValue maps bits j = ∑ q : Fin 16,
      let word := bits[j*4+q.val/4]! >>> (16*(q.val%4)).toUInt64
      let pair := maps[q.val]!
      pair.1[(word &&& 255).toNat]!+pair.2[((word >>> 8) &&& 255).toNat]! := by
  let term (q : Nat) :=
    let word := bits[j*4+q/4]! >>> (16*(q%4)).toUInt64
    let pair := maps[q]!
    pair.1[(word &&& 255).toNat]!+pair.2[((word >>> 8) &&& 255).toNat]!
  have hf := foldl_value_sum id (fun value q => value+term q) term (fun _ _ => rfl)
    (List.range 16) (0 : W)
  simp only [id_eq,list_range_sum,zero_add] at hf
  simp only [blockValue,Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure,Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range']
  generalize hxs : List.range 16 = xs at hf ⊢
  change xs.foldl (fun value q => value+term q) 0 = _
  rw [hf]
  exact (Fin.sum_univ_eq_sum_range term 16).symm
/-- Captured block words preserve the source's exact bitsliced coordinates. -/
theorem blockWords_get (w : SlicedWitness) (d m b i : Nat) (hi : i < 6400) :
    (blockWords w d m b)[i]! = (w.layers[12*(m+1)-d]!)[i/4*(2^w.nLog/64)+4*b+i%4]! := by
  rw [getElem!_pos _ _ (by simpa only [blockWords,Array.size_ofFn] using hi)]
  exact Array.getElem_ofFn ..
/-- Reconstructing a captured raw block preserves every retained native table cell. -/
theorem blockValue_eq (w : SlicedWitness) (d : Nat) (mu point : Array W) (m b j : Nat) (hj : j < 1600) :
    blockValue (foldedPackMaps mu point) (blockWords w d m b) j = packedTableValue w d mu point m b j := by
  rw [blockValue_sum,packedTableValue_sum]
  apply Finset.sum_congr rfl
  intro q _
  have hq := q.isLt
  have hi : j*4+q.val/4 < 6400 := by omega
  have hd : (j*4+q.val/4)/4 = j := by omega
  have hm : (j*4+q.val/4)%4 = q.val/4 := by omega
  rw [blockWords_get w d m b _ hi,hd,hm]
/-- A physical retained row generated once for each consecutive distinct raw block. -/
def renderBlock (maps : Array (Array W × Array W)) (bits : Array UInt64) : PackedE :=
  PackedE.ofArray (Array.ofFn fun j : Fin 1600 => blockValue maps bits j.val)
/-- Build retained extension rows directly while sharing repeated padding blocks. -/
def packedSharedRows (w : SlicedWitness) (d : Nat) (mu point : Array W) : Array PackedE :=
  let rows := 2^(w.nLog-4)/16
  shareRows (fun i => blockWords w d (i/rows) (i%rows)) (renderBlock (foldedPackMaps mu point)) (2*rows)
/-- Direct shared-row generation has precisely the complete native retained table bytes. -/
theorem packedSharedRows_eq (w : SlicedWitness) (d : Nat) (mu point : Array W) :
    expandRows (packedSharedRows w d mu point) = packedTable w d mu point := by
  let rows := 2^(w.nLog-4)/16
  have shape : (packedSharedRows w d mu point).size = 2*rows := by
    simp only [packedSharedRows,shareRows_eq,Array.size_ofFn]
    rfl
  apply PackedE.ext_get
  · rw [expandRows_size,shape,packedTable_size]
  · intro i hi
    rw [expandRows_size,shape] at hi
    have hrows : 0 < rows := by omega
    have segment : i/1600/rows < 2 := (Nat.div_lt_iff_lt_mul hrows).mpr (by omega)
    have block : i/1600%rows < rows := Nat.mod_lt _ hrows
    have pos : i%1600 < 1600 := Nat.mod_lt _ (by decide)
    rw [expandRows_get _ _ (by rw [shape]; exact hi)]
    have rowIndex : i/1600 < 2*rows := by omega
    have readrow : (packedSharedRows w d mu point)[i/1600]! =
        renderBlock (foldedPackMaps mu point) (blockWords w d (i/1600/rows) (i/1600%rows)) := by
      rw [packedSharedRows,shareRows_eq,getElem!_pos _ _ (by simpa only [Array.size_ofFn] using rowIndex),Array.getElem_ofFn]
    rw [readrow,renderBlock,PackedE.get_ofArray _ _ (by simpa only [Array.size_ofFn] using pos),Array.getElem_ofFn,blockValue_eq _ _ _ _ _ _ _ pos]
    have offset : (i/1600/rows*rows+i/1600%rows)*1600+i%1600 = i := by
      rw [Nat.div_add_mod',Nat.div_add_mod']
    have hg := packedTable_get w d mu point ⟨i/1600/rows,segment⟩ (i/1600%rows) block ⟨i%1600,pos⟩
    change (packedTable w d mu point).get ((i/1600/rows*rows+i/1600%rows)*1600+i%1600) = _ at hg
    rw [offset] at hg
    exact hg.symm
/-- One byte-map pair contributing to a retained position. -/
@[inline] def blockTerm (maps : Array (Array W × Array W)) (bits : Array UInt64) (j q : Nat) : W :=
  let word := bits[j*4+q/4]! >>> (16*(q%4)).toUInt64
  let pair := maps[q]!
  WordExt3.add pair.1[(word &&& 255).toNat]! pair.2[((word >>> 8) &&& 255).toNat]!

/-- Retained byte-map sums carry only three unboxed words between iterations. -/
def blockValueWords (maps : Array (Array W × Array W)) (bits : Array UInt64) (j : Nat) :
    Nat → UInt64 → UInt64 → UInt64 → W
  | 0, a0, a1, a2 => ⟨⟨a0⟩,⟨a1⟩,⟨a2⟩⟩
  | n+1, a0, a1, a2 =>
    let value := blockTerm maps bits j n
    blockValueWords maps bits j n (a0 ^^^ value.c0.val) (a1 ^^^ value.c1.val) (a2 ^^^ value.c2.val)

/-- The word accumulator is the complete byte-map sum plus its entering scalar. -/
theorem blockValueWords_eq (maps : Array (Array W × Array W)) (bits : Array UInt64) (j n : Nat)
    (a0 a1 a2 : UInt64) :
    blockValueWords maps bits j n a0 a1 a2 =
      (⟨⟨a0⟩,⟨a1⟩,⟨a2⟩⟩ : W) + ∑ q ∈ Finset.range n, blockTerm maps bits j q := by
  induction n generalizing a0 a1 a2 with
  | zero => simp only [blockValueWords,Finset.range_zero,Finset.sum_empty,add_zero]
  | succ n ih =>
    rw [blockValueWords,ih,Finset.sum_range_succ]
    change ((⟨⟨a0⟩,⟨a1⟩,⟨a2⟩⟩ : W)+blockTerm maps bits j n)+_ = _
    ac_rfl

/-- Reconstruct a retained coordinate with one scalar allocation at loop exit. -/
def blockValueDirect (maps : Array (Array W × Array W)) (bits : Array UInt64) (j : Nat) : W :=
  blockValueWords maps bits j 16 0 0 0

/-- Unboxed byte-map reconstruction preserves every retained coordinate. -/
@[csimp] theorem blockValue_code : blockValue = blockValueDirect := by
  funext maps bits j
  rw [blockValue_sum,blockValueDirect,blockValueWords_eq]
  change (∑ q : Fin 16, blockTerm maps bits j q.val) = 0+_
  rw [zero_add,Fin.sum_univ_eq_sum_range]

/-- One retained byte-map term with machine-indexed word and shift arithmetic. -/
@[inline] def blockTermU (maps : Array (Array W × Array W)) (bits : Array UInt64)
    (j q : USize) : W :=
  let word := bits[(4*j+q/4).toNat]! >>> (16*(q%4)).toNat.toUInt64
  let pair := maps[q.toNat]!
  WordExt3.add pair.1[(word &&& 255).toNat]! pair.2[((word >>> 8) &&& 255).toNat]!

/-- Native term addresses agree with bounded retained row coordinates. -/
theorem blockTermU_eq (maps : Array (Array W × Array W)) (bits : Array UInt64)
    (j q : USize) (hj : j.toNat < 1600) (hq : q.toNat < 16) :
    blockTermU maps bits j q = blockTerm maps bits j.toNat q.toNat := by
  have h4 : (4 : USize).toNat = 4 := usize_small 4 (by decide)
  have h16 : (16 : USize).toNat = 16 := usize_small 16 (by decide)
  have hs := USize.le_size
  have hm : 4*j.toNat < USize.size := by omega
  have ha : 4*j.toNat+q.toNat/4 < USize.size := by omega
  have ht : 16*(q.toNat%4) < USize.size := by omega
  simp only [blockTermU, blockTerm, USize.toNat_add, USize.toNat_mul,
    USize.toNat_div, USize.toNat_mod, h4, h16,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ht]
  rw [Nat.mul_comm 4]

/-- Scalar byte-map accumulation with a native sixteen-term countdown. -/
def blockValueWordsU (maps : Array (Array W × Array W)) (bits : Array UInt64)
    (j : USize) (hj : j.toNat < 1600) (n : USize) (hn : n.toNat ≤ 16)
    (a0 a1 a2 : UInt64) : W :=
  if hz : n = 0 then ⟨⟨a0⟩,⟨a1⟩,⟨a2⟩⟩ else
    have h1 : (1 : USize) ≤ n := by
      rw [USize.le_iff_toNat_le, USize.toNat_one]
      have hne : n.toNat ≠ 0 := fun h => hz (USize.toNat_inj.mp h)
      omega
    have he : (n-1).toNat+1 = n.toNat := by
      rw [USize.toNat_sub_of_le _ _ h1, USize.toNat_one]
      have hp : 1 ≤ n.toNat := by simpa only [USize.le_iff_toNat_le, USize.toNat_one] using h1
      omega
    let value := blockTermU maps bits j (n-1)
    blockValueWordsU maps bits j hj (n-1) (by omega)
      (a0 ^^^ value.c0.val) (a1 ^^^ value.c1.val) (a2 ^^^ value.c2.val)
termination_by n.toNat
decreasing_by omega

/-- Native accumulation preserves every scalar word of the retained position. -/
theorem blockValueWordsU_eq (maps : Array (Array W × Array W)) (bits : Array UInt64)
    (j : USize) (hj : j.toNat < 1600) (n : USize) (hn : n.toNat ≤ 16)
    (a0 a1 a2 : UInt64) :
    blockValueWordsU maps bits j hj n hn a0 a1 a2 =
      blockValueWords maps bits j.toNat n.toNat a0 a1 a2 := by
  rw [blockValueWordsU]
  split
  · rename_i hz
    subst n
    rfl
  · rename_i hz
    have h1 : (1 : USize) ≤ n := by
      rw [USize.le_iff_toNat_le, USize.toNat_one]
      have hne : n.toNat ≠ 0 := fun h => hz (USize.toNat_inj.mp h)
      omega
    have he : (n-1).toNat+1 = n.toNat := by
      rw [USize.toNat_sub_of_le _ _ h1, USize.toNat_one]
      have hp : 1 ≤ n.toNat := by simpa only [USize.le_iff_toNat_le, USize.toNat_one] using h1
      omega
    rw [blockValueWordsU_eq, blockTermU_eq _ _ _ _ hj (by omega)]
    conv_rhs => rw [← he, blockValueWords]
termination_by n.toNat
decreasing_by
  rw [USize.toNat_sub_of_le _ _ (by assumption), USize.toNat_one]
  have _hp : n.toNat ≠ 0 := fun h => (by assumption : n ≠ 0) (USize.toNat_inj.mp h)
  omega

/-- Use native addresses for physical retained positions. -/
def blockValueNative (maps : Array (Array W × Array W)) (bits : Array UInt64) (j : Nat) : W :=
  if hj : j < 1600 then
    blockValueWordsU maps bits j.toUSize (by rw [usize_small j (by omega)]; exact hj)
      16 (by change (16 : Nat).toUSize.toNat ≤ 16; rw [usize_small 16 (by decide)]) 0 0 0
  else blockValueWords maps bits j 16 0 0 0

/-- Machine-indexed reconstruction preserves all positions of the total scalar definition. -/
@[csimp] theorem blockValueDirect_native_code : blockValueDirect = blockValueNative := by
  funext maps bits j
  unfold blockValueNative blockValueDirect
  split
  · rename_i hj
    have h16 : (16 : USize).toNat = 16 := usize_small 16 (by decide)
    rw [blockValueWordsU_eq, usize_small j (by omega), h16]
  · rfl

/-- Fill a physical retained row directly in packed storage. -/
def renderBlockLoop (maps : Array (Array W × Array W)) (bits : Array UInt64) : Nat → PackedE → PackedE
  | 0, out => out
  | n+1, out => renderBlockLoop maps bits n (out.set n (blockValue maps bits n))

/-- Direct row generation preserves its buffer length. -/
theorem renderBlockLoop_size (maps : Array (Array W × Array W)) (bits : Array UInt64)
    (n : Nat) (out : PackedE) (hn : n ≤ out.size) :
    (renderBlockLoop maps bits n out).size = out.size := by
  induction n generalizing out with
  | zero => rfl
  | succ n ih =>
    rw [renderBlockLoop,ih _ (by rw [PackedE.size_set _ _ _ (by omega)]; omega),
      PackedE.size_set _ _ _ (by omega)]

/-- Direct row generation writes precisely its requested prefix. -/
theorem renderBlockLoop_get (maps : Array (Array W × Array W)) (bits : Array UInt64)
    (n : Nat) (out : PackedE) (hn : n ≤ out.size) (i : Nat) (hi : i < out.size) :
    (renderBlockLoop maps bits n out).get i = if i < n then blockValue maps bits i else out.get i := by
  induction n generalizing out with
  | zero => simp only [renderBlockLoop,Nat.not_lt_zero,ite_false]
  | succ n ih =>
    have hn' : n < out.size := by omega
    rw [renderBlockLoop,ih _ (by rw [PackedE.size_set _ _ _ hn']; omega)
      (by rw [PackedE.size_set _ _ _ hn']; exact hi)]
    by_cases h : i < n
    · rw [ite_eq_left h,ite_eq_left (by omega)]
    · rw [ite_eq_right h,PackedE.get_set _ _ _ hn' hi]
      by_cases he : i=n
      · subst i; rw [ite_eq_left rfl,ite_eq_left (by omega)]
      · rw [ite_eq_right (Ne.symm he),ite_eq_right (by omega)]

/-- Allocate each distinct retained row once, without a boxed scalar array. -/
def renderBlockDirect (maps : Array (Array W × Array W)) (bits : Array UInt64) : PackedE :=
  renderBlockLoop maps bits 1600 (PackedE.zeros 1600)

/-- Packed row generation retains every byte of the complete scalar-array specification. -/
@[csimp] theorem renderBlock_code : renderBlock = renderBlockDirect := by
  funext maps bits
  apply PackedE.ext_get
  · simp only [renderBlock,renderBlockDirect,PackedE.ofArray,Array.size_ofFn]
    exact (renderBlockLoop_size maps bits 1600 (PackedE.zeros 1600) (by rfl)).symm
  · intro i hi
    have hi' : i < 1600 := by simpa only [renderBlock,PackedE.ofArray,Array.size_ofFn] using hi
    rw [renderBlock,PackedE.get_ofArray _ _ (by simpa only [Array.size_ofFn] using hi'),Array.getElem_ofFn,
      renderBlockDirect,renderBlockLoop_get _ _ _ _ (by rfl) i hi',ite_eq_left hi']

/-- Copy source-word references without an unboxed callback return and reboxing boundary. -/
def blockWordsLoop (state : Array UInt64) (groups base : Nat) : Nat → Array UInt64 → Array UInt64
  | 0, out => out
  | n+1, out => blockWordsLoop state groups base n (out.set! n state[n/4*groups+base+n%4]!)

/-- Source-word copying preserves its allocated key length. -/
theorem blockWordsLoop_size (state : Array UInt64) (groups base n : Nat) (out : Array UInt64) :
    (blockWordsLoop state groups base n out).size = out.size := by
  induction n generalizing out with
  | zero => rfl
  | succ n ih => rw [blockWordsLoop,ih,Array.size_set!]

/-- Source-word copying fills precisely its selected raw-key prefix. -/
theorem blockWordsLoop_get (state : Array UInt64) (groups base n : Nat) (out : Array UInt64)
    (hn : n ≤ out.size) (i : Nat) (hi : i < out.size) :
    (blockWordsLoop state groups base n out)[i]! =
      if i < n then state[i/4*groups+base+i%4]! else out[i]! := by
  induction n generalizing out with
  | zero => simp only [blockWordsLoop,Nat.not_lt_zero,ite_false]
  | succ n ih =>
    rw [blockWordsLoop,ih _ (by rw [Array.size_set!]; omega) (by rw [Array.size_set!]; exact hi)]
    by_cases h : i < n
    · rw [ite_eq_left h,ite_eq_left (by omega)]
    · rw [ite_eq_right h]
      by_cases he : i=n
      · subst i; rw [Array.getElem!_set!_self _ _ _ (by omega),ite_eq_left (by omega)]
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm he),ite_eq_right (by omega)]

/-- Capture raw source words with one shared layer lookup and one shared group stride. -/
def blockWordsDirect (w : SlicedWitness) (d m b : Nat) : Array UInt64 :=
  let state := w.layers[12*(m+1)-d]!
  let groups := 2^w.nLog/64
  blockWordsLoop state groups (4*b) 6400 (Array.replicate 6400 0)

/-- Arrays with identical lengths and in-range default reads are equal. -/
theorem array_eq_of_get (a b : Array UInt64) (hs : a.size = b.size)
    (h : ∀ i, i < a.size → a[i]! = b[i]!) : a = b := by
  apply Array.ext hs
  intro i hi hj
  simpa only [getElem!_pos a i hi, getElem!_pos b i hj] using h i hi

/-- Direct source-word copying preserves the complete raw block used as a cache key. -/
@[csimp] theorem blockWords_code : blockWords = blockWordsDirect := by
  funext w d m b
  apply array_eq_of_get
  · simp only [blockWords,Array.size_ofFn,blockWordsDirect,blockWordsLoop_size,Array.size_replicate]
  · intro i hi
    have hi' : i < 6400 := by simpa only [blockWords,Array.size_ofFn] using hi
    rw [blockWords_get _ _ _ _ _ hi',blockWordsDirect,
      blockWordsLoop_get _ _ _ _ _ (by simp only [Array.size_replicate]; omega) i
        (by simpa only [Array.size_replicate] using hi'),ite_eq_left hi']

/-- Compile row-cache generators with the direct packed renderer in scope. -/
def packedSharedRowsDirect (w : SlicedWitness) (d : Nat) (mu point : Array W) : Array PackedE :=
  let rows := 2^(w.nLog-4)/16
  shareRows (fun i => blockWords w d (i/rows) (i%rows)) (renderBlock (foldedPackMaps mu point)) (2*rows)

/-- Direct cache generation retains every physical row and its sharing semantics. -/
@[csimp] theorem packedSharedRows_code : packedSharedRows = packedSharedRowsDirect := rfl

/-- Copy shared row coordinates directly into the production packed buffer. -/
def expandRowsLoop (rows : Array PackedE) : Nat → PackedE → PackedE
  | 0, out => out
  | n+1, out => expandRowsLoop rows n (out.set n ((rows[n/1600]!).get (n%1600)))

/-- Direct expansion preserves the requested packed-buffer length. -/
theorem expandRowsLoop_size (rows : Array PackedE) (n : Nat) (out : PackedE) (hn : n ≤ out.size) :
    (expandRowsLoop rows n out).size = out.size := by
  induction n generalizing out with
  | zero => rfl
  | succ n ih =>
    rw [expandRowsLoop,ih _ (by rw [PackedE.size_set _ _ _ (by omega)]; omega),
      PackedE.size_set _ _ _ (by omega)]

/-- Direct expansion copies exactly the selected physical row coordinate. -/
theorem expandRowsLoop_get (rows : Array PackedE) (n : Nat) (out : PackedE) (hn : n ≤ out.size)
    (i : Nat) (hi : i < out.size) :
    (expandRowsLoop rows n out).get i = if i < n then (rows[i/1600]!).get (i%1600) else out.get i := by
  induction n generalizing out with
  | zero => simp only [expandRowsLoop,Nat.not_lt_zero,ite_false]
  | succ n ih =>
    have hn' : n < out.size := by omega
    rw [expandRowsLoop,ih _ (by rw [PackedE.size_set _ _ _ hn']; omega)
      (by rw [PackedE.size_set _ _ _ hn']; exact hi)]
    by_cases h : i < n
    · rw [ite_eq_left h,ite_eq_left (by omega)]
    · rw [ite_eq_right h,PackedE.get_set _ _ _ hn' hi]
      by_cases he : i=n
      · subst i; rw [ite_eq_left rfl,ite_eq_left (by omega)]
      · rw [ite_eq_right (Ne.symm he),ite_eq_right (by omega)]

/-- Expand shared rows without an intermediate scalar array. -/
def expandRowsDirect (rows : Array PackedE) : PackedE :=
  expandRowsLoop rows (rows.size*1600) (PackedE.zeros (rows.size*1600))

/-- Direct packed expansion preserves every byte at the production table boundary. -/
@[csimp] theorem expandRows_code : expandRows = expandRowsDirect := by
  funext rows
  apply PackedE.ext_get
  · rw [expandRows_size,expandRowsDirect,expandRowsLoop_size _ _ _ (by rfl)]
    rfl
  · intro i hi
    have hi' : i < rows.size*1600 := by rwa [expandRows_size] at hi
    rw [expandRows_get _ _ hi',expandRowsDirect,expandRowsLoop_get _ _ _ (by rfl) i hi',ite_eq_left hi']

/-- Materialize shared physical rows at the existing retained-table boundary. -/
def packedTableShared (w : SlicedWitness) (d : Nat) (mu point : Array W) : PackedE :=
  expandRows (packedSharedRows w d mu point)

/-- Complete scalar reads determine a fixed packed word buffer. -/
theorem fixedWords_ext_read (a b : FixedWords n)
    (same : ∀ i, i < n → readWord a i = readWord b i) : a = b := by
  have h := packed_ext a.toBuffer.val b.toBuffer.val rfl (by
    intro i
    have hi : i.val < n := i.isLt
    have hc := same i.val hi
    rw [readWord_buffer a _ hi, readWord_buffer b _ hi] at hc
    exact congrArg Word.mk hc)
  exact Subtype.ext (congrArg Packed.bytes h)
/-- Materialize a fixed source column without a boxed word array. -/
@[specialize] def columnWordsLoop (f : Nat → UInt64) : Nat → FixedWords 1600 → FixedWords 1600
  | 0, out => out
  | n+1, out => columnWordsLoop f n (writeWord out n (f n))
/-- A materialized source prefix preserves every word outside the prefix. -/
theorem columnWordsLoop_get (f : Nat → UInt64) (count : Nat) (out : FixedWords 1600)
    (hc : count ≤ 1600) (i : Nat) (hi : i < 1600) :
    readWord (columnWordsLoop f count out) i = if i < count then f i else readWord out i := by
  induction count generalizing out with
  | zero => simp only [columnWordsLoop, Nat.not_lt_zero, ite_false]
  | succ count ih =>
    rw [columnWordsLoop, ih _ (by omega), readWord_writeWord _ _ _ (by omega) hi]
    by_cases h : i < count
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h]
      by_cases he : count = i
      · subst i; simp only [ite_true, Nat.lt_succ_self]
      · rw [ite_eq_right he, ite_eq_right (by omega)]
/-- Materialize a packed column with a machine countdown and unboxed word callbacks. -/
@[specialize] def columnWordsLoopU (f : USize → UInt64) (n : USize) (out : FixedWords 1600) : FixedWords 1600 :=
  if hz : n = 0 then out else
    columnWordsLoopU f (n-1) (writeUWord out (n-1) (f (n-1)))
termination_by n.toNat
decreasing_by
  have h1 : (1 : USize) ≤ n := by
    rw [USize.le_iff_toNat_le, USize.toNat_one]
    have hn : n.toNat ≠ 0 := fun h => hz (USize.toNat_inj.mp h)
    omega
  rw [USize.toNat_sub_of_le _ _ h1, USize.toNat_one]
  have hn : 1 ≤ n.toNat := by simpa only [USize.le_iff_toNat_le, USize.toNat_one] using h1
  omega
/-- Native column countdown is the exact natural-coordinate materialization. -/
theorem columnWordsLoopU_eq (f : USize → UInt64) (n : USize) (out : FixedWords 1600) :
    columnWordsLoopU f n out = columnWordsLoop (fun i => f i.toUSize) n.toNat out := by
  rw [columnWordsLoopU]
  split
  · rename_i hz
    subst n
    rfl
  · rename_i hz
    have h1 : (1 : USize) ≤ n := by
      rw [USize.le_iff_toNat_le, USize.toNat_one]
      have hn : n.toNat ≠ 0 := fun h => hz (USize.toNat_inj.mp h)
      omega
    have he : n.toNat = (n-1).toNat+1 := by
      rw [USize.toNat_sub_of_le _ _ h1, USize.toNat_one]
      have hn : 1 ≤ n.toNat := by simpa only [USize.le_iff_toNat_le, USize.toNat_one] using h1
      omega
    rw [columnWordsLoopU_eq]
    conv_rhs => rw [he, columnWordsLoop]
    simp only [writeWord, Nat.toUSize, USize.ofNat_toNat]
termination_by n.toNat
decreasing_by
  rw [USize.toNat_sub_of_le _ _ (by assumption), USize.toNat_one]
  have _hn : n.toNat ≠ 0 := fun h => (by assumption : n ≠ 0) (USize.toNat_inj.mp h)
  omega
/-- One raw column shared by its four consecutive sixteen-bit binary packs. -/
def sourceColumn (state : Array UInt64) (groups : USize) (offset : Nat) : FixedWords 1600 :=
  let nativeOffset := offset.toUSize
  columnWordsLoopU (fun j => state[(j*groups+nativeOffset).toNat]!) 1600 (zeroWords 1600)
/-- A packed source column retains its exact machine-indexed witness word. -/
theorem sourceColumn_get (state : Array UInt64) (groups : USize) (offset i : Nat) (hi : i < 1600) :
    readWord (sourceColumn state groups offset) i = state[(i.toUSize*groups+offset.toUSize).toNat]! := by
  rw [sourceColumn, columnWordsLoopU_eq, tensorCount, columnWordsLoop_get _ _ _ (by omega) _ hi, ite_eq_left hi]
/-- Binary products read the shared raw column using packed machine-word loads. -/
def columnPayload (column : FixedWords 1600) (bits : UInt64) (maps : RmfeProducts) : FixedWords 1600 :=
  columnWordsLoopU (fun k =>
    let a := (readUWord column k >>> bits) &&& 65535
    let b := (readUWord column (shiftU k 1) >>> bits) &&& 65535
    let c := (readUWord column (shiftU k 2) >>> bits) &&& 65535
    maps.ones (a ^^^ c) ^^^ maps.mul b c) 1600 (zeroWords 1600)
/-- Packed source columns preserve the entire reference binary payload. -/
theorem columnPayload_eq (state : Array UInt64) (groups : USize) (offset : Nat)
    (bits : UInt64) (maps : RmfeProducts) :
    columnPayload (sourceColumn state groups offset) bits maps =
      productPayload state groups offset.toUSize bits maps 0 (zeroWords 1600) := by
  apply fixedWords_ext_read
  intro i hi
  rw [columnPayload, columnWordsLoopU_eq, tensorCount, columnWordsLoop_get _ _ _ (by omega) _ hi, ite_eq_left hi,
    productPayload_get _ _ _ _ _ _ _ _ hi, ite_eq_left (Nat.zero_le _)]
  have h1 : (1 : Nat).toUSize = (1 : USize) := by
    apply USize.toNat_inj.mp
    rw [payloadIndex 1 (by decide), USize.toNat_one]
  have h2 : (2 : Nat).toUSize = (2 : USize) := by
    apply USize.toNat_inj.mp
    rw [payloadIndex 2 (by decide), USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)]
  have hs1 := shiftU_small i 1 hi (by decide)
  have hs2 := shiftU_small i 2 hi (by decide)
  rw [h1] at hs1
  rw [h2] at hs2
  dsimp only
  rw [hs1, hs2]
  change (let a := (readWord (sourceColumn state groups offset) i >>> bits) &&& 65535
          let b := (readWord (sourceColumn state groups offset) (shift i 1) >>> bits) &&& 65535
          let c := (readWord (sourceColumn state groups offset) (shift i 2) >>> bits) &&& 65535
          maps.ones (a ^^^ c) ^^^ maps.mul b c) = _
  rw [sourceColumn_get _ _ _ _ hi,
    sourceColumn_get state groups offset (shift i 1) (CompStark.Keccak.Gkr.along ⟨i,hi⟩ 1).isLt,
    sourceColumn_get state groups offset (shift i 2) (CompStark.Keccak.Gkr.along ⟨i,hi⟩ 2).isLt]
  unfold productCell
  dsimp only
  rw [hs1, hs2]
/-- Every shared row retains its generated value at a proved logical coordinate. -/
theorem shareRows_get {Key Value : Type} [BEq Key] [LawfulBEq Key]
    (key : Nat → Key) (generate : Key → Value) (count i : Nat) (hi : i < count) :
    (shareRows key generate count)[i]'(by rw [shareRows_eq, Array.size_ofFn]; exact hi) = generate (key i) := by
  simp only [shareRows_eq, Array.getElem_ofFn]
/-- Build product polynomials while sharing the packed source of each four-pack group. -/
def productColumns (w : SlicedWitness) (d : Nat) (claim : Claim) (maps : RmfeProducts) : ProductData := Id.run do
  let packs := 2^(w.nLog-4)
  let groups := 2^w.nLog/64
  let eq := eqTable claim.point
  let digits := weightDigits claim.weights
  let mut result := Array.replicate 47 (lane 0)
  let mut retained := #[]
  for m in [:2] do
    let state := w.layers[12*(m+1)-d]!
    let columns := shareRows (fun b => b/4) (sourceColumn state groups.toUSize) packs
    for hb : b in [:packs] do
      let payload := columnPayload (columns[b]'(by rw [show columns = shareRows (fun b => b/4) (sourceColumn state groups.toUSize) packs from rfl, shareRows_eq, Array.size_ofFn]; exact hb.upper)) (16*(b%4)).toUInt64 maps
      let coeffs := weightedPayload payload digits
      retained := retained.push coeffs
      let weight := eq[m*packs+b]!
      for k in [:47] do
        result := result.set! k (WordExt3.add result[k]! (WordExt3.mul weight (coeffs.get k)))
  return ⟨result, retained⟩
/-- Shared packed witness columns preserve every product coefficient and retained polynomial. -/
@[csimp] theorem productColumns_code : product = productColumns := by
  funext w d claim maps
  simp (disch := exact Membership.mem.upper ‹_›) only [productColumns, shareRows_get, columnPayload_eq]
  rfl

/-- Reusing equal raw blocks preserves the complete production retained table. -/
@[csimp] theorem packedTable_code : packedTable = packedTableShared := by
  funext w d mu point
  exact (packedSharedRows_eq w d mu point).symm

/-- Compile the observed layer with direct packed shared-row generation. -/
def proveLayerMShared {M : Type → Type} [Monad M] (mark : Phase → Bool → M Unit) (writer : Writer) (w : SlicedWitness) (d : Nat) (claim : Claim)
    (products : RmfeProducts) : M (Layer × Claim × Writer) := do
  mark .product true
  let prod := product w d claim products
  let (s, next) := (writer.writeAll prod.message).sample
  let mut writer := next
  let mut value := evaluate prod.message s
  mark .product false
  mark .rmfe true
  let mu := instanceWeights s
  let kappa := sum mu
  let mut table := PackedE.zeros 0
  mark .rmfe false
  mark .pack true
  let constants := packConstants claim.weights kappa
  mark .packMaps true
  let challenge := CompStark.Sumcheck.prepare s
  let maps := prepareWeightMaps claim.weights challenge
  mark .packMaps false
  mark .packTensor true
  let early := earlyValues w d claim maps products (binaryValues prod.packs claim.point challenge)
  mark .packTensor false

  let mut scale := lane 1
  let mut point := #[]
  let mut packMessages := #[]
  for i in [:claim.point.size] do
    let later := eqTable (claim.point.extract (i+1) claim.point.size)
    mark .packCoefficients true
    let coeffs := if i < 4 then (earlyRound early claim.point point).map (scale*·)
      else packRoundFromClaim table claim.weights constants later claim.point[i]! scale value
    mark .packCoefficients false
    let message := #[coeffs[1]!, coeffs[2]!]
    let (r, next) := (writer.writeAll message).sample
    writer := next
    packMessages := packMessages.push message
    value := (1+claim.point[i]!+r)*(coeffs[0]!+r*(coeffs[1]!+r*coeffs[2]!))
    scale := scale*(1+claim.point[i]!+r)
    point := point.push r
    if i = 3 then
      mark .pack false
      mark .rmfe true
      table := packedTable w d mu point
      mark .rmfe false
      mark .pack true
    else if 4 ≤ i then
      mark .packFolds true
      table := foldPacked table 1600 r
      mark .packFolds false
  mark .pack false
  mark .position true
  let mut t := Array.ofFn fun k : Fin 3 => Array.ofFn fun j : Fin 2048 =>
    if j.val < 1600 then table.get (shift j.val k.val) else lane 0
  let mut weights := claim.weights ++ Array.replicate 448 0
  let mut positionPoint := #[]
  let mut positionMessages := #[]
  for _ in [:11] do
    let message := (positionRound weights t kappa).map (scale*·)
    let (r, next) := (writer.writeAll message).sample
    writer := next
    positionMessages := positionMessages.push message
    positionPoint := positionPoint.push r
    if 1024 ≤ weights.size then
      let map := CompStark.Sumcheck.prepare r
      weights := foldArrayShared weights 1 map
      t := t.map fun a => foldArrayShared a 1 map
    else
      weights := fold weights 1 r
      t := t.map fun a => fold a 1 r
  let evaluations := t.map (·[0]!)
  let (beta, next) := (writer.writeAll evaluations).sample
  mark .position false
  mark .batch true
  let eq := eqTable positionPoint
  let beta2 := beta*beta
  let chi := Array.ofFn fun j : Fin 1600 =>
    eq[j.val]!+beta*eq[shift j.val 4]!+beta2*eq[shift j.val 3]!
  let nextClaim := Claim.mk
    (evaluations[0]!+beta*(evaluations[1]!+beta*evaluations[2]!)) mu point (transposeWeights chi)
  mark .batch false
  return (⟨prod.message, s, packMessages, point, positionMessages, positionPoint, evaluations, beta⟩, nextClaim, next)


/-- Driver compilation retains every protocol state and observer effect. -/
@[csimp] theorem proveLayerM_code : @proveLayerM = @proveLayerMShared := rfl

/-- Prepare only finite endpoints for layers with constant pack blocks. -/
def proveLayerMUniform {M : Type → Type} [Monad M] (mark : Phase → Bool → M Unit) (writer : Writer) (w : SlicedWitness) (d : Nat) (claim : Claim)
    (products : RmfeProducts) (_hp : products = prepareRmfeProducts) : M (Layer × Claim × Writer) := do
  mark .product true
  let prod := product w d claim products
  let (s, next) := (writer.writeAll prod.message).sample
  let mut writer := next
  let mut value := evaluate prod.message s
  mark .product false
  mark .rmfe true
  let mu := instanceWeights s
  let kappa := sum mu
  let mut table := PackedE.zeros 0
  mark .rmfe false
  mark .pack true
  let constants := packConstants claim.weights kappa
  mark .packMaps true
  let challenge := CompStark.Sumcheck.prepare s
  let uniform := decide (UniformLayer w d)
  let maps := if uniform then none else some (prepareWeightMaps claim.weights challenge)
  mark .packMaps false
  mark .packTensor true
  let binary := binaryValues prod.packs claim.point challenge
  let early := match maps with
    | none => initialTensorValues binary
    | some maps => earlyValues w d claim maps products binary
  mark .packTensor false

  let mut scale := lane 1
  let mut point := #[]
  let mut packMessages := #[]
  for i in [:claim.point.size] do
    let later := eqTable (claim.point.extract (i+1) claim.point.size)
    mark .packCoefficients true
    let coeffs := if i < 4 then (earlyRound early claim.point point).map (scale*·)
      else packRoundFromClaim table claim.weights constants later claim.point[i]! scale value
    mark .packCoefficients false
    let message := #[coeffs[1]!, coeffs[2]!]
    let (r, next) := (writer.writeAll message).sample
    writer := next
    packMessages := packMessages.push message
    value := (1+claim.point[i]!+r)*(coeffs[0]!+r*(coeffs[1]!+r*coeffs[2]!))
    scale := scale*(1+claim.point[i]!+r)
    point := point.push r
    if i = 3 then
      mark .pack false
      mark .rmfe true
      table := packedTable w d mu point
      mark .rmfe false
      mark .pack true
    else if 4 ≤ i then
      mark .packFolds true
      table := foldPacked table 1600 r
      mark .packFolds false
  mark .pack false
  mark .position true
  let mut t := Array.ofFn fun k : Fin 3 => Array.ofFn fun j : Fin 2048 =>
    if j.val < 1600 then table.get (shift j.val k.val) else lane 0
  let mut weights := claim.weights ++ Array.replicate 448 0
  let mut positionPoint := #[]
  let mut positionMessages := #[]
  for _ in [:11] do
    let message := (positionRound weights t kappa).map (scale*·)
    let (r, next) := (writer.writeAll message).sample
    writer := next
    positionMessages := positionMessages.push message
    positionPoint := positionPoint.push r
    if 1024 ≤ weights.size then
      let map := CompStark.Sumcheck.prepare r
      weights := foldArrayShared weights 1 map
      t := t.map fun a => foldArrayShared a 1 map
    else
      weights := fold weights 1 r
      t := t.map fun a => fold a 1 r
  let evaluations := t.map (·[0]!)
  let (beta, next) := (writer.writeAll evaluations).sample
  mark .position false
  mark .batch true
  let eq := eqTable positionPoint
  let beta2 := beta*beta
  let chi := Array.ofFn fun j : Fin 1600 =>
    eq[j.val]!+beta*eq[shift j.val 4]!+beta2*eq[shift j.val 3]!
  let nextClaim := Claim.mk
    (evaluations[0]!+beta*(evaluations[1]!+beta*evaluations[2]!)) mu point (transposeWeights chi)
  mark .batch false
  return (⟨prod.message, s, packMessages, point, positionMessages, positionPoint, evaluations, beta⟩, nextClaim, next)


/-- Constant-block preparation preserves the observed layer and writer exactly. -/
theorem proveLayerMUniform_eq {M : Type → Type} [Monad M]
    (mark : Phase → Bool → M Unit) (writer : Writer) (w : SlicedWitness) (d : Nat) (claim : Claim)
    (products : RmfeProducts) (hp : products = prepareRmfeProducts) :
    proveLayerMUniform mark writer w d claim products hp =
      proveLayerMShared mark writer w d claim products := by
  subst products
  by_cases h : UniformLayer w d
  · simp only [proveLayerMUniform, proveLayerMShared, h, decide_true, ite_true,
      early_uniform w d h]
  · simp only [proveLayerMUniform, proveLayerMShared, h, decide_false, Bool.false_eq_true, ite_false]

/-- Compile the complete observed reduction with shared-row layers. -/
def proveMShared {M : Type → Type} [Monad M] (mark : Phase → Bool → M Unit) (writer : Writer) (w : SlicedWitness) (committed : Array UInt64)
    (batchPoint output : Array W) : M Reduction := do
  mark .setup true
  let (segmentPoint, writer) := writer.sampleMany 1
  let segment := segmentPoint[0]!
  let (lanes, writer) := writer.sampleMany 5
  let laneEq := eqTable lanes
  let words := outputWords committed (2^w.nLog) batchPoint
  let wordWeights := Array.ofFn fun slot : Fin 64 =>
    if 25 ≤ slot.val && slot.val < 50 then (1+segment)*laneEq[slot.val-25]! else 0
  let middle := dot words wordWeights
  let writer := writer.write middle
  let mut claim := Claim.mk
    (middle+segment*dot (laneEq.extract 0 25) output)
    (eqTable (batchPoint.extract 0 4)) ((batchPoint.extract 4 batchPoint.size).push segment)
    (Array.ofFn fun j : Fin 1600 => WordExt3.mulScalar laneEq[j.val/64]! ⟨1 <<< (j.val%64).toUInt64⟩)
  let mut writer := writer
  let mut layers := #[]
  mark .setup false
  mark .rmfe true
  let products := prepareRmfeProducts
  mark .rmfe false
  for d in [:12] do
    let (layer, nextClaim, next) ← proveLayerMUniform mark writer w d claim products rfl
    layers := layers.push layer
    claim := nextClaim
    writer := next
  mark .openings true
  let (openings, finalWriter) := proveOpenings writer committed (2^w.nLog) words wordWeights middle claim
  mark .openings false
  return ⟨batchPoint, segment, lanes, middle, layers, claim, openings, finalWriter⟩


/-- Driver compilation retains every protocol state and observer effect. -/
@[csimp] theorem proveM_code : @proveM = @proveMShared := by
  funext M inst mark writer w committed batchPoint output
  unfold proveMShared
  simp only [proveLayerMUniform_eq]
  rfl

/-- Compile the pure reduction through the certified shared-row driver. -/
def proveShared (writer : Writer) (w : SlicedWitness) (committed : Array UInt64)
    (batchPoint output : Array W) : Reduction :=
  Id.run (proveM (fun _ _ => pure ()) writer w committed batchPoint output)


/-- Driver compilation retains every protocol state and observer effect. -/
@[csimp] theorem prove_code : @prove = @proveShared := rfl

end CompStark.Keccak.GkrProver
