/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Algorithms derived from succinctlabs/flock (flock-core), MIT OR Apache-2.0.
Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum.
Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang.
-/
module
public import CompStark.Pcs.InductionDot

/-! Eight-query mixed dots over transposed tensors with deferred base-field reduction. -/
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
@[expose] public section
namespace CompStark.Pcs
open BF64

/-- A carry-less polynomial awaiting reduction modulo the base-field polynomial. -/
structure InductionWide where
  /-- Low 64 polynomial coefficients. -/
  lo : UInt64
  /-- High 64 polynomial coefficients. -/
  hi : UInt64

/-- Reduce a complete mixed dot once. -/
@[inline] def InductionWide.reduce (a : InductionWide) : Word := ⟨Word.reduceWide a.lo a.hi⟩

/-- XOR unreduced polynomial accumulators. -/
@[inline] def InductionWide.add (a b : InductionWide) : InductionWide := ⟨a.lo ^^^ b.lo,a.hi ^^^ b.hi⟩

/-- Polynomial reduction is linear over every unreduced accumulator. -/
theorem InductionWide.reduce_add (a b : InductionWide) :
    (a.add b).reduce.toField = a.reduce.toField + b.reduce.toField := by
  apply BF64.ext
  change (Word.reduceWide (a.lo ^^^ b.lo) (a.hi ^^^ b.hi)).toBitVec =
    (Word.reduceWide a.lo a.hi).toBitVec ^^^ (Word.reduceWide b.lo b.hi).toBitVec
  simp only [Word.reduceWide,UInt64.toBitVec_xor,UInt64.toBitVec_shiftLeft,
    UInt64.toBitVec_shiftRight,UInt64.toBitVec_ofNat,BitVec.shiftLeft_eq',
    BitVec.ushiftRight_eq',BitVec.ofNat_eq_ofNat,BitVec.toNat_umod,
    BitVec.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
  simp only [BitVec.shiftLeft_xor_distrib,BitVec.ushiftRight_xor_distrib]
  ac_rfl

/-- Carry-less base multiplication before its final polynomial reduction. -/
@[inline] def InductionWide.mul (a b : Word) : InductionWide :=
  let lo := Word.clMul32 a.val b.val
  let hi := Word.clMul32 (a.val >>> 32) (b.val >>> 32)
  let mid := Word.clMul32 (a.val ^^^ (a.val >>> 32)) (b.val ^^^ (b.val >>> 32)) ^^^ lo ^^^ hi
  ⟨lo ^^^ (mid <<< 32),hi ^^^ (mid >>> 32)⟩

/-- Hardware carry-less multiplication before the shared final reduction. -/
@[inline] def InductionWide.mulClmul (a b : Word) : InductionWide :=
  ⟨Word.clMulLo a.val b.val, Word.clMulHi a.val b.val⟩

/-- The hardware product has the original pure Karatsuba polynomial coefficients. -/
@[csimp] theorem InductionWide.mul_code : InductionWide.mul = InductionWide.mulClmul := by
  rfl

/-- The unreduced base product reduces to the exact field product. -/
theorem InductionWide.mul_eq (a b : Word) : (InductionWide.mul a b).reduce.toField = a.toField*b.toField :=
  Word.toField_mulMasked a b

/-- Eight full-width coefficients of shared mixed-dot weights. -/
structure Weights8 where
  /-- Polynomial-coordinate words in query order. -/
  words : Vector UInt64 8

/-- Pack eight shared mixed-dot weights. -/
def Weights8.create (f : Fin 8 → Word) : Weights8 :=
  ⟨Vector.ofFn fun i => (f i).val⟩

/-- Multiply one packed weight without reducing its carry-less polynomial. -/
@[inline] def Weights8.product (weights : Weights8) (i : Fin 8) (a : Word) : InductionWide :=
  InductionWide.mul a ⟨weights.words[i]⟩

/-- Packed weights retain the exact base-field product. -/
theorem Weights8.product_eq (f : Fin 8 → Word) (i : Fin 8) (a : Word) :
    ((Weights8.create f).product i a).reduce.toField = a.toField * (f i).toField := by
  simp only [Weights8.create, Weights8.product, Fin.getElem_fin, Vector.getElem_ofFn]
  exact Word.toField_mulMasked a (f i)

/-- Eight cubic extension weights in paired low/high limbs and consecutive third limbs. -/
structure ExtensionWeights8 where
  /-- First two limbs of even-numbered queries. -/
  lo : Vector UInt64 8
  /-- First two limbs of odd-numbered queries. -/
  hi : Vector UInt64 8
  /-- Third limbs in query order. -/
  c2 : Vector UInt64 8

/-- Pack the paired extension-limb layout consumed by Rust's mixed dot kernel. -/
def ExtensionWeights8.create (f : Fin 8 → Fin 3 → Word) : ExtensionWeights8 :=
  ⟨Vector.ofFn (fun i => (f ⟨2*(i.val/2),by have := i.isLt; omega⟩ ⟨i.val%2,by omega⟩).val),
    Vector.ofFn (fun i => (f ⟨2*(i.val/2)+1,by have := i.isLt; omega⟩ ⟨i.val%2,by omega⟩).val),
    Vector.ofFn (fun i => (f i 2).val)⟩

/-- Read one base coordinate from the eight-query paired extension layout. -/
@[inline] def ExtensionWeights8.coordinate (weights : ExtensionWeights8) (q : Fin 8) (c : Fin 3) : Word :=
  if bound : c.val < 2 then
    let i : Fin 8 := ⟨2*(q.val/2)+c.val,by have := q.isLt; omega⟩
    ⟨if q.val%2 = 0 then weights.lo[i] else weights.hi[i]⟩
  else ⟨weights.c2[q]⟩

/-- Paired extension-limb packing retains every original query coordinate. -/
theorem ExtensionWeights8.coordinate_eq (f : Fin 8 → Fin 3 → Word) (q : Fin 8) (c : Fin 3) :
    (ExtensionWeights8.create f).coordinate q c = f q c := by
  unfold ExtensionWeights8.coordinate ExtensionWeights8.create
  split
  · rename_i bound
    dsimp only
    split
    · rename_i even
      simp only [Fin.getElem_fin,Vector.getElem_ofFn]
      have query : (⟨2*((2*(q.val/2)+c.val)/2),by omega⟩ : Fin 8) = q := by
        apply Fin.ext
        dsimp only
        omega
      have coord : (⟨(2*(q.val/2)+c.val)%2,by omega⟩ : Fin 3) = c := by
        apply Fin.ext
        dsimp only
        omega
      rw [query,coord]
    · rename_i odd
      simp only [Fin.getElem_fin,Vector.getElem_ofFn]
      have query : (⟨2*((2*(q.val/2)+c.val)/2)+1,by omega⟩ : Fin 8) = q := by
        apply Fin.ext
        dsimp only
        omega
      have coord : (⟨(2*(q.val/2)+c.val)%2,by omega⟩ : Fin 3) = c := by
        apply Fin.ext
        dsimp only
        omega
      rw [query,coord]
  · rename_i bound
    have coord : c = 2 := by apply Fin.ext; have := c.isLt; omega
    subst c
    simp only [Fin.getElem_fin,Vector.getElem_ofFn]

/-- Accumulate one coordinate of a paired eight-query extension weight. -/
@[inline] def ExtensionWeights8.product (weights : ExtensionWeights8) (q : Fin 8) (c : Fin 3) (a : Word) : InductionWide :=
  InductionWide.mul a (weights.coordinate q c)

/-- Paired mixed products retain the exact base-coordinate field product. -/
theorem ExtensionWeights8.product_eq (f : Fin 8 → Fin 3 → Word) (q : Fin 8) (c : Fin 3) (a : Word) :
    ((ExtensionWeights8.create f).product q c a).reduce.toField = a.toField*(f q c).toField := by
  rw [ExtensionWeights8.product,InductionWide.mul_eq,ExtensionWeights8.coordinate_eq]

/-- Accumulate all unreduced products with two native scalar accumulators. -/
@[specialize] def inductionWideLoop (count : Nat) (f : Fin count → InductionWide)
    (left : Nat) (bound : left ≤ count) (lo hi : UInt64) : Word :=
  match left with
  | 0 => (⟨lo,hi⟩ : InductionWide).reduce
  | left+1 =>
    let term := f ⟨left,by omega⟩
    inductionWideLoop count f left (by omega) (lo ^^^ term.lo) (hi ^^^ term.hi)
termination_by structural left

/-- Deferred reduction gives the exact finite sum of mixed products. -/
theorem inductionWideLoop_eq (count : Nat) (f : Fin count → InductionWide)
    (left : Nat) (bound : left ≤ count) (lo hi : UInt64) :
    (inductionWideLoop count f left bound lo hi).toField =
      (⟨lo,hi⟩ : InductionWide).reduce.toField +
        ∑ i : Fin left, (f ⟨i.val,by omega⟩).reduce.toField := by
  induction left generalizing lo hi with
  | zero =>
    rw [inductionWideLoop]
    simp only [Fin.sum_univ_zero,add_zero]
  | succ left ih =>
    rw [inductionWideLoop,ih,Fin.sum_univ_castSucc]
    have add := InductionWide.reduce_add (⟨lo,hi⟩ : InductionWide) (f ⟨left,by omega⟩)
    change _ + _ = _
    rw [show (⟨lo ^^^ (f ⟨left,by omega⟩).lo,hi ^^^ (f ⟨left,by omega⟩).hi⟩ : InductionWide).reduce.toField =
      (⟨lo,hi⟩ : InductionWide).reduce.toField + (f ⟨left,by omega⟩).reduce.toField from add]
    ac_rfl

/-- Pad a finite sum with zero terms. -/
private theorem sum_padded {A : Type} [AddCommMonoid A] (count padded : Nat) (bound : count ≤ padded)
    (f : Fin count → A) :
    (∑ i : Fin padded, if h : i.val < count then f ⟨i.val,h⟩ else 0) = ∑ i : Fin count, f i := by
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le bound
  rw [Fin.sum_univ_add]
  simp only [Fin.val_castAdd,Fin.val_natAdd,Fin.isLt,↓reduceDIte]
  have high : (∑ i : Fin extra, if h : count+i.val < count then f ⟨count+i.val,h⟩ else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact dite_eq_right (by omega)
  rw [high,add_zero]

/-- Reconstruct split tensors with transposed low rows and eight-query packed high weights. -/
def splitDotRowsPresplit (lo hi lanes count : Nat)
    (low : Vector (Vector Word (2^lo)) count)
    (scaled : Vector (Vector (Vector Word lanes) count) (2^hi)) :
    BF64.Packed.Buffer (2^(lo+hi)*lanes) :=
  let groups := (count+7)/8
  let transposed := Vector.ofFn fun l : Fin (2^lo) => Vector.ofFn fun q : Fin (groups*8) =>
    if h : q.val < count then low[q.val][l] else ⟨0⟩
  let packed := Vector.ofFn fun h : Fin (2^hi) => Vector.ofFn fun group : Fin groups =>
    Vector.ofFn fun c : Fin lanes => Weights8.create fun lane =>
      if bound : group.val*8+lane.val < count then scaled[h][group.val*8+lane.val][c] else ⟨0⟩
  AdditiveNTT.Packed.tabulate _ fun i =>
    let row := i.divNat
    let h : Fin (2^hi) := ⟨row.val/2^lo,by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
      simpa only [pow_add,Nat.mul_comm] using row.isLt⟩
    let l : Fin (2^lo) := ⟨row.val%2^lo,Nat.mod_lt _ (Nat.two_pow_pos _)⟩
    let c := i.modNat
    inductionWideLoop (groups*8) (fun q =>
      (packed[h][q.divNat][c]).product q.modNat transposed[l][q]) (groups*8) (Nat.le_refl _) 0 0

/-- Reconstruct the split tensor using Rust's paired eight-query extension weights. -/
def splitDotRowsPacked (lo hi lanes count : Nat)
    (low : Vector (Vector Word (2^lo)) count)
    (scaled : Vector (Vector (Vector Word lanes) count) (2^hi)) :
    BF64.Packed.Buffer (2^(lo+hi)*lanes) :=
  let groups := (count+7)/8
  let components := (lanes+2)/3
  let transposed := Vector.ofFn fun l : Fin (2^lo) => Vector.ofFn fun q : Fin (groups*8) =>
    if h : q.val < count then low[q.val][l] else ⟨0⟩
  let packed := Vector.ofFn fun h : Fin (2^hi) => Vector.ofFn fun group : Fin groups =>
    Vector.ofFn fun component : Fin components => ExtensionWeights8.create fun q c =>
      if bound : group.val*8+q.val < count ∧ component.val*3+c.val < lanes then
        scaled[h][group.val*8+q.val][component.val*3+c.val] else ⟨0⟩
  AdditiveNTT.Packed.tabulate _ fun i =>
    let row := i.divNat
    let h : Fin (2^hi) := ⟨row.val/2^lo,by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
      simpa only [pow_add,Nat.mul_comm] using row.isLt⟩
    let l : Fin (2^lo) := ⟨row.val%2^lo,Nat.mod_lt _ (Nat.two_pow_pos _)⟩
    let c := i.modNat
    let component : Fin components := ⟨c.val/3,by dsimp only [components]; have := c.isLt; omega⟩
    inductionWideLoop (groups*8) (fun q =>
      (packed[h][q.divNat][component]).product q.modNat ⟨c.val%3,by omega⟩ transposed[l][q])
      (groups*8) (Nat.le_refl _) 0 0

/-- An empty unreduced accumulator represents the field zero. -/
theorem InductionWide.reduce_zero : (⟨0,0⟩ : InductionWide).reduce.toField = 0 := rfl

/-- One padded query lane contributes its original mixed product or zero. -/
theorem packedQuery_eq (count groups : Nat) (q : Fin (groups*8))
    (weight low : Fin count → Word) :
    ((Weights8.create fun lane =>
      if h : q.divNat.val*8+lane.val < count then weight ⟨q.divNat.val*8+lane.val,h⟩ else ⟨0⟩).product
      q.modNat (if h : q.val < count then low ⟨q.val,h⟩ else ⟨0⟩)).reduce.toField =
      if h : q.val < count then Word.ringEquiv (weight ⟨q.val,h⟩ * low ⟨q.val,h⟩) else 0 := by
  rw [Weights8.product_eq]
  have address : (q.val/8)*8+q.val%8 = q.val := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod q.val 8
  change (if h : q.val < count then low ⟨q.val,h⟩ else ⟨0⟩).toField *
    (if h : (q.val/8)*8+q.val%8 < count then weight ⟨(q.val/8)*8+q.val%8,h⟩ else ⟨0⟩).toField = _
  simp only [address]
  split
  · rename_i bound
    rw [map_mul]
    exact mul_comm _ _
  · rename_i bound
    change (0 : BF64) * 0 = 0
    exact zero_mul _

/-- One padded query and component retain the original paired mixed-dot product. -/
theorem pairedQuery_eq (count groups lanes : Nat) (q : Fin (groups*8)) (c : Fin lanes)
    (weight : Fin count → Fin lanes → Word) (low : Fin count → Word) :
    ((ExtensionWeights8.create fun lane component =>
      if h : q.divNat.val*8+lane.val < count ∧ (c.val/3)*3+component.val < lanes then
        weight ⟨q.divNat.val*8+lane.val,h.1⟩ ⟨(c.val/3)*3+component.val,h.2⟩ else ⟨0⟩).product
      q.modNat ⟨c.val%3,by omega⟩ (if h : q.val < count then low ⟨q.val,h⟩ else ⟨0⟩)).reduce.toField =
      if h : q.val < count then Word.ringEquiv (weight ⟨q.val,h⟩ c * low ⟨q.val,h⟩) else 0 := by
  rw [ExtensionWeights8.product_eq]
  have query : (q.val/8)*8+q.val%8 = q.val := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod q.val 8
  have component : (c.val/3)*3+c.val%3 = c.val := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod c.val 3
  change (if h : q.val < count then low ⟨q.val,h⟩ else ⟨0⟩).toField *
    (if h : (q.val/8)*8+q.val%8 < count ∧ (c.val/3)*3+c.val%3 < lanes then
      weight ⟨(q.val/8)*8+q.val%8,h.1⟩ ⟨(c.val/3)*3+c.val%3,h.2⟩ else ⟨0⟩).toField = _
  simp only [query,component,c.isLt,and_true]
  split
  · rw [map_mul]
    exact mul_comm _ _
  · change (0 : BF64) * 0 = 0
    exact zero_mul _

section
attribute [local irreducible] inductionWideLoop Weights8.product Weights8.create InductionWide.reduce
  AdditiveNTT.Packed.tabulate Word.toField

set_option maxHeartbeats 600000 in
set_option maxRecDepth 8192 in
/-- Transposition, eight-query padding and deferred reduction retain every output word. -/
theorem splitDotRowsPresplit_eq (lo hi lanes count : Nat)
    (low : Vector (Vector Word (2^lo)) count)
    (scaled : Vector (Vector (Vector Word lanes) count) (2^hi)) :
    splitDotRowsPresplit lo hi lanes count low scaled = splitDotRows lo hi lanes count low scaled := by
  unfold splitDotRowsPresplit splitDotRows
  apply congrArg (AdditiveNTT.Packed.tabulate (2^(lo+hi)*lanes))
  funext i
  apply Word.toField_injective
  rw [inductionWideLoop_eq,InductionWide.reduce_zero,zero_add]
  change _ = Word.ringEquiv (∑ q : Fin count, _)
  rw [map_sum]
  have padded : count ≤ ((count+7)/8)*8 := by omega
  conv_rhs => rw [← sum_padded count (((count+7)/8)*8) padded]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Fin.getElem_fin,Vector.getElem_ofFn]
  have highBound : i.divNat.val/2^lo < 2^hi := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    simpa only [pow_add,Nat.mul_comm] using i.divNat.isLt
  exact packedQuery_eq count ((count+7)/8) q
    (fun q => scaled[i.divNat.val/2^lo][q][i.modNat])
    (fun q => low[q][i.divNat.val%2^lo])


/-- Paired extension packing, transposition and deferred reduction preserve every dense output. -/
theorem splitDotRowsPacked_eq (lo hi lanes count : Nat)
    (low : Vector (Vector Word (2^lo)) count)
    (scaled : Vector (Vector (Vector Word lanes) count) (2^hi)) :
    splitDotRowsPacked lo hi lanes count low scaled = splitDotRows lo hi lanes count low scaled := by
  unfold splitDotRowsPacked splitDotRows
  apply congrArg (AdditiveNTT.Packed.tabulate (2^(lo+hi)*lanes))
  funext i
  apply Word.toField_injective
  rw [inductionWideLoop_eq,InductionWide.reduce_zero,zero_add]
  change _ = Word.ringEquiv (∑ q : Fin count, _)
  rw [map_sum]
  have padded : count ≤ ((count+7)/8)*8 := by omega
  conv_rhs => rw [← sum_padded count (((count+7)/8)*8) padded]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Fin.getElem_fin,Vector.getElem_ofFn]
  have highBound : i.divNat.val/2^lo < 2^hi := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    simpa only [pow_add,Nat.mul_comm] using i.divNat.isLt
  exact pairedQuery_eq count ((count+7)/8) lanes q i.modNat
    (fun q c => scaled[i.divNat.val/2^lo][q][c])
    (fun q => low[q][i.divNat.val%2^lo])

/-- Native dense reconstruction executes the certified paired eight-query layout. -/
@[csimp] theorem splitDotRowsNative_code : @splitDotRowsNative = @splitDotRowsPacked := by
  funext lo hi lanes count low scaled
  exact (congrFun (congrFun (congrFun (congrFun (congrFun (congrFun splitDotRows_code lo) hi) lanes) count) low) scaled).symm.trans
    (splitDotRowsPacked_eq lo hi lanes count low scaled).symm

/-- Dense induction with transposed low tensors and eight-query deferred-reduction dots. -/
def induceSplitRowsPacked (lo hi rate : Nat) (hd : lo+hi+rate < 64) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2^(lo+hi+rate))) count) (values : Fin count → Fin lanes → Word) :
    BF64.Packed.Buffer (2^(lo+hi)*lanes) :=
  let constants := inductionConstants (lo+hi) (by omega)
  let factors := positions.map (inductionFactors (by omega) hd constants)
  let low := factors.map fun f => novelTensor lo (Vector.ofFn fun k => f[k.val])
  let high := factors.map fun f => novelTensor hi (Vector.ofFn fun k => f[lo+k.val]'(by have := k.isLt; omega))
  let scaled := Vector.ofFn fun h : Fin (2^hi) => Vector.ofFn fun q : Fin count =>
    Vector.ofFn fun c : Fin lanes => values q c * high[q][h]
  splitDotRowsPacked lo hi lanes count low scaled

/-- Packed dense induction equals the complete split-tensor specification. -/
theorem induceSplitRowsPacked_eq (lo hi rate : Nat) (hd : lo+hi+rate < 64) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2^(lo+hi+rate))) count) (values : Fin count → Fin lanes → Word) :
    induceSplitRowsPacked lo hi rate hd lanes positions values = induceSplitRows lo hi rate hd lanes positions values := by
  unfold induceSplitRowsPacked induceSplitRows
  rw [splitDotRowsPacked_eq]

/-- Every packed dense induction coordinate equals the certified encoder transpose. -/
theorem induceSplitRowsPacked_refines (lo hi rate : Nat) (hd : lo+hi+rate < 64)
    (plan : AdditiveNTT.Packed.FlatPlan (lo+hi+rate) hd) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2^(lo+hi+rate))) count) (values : Fin count → Fin lanes → Word)
    (index : Fin (2^(lo+hi)*lanes)) :
    BF64.Packed.read (induceSplitRowsPacked lo hi rate hd lanes positions values) index =
      BF64.Packed.read (induceRows hd plan lanes positions values) index := by
  rw [induceSplitRowsPacked_eq]
  exact induceSplitRows_refines lo hi rate hd plan lanes positions values index

end

end CompStark.Pcs
