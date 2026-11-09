/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.PackedInductionDot
public import CompStark.Pcs.BitFold

/-! Packed mixed base/extension dots with one reduction per output coordinate. -/
@[expose] public section
namespace CompStark.Pcs
open BF64
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
attribute [local irreducible] Word.toField WordExt3.toField

/-- Three unreduced polynomial coordinates of one extension accumulator. -/
structure MixedWide where
  /-- Constant polynomial coordinate. -/
  c0 : InductionWide
  /-- Linear polynomial coordinate. -/
  c1 : InductionWide
  /-- Quadratic polynomial coordinate. -/
  c2 : InductionWide

/-- Reduce all three polynomial coordinates once. -/
@[inline] def MixedWide.reduce (a : MixedWide) : WordExt3 :=
  ⟨a.c0.reduce, a.c1.reduce, a.c2.reduce⟩

/-- XOR the three unreduced polynomial coordinates. -/
@[inline] def MixedWide.add (a b : MixedWide) : MixedWide :=
  ⟨a.c0.add b.c0, a.c1.add b.c1, a.c2.add b.c2⟩

/-- Deferred polynomial reduction preserves extension addition. -/
theorem MixedWide.reduce_add (a b : MixedWide) :
    (a.add b).reduce = WordExt3.add a.reduce b.reduce := by
  simp only [MixedWide.add, MixedWide.reduce, WordExt3.add]
  congr 1 <;> apply Word.toField_injective <;>
    simp only [Word.toField_add, InductionWide.reduce_add]

/-- An empty wide accumulator reduces to the extension zero. -/
theorem MixedWide.reduce_zero : (⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ : MixedWide).reduce = 0 := rfl

/-- Multiply extension coordinates before the final base-polynomial reduction. -/
@[inline] def MixedWide.mul (a b : WordExt3) : MixedWide :=
  let p0 := InductionWide.mul a.c0 b.c0
  let p1 := InductionWide.mul a.c1 b.c1
  let p2 := InductionWide.mul a.c2 b.c2
  let p01 := ((InductionWide.mul (Word.add a.c0 a.c1) (Word.add b.c0 b.c1)).add p0).add p1
  let p02 := ((InductionWide.mul (Word.add a.c0 a.c2) (Word.add b.c0 b.c2)).add p0).add p2
  let p12 := ((InductionWide.mul (Word.add a.c1 a.c2) (Word.add b.c1 b.c2)).add p1).add p2
  ⟨p0.add p12, (p01.add p12).add p2, (p02.add p1).add p2⟩

/-- Cubic folding before base reduction retains the exact extension product. -/
theorem MixedWide.reduce_mul (a b : WordExt3) :
    (MixedWide.mul a b).reduce = WordExt3.mul a b := by
  simp only [MixedWide.mul, MixedWide.reduce, InductionWide.mul_code,
    InductionWide.mulClmul, InductionWide.add, InductionWide.reduce,
    WordExt3.mul_eq_mulDeferred, WordExt3.mulDeferred, WordExt3.wideProduct,
    WordExt3.wideXor, WordExt3.reduceProduct]

/-- Eight extension weights in the paired limb layout of the mixed dot kernel. -/
abbrev MixedWeights8 := ExtensionWeights8

/-- Pack paired first/second limbs and consecutive third limbs once for all witness rows. -/
def MixedWeights8.create (f : Fin 8 → WordExt3) : MixedWeights8 :=
  ExtensionWeights8.create fun i c => mapLimb (f i) c

/-- Multiply one paired extension weight, retaining all unreduced coordinates. -/
@[inline] def MixedWeights8.product (w : MixedWeights8) (i : Fin 8) (a : Word) : MixedWide :=
  if a.val = 0 then ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ else
    ⟨ExtensionWeights8.product w i 0 a, ExtensionWeights8.product w i 1 a, ExtensionWeights8.product w i 2 a⟩

/-- Paired extension products equal the complete mixed scalar product. -/
theorem MixedWeights8.product_eq (f : Fin 8 → WordExt3) (i : Fin 8) (a : Word) :
    ((MixedWeights8.create f).product i a).reduce = WordExt3.mulScalar (f i) a := by
  unfold MixedWeights8.product
  split
  · rename_i zero
    rw [MixedWide.reduce_zero]
    apply WordExt3.toField_injective
    rw [WordExt3.toField_mulScalar]
    have scalar : a.toField = 0 := by
      have az : a = ⟨0⟩ := by cases a; exact congrArg Word.mk zero
      rw [az]
      exact map_zero Word.ringEquiv
    rw [scalar, zero_smul]
    exact map_zero WordExt3.ringEquiv
  · simp only [MixedWeights8.create, MixedWide.reduce, WordExt3.mulScalar]
    congr 1 <;> apply Word.toField_injective <;>
      simp only [ExtensionWeights8.product_eq, Word.toField_mulMasked, mapLimb, Fin.val_zero, Fin.val_one,
        show (2 : Fin 3).val = 2 from rfl, Nat.reduceEqDiff, ite_true, ite_false] <;>
      exact mul_comm _ _

/-- Accumulate three unreduced coordinates with six native scalar registers. -/
@[specialize] def mixedWideLoop (count : Nat) (f : Fin count → MixedWide)
    (left : Nat) (bound : left ≤ count) (a0 b0 a1 b1 a2 b2 : UInt64) : WordExt3 :=
  match left with
  | 0 => (⟨⟨a0,b0⟩,⟨a1,b1⟩,⟨a2,b2⟩⟩ : MixedWide).reduce
  | left+1 =>
    let v := f ⟨left, by omega⟩
    mixedWideLoop count f left (by omega)
      (a0 ^^^ v.c0.lo) (b0 ^^^ v.c0.hi) (a1 ^^^ v.c1.lo) (b1 ^^^ v.c1.hi)
      (a2 ^^^ v.c2.lo) (b2 ^^^ v.c2.hi)
termination_by structural left

/-- Wide accumulation preserves the complete finite extension sum. -/
theorem mixedWideLoop_refines (count : Nat) (f : Fin count → MixedWide)
    (left : Nat) (bound : left ≤ count) (a0 b0 a1 b1 a2 b2 : UInt64) :
    (mixedWideLoop count f left bound a0 b0 a1 b1 a2 b2).toField =
      (⟨⟨a0,b0⟩,⟨a1,b1⟩,⟨a2,b2⟩⟩ : MixedWide).reduce.toField +
        ∑ i : Fin left, (f ⟨i.val,by omega⟩).reduce.toField := by
  induction left generalizing a0 b0 a1 b1 a2 b2 with
  | zero =>
    rw [mixedWideLoop]
    simp only [Fin.sum_univ_zero, add_zero]
  | succ left ih =>
    rw [mixedWideLoop, ih, Fin.sum_univ_castSucc]
    change (MixedWide.add (⟨⟨a0,b0⟩,⟨a1,b1⟩,⟨a2,b2⟩⟩ : MixedWide)
      (f ⟨left,by omega⟩)).reduce.toField + _ = _
    rw [MixedWide.reduce_add, WordExt3.toField_add]
    ac_rfl

/-- Sum extension products with scalar accumulators and one reduction at the boundary. -/
@[inline] def dotExtWide (count : Nat) (a b : Fin count → WordExt3) : WordExt3 :=
  mixedWideLoop count (fun i => MixedWide.mul (a i) (b i)) count (Nat.le_refl _) 0 0 0 0 0 0

/-- Deferred extension dots preserve the complete finite product sum. -/
theorem dotExtWide_refines (count : Nat) (a b : Fin count → WordExt3) :
    (dotExtWide count a b).toField = ∑ i : Fin count, (a i).toField * (b i).toField := by
  rw [dotExtWide, mixedWideLoop_refines, MixedWide.reduce_zero]
  have z : (0 : WordExt3).toField = 0 := map_zero WordExt3.ringEquiv
  simp only [z, zero_add, MixedWide.reduce_mul, WordExt3.toField_mul]

/-- Eight-wide packed extension weights with a zero-padded final group. -/
abbrev MixedDotPlan (count : Nat) := Vector MixedWeights8 ((count+7)/8)

/-- Retain packed weights once before visiting the witness lanes. -/
def prepareMixedDot {count : Nat} (weights : Vector WordExt3 count) : MixedDotPlan count :=
  Vector.ofFn fun group => MixedWeights8.create fun i =>
    if h : group.val*8+i.val < count then weights[group.val*8+i.val]'h else 0

/-- Apply retained weights to a complete mixed dot and reduce each coordinate once. -/
@[inline] def dotMixedPlan {count : Nat} (plan : MixedDotPlan count) (f : Fin count → Word) : WordExt3 :=
  let groups := (count+7)/8
  mixedWideLoop (groups*8) (fun q => if h : q.val < count then
    plan[q.divNat].product q.modNat (f ⟨q.val,h⟩) else ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩)
    (groups*8) (Nat.le_refl _) 0 0 0 0 0 0

/-- Packed mixed dots retain every unpadded scalar product. -/
theorem dotMixedPlan_refines {count : Nat} (weights : Vector WordExt3 count) (f : Fin count → Word) :
    (dotMixedPlan (prepareMixedDot weights) f).toField =
      ∑ i : Fin count, weights[i].toField * (algebraMap BF64 BF64.Ext3) (f i).toField := by
  unfold dotMixedPlan
  rw [mixedWideLoop_refines, MixedWide.reduce_zero]
  have z : (0 : WordExt3).toField = 0 := map_zero WordExt3.ringEquiv
  rw [z, zero_add]
  calc
    _ = ∑ q : Fin (((count+7)/8)*8), if h : q.val < count then
        weights[q.val].toField * (algebraMap BF64 BF64.Ext3) (f ⟨q.val,h⟩).toField else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      split
      · rename_i bound
        simp only [prepareMixedDot, Fin.getElem_fin, Vector.getElem_ofFn, MixedWeights8.product_eq]
        have address : q.val/8*8+q.val%8 = q.val := by omega
        simp only [Fin.divNat, Fin.modNat, address, bound, dite_true]
        rw [WordExt3.toField_mulScalar, Algebra.smul_def, mul_comm]
      · exact (congrArg WordExt3.toField MixedWide.reduce_zero).trans z
    _ = _ := by
      simpa only [Fin.getElem_fin] using sum_zero_padding count (((count+7)/8)*8) (by omega)
        (fun i : Fin count => weights[i].toField * (algebraMap BF64 BF64.Ext3) (f i).toField)

/-- Author PCS coefficients with unreduced extension dots. -/
def roundCoefficientsWide (rows width : Nat) (table weights : Vector WordExt3 (2*rows*width)) :
    Vector WordExt3 2 :=
  #v[dotExtWide (rows*width) (fun i => table[roundLow rows width i])
      (fun i => weights[roundLow rows width i]),
    dotExtWide (rows*width) (fun i => WordExt3.add table[roundLow rows width i] table[roundHigh rows width i])
      (fun i => WordExt3.add weights[roundLow rows width i] weights[roundHigh rows width i])]

/-- Deferred PCS messages preserve both full quadratic coefficients. -/
@[csimp] theorem roundCoefficientsDirect_code : @roundCoefficientsDirect = @roundCoefficientsWide := by
  funext rows width table weights
  apply Vector.ext
  intro i hi
  apply WordExt3.toField_injective
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl
  · change (sumExt _ _).toField = (dotExtWide _ _ _).toField
    simp only [sumExt_toField, dotExtWide_refines, roundProduct_eq, WordExt3.toField_mul]
  · change (sumExt _ _).toField = (dotExtWide _ _ _).toField
    simp only [sumExt_toField, dotExtWide_refines, roundProduct_eq, WordExt3.toField_mul]

/-- Author both message coefficients in one traversal with twelve unreduced scalar words. -/
@[specialize] def roundPairLoop (count : Nat) (f0 f1 w0 w1 : Fin count → WordExt3)
    (left : Nat) (bound : left ≤ count)
    (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : UInt64) : Vector WordExt3 2 :=
  match left with
  | 0 => #v[(⟨⟨a0,a1⟩,⟨a2,a3⟩,⟨a4,a5⟩⟩ : MixedWide).reduce,
      (⟨⟨b0,b1⟩,⟨b2,b3⟩,⟨b4,b5⟩⟩ : MixedWide).reduce]
  | left+1 =>
    let i : Fin count := ⟨left,by omega⟩
    let x0 := f0 i
    let x1 := f1 i
    let y0 := w0 i
    let y1 := w1 i
    let u := MixedWide.mul x0 y0
    let v := MixedWide.mul (WordExt3.add x0 x1) (WordExt3.add y0 y1)
    roundPairLoop count f0 f1 w0 w1 left (by omega)
      (a0 ^^^ u.c0.lo) (a1 ^^^ u.c0.hi) (a2 ^^^ u.c1.lo) (a3 ^^^ u.c1.hi)
      (a4 ^^^ u.c2.lo) (a5 ^^^ u.c2.hi)
      (b0 ^^^ v.c0.lo) (b1 ^^^ v.c0.hi) (b2 ^^^ v.c1.lo) (b3 ^^^ v.c1.hi)
      (b4 ^^^ v.c2.lo) (b5 ^^^ v.c2.hi)
termination_by structural left

/-- The fused message coordinate 0 retains its exact visited finite sum. -/
theorem roundPairLoop_message0 (count : Nat) (f0 f1 w0 w1 : Fin count → WordExt3)
    (left : Nat) (bound : left ≤ count)
    (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : UInt64) :
    (roundPairLoop count f0 f1 w0 w1 left bound a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5)[0].toField =
      (⟨⟨a0,a1⟩,⟨a2,a3⟩,⟨a4,a5⟩⟩ : MixedWide).reduce.toField +
        ∑ i : Fin left, (f0 ⟨i.val,by omega⟩).toField * (w0 ⟨i.val,by omega⟩).toField := by
  induction left generalizing a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 with
  | zero => simp only [roundPairLoop, Fin.sum_univ_zero, add_zero]; rfl
  | succ left ih =>
    rw [roundPairLoop, ih, Fin.sum_univ_castSucc]
    change (MixedWide.add (⟨⟨a0,a1⟩,⟨a2,a3⟩,⟨a4,a5⟩⟩ : MixedWide) _).reduce.toField + _ = _
    rw [MixedWide.reduce_add, WordExt3.toField_add, MixedWide.reduce_mul, WordExt3.toField_mul]
    simp only [Fin.val_castSucc, Fin.val_last]
    ac_rfl

/-- The fused message coordinate 1 retains its exact visited finite sum. -/
theorem roundPairLoop_message1 (count : Nat) (f0 f1 w0 w1 : Fin count → WordExt3)
    (left : Nat) (bound : left ≤ count)
    (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : UInt64) :
    (roundPairLoop count f0 f1 w0 w1 left bound a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5)[1].toField =
      (⟨⟨b0,b1⟩,⟨b2,b3⟩,⟨b4,b5⟩⟩ : MixedWide).reduce.toField +
        ∑ i : Fin left, ((f0 ⟨i.val,by omega⟩).toField + (f1 ⟨i.val,by omega⟩).toField) *
        ((w0 ⟨i.val,by omega⟩).toField + (w1 ⟨i.val,by omega⟩).toField) := by
  induction left generalizing a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 with
  | zero => simp only [roundPairLoop, Fin.sum_univ_zero, add_zero]; rfl
  | succ left ih =>
    rw [roundPairLoop, ih, Fin.sum_univ_castSucc]
    change (MixedWide.add (⟨⟨b0,b1⟩,⟨b2,b3⟩,⟨b4,b5⟩⟩ : MixedWide) _).reduce.toField + _ = _
    rw [MixedWide.reduce_add, WordExt3.toField_add, MixedWide.reduce_mul, WordExt3.toField_mul]
    simp only [WordExt3.toField_add, Fin.val_castSucc, Fin.val_last]
    ac_rfl

/-- Fused messages consume indexed tables directly without materializing input copies. -/
@[inline] def roundCoefficientsWith (rows width : Nat)
    (table weights : Fin (2*rows*width) → WordExt3) : Vector WordExt3 2 :=
  roundPairLoop (rows*width) (fun i => table (roundLow rows width i))
    (fun i => table (roundHigh rows width i)) (fun i => weights (roundLow rows width i))
    (fun i => weights (roundHigh rows width i)) (rows*width) (Nat.le_refl _)
    0 0 0 0 0 0 0 0 0 0 0 0

/-- Direct indexed messages equal the complete two-pass deferred message. -/
theorem roundCoefficientsWith_eq (rows width : Nat)
    (table weights : Fin (2*rows*width) → WordExt3) :
    roundCoefficientsWith rows width table weights =
      roundCoefficientsWide rows width (Vector.ofFn table) (Vector.ofFn weights) := by
  apply Vector.ext
  intro i hi
  apply WordExt3.toField_injective
  have cases : i = 0 ∨ i = 1 := by omega
  have z : (0 : WordExt3).toField = 0 := map_zero WordExt3.ringEquiv
  rcases cases with rfl | rfl
  · rw [roundCoefficientsWith, roundPairLoop_message0]
    change _ = (dotExtWide (rows*width) (fun i => (Vector.ofFn table)[roundLow rows width i])
      (fun i => (Vector.ofFn weights)[roundLow rows width i])).toField
    simp only [MixedWide.reduce_zero, z, zero_add, dotExtWide_refines, Fin.getElem_fin, Vector.getElem_ofFn]
  · rw [roundCoefficientsWith, roundPairLoop_message1]
    change _ = (dotExtWide (rows*width)
      (fun i => WordExt3.add ((Vector.ofFn table)[roundLow rows width i]) ((Vector.ofFn table)[roundHigh rows width i]))
      (fun i => WordExt3.add ((Vector.ofFn weights)[roundLow rows width i]) ((Vector.ofFn weights)[roundHigh rows width i]))).toField
    simp only [MixedWide.reduce_zero, z, zero_add, dotExtWide_refines, Fin.getElem_fin, Vector.getElem_ofFn, WordExt3.toField_add]

end CompStark.Pcs
