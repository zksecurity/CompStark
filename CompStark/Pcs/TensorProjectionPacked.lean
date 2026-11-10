/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.MixedDot
public import CompStark.Pcs.ByteFoldRows
public import CompStark.Pcs.TensorProjectionActive

/-! Retained packed point weights and shared binary-coordinate projection tables. -/
@[expose] public section
namespace CompStark.Pcs
open BF64
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
attribute [local irreducible] Word.toField WordExt3.toField

/-- A compact point interval with its retained eight-wide mixed weights. -/
structure PackedWindowProjection (cols : Nat) where
  /-- Exact occupied interval. -/
  window : BasisWindow cols
  /-- Three packed polynomial coordinates of every local weight. -/
  weights : MixedDotPlan window.count

/-- Pack a point's mixed weights once for all physical witness lanes. -/
def packedWindowProjector {cols : Nat} (w : BasisWindow cols) : PackedWindowProjection cols :=
  ⟨w, prepareMixedDot w.values⟩

/-- Project one occupied interval with deferred polynomial reduction. -/
@[inline] def PackedWindowProjection.project {cols : Nat} (p : PackedWindowProjection cols)
    (f : Fin cols → Word) : WordExt3 :=
  dotMixedPlan p.weights fun i =>
    f ⟨p.window.start+i.val, by have := p.window.fits; have := i.isLt; omega⟩

/-- Retained packed point weights give the complete occupied mixed dot. -/
theorem packedWindowProjector_eq {cols : Nat} (w : BasisWindow cols) (f : Fin cols → Word) :
    (packedWindowProjector w).project f = w.projectAt f := by
  apply WordExt3.toField_injective
  unfold PackedWindowProjection.project packedWindowProjector BasisWindow.projectAt
  rw [dotMixedPlan_refines, sumWords_refines]
  simp only [List.map_ofFn, Function.comp_apply, WordExt3.toField_mulScalar,
    Algebra.smul_def, List.sum_ofFn, Fin.getElem_fin]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Deferred base-times-extension products retain the exact mixed field product. -/
theorem mixedScalar_reduce (x : Word) (w : WordExt3) :
    (⟨InductionWide.mul x w.c0, InductionWide.mul x w.c1,
      InductionWide.mul x w.c2⟩ : MixedWide).reduce.toField =
      w.toField * (algebraMap BF64 BF64.Ext3) x.toField := by
  have same : (⟨InductionWide.mul x w.c0, InductionWide.mul x w.c1,
      InductionWide.mul x w.c2⟩ : MixedWide).reduce = WordExt3.mulScalar w x := by
    unfold MixedWide.reduce WordExt3.mulScalar
    congr 1 <;> apply Word.toField_injective <;>
      simp only [InductionWide.mul_eq, Word.toField_mulMasked] <;> exact mul_comm _ _
  rw [same, WordExt3.toField_mulScalar, Algebra.smul_def, mul_comm]

/-- Machine-indexed mixed products with six unreduced scalar accumulators. -/
def windowDotLoop {size count : Nat} (source : Vector Word size)
    (weights : Vector WordExt3 count) (offset : USize)
    (fits : offset.toNat+count ≤ size) (native : size < USize.size)
    (left : Nat) (bound : left ≤ count) (a0 b0 a1 b1 a2 b2 : UInt64) : WordExt3 :=
  match left with
  | 0 => (⟨⟨a0,b0⟩,⟨a1,b1⟩,⟨a2,b2⟩⟩ : MixedWide).reduce
  | left+1 =>
    have ilt : left < USize.size := by omega
    have it : left.toUSize.toNat = left := USize.toNat_ofNat_of_lt' ilt
    let i := left.toUSize
    let k := offset+i
    have kt : k.toNat = offset.toNat+left := by
      rw [USize.toNat_add]
      change (offset.toNat+left.toUSize.toNat)%USize.size = _
      rw [it, Nat.mod_eq_of_lt (by omega : offset.toNat+left < USize.size)]
    let x := source.uget k (by rw [kt]; omega)
    let w := weights.uget i (by rw [it]; omega)
    let p : MixedWide := ⟨InductionWide.mul x w.c0,
      InductionWide.mul x w.c1, InductionWide.mul x w.c2⟩
    windowDotLoop source weights offset fits native left (by omega)
      (a0 ^^^ p.c0.lo) (b0 ^^^ p.c0.hi) (a1 ^^^ p.c1.lo) (b1 ^^^ p.c1.hi)
      (a2 ^^^ p.c2.lo) (b2 ^^^ p.c2.hi)
termination_by structural left

/-- Scalar window accumulation retains exactly the visited mixed products. -/
theorem windowDotLoop_refines {size count : Nat} (source : Vector Word size)
    (weights : Vector WordExt3 count) (offset : USize)
    (fits : offset.toNat+count ≤ size) (native : size < USize.size)
    (left : Nat) (bound : left ≤ count) (a0 b0 a1 b1 a2 b2 : UInt64) :
    (windowDotLoop source weights offset fits native left bound a0 b0 a1 b1 a2 b2).toField =
      (⟨⟨a0,b0⟩,⟨a1,b1⟩,⟨a2,b2⟩⟩ : MixedWide).reduce.toField +
      ∑ i : Fin left, weights[i.val].toField * (algebraMap BF64 BF64.Ext3)
        (source[offset.toNat+i.val]'(by have := i.isLt; omega)).toField := by
  induction left generalizing a0 b0 a1 b1 a2 b2 with
  | zero => rw [windowDotLoop]; simp only [Fin.sum_univ_zero, add_zero]
  | succ left ih =>
    rw [windowDotLoop, ih, Fin.sum_univ_castSucc]
    change (MixedWide.add (⟨⟨a0,b0⟩,⟨a1,b1⟩,⟨a2,b2⟩⟩ : MixedWide) _).reduce.toField + _ = _
    rw [MixedWide.reduce_add, WordExt3.toField_add]
    have it : left.toUSize.toNat = left := USize.toNat_ofNat_of_lt' (by omega)
    have kt : (offset+left.toUSize).toNat = offset.toNat+left := by
      rw [USize.toNat_add]
      change (offset.toNat+left.toUSize.toNat)%USize.size = _
      rw [it, Nat.mod_eq_of_lt (by omega : offset.toNat+left < USize.size)]
    simp only [Vector.uget, Array.uget, it, kt, Vector.getElem_toArray, mixedScalar_reduce]
    simp only [Fin.val_castSucc, Fin.val_last]
    ac_rfl

/-- Contiguous mixed dots use machine loads and reduce once at the output boundary. -/
def windowDot {size count : Nat} (source : Vector Word size) (offset : Nat)
    (weights : Vector WordExt3 count) (fits : offset+count ≤ size) : WordExt3 :=
  if native : size < USize.size then
    windowDotLoop source weights offset.toUSize (by
      rw [USize.toNat_ofNat_of_lt' (by omega : offset < USize.size)]; exact fits)
      native count (Nat.le_refl _) 0 0 0 0 0 0
  else dotMixedPlan (prepareMixedDot weights) fun i => source[offset+i.val]'(by have := i.isLt; omega)

/-- Contiguous scalar dots preserve the full occupied-window contraction. -/
theorem windowDot_refines {size count : Nat} (source : Vector Word size) (offset : Nat)
    (weights : Vector WordExt3 count) (fits : offset+count ≤ size) :
    (windowDot source offset weights fits).toField =
      ∑ i : Fin count, weights[i.val].toField * (algebraMap BF64 BF64.Ext3)
        (source[offset+i.val]'(by have := i.isLt; omega)).toField := by
  unfold windowDot
  split
  · rename_i native
    rw [windowDotLoop_refines, MixedWide.reduce_zero]
    simp only [USize.toNat_ofNat_of_lt' (by omega : offset < USize.size)]
    have z : (0 : WordExt3).toField = 0 := map_zero WordExt3.ringEquiv
    rw [z, zero_add]
  · exact dotMixedPlan_refines _ _

attribute [local irreducible] tensorPatternKeys tensorPatternActive windowProjector packedWindowProjector

/-- Cache packed point projections only on each retained low pattern's occupied high blocks. -/
def tensorWindowMatrixPacked (lanes cols low high count : Nat) (shape : cols = high*low)
    (f : Vector Word (lanes*cols)) (windows : Vector (BasisWindow low) count)
    (gamma : Vector (Vector WordExt3 high) count) : Vector (Vector WordExt3 count) lanes :=
  let unique := windows.toList.dedup
  let patterns := unique.length
  let plans := unique.toArray.map packedWindowProjector
  let keys := tensorPatternKeys windows
  let active : Vector (Vector Bool high) patterns := Vector.ofFn fun p =>
    Vector.ofFn fun h => tensorPatternActive keys gamma p h
  let cache : Vector (Vector (Vector WordExt3 high) patterns) lanes := Vector.ofFn fun lane =>
    Vector.ofFn fun p => Vector.ofFn fun h =>
      if active[p.val][h.val] then
        (plans[p.val]'(by simpa only [plans, Array.size_map, List.size_toArray] using p.isLt)).project
          (fun x => f[basisAddress lane ((basisAddress h x).cast shape.symm)])
      else 0
  Vector.ofFn fun lane => Vector.ofFn fun t => sumExt high fun h =>
    roundProduct gamma[t.val][h.val] cache[lane.val][keys[t.val].val][h.val]

/-- Packed low-pattern dots preserve the complete active-block matrix. -/
@[csimp] theorem tensorWindowMatrixActive_code : @tensorWindowMatrixActive = @tensorWindowMatrixPacked := by
  funext lanes cols low high count shape f windows gamma
  apply Vector.ext
  intro lane hl
  apply Vector.ext
  intro term ht
  simp only [tensorWindowMatrixActive, tensorWindowMatrixPacked, Vector.getElem_ofFn,
    Fin.getElem_fin]
  apply congrArg (sumExt high)
  funext h
  simp only [Array.getElem_map, List.getElem_toArray]
  congr 1
  split <;> simp only [windowProjector_eq, packedWindowProjector_eq]

/-- Project one physical low block with a contiguous scalar dot. -/
def projectWindowRow (lanes cols low high : Nat) (shape : cols = high*low)
    (source : Vector Word (lanes*cols)) (lane : Fin lanes) (h : Fin high) (w : BasisWindow low) : WordExt3 :=
  windowDot source (lane.val*cols+h.val*low+w.start) w.values (by
    have hb := Nat.mul_le_mul_right low (Nat.succ_le_of_lt h.isLt)
    have hl := Nat.mul_le_mul_right cols (Nat.succ_le_of_lt lane.isLt)
    rw [Nat.succ_mul, ← shape] at hb
    rw [Nat.succ_mul] at hl
    have := w.fits
    omega)

/-- Direct row projection retains the complete compact-window mixed sum. -/
theorem projectWindowRow_eq (lanes cols low high : Nat) (shape : cols = high*low)
    (source : Vector Word (lanes*cols)) (lane : Fin lanes) (h : Fin high) (w : BasisWindow low) :
    projectWindowRow lanes cols low high shape source lane h w =
      w.projectAt (fun x => source[basisAddress lane ((basisAddress h x).cast shape.symm)]) := by
  apply WordExt3.toField_injective
  simp only [projectWindowRow, windowDot_refines, BasisWindow.projectAt, sumWords_refines,
    List.map_ofFn, Function.comp_apply, List.sum_ofFn, WordExt3.toField_mulScalar, Algebra.smul_def,
    basisAddress, Fin.val_cast, Nat.add_assoc]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Project occupied low patterns through direct scalar window dots. -/
def tensorWindowMatrixScalar (lanes cols low high count : Nat) (shape : cols = high*low)
    (f : Vector Word (lanes*cols)) (windows : Vector (BasisWindow low) count)
    (gamma : Vector (Vector WordExt3 high) count) : Vector (Vector WordExt3 count) lanes :=
  let unique := windows.toList.dedup
  let patterns := unique.length
  let plans := unique.toArray
  let keys := tensorPatternKeys windows
  let active : Vector (Vector Bool high) patterns := Vector.ofFn fun p =>
    Vector.ofFn fun h => tensorPatternActive keys gamma p h
  let cache : Vector (Vector (Vector WordExt3 high) patterns) lanes := Vector.ofFn fun lane =>
    Vector.ofFn fun p => Vector.ofFn fun h =>
      if active[p.val][h.val] then
        let w := plans[p.val]'(by simpa only [plans, List.size_toArray] using p.isLt)
        projectWindowRow lanes cols low high shape f lane h w
      else 0
  Vector.ofFn fun lane => Vector.ofFn fun t => dotExtWide high (fun h => gamma[t.val][h.val]) (fun h => cache[lane.val][keys[t.val].val][h.val])

/-- Direct machine-indexed window dots preserve the packed projection matrix. -/
@[csimp] theorem tensorWindowMatrixPacked_code : @tensorWindowMatrixPacked = @tensorWindowMatrixScalar := by
  funext lanes cols low high count shape f windows gamma
  apply Vector.ext
  intro lane hl
  apply Vector.ext
  intro term ht
  apply WordExt3.toField_injective
  simp only [tensorWindowMatrixPacked, tensorWindowMatrixScalar, Vector.getElem_ofFn,
    Fin.getElem_fin, sumExt_toField, dotExtWide_refines, roundProduct_eq, WordExt3.toField_mul]
  apply Finset.sum_congr rfl
  intro h _
  apply congrArg (HMul.hMul _)
  simp only [Array.getElem_map, List.getElem_toArray]
  split <;> simp only [packedWindowProjector_eq, projectWindowRow_eq, Fin.getElem_fin]

/-- Project packed point patterns and all shared binary ring coordinates. -/
def projectTensorPointBinaryPacked (lanes cols low high count : Nat) (shape : cols = high*low)
    (f : Vector Word (lanes*cols)) (windows : Vector (BasisWindow low) count)
    (gamma : Vector (Vector WordExt3 high) count) (ring : Vector WordExt3 cols) :
    Vector WordExt3 (lanes*(count+192)) :=
  let points := tensorWindowMatrixPacked lanes cols low high count shape f windows gamma
  let ringPlan := prepareByteFold ring
  let rings : Vector (Vector Word 192) lanes := Vector.ofFn fun lane =>
    transposeExt (foldBytePlan ringPlan (Vector.ofFn fun x => f[basisAddress lane x]))
  Vector.ofFn fun i => Fin.addCases
    (fun term : Fin count => points[i.divNat][term])
    (fun bit : Fin 192 => ⟨rings[i.divNat][bit], ⟨0⟩, ⟨0⟩⟩) i.modNat

/-- The joint packed-point and binary projection preserves every retained term. -/
@[csimp] theorem projectTensorPointBinaryActive_code :
    @projectTensorPointBinaryActive = @projectTensorPointBinaryPacked := by
  funext lanes cols low high count shape f windows gamma ring
  simp only [projectTensorPointBinaryActive, projectTensorPointBinaryPacked, ← tensorWindowMatrixActive_code]

end CompStark.Pcs
