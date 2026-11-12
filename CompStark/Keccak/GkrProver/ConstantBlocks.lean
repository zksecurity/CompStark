/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Keccak.GkrProver.TensorRows
/-! Checked constant pack blocks have no mixed ternary contributions. -/
@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option compiler.maxRecInline 0
attribute [local irreducible] earlyValues prepareWeightMaps prepareRmfeProducts tensorBlock mixedEmbeddings ternaryPlan
/-- A constant Boolean factor has zero derivatives at every infinity coordinate. -/
theorem ternaryLift_constant (n : Nat) (c : W) (q : Nat) :
    ternaryLift n (fun _ => c) q = if ternaryIsFinite n q then c else 0 := by
  induction n generalizing c q with
  | zero => rfl
  | succ n ih =>
    rw [ternaryLift, ternaryIsFinite]
    by_cases hz : q%3 = 0
    · simp only [hz, Nat.reduceEqDiff, ite_true, ne_eq, not_false_eq_true,
        decide_true, Bool.true_and]
      exact ih c (q/3)
    · rw [ite_eq_right hz]
      by_cases ho : q%3 = 1
      · simp only [ho, Nat.reduceEqDiff, ite_true, ne_eq, not_false_eq_true,
          decide_true, Bool.true_and]
        exact ih c (q/3)
      · have hi : q%3 = 2 := by omega
        simp only [hi, Nat.reduceEqDiff, ite_false, ne_eq, not_true_eq_false,
          decide_false, Bool.false_and, Bool.false_eq_true, CharTwo.add_self_eq_zero]
        exact ternaryLift_zero_table n (q/3)
/-- All sixteen pack vertices of every position in a block coincide. -/
def UniformBlock (state : Array UInt64) (groups base : Nat) : Prop :=
  ∀ j : Fin 1600, ∀ b : Fin 16,
    tensorVertices state groups base j b = tensorVertices state groups base j 0
/-- Constant-block detection is executable on finite position and pack coordinates. -/
instance (state : Array UInt64) (groups base : Nat) : Decidable (UniformBlock state groups base) :=
  Fintype.decidableForallFintype (p := fun j : Fin 1600 => ∀ b : Fin 16,
    tensorVertices state groups base j b = tensorVertices state groups base j 0)
/-- A lifted RMFE factor of a constant block vanishes at every nonbinary assignment. -/
theorem uniform_factor (state : Array UInt64) (groups base : Nat) (h : UniformBlock state groups base)
    (s : W) (j : Fin 1600) (q : Fin 81) (hq : (ternaryPlan[q.val]!).2 ≠ 81) :
    ternaryLift 4 (tensorFactor s state groups base j) q.val = 0 := by
  have hf : tensorFactor s state groups base j =
      fun _ => rmfeValue s (tensorVertices state groups base j 0) := by
    funext i
    unfold tensorFactor
    rw [h]
  rw [hf, ternaryLift_constant]
  have hq' : ternaryIsFinite 4 q.val ≠ true := fun hh => hq ((ternaryPlan_finite q).mpr hh)
  exact ite_eq_right hq'
/-- Every nonbinary weighted tensor position of a constant block is zero. -/
theorem uniform_product (state : Array UInt64) (groups base : Nat) (h : UniformBlock state groups base)
    (weights : Array W) (s : W) (j : Fin 1600) (q : Fin 81) (hq : (ternaryPlan[q.val]!).2 ≠ 81) :
    tensorColumnProduct weights s state groups base j q = 0 := by
  unfold tensorColumnProduct
  rw [uniform_factor state groups base h s _ q hq, mul_zero, zero_mul]
/-- Native source-word offsets shared by all positions of a pack block. -/
def uniformOffsets (base : Nat) : Array USize :=
  Array.ofFn fun b : Fin 16 => ((base+b.val)/4).toUSize
/-- Native within-word shifts shared by every position of a pack block. -/
def uniformShifts (base : Nat) : Array UInt64 :=
  Array.ofFn fun b : Fin 16 => (16*((base+b.val)%4)).toUInt64
/-- Read a pack vertex without constructing an extension-field carrier. -/
@[inline] def uniformVertex (state : Array UInt64) (groups : USize)
    (offsets : Array USize) (shifts : Array UInt64) (j : USize) (b : Nat) : UInt64 :=
  (state[(j*groups+offsets[b]!).toNat]! >>> shifts[b]!) &&& 65535
/-- Scalar vertex reads are the exact constant coordinate of a tensor vertex. -/
theorem uniformVertex_eq (state : Array UInt64) (groups base : Nat) (j : Fin 1600) (b : Fin 16) :
    lane (uniformVertex state groups.toUSize (uniformOffsets base) (uniformShifts base) j.val.toUSize b.val) =
      tensorVertices state groups base j b := by
  have ho : (uniformOffsets base)[b.val]! = ((base+b.val)/4).toUSize := by
    unfold uniformOffsets
    rw [getElem!_pos _ _ (by rw [Array.size_ofFn]; exact b.isLt), Array.getElem_ofFn]
  have hs : (uniformShifts base)[b.val]! = (16*((base+b.val)%4)).toUInt64 := by
    unfold uniformShifts
    rw [getElem!_pos _ _ (by rw [Array.size_ofFn]; exact b.isLt), Array.getElem_ofFn]
  simp only [uniformVertex, ho, hs, tensorVertices]
/-- Scalar lane equality is machine-word equality. -/
theorem lane_eq_iff (a b : UInt64) : lane a = lane b ↔ a = b := by
  constructor
  · exact fun h => congrArg (fun x : W => x.c0.val) h
  · exact congrArg lane
/-- Check a row's vertices with scalar loop state and precomputed source offsets. -/
def uniformRowCheck (state : Array UInt64) (groups : USize) (offsets : Array USize)
    (shifts : Array UInt64) (j : USize) (expected : UInt64) : Nat → Bool
  | 0 => true
  | n+1 => (uniformVertex state groups offsets shifts j n == expected) &&
      uniformRowCheck state groups offsets shifts j expected n
/-- The scalar row check covers every requested pack vertex. -/
theorem uniformRowCheck_iff (state : Array UInt64) (groups base : Nat) (j : Fin 1600)
    (n : Nat) (hn : n ≤ 16) :
    uniformRowCheck state groups.toUSize (uniformOffsets base) (uniformShifts base) j.val.toUSize
      (uniformVertex state groups.toUSize (uniformOffsets base) (uniformShifts base) j.val.toUSize 0) n = true ↔
      ∀ b : Fin 16, b.val < n → tensorVertices state groups base j b = tensorVertices state groups base j 0 := by
  induction n with
  | zero => simp only [uniformRowCheck, Nat.not_lt_zero, IsEmpty.forall_iff, implies_true]
  | succ n ih =>
    have h0 := uniformVertex_eq state groups base j (0 : Fin 16)
    change lane (uniformVertex state groups.toUSize (uniformOffsets base) (uniformShifts base) j.val.toUSize 0) = _ at h0
    rw [uniformRowCheck, Bool.and_eq_true, beq_iff_eq, ← lane_eq_iff,
      uniformVertex_eq state groups base j ⟨n,by omega⟩, h0, ih (by omega)]
    constructor
    · rintro ⟨h,hs⟩ b hb
      by_cases he : b.val = n
      · have eb : b = ⟨n,by omega⟩ := Fin.ext he
        simpa only [eb] using h
      · exact hs b (by omega)
    · intro h
      exact ⟨h ⟨n,by omega⟩ (by change n < n+1; omega),fun b hb => h b (by omega)⟩
/-- Check all source positions without callbacks or extension constructors. -/
def uniformBlockCheckLoop (state : Array UInt64) (groups : USize) (offsets : Array USize)
    (shifts : Array UInt64) : Nat → Bool
  | 0 => true
  | n+1 => uniformRowCheck state groups offsets shifts n.toUSize
      (uniformVertex state groups offsets shifts n.toUSize 0) 16 &&
      uniformBlockCheckLoop state groups offsets shifts n
/-- The complete scalar check covers exactly the requested source positions. -/
theorem uniformBlockCheckLoop_iff (state : Array UInt64) (groups base n : Nat) (hn : n ≤ 1600) :
    uniformBlockCheckLoop state groups.toUSize (uniformOffsets base) (uniformShifts base) n = true ↔
      ∀ j : Fin 1600, j.val < n → ∀ b : Fin 16,
        tensorVertices state groups base j b = tensorVertices state groups base j 0 := by
  induction n with
  | zero => simp only [uniformBlockCheckLoop, Nat.not_lt_zero, IsEmpty.forall_iff, implies_true]
  | succ n ih =>
    rw [uniformBlockCheckLoop, Bool.and_eq_true,
      uniformRowCheck_iff state groups base ⟨n,by omega⟩ 16 (by omega), ih (by omega)]
    constructor
    · rintro ⟨h,hs⟩ j hj b
      by_cases he : j.val = n
      · have ej : j = ⟨n,by omega⟩ := Fin.ext he
        simpa only [ej] using h b b.isLt
      · exact hs j (by omega) b
    · intro h
      exact ⟨fun b _ => h ⟨n,by omega⟩ (by change n < n+1; omega) b,fun j hj => h j (by omega)⟩
/-- Decide pack-block uniformity from scalar machine-word comparisons. -/
def uniformBlockDec (state : Array UInt64) (groups base : Nat) : Decidable (UniformBlock state groups base) :=
  let check := uniformBlockCheckLoop state groups.toUSize (uniformOffsets base) (uniformShifts base) 1600
  have he : check = true ↔ UniformBlock state groups base := by
    rw [uniformBlockCheckLoop_iff _ _ _ _ (by omega)]
    simp only [Fin.isLt, forall_const, UniformBlock]
  if h : check = true then isTrue (he.mp h) else isFalse (fun hp => h (he.mpr hp))
/-- Scalar block checks implement the same kernel-checked decision procedure. -/
@[csimp] theorem uniformBlock_dec_code : instDecidableUniformBlock = uniformBlockDec := by
  funext state groups base
  exact Subsingleton.elim _ _
/-- All retained pack blocks of the two selected source segments are constant. -/
def UniformLayer (w : SlicedWitness) (d : Nat) : Prop :=
  ∀ m : Fin 2, ∀ b : Fin (2^(w.nLog-4)/16),
    UniformBlock w.layers[12*(m.val+1)-d]! (2^w.nLog/64) (16*b.val)
/-- Layer uniformity checks only the source pack vertices. -/
instance (w : SlicedWitness) (d : Nat) : Decidable (UniformLayer w d) :=
  Fintype.decidableForallFintype (p := fun m : Fin 2 => ∀ b : Fin (2^(w.nLog-4)/16),
    UniformBlock w.layers[12*(m.val+1)-d]! (2^w.nLog/64) (16*b.val))
/-- Bounded scalar reads determine a complete tensor-value array. -/
theorem arrayValues_ext (a b : Array W) (ha : a.size = 81) (hb : b.size = 81)
    (same : ∀ q : Fin 81, a[q.val]! = b[q.val]!) : a = b := by
  apply Array.ext (ha.trans hb.symm)
  intro i hi hj
  have h := same ⟨i,by omega⟩
  exact (getElem!_pos a i hi).symm.trans (h.trans (getElem!_pos b i hj))
/-- A constant layer retains the finite endpoints and has no mixed contributions. -/
theorem early_uniform (w : SlicedWitness) (d : Nat) (h : UniformLayer w d) (claim : Claim) (s : W)
    (binary : Array W) :
    earlyValues w d claim (prepareWeightMaps claim.weights (CompStark.Sumcheck.prepare s))
      prepareRmfeProducts binary = initialTensorValues binary := by
  apply arrayValues_ext _ _
    (earlyValues_blocks_get w d claim _ _ binary ⟨0,by decide⟩).1 (Array.size_ofFn ..)
  intro q
  have hi : (initialTensorValues binary)[q.val]! =
      if (ternaryPlan[q.val]!).2 = 81 then binary[(ternaryPlan[q.val]!).1]! else 0 := by
    unfold initialTensorValues
    rw [getElem!_pos _ _ (by rw [Array.size_ofFn]; exact q.isLt),Array.getElem_ofFn]
    generalize ternaryPlan[q.val]! = plan
    rcases plan with ⟨b,hi⟩
    rfl
  rw [earlyValues_get w d claim s binary q]
  change _ = (initialTensorValues binary)[q.val]!
  rw [hi]
  split
  · rfl
  · rename_i hf
    apply Finset.sum_eq_zero
    intro m hm
    apply Finset.sum_eq_zero
    intro b hb
    rw [show (∑ j : Fin 1600, tensorColumnProduct claim.weights s w.layers[12*(m+1)-d]!
      (2^w.nLog/64) (16*b) j q) = 0 from by
        apply Finset.sum_eq_zero
        intro j _
        exact uniform_product _ _ _ (h ⟨m,Finset.mem_range.mp hm⟩ ⟨b,Finset.mem_range.mp hb⟩) _ _ j q hf,
      mul_zero]

end CompStark.Keccak.GkrProver
