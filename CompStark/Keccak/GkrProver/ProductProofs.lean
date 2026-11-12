/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.Refinement

/-! Polynomial semantics of the native product payload and its weighted bit buckets. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak BF64 BinaryField Polynomial
open scoped BigOperators

/-- One coefficient word of a native position weight. -/
def weightCoordinate (weights : Array W) (j : Nat) (c : Fin 3) : UInt64 :=
  if c.val = 0 then weights[j]!.c0.val
  else if c.val = 1 then weights[j]!.c1.val else weights[j]!.c2.val

/-- Writing a complete position weight changes exactly its three scalar coordinates. -/
theorem weightDigits_step (weights : Array W) (out : FixedWords 4800)
    (j i : Fin 1600) (c : Fin 3) :
    readWord
      (writeWord (writeWord (writeWord out (3*j.val) weights[j.val]!.c0.val)
        (3*j.val+1) weights[j.val]!.c1.val) (3*j.val+2) weights[j.val]!.c2.val)
      (3*i.val+c.val) =
        if j = i then weightCoordinate weights i.val c else readWord out (3*i.val+c.val) := by
  have hj := j.isLt
  have hi := i.isLt
  have hc := c.isLt
  rw [readWord_writeWord _ _ _ (by omega) (by omega),
    readWord_writeWord _ _ _ (by omega) (by omega),
    readWord_writeWord _ _ _ (by omega) (by omega)]
  by_cases he : j = i
  · subst j
    fin_cases c
    · change (if 3*i.val+2 = 3*i.val+0 then _ else
        if 3*i.val+1 = 3*i.val+0 then _ else _) = _
      rw [ite_eq_right (by omega),ite_eq_right (by omega)]
      simp only [Nat.add_zero,ite_true,weightCoordinate]
    · change (if 3*i.val+2 = 3*i.val+1 then _ else _) = _
      rw [ite_eq_right (by omega)]
      simp only [ite_true,weightCoordinate,Nat.reduceEqDiff,ite_false]
    · simp only [ite_true,weightCoordinate,Nat.reduceEqDiff,ite_false]
  · have hne : j.val ≠ i.val := fun h => he (Fin.ext h)
    rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right he]

/-- Materializing position weights preserves every scalar word consumed by the buckets. -/
theorem weightDigits_get (weights : Array W) (i : Fin 1600) (c : Fin 3) :
    readWord (weightDigits weights) (3*i.val+c.val) = weightCoordinate weights i.val c := by
  simp only [weightDigits,Std.Legacy.Range.forIn_eq_forIn_range',List.forIn_pure_yield_eq_foldl,
    pure_bind,Id.run_pure]
  let step (out : FixedWords 4800) (j : Nat) :=
    writeWord (writeWord (writeWord out (3*j) weights[j]!.c0.val)
      (3*j+1) weights[j]!.c1.val) (3*j+2) weights[j]!.c2.val
  have hf (xs : List Nat) (hx : ∀ j ∈ xs, j < 1600) (out : FixedWords 4800) :
      readWord (xs.foldl step out) (3*i.val+c.val) =
        if i.val ∈ xs then weightCoordinate weights i.val c else readWord out (3*i.val+c.val) := by
    induction xs generalizing out with
    | nil => simp only [List.foldl_nil,List.not_mem_nil,ite_false]
    | cons j xs ih =>
      rw [List.foldl_cons,ih (fun k hk => hx k (List.mem_cons_of_mem j hk))]
      by_cases ht : i.val ∈ xs
      · rw [ite_eq_left ht,ite_eq_left (List.mem_cons_of_mem j ht)]
      · rw [ite_eq_right ht]
        have hj : j < 1600 := hx j (List.mem_cons_self)
        change readWord (writeWord (writeWord (writeWord out (3*j) weights[j]!.c0.val)
          (3*j+1) weights[j]!.c1.val) (3*j+2) weights[j]!.c2.val) _ = _
        rw [weightDigits_step weights out ⟨j,hj⟩ i c]
        by_cases he : j = i.val
        · subst j
          rw [ite_eq_left rfl,ite_eq_left List.mem_cons_self]
        · rw [ite_eq_right (by intro h; exact he (congrArg Fin.val h)),
            ite_eq_right (by simp only [List.mem_cons,ht,or_false]; exact Ne.symm he)]
  change readWord ((List.range' 0 1600).foldl step _) (3*i.val+c.val) = _
  have hbound : ∀ j ∈ List.range' 0 1600, j < 1600 := by
    intro j hj
    obtain ⟨k,hk,he⟩ := List.mem_range'.mp hj
    omega
  rw [hf _ hbound,ite_eq_left (List.mem_range'.mpr ⟨i.val,i.isLt,by omega⟩)]

/-- The three extension coordinates stored in one polynomial-byte bucket. -/
def bucketValue (buckets : FixedWords (6*256*3)) (j : Nat) : W :=
  ⟨⟨readWord buckets (3*j)⟩,⟨readWord buckets (3*j+1)⟩,⟨readWord buckets (3*j+2)⟩⟩

/-- XOR accumulation into one bucket adds its weight and preserves all other buckets. -/
theorem bucketValue_accumulate (buckets : FixedWords (6*256*3)) (j i : Fin (6*256))
    (w0 w1 w2 : UInt64) :
    bucketValue
      (writeWord (writeWord (writeWord buckets (3*j.val)
        (readWord buckets (3*j.val) ^^^ w0)) (3*j.val+1)
        (readWord buckets (3*j.val+1) ^^^ w1)) (3*j.val+2)
        (readWord buckets (3*j.val+2) ^^^ w2)) i.val =
      bucketValue buckets i.val + if j = i then ⟨⟨w0⟩,⟨w1⟩,⟨w2⟩⟩ else 0 := by
  have hj := j.isLt
  have hi := i.isLt
  have hc (c : Fin 3) :
      readWord
        (writeWord (writeWord (writeWord buckets (3*j.val)
          (readWord buckets (3*j.val) ^^^ w0)) (3*j.val+1)
          (readWord buckets (3*j.val+1) ^^^ w1)) (3*j.val+2)
          (readWord buckets (3*j.val+2) ^^^ w2)) (3*i.val+c.val) =
        if j = i then readWord buckets (3*i.val+c.val) ^^^
          (if c.val = 0 then w0 else if c.val = 1 then w1 else w2)
        else readWord buckets (3*i.val+c.val) := by
    have hcl := c.isLt
    rw [readWord_writeWord _ _ _ (by omega) (by omega),
      readWord_writeWord _ _ _ (by omega) (by omega),
      readWord_writeWord _ _ _ (by omega) (by omega)]
    by_cases he : j = i
    · subst j
      fin_cases c
      · simp only [Nat.add_zero,ite_true]
        rw [ite_eq_right (by omega),ite_eq_right (by omega)]
      · simp only [ite_true,Nat.reduceEqDiff,ite_false]
        rw [ite_eq_right (by omega)]
      · simp only [ite_true,Nat.reduceEqDiff,ite_false]
    · have hne : j.val ≠ i.val := fun h => he (Fin.ext h)
      rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right he]
  unfold bucketValue
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  simp only [Fin.val_zero,Nat.add_zero] at h0
  simp only [Fin.val_one] at h1
  simp only [show (2 : Fin 3).val = 2 from rfl] at h2
  rw [h0,h1,h2]
  by_cases he : j = i
  · simp only [he,ite_true]
    rfl
  · simp only [he,ite_false,add_zero]

/-- A polynomial byte always selects one of the 256 buckets on either machine width. -/
theorem payloadDigit_bound (value : UInt64) : (value &&& 255).toNat < 256 := by
  have h := UInt64.and_le_right (a := value) (b := 255)
  rw [UInt64.le_iff_toNat_le] at h
  exact Nat.lt_succ_of_le h

/-- Machine-indexed byte scattering is exactly three checked scalar XOR stores. -/
theorem scatterDigit_eq (buckets : FixedWords (6*256*3)) (digit : Fin 6)
    (value w0 w1 w2 : UInt64) :
    scatterDigit buckets digit.val.toUSize value w0 w1 w2 =
      let k := 3*(256*digit.val+(value &&& 255).toNat)
      writeWord (writeWord (writeWord buckets k (readWord buckets k ^^^ w0))
        (k+1) (readWord buckets (k+1) ^^^ w1)) (k+2) (readWord buckets (k+2) ^^^ w2) := by
  let k := 3*(256*digit.val+(value &&& 255).toNat)
  have hk : k+2 < 6*256*3 := by
    have := digit.isLt
    have := payloadDigit_bound value
    dsimp only [k]
    omega
  have he : scatterDigit buckets digit.val.toUSize value w0 w1 w2 =
      let b0 := writeWord buckets k (readWord buckets k ^^^ w0)
      let b1 := writeWord b0 (k+1) (readWord b0 (k+1) ^^^ w1)
      writeWord b1 (k+2) (readWord b1 (k+2) ^^^ w2) := by
    simp only [scatterDigit,writeWord,readWord,k,Nat.toUSize,USize.ofNat_add,USize.ofNat_mul,
      USize.ofNat_uInt64ToNat]
    rfl
  rw [he]
  dsimp only
  rw [readWord_writeWord _ _ _ (by omega) (by omega),ite_eq_right (by omega),
    readWord_writeWord _ _ _ (by omega) (by omega),ite_eq_right (by omega),
    readWord_writeWord _ _ _ (by omega) (by omega),ite_eq_right (by omega)]

/-- Scattering one payload byte adds precisely its extension weight to the selected bucket. -/
theorem scatterDigit_bucketValue (buckets : FixedWords (6*256*3))
    (digit queryDigit : Fin 6) (queryByte : Fin 256) (value w0 w1 w2 : UInt64) :
    bucketValue (scatterDigit buckets digit.val.toUSize value w0 w1 w2)
      (256*queryDigit.val+queryByte.val) =
      bucketValue buckets (256*queryDigit.val+queryByte.val) +
        if digit = queryDigit ∧ (value &&& 255).toNat = queryByte.val
        then ⟨⟨w0⟩,⟨w1⟩,⟨w2⟩⟩ else 0 := by
  have hd := digit.isLt
  have hq := queryDigit.isLt
  have hb := queryByte.isLt
  have hv := payloadDigit_bound value
  rw [scatterDigit_eq]
  rw [bucketValue_accumulate buckets
    ⟨256*digit.val+(value &&& 255).toNat,by omega⟩
    ⟨256*queryDigit.val+queryByte.val,by omega⟩]
  have he : (⟨256*digit.val+(value &&& 255).toNat,by omega⟩ : Fin (6*256)) =
      ⟨256*queryDigit.val+queryByte.val,by omega⟩ ↔
      digit = queryDigit ∧ (value &&& 255).toNat = queryByte.val := by
    simp only [Fin.ext_iff]
    omega
  simp only [he]

/-- Machine-coordinate scattering preserves the same selected-bucket sum. -/
theorem scatterDigit_bucketValueU (buckets : FixedWords (6*256*3))
    (digit : USize) (hd : digit.toNat < 6) (queryDigit : Fin 6) (queryByte : Fin 256)
    (value w0 w1 w2 : UInt64) :
    bucketValue (scatterDigit buckets digit value w0 w1 w2)
      (256*queryDigit.val+queryByte.val) =
      bucketValue buckets (256*queryDigit.val+queryByte.val) +
        if digit.toNat = queryDigit.val ∧ (value &&& 255).toNat = queryByte.val
        then ⟨⟨w0⟩,⟨w1⟩,⟨w2⟩⟩ else 0 := by
  simpa only [Nat.toUSize,USize.ofNat_toNat,Fin.ext_iff] using
    scatterDigit_bucketValue buckets ⟨digit.toNat,hd⟩ queryDigit queryByte value w0 w1 w2

/-- The extension weight represented by three scalar position coordinates. -/
def positionWeight (weights : FixedWords 4800) (j : Nat) : W :=
  ⟨⟨readWord weights (3*j)⟩,⟨readWord weights (3*j+1)⟩,⟨readWord weights (3*j+2)⟩⟩

/-- Materialized scalar coordinates reconstruct the supplied position weight exactly. -/
theorem positionWeight_weightDigits (weights : Array W) (j : Fin 1600) :
    positionWeight (weightDigits weights) j.val = weights[j.val]! := by
  have h0 := weightDigits_get weights j ⟨0,by decide⟩
  have h1 := weightDigits_get weights j ⟨1,by decide⟩
  have h2 := weightDigits_get weights j ⟨2,by decide⟩
  simp only [Nat.add_zero,weightCoordinate,ite_true] at h0
  simp only [weightCoordinate,Nat.reduceEqDiff,ite_false,ite_true] at h1 h2
  unfold positionWeight
  rw [h0,h1,h2]

/-- Every scattered byte bucket is the sum of exactly the position weights selecting that byte. -/
theorem scatterPayload_bucketValue (payload : FixedWords 1600) (weights : FixedWords 4800)
    (j : Nat) (buckets : FixedWords (6*256*3)) (digit : Fin 6) (value : Fin 256) :
    bucketValue (scatterPayload payload weights j buckets) (256*digit.val+value.val) =
      bucketValue buckets (256*digit.val+value.val) +
        ∑ k ∈ Finset.Ico j 1600,
          if ((readWord payload k >>> (8*digit.val).toUInt64) &&& 255).toNat = value.val
          then positionWeight weights k else 0 := by
  rw [scatterPayload]
  split
  · rename_i hj
    rw [scatterPayload_bucketValue payload weights (j+1)]
    rw [scatterDigit_bucketValueU _ 5 (by simp only [USize.reduceToNat]; decide) digit value,
      scatterDigit_bucketValueU _ 4 (by simp only [USize.reduceToNat]; decide) digit value,
      scatterDigit_bucketValueU _ 3 (by simp only [USize.reduceToNat]; decide) digit value,
      scatterDigit_bucketValueU _ 2 (by simp only [USize.reduceToNat]; decide) digit value,
      scatterDigit_bucketValueU _ 1 (by simp only [USize.reduceToNat]; decide) digit value,
      scatterDigit_bucketValueU _ 0 (by simp only [USize.reduceToNat]; decide) digit value]
    rw [Finset.sum_eq_sum_Ico_succ_bot hj]
    fin_cases digit <;>
      simp only [USize.reduceToNat,Nat.reduceEqDiff,false_and,ite_false,true_and,add_zero] <;>
      rw [add_assoc] <;>
      simp only [positionWeight,readWord,Nat.toUSize,USize.ofNat_add,USize.ofNat_mul,
        Nat.reduceMul,Nat.toUInt64] <;>
      rfl
  · rename_i hj
    rw [Finset.Ico_eq_empty_of_le (by omega),Finset.sum_empty,add_zero]
termination_by 1600-j

/-- Every allocated bucket denotes the zero extension weight. -/
theorem bucketValue_zero (j : Fin (6*256)) :
    bucketValue (zeroWords (6*256*3)) j.val = 0 := by
  have hz (k : Nat) (hk : k < 6*256*3) :
      readWord (zeroWords (6*256*3)) k = 0 := by
    change readUWord (zeroWords (6*256*3)) k.toUSize = 0
    rw [← getUWord_eq_readUWord _ _ ((zeroWords (6*256*3)).index_bound k hk)]
    exact getUWord_zeroWords _ _ _ _
  have hj := j.isLt
  unfold bucketValue
  rw [hz _ (by omega),hz _ (by omega),hz _ (by omega)]
  rfl

/-- The production scatter buffer contains exactly the supplied weights grouped by payload byte. -/
theorem scatterPayload_weightDigits (payload : FixedWords 1600) (weights : Array W)
    (digit : Fin 6) (value : Fin 256) :
    bucketValue (scatterPayload payload (weightDigits weights) 0 (zeroWords (6*256*3)))
      (256*digit.val+value.val) =
      ∑ k ∈ Finset.Ico 0 1600,
        if ((readWord payload k >>> (8*digit.val).toUInt64) &&& 255).toNat = value.val
        then weights[k]! else 0 := by
  have hd := digit.isLt
  have hv := value.isLt
  rw [scatterPayload_bucketValue,bucketValue_zero ⟨256*digit.val+value.val,by omega⟩,zero_add]
  apply Finset.sum_congr rfl
  intro k hk
  have hkb : k < 1600 := (Finset.mem_Ico.mp hk).2
  rw [positionWeight_weightDigits weights ⟨k,hkb⟩]

/-- A pointwise native chi payload denotes the exact affine RMFE product polynomial. -/
theorem productCell_poly (state : Array UInt64) (groups offset : USize) (bits : UInt64) (j : Nat) :
    toPoly (productCell state groups offset bits prepareRmfeProducts j).toBitVec =
      let k := j.toUSize
      let a := (state[(k*groups+offset).toNat]! >>> bits) &&& 65535
      let b := (state[(shiftU k 1*groups+offset).toNat]! >>> bits) &&& 65535
      let c := (state[(shiftU k 2*groups+offset).toNat]! >>> bits) &&& 65535
      toPoly (embeddingRaw 65535).toBitVec * toPoly (embeddingRaw a).toBitVec +
        (toPoly (embeddingRaw 65535).toBitVec + toPoly (embeddingRaw b).toBitVec) *
          toPoly (embeddingRaw c).toBitVec := by
  exact prepareRmfeProducts_chi_poly _ _ _

/-- The complete production payload loop retains the certified affine RMFE polynomial at every position. -/
theorem productPayload_poly (state : Array UInt64) (groups offset : USize) (bits : UInt64)
    (out : FixedWords 1600) (j : Fin 1600) :
    toPoly (readWord (productPayload state groups offset bits prepareRmfeProducts 0 out) j.val).toBitVec =
      toPoly (productCell state groups offset bits prepareRmfeProducts j.val).toBitVec := by
  rw [productPayload_get _ _ _ _ _ _ _ _ j.isLt,ite_eq_left (Nat.zero_le _)]

end CompStark.Keccak.GkrProver
