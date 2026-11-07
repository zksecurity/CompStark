/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.RingSwitch
public import CompPoly.Fields.Binary.BF64.WordField

/-! Materialized factors of equality tensors, in little-endian numeric order. -/

@[expose] public section
namespace CompStark.Pcs

/-- The little-endian Boolean coordinates of a numeric table index. -/
def vertex (n : Nat) (i : Fin (2 ^ n)) : Whir.Cube n := fun j => i.val.testBit j.val

/-- Encode a Boolean vertex by its little-endian bit pattern. -/
def vertexIndex (n : Nat) (u : Whir.Cube n) : Fin (2 ^ n) :=
  ((BitVec.ofBoolListLE (List.ofFn u)).cast List.length_ofFn).toFin

/-- Numeric encoding recovers every coordinate of the input vertex. -/
theorem vertex_vertexIndex (n : Nat) (u : Whir.Cube n) : vertex n (vertexIndex n u) = u := by
  funext i
  change (((BitVec.ofBoolListLE (List.ofFn u)).cast List.length_ofFn).getLsbD i.val) = u i
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]

/-- Numeric indices are determined by their bounded Boolean coordinates. -/
theorem vertex_injective (n : Nat) : Function.Injective (vertex n) := by
  intro x y h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact congrFun h ⟨i, hi⟩
  · rw [Nat.testBit_eq_false_of_lt (x.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_eq_false_of_lt (y.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]

/-- Numeric table order and Boolean vertices are equivalent. -/
def vertexEquiv (n : Nat) : Fin (2 ^ n) ≃ Whir.Cube n where
  toFun := vertex n
  invFun := vertexIndex n
  left_inv i := vertex_injective n (vertex_vertexIndex n (vertex n i))
  right_inv := vertex_vertexIndex n

/-- Store a complete Boolean table once for subsequent constant-time numeric lookups. -/
@[macro_inline] def cacheTable {F : Type} {n : Nat} (table : Whir.Table F n) : Whir.Table F n :=
  let values := Vector.ofFn (fun i : Fin (2 ^ n) => table (vertex n i))
  fun u => values[vertexIndex n u]

/-- Cached table lookup preserves every Boolean coordinate. -/
theorem cacheTable_eq {F : Type} {n : Nat} (table : Whir.Table F n) : cacheTable table = table := by
  funext u
  simp only [cacheTable, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, vertex_vertexIndex]

/-- Cache each equality factor separately, retaining only `2^lo + 2^hi` field values. -/
@[macro_inline] def cachedFactoredEq {F : Type} [CommRing F] {lo hi : Nat}
    (point : Fin (lo + hi) → F) : FactoredEq F lo hi :=
  ⟨cacheTable (Whir.eqWeight (fun i => point (Fin.castAdd hi i))),
    cacheTable (Whir.eqWeight (fun i => point (Fin.natAdd lo i)))⟩

/-- Caching changes neither factor nor any reconstructed tensor weight. -/
theorem cachedFactoredEq_eq {F : Type} [CommRing F] {lo hi : Nat}
    (point : Fin (lo + hi) → F) : cachedFactoredEq point = factoredEq point := by
  simp only [cachedFactoredEq, factoredEq, cacheTable_eq]

/-- Shared factored weights equal the full equality tensor entrywise. -/
theorem cachedFactoredEq_eval {F : Type} [CommRing F] {lo hi : Nat}
    (point : Fin (lo + hi) → F) (u : Whir.Cube (lo + hi)) :
    (cachedFactoredEq point).eval u = Whir.eqWeight point u := by
  rw [cachedFactoredEq_eq, factoredEq_eval]

/-- Transport an equality tensor along a ring homomorphism. -/
theorem map_eqWeight {F G : Type} [CommRing F] [CommRing G] (φ : F →+* G)
    {n : Nat} (point : Fin n → F) (u : Whir.Cube n) :
    φ (Whir.eqWeight point u) = Whir.eqWeight (fun i => φ (point i)) u := by
  simp only [Whir.eqWeight, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  split <;> simp only [map_sub, map_one]

/-- Cache equality factors directly on the executable cubic-extension field. -/
@[macro_inline] def wordFactoredEq {lo hi : Nat} (point : Fin (lo + hi) → BF64.Ext3) :
    FactoredEq BF64.WordExt3 lo hi :=
  cachedFactoredEq (fun i => BF64.WordExt3.ofField (point i))

/-- Reconstruct a tensor entry using one word-field product. -/
theorem wordFactoredEq_eval {lo hi : Nat} (point : Fin (lo + hi) → BF64.Ext3)
    (u : Whir.Cube (lo + hi)) :
    ((wordFactoredEq point).eval u).toField = Whir.eqWeight point u := by
  rw [wordFactoredEq, cachedFactoredEq_eval]
  have h := map_eqWeight BF64.WordExt3.ringEquiv.toRingHom
    (fun i => BF64.WordExt3.ofField (point i)) u
  have hf : (fun i => BF64.WordExt3.ringEquiv.toRingHom
      (BF64.WordExt3.ofField (point i))) = point := by
    funext i
    exact BF64.WordExt3.toField_ofField (point i)
  exact h.trans (congrArg (fun z => Whir.eqWeight z u) hf)

/-- Read one polynomial-basis bit with a machine shift and mask. -/
@[inline] def packedBit (a : UInt64) (i : Fin 64) : Bool :=
  ((a >>> i.val.toUInt64) &&& 1) == 1

/-- The machine test is exactly the corresponding bounded polynomial-basis bit. -/
theorem packedBit_eq (a : UInt64) (i : Fin 64) :
    packedBit a i = a.toBitVec.getLsbD i.val := by
  have hi : i.val < UInt64.size := lt_trans i.isLt (by decide)
  have hs : (a >>> i.val.toUInt64).toBitVec.getLsbD 0 = a.toBitVec.getLsbD i.val := by
    simp only [UInt64.toBitVec_shiftRight, BitVec.ushiftRight_eq', BitVec.toNat_umod,
      UInt64.toNat_toBitVec, BitVec.getLsbD_ushiftRight, Nat.add_zero]
    change a.toBitVec.getLsbD ((i.val % 2 ^ 64) % 64) = _
    rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt i.isLt]
  unfold packedBit
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, ← UInt64.toBitVec_inj]
  rw [UInt64.toBitVec_and]
  change ((a >>> i.val.toUInt64).toBitVec &&& 1#64) = 1#64 ↔ _
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD, hs]
  cases a.toBitVec.getLsbD i.val <;> decide

/-- Fold one bit column using scalar XOR accumulators and a descending numeric cursor. -/
def bitFoldLoop (packed : Vector BF64.Word count) (weights : Vector BF64.WordExt3 count)
    (bit : Fin 64) : (n : Nat) → n ≤ count → UInt64 → UInt64 → UInt64 → BF64.WordExt3
  | 0, _, a, b, c => ⟨⟨a⟩, ⟨b⟩, ⟨c⟩⟩
  | n + 1, h, a, b, c =>
      let i : Fin count := ⟨n, by omega⟩
      if packedBit packed[i].val bit then
        let w := weights[i]
        bitFoldLoop packed weights bit n (by omega)
          (a ^^^ w.c0.val) (b ^^^ w.c1.val) (c ^^^ w.c2.val)
      else bitFoldLoop packed weights bit n (by omega) a b c

/-- Scalar accumulators equal their initial word plus the visited column's weighted sum. -/
theorem bitFoldLoop_refines (packed : Vector BF64.Word count)
    (weights : Vector BF64.WordExt3 count) (bit : Fin 64) (n : Nat) (h : n ≤ count)
    (a b c : UInt64) :
    (bitFoldLoop packed weights bit n h a b c).toField =
      (BF64.WordExt3.mk ⟨a⟩ ⟨b⟩ ⟨c⟩).toField +
        ∑ i : Fin n, if packedBit packed[i.castLE h].val bit then weights[i.castLE h].toField else 0 := by
  induction n generalizing a b c with
  | zero => simp only [bitFoldLoop, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  | succ n ih =>
      rw [bitFoldLoop]
      split
      · rename_i hb
        rw [ih]
        change (BF64.WordExt3.add ⟨⟨a⟩, ⟨b⟩, ⟨c⟩⟩ weights[n]).toField + _ = _
        rw [BF64.WordExt3.toField_add, Fin.sum_univ_castSucc]
        change packedBit packed[n].val bit = true at hb
        simp only [Fin.getElem_fin, Fin.val_castLE, Fin.val_castSucc, Fin.val_last, hb, ↓reduceIte]
        rw [add_assoc, add_comm weights[n].toField]
      · rename_i hb
        rw [ih, Fin.sum_univ_castSucc]
        change ¬packedBit packed[n].val bit = true at hb
        simp only [Fin.getElem_fin, Fin.val_castLE, Fin.val_castSucc, Fin.val_last, hb, Bool.false_eq_true, ↓reduceIte, add_zero]


/-- Fold all 64 bit columns of a packed base-field table against shared extension weights. -/
def foldBits (packed : Vector BF64.Word count) (weights : Vector BF64.WordExt3 count) :
    Vector BF64.WordExt3 64 :=
  Vector.ofFn fun bit => bitFoldLoop packed weights bit count (Nat.le_refl count) 0 0 0

/-- Packed bit folds equal the 64 independent weighted Boolean sums. -/
theorem foldBits_refines (packed : Vector BF64.Word count) (weights : Vector BF64.WordExt3 count)
    (bit : Fin 64) :
    (foldBits packed weights)[bit].toField =
      ∑ i : Fin count, if packed[i].val.toBitVec.getLsbD bit.val then weights[i].toField else 0 := by
  simp only [foldBits, Fin.getElem_fin, Vector.getElem_ofFn, bitFoldLoop_refines,
    packedBit_eq, Fin.val_castLE]
  exact zero_add _


end CompStark.Pcs
