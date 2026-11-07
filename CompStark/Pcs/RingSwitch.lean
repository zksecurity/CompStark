/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompPoly.Fields.Binary.BF64.WordExt3Proofs
public import ArkLib.ProofSystem.Whir.Algebra

/-! Executable Frobenius maps and factored equality weights for binary-field PCS openings. -/

@[expose] public section
namespace CompStark.Pcs

/-- Apply the ordered two-term Frobenius maps over a specification ring. -/
def frobeniusMap {F : Type} [CommRing F] : List (Nat × F) → F → F
  | [], a => a
  | (shift, coefficient) :: rest, a =>
      frobeniusMap rest (a + coefficient * a ^ 2 ^ shift)

/-- Apply Frobenius maps without leaving the three-word extension carrier. -/
def wordMap : List (Nat × BF64.WordExt3) → BF64.WordExt3 → BF64.WordExt3
  | [], a => a
  | (shift, coefficient) :: rest, a =>
      wordMap rest (BF64.WordExt3.add a
        (BF64.WordExt3.mul coefficient (a.frobenius shift)))

/-- Every word-map output equals the ordered specification composition. -/
theorem wordMap_refines (stages : List (Nat × BF64.WordExt3)) (a : BF64.WordExt3) :
    (wordMap stages a).toField =
      frobeniusMap (stages.map fun stage => (stage.1, stage.2.toField)) a.toField := by
  induction stages generalizing a with
  | nil => rfl
  | cons stage stages ih =>
      simp only [wordMap, ih, BF64.WordExt3.toField_add, BF64.WordExt3.toField_mul,
        BF64.WordExt3.toField_frobenius, List.map_cons, frobeniusMap]

/-- Six descending maps for packing 64 Boolean coordinates into one base-field word. -/
def binary64Stages (challenges : Vector BF64.WordExt3 6) : List (Nat × BF64.WordExt3) :=
  List.ofFn fun i : Fin 6 => (2 ^ (5 - i.val), challenges[i])

/-- The composed binary-64 map uses exactly 63 squarings and six extension products. -/
def binary64Map (challenges : Vector BF64.WordExt3 6) (a : BF64.WordExt3) : BF64.WordExt3 :=
  wordMap (binary64Stages challenges) a

/-- The polynomial-basis coordinate of the cubic extension, with limb order constant, linear, quadratic. -/
def coordinateBasis (i : Fin 192) : BF64.WordExt3 :=
  let bit : BF64.Word := ⟨(1 : UInt64) <<< (i.val % 64).toUInt64⟩
  if i.val < 64 then ⟨bit, ⟨0⟩, ⟨0⟩⟩
  else if i.val < 128 then ⟨⟨0⟩, bit, ⟨0⟩⟩ else ⟨⟨0⟩, ⟨0⟩, bit⟩

/-- The shared map's values on all 192 binary coordinate vectors. -/
def coordinateWeights (challenges : Vector BF64.WordExt3 6) : Vector BF64.WordExt3 192 :=
  Vector.ofFn fun i => binary64Map challenges (coordinateBasis i)

/-- Every coordinate weight agrees with the specification map, in the same limb order. -/
theorem coordinateWeights_refines (challenges : Vector BF64.WordExt3 6) (i : Fin 192) :
    (coordinateWeights challenges)[i].toField =
      frobeniusMap ((binary64Stages challenges).map fun stage => (stage.1, stage.2.toField))
        (coordinateBasis i).toField := by
  simp only [coordinateWeights, Fin.getElem_fin, Vector.getElem_ofFn, binary64Map,
    wordMap_refines]

/-- Sum extension words without converting partial sums to the specification carrier. -/
def sumWords (values : List BF64.WordExt3) : BF64.WordExt3 :=
  values.foldr BF64.WordExt3.add ⟨⟨0⟩, ⟨0⟩, ⟨0⟩⟩

/-- Word accumulation preserves the specification field's sum. -/
theorem sumWords_refines (values : List BF64.WordExt3) :
    (sumWords values).toField = (values.map BF64.WordExt3.toField).sum := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [sumWords, List.foldr_cons, BF64.WordExt3.toField_add, List.map_cons,
        List.sum_cons] at *
      rw [ih]

/-- Keep the two factors of an equality tensor in separate shared tables. -/
structure FactoredEq (F : Type) (lo hi : Nat) where
  /-- Values for the low coordinates. -/
  low : Whir.Table F lo
  /-- Values for the high coordinates. -/
  high : Whir.Table F hi

/-- Evaluate a factored equality tensor at one Boolean vertex. -/
def FactoredEq.eval {F : Type} [Mul F] {lo hi : Nat} (tensor : FactoredEq F lo hi)
    (u : Whir.Cube (lo + hi)) : F :=
  tensor.low (fun i => u (Fin.castAdd hi i)) * tensor.high (fun i => u (Fin.natAdd lo i))

/-- Construct the two equality factors without constructing their Cartesian product. -/
def factoredEq {F : Type} [CommRing F] {lo hi : Nat} (point : Fin (lo + hi) → F) :
    FactoredEq F lo hi :=
  ⟨Whir.eqWeight (fun i => point (Fin.castAdd hi i)),
    Whir.eqWeight (fun i => point (Fin.natAdd lo i))⟩

/-- Factoring preserves every weight, including empty low or high coordinate blocks. -/
theorem factoredEq_eval {F : Type} [CommRing F] {lo hi : Nat}
    (point : Fin (lo + hi) → F) (u : Whir.Cube (lo + hi)) :
    (factoredEq point).eval u = Whir.eqWeight point u := by
  simpa only [FactoredEq.eval, factoredEq, Whir.splitCubeEquiv] using
    (Whir.eqWeight_add point (fun i => u (Fin.castAdd hi i))
      (fun i => u (Fin.natAdd lo i))).symm.trans
        (congrArg (Whir.eqWeight point) ((Whir.splitCubeEquiv lo hi).left_inv u))

/-- Apply the map after reconstructing one tensor entry, retaining the factored input. -/
def ringWeight {lo hi : Nat} (stages : List (Nat × BF64.WordExt3))
    (tensor : FactoredEq BF64.Ext3 lo hi) (u : Whir.Cube (lo + hi)) : BF64.Ext3 :=
  (wordMap stages (BF64.WordExt3.ofField (tensor.eval u))).toField

/-- Factored word ring weights equal the map of the mathematical equality tensor. -/
theorem ringWeight_refines {lo hi : Nat} (stages : List (Nat × BF64.WordExt3))
    (point : Fin (lo + hi) → BF64.Ext3) (u : Whir.Cube (lo + hi)) :
    ringWeight stages (factoredEq point) u =
      frobeniusMap (stages.map fun stage => (stage.1, stage.2.toField))
        (Whir.eqWeight point u) := by
  rw [ringWeight, wordMap_refines, BF64.WordExt3.toField_ofField, factoredEq_eval]

/-- Produce consecutive batching powers by one multiplication per step. -/
def powersFrom {F : Type} [Monoid F] (r : F) : Nat → F → List F
  | 0, _ => []
  | n + 1, a => a :: powersFrom r n (a * r)

/-- Consecutive multiplication gives the exact power order, from an arbitrary offset. -/
theorem powersFrom_eq {F : Type} [Monoid F] (r : F) (n start : Nat) :
    powersFrom r n (r ^ start) = (List.range' start n).map (fun i => r ^ i) := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
      rw [powersFrom, ← pow_succ, ih, List.range'_succ, List.map_cons]

/-- Ring claims precede point claims in one shared, uninterrupted batching-power sequence. -/
theorem powersFrom_append {F : Type} [Monoid F] (r : F) (rings points : Nat) :
    powersFrom r (rings + points) 1 =
      powersFrom r rings 1 ++ powersFrom r points (r ^ rings) := by
  rw [← pow_zero r, powersFrom_eq, powersFrom_eq, powersFrom_eq,
    ← List.map_append, ← List.range'_append]
  simp only [one_mul, zero_add]

end CompStark.Pcs
