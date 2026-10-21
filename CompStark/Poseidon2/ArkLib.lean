/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Poseidon2.KoalaBear
public import ArkLib.Data.Hash.Poseidon2

/-! # CompStark's Poseidon2 is ArkLib's

ArkLib's Poseidon2 (`_root_.Poseidon2.permute`, a translation of leanSpec over
`KoalaBear.Field`) agrees with ours on Plonky3's KoalaBear instances at width 16 and 24
(`permute_arkLib16`, `permute_arkLib24`).
-/

@[expose] public section
namespace CompStark.Poseidon2

open scoped BigOperators

local notation "𝔽" => _root_.KoalaBear.Field

/-- Summing a vector from the left is its `Finset` sum. -/
theorem foldl_add_eq_sum {F : Type*} [AddCommMonoid F] {n : Nat} (v : Vector F n) :
    v.foldl (· + ·) 0 = ∑ j : Fin n, v[(j : Nat)] := by
  rw [Vector.foldl_eq_toList_foldl, ← List.sum_eq_foldl, ← List.sum_ofFn]
  congr 1
  apply List.ext_getElem <;>
    simp only [Vector.length_toList, List.length_ofFn, Vector.getElem_toList, List.getElem_ofFn,
      implies_true]

/-- Mapping over the rows of `ofFlatten v` maps over the consecutive chunks of `v`. -/
theorem getElem_map_ofFlatten {α β : Type*} {m n : Nat} (v : Vector α (m * n))
    (f : Vector α n → β) (i : Nat) (hi : i < m) :
    ((Vector.Matrix.ofFlatten v).map f)[i] =
      f (Vector.ofFn fun j : Fin n ↦ v[i * n + j]'(by nlinarith [j.isLt])) := by
  simp only [Vector.Matrix.ofFlatten, Vector.getElem_map]
  rw [Vector.getElem_finRange]
  congr 1
  ext j hj
  simp only [Vector.getElem_cast, Vector.getElem_extract, Vector.getElem_ofFn]

/-- ArkLib's `M₄` applied to a chunk of four. -/
theorem getElem_applyM4 (c : Vector 𝔽 4) (j : Nat) (hj : j < 4) :
    (_root_.Poseidon2.applyM4 c)[j] = match j with
      | 0 => 2 * c[0] + 3 * c[1] + c[2] + c[3]
      | 1 => c[0] + 2 * c[1] + 3 * c[2] + c[3]
      | 2 => c[0] + c[1] + 2 * c[2] + 3 * c[3]
      | _ => 3 * c[0] + c[1] + c[2] + 2 * c[3] := by
  obtain _ | _ | _ | _ | j := j
  rotate_left 4
  · omega
  all_goals
    simp only [_root_.Poseidon2.applyM4, Vector.Matrix.mulVec, Vector.dotProduct,
      _root_.Poseidon2.m4Matrix, Vector.getElem_map, foldl_add_eq_sum, Fin.sum_univ_four,
      Vector.getElem_zipWith, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      Nat.one_mod, Nat.reduceMod, Nat.mod_succ, Nat.cast_ofNat, one_mul, zero_add, Nat.reduceAdd]

/-- The external layers agree. -/
theorem externalLinear_eq (params : _root_.Poseidon2.Params) (s : Vector 𝔽 params.width) :
    externalLinear s = _root_.Poseidon2.externalLinearLayer params s := by
  have hw := params.widthDiv4_mul_4_eq_width
  have hm : ∀ b (hb : b < params.widthDiv4) j (hj : j < 4),
      (_root_.Poseidon2.applyM4 (Vector.ofFn fun k : Fin 4 ↦
        s[b * 4 + k]'(by omega)))[j] = mat4 s b j := by
    intro b hb j hj
    have hx : ∀ k (hk : k < 4), s[4 * b + k]?.getD 0 = s[b * 4 + k]'(by omega) := by
      intro k hk
      rw [Vector.getElem?_eq_getElem (by omega), Option.getD_some]
      congr 1
      omega
    rw [getElem_applyM4]
    obtain _ | _ | _ | _ | j := j
    rotate_left 4
    · omega
    all_goals
      simp only [mat4, Vector.getElem_ofFn]
      rw [hx 0 (by omega), hx 1 (by omega), hx 2 (by omega), hx 3 (by omega)]
      rfl
  ext i hi
  simp only [externalLinear, _root_.Poseidon2.externalLinearLayer, Vector.getElem_ofFn,
    Vector.getElem_cast, Vector.getElem_flatten, Vector.getElem_map, getElem_map_ofFlatten,
    Vector.getElem_zipWith, Vector.Matrix.transpose, foldl_add_eq_sum, Vector.get_eq_getElem]
  rw [hm _ (by unfold _root_.Poseidon2.Params.widthDiv4; omega) _ (by omega)]
  congr 1
  exact Finset.sum_congr rfl fun b _ ↦
    (hm _ b.isLt _ (by omega)).symm

/-- The internal layers agree. -/
theorem internalLinear_eq (params : _root_.Poseidon2.Params) (s : Vector 𝔽 params.width) :
    internalLinear params.internalDiagVectors s =
      _root_.Poseidon2.internalLinearLayer params s := by
  ext i hi
  simp only [internalLinear, _root_.Poseidon2.internalLinearLayer, Vector.getElem_ofFn,
    Vector.getElem_zipWith, foldl_add_eq_sum, Fin.getElem_fin]
  exact add_comm _ _

/-- The full rounds agree. -/
theorem fullRound_eq (params : _root_.Poseidon2.Params) (P : Params 𝔽 params.width)
    (hd : P.degree = _root_.Poseidon2.sBoxDegree) (s c : Vector 𝔽 params.width) :
    fullRound P s c = _root_.Poseidon2.fullRound params s c := by
  rw [fullRound, _root_.Poseidon2.fullRound, externalLinear_eq, hd]
  congr 1
  ext i hi
  simp only [Vector.getElem_ofFn, Vector.getElem_map, Vector.getElem_zipWith, Fin.getElem_fin]

/-- The partial rounds agree. -/
theorem partialRound_eq (params : _root_.Poseidon2.Params) (P : Params 𝔽 params.width)
    (hd : P.degree = _root_.Poseidon2.sBoxDegree) (hV : P.diagonal = params.internalDiagVectors)
    (s : Vector 𝔽 params.width) (c : 𝔽) :
    partialRound P s c = _root_.Poseidon2.partialRound params s c := by
  rw [partialRound, _root_.Poseidon2.partialRound, hV, internalLinear_eq, hd]
  congr 1
  ext i hi
  simp only [Vector.getElem_ofFn, Vector.getElem_set, Fin.getElem_fin, ite_true]
  by_cases h : i = 0
  · subst h
    simp only [ite_true]
  · simp only [h, ite_false, Ne.symm h]

/-- The permutations agree when the parameters do: the same S-box and diagonal, and our round
constants are the chunks that ArkLib's `permute` extracts from its flat table. -/
theorem permute_eq (params : _root_.Poseidon2.Params) (P : Params 𝔽 params.width)
    (hd : P.degree = _root_.Poseidon2.sBoxDegree) (hV : P.diagonal = params.internalDiagVectors)
    (hi : P.initial = (List.finRange params.halfNumFullRounds).map fun k : Fin _ ↦
      (params.roundConstants.extract (k * params.width) (k * params.width + params.width)).cast
        (_root_.Poseidon2.firstHalfRoundConstants_extract_length params k))
    (hp : P.internal = (List.finRange params.numPartialRounds).map fun k ↦
      (params.roundConstants.drop (params.halfNumFullRounds * params.width))[k.val]'
        (_root_.Poseidon2.partialRoundConstant_index_lt params k))
    (ht : P.terminal = (List.finRange params.halfNumFullRounds).map fun k : Fin _ ↦
      (((params.roundConstants.drop (params.halfNumFullRounds * params.width)).drop
        params.numPartialRounds).extract (k * params.width) (k * params.width + params.width)).cast
        (_root_.Poseidon2.secondHalfRoundConstants_extract_length params k))
    (s : Vector 𝔽 params.width) :
    permute P s = _root_.Poseidon2.permute params s := by
  simp only [permute, _root_.Poseidon2.permute, Fin.foldl_eq_finRange_foldl, hi, hp, ht,
    List.foldl_map, externalLinear_eq, fullRound_eq params P hd, partialRound_eq params P hd hV,
    Fin.getElem_fin]

/-- Plonky3's width-16 instance is ArkLib's `params16`. -/
theorem permute_arkLib16 (s : Vector 𝔽 16) :
    permute (KoalaBear.width16 𝔽) s = _root_.Poseidon2.permute _root_.Poseidon2.params16 s := by
  apply permute_eq _root_.Poseidon2.params16 (KoalaBear.width16 𝔽) rfl
  · simp only [KoalaBear.width16, Params.ofNat, KoalaBear.diagonal16, _root_.Poseidon2.params16,
      one_div, neg_div]
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- Plonky3's width-24 instance is ArkLib's `params24`. -/
theorem permute_arkLib24 (s : Vector 𝔽 24) :
    permute (KoalaBear.width24 𝔽) s = _root_.Poseidon2.permute _root_.Poseidon2.params24 s := by
  apply permute_eq _root_.Poseidon2.params24 (KoalaBear.width24 𝔽) rfl
  · simp only [KoalaBear.width24, Params.ofNat, KoalaBear.diagonal24, _root_.Poseidon2.params24,
      one_div, neg_div]
  · decide +kernel
  · decide +kernel
  · decide +kernel

end CompStark.Poseidon2
