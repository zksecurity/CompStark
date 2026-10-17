/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Poseidon2.KoalaBear
public import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-! # Poseidon2 along ring homomorphisms

The permutation uses only ring operations and its parameters, so a ring homomorphism maps a run
of the permutation to a run with the mapped parameters (`permute_map`). Plonky3's KoalaBear
instances map to themselves (`width16_map`, `width24_map`), so the permutation on the Montgomery
field `KoalaBear.Fast.Field` is the specification on `KoalaBear.Field`, read through the ring
isomorphism between them (`fast_width16`, `fast_width24`).
-/

@[expose] public section
namespace CompStark.Poseidon2

variable {F K : Type*} {t : Nat}

/-- The parameters with every constant mapped by `f`. -/
def Params.map [CommRing F] [CommRing K] (f : F →+* K) (P : Params F t) : Params K t where
  degree := P.degree
  initial := P.initial.map (·.map f)
  internal := P.internal.map f
  terminal := P.terminal.map (·.map f)
  diagonal := P.diagonal.map f

section Ring
variable [CommRing F] [CommRing K] (f : F →+* K)

theorem getElem?_getD_map (s : Vector F t) (i : Nat) :
    (s.map f)[i]?.getD 0 = f (s[i]?.getD 0) := by
  rw [Vector.getElem?_map]
  cases s[i]? <;> simp only [Option.map_none, Option.map_some, Option.getD_none,
    Option.getD_some, map_zero]

theorem mat4_map (s : Vector F t) (b i : Nat) : f (mat4 s b i) = mat4 (s.map f) b i := by
  unfold mat4
  simp only [getElem?_getD_map]
  split <;> simp only [map_add, map_mul, map_ofNat]

theorem externalLinear_map (s : Vector F t) :
    (externalLinear s).map f = externalLinear (s.map f) := by
  ext i hi
  simp only [externalLinear, Vector.getElem_map, Vector.getElem_ofFn, map_add, map_sum, mat4_map]

theorem internalLinear_map (V s : Vector F t) :
    (internalLinear V s).map f = internalLinear (V.map f) (s.map f) := by
  ext i hi
  simp only [internalLinear, Vector.getElem_map, Vector.getElem_ofFn, map_add, map_mul, map_sum,
    Fin.getElem_fin]

theorem fullRound_map (P : Params F t) (s c : Vector F t) :
    (fullRound P s c).map f = fullRound (P.map f) (s.map f) (c.map f) := by
  simp only [fullRound, Params.map]
  rw [externalLinear_map]
  congr 1
  ext i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn, map_pow, map_add, Fin.getElem_fin]

theorem partialRound_map (P : Params F t) (s : Vector F t) (c : F) :
    (partialRound P s c).map f = partialRound (P.map f) (s.map f) (f c) := by
  simp only [partialRound, Params.map]
  rw [internalLinear_map]
  congr 1
  ext i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin]
  split <;> simp only [map_pow, map_add]

/-- A ring homomorphism maps a run of the permutation to a run with mapped parameters. -/
theorem permute_map (P : Params F t) (s : Vector F t) :
    (permute P s).map f = permute (P.map f) (s.map f) := by
  have hfull (L : List (Vector F t)) (s : Vector F t) :
      (L.foldl (fullRound P) s).map f =
        (L.map (·.map f)).foldl (fullRound (P.map f)) (s.map f) := by
    induction L generalizing s with
    | nil => rfl
    | cons c L ih => simp only [List.foldl_cons, List.map_cons, ih, fullRound_map]
  have hpart (L : List F) (s : Vector F t) :
      (L.foldl (partialRound P) s).map f = (L.map f).foldl (partialRound (P.map f)) (s.map f) := by
    induction L generalizing s with
    | nil => rfl
    | cons c L ih => simp only [List.foldl_cons, List.map_cons, ih, partialRound_map]
  unfold permute
  rw [hfull, hpart, hfull, externalLinear_map]
  rfl

end Ring

section Field
variable [Field F] [Field K] (f : F →+* K)

theorem width16_map : (KoalaBear.width16 F).map f = KoalaBear.width16 K := by
  simp only [Params.map, KoalaBear.width16, KoalaBear.diagonal16, List.map_map, Function.comp_def,
    Vector.map_map, map_natCast, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
    map_neg, map_inv₀, map_pow, map_ofNat, map_one]

theorem width24_map : (KoalaBear.width24 F).map f = KoalaBear.width24 K := by
  simp only [Params.map, KoalaBear.width24, KoalaBear.diagonal24, List.map_map, Function.comp_def,
    Vector.map_map, map_natCast, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
    map_neg, map_inv₀, map_pow, map_ofNat, map_one]

end Field

open _root_.KoalaBear.Fast (ringEquiv) in
/-- On the Montgomery field the width-16 permutation is the specification. -/
theorem fast_width16 (s : Vector _root_.KoalaBear.Fast.Field 16) :
    (permute (KoalaBear.width16 _) s).map ringEquiv =
      permute (KoalaBear.width16 _root_.KoalaBear.Field) (s.map ringEquiv) := by
  have h := permute_map ringEquiv.toRingHom (KoalaBear.width16 _) s
  rw [width16_map] at h
  exact h

open _root_.KoalaBear.Fast (ringEquiv) in
/-- On the Montgomery field the width-24 permutation is the specification. -/
theorem fast_width24 (s : Vector _root_.KoalaBear.Fast.Field 24) :
    (permute (KoalaBear.width24 _) s).map ringEquiv =
      permute (KoalaBear.width24 _root_.KoalaBear.Field) (s.map ringEquiv) := by
  have h := permute_map ringEquiv.toRingHom (KoalaBear.width24 _) s
  rw [width24_map] at h
  exact h

end CompStark.Poseidon2
