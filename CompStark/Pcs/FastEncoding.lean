/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.AdditiveEncoding
public import CompPoly.Fields.Binary.AdditiveNTT.Correctness
@[expose] public section
namespace CompStark.Pcs
open CompStark.BinaryFields Polynomial
variable {S : Type} [Field S]

/-- Encode a complete scalar row with cached additive-NTT butterflies. -/
def encodeArray (phi : K →+* S) (vars rate : ℕ) (h : vars + rate < 64)
    (f : Whir.Table S vars) : Array S :=
  AdditiveNTT.computableAdditiveNTTFast (β := fun j => phi (basis j))
    (ℓ := vars) (R_rate := rate) (h_ℓ_add_R_rate := h) (fun i => f (mask vars i))

/-- The butterfly array has exactly the scalar encoder's value in every column. -/
theorem encodeArray_correct [Fintype S] [DecidableEq S] [Algebra (ZMod 2) S]
    (phi : K →+* S) (vars rate : ℕ) (h : vars + rate < 64) (f : Whir.Table S vars)
    (x : Fin (2 ^ (vars + rate))) :
    (encodeArray phi vars rate h f).getD x.val 0 =
      (encoding vars rate (Nat.le_of_lt h)).encode phi f x := by
  exact congrFun ((AdditiveNTT.computableAdditiveNTTFast_eq_computableAdditiveNTT
    (𝔽q := ZMod 2) (β := fun j => phi (basis j)) (ℓ := vars) (R_rate := rate)
    (h_ℓ_add_R_rate := h) (fun i => f (mask vars i))).trans
      (computableAdditiveNTT_eq_encode phi vars rate h f)) x

/-- Encode on an isomorphic executable field and transport each output coefficient back. -/
def encodeArrayMapped {T : Type} [Field T] (e : S ≃+* T) (phi : K →+* S)
    (vars rate : Nat) (h : vars + rate < 64) (f : Whir.Table S vars) : Array S :=
  (encodeArray (e.toRingHom.comp phi) vars rate h (fun u => e (f u))).map e.symm

/-- Carrier transport preserves every encoded column of the exact specification. -/
theorem encodeArrayMapped_correct [Fintype S] [Algebra (ZMod 2) S]
    {T : Type} [Field T] (e : S ≃+* T) (phi : K →+* S)
    (vars rate : Nat) (h : vars + rate < 64) (f : Whir.Table S vars)
    (x : Fin (2 ^ (vars + rate))) :
    (encodeArrayMapped e phi vars rate h f).getD x.val 0 =
      (encoding vars rate (Nat.le_of_lt h)).encode phi f x := by
  classical
  let : Fintype T := Fintype.ofEquiv S e.toEquiv
  let : Algebra (ZMod 2) T := (e.toRingHom.comp (algebraMap (ZMod 2) S)).toAlgebra
  have get (a : Array T) (i : Nat) : (a.map e.symm).getD i 0 = e.symm (a.getD i 0) := by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases a[i]? <;> simp only [Option.map_none, Option.map_some, Option.getD_none,
      Option.getD_some, map_zero]
  rw [encodeArrayMapped, get, encodeArray_correct]
  apply e.injective
  rw [e.apply_symm_apply]
  simp only [Whir.Encoding.encode, RingHom.comp_apply, map_sum, map_mul]
  rfl

/-- Materialize every encoded scalar row once and share it across column comparisons. -/
@[macro_inline] def interleaveFast (phi : K →+* S) (vars rate lanes : ℕ) (h : vars + rate < 64)
    (f : Whir.Table S (lanes + vars)) : Whir.Word S lanes (2 ^ (vars + rate)) :=
  let rows := Vector.ofFn fun i : Fin (2 ^ lanes) =>
    encodeArray phi vars rate h (fun v => f (Fin.addCases (mask lanes i) v))
  fun x row => (rows[((cubeEquiv lanes).symm row).val]).getD x.val 0

/-- Shared butterfly rows are exactly the mathematical interleaved encoding. -/
theorem interleaveFast_correct [Fintype S] [DecidableEq S] [Algebra (ZMod 2) S]
    (phi : K →+* S) (vars rate lanes : ℕ) (h : vars + rate < 64)
    (f : Whir.Table S (lanes + vars)) :
    interleaveFast phi vars rate lanes h f = (encoding vars rate (Nat.le_of_lt h)).interleave phi f := by
  funext x row
  simp only [interleaveFast, Vector.getElem_ofFn, encodeArray_correct,
    ← cubeEquiv_apply, Fin.eta, Equiv.apply_symm_apply, Whir.Encoding.interleave]

/-- The base-field butterfly array is the encoder's value in every column. -/
theorem encodeArrayBase_correct (vars rate : ℕ) (h : vars + rate < 64) (f : Whir.Table K vars)
    (x : Fin (2 ^ (vars + rate))) :
    (encodeArray (RingHom.id K) vars rate h f).getD x.val 0 =
      (encoding vars rate (Nat.le_of_lt h)).encode (RingHom.id K) f x := by
  let : Algebra (ZMod 2) K := (ZMod.castHom (by decide) K).toAlgebra
  exact encodeArray_correct (RingHom.id K) vars rate h f x

/-- The extension-field butterfly array is the encoder's value in every column. -/
theorem encodeArrayExtension_correct (vars rate : ℕ) (h : vars + rate < 64) (f : Whir.Table E vars)
    (x : Fin (2 ^ (vars + rate))) :
    (encodeArray (algebraMap K E) vars rate h f).getD x.val 0 =
      (encoding vars rate (Nat.le_of_lt h)).encode (algebraMap K E) f x := by
  let : Algebra (ZMod 2) E := (ZMod.castHom (by decide) E).toAlgebra
  let : Fintype E := Fintype.ofFinite E
  exact encodeArray_correct (algebraMap K E) vars rate h f x

/-- Encode all candidate lanes through their executable scalar-field carrier. -/
def scalarEncodingRows {T : Type} [Field T] (e : S ≃+* T) (phi : K →+* S)
    (vars rate lanes : Nat) (h : vars + rate < 64) (f : Whir.Table S (lanes + vars)) :
    Vector (Array S) (2 ^ lanes) :=
  Vector.ofFn fun row : Fin (2 ^ lanes) =>
    encodeArrayMapped e phi vars rate h (fun u => f (Fin.addCases (mask lanes row) u))

/-- Scalar carrier row images preserve every mathematical encoded column. -/
theorem scalarEncodingRows_correct [Fintype S] [DecidableEq S] [Algebra (ZMod 2) S]
    {T : Type} [Field T] (e : S ≃+* T) (phi : K →+* S) (vars rate lanes : Nat)
    (h : vars + rate < 64) (f : Whir.Table S (lanes + vars))
    (row : Fin (2 ^ lanes)) (x : Fin (2 ^ (vars + rate))) :
    ((scalarEncodingRows e phi vars rate lanes h f)[row.val]).getD x.val 0 =
      (encoding vars rate h.le).encode phi (fun u => f (Fin.addCases (mask lanes row) u)) x := by
  simp only [scalarEncodingRows, Vector.getElem_ofFn, encodeArrayMapped_correct]

end CompStark.Pcs
