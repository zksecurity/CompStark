/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.Decoder
public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Encoder
set_option autoImplicit false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
@[expose] public section
namespace CompStark.Pcs
open CompStark.BinaryFields CompPoly AdditiveNTT BF64

/-- The native flat basis is the protocol's ordered polynomial basis. -/
theorem packedBasis_toField (i : Fin 64) : (Packed.flatBasis i).toField = basis i := by
  rw [Packed.flatBasis_toField]
  have h : ∀ j : Fin 64, BF64.binaryBasisVector j = basis j := by decide +kernel
  exact h i

noncomputable local instance packedCodewordWordFintype : Fintype Word := Fintype.ofFinite Word
local instance : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- Changing an equal basis preserves the complete native transform. -/
theorem wordTransform_congr (vars rate : Nat) (hd : vars+rate < 64)
    (beta gamma : Fin 64 → Word) [Fact (LinearIndependent (ZMod 2) beta)]
    [Fact (LinearIndependent (ZMod 2) gamma)] (same : beta = gamma)
    (source : Fin (2^vars) → Word) :
    computableAdditiveNTT (𝔽q := ZMod 2) beta hd source =
      computableAdditiveNTT (𝔽q := ZMod 2) gamma hd source := by
  subst gamma
  rfl

/-- The word transform is exactly the mathematical base-field encoder. -/
theorem baseTransform_refines (vars rate : Nat) (hd : vars+rate < 64)
    (source : Fin (2^vars) → Word) :
    (fun x => (computableAdditiveNTT (𝔽q := ZMod 2) Packed.flatBasis hd source x).toField) =
      (encoding vars rate hd.le).encode (RingHom.id K)
        (fun u => (source (cubeIndex vars u)).toField) := by
  let phi : K →+* Word := Word.ringEquiv.symm.toRingHom
  have bases : phi ∘ basis = Packed.flatBasis := by
    funext i
    apply Word.toField_injective
    change (Word.ofField (basis i)).toField = (Packed.flatBasis i).toField
    rw [Word.toField_ofField, packedBasis_toField]
  let : Fact (LinearIndependent (ZMod 2) (phi ∘ basis)) :=
    ⟨by rw [bases]; exact Packed.flatBasis_linearIndependent⟩
  have additive (a b : Word) : (a+b).toField = a.toField+b.toField :=
    Word.ringEquiv.map_add a b
  have scalar (a : K) (b : Word) : (phi a*b).toField = a*b.toField := by
    change Word.ringEquiv (Word.ringEquiv.symm a*b) = a*Word.ringEquiv b
    rw [map_mul, RingEquiv.apply_symm_apply]
  have transported := computableAdditiveNTT_project (F := ZMod 2)
    (β := basis) phi Word.toField additive scalar hd source
  have native : (fun x => (computableAdditiveNTT (𝔽q := ZMod 2) Packed.flatBasis hd source x).toField) =
      computableAdditiveNTT (𝔽q := ZMod 2) basis hd (fun i => (source i).toField) := by
    have basisChange := wordTransform_congr vars rate hd (phi ∘ basis) Packed.flatBasis bases source
    exact (congrArg (fun transform => Word.toField ∘ transform) basisChange.symm).trans transported
  have interpreted := computableAdditiveNTT_eq_encode (RingHom.id K)
    vars rate hd (fun u => (source (cubeIndex vars u)).toField)
  have input : (fun i => (source (cubeIndex vars (mask vars i))).toField) =
      (fun i => (source i).toField) := by
    funext i
    rw [show cubeIndex vars (mask vars i) = i from (cubeEquiv vars).symm_apply_apply i]
  rw [input] at interpreted
  exact native.trans interpreted

/-- Read a row-major coefficient buffer in the protocol's lane-first variable order. -/
def packedBaseTable (vars lanes : Nat) (a : BF64.Packed.Buffer (2 ^ vars * 2 ^ lanes)) :
    Whir.Table K (lanes + vars) := fun u =>
  (Packed.laneView a (cubeIndex lanes (fun i => u (Fin.castAdd vars i)))
    (cubeIndex vars (fun i => u (Fin.natAdd lanes i)))).toField

/-- Re-encode recovered coefficients together through one packed transform. -/
@[macro_inline] def packedBaseWord (vars rate lanes : Nat) (hd : vars+rate < 64)
    (a : BF64.Packed.Buffer (2 ^ vars * 2 ^ lanes)) : Whir.Word K lanes (2 ^ (vars + rate)) :=
  let plan := Packed.Plan.create Packed.flatBasis (vars + rate) hd
  let encoded := Packed.encodeRows plan (2 ^ lanes) a
  fun x row => (Packed.laneView encoded (cubeIndex lanes row) x).toField

/-- Packed forward rows preserve every column and lane of the protocol codeword. -/
theorem packedBaseWord_eq (vars rate lanes : Nat) (hd : vars+rate < 64)
    (a : BF64.Packed.Buffer (2 ^ vars * 2 ^ lanes)) :
    packedBaseWord vars rate lanes hd a =
      (encoding vars rate hd.le).interleave (RingHom.id K) (packedBaseTable vars lanes a) := by
  funext x row
  unfold packedBaseWord
  rw [Packed.encodeRows, Packed.laneView_encodeRows (F := ZMod 2) hd]
  have bridge := congrFun (baseTransform_refines vars rate hd (Packed.laneView a (cubeIndex lanes row))) x
  refine bridge.trans ?_
  unfold Whir.Encoding.interleave packedBaseTable
  simp only [Fin.addCases_left, Fin.addCases_right]

/-- Check every numeric column and lane without constructing Boolean-function enumerations. -/
def packedCodewordCheck (vars rate lanes : Nat) (hd : vars+rate < 64)
    (word : Whir.Word K lanes (2 ^ (vars + rate)))
    (a : BF64.Packed.Buffer (2 ^ vars * 2 ^ lanes)) : Bool :=
  let encoded := packedBaseWord vars rate lanes hd a
  (List.finRange (2 ^ (vars+rate))).all fun x =>
    (List.finRange (2 ^ lanes)).all fun row => decide (word x (mask lanes row) = encoded x (mask lanes row))

/-- Complete packed comparison is exactly equality with the mathematical codeword. -/
theorem packedCodewordCheck_eq (vars rate lanes : Nat) (hd : vars+rate < 64)
    (word : Whir.Word K lanes (2 ^ (vars + rate)))
    (a : BF64.Packed.Buffer (2 ^ vars * 2 ^ lanes)) :
    packedCodewordCheck vars rate lanes hd word a =
      decide (word = (encoding vars rate hd.le).interleave (RingHom.id K) (packedBaseTable vars lanes a)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [packedCodewordCheck, packedBaseWord_eq, List.all_eq_true,
    List.mem_finRange, forall_true_left, decide_eq_true_eq]
  constructor
  · intro same
    funext x row
    simpa only [mask_cubeIndex] using same x (cubeIndex lanes row)
  · intro same x row
    exact congrFun (congrFun same x) (mask lanes row)

end CompStark.Pcs
