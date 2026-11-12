/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.FastEncoding
public import CompStark.Pcs.Encoding

/-! Native bit-plane encoding of production extension-field rows. -/

set_option maxHeartbeats 400000
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStark.Pcs.Prover.Encoding
open CompStark.BinaryFields AdditiveNTT

/-- The pinned word basis agrees with the protocol's ordered generator powers. -/
theorem flatBasis_eq (i : Fin 64) : (Packed.flatBasis i).toField = Pcs.basis i := by
  rw [Packed.flatBasis_toField]
  have h : ∀ j : Fin 64, BF64.binaryBasisVector j = Pcs.basis j := by decide +kernel
  exact h i

/-- The native constant extension basis is the protocol basis after scalar extension. -/
theorem extensionBasis_eq : Packed.extensionBasis = fun i => (algebraMap K E) (Pcs.basis i) := by
  funext i
  change (algebraMap K E) ((Packed.flatBasis i).toField) = _
  rw [flatBasis_eq]

/-- Interpret consecutive physical extension limbs as the protocol's Boolean message table. -/
def message {vars lanes : Nat} (a : BF64.Packed.Buffer (2 ^ vars * (3 * 2 ^ lanes))) :
    Whir.Table E (lanes + vars) := fun u =>
  Packed.extensionLaneView a (Pcs.cubeIndex lanes (fun i => u (Fin.castAdd vars i)))
    (Pcs.cubeIndex vars (fun i => u (Fin.natAdd lanes i)))

/-- Encode physical extension rows once and expose the resulting protocol word. -/
@[macro_inline] def encode {vars rate lanes : Nat} (h : vars + rate < 64)
    (plan : Bitsliced.Plan Packed.flatBasis (vars + rate) h) (hlanes : 3 * 2 ^ lanes ≤ 64)
    (a : BF64.Packed.Buffer (2 ^ vars * (3 * 2 ^ lanes)))
    (hn : 8 * (2 ^ (vars + rate) * 64) < 4294967296) :
    Whir.Word E lanes (2 ^ (vars + rate)) :=
  let encoded := CompStark.Pcs.encodeExtensionRows (ell := vars) (rate := rate) h plan (2 ^ lanes) hlanes a hn
  fun x row => Packed.extensionLaneView encoded (Pcs.cubeIndex lanes row) x

noncomputable local instance : Fintype E := Fintype.ofFinite E
local instance : Algebra (ZMod 2) E := ZMod.algebra E 2

/-- Equal ordered bases produce equal executable additive transforms. -/
theorem ntt_congr {vars rate : Nat} (h : vars + rate < 64)
    (β γ : Fin 64 → E) [Fact (LinearIndependent (ZMod 2) β)]
    [Fact (LinearIndependent (ZMod 2) γ)] (eq : β = γ) (a : Fin (2 ^ vars) → E) :
    AdditiveNTT.computableAdditiveNTT (𝔽q := ZMod 2) β h a =
      AdditiveNTT.computableAdditiveNTT (𝔽q := ZMod 2) γ h a := by
  subst γ
  rfl

/-- Native bit-plane rows are exactly the mathematical interleaved WHIR encoding. -/
theorem encode_refines {vars rate lanes : Nat} (h : vars + rate < 64)
    (plan : Bitsliced.Plan Packed.flatBasis (vars + rate) h) (hlanes : 3 * 2 ^ lanes ≤ 64)
    (a : BF64.Packed.Buffer (2 ^ vars * (3 * 2 ^ lanes)))
    (hn : 8 * (2 ^ (vars + rate) * 64) < 4294967296) :
    encode (vars := vars) (rate := rate) (lanes := lanes) h plan hlanes a hn = (Pcs.encoding vars rate h.le).interleave (algebraMap K E) (message (vars := vars) (lanes := lanes) a) := by
  funext x row
  have native := congrFun (CompStark.Pcs.encodeExtensionRows_refines (ell := vars) (rate := rate) h plan (2 ^ lanes)
    hlanes a hn (Pcs.cubeIndex lanes row)) x
  have basisChange := congrFun (ntt_congr (vars := vars) (rate := rate) h Packed.extensionBasis
    (fun i => (algebraMap K E) (Pcs.basis i)) extensionBasis_eq
    (Packed.extensionLaneView a (Pcs.cubeIndex lanes row))) x
  have result := native.trans basisChange
  refine result.trans ?_
  have source : (fun j => message (vars := vars) (lanes := lanes) a (Fin.addCases row (Pcs.mask vars j))) =
      Packed.extensionLaneView a (Pcs.cubeIndex lanes row) := by
    funext j
    simp only [message, Fin.addCases_left, Fin.addCases_right]
    congr 1
    exact (Pcs.cubeEquiv vars).left_inv j
  rw [← source]
  have bridge := congrFun (Pcs.computableAdditiveNTT_eq_encode (algebraMap K E) vars rate h
    (fun v => message (vars := vars) (lanes := lanes) a (Fin.addCases row v))) x
  exact bridge

end CompStark.Pcs.Prover.Encoding
