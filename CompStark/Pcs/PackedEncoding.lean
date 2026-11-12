/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.FastEncoding
public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Layout
public import CompPoly.Fields.Binary.AdditiveNTT.Packed.FlatBasis
public import CompPoly.Fields.Binary.AdditiveNTT.ScalarExtension
/-! Shared packed base-field transforms for decoded interleaved candidates. -/

set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
@[expose] public section
namespace CompStark.Pcs
open CompStark.BinaryFields BF64 AdditiveNTT

/-- Pack every base-field candidate lane in row-major novel coefficient order. -/
def packedEncodingInput (vars lanes : Nat) (f : Whir.Table K (lanes + vars)) :
    BF64.Packed.Buffer (2 ^ vars * 2 ^ lanes) :=
  BF64.Packed.ofFn _ fun j =>
    let pair := finProdFinEquiv.symm j
    Word.ofField (f (Fin.addCases (mask lanes pair.2) (mask vars pair.1)))

/-- Encode every candidate lane using one shared packed transform plan. -/
@[noinline, nospecialize] def packedEncodingRows (phi : K →+* K) (vars rate lanes : Nat) (h : vars + rate < 64)
    (f : Whir.Table K (lanes + vars)) : Vector (Array K) (2 ^ lanes) :=
  let beta := fun j => Word.ofField (phi (basis j))
  let plan := Packed.Plan.create beta (vars + rate) h
  let input := packedEncodingInput vars lanes f
  let encoded := Packed.forward plan vars (by omega) (2 ^ lanes) (Packed.tileRows vars rate _ input)
  Vector.ofFn fun row => Array.ofFn fun x : Fin (2 ^ (vars + rate)) =>
    (Packed.laneView encoded row x).toField

/-- Shared packed rows preserve the exact ordered base-field encoder in every column. -/
theorem packedEncodingRows_correct (phi : K →+* K) (vars rate lanes : Nat)
    (h : vars + rate < 64) (f : Whir.Table K (lanes + vars))
    (row : Fin (2 ^ lanes)) (x : Fin (2 ^ (vars + rate))) :
    ((packedEncodingRows phi vars rate lanes h f)[row.val]).getD x.val 0 =
      (encoding vars rate h.le).encode phi (fun u => f (Fin.addCases (mask lanes row) u)) x := by
  let _ : Fintype Word := Fintype.ofFinite Word
  let beta : Fin 64 → K := fun j => phi (basis j)
  let rho : K →+* Word := Word.ringEquiv.symm.toRingHom
  let : Fact (LinearIndependent (ZMod 2) beta) := ⟨extendedBasis_independent phi⟩
  let : Fact (LinearIndependent (ZMod 2) (rho ∘ beta)) :=
    ⟨extendedBasis_independent (rho.comp phi)⟩
  let input := packedEncodingInput vars lanes f
  let plan := Packed.Plan.create (rho ∘ beta) (vars + rate) h
  have projected := computableAdditiveNTT_project (F := ZMod 2) (β := beta)
    rho Word.toField (fun a b => Word.toField_add a b)
    (fun a b => by
      change Word.ringEquiv (Word.ringEquiv.symm a * b) = a * Word.ringEquiv b
      rw [map_mul, RingEquiv.apply_symm_apply]) h (Packed.laneView input row)
  have source : Word.toField ∘ Packed.laneView input row =
      (fun i => f (Fin.addCases (mask lanes row) (mask vars i))) := by
    funext i
    simp only [Function.comp_apply, input, packedEncodingInput, Packed.laneView, BF64.Packed.read_ofFn,
      Equiv.symm_apply_apply, Word.toField_ofField]
  have transformed := congrFun projected x
  rw [source] at transformed
  change _ = computableAdditiveNTT (𝔽q := ZMod 2) (fun j => phi (basis j)) h
    (fun i => f (Fin.addCases (mask lanes row) (mask vars i))) x at transformed
  rw [computableAdditiveNTT_eq_encode phi vars rate h (fun u => f (Fin.addCases (mask lanes row) u))] at transformed
  change ((Vector.ofFn fun row : Fin (2 ^ lanes) => Array.ofFn fun x : Fin (2 ^ (vars + rate)) =>
    (Packed.laneView (Packed.forward plan vars (by omega) (2 ^ lanes)
      (Packed.tileRows vars rate _ input)) row x).toField)[row.val]).getD x.val 0 = _
  simp only [Vector.getElem_ofFn, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
    dite_eq_left x.isLt, Option.getD_some]
  rw [Packed.laneView_encodeRows (F := ZMod 2) h]
  exact transformed
end CompStark.Pcs
