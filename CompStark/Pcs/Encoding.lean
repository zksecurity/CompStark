/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Layout
public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Extension

/-! Bit-plane encoding of cubic-extension rows with shared base-field twiddles. -/

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStark.Pcs
open BF64 AdditiveNTT

/-- Pad each row to the sixty-four base-field lanes consumed by the bit-plane kernel. -/
def padEncodingRows (rows lanes : Nat) (a : BF64.Packed.Buffer (rows * lanes)) :
    Bitsliced.Rows rows :=
  Packed.tabulate _ fun j =>
    if h : j.val % 64 < lanes then
      BF64.Packed.read a ⟨j.val / 64 * lanes + j.val % 64, by
        have hr : j.val / 64 < rows := by have := j.isLt; omega
        nlinarith⟩
    else ⟨0⟩

/-- Remove padding while retaining row order and consecutive extension limbs. -/
def compactEncodingRows (rows lanes : Nat) (h : lanes ≤ 64) (a : Bitsliced.Rows rows) :
    BF64.Packed.Buffer (rows * lanes) :=
  Packed.tabulate _ fun j =>
    BF64.Packed.read a ⟨j.val / lanes * 64 + j.val % lanes, by
      have hl : 0 < lanes := by have := j.isLt; nlinarith
      have hr : j.val / lanes < rows := by
        exact (Nat.div_lt_iff_lt_mul hl).mpr j.isLt
      have hc := Nat.mod_lt j.val hl
      nlinarith⟩

/-- Encode row-major cubic-extension limbs through one shared sixty-four-plane transform.
The physical row holds at most twenty-one extension elements. -/
def encodeExtensionRows {ell rate : Nat} (hd : ell + rate < 64)
    (plan : Bitsliced.Plan Packed.flatBasis (ell + rate) hd) (lanes : Nat)
    (hlanes : 3 * lanes ≤ 64) (a : BF64.Packed.Buffer (2 ^ ell * (3 * lanes)))
    (hn : 8 * (2 ^ (ell + rate) * 64) < 4294967296) :
    BF64.Packed.Buffer (2 ^ (ell + rate) * (3 * lanes)) :=
  let padded := padEncodingRows (2 ^ ell) (3 * lanes) a
  let tiled := Packed.tileRows ell rate 64 padded
  compactEncodingRows _ (3 * lanes) hlanes (Bitsliced.encode plan ell (by omega) tiled hn)

/-- Padding preserves every source lane, including a partial final physical row. -/
theorem laneView_padEncodingRows (rows lanes : Nat) (h : lanes ≤ 64)
    (a : BF64.Packed.Buffer (rows * lanes)) (c : Fin lanes) :
    Packed.laneView (padEncodingRows rows lanes a) (Fin.castLE h c) = Packed.laneView a c := by
  funext r
  dsimp only [Packed.laneView, finProdFinEquiv, Equiv.coe_fn_mk, Fin.castLE]
  simp only [padEncodingRows, Packed.read_tabulate]
  have hm : (c.val + 64 * r.val) % 64 = c.val := by have := c.isLt; omega
  have hd : (c.val + 64 * r.val) / 64 = r.val := by have := c.isLt; omega
  simp only [hm, hd, c.isLt, dite_true]
  congr 1
  apply Fin.ext
  dsimp only [Fin.val_mk]
  nlinarith

/-- Removing padding preserves each retained physical lane. -/
theorem laneView_compactEncodingRows (rows lanes : Nat) (h : lanes ≤ 64)
    (a : Bitsliced.Rows rows) (c : Fin lanes) :
    Packed.laneView (compactEncodingRows rows lanes h a) c =
      Packed.laneView a (Fin.castLE h c) := by
  funext r
  dsimp only [Packed.laneView, finProdFinEquiv, Equiv.coe_fn_mk, Fin.castLE]
  simp only [compactEncodingRows, Packed.read_tabulate]
  have hp : 0 < lanes := by have := c.isLt; omega
  have hm : (c.val + lanes * r.val) % lanes = c.val := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt c.isLt]
  have hd : (c.val + lanes * r.val) / lanes = r.val := by
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt c.isLt, Nat.zero_add]
  simp only [hm, hd]
  congr 1
  apply Fin.ext
  dsimp only [Fin.val_mk]
  nlinarith

/-- The bit-plane driver preserves every base-field lane of the packed scalar transform. -/
theorem bitsliced_encode_lane {ell rate : Nat} (hd : ell + rate < 64)
    (plan : Bitsliced.Plan Packed.flatBasis (ell + rate) hd)
    (a : Bitsliced.Rows (2 ^ (ell + rate)))
    (hn : 8 * (2 ^ (ell + rate) * 64) < 4294967296) (c : Fin 64) :
    Packed.laneView (Bitsliced.encode plan ell (by omega) a hn) c =
      Packed.laneView (Packed.forward plan.toPacked ell (by omega) 64 a) c := by
  funext r
  have index : finProdFinEquiv (r, c) = Bitsliced.wordIndex r c := by
    apply Fin.ext
    change c.val + 64 * r.val = r.val * 64 + c.val
    omega
  change BF64.Packed.read _ (finProdFinEquiv (r, c)) = BF64.Packed.read _ (finProdFinEquiv (r, c))
  rw [index]
  exact Bitsliced.read_encode plan ell (by omega) a hn r c

/-- Each physical extension coefficient is encoded by the exact generic scalar NTT. -/
theorem encodeExtensionRows_coordinate {ell rate : Nat} (hd : ell + rate < 64)
    (plan : Bitsliced.Plan Packed.flatBasis (ell + rate) hd) (lanes : Nat)
    (hlanes : 3 * lanes ≤ 64) (a : BF64.Packed.Buffer (2 ^ ell * (3 * lanes)))
    (hn : 8 * (2 ^ (ell + rate) * 64) < 4294967296) (c : Fin (3 * lanes)) :
    Packed.laneView (encodeExtensionRows hd plan lanes hlanes a hn) c =
      computableAdditiveNTT (𝔽q := ZMod 2) Packed.flatBasis hd (Packed.laneView a c) := by
  let : Fintype Word := Fintype.ofFinite Word
  rw [encodeExtensionRows, laneView_compactEncodingRows, bitsliced_encode_lane]
  rw [Packed.laneView_encodeRows (F := ZMod 2) hd plan.toPacked,
    laneView_padEncodingRows]

/-- Encode only the physical cubic-extension limbs, without padding to sixty-four lanes. -/
def encodeExtensionRowsScalar {ell rate : Nat} (hd : ell + rate < 64)
    (plan : Bitsliced.Plan Packed.flatBasis (ell + rate) hd) (lanes : Nat)
    (hlanes : 3 * lanes ≤ 64) (a : BF64.Packed.Buffer (2 ^ ell * (3 * lanes)))
    (hn : 8 * (2 ^ (ell + rate) * 64) < 4294967296) :
    BF64.Packed.Buffer (2 ^ (ell + rate) * (3 * lanes)) :=
  if hl : 0 < 3 * lanes then
    have hsize : 8 * (2 ^ (ell + rate) * (3 * lanes)) < 4294967296 := by nlinarith
    Packed.Scalar.forward plan ell (by omega) (3 * lanes) hl
      (Packed.Scalar.tileRows ell rate (3 * lanes) hl a hsize) hsize
  else ⟨BF64.Packed.zeros _, rfl⟩

/-- Direct physical-limb encoding preserves every output byte of padded encoding. -/
@[csimp] theorem encodeExtensionRows_code : @encodeExtensionRows = @encodeExtensionRowsScalar := by
  funext ell rate hd plan lanes hlanes a hn
  unfold encodeExtensionRowsScalar
  split
  · rename_i hl
    rw [Packed.Scalar.forward_eq, Packed.Scalar.tileRows_eq]
    apply BF64.Packed.read_ext
    intro j
    let row : Fin (2 ^ (ell + rate)) := ⟨j.val / (3 * lanes),
      (Nat.div_lt_iff_lt_mul hl).mpr j.isLt⟩
    let lane : Fin (3 * lanes) := ⟨j.val % (3 * lanes), Nat.mod_lt _ hl⟩
    have he : finProdFinEquiv (row, lane) = j := by
      apply Fin.ext
      change j.val % (3 * lanes) + (3 * lanes) * (j.val / (3 * lanes)) = j.val
      exact Nat.mod_add_div _ _
    let : Fintype Word := Fintype.ofFinite Word
    have hleft := congrFun (encodeExtensionRows_coordinate hd plan lanes hlanes a hn lane) row
    have hright := congrFun (Packed.laneView_encodeRows (F := ZMod 2)
      hd plan.toPacked (3 * lanes) a lane) row
    simpa only [Packed.laneView, he] using hleft.trans hright.symm
  · rename_i hl
    apply BF64.Packed.read_ext
    intro j
    have hz : 3 * lanes = 0 := by omega
    have hj := j.isLt
    simp only [hz, Nat.mul_zero] at hj
    omega

local instance : Algebra (ZMod 2) Ext3 := ZMod.algebra Ext3 2

/-- Cubic-extension row encoding refines the generic extension-field additive encoder. -/
theorem encodeExtensionRows_refines {ell rate : Nat} (hd : ell + rate < 64)
    (plan : Bitsliced.Plan Packed.flatBasis (ell + rate) hd) (lanes : Nat)
    (hlanes : 3 * lanes ≤ 64) (a : BF64.Packed.Buffer (2 ^ ell * (3 * lanes)))
    (hn : 8 * (2 ^ (ell + rate) * 64) < 4294967296) (lane : Fin lanes) :
    Packed.extensionLaneView (encodeExtensionRows hd plan lanes hlanes a hn) lane =
      computableAdditiveNTT (𝔽q := ZMod 2) Packed.extensionBasis hd
        (Packed.extensionLaneView a lane) := by
  let : Fintype Word := Fintype.ofFinite Word
  funext row
  apply CompPoly.Extension.Ext.ext
  intro c
  change Fin 3 at c
  apply Word.equivField.symm.injective
  change Packed.extensionCoordinate c
    (Packed.extensionLaneView (encodeExtensionRows hd plan lanes hlanes a hn) lane row) =
      Packed.extensionCoordinate c _
  let : Fact (LinearIndependent (ZMod 2) (Packed.extensionScalar ∘ Packed.flatBasis)) :=
    ⟨Packed.extensionBasis_linearIndependent⟩
  have projection := congrFun (computableAdditiveNTT_project (F := ZMod 2)
    (β := Packed.flatBasis) Packed.extensionScalar (Packed.extensionCoordinate c)
    (Packed.extensionCoordinate_add c) (Packed.extensionCoordinate_mul c) hd
    (Packed.extensionLaneView a lane)) row
  change Packed.extensionCoordinate c
    (computableAdditiveNTT (𝔽q := ZMod 2) Packed.extensionBasis hd
      (Packed.extensionLaneView a lane) row) = _ at projection
  rw [projection]
  change (Packed.extensionCoordinate c ∘ Packed.extensionLaneView
    (encodeExtensionRows hd plan lanes hlanes a hn) lane) row = _
  rw [Packed.extensionCoordinate_laneView, Packed.extensionCoordinate_laneView]
  exact congrFun (encodeExtensionRows_coordinate hd plan lanes hlanes a hn
    ⟨3 * lane.val + c.val, by omega⟩) row

end CompStark.Pcs
