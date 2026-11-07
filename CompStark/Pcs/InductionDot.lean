/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.DenseInduction

/-! Direct scalar accumulation for split-tensor induction. -/
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
@[expose] public section
namespace CompStark.Pcs
open BF64

/-- Accumulate query products directly, specializing the coordinate-producing function. -/
@[specialize] def inductionDotLoop (count : Nat) (f : Fin count → Word)
    (left : Nat) (bound : left ≤ count) (acc : Word) : Word :=
  match left with
  | 0 => acc
  | left+1 => inductionDotLoop count f left (by omega) (Word.add acc (f ⟨left, by omega⟩))
termination_by structural left

/-- Direct scalar accumulation is the finite sum of its remaining query coordinates. -/
theorem inductionDotLoop_eq (count : Nat) (f : Fin count → Word)
    (left : Nat) (bound : left ≤ count) (acc : Word) :
    inductionDotLoop count f left bound acc = acc + ∑ i : Fin left, f ⟨i.val, by omega⟩ := by
  induction left generalizing acc with
  | zero =>
    rw [inductionDotLoop]
    simp only [Fin.sum_univ_zero, add_zero]
  | succ left ih =>
    rw [inductionDotLoop, ih, Fin.sum_univ_castSucc]
    change (acc + f ⟨left, by omega⟩) + ∑ i : Fin left, f ⟨i.val, by omega⟩ =
      acc + ((∑ i : Fin left, f ⟨i.val, by omega⟩) + f ⟨left, by omega⟩)
    ac_rfl

/-- Split matrices reconstruct their packed output without a list of query products. -/
def splitDotRowsNative (lo hi lanes count : Nat)
    (low : Vector (Vector Word (2^lo)) count)
    (scaled : Vector (Vector (Vector Word lanes) count) (2^hi)) :
    BF64.Packed.Buffer (2^(lo+hi)*lanes) :=
  AdditiveNTT.Packed.tabulate _ fun i =>
    let row : Fin (2^(lo+hi)) := i.divNat
    let h : Fin (2^hi) := ⟨row.val/2^lo, by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
      simpa only [pow_add, Nat.mul_comm] using row.isLt⟩
    let l : Fin (2^lo) := ⟨row.val%2^lo, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
    let c : Fin lanes := i.modNat
    inductionDotLoop count (fun q => Word.mulMasked scaled[h][q][c] low[q][l]) count (Nat.le_refl _) 0

/-- Direct accumulation preserves the complete certified split-tensor output buffer. -/
@[csimp] theorem splitDotRows_code : @splitDotRows = @splitDotRowsNative := by
  funext lo hi lanes count low scaled
  unfold splitDotRows splitDotRowsNative
  congr 1
  funext i
  rw [inductionDotLoop_eq, zero_add]
  rfl

/-- Dense induction with direct accumulation in the split matrix reconstruction. -/
def induceSplitRowsFast (lo hi rate : Nat) (hd : lo+hi+rate < 64) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2^(lo+hi+rate))) count) (values : Fin count → Fin lanes → Word) :
    BF64.Packed.Buffer (2^(lo+hi)*lanes) :=
  let constants := inductionConstants (lo+hi) (by omega)
  let factors := positions.map (inductionFactors (by omega) hd constants)
  let low := factors.map fun f => novelTensor lo (Vector.ofFn fun k => f[k.val])
  let high := factors.map fun f => novelTensor hi (Vector.ofFn fun k => f[lo+k.val]'(by have := k.isLt; omega))
  let scaled := Vector.ofFn fun h : Fin (2^hi) => Vector.ofFn fun q : Fin count =>
    Vector.ofFn fun c : Fin lanes => values q c * high[q][h]
  splitDotRowsNative lo hi lanes count low scaled

/-- The compiled dense entry point uses the proven direct accumulator. -/
@[csimp] theorem induceSplitRows_code : @induceSplitRows = @induceSplitRowsFast := by
  funext lo hi rate hd lanes count positions values
  unfold induceSplitRows induceSplitRowsFast
  rw [splitDotRows_code]

end CompStark.Pcs
