/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Algorithms derived from succinctlabs/flock (flock-core), MIT OR Apache-2.0.
Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum.
Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang.
-/
module
public import CompStark.Pcs.CompactInduction
public import CompPoly.Fields.Binary.AdditiveNTT.Packed.TwiddleRow

/-! Compact normalized subspace rows with three byte subset-sum tables. -/
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
@[expose] public section
namespace CompStark.Pcs
open BF64 AdditiveNTT AdditiveNTT.Packed

/-- The normalized row retained at each additive-transform stage. -/
structure CompactRows (d : Nat) (hd : d < 64) where
  /-- Scalar row coordinates and three subset-sum byte tables per stage. -/
  stages : Vector (Sigma TwiddleRow) d
  /-- Each compact lookup agrees with the complete-domain stage twiddle. -/
  lookup_eq : ∀ (i : Fin d) (block : Fin (2^(d-i.val-1))),
    stages[i].2.lookup block.val = (Packed.stageTwiddles Packed.flatBasis d hd i).getD block.val 0

/-- Normalize one retained stage row and prepare its three byte tables. -/
def compactRow (d : Nat) (hd : d < 64) (i : Fin d) : TwiddleRow (d-i.val-1) :=
  let raw := computableNormalizedWValuesArray (β := Packed.flatBasis) (ℓ := d)
    (R_rate := 0) (h_ℓ_add_R_rate := by omega) i
  TwiddleRow.create _ ⟨raw, by
    simp only [raw, computableNormalizedWValuesArray, Array.size_ofFn, Nat.add_zero]⟩

/-- A retained normalized row represents the exact complete-domain twiddle. -/
theorem compactRow_eq (d : Nat) (hd : d < 64) (i : Fin d) (block : Fin (2^(d-i.val-1))) :
    (compactRow d hd i).lookup block.val =
      (Packed.stageTwiddles Packed.flatBasis d hd i).getD block.val 0 := by
  rw [TwiddleRow.lookup_eq, rowSubset_eq, ← inductionTwiddles_eq]
  simp only [inductionTwiddles, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
    block.isLt, ↓reduceDIte, Option.getD_some, inductionDotLoop_eq, zero_add,
    compactRow, TwiddleRow.create]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.getBit_eq_testBit]
  split <;> rfl

/-- Compute normalized subspace rows without enumerating full-domain twiddle arrays. -/
def CompactRows.create (d : Nat) (hd : d < 64) : CompactRows d hd where
  stages := Vector.ofFn fun i => ⟨d-i.val-1, compactRow d hd i⟩
  lookup_eq i block := by
    have entry : (Vector.ofFn fun j : Fin d => (⟨d-j.val-1, compactRow d hd j⟩ : Sigma TwiddleRow))[i.val] =
        ⟨d-i.val-1, compactRow d hd i⟩ := Vector.getElem_ofFn i.isLt
    exact (congrArg (fun row : Sigma TwiddleRow => row.2.lookup block.val) entry).trans
      (compactRow_eq d hd i block)

/-- Sweep one occupied block at a time with its compact normalized-row lookup. -/
def occupiedSweepRows {k n words rowLength : Nat} (blocks : Vector (Fin k) n) (span : Nat)
    (size : k*(2*span) = words) (offset : Nat) (row : TwiddleRow rowLength)
    (a : BF64.Packed.Buffer words) : BF64.Packed.Buffer words :=
  Fin.foldl n (fun a b =>
    let scalar := row.lookup (offset+blocks[b].val)
    let multiplier := if rowLength < 8 then inductionMultiplier scalar else Packed.Multiplier.masked scalar
    let base := 2*span*blocks[b].val
    Fin.foldl span (fun a c =>
      let lo : Fin words := ⟨c.val+base, by
        have bound := (frontierIndex blocks span size b c 0).isLt
        simpa only [frontierIndex, Fin.val_cast, Fin.val_zero, Nat.mul_zero, Nat.add_zero, base] using bound⟩
      let hi : Fin words := ⟨c.val+span+base, by
        have bound := (frontierIndex blocks span size b c 1).isLt
        simpa only [frontierIndex, Fin.val_cast, Fin.val_one, Nat.mul_one, base] using bound⟩
      let out := transposePair multiplier (BF64.Packed.read a lo) (BF64.Packed.read a hi)
      BF64.Packed.write (BF64.Packed.write a lo out.1) hi out.2) a) a

/-- Sweep a contiguous butterfly block with a specialized scalar multiplication closure. -/
@[specialize] def twiddleBlockSweep {k words : Nat} (block : Fin k) (span : Nat)
    (size : k*(2*span) = words) (applyScalar : Word → Word)
    (a : BF64.Packed.Buffer words) : BF64.Packed.Buffer words :=
  let base := 2*span*block.val
  Fin.foldl span (fun a c =>
    let lo : Fin words := ⟨c.val+base,by dsimp only [base]; have := c.isLt; have := block.isLt; nlinarith⟩
    let hi : Fin words := ⟨c.val+span+base,by dsimp only [base]; have := c.isLt; have := block.isLt; nlinarith⟩
    let total := Word.add (BF64.Packed.read a lo) (BF64.Packed.read a hi)
    let high := Word.add (BF64.Packed.read a hi) (applyScalar total)
    BF64.Packed.write (BF64.Packed.write a lo total) hi high) a

/-- Dispatch scalar multiplication outside the inner window butterfly loop. -/
def occupiedSweepRowsNative {k n words rowLength : Nat} (blocks : Vector (Fin k) n) (span : Nat)
    (size : k*(2*span) = words) (offset : Nat) (row : TwiddleRow rowLength)
    (a : BF64.Packed.Buffer words) : BF64.Packed.Buffer words :=
  Fin.foldl n (fun a b =>
    let scalar := row.lookup (offset+blocks[b].val)
    if rowLength < 8 then
      let map := Sumcheck.byteMap scalar
      twiddleBlockSweep blocks[b] span size (Sumcheck.mapMul map) a
    else twiddleBlockSweep blocks[b] span size (Word.mulMasked scalar) a) a

/-- Arithmetic scalar multiplication is shared across each occupied block. -/
def occupiedSweepRowsScalar {k n words rowLength : Nat} (blocks : Vector (Fin k) n) (span : Nat)
    (size : k*(2*span) = words) (offset : Nat) (row : TwiddleRow rowLength)
    (a : BF64.Packed.Buffer words) : BF64.Packed.Buffer words :=
  Fin.foldl n (fun a b =>
    let scalar := row.lookup (offset+blocks[b].val)
    scalarBlockSweep blocks[b] span size scalar a) a

/-- Hardware-backed products preserve the prepared-map butterfly. -/
@[csimp] theorem occupiedSweepRowsNative_code : @occupiedSweepRowsNative = @occupiedSweepRowsScalar := by
  funext k n words rowLength blocks span size offset row a
  unfold occupiedSweepRowsNative occupiedSweepRowsScalar
  simp only [scalarBlockSweep_eq,twiddleBlockSweep,transposePair,Packed.Multiplier.masked]
  apply congrArg (fun update => Fin.foldl n update a)
  funext input b
  split
  · have same : Sumcheck.mapMul (Sumcheck.byteMap (row.lookup (offset+blocks[b].val))) =
        Word.mulMasked (row.lookup (offset+blocks[b].val)) := by
      funext v
      apply Word.toField_injective
      rw [Sumcheck.mapMul_eq, Sumcheck.byteMap_eq, Word.ByteMap.toField_mul,
        Word.toField_mulMasked]
    rw [same]
  · rfl

/-- Specialized inner multiplication preserves every occupied butterfly and output word. -/
@[csimp] theorem occupiedSweepRows_code : @occupiedSweepRows = @occupiedSweepRowsNative := by
  funext k n words rowLength blocks span size offset row a
  unfold occupiedSweepRows occupiedSweepRowsNative
  apply congrArg (fun update => Fin.foldl n update a)
  funext input b
  dsimp only
  split <;>
    simp only [twiddleBlockSweep,transposePair,inductionMultiplier,Packed.Multiplier.masked]

/-- Inline row lookup agrees with a materialized occupied multiplier vector. -/
theorem occupiedSweepRows_eq {k n words rowLength : Nat} (blocks : Vector (Fin k) n) (span : Nat)
    (size : k*(2*span) = words) (offset : Nat) (row : TwiddleRow rowLength) (a : BF64.Packed.Buffer words) :
    occupiedSweepRows blocks span size offset row a = occupiedSweepBlocks blocks span size
      (Vector.ofFn fun b => if rowLength < 8 then inductionMultiplier (row.lookup (offset+blocks[b].val))
        else Packed.Multiplier.masked (row.lookup (offset+blocks[b].val))) a := by
  unfold occupiedSweepRows occupiedSweepBlocks
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]

/-- An occupied stage stores normalized rows instead of complete-domain multiplier tables. -/
def occupiedStageRows {d count : Nat} {hd : d < 64} (rows : CompactRows d hd) (i : Fin d)
    (lanes : Nat) (positions : Vector (Fin (2^d)) count) (a : BF64.Packed.Buffer (2^d*lanes)) :
    BF64.Packed.Buffer (2^d*lanes) :=
  let blocks := occupiedBlocks i positions
  let cached : Vector _ blocks.length := ⟨blocks.toArray, List.size_toArray⟩
  occupiedSweepRows cached (2^i.val*lanes) (Packed.stage_word_count d i lanes) 0 rows.stages[i].2 a

/-- Compact row lookups preserve every word of an occupied stage. -/
theorem occupiedStageRows_eq {d count : Nat} {hd : d < 64} (rows : CompactRows d hd)
    (plan : Packed.FlatPlan d hd) (i : Fin d) (lanes : Nat)
    (positions : Vector (Fin (2^d)) count) (a : BF64.Packed.Buffer (2^d*lanes)) :
    occupiedStageRows rows i lanes positions a = occupiedStage plan i lanes positions a := by
  let blocks := occupiedBlocks i positions
  let cached : Vector _ blocks.length := ⟨blocks.toArray, List.size_toArray⟩
  have pair (j : Fin (blocks.length*(2^i.val*lanes))) :
      transposePair ((Vector.ofFn fun b : Fin blocks.length =>
        if rows.stages[i].1 < 8 then inductionMultiplier (rows.stages[i].2.lookup cached[b].val)
        else Packed.Multiplier.masked (rows.stages[i].2.lookup cached[b].val))[j.divNat]) =
      transposePair (plan.get i cached[j.divNat]) := by
    funext u v
    apply transposePair_scalar_eq
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    split <;> change rows.stages[i].2.lookup cached[j.divNat].val = (plan.get i cached[j.divNat]).scalar
    all_goals exact (rows.lookup_eq i cached[j.divNat]).trans (plan.scalar_eq i cached[j.divNat]).symm
  unfold occupiedStageRows
  rw [occupiedSweepRows_eq, occupiedSweepBlocks_eq]
  simp only [Nat.zero_add]
  exact congrArg (fun op => Packed.sweep (fun p => Fin.cast (Packed.stage_word_count d i lanes)
    (occupiedIndexCached cached (2^i.val*lanes) p)) op a) (funext pair)

/-- Run occupied transpose stages using compact normalized subspace rows. -/
def occupiedRunRows {d count : Nat} {hd : d < 64} (rows : CompactRows d hd)
    (lanes : Nat) (positions : Vector (Fin (2^d)) count) :
    (steps : Nat) → steps ≤ d → BF64.Packed.Buffer (2^d*lanes) → BF64.Packed.Buffer (2^d*lanes)
  | 0, _, a => a
  | steps+1, bound, a => occupiedStageRows rows ⟨steps, by omega⟩ lanes positions
      (occupiedRunRows rows lanes positions steps (by omega) a)

/-- Compact rows reproduce the complete occupied-stage run. -/
theorem occupiedRunRows_eq {d count : Nat} {hd : d < 64} (rows : CompactRows d hd)
    (plan : Packed.FlatPlan d hd) (lanes : Nat) (positions : Vector (Fin (2^d)) count)
    (steps : Nat) (bound : steps ≤ d) (a : BF64.Packed.Buffer (2^d*lanes)) :
    occupiedRunRows rows lanes positions steps bound a = occupiedRun plan lanes positions steps bound a := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    change occupiedStageRows rows ⟨steps, by omega⟩ lanes positions
      (occupiedRunRows rows lanes positions steps (by omega) a) =
      occupiedStage plan ⟨steps, by omega⟩ lanes positions
        (occupiedRun plan lanes positions steps (by omega) a)
    rw [occupiedStageRows_eq rows plan, ih]

/-- Induce query weights with compact normalized rows and three byte tables per row. -/
def induceOccupiedByteRows {ell rate : Nat} (hd : ell+rate < 64)
    (lanes : Nat) {count : Nat} (positions : Vector (Fin (2^(ell+rate))) count)
    (values : Fin count → Fin lanes → Word) : BF64.Packed.Buffer (2^ell*lanes) :=
  let rows := CompactRows.create (ell+rate) hd
  collapseRows ell rate lanes (occupiedRunRows rows lanes positions ell (by omega)
    (scatterRows _ lanes positions values))

/-- Three-table row preparation retains every coordinate of certified induction. -/
theorem induceOccupiedByteRows_refines {ell rate : Nat} (hd : ell+rate < 64)
    (plan : Packed.FlatPlan (ell+rate) hd) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2^(ell+rate))) count) (values : Fin count → Fin lanes → Word)
    (index : Fin (2^ell*lanes)) :
    BF64.Packed.read (induceOccupiedByteRows hd lanes positions values) index =
      BF64.Packed.read (induceRows hd plan lanes positions values) index := by
  simp only [induceOccupiedByteRows, occupiedRunRows_eq _ plan]
  exact induceOccupiedRows_refines hd plan lanes positions values index

end CompStark.Pcs
