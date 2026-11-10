/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Algorithms derived from succinctlabs/flock (flock-core), MIT OR Apache-2.0.
Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum.
Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang.
-/
module
public import CompStark.Pcs.SparseInduction
public import CompStark.Sumcheck.Buffer

/-! Query-local twiddle preparation for occupied transposed transforms. -/
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
@[expose] public section
namespace CompStark.Pcs
open BF64 AdditiveNTT

/-- Prepare only the multipliers selected by the occupied blocks of one stage. -/
def occupiedMultipliers (d : Nat) (hd : d < 64) (i : Fin d) {n : Nat}
    (blocks : Vector (Fin (2^(d-i.val-1))) n) : Vector Packed.Multiplier n :=
  let values := computableNormalizedWValuesArray (β := Packed.flatBasis) (ℓ := d)
    (R_rate := 0) (h_ℓ_add_R_rate := by omega) i
  blocks.map fun block =>
    let scalar := inductionDotLoop (d-i.val-1) (fun k =>
      if Nat.getBit k.val block.val = 1 then values.getD k.val 0 else 0)
      (d-i.val-1) (Nat.le_refl _) 0
    if d-i.val-1 < 8 then inductionMultiplier scalar else Packed.Multiplier.masked scalar

/-- Query-local preparation retains each selected generic stage twiddle. -/
theorem occupiedMultipliers_scalar (d : Nat) (hd : d < 64) (i : Fin d) {n : Nat}
    (blocks : Vector (Fin (2^(d-i.val-1))) n) (j : Fin n) :
    (occupiedMultipliers d hd i blocks)[j].scalar =
      (Packed.stageTwiddles Packed.flatBasis d hd i).getD blocks[j].val 0 := by
  rw [← inductionTwiddles_eq]
  simp only [inductionTwiddles, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
    blocks[j].isLt, ↓reduceDIte, Option.getD_some]
  simp only [occupiedMultipliers, Fin.getElem_fin, Vector.getElem_map]
  split <;> simp only [inductionMultiplier, Packed.Multiplier.masked, Array.getD_eq_getD_getElem?]

/-- Certified multiplication depends only on its retained scalar. -/
theorem transposePair_scalar_eq (a b : Packed.Multiplier) (same : a.scalar = b.scalar)
    (u v : Word) : transposePair a u v = transposePair b u v := by
  have apply_eq (w : Word) : a.apply w = b.apply w := by
    apply Word.toField_injective
    rw [a.correct, b.correct, same]
  simp only [transposePair, apply_eq]

/-- Increasing blocked folds retain the flattened row-major traversal. -/
private theorem foldl_blocks {α : Type} (blocks span : Nat) (f : α → Fin (blocks*span) → α) (a : α) :
    Fin.foldl blocks (fun a b => Fin.foldl span (fun a j =>
      f a ⟨b.val*span+j.val, by have := b.isLt; have := j.isLt; nlinarith⟩) a) a =
    Fin.foldl (blocks*span) f a := by
  induction blocks with
  | zero => simp only [Nat.zero_mul, Fin.foldl_zero]
  | succ blocks ih =>
    rw [Fin.foldl_succ_last]
    have old := ih (fun a j => f a ⟨j.val, by have := j.isLt; rw [Nat.succ_mul]; omega⟩)
    simp only [Fin.val_castSucc] at old ⊢
    rw [old]
    conv_rhs => rw [Fin.foldl_congr (Nat.succ_mul blocks span) f, Fin.foldl_add]
    rfl

/-- Address one side of a butterfly using a fixed block base and an inner column. -/
@[inline] def frontierIndex {k n words : Nat} (blocks : Vector (Fin k) n) (span : Nat)
    (size : k*(2*span) = words) (b : Fin n) (c : Fin span) (side : Fin 2) : Fin words :=
  Fin.cast size ⟨c.val+span*side.val+2*span*blocks[b].val, by
    have := c.isLt
    have := side.isLt
    have := blocks[b].isLt
    nlinarith⟩

/-- Flattened block/column coordinates recover the cached parent block. -/
private theorem frontierPair_divNat (n span : Nat) (b : Fin n) (c : Fin span) :
    (⟨b.val*span+c.val, by have := b.isLt; have := c.isLt; nlinarith⟩ : Fin (n*span)).divNat = b := by
  have positive : 0 < span := by have := c.isLt; omega
  apply Fin.ext
  change (b.val*span+c.val)/span = b.val
  rw [Nat.mul_comm b.val span, Nat.mul_add_div positive,
    Nat.div_eq_of_lt c.isLt, Nat.add_zero]

/-- Fixed block-base addressing agrees with the flattened occupied-pair address. -/
theorem frontierIndex_eq {k n words : Nat} (blocks : Vector (Fin k) n) (span : Nat)
    (size : k*(2*span) = words) (b : Fin n) (c : Fin span) (side : Fin 2) :
    frontierIndex blocks span size b c side = Fin.cast size
      (occupiedIndexCached blocks span
        ((⟨b.val*span+c.val, by have := b.isLt; have := c.isLt; nlinarith⟩ : Fin (n*span)),side)) := by
  apply Fin.ext
  simp only [frontierIndex, occupiedIndexCached, Fin.val_cast, frontierPair_divNat]
  change c.val+span*side.val+2*span*blocks[b].val =
    (b.val*span+c.val)%span+span*side.val+2*span*blocks[b].val
  rw [Nat.mul_add_mod_of_lt c.isLt]

/-- Traverse one occupied block at a time, sharing its multiplier across the inner loop. -/
def occupiedSweepBlocks {k n words : Nat} (blocks : Vector (Fin k) n) (span : Nat)
    (size : k*(2*span) = words) (multipliers : Vector Packed.Multiplier n)
    (a : BF64.Packed.Buffer words) : BF64.Packed.Buffer words :=
  Fin.foldl n (fun a b =>
    let multiplier := multipliers[b]
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

/-- Fixed-length byte storage carried directly by the butterfly loop. -/
abbrev InductionBytes (words : Nat) := {bytes : ByteArray // bytes.size = 8*words}

/-- Restore the certified word view once at a butterfly-block boundary. -/
@[inline] def InductionBytes.buffer {words : Nat} (bytes : InductionBytes words) : BF64.Packed.Buffer words :=
  ⟨⟨words,bytes.val,bytes.property⟩,rfl⟩

/-- Retain only the physical byte array inside a butterfly block. -/
@[inline] def InductionBytes.ofBuffer {words : Nat} (a : BF64.Packed.Buffer words) : InductionBytes words :=
  ⟨a.val.bytes,by rw [a.val.byteSize,a.property]⟩

/-- The physical byte view preserves every certified buffer. -/
theorem InductionBytes.buffer_ofBuffer {words : Nat} (a : BF64.Packed.Buffer words) :
    (InductionBytes.ofBuffer a).buffer = a := by
  rcases a with ⟨⟨size,bytes,h⟩,equal⟩
  dsimp only at equal
  subst size
  rfl

/-- Update a butterfly while carrying no runtime word-buffer constructor. -/
@[inline] def InductionBytes.butterfly {words : Nat} (bytes : InductionBytes words)
    (lo hi : Fin words) (scalar : Word) : InductionBytes words :=
  let a := bytes.buffer
  let total := Word.add (BF64.Packed.read a lo) (BF64.Packed.read a hi)
  let high := Word.add (BF64.Packed.read a hi) (Word.mulMasked scalar total)
  InductionBytes.ofBuffer (BF64.Packed.write (BF64.Packed.write a lo total) hi high)

/-- Load and store butterflies with the approved bounded native word accessors. -/
@[inline] def InductionBytes.butterflyIndices {words : Nat} (native : 8*words < USize.size)
    (bytes : InductionBytes words) (lo hi : USize) (low : lo.toNat < words) (high : hi.toNat < words)
    (scalar : Word) : InductionBytes words :=
  let a := bytes.buffer
  let u := Sumcheck.readWord a lo low native
  let v := Sumcheck.readWord a hi high native
  let total := Word.add u v
  let bot := Word.add v (Word.mulMasked scalar total)
  InductionBytes.ofBuffer (Sumcheck.writeWord (Sumcheck.writeWord a lo low native total) hi high native bot)

/-- Native word access preserves every input read and output byte. -/
theorem InductionBytes.butterflyIndices_eq {words : Nat} (native : 8*words < USize.size)
    (bytes : InductionBytes words) (lo hi : USize) (low : lo.toNat < words) (high : hi.toNat < words)
    (scalar : Word) :
    bytes.butterflyIndices native lo hi low high scalar =
      bytes.butterfly ⟨lo.toNat,low⟩ ⟨hi.toNat,high⟩ scalar := by
  simp only [butterflyIndices,butterfly,Sumcheck.readWord_eq,Sumcheck.writeWord_eq]

/-- Bounded native addition agrees with its natural coordinate. -/
private theorem inductionAdd (x y : USize) (safe : x.toNat+y.toNat < USize.size) :
    (x+y).toNat = x.toNat+y.toNat := by
  rw [USize.toNat_add]
  change (x.toNat+y.toNat)%USize.size = x.toNat+y.toNat
  exact Nat.mod_eq_of_lt safe

/-- Both butterfly endpoints use exact native addition in an addressable block. -/
theorem inductionBlockIndices {k words : Nat} (block : Fin k) (span : Nat)
    (size : k*(2*span) = words) (native : 8*words < USize.size) (c : Fin span) :
    (c.val.toUSize+(2*span*block.val).toUSize).toNat = c.val+2*span*block.val ∧
      (c.val.toUSize+(2*span*block.val).toUSize+span.toUSize).toNat = c.val+span+2*span*block.val := by
  have bound : c.val+span+2*span*block.val < words := by
    have := c.isLt; have := block.isLt; nlinarith
  have ci := USize.toNat_ofNat_of_lt' (show c.val < USize.size by omega)
  have bi := USize.toNat_ofNat_of_lt' (show 2*span*block.val < USize.size by omega)
  have si := USize.toNat_ofNat_of_lt' (show span < USize.size by omega)
  have low : (c.val.toUSize+(2*span*block.val).toUSize).toNat = c.val+2*span*block.val := by
    rw [inductionAdd _ _ (by rw [ci,bi]; omega),ci,bi]
  refine ⟨low,?_⟩
  rw [inductionAdd _ _ (by rw [low,si]; omega),low,si]
  omega

/-- Direct byte-array state retains the ordered scalar butterflies. -/
def scalarBlockSweep {k words : Nat} (block : Fin k) (span : Nat)
    (size : k*(2*span) = words) (scalar : Word)
    (a : BF64.Packed.Buffer words) : BF64.Packed.Buffer words :=
  let base := 2*span*block.val
  InductionBytes.buffer (Fin.foldl span (fun bytes c =>
    let lo : Fin words := ⟨c.val+base,by dsimp only [base]; have := c.isLt; have := block.isLt; nlinarith⟩
    let hi : Fin words := ⟨c.val+span+base,by dsimp only [base]; have := c.isLt; have := block.isLt; nlinarith⟩
    bytes.butterfly lo hi scalar) (InductionBytes.ofBuffer a))

/-- Addressable buffers retain machine byte offsets for the whole block. -/
def scalarBlockSweepMachine {k words : Nat} (block : Fin k) (span : Nat)
    (size : k*(2*span) = words) (scalar : Word) (a : BF64.Packed.Buffer words) : BF64.Packed.Buffer words :=
  if native : 8*words < USize.size then
    let base := (2*span*block.val).toUSize
    InductionBytes.buffer (Fin.foldl span (fun bytes c =>
      let lo := c.val.toUSize+base
      let hi := lo+span.toUSize
      bytes.butterflyIndices native lo hi
        (by rw [(inductionBlockIndices block span size native c).1]; have := c.isLt; have := block.isLt; nlinarith)
        (by rw [(inductionBlockIndices block span size native c).2]; have := c.isLt; have := block.isLt; nlinarith)
        scalar) (InductionBytes.ofBuffer a))
  else scalarBlockSweep block span size scalar a

/-- Machine byte addressing preserves the complete butterfly-block fold. -/
@[csimp] theorem scalarBlockSweep_code : @scalarBlockSweep = @scalarBlockSweepMachine := by
  funext k words block span size scalar a
  unfold scalarBlockSweepMachine
  split
  · rename_i native
    simp only [InductionBytes.butterflyIndices_eq,
      (inductionBlockIndices block span size native _).1,
      (inductionBlockIndices block span size native _).2]
    rfl
  · rfl

/-- Byte-array state is equal to the complete word-buffer fold. -/
theorem scalarBlockSweep_eq {k words : Nat} (block : Fin k) (span : Nat)
    (size : k*(2*span) = words) (scalar : Word) (a : BF64.Packed.Buffer words) :
    scalarBlockSweep block span size scalar a =
      Fin.foldl span (fun a c =>
        let lo : Fin words := ⟨c.val+2*span*block.val,by have := c.isLt; have := block.isLt; nlinarith⟩
        let hi : Fin words := ⟨c.val+span+2*span*block.val,by have := c.isLt; have := block.isLt; nlinarith⟩
        let out := transposePair (Packed.Multiplier.masked scalar) (BF64.Packed.read a lo) (BF64.Packed.read a hi)
        BF64.Packed.write (BF64.Packed.write a lo out.1) hi out.2) a := by
  unfold scalarBlockSweep
  simp only [Fin.foldl_eq_finRange_foldl]
  symm
  conv_lhs => rw [← InductionBytes.buffer_ofBuffer a]
  apply List.foldl_hom InductionBytes.buffer
  intro bytes c
  rw [InductionBytes.butterfly,InductionBytes.buffer_ofBuffer]
  rfl

/-- Scalar multipliers remove the per-butterfly indirect call. -/
def occupiedSweepBlocksScalar {k n words : Nat} (blocks : Vector (Fin k) n) (span : Nat)
    (size : k*(2*span) = words) (multipliers : Vector Packed.Multiplier n)
    (a : BF64.Packed.Buffer words) : BF64.Packed.Buffer words :=
  Fin.foldl n (fun a b => scalarBlockSweep blocks[b] span size multipliers[b].scalar a) a

/-- The scalar butterfly agrees with any certified multiplier implementation. -/
@[csimp] theorem occupiedSweepBlocks_code : @occupiedSweepBlocks = @occupiedSweepBlocksScalar := by
  funext k n words blocks span size multipliers a
  unfold occupiedSweepBlocks occupiedSweepBlocksScalar
  simp only [scalarBlockSweep_eq]
  apply congrArg (fun update => Fin.foldl n update a)
  funext input b
  have same : transposePair multipliers[b] =
      transposePair (Packed.Multiplier.masked multipliers[b].scalar) := by
    funext u v
    exact transposePair_scalar_eq multipliers[b]
      (Packed.Multiplier.masked multipliers[b].scalar) rfl u v
  rw [same]


section
attribute [local irreducible] BF64.Packed.read BF64.Packed.write transposePair

/-- Block-major traversal preserves the complete ordered occupied-pair sweep. -/
theorem occupiedSweepBlocks_eq {k n words : Nat} (blocks : Vector (Fin k) n) (span : Nat)
    (size : k*(2*span) = words) (multipliers : Vector Packed.Multiplier n)
    (a : BF64.Packed.Buffer words) :
    occupiedSweepBlocks blocks span size multipliers a =
      Packed.sweep (fun p => Fin.cast size (occupiedIndexCached blocks span p))
        (fun j => transposePair multipliers[j.divNat]) a := by
  unfold occupiedSweepBlocks Packed.sweep
  rw [← foldl_blocks n span]
  apply congrArg (fun f : BF64.Packed.Buffer words → Fin n → BF64.Packed.Buffer words => Fin.foldl n f a)
  funext a b
  dsimp only
  apply congrArg (fun f : BF64.Packed.Buffer words → Fin span → BF64.Packed.Buffer words => Fin.foldl span f a)
  funext a c
  simp only [Packed.updatePair, frontierPair_divNat, ← frontierIndex_eq, frontierIndex,
    Fin.cast_mk, Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.mul_one, Nat.add_zero]
end

/-- Sweep occupied blocks with a multiplier array proportional to the live frontier. -/
def occupiedStageCompact {d count : Nat} (hd : d < 64) (i : Fin d)
    (lanes : Nat) (positions : Vector (Fin (2^d)) count) (a : BF64.Packed.Buffer (2^d*lanes)) :
    BF64.Packed.Buffer (2^d*lanes) :=
  let blocks := occupiedBlocks i positions
  let cached : Vector _ blocks.length := ⟨blocks.toArray, List.size_toArray⟩
  let multipliers := occupiedMultipliers d hd i cached
  let span := 2^i.val*lanes
  occupiedSweepBlocks cached span (Packed.stage_word_count d i lanes) multipliers a

/-- Compact twiddle preparation leaves the complete occupied-stage buffer unchanged. -/
theorem occupiedStageCompact_eq {d count : Nat} (hd : d < 64) (plan : Packed.FlatPlan d hd)
    (i : Fin d) (lanes : Nat) (positions : Vector (Fin (2^d)) count)
    (a : BF64.Packed.Buffer (2^d*lanes)) :
    occupiedStageCompact hd i lanes positions a = occupiedStage plan i lanes positions a := by
  let blocks := occupiedBlocks i positions
  let cached : Vector _ blocks.length := ⟨blocks.toArray, List.size_toArray⟩
  have pair (j : Fin (blocks.length*(2^i.val*lanes))) :
      transposePair (occupiedMultipliers d hd i cached)[j.divNat] =
        transposePair (plan.get i cached[j.divNat]) := by
    funext u v
    apply transposePair_scalar_eq
    rw [occupiedMultipliers_scalar]
    exact (plan.scalar_eq i _).symm
  unfold occupiedStageCompact
  rw [occupiedSweepBlocks_eq]
  exact congrArg (fun op => Packed.sweep (fun p => Fin.cast (Packed.stage_word_count d i lanes)
    (occupiedIndexCached cached (2^i.val*lanes) p)) op a) (funext pair)

/-- Execute low transpose stages with query-local multiplier preparation. -/
def occupiedRunCompact {d count : Nat} (hd : d < 64)
    (lanes : Nat) (positions : Vector (Fin (2^d)) count) :
    (steps : Nat) → steps ≤ d → BF64.Packed.Buffer (2^d*lanes) → BF64.Packed.Buffer (2^d*lanes)
  | 0, _, a => a
  | steps+1, bound, a => occupiedStageCompact hd ⟨steps, by omega⟩ lanes positions
      (occupiedRunCompact hd lanes positions steps (by omega) a)

/-- Compact stages reproduce every occupied transpose stage for every certified plan. -/
theorem occupiedRunCompact_eq {d count : Nat} (hd : d < 64) (plan : Packed.FlatPlan d hd)
    (lanes : Nat) (positions : Vector (Fin (2^d)) count) (steps : Nat) (bound : steps ≤ d)
    (a : BF64.Packed.Buffer (2^d*lanes)) :
    occupiedRunCompact hd lanes positions steps bound a = occupiedRun plan lanes positions steps bound a := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    change occupiedStageCompact hd ⟨steps, by omega⟩ lanes positions
      (occupiedRunCompact hd lanes positions steps (by omega) a) =
      occupiedStage plan ⟨steps, by omega⟩ lanes positions
        (occupiedRun plan lanes positions steps (by omega) a)
    rw [occupiedStageCompact_eq hd plan, ih]

/-- Induce query weights without constructing a full-domain twiddle plan. -/
def induceOccupiedCompactRows {ell rate : Nat} (hd : ell+rate < 64)
    (lanes : Nat) {count : Nat} (positions : Vector (Fin (2^(ell+rate))) count)
    (values : Fin count → Fin lanes → Word) : BF64.Packed.Buffer (2^ell*lanes) :=
  collapseRows ell rate lanes (occupiedRunCompact hd lanes positions ell (by omega)
    (scatterRows _ lanes positions values))

/-- Query-local twiddles preserve every coordinate of the certified encoder transpose. -/
theorem induceOccupiedCompactRows_refines {ell rate : Nat} (hd : ell+rate < 64)
    (plan : Packed.FlatPlan (ell+rate) hd) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2^(ell+rate))) count) (values : Fin count → Fin lanes → Word)
    (index : Fin (2^ell*lanes)) :
    BF64.Packed.read (induceOccupiedCompactRows hd lanes positions values) index =
      BF64.Packed.read (induceRows hd plan lanes positions values) index := by
  simp only [induceOccupiedCompactRows, occupiedRunCompact_eq hd plan]
  exact induceOccupiedRows_refines hd plan lanes positions values index

/-- Replica sums materialized with bounded native word loads and stores. -/
def collapseRowsNative (ell rate lanes : Nat) (a : BF64.Packed.Buffer (2^(ell+rate)*lanes)) :
    BF64.Packed.Buffer (2^ell*lanes) :=
  if native : 8*(2^(ell+rate)*lanes) < USize.size then
    have smaller : 2^ell*lanes ≤ 2^(ell+rate)*lanes := by
      rw [pow_add]
      exact Nat.mul_le_mul_right lanes (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos rate))
    have outputBound : 8*(2^ell*lanes) < USize.size := by omega
    Sumcheck.fillWordBuffer (2^ell*lanes) outputBound fun i hi =>
      Fin.foldl (2^rate) (fun acc replica =>
        let j : Fin (2^(ell+rate)*lanes) := ⟨replica.val*(2^ell*lanes)+i.toNat,by
          have := replica.isLt
          rw [pow_add]
          nlinarith⟩
        Word.add acc (Sumcheck.readWord a j.val.toUSize (by
          rw [USize.toNat_ofNat_of_lt' (by have := j.isLt; omega)]
          exact j.isLt) native)) ⟨0⟩
  else collapseRows ell rate lanes a

/-- Native replica collapse retains every packed output byte. -/
@[csimp] theorem collapseRows_code : collapseRows = collapseRowsNative := by
  funext ell rate lanes a
  unfold collapseRowsNative
  split
  · rename_i native
    rw [Sumcheck.fillWordBuffer_eq]
    unfold collapseRows Packed.tabulate BF64.Packed.ofFn
    rw [Fin.foldl_eq_finRange_foldl]
    congr 1
    funext buffer i
    congr 1
    have h : i.val.toUSize.toNat = i.val := by
      apply USize.toNat_ofNat_of_lt'
      have := i.isLt
      have smaller : 2^ell*lanes ≤ 2^(ell+rate)*lanes := by
        rw [pow_add]
        exact Nat.mul_le_mul_right lanes (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos rate))
      omega
    simp only [Sumcheck.readWord_eq,h]
    congr 1
    funext acc replica
    congr 1
    apply congrArg (BF64.Packed.read a)
    apply Fin.ext
    symm
    apply USize.toNat_ofNat_of_lt'
    have := replica.isLt
    have := i.isLt
    rw [pow_add] at native
    nlinarith
  · rfl

end CompStark.Pcs
