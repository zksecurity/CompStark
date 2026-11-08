/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Algorithms derived from succinctlabs/flock (flock-core), MIT OR Apache-2.0.
Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum.
Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang.
-/
module
public import CompStark.Pcs.CompactInduction

/-! Compact normalized subspace rows with three byte subset-sum tables. -/
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
@[expose] public section
namespace CompStark.Pcs
open BF64 AdditiveNTT

/-- Pad a finite family with zero without changing its complete sum. -/
private theorem sum_pad {A : Type} [AddCommMonoid A] (n extra : Nat) (f : Nat → A) :
    (∑ i : Fin (n+extra), if i.val < n then f i.val else 0) = ∑ i : Fin n, f i.val := by
  rw [Fin.sum_univ_add]
  simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.isLt, ↓reduceIte]
  have high : (∑ i : Fin extra, if n+i.val < n then f (n+i.val) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (by omega)
  rw [high, add_zero]

/-- Sum the row entries selected by a block's binary digits. -/
def rowSubset (n : Nat) (values : Nat → Word) (block : Nat) : Word :=
  inductionDotLoop n (fun k => if block.testBit k.val then values k.val else ⟨0⟩) n (Nat.le_refl _) ⟨0⟩

/-- Row accumulation is precisely its finite subset sum. -/
theorem rowSubset_eq (n : Nat) (values : Nat → Word) (block : Nat) :
    rowSubset n values block = ∑ k : Fin n, if block.testBit k.val then values k.val else 0 := by
  rw [rowSubset, inductionDotLoop_eq]
  change (0 : Word) + (∑ k : Fin n, if block.testBit k.val then values k.val else 0) = _
  exact zero_add _

/-- A normalized subspace row retains three independent byte subset-sum tables. -/
def rowByteTables (n : Nat) (values : Nat → Word) : Vector (Vector Word 256) 3 :=
  Vector.ofFn fun byte => Vector.ofFn fun digit =>
    rowSubset 8 (fun bit => if 8*byte.val+bit < n then values (8*byte.val+bit) else ⟨0⟩) digit.val

/-- Build subset tables a bit at a time, sharing every shorter subset. -/
def subsetTable (values : Nat → Word) : (bits : Nat) → Vector Word (2^bits)
  | 0 => Vector.replicate 1 ⟨0⟩
  | bits+1 =>
    let previous := subsetTable values bits
    Vector.ofFn fun digit => Word.add previous[digit.val%2^bits]
      (if digit.val.testBit bits then values bits else ⟨0⟩)

/-- The shared table recurrence retains every subset sum. -/
theorem subsetTable_eq (values : Nat → Word) (bits : Nat) (digit : Fin (2^bits)) :
    (subsetTable values bits)[digit] = rowSubset bits values digit.val := by
  induction bits with
  | zero =>
    rw [subsetTable, rowSubset_eq]
    rw [Fin.sum_univ_zero]
    exact Vector.getElem_replicate digit.isLt
  | succ bits ih =>
    rw [subsetTable, Fin.getElem_fin, Vector.getElem_ofFn]
    rw [show (subsetTable values bits)[digit.val%2^bits] =
      rowSubset bits values (digit.val%2^bits) from ih ⟨_, Nat.mod_lt _ (Nat.two_pow_pos _)⟩]
    rw [rowSubset_eq, rowSubset_eq, Fin.sum_univ_castSucc]
    change (∑ k : Fin bits, if (digit.val%2^bits).testBit k.val then values k.val else 0) +
      (if digit.val.testBit bits then values bits else ⟨0⟩) =
      (∑ k : Fin bits, if digit.val.testBit k.val then values k.val else 0) +
      (if digit.val.testBit bits then values bits else ⟨0⟩)
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.testBit_mod_two_pow]
    simp only [k.isLt, decide_true, Bool.true_and]

/-- Append the upper half of each subset table with one shared row entry. -/
def subsetTableAppend (values : Nat → Word) : (bits : Nat) → Vector Word (2^bits)
  | 0 => Vector.replicate 1 ⟨0⟩
  | bits+1 =>
    let previous := subsetTableAppend values bits
    let high := values bits
    (previous ++ previous.map (fun x => Word.add x high)).cast (by simp only [pow_succ]; omega)

/-- Appending a scaled upper half preserves every shared subset-table entry. -/
theorem subsetTableAppend_eq (values : Nat → Word) (bits : Nat) :
    subsetTableAppend values bits = subsetTable values bits := by
  induction bits with
  | zero => rfl
  | succ bits ih =>
    apply Vector.ext
    intro digit hdigit
    rw [subsetTableAppend,subsetTable,ih]
    simp only [Vector.getElem_cast,Vector.getElem_append,Vector.getElem_ofFn]
    by_cases low : digit < 2^bits
    · simp only [low,↓reduceDIte,Nat.mod_eq_of_lt low,Nat.testBit_lt_two_pow low,Bool.false_eq_true,↓reduceIte]
      exact (add_zero ((subsetTable values bits)[digit])).symm
    · have high : 2^bits ≤ digit := by omega
      have digitDiv : digit / 2^bits = 1 := by
        apply Nat.div_eq_of_lt_le
        · simpa only [one_mul] using high
        · simpa only [pow_succ,Nat.mul_comm] using hdigit
      have digitMod : digit % 2^bits = digit-2^bits := by
        have := Nat.mod_add_div digit (2^bits)
        rw [digitDiv,Nat.mul_one] at this
        omega
      simp only [low,↓reduceDIte,Vector.getElem_map,Nat.testBit_eq_decide_div_mod_eq,digitDiv,
        Nat.reduceMod,decide_true,↓reduceIte,digitMod]

/-- Compiled byte tables append their upper halves without per-entry bit tests. -/
@[csimp] theorem subsetTable_code : subsetTable = subsetTableAppend := by
  funext values bits
  exact (subsetTableAppend_eq values bits).symm

/-- Three byte tables share their successive partial subset sums. -/
def rowByteTablesShared (n : Nat) (values : Nat → Word) : Vector (Vector Word 256) 3 :=
  Vector.ofFn fun byte => subsetTable
    (fun bit => if 8*byte.val+bit < n then values (8*byte.val+bit) else ⟨0⟩) 8

section
attribute [local irreducible] subsetTable rowSubset

/-- Sharing table prefixes preserves every prepared byte entry. -/
@[csimp] theorem rowByteTables_code : rowByteTables = rowByteTablesShared := by
  funext n values
  unfold rowByteTables rowByteTablesShared
  apply congrArg Vector.ofFn
  funext byte
  apply Vector.ext
  intro digit hdigit
  rw [Vector.getElem_ofFn]
  exact (subsetTable_eq _ 8 ⟨digit,hdigit⟩).symm

end

/-- The three byte digits of a small block retain every selected low bit. -/
theorem rowByte_bit (block : Nat) (byte : Fin 3) (bit : Fin 8) :
    ((block / 2^(8*byte.val)) % 256).testBit bit.val = block.testBit (8*byte.val+bit.val) := by
  rw [show 256 = 2^8 from rfl, Nat.testBit_mod_two_pow]
  simp only [bit.isLt, decide_true, Bool.true_and]
  rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]

/-- Read one twiddle with three table loads and two XORs in the 24-bit block range. -/
def rowByteLookup (tables : Vector (Vector Word 256) 3) (block : Nat) : Word :=
  Word.add (Word.add tables[0][block%256] tables[1][(block/256)%256]) tables[2][(block/65536)%256]

/-- The explicit three-load lookup is the finite sum over its byte digits. -/
theorem rowByteLookup_sum (tables : Vector (Vector Word 256) 3) (block : Nat) :
    rowByteLookup tables block = ∑ byte : Fin 3, tables[byte][(block/2^(8*byte.val))%256] := by
  simp only [rowByteLookup, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Fin.val_zero, Fin.val_succ, Nat.mul_zero, pow_zero, Nat.div_one]
  exact add_assoc _ _ _

/-- Three byte loads reconstruct the complete padded low-bit subset sum. -/
theorem rowByteLookup_eq (n : Nat) (values : Nat → Word) (block : Nat) :
    rowByteLookup (rowByteTables n values) block =
      ∑ k : Fin 24, if k.val < n then
        (if block.testBit k.val then values k.val else 0) else 0 := by
  rw [rowByteLookup_sum, ← (finProdFinEquiv : Fin 3 × Fin 8 ≃ Fin 24).sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro byte _
  rw [rowByteTables, Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_ofFn]
  rw [rowSubset_eq]
  apply Finset.sum_congr rfl
  intro bit _
  rw [rowByte_bit]
  have address : (finProdFinEquiv (byte,bit)).val = 8*byte.val+bit.val := by
    simp only [finProdFinEquiv, Equiv.coe_fn_mk]
    omega
  simp only [address]
  split <;> split <;> rfl

/-- Truncating a subset sum preserves it when every omitted entry is zero. -/
private theorem sum_truncate {A : Type} [AddCommMonoid A] (n width : Nat) (f : Nat → A)
    (high : ∀ k, width ≤ k → f k = 0) :
    (∑ k : Fin width, if k.val < n then f k.val else 0) = ∑ k : Fin n, f k.val := by
  by_cases short : n ≤ width
  · have shape : n+(width-n) = width := by omega
    have pad := sum_pad n (width-n) f
    rw [shape] at pad
    exact pad
  · have long : width ≤ n := by omega
    have shape : width+(n-width) = n := by omega
    have expanded := Fin.sum_univ_add (fun k : Fin (width+(n-width)) => f k.val)
    simp only [Fin.val_castAdd, Fin.val_natAdd] at expanded
    have zeros : (∑ k : Fin (n-width), f (width+k.val)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      exact high _ (by omega)
    rw [zeros, add_zero, shape] at expanded
    rw [expanded]
    apply Finset.sum_congr rfl
    intro k _
    rw [ite_eq_left (by have := k.isLt; omega)]

/-- Blocks below 24 bits have no contribution from higher row coordinates. -/
theorem rowByteLookup_small (n : Nat) (values : Nat → Word) (block : Nat) (small : block < 2^24) :
    rowByteLookup (rowByteTables n values) block = rowSubset n values block := by
  rw [rowByteLookup_eq, rowSubset_eq]
  apply sum_truncate n 24 (fun k => if block.testBit k then values k else 0)
  intro k bound
  have bit : block.testBit k = false := Nat.testBit_eq_false_of_lt
    (lt_of_lt_of_le small (Nat.pow_le_pow_right (by omega) bound))
  rw [bit]
  rfl

/-- A compact row owns its scalar entries and three byte subset-sum tables. -/
structure TwiddleRow (n : Nat) where
  /-- Normalized subspace polynomial values at the higher domain basis elements. -/
  values : Vector Word n
  /-- The three low-byte subset-sum tables. -/
  tables : Vector (Vector Word 256) 3
  /-- Every table entry is the subset sum of its eight row coordinates. -/
  tables_eq : tables = rowByteTables n (fun k => values.toArray.getD k ⟨0⟩)

/-- Build the compact row and its byte tables once. -/
def TwiddleRow.create (n : Nat) (values : Vector Word n) : TwiddleRow n :=
  ⟨values, rowByteTables n (fun k => values.toArray.getD k ⟨0⟩), rfl⟩

/-- Use the byte tables below 24 bits and the scalar row above that range. -/
def TwiddleRow.lookup {n : Nat} (row : TwiddleRow n) (block : Nat) : Word :=
  if block < 2^24 then rowByteLookup row.tables block else rowSubset n (fun k => row.values.toArray.getD k ⟨0⟩) block

/-- Both supported block ranges retain the exact normalized-row subset sum. -/
theorem TwiddleRow.lookup_eq {n : Nat} (row : TwiddleRow n) (block : Nat) :
    row.lookup block = rowSubset n (fun k => row.values.toArray.getD k ⟨0⟩) block := by
  unfold lookup
  split
  · rw [row.tables_eq, rowByteLookup_small _ _ _ ‹_›]
  · rfl

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
