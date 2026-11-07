/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Algorithms derived from succinctlabs/flock (flock-core), MIT OR Apache-2.0.
Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum.
Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang.
-/
module
public import CompStark.Pcs.Induction
public import CompStark.Sumcheck.Preparation

/-! Occupied-block transposed additive transforms. -/
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
@[expose] public section
namespace CompStark.Pcs
open BF64 AdditiveNTT

/-- A certified fixed multiplier with nibble-built tables and machine-size lookups. -/
def inductionMultiplier (scalar : Word) : Packed.Multiplier where
  scalar := scalar
  apply := Sumcheck.mapMul (Sumcheck.byteMap scalar)
  correct a := by
    rw [Sumcheck.mapMul_eq, Sumcheck.byteMap_eq, Word.ByteMap.toField_mul]

/-- Prepare byte maps only for the sixteen-block frontier reused by sparse induction. -/
def sparseInductionPlan (d : Nat) (hd : d < 64) : Packed.FlatPlan d hd where
  stages := Vector.ofFn fun i =>
    let raw := Packed.stageTwiddles Packed.flatBasis d hd i
    Array.ofFn fun u : Fin (2^(d-i.val-1)) =>
      let scalar := raw.getD u.val 0
      if d-i.val-1 < 4 then inductionMultiplier scalar else Packed.Multiplier.masked scalar
  stageSize i := by simp only [Vector.getElem_ofFn, Array.size_ofFn]
  scalar_eq i u := by
    simp only [Vector.getElem_ofFn, Array.getElem_ofFn]
    split <;> rfl

/-- The distinct blocks touched by the original ordered query positions at a transpose stage. -/
def occupiedBlocks {d count : Nat} (i : Fin d)
    (positions : Vector (Fin (2^d)) count) : List (Fin (2^(d-i.val-1))) :=
  (positions.toList.map fun q =>
    (⟨q.val/2^(i.val+1), by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
      have power : 2^(d-i.val-1)*2^(i.val+1) = 2^d := by rw [← pow_add]; congr 1; omega
      rw [power]
      exact q.isLt⟩ : Fin (2^(d-i.val-1)))).dedup

/-- Project an active block and its butterfly position into the complete stage's pair index. -/
def occupiedPair (blocks : List (Fin k)) (span : Nat) : Fin (blocks.length*span) → Fin (k*span) :=
  let cached := blocks.toArray
  fun j => finProdFinEquiv (cached[j.divNat.val]'(by simpa only [cached, List.size_toArray] using j.divNat.isLt), j.modNat)

/-- Address an occupied pair using its retained block array and direct row-major arithmetic. -/
@[inline] def occupiedPairCached {k n : Nat} (blocks : Vector (Fin k) n) (span : Nat)
    (j : Fin (n*span)) : Fin (k*span) :=
  ⟨blocks[j.divNat].val*span+j.modNat.val, by
    have := blocks[j.divNat].isLt
    have := j.modNat.isLt
    nlinarith⟩

/-- Cached direct addressing is exactly the certified occupied-pair map. -/
theorem occupiedPairCached_eq {k : Nat} (blocks : List (Fin k)) (span : Nat) :
    occupiedPairCached (⟨blocks.toArray, List.size_toArray⟩ : Vector (Fin k) blocks.length) span =
      occupiedPair blocks span := by
  funext j
  apply Fin.ext
  simp only [occupiedPairCached, occupiedPair, finProdFinEquiv, Equiv.coe_fn_mk,
    Fin.getElem_fin, Vector.getElem_mk]
  simp only [Nat.add_comm, Nat.mul_comm]

/-- Cached occupied-pair addressing retains its selected parent block. -/
theorem occupiedPairCached_divNat {k n : Nat} (blocks : Vector (Fin k) n) (span : Nat)
    (j : Fin (n*span)) : (occupiedPairCached blocks span j).divNat = blocks[j.divNat] := by
  have positive : 0 < span := by have := j.modNat.isLt; omega
  apply Fin.ext
  change (blocks[j.divNat].val*span+j.modNat.val)/span = blocks[j.divNat].val
  rw [Nat.mul_comm blocks[j.divNat].val span, Nat.mul_add_div positive,
    Nat.div_eq_of_lt j.modNat.isLt, Nat.add_zero]

/-- Cached occupied-pair addressing retains its position inside the selected block. -/
theorem occupiedPairCached_modNat {k n : Nat} (blocks : Vector (Fin k) n) (span : Nat)
    (j : Fin (n*span)) : (occupiedPairCached blocks span j).modNat = j.modNat := by
  apply Fin.ext
  exact Nat.mul_add_mod_of_lt j.modNat.isLt

/-- Address one side of an active butterfly with its cached block and shared stride. -/
@[inline] def occupiedIndexCached {k n : Nat} (blocks : Vector (Fin k) n) (span : Nat)
    (p : Fin (n*span) × Fin 2) : Fin (k*(2*span)) :=
  ⟨p.1.modNat.val+span*p.2.val+2*span*blocks[p.1.divNat].val, by
    have := p.1.modNat.isLt
    have := p.2.isLt
    have := blocks[p.1.divNat].isLt
    nlinarith⟩

/-- Direct active addresses are the complete stage permutation on the same occupied pair. -/
theorem occupiedIndexCached_eq {d n : Nat} (i : Fin d) (lanes : Nat)
    (blocks : Vector (Fin (2^(d-i.val-1))) n) (p : Fin (n*(2^i.val*lanes)) × Fin 2) :
    Fin.cast (Packed.stage_word_count d i lanes) (occupiedIndexCached blocks (2^i.val*lanes) p) =
      Packed.stageIndex d i lanes (occupiedPairCached blocks (2^i.val*lanes) p.1,p.2) := by
  apply Fin.ext
  change p.1.modNat.val+(2^i.val*lanes)*p.2.val+2*(2^i.val*lanes)*blocks[p.1.divNat].val =
    (occupiedPairCached blocks (2^i.val*lanes) p.1).modNat.val+(2^i.val*lanes)*p.2.val+
      2*(2^i.val*lanes)*(occupiedPairCached blocks (2^i.val*lanes) p.1).divNat.val
  rw [occupiedPairCached_modNat, occupiedPairCached_divNat]

/-- Active-pair addressing is injective when each occupied block occurs once. -/
theorem occupiedPair_injective {k : Nat} (blocks : List (Fin k)) (span : Nat) (unique : blocks.Nodup) :
    Function.Injective (occupiedPair blocks span) := by
  intro a b equal
  dsimp only [occupiedPair] at equal
  have components := finProdFinEquiv.injective equal
  have blockEqual := congrArg Prod.fst components
  have innerEqual := congrArg Prod.snd components
  simp only [List.getElem_toArray] at blockEqual
  have sameBlock : a.divNat = b.divNat := Fin.ext (unique.getElem_inj.mp blockEqual)
  exact finProdFinEquiv.symm.injective (Prod.ext sameBlock innerEqual)

/-- The active pair map covers exactly the pairs in its occupied blocks. -/
theorem occupiedPair_range {k : Nat} (blocks : List (Fin k)) (span : Nat) (t : Fin (k*span)) :
    (∃ j, occupiedPair blocks span j = t) ↔ t.divNat ∈ blocks := by
  constructor
  · rintro ⟨j,rfl⟩
    dsimp only [occupiedPair]
    have eq : (finProdFinEquiv (blocks.toArray[j.divNat.val]'(by simpa using j.divNat.isLt),j.modNat)).divNat =
        blocks.toArray[j.divNat.val]'(by simpa using j.divNat.isLt) :=
      congrArg Prod.fst (finProdFinEquiv.symm_apply_apply _)
    rw [eq]
    exact List.getElem_mem _
  · intro member
    let idx : Fin blocks.length := ⟨blocks.idxOf t.divNat, List.idxOf_lt_length_iff.mpr member⟩
    refine ⟨finProdFinEquiv (idx,t.modNat), ?_⟩
    have div : (finProdFinEquiv (idx,t.modNat)).divNat = idx :=
      congrArg Prod.fst (finProdFinEquiv.symm_apply_apply _)
    have mod : (finProdFinEquiv (idx,t.modNat)).modNat = t.modNat :=
      congrArg Prod.snd (finProdFinEquiv.symm_apply_apply _)
    simp only [occupiedPair, div, mod, List.getElem_toArray]
    rw [List.getElem_idxOf (List.idxOf_lt_length_iff.mpr member)]
    exact finProdFinEquiv.apply_symm_apply t

/-- A disjoint butterfly sweep preserves every coordinate outside the image of its pairs. -/
theorem read_sweep_outside {n k : Nat} (index : Fin k × Fin 2 → Fin n)
    (op : Fin k → Word → Word → Word × Word) (a : BF64.Packed.Buffer n) (t : Fin n)
    (outside : ∀ j b, index (j,b) ≠ t) :
    BF64.Packed.read (Packed.sweep index op a) t = BF64.Packed.read a t := by
  unfold Packed.sweep
  rw [Fin.foldl_eq_finRange_foldl]
  have loop (xs : List (Fin k)) (a : BF64.Packed.Buffer n) :
      BF64.Packed.read (xs.foldl (Packed.updatePair index op) a) t = BF64.Packed.read a t := by
    induction xs generalizing a with
    | nil => rfl
    | cons j xs ih =>
      rw [List.foldl_cons, ih]
      simp only [Packed.updatePair, BF64.Packed.read_write, outside, ↓reduceIte]
  exact loop _ a

/-- Transpose only butterflies belonging to occupied blocks, in disjoint active-pair order. -/
def occupiedStage {d count : Nat} {hd : d < 64} (plan : Packed.FlatPlan d hd) (i : Fin d)
    (lanes : Nat) (positions : Vector (Fin (2^d)) count) (a : BF64.Packed.Buffer (2^d*lanes)) :
    BF64.Packed.Buffer (2^d*lanes) :=
  let blocks := occupiedBlocks i positions
  let cached : Vector _ blocks.length := ⟨blocks.toArray, List.size_toArray⟩
  let span := 2^i.val*lanes
  Packed.sweep (fun p => Fin.cast (Packed.stage_word_count d i lanes)
      (occupiedIndexCached cached span p))
    (fun j => transposePair (plan.get i cached[j.divNat])) a

/-- The cached implementation retains the original occupied butterfly sweep. -/
theorem occupiedStage_eq {d count : Nat} {hd : d < 64} (plan : Packed.FlatPlan d hd) (i : Fin d)
    (lanes : Nat) (positions : Vector (Fin (2^d)) count) (a : BF64.Packed.Buffer (2^d*lanes)) :
    occupiedStage plan i lanes positions a =
      Packed.sweep (fun p => Packed.stageIndex d i lanes
        (occupiedPair (occupiedBlocks i positions) (2^i.val*lanes) p.1,p.2))
        (fun j => transposePair (plan.get i
          (occupiedPair (occupiedBlocks i positions) (2^i.val*lanes) j).divNat)) a := by
  unfold occupiedStage
  dsimp only
  simp only [occupiedIndexCached_eq, ← occupiedPairCached_divNat, occupiedPairCached_eq]

/-- Each occupied-stage result reads its original pair, and every omitted pair is unchanged. -/
theorem occupiedStage_read {d count : Nat} {hd : d < 64} (plan : Packed.FlatPlan d hd)
    (i : Fin d) (lanes : Nat) (positions : Vector (Fin (2^d)) count)
    (a : BF64.Packed.Buffer (2^d*lanes))
    (t : Fin (2^(d-i.val-1)*(2^i.val*lanes))) (b : Fin 2) :
    BF64.Packed.read (occupiedStage plan i lanes positions a) (Packed.stageIndex d i lanes (t,b)) =
      if t.divNat ∈ occupiedBlocks i positions then
        if b = 0 then (transposePair (plan.get i t.divNat)
          (BF64.Packed.read a (Packed.stageIndex d i lanes (t,0)))
          (BF64.Packed.read a (Packed.stageIndex d i lanes (t,1)))).1
        else (transposePair (plan.get i t.divNat)
          (BF64.Packed.read a (Packed.stageIndex d i lanes (t,0)))
          (BF64.Packed.read a (Packed.stageIndex d i lanes (t,1)))).2
      else BF64.Packed.read a (Packed.stageIndex d i lanes (t,b)) := by
  let blocks := occupiedBlocks i positions
  let selected := occupiedPair blocks (2^i.val*lanes)
  have injective : Function.Injective (fun p : Fin (blocks.length*(2^i.val*lanes)) × Fin 2 => Packed.stageIndex d i lanes (selected p.1,p.2)) := by
    intro x y h
    have components := (Packed.stageIndex d i lanes).injective h
    apply Prod.ext
    · exact occupiedPair_injective blocks _ (List.nodup_dedup _) (congrArg Prod.fst components)
    · have second := congrArg Prod.snd components
      exact second
  by_cases member : t.divNat ∈ blocks
  · obtain ⟨j,entry⟩ := (occupiedPair_range blocks _ t).mpr member
    simp only [show t.divNat ∈ occupiedBlocks i positions from member, ↓reduceIte]
    rw [← entry]
    rw [occupiedStage_eq]
    change BF64.Packed.read (Packed.sweep _ _ a) ((fun p : Fin (blocks.length*(2^i.val*lanes)) × Fin 2 => Packed.stageIndex d i lanes (selected p.1,p.2)) (j,b)) = _
    rw [Packed.read_sweep _ injective]
  · simp only [show ¬t.divNat ∈ occupiedBlocks i positions from member, ↓reduceIte]
    rw [occupiedStage_eq]
    apply read_sweep_outside
    intro j side equal
    have components := (Packed.stageIndex d i lanes).injective equal
    apply member
    exact (occupiedPair_range blocks _ t).mp ⟨j,congrArg Prod.fst components⟩

/-- The original queries are the only possible sources of a live block after `s` low stages. -/
def QuerySupport {d count : Nat} (s lanes : Nat) (positions : Vector (Fin (2^d)) count)
    (a : BF64.Packed.Buffer (2^d*lanes)) : Prop :=
  ∀ index, (∀ q : Fin count, index.val/(2^s*lanes) ≠ positions[q].val/2^s) →
    BF64.Packed.read a index = ⟨0⟩

/-- Joining two adjacent blocks cannot create a source outside their parent block. -/
theorem QuerySupport.coarsen {d count : Nat} {s lanes : Nat}
    {positions : Vector (Fin (2^d)) count} {a : BF64.Packed.Buffer (2^d*lanes)}
    (support : QuerySupport s lanes positions a) : QuerySupport (s+1) lanes positions a := by
  intro index outside
  apply support index
  intro q same
  apply outside q
  have halves := congrArg (fun x : Nat => x/2) same
  simpa only [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm] using halves

/-- Each stage's two addresses have the stage pair's common high block. -/
theorem stageIndex_block (d : Nat) (i : Fin d) (lanes : Nat)
    (t : Fin (2^(d-i.val-1)*(2^i.val*lanes))) (b : Fin 2) :
    (Packed.stageIndex d i lanes (t,b)).val/(2^(i.val+1)*lanes) = t.divNat.val := by
  have positive : 0 < 2^i.val*lanes := by
    have bound := t.isLt
    by_contra h
    have : 2^i.val*lanes = 0 := by omega
    simp only [this, Nat.mul_zero, Nat.not_lt_zero] at bound
  change (t.val%(2^i.val*lanes)+(2^i.val*lanes)*b.val+
    (2*(2^i.val*lanes))*(t.val/(2^i.val*lanes)))/(2^(i.val+1)*lanes) = _
  have small : t.val%(2^i.val*lanes)+(2^i.val*lanes)*b.val < 2*(2^i.val*lanes) := by
    have := Nat.mod_lt t.val positive
    have := b.isLt
    nlinarith
  rw [pow_succ]
  have stride : 2^i.val*2*lanes = 2*(2^i.val*lanes) := by ac_rfl
  rw [stride, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt small, Nat.zero_add]
  rfl

/-- Parent blocks absent from the query list contain only zero input words. -/
theorem querySupport_stage_zero {d count : Nat} {hd : d < 64}
    (_plan : Packed.FlatPlan d hd) (i : Fin d) (lanes : Nat)
    (positions : Vector (Fin (2^d)) count) (a : BF64.Packed.Buffer (2^d*lanes))
    (support : QuerySupport i.val lanes positions a)
    (t : Fin (2^(d-i.val-1)*(2^i.val*lanes)))
    (absent : t.divNat ∉ occupiedBlocks i positions) (b : Fin 2) :
    BF64.Packed.read a (Packed.stageIndex d i lanes (t,b)) = ⟨0⟩ := by
  apply support.coarsen
  intro q equal
  apply absent
  rw [occupiedBlocks, List.mem_dedup, List.mem_map]
  refine ⟨positions[q], ?_, ?_⟩
  · exact Vector.mem_toList_iff.mpr (Vector.getElem_mem q.isLt)
  · apply Fin.ext
    rw [stageIndex_block] at equal
    exact equal.symm

/-- Occupied-block membership is exactly a matching parent of an original query. -/
theorem mem_occupiedBlocks {d count : Nat} (i : Fin d)
    (positions : Vector (Fin (2^d)) count) (block : Fin (2^(d-i.val-1))) :
    block ∈ occupiedBlocks i positions ↔
      ∃ q : Fin count, block.val = positions[q].val/2^(i.val+1) := by
  rw [occupiedBlocks, List.mem_dedup, List.mem_map]
  constructor
  · rintro ⟨position, member, equality⟩
    obtain ⟨q,bound,entry⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp member)
    refine ⟨⟨q,bound⟩, ?_⟩
    subst position
    exact (congrArg Fin.val equality).symm
  · rintro ⟨q,equality⟩
    refine ⟨positions[q], Vector.mem_toList_iff.mpr (Vector.getElem_mem q.isLt), ?_⟩
    exact Fin.ext equality.symm

/-- The zero butterfly remains zero for every certified multiplier. -/
theorem transposePair_zero (m : Packed.Multiplier) :
    transposePair m ⟨0⟩ ⟨0⟩ = (⟨0⟩,⟨0⟩) :=
  (sparseTransposePair_eq m ⟨0⟩ ⟨0⟩).symm.trans rfl

/-- On the query-support invariant, an occupied stage equals every full transpose coordinate. -/
theorem occupiedStage_refines {d count : Nat} {hd : d < 64} (plan : Packed.FlatPlan d hd)
    (i : Fin d) (lanes : Nat) (positions : Vector (Fin (2^d)) count)
    (a : BF64.Packed.Buffer (2^d*lanes)) (support : QuerySupport i.val lanes positions a)
    (index : Fin (2^d*lanes)) :
    BF64.Packed.read (occupiedStage plan i lanes positions a) index =
      BF64.Packed.read (Packed.stageSweep plan i lanes sparseTransposePair a) index := by
  obtain ⟨⟨t,b⟩,rfl⟩ := (Packed.stageIndex d i lanes).surjective index
  rw [occupiedStage_read, Packed.stageSweep_eq_sweep, Packed.read_sweep _ (Packed.stageIndex d i lanes).injective]
  simp only [sparseTransposePair_eq]
  split
  · rfl
  · rename_i absent
    have zero0 := querySupport_stage_zero plan i lanes positions a support t absent (0 : Fin 2)
    have zero1 := querySupport_stage_zero plan i lanes positions a support t absent (1 : Fin 2)
    have zerob := querySupport_stage_zero plan i lanes positions a support t absent b
    rw [zerob, zero0, zero1, transposePair_zero]
    split <;> rfl

/-- One occupied stage expands support only to the parents of the input query blocks. -/
theorem occupiedStage_support {d count : Nat} {hd : d < 64} (plan : Packed.FlatPlan d hd)
    (i : Fin d) (lanes : Nat) (positions : Vector (Fin (2^d)) count)
    (a : BF64.Packed.Buffer (2^d*lanes)) (support : QuerySupport i.val lanes positions a) :
    QuerySupport (i.val+1) lanes positions (occupiedStage plan i lanes positions a) := by
  intro index outside
  obtain ⟨⟨t,b⟩,rfl⟩ := (Packed.stageIndex d i lanes).surjective index
  have absent : t.divNat ∉ occupiedBlocks i positions := by
    intro member
    obtain ⟨q,equal⟩ := (mem_occupiedBlocks i positions t.divNat).mp member
    apply outside q
    rw [stageIndex_block]
    exact equal
  rw [occupiedStage_read, ite_eq_right absent]
  exact querySupport_stage_zero plan i lanes positions a support t absent b

/-- Scattering ordered query values starts with no support outside the queried rows. -/
theorem scatterRows_support {d count : Nat} (lanes : Nat)
    (positions : Vector (Fin (2^d)) count) (values : Fin count → Fin lanes → Word) :
    QuerySupport 0 lanes positions (scatterRows (2^d) lanes positions values) := by
  intro index outside
  apply Word.toField_injective
  change (BF64.Packed.read (scatterRows (2^d) lanes positions values) index).toField = 0
  rw [← unitRows_pairing index, scatterRows_pairing]
  apply Finset.sum_eq_zero
  intro q _
  apply Finset.sum_eq_zero
  intro c _
  have different : (⟨positions[q].val*lanes+c.val, by have := positions[q].isLt; have := c.isLt; nlinarith⟩ : Fin (2^d*lanes)) ≠ index := by
    intro equal
    apply outside q
    have bound := c.isLt
    have pos : 0 < lanes := by omega
    have same := congrArg Fin.val equal
    simp only [pow_zero, Nat.one_mul]
    rw [← same]
    change (positions[q].val*lanes+c.val)/lanes = positions[q].val/1
    rw [Nat.mul_comm positions[q].val lanes, Nat.mul_add_div pos,
      Nat.div_eq_of_lt c.isLt, Nat.add_zero, Nat.div_one]
  simp only [unitRows, Packed.read_tabulate, different, ↓reduceIte]
  exact zero_mul _

/-- Run the low transpose stages, retaining only the descendants of occupied query blocks. -/
def occupiedRun {d count : Nat} {hd : d < 64} (plan : Packed.FlatPlan d hd)
    (lanes : Nat) (positions : Vector (Fin (2^d)) count) :
    (steps : Nat) → steps ≤ d → BF64.Packed.Buffer (2^d*lanes) → BF64.Packed.Buffer (2^d*lanes)
  | 0, _, a => a
  | steps+1, bound, a => occupiedStage plan ⟨steps, by omega⟩ lanes positions
      (occupiedRun plan lanes positions steps (by omega) a)

/-- Corresponding complete stages preserve equality of every packed input coordinate. -/
theorem transposeStage_congr {d : Nat} {hd : d < 64} (plan : Packed.FlatPlan d hd)
    (i : Fin d) (lanes : Nat) (a b : BF64.Packed.Buffer (2^d*lanes))
    (same : ∀ index, BF64.Packed.read a index = BF64.Packed.read b index) (index : Fin (2^d*lanes)) :
    BF64.Packed.read (Packed.stageSweep plan i lanes sparseTransposePair a) index =
      BF64.Packed.read (Packed.stageSweep plan i lanes sparseTransposePair b) index := by
  obtain ⟨⟨t,side⟩,rfl⟩ := (Packed.stageIndex d i lanes).surjective index
  simp only [Packed.stageSweep_eq_sweep, Packed.read_sweep _ (Packed.stageIndex d i lanes).injective, same]

/-- Occupied stages preserve the support invariant and the complete certified transpose. -/
theorem occupiedRun_refines {d count : Nat} {hd : d < 64} (plan : Packed.FlatPlan d hd)
    (lanes : Nat) (positions : Vector (Fin (2^d)) count) (steps : Nat) (bound : steps ≤ d)
    (a : BF64.Packed.Buffer (2^d*lanes)) (support : QuerySupport 0 lanes positions a) :
    QuerySupport steps lanes positions (occupiedRun plan lanes positions steps bound a) ∧
      ∀ index, BF64.Packed.read (occupiedRun plan lanes positions steps bound a) index =
        BF64.Packed.read (transposeRows plan steps bound lanes a) index := by
  induction steps with
  | zero => exact ⟨support, fun _ => rfl⟩
  | succ steps ih =>
    obtain ⟨previousSupport,previousSame⟩ := ih (by omega)
    constructor
    · exact occupiedStage_support plan ⟨steps, by omega⟩ lanes positions _ previousSupport
    · intro index
      change BF64.Packed.read (occupiedStage plan ⟨steps, by omega⟩ lanes positions
        (occupiedRun plan lanes positions steps (by omega) a)) index = _
      rw [occupiedStage_refines plan _ lanes positions _ previousSupport]
      unfold transposeRows
      rw [Fin.foldl_succ_last]
      apply transposeStage_congr
      exact previousSame

/-- Sparse query induction prunes the complete transpose to its occupied block frontier. -/
def induceOccupiedRows {ell rate : Nat} (hd : ell+rate < 64)
    (plan : Packed.FlatPlan (ell+rate) hd) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2^(ell+rate))) count) (values : Fin count → Fin lanes → Word) :
    BF64.Packed.Buffer (2^ell*lanes) :=
  collapseRows ell rate lanes (occupiedRun plan lanes positions ell (by omega)
    (scatterRows _ lanes positions values))

/-- Pruned sparse induction agrees with every coordinate of the full encoder transpose. -/
theorem induceOccupiedRows_refines {ell rate : Nat} (hd : ell+rate < 64)
    (plan : Packed.FlatPlan (ell+rate) hd) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2^(ell+rate))) count) (values : Fin count → Fin lanes → Word)
    (index : Fin (2^ell*lanes)) :
    BF64.Packed.read (induceOccupiedRows hd plan lanes positions values) index =
      BF64.Packed.read (induceRows hd plan lanes positions values) index := by
  have same := (occupiedRun_refines plan lanes positions ell (by omega) _
    (scatterRows_support lanes positions values)).2
  simp only [induceOccupiedRows, induceRows, collapseRows, Packed.read_tabulate, same]

end CompStark.Pcs
