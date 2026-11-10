/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.TiledInduction

/-! Occupied high-row plans shared by every induction column strip. -/
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
@[expose] public section
namespace CompStark.Pcs
open BF64 AdditiveNTT

/-- A complete high stage retains one normalized multiplier per block. -/
theorem stripStage_dense (base high : Nat) (hd : base+high < 64) (rows : CompactRows (base+high) hd)
    (columns : Nat) (i : Fin high) (a : BF64.Packed.Buffer (2^high*columns)) :
    stripStage base high hd rows columns i a = Packed.sweep (Packed.stageIndex high i columns)
      (fun t => transposePair (rowMultiplier rows.stages[(⟨base+i.val,by have := i.isLt; omega⟩ : Fin (base+high))].2 t.divNat.val)) a := by
  unfold stripStage
  rw [occupiedSweepRows_eq,occupiedSweepBlocks_eq]
  have indices : (fun p => Fin.cast (Packed.stage_word_count high i columns)
      (occupiedIndexCached (Vector.ofFn (fun b : Fin (2^(high-i.val-1)) => b)) (2^i.val*columns) p)) =
      Packed.stageIndex high i columns := by
    funext p
    rw [occupiedIndexCached_eq,occupiedPair_identity]
  rw [indices]
  simp only [rowMultiplier,Fin.getElem_fin,Vector.getElem_ofFn,Nat.zero_add]

/-- Skip the high-stage blocks with no original query window. -/
def stripSparseStage (base high : Nat) (hd : base+high < 64) (rows : CompactRows (base+high) hd)
    (columns : Nat) {count : Nat} (positions : Vector (Fin (2^high)) count) (i : Fin high)
    (a : BF64.Packed.Buffer (2^high*columns)) : BF64.Packed.Buffer (2^high*columns) :=
  selectedStage rows.stages[(⟨base+i.val,by have := i.isLt; omega⟩ : Fin (base+high))].2
    high i columns 0 (occupiedBlocks i positions) a

/-- An occupied high stage equals the complete high stage on query-supported inputs. -/
theorem stripSparseStage_refines (base high : Nat) (hd : base+high < 64) (rows : CompactRows (base+high) hd)
    (columns : Nat) {count : Nat} (positions : Vector (Fin (2^high)) count) (i : Fin high)
    (a : BF64.Packed.Buffer (2^high*columns)) (support : QuerySupport i.val columns positions a)
    (index : Fin (2^high*columns)) :
    BF64.Packed.read (stripSparseStage base high hd rows columns positions i a) index =
      BF64.Packed.read (stripStage base high hd rows columns i a) index := by
  obtain ⟨⟨t,b⟩,rfl⟩ := (Packed.stageIndex high i columns).surjective index
  rw [stripSparseStage,selectedStage_read _ high i columns 0 (occupiedBlocks i positions) (by unfold occupiedBlocks; exact List.nodup_dedup _),stripStage_dense,
    Packed.read_sweep _ (Packed.stageIndex high i columns).injective]
  simp only [Nat.zero_add]
  split
  · rfl
  · rename_i absent
    let plan := sparseInductionPlan high (by omega)
    have zero0 := querySupport_stage_zero plan i columns positions a support t absent (0 : Fin 2)
    have zero1 := querySupport_stage_zero plan i columns positions a support t absent (1 : Fin 2)
    have zerob := querySupport_stage_zero plan i columns positions a support t absent b
    rw [zerob,zero0,zero1,transposePair_zero]
    split <;> rfl

/-- An occupied high stage only expands support into the parents of live windows. -/
theorem stripSparseStage_support (base high : Nat) (hd : base+high < 64) (rows : CompactRows (base+high) hd)
    (columns : Nat) {count : Nat} (positions : Vector (Fin (2^high)) count) (i : Fin high)
    (a : BF64.Packed.Buffer (2^high*columns)) (support : QuerySupport i.val columns positions a) :
    QuerySupport (i.val+1) columns positions (stripSparseStage base high hd rows columns positions i a) := by
  intro index outside
  obtain ⟨⟨t,b⟩,rfl⟩ := (Packed.stageIndex high i columns).surjective index
  have absent : t.divNat ∉ occupiedBlocks i positions := by
    intro member
    obtain ⟨q,equal⟩ := (mem_occupiedBlocks i positions t.divNat).mp member
    apply outside q
    rw [stageIndex_block]
    exact equal
  rw [stripSparseStage,selectedStage_read _ high i columns 0 (occupiedBlocks i positions) (by unfold occupiedBlocks; exact List.nodup_dedup _),ite_eq_right absent]
  exact querySupport_stage_zero (sparseInductionPlan high (by omega)) i columns positions a support t absent b

/-- Execute the occupied high-row continuation in one contiguous strip. -/
def stripSparseRun (base high : Nat) (hd : base+high < 64) (rows : CompactRows (base+high) hd)
    (columns : Nat) {count : Nat} (positions : Vector (Fin (2^high)) count) :
    (steps : Nat) → steps ≤ high → BF64.Packed.Buffer (2^high*columns) → BF64.Packed.Buffer (2^high*columns)
  | 0,_,a => a
  | steps+1,bound,a => stripSparseStage base high hd rows columns positions ⟨steps,by omega⟩
      (stripSparseRun base high hd rows columns positions steps (by omega) a)

/-- The sparse high-row continuation preserves support and every dense strip coordinate. -/
theorem stripSparseRun_refines (base high : Nat) (hd : base+high < 64) (rows : CompactRows (base+high) hd)
    (columns : Nat) {count : Nat} (positions : Vector (Fin (2^high)) count)
    (steps : Nat) (bound : steps ≤ high) (a : BF64.Packed.Buffer (2^high*columns))
    (support : QuerySupport 0 columns positions a) :
    QuerySupport steps columns positions (stripSparseRun base high hd rows columns positions steps bound a) ∧
      ∀ index, BF64.Packed.read (stripSparseRun base high hd rows columns positions steps bound a) index =
        BF64.Packed.read (stripRun base high hd rows columns steps bound a) index := by
  induction steps with
  | zero => exact ⟨support,fun _ => rfl⟩
  | succ steps ih =>
    obtain ⟨previous,same⟩ := ih (by omega)
    constructor
    · exact stripSparseStage_support base high hd rows columns positions ⟨steps,by omega⟩ _ previous
    · intro index
      change BF64.Packed.read (stripSparseStage base high hd rows columns positions ⟨steps,by omega⟩ _) index = _
      rw [stripSparseStage_refines _ _ _ _ _ _ _ _ previous,stripRun,stripStage_dense,stripStage_dense]
      exact tileSweep_congr _ _ _ _ same index

/-- Original query positions projected onto their containing low windows. -/
def queryWindows (base high : Nat) {count : Nat} (positions : Vector (Fin (2^(base+high))) count) :
    Vector (Fin (2^high)) count :=
  positions.map fun p => ⟨p.val/2^base,by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    simpa only [pow_add,Nat.mul_comm] using p.isLt⟩

/-- Gathering low windows introduces no support outside the queried high rows. -/
theorem windowStripInput_support (base high : Nat) (hd : base+high < 64) (rows : CompactRows (base+high) hd)
    (lanes columns offset : Nat) (fits : offset+columns ≤ 2^base*lanes) {count : Nat}
    (positions : Vector (Fin (2^(base+high))) count) (values : Fin count → Fin lanes → Word) :
    QuerySupport 0 columns (queryWindows base high positions)
      (windowStripInput base high lanes columns offset fits (occupiedWindows rows base lanes (by omega) positions values)) := by
  intro index outside
  simp only [pow_zero,Nat.one_mul] at outside
  rw [windowStripInput,Packed.read_tabulate]
  unfold readWindow occupiedWindows
  rw [Fin.getElem_fin,Vector.getElem_ofFn]
  have absent : positions.any (fun p => decide (p.val/2^base = index.divNat.val)) = false := by
    apply Vector.any_eq_false.mpr
    intro q bound
    simp only [decide_eq_true_eq]
    intro equal
    exact outside ⟨q,bound⟩ (by simpa only [queryWindows,Fin.getElem_fin,Vector.getElem_map,Nat.div_one,Fin.divNat] using equal.symm)
  simp only [Fin.val_cast,absent,Bool.false_eq_true,↓reduceIte]

/-- Shared occupied blocks and normalized multipliers for one high stage. -/
structure StripPlanLayer where
  /-- Original high-stage block numbers, in query discovery order. -/
  blocks : Array Nat
  /-- One prepared multiplier for each retained block. -/
  multipliers : Array Packed.Multiplier
  /-- Every occupied block has exactly one retained multiplier. -/
  size_eq : multipliers.size = blocks.size

/-- Prepare one occupied high-row layer independently of the column strip. -/
def prepareStripLayer (base high : Nat) (hd : base+high < 64) (rows : CompactRows (base+high) hd)
    {count : Nat} (positions : Vector (Fin (2^high)) count) (i : Fin high) : StripPlanLayer :=
  let blocks := (occupiedBlocks i positions).toArray
  ⟨blocks.map Fin.val,blocks.map (fun b => rowMultiplier
      rows.stages[(⟨base+i.val,by have := i.isLt; omega⟩ : Fin (base+high))].2 b.val),by simp only [Array.size_map]⟩

/-- Execute one strip stage from a retained occupied block and multiplier layer. -/
def stripStagePlanned (high columns : Nat) (i : Fin high) (layer : StripPlanLayer)
    (a : BF64.Packed.Buffer (2^high*columns)) : BF64.Packed.Buffer (2^high*columns) :=
  let blocks := layer.blocks.map fun b => (⟨b % 2^(high-i.val-1),Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : Fin (2^(high-i.val-1)))
  occupiedSweepBlocks (⟨blocks,by simp only [blocks,Array.size_map]⟩ : Vector _ layer.blocks.size)
    (2^i.val*columns) (Packed.stage_word_count high i columns) ⟨layer.multipliers,layer.size_eq⟩ a

/-- Equal retained arrays identify vectors even when their certified lengths differ syntactically. -/
private theorem vector_heq_of_toArray_eq {α : Type} {n m : Nat} (a : Vector α n) (b : Vector α m)
    (same : a.toArray = b.toArray) : HEq a b := by
  rcases a with ⟨a,ha⟩
  rcases b with ⟨b,hb⟩
  dsimp only at same
  subst b
  subst n
  subst m
  rfl

/-- Prepared high-row layers retain the exact selected-block stage. -/
theorem stripStagePlanned_eq (base high : Nat) (hd : base+high < 64) (rows : CompactRows (base+high) hd)
    (columns : Nat) {count : Nat} (positions : Vector (Fin (2^high)) count) (i : Fin high)
    (a : BF64.Packed.Buffer (2^high*columns)) :
    stripStagePlanned high columns i (prepareStripLayer base high hd rows positions i) a =
      stripSparseStage base high hd rows columns positions i a := by
  unfold stripStagePlanned prepareStripLayer stripSparseStage selectedStage
  rw [occupiedSweepRows_eq]
  have blocks : ((occupiedBlocks i positions).toArray.map Fin.val).map
      (fun b => (⟨b % 2^(high-i.val-1),Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : Fin (2^(high-i.val-1)))) =
      (occupiedBlocks i positions).toArray := by
    rw [Array.map_map]
    apply Array.map_id''
    intro b
    exact Fin.ext (Nat.mod_eq_of_lt b.isLt)
  simp only [blocks,Nat.zero_add]
  congr 1
  · simp only [Array.size_map,List.size_toArray]
  · apply vector_heq_of_toArray_eq
    rfl
  · apply vector_heq_of_toArray_eq
    simp only [Vector.toArray_ofFn]
    apply Array.ext
    · simp only [Array.size_map,List.size_toArray,Array.size_ofFn]
    · intro j left right
      simp only [Array.getElem_map,Array.getElem_ofFn,rowMultiplier,Vector.getElem_mk,Fin.getElem_fin]

/-- Execute a column strip from the retained occupied high-row plan. -/
def stripRunPlanned (high columns : Nat) (plan : Vector StripPlanLayer high) :
    (steps : Nat) → steps ≤ high → BF64.Packed.Buffer (2^high*columns) → BF64.Packed.Buffer (2^high*columns)
  | 0,_,a => a
  | steps+1,bound,a => stripStagePlanned high columns ⟨steps,by omega⟩ plan[steps]
      (stripRunPlanned high columns plan steps (by omega) a)

/-- A shared high-row plan retains every occupied strip stage. -/
theorem stripRunPlanned_eq (base high : Nat) (hd : base+high < 64) (rows : CompactRows (base+high) hd)
    (columns : Nat) {count : Nat} (positions : Vector (Fin (2^high)) count)
    (plan : Vector StripPlanLayer high) (same : ∀ i, plan[i] = prepareStripLayer base high hd rows positions i)
    (steps : Nat) (bound : steps ≤ high) (a : BF64.Packed.Buffer (2^high*columns)) :
    stripRunPlanned high columns plan steps bound a = stripSparseRun base high hd rows columns positions steps bound a := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    rw [stripRunPlanned,stripSparseRun,ih]
    have entry := same ⟨steps,by omega⟩
    simp only [Fin.getElem_fin] at entry
    rw [entry,stripStagePlanned_eq]

/-- Equal source coordinates give identical collapsed replica buffers. -/
theorem collapseRows_congr (keep rate columns : Nat)
    (a b : BF64.Packed.Buffer (2^(keep+rate)*columns))
    (same : ∀ i, BF64.Packed.read a i = BF64.Packed.read b i) :
    collapseRows keep rate columns a = collapseRows keep rate columns b := by
  simp only [collapseRows,same]

/-- Occupied window and strip induction with one shared high-row plan. -/
def tiledInduceSparse (base keep rate stripe : Nat) (stripeBound : stripe ≤ base)
    (hd : base+(keep+rate) < 64) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2^(base+(keep+rate)))) count) (values : Fin count → Fin lanes → Word) :
    BF64.Packed.Buffer (2^(base+keep)*lanes) :=
  let rows := CompactRows.create (base+(keep+rate)) hd
  let windows := occupiedWindows rows base lanes (by omega) positions values
  let highPositions := queryWindows base (keep+rate) positions
  let plan := Vector.ofFn fun i => prepareStripLayer base (keep+rate) hd rows highPositions i
  let strips := Vector.ofFn fun strip : Fin (2^(base-stripe)) =>
    let fits : strip.val*(2^stripe*lanes)+(2^stripe*lanes) ≤ 2^base*lanes := by
      rw [← stripColumnCount base stripe lanes stripeBound]
      have bound := Nat.mul_le_mul_right (2^stripe*lanes) (show strip.val+1 ≤ 2^(base-stripe) by have := strip.isLt; omega)
      nlinarith
    collapseRows keep rate (2^stripe*lanes)
      (stripRunPlanned (keep+rate) (2^stripe*lanes) plan keep (by omega)
        (windowStripInput base (keep+rate) lanes (2^stripe*lanes) (strip.val*(2^stripe*lanes)) fits windows))
  materializeStrips base keep stripe lanes stripeBound strips

/-- The shared occupied high-row plan equals the complete certified tiled transpose. -/
theorem tiledInduceSparse_eq (base keep rate stripe : Nat) (stripeBound : stripe ≤ base)
    (hd : base+(keep+rate) < 64) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2^(base+(keep+rate)))) count) (values : Fin count → Fin lanes → Word) :
    tiledInduceSparse base keep rate stripe stripeBound hd lanes positions values =
      tiledInduceCore base keep rate stripe stripeBound hd lanes positions values := by
  unfold tiledInduceSparse tiledInduceCore
  apply congrArg (materializeStrips base keep stripe lanes stripeBound)
  apply congrArg Vector.ofFn
  funext strip
  dsimp only
  rw [stripRunPlanned_eq base (keep+rate) hd (CompactRows.create (base+(keep+rate)) hd)
    (2^stripe*lanes) (queryWindows base (keep+rate) positions) _
    (fun i => by simp only [Fin.getElem_fin,Vector.getElem_ofFn])]
  unfold windowStripResult
  apply collapseRows_congr
  exact (stripSparseRun_refines base (keep+rate) hd _ _ _ keep (by omega) _
    (windowStripInput_support base (keep+rate) hd _ _ _ _ _ positions values)).2

/-- The prepared tiled entry point executes the certified occupied strip plan. -/
@[csimp] theorem tiledInducePrepared_code : @tiledInducePrepared = @tiledInduceSparse := by
  funext base keep rate stripe stripeBound hd lanes count positions values
  exact (congrFun (congrFun (congrFun (congrFun (congrFun (congrFun (congrFun (congrFun
    (congrFun (congrFun tiledInduceCore_code base) keep) rate) stripe) stripeBound) hd) lanes) count) positions) values).symm.trans
      (tiledInduceSparse_eq base keep rate stripe stripeBound hd lanes positions values).symm

/-- Sparse window and strip storage with occupied high-stage plans. -/
def induceSparseStripRows {ell rate : Nat} (hd : ell+rate < 64) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2^(ell+rate))) count) (values : Fin count → Fin lanes → Word) :
    BF64.Packed.Buffer (2^ell*lanes) :=
  let base := min 10 ell
  let keep := ell-base
  let same : base+keep = ell := Nat.add_sub_of_le (Nat.min_le_right _ _)
  let positions' := positions.map (Fin.cast (congrArg (fun k => 2^(k+rate)) same.symm))
  let result := tiledInduceSparse base keep rate (min 4 base) (Nat.min_le_right _ _) (by omega) lanes
    (positions'.map (Fin.cast (congrArg (fun k => 2^k) (Nat.add_assoc base keep rate)))) values
  ⟨result.val,result.property.trans (congrArg (fun k => 2^k*lanes) same)⟩

/-- Occupied high-stage plans preserve every coordinate of window and strip induction. -/
theorem induceSparseStripRows_eq {ell rate : Nat} (hd : ell+rate < 64) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2^(ell+rate))) count) (values : Fin count → Fin lanes → Word) :
    induceSparseStripRows hd lanes positions values = induceWindowStripRows hd lanes positions values := by
  unfold induceSparseStripRows induceWindowStripRows
  simp only [tiledInduceSparse_eq]

/-- Sparse strips retain the complete encoder-transpose coordinates. -/
theorem induceSparseStripRows_refines {ell rate : Nat} (hd : ell+rate < 64)
    (plan : Packed.FlatPlan (ell+rate) hd) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2^(ell+rate))) count) (values : Fin count → Fin lanes → Word)
    (index : Fin (2^ell*lanes)) :
    BF64.Packed.read (induceSparseStripRows hd lanes positions values) index =
      BF64.Packed.read (induceRows hd plan lanes positions values) index := by
  rw [induceSparseStripRows_eq]
  exact induceWindowStripRows_refines hd plan lanes positions values index

end CompStark.Pcs
