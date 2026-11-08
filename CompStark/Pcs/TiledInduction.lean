/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Algorithms derived from succinctlabs/flock (flock-core), MIT OR Apache-2.0.
Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum.
Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang.
-/
module
public import CompStark.Pcs.TwiddleRow

/-! Window and column-strip projections of additive transpose stages. -/
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
@[expose] public section
namespace CompStark.Pcs
open BF64 AdditiveNTT

/-- Copy a closed tile of a packed buffer into contiguous tileSize storage. -/
def tileProject {global tileSize : Nat} (address : Fin tileSize → Fin global)
    (a : BF64.Packed.Buffer global) : BF64.Packed.Buffer tileSize :=
  Packed.tabulate tileSize fun i => BF64.Packed.read a (address i)

/-- A closed tile executes a disjoint butterfly stage independently of the other tiles. -/
theorem tileSweep_read {global tileSize globalPairs localPairs : Nat}
    (address : Fin tileSize → Fin global)
    (localIndex : Fin localPairs × Fin 2 ≃ Fin tileSize)
    (globalIndex : Fin globalPairs × Fin 2 ≃ Fin global)
    (pair : Fin localPairs → Fin globalPairs)
    (closed : ∀ t b, address (localIndex (t,b)) = globalIndex (pair t,b))
    (op : Fin globalPairs → Word → Word → Word × Word)
    (a : BF64.Packed.Buffer global) (x : Fin tileSize) :
    BF64.Packed.read (Packed.sweep localIndex (fun t => op (pair t)) (tileProject address a)) x =
      BF64.Packed.read (Packed.sweep globalIndex op a) (address x) := by
  obtain ⟨⟨t,b⟩,rfl⟩ := localIndex.surjective x
  rw [Packed.read_sweep _ localIndex.injective, closed, Packed.read_sweep _ globalIndex.injective]
  simp only [tileProject, Packed.read_tabulate, closed]

/-- Changing a tile's materialization preserves a disjoint tileSize stage. -/
theorem tileSweep_congr {tileSize localPairs : Nat}
    (index : Fin localPairs × Fin 2 ≃ Fin tileSize)
    (op : Fin localPairs → Word → Word → Word × Word)
    (a b : BF64.Packed.Buffer tileSize)
    (same : ∀ x, BF64.Packed.read a x = BF64.Packed.read b x) (x : Fin tileSize) :
    BF64.Packed.read (Packed.sweep index op a) x = BF64.Packed.read (Packed.sweep index op b) x := by
  obtain ⟨⟨t,side⟩,rfl⟩ := index.surjective x
  simp only [Packed.read_sweep _ index.injective, same]

/-- Embed one contiguous window in its complete additive domain. -/
@[inline] def windowAddress (d width lanes : Nat) (bound : width ≤ d)
    (window : Fin (2^(d-width))) (x : Fin (2^width*lanes)) : Fin (2^d*lanes) :=
  ⟨window.val*(2^width*lanes)+x.val, by
    have shape : 2^d*lanes = 2^(d-width)*(2^width*lanes) := by
      rw [← Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel bound]
    rw [shape]
    have := window.isLt
    have := x.isLt
    nlinarith⟩

/-- Number of stage blocks per window and across the complete domain. -/
theorem windowBlockCount (d width : Nat) (bound : width ≤ d) (i : Fin width) :
    2^(d-i.val-1) = 2^(d-width)*2^(width-i.val-1) := by
  rw [← pow_add]
  congr 1
  have := i.isLt
  omega

/-- Embed a window's local butterfly pair into the complete stage. -/
@[inline] def windowPair (d width lanes : Nat) (bound : width ≤ d) (i : Fin width)
    (window : Fin (2^(d-width)))
    (t : Fin (2^(width-i.val-1)*(2^i.val*lanes))) :
    Fin (2^(d-i.val-1)*(2^i.val*lanes)) :=
  finProdFinEquiv (⟨window.val*2^(width-i.val-1)+t.divNat.val, by
    rw [windowBlockCount d width bound i]
    have := window.isLt
    have := t.divNat.isLt
    nlinarith⟩,t.modNat)

/-- Every low stage pairs coordinates inside their original window. -/
theorem windowStage_closed (d width lanes : Nat) (bound : width ≤ d) (i : Fin width)
    (window : Fin (2^(d-width)))
    (t : Fin (2^(width-i.val-1)*(2^i.val*lanes))) (side : Fin 2) :
    windowAddress d width lanes bound window (Packed.stageIndex width i lanes (t,side)) =
      Packed.stageIndex d ⟨i.val, by have := i.isLt; omega⟩ lanes
        (windowPair d width lanes bound i window t,side) := by
  have div : (windowPair d width lanes bound i window t).divNat =
      (⟨window.val*2^(width-i.val-1)+t.divNat.val, by
        rw [windowBlockCount d width bound i]
        have := window.isLt
        have := t.divNat.isLt
        nlinarith⟩ : Fin (2^(d-i.val-1))) :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply _)
  have mod : (windowPair d width lanes bound i window t).modNat = t.modNat :=
    congrArg Prod.snd (finProdFinEquiv.symm_apply_apply _)
  apply Fin.ext
  change window.val*(2^width*lanes)+(t.modNat.val+(2^i.val*lanes)*side.val+
    2*(2^i.val*lanes)*t.divNat.val) =
    (windowPair d width lanes bound i window t).modNat.val+(2^i.val*lanes)*side.val+
      2*(2^i.val*lanes)*(windowPair d width lanes bound i window t).divNat.val
  rw [div, mod]
  have size := Packed.stage_word_count width i lanes
  nlinarith

/-- A window-local block retains the domain's normalized-row address. -/
@[inline] def windowBlock (d width : Nat) (bound : width ≤ d) (i : Fin width)
    (window : Fin (2^(d-width))) (b : Fin (2^(width-i.val-1))) : Fin (2^(d-i.val-1)) :=
  ⟨window.val*2^(width-i.val-1)+b.val, by
    rw [windowBlockCount d width bound i]
    have := window.isLt
    have := b.isLt
    nlinarith⟩

/-- An identity block vector preserves a flattened pair index. -/
theorem occupiedPair_identity (blocks span : Nat) (t : Fin (blocks*span)) :
    occupiedPairCached (Vector.ofFn (fun b : Fin blocks => b)) span t = t := by
  apply Fin.ext
  simp only [occupiedPairCached, Fin.getElem_fin, Vector.getElem_ofFn]
  change (t.val/span)*span+t.val%span = t.val
  simpa only [Nat.mul_comm] using Nat.div_add_mod t.val span

/-- A local window stage with one compact-row multiplier per block. -/
def windowStage {d : Nat} {hd : d < 64} (rows : CompactRows d hd) (width lanes : Nat)
    (bound : width ≤ d) (i : Fin width) (window : Fin (2^(d-width)))
    (a : BF64.Packed.Buffer (2^width*lanes)) : BF64.Packed.Buffer (2^width*lanes) :=
  let globalI : Fin d := ⟨i.val, by have := i.isLt; omega⟩
  let multipliers := Vector.ofFn fun b : Fin (2^(width-i.val-1)) =>
    let scalar := rows.stages[globalI].2.lookup (windowBlock d width bound i window b).val
    if d-i.val-1 < 8 then inductionMultiplier scalar else Packed.Multiplier.masked scalar
  occupiedSweepBlocks (Vector.ofFn (fun b : Fin (2^(width-i.val-1)) => b))
    (2^i.val*lanes) (Packed.stage_word_count width i lanes) multipliers a

/-- Window-local blocked sweeps have the complete local pair partition. -/
theorem windowStage_eq {d : Nat} {hd : d < 64} (rows : CompactRows d hd)
    (plan : Packed.FlatPlan d hd) (width lanes : Nat) (bound : width ≤ d)
    (i : Fin width) (window : Fin (2^(d-width))) (a : BF64.Packed.Buffer (2^width*lanes)) :
    windowStage rows width lanes bound i window a =
      Packed.sweep (Packed.stageIndex width i lanes)
        (fun t => transposePair (plan.get ⟨i.val, by have := i.isLt; omega⟩
          (windowBlock d width bound i window t.divNat))) a := by
  unfold windowStage
  rw [occupiedSweepBlocks_eq]
  have indices : (fun p => Fin.cast (Packed.stage_word_count width i lanes)
      (occupiedIndexCached (Vector.ofFn (fun b : Fin (2^(width-i.val-1)) => b)) (2^i.val*lanes) p)) =
      Packed.stageIndex width i lanes := by
    funext p
    rw [occupiedIndexCached_eq, occupiedPair_identity]
  rw [indices]
  apply congrArg (fun op => Packed.sweep (Packed.stageIndex width i lanes) op a)
  funext t u v
  apply transposePair_scalar_eq
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  split <;> change rows.stages[(⟨i.val, by have := i.isLt; omega⟩ : Fin d)].2.lookup
    (windowBlock d width bound i window t.divNat).val = _
  all_goals exact (rows.lookup_eq _ _).trans (plan.scalar_eq _ _).symm

section
attribute [local irreducible] transposePair BF64.Packed.read Packed.sweep

/-- A window stage agrees with projection of the corresponding complete transpose stage. -/
theorem windowStage_read {d : Nat} {hd : d < 64} (rows : CompactRows d hd)
    (plan : Packed.FlatPlan d hd) (width lanes : Nat) (bound : width ≤ d)
    (i : Fin width) (window : Fin (2^(d-width))) (a : BF64.Packed.Buffer (2^d*lanes))
    (x : Fin (2^width*lanes)) :
    BF64.Packed.read (windowStage rows width lanes bound i window
      (tileProject (windowAddress d width lanes bound window) a)) x =
      BF64.Packed.read (Packed.stageSweep plan ⟨i.val, by have := i.isLt; omega⟩ lanes sparseTransposePair a)
        (windowAddress d width lanes bound window x) := by
  rw [windowStage_eq rows plan, Packed.stageSweep_eq_sweep]
  have pairDiv (t : Fin (2^(width-i.val-1)*(2^i.val*lanes))) :
      (windowPair d width lanes bound i window t).divNat = windowBlock d width bound i window t.divNat :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply _)
  rw [show sparseTransposePair = transposePair from funext fun m => funext fun u => funext fun v => sparseTransposePair_eq m u v]
  have proof := tileSweep_read (windowAddress d width lanes bound window)
    (Packed.stageIndex width i lanes)
    (Packed.stageIndex d ⟨i.val, by have := i.isLt; omega⟩ lanes)
    (windowPair d width lanes bound i window) (windowStage_closed d width lanes bound i window)
    (fun t => transposePair (plan.get ⟨i.val, by have := i.isLt; omega⟩ t.divNat)) a x
  simpa only [pairDiv] using proof

/-- Local window stages preserve equality of every input coordinate. -/
theorem windowStage_congr {d : Nat} {hd : d < 64} (rows : CompactRows d hd)
    (plan : Packed.FlatPlan d hd) (width lanes : Nat) (bound : width ≤ d)
    (i : Fin width) (window : Fin (2^(d-width))) (a b : BF64.Packed.Buffer (2^width*lanes))
    (same : ∀ x, BF64.Packed.read a x = BF64.Packed.read b x) (x : Fin (2^width*lanes)) :
    BF64.Packed.read (windowStage rows width lanes bound i window a) x =
      BF64.Packed.read (windowStage rows width lanes bound i window b) x := by
  rw [windowStage_eq rows plan, windowStage_eq rows plan]
  exact tileSweep_congr _ _ a b same x

/-- Run the transpose prefix entirely within one contiguous window. -/
def windowRun {d : Nat} {hd : d < 64} (rows : CompactRows d hd) (width lanes : Nat)
    (bound : width ≤ d) (window : Fin (2^(d-width))) :
    (steps : Nat) → steps ≤ width → BF64.Packed.Buffer (2^width*lanes) → BF64.Packed.Buffer (2^width*lanes)
  | 0, _, a => a
  | steps+1, hsteps, a => windowStage rows width lanes bound ⟨steps, by omega⟩ window
      (windowRun rows width lanes bound window steps (by omega) a)

/-- A complete local prefix is the window projection of the complete-domain prefix. -/
theorem windowRun_read {d : Nat} {hd : d < 64} (rows : CompactRows d hd)
    (plan : Packed.FlatPlan d hd) (width lanes : Nat) (bound : width ≤ d)
    (window : Fin (2^(d-width))) (steps : Nat) (hsteps : steps ≤ width)
    (a : BF64.Packed.Buffer (2^d*lanes)) (x : Fin (2^width*lanes)) :
    BF64.Packed.read (windowRun rows width lanes bound window steps hsteps
      (tileProject (windowAddress d width lanes bound window) a)) x =
      BF64.Packed.read (transposeRows plan steps (by omega) lanes a)
        (windowAddress d width lanes bound window x) := by
  induction steps generalizing x with
  | zero => exact Packed.read_tabulate _ _ _
  | succ steps ih =>
    change BF64.Packed.read (windowStage rows width lanes bound ⟨steps, by omega⟩ window
      (windowRun rows width lanes bound window steps (by omega)
        (tileProject (windowAddress d width lanes bound window) a))) x = _
    calc
      _ = BF64.Packed.read (windowStage rows width lanes bound ⟨steps, by omega⟩ window
        (tileProject (windowAddress d width lanes bound window)
          (transposeRows plan steps (by omega) lanes a))) x := by
        apply windowStage_congr rows plan
        intro y
        simp only [tileProject, Packed.read_tabulate]
        exact ih (by omega) y
      _ = _ := by
        rw [windowStage_read rows plan]
        unfold transposeRows
        rw [Fin.foldl_succ_last]
        rfl

/-- Select a contiguous column strip across every row of a row-major buffer. -/
@[inline] def stripAddress (rows columns fullColumns offset : Nat)
    (fits : offset+columns ≤ fullColumns) (x : Fin (rows*columns)) : Fin (rows*fullColumns) :=
  ⟨x.divNat.val*fullColumns+offset+x.modNat.val, by
    have := x.divNat.isLt
    have := x.modNat.isLt
    nlinarith⟩

/-- Strip projection retains each selected row and column. -/
theorem stripAddress_mk (rows columns fullColumns offset : Nat)
    (fits : offset+columns ≤ fullColumns) (r : Fin rows) (c : Fin columns) :
    stripAddress rows columns fullColumns offset fits (finProdFinEquiv (r,c)) =
      finProdFinEquiv (r,(⟨offset+c.val, by have := c.isLt; omega⟩ : Fin fullColumns)) := by
  have div : (finProdFinEquiv (r,c)).divNat = r := congrArg Prod.fst (finProdFinEquiv.symm_apply_apply _)
  have mod : (finProdFinEquiv (r,c)).modNat = c := congrArg Prod.snd (finProdFinEquiv.symm_apply_apply _)
  apply Fin.ext
  change (finProdFinEquiv (r,c)).divNat.val*fullColumns+offset+(finProdFinEquiv (r,c)).modNat.val = _
  rw [div,mod]
  change r.val*fullColumns+offset+c.val = offset+c.val+fullColumns*r.val
  ac_rfl

/-- Lift a row butterfly through a contiguous set of scalar columns. -/
@[inline] def columnIndex {rows pairs : Nat} (index : Fin pairs × Fin 2 ≃ Fin rows) (columns : Nat) :
    Fin (pairs*columns) × Fin 2 ≃ Fin (rows*columns) where
  toFun p := finProdFinEquiv (index (p.1.divNat,p.2),p.1.modNat)
  invFun x := (finProdFinEquiv ((index.symm x.divNat).1,x.modNat),(index.symm x.divNat).2)
  left_inv p := by
    have div (r : Fin rows) (c : Fin columns) : (finProdFinEquiv (r,c)).divNat = r :=
      congrArg Prod.fst (finProdFinEquiv.symm_apply_apply _)
    have mod (r : Fin rows) (c : Fin columns) : (finProdFinEquiv (r,c)).modNat = c :=
      congrArg Prod.snd (finProdFinEquiv.symm_apply_apply _)
    simp only [div, mod, Equiv.symm_apply_apply]
    exact Prod.ext (finProdFinEquiv.apply_symm_apply p.1) rfl
  right_inv x := by
    have div (r : Fin pairs) (c : Fin columns) : (finProdFinEquiv (r,c)).divNat = r :=
      congrArg Prod.fst (finProdFinEquiv.symm_apply_apply _)
    have mod (r : Fin pairs) (c : Fin columns) : (finProdFinEquiv (r,c)).modNat = c :=
      congrArg Prod.snd (finProdFinEquiv.symm_apply_apply _)
    simp only [div, mod, Prod.mk.eta, Equiv.apply_symm_apply]
    exact finProdFinEquiv.apply_symm_apply x

/-- A strip's pair map retains its source row and shifts its selected column. -/
@[inline] def stripPair (pairs columns fullColumns offset : Nat)
    (fits : offset+columns ≤ fullColumns) (t : Fin (pairs*columns)) : Fin (pairs*fullColumns) :=
  finProdFinEquiv (t.divNat,(⟨offset+t.modNat.val, by have := t.modNat.isLt; omega⟩ : Fin fullColumns))

/-- Column strips are closed under every lifted row butterfly. -/
theorem columnIndex_strip {rows pairs : Nat} (index : Fin pairs × Fin 2 ≃ Fin rows)
    (columns fullColumns offset : Nat) (fits : offset+columns ≤ fullColumns)
    (t : Fin (pairs*columns)) (side : Fin 2) :
    stripAddress rows columns fullColumns offset fits (columnIndex index columns (t,side)) =
      columnIndex index fullColumns (stripPair pairs columns fullColumns offset fits t,side) := by
  have div : (stripPair pairs columns fullColumns offset fits t).divNat = t.divNat :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply _)
  have mod : (stripPair pairs columns fullColumns offset fits t).modNat =
      (⟨offset+t.modNat.val, by have := t.modNat.isLt; omega⟩ : Fin fullColumns) :=
    congrArg Prod.snd (finProdFinEquiv.symm_apply_apply _)
  change stripAddress rows columns fullColumns offset fits
    (finProdFinEquiv (index (t.divNat,side),t.modNat)) = _
  rw [stripAddress_mk]
  change _ = finProdFinEquiv (index ((stripPair pairs columns fullColumns offset fits t).divNat,side),
    (stripPair pairs columns fullColumns offset fits t).modNat)
  rw [div,mod]

/-- A scalar-row stage partition without a trailing singleton lane. -/
@[inline] def rowStageIndex (d : Nat) (i : Fin d) :
    Fin (2^(d-i.val-1)*2^i.val) × Fin 2 ≃ Fin (2^d) :=
  (Equiv.prodCongr (finCongr (by simp only [Nat.mul_one])).symm (Equiv.refl _)).trans
    ((Packed.stageIndex d i 1).trans (finCongr (Nat.mul_one _)))

/-- Lifting a row partition through columns is the row-major additive stage. -/
theorem columnIndex_stage (d : Nat) (i : Fin d) (columns : Nat)
    (t : Fin ((2^(d-i.val-1)*2^i.val)*columns)) (side : Fin 2) :
    columnIndex (rowStageIndex d i) columns (t,side) =
      Packed.stageIndex d i columns (Fin.cast (Nat.mul_assoc _ _ _) t,side) := by
  apply Fin.ext
  dsimp only [columnIndex, rowStageIndex, Packed.stageIndex, Equiv.trans, Equiv.prodCongr, Equiv.symm, Equiv.coe_fn_mk, finCongr, finProdFinEquiv, Fin.cast, Fin.divNat, Fin.modNat]
  simp only [Nat.mul_one]
  change t.val%columns+columns*((t.val/columns)%2^i.val+2^i.val*side.val+
    2*2^i.val*((t.val/columns)/2^i.val)) =
    t.val%(2^i.val*columns)+(2^i.val*columns)*side.val+
      2*(2^i.val*columns)*(t.val/(2^i.val*columns))
  rw [Nat.div_div_eq_div_mul]
  have mods := Nat.mod_mul (x := t.val) (a := columns) (b := 2^i.val)
  rw [Nat.mul_comm columns (2^i.val)] at mods ⊢
  rw [mods]
  ring

/-- A stage above the window sees one row per window. -/
theorem stripStagePairCount (base high lanes : Nat) (i : Fin high) :
    (2^(high-i.val-1)*2^i.val)*(2^base*lanes) =
      2^((base+high)-(base+i.val)-1)*(2^(base+i.val)*lanes) := by
  have subtract : base+high-(base+i.val)-1 = high-i.val-1 := by omega
  rw [subtract, pow_add]
  ac_rfl

/-- The strip view and complete-domain view contain the same words. -/
theorem stripWordCount (base high lanes : Nat) :
    2^high*(2^base*lanes) = 2^(base+high)*lanes := by
  rw [pow_add]
  ac_rfl

/-- The lifted row partition is the complete-domain stage above the window. -/
theorem stripStageIndex (base high lanes : Nat) (i : Fin high)
    (t : Fin ((2^(high-i.val-1)*2^i.val)*(2^base*lanes))) (side : Fin 2) :
    Fin.cast (stripWordCount base high lanes)
      (columnIndex (rowStageIndex high i) (2^base*lanes) (t,side)) =
      Packed.stageIndex (base+high) ⟨base+i.val, by have := i.isLt; omega⟩ lanes
        (Fin.cast (stripStagePairCount base high lanes i) t,side) := by
  rw [columnIndex_stage]
  apply Fin.ext
  simp only [Packed.stageIndex, Equiv.coe_fn_mk, Fin.val_cast]
  have span : 2^i.val*(2^base*lanes) = 2^(base+i.val)*lanes := by
    rw [pow_add]
    ac_rfl
  rw [span]

/-- A column strip embeds the low-window row view into the complete domain. -/
@[inline] def domainStripAddress (base high lanes columns offset : Nat)
    (fits : offset+columns ≤ 2^base*lanes) (x : Fin (2^high*columns)) : Fin (2^(base+high)*lanes) :=
  Fin.cast (stripWordCount base high lanes) (stripAddress (2^high) columns (2^base*lanes) offset fits x)

/-- A strip pair retains its row butterfly and selected complete-domain column. -/
@[inline] def domainStripPair (base high lanes columns offset : Nat)
    (fits : offset+columns ≤ 2^base*lanes) (i : Fin high)
    (t : Fin ((2^(high-i.val-1)*2^i.val)*columns)) :
    Fin (2^((base+high)-(base+i.val)-1)*(2^(base+i.val)*lanes)) :=
  Fin.cast (stripStagePairCount base high lanes i)
    (stripPair (2^(high-i.val-1)*2^i.val) columns (2^base*lanes) offset fits t)

/-- Every high transpose stage remains inside each projected column strip. -/
theorem domainStrip_closed (base high lanes columns offset : Nat)
    (fits : offset+columns ≤ 2^base*lanes) (i : Fin high)
    (t : Fin ((2^(high-i.val-1)*2^i.val)*columns)) (side : Fin 2) :
    domainStripAddress base high lanes columns offset fits
      (columnIndex (rowStageIndex high i) columns (t,side)) =
      Packed.stageIndex (base+high) ⟨base+i.val, by have := i.isLt; omega⟩ lanes
        (domainStripPair base high lanes columns offset fits i t,side) := by
  unfold domainStripAddress domainStripPair
  rw [columnIndex_strip, stripStageIndex]

/-- A strip pair retains the original high-stage block number. -/
theorem domainStripPair_block (base high lanes columns offset : Nat)
    (fits : offset+columns ≤ 2^base*lanes) (i : Fin high)
    (t : Fin ((2^(high-i.val-1)*2^i.val)*columns)) :
    (domainStripPair base high lanes columns offset fits i t).divNat.val =
      t.val/(2^i.val*columns) := by
  have row : (stripPair (2^(high-i.val-1)*2^i.val) columns (2^base*lanes) offset fits t).divNat = t.divNat :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply _)
  have span : 2^(base+i.val)*lanes = (2^base*lanes)*2^i.val := by
    rw [pow_add]
    ac_rfl
  change (stripPair (2^(high-i.val-1)*2^i.val) columns (2^base*lanes) offset fits t).val /
    (2^(base+i.val)*lanes) = _
  rw [span, ← Nat.div_div_eq_div_mul]
  change (stripPair (2^(high-i.val-1)*2^i.val) columns (2^base*lanes) offset fits t).divNat.val / 2^i.val = _
  rw [row]
  change (t.val/columns)/2^i.val = _
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm columns (2^i.val)]

/-- Sweep a column strip with the normalized row of the original domain. -/
def stripStage (base high : Nat) (hd : base+high < 64) (rows : CompactRows (base+high) hd)
    (columns : Nat) (i : Fin high) (a : BF64.Packed.Buffer (2^high*columns)) :
    BF64.Packed.Buffer (2^high*columns) :=
  occupiedSweepRows (Vector.ofFn (fun b : Fin (2^(high-i.val-1)) => b))
    (2^i.val*columns) (Packed.stage_word_count high i columns) 0
    rows.stages[(⟨base+i.val, by have := i.isLt; omega⟩ : Fin (base+high))].2 a

/-- A strip's native blocked stage uses exactly its original-domain multipliers. -/
theorem stripStage_eq (base high : Nat) (hd : base+high < 64) (rows : CompactRows (base+high) hd)
    (plan : Packed.FlatPlan (base+high) hd) (lanes columns offset : Nat)
    (fits : offset+columns ≤ 2^base*lanes) (i : Fin high)
    (a : BF64.Packed.Buffer (2^high*columns)) :
    stripStage base high hd rows columns i a =
      Packed.sweep (Packed.stageIndex high i columns)
        (fun t => transposePair (plan.get ⟨base+i.val, by have := i.isLt; omega⟩
          (domainStripPair base high lanes columns offset fits i
            (Fin.cast (Nat.mul_assoc _ _ _).symm t)).divNat)) a := by
  unfold stripStage
  rw [occupiedSweepRows_eq, occupiedSweepBlocks_eq]
  have indices : (fun p => Fin.cast (Packed.stage_word_count high i columns)
      (occupiedIndexCached (Vector.ofFn (fun b : Fin (2^(high-i.val-1)) => b)) (2^i.val*columns) p)) =
      Packed.stageIndex high i columns := by
    funext p
    rw [occupiedIndexCached_eq, occupiedPair_identity]
  rw [indices]
  apply congrArg (fun op => Packed.sweep (Packed.stageIndex high i columns) op a)
  funext t u v
  apply transposePair_scalar_eq
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Nat.zero_add]
  have scalar : rows.stages[(⟨base+i.val, by have := i.isLt; omega⟩ : Fin (base+high))].2.lookup t.divNat.val =
      (plan.get ⟨base+i.val, by have := i.isLt; omega⟩
        (domainStripPair base high lanes columns offset fits i (Fin.cast (Nat.mul_assoc _ _ _).symm t)).divNat).scalar := by
    have address : (domainStripPair base high lanes columns offset fits i
        (Fin.cast (Nat.mul_assoc _ _ _).symm t)).divNat.val = t.divNat.val := by
      exact domainStripPair_block base high lanes columns offset fits i (Fin.cast (Nat.mul_assoc _ _ _).symm t)
    rw [← address]
    exact (rows.lookup_eq _ _).trans (plan.scalar_eq _ _).symm
  split <;> exact scalar

/-- High transpose stages execute independently over contiguous column strips. -/
theorem stripStage_read (base high : Nat) (hd : base+high < 64) (rows : CompactRows (base+high) hd)
    (plan : Packed.FlatPlan (base+high) hd) (lanes columns offset : Nat)
    (fits : offset+columns ≤ 2^base*lanes) (i : Fin high)
    (a : BF64.Packed.Buffer (2^(base+high)*lanes)) (x : Fin (2^high*columns)) :
    BF64.Packed.read (stripStage base high hd rows columns i
      (tileProject (domainStripAddress base high lanes columns offset fits) a)) x =
      BF64.Packed.read (Packed.stageSweep plan ⟨base+i.val, by have := i.isLt; omega⟩ lanes sparseTransposePair a)
        (domainStripAddress base high lanes columns offset fits x) := by
  rw [stripStage_eq base high hd rows plan lanes columns offset fits, Packed.stageSweep_eq_sweep]
  rw [show sparseTransposePair = transposePair from funext fun m => funext fun u => funext fun v => sparseTransposePair_eq m u v]
  have closed (t : Fin (2^(high-i.val-1)*(2^i.val*columns))) (side : Fin 2) :
      domainStripAddress base high lanes columns offset fits (Packed.stageIndex high i columns (t,side)) =
        Packed.stageIndex (base+high) ⟨base+i.val, by have := i.isLt; omega⟩ lanes
          (domainStripPair base high lanes columns offset fits i (Fin.cast (Nat.mul_assoc _ _ _).symm t),side) := by
    have proof := domainStrip_closed base high lanes columns offset fits i
      (Fin.cast (Nat.mul_assoc _ _ _).symm t) side
    rw [columnIndex_stage] at proof
    exact proof
  exact tileSweep_read (domainStripAddress base high lanes columns offset fits)
    (Packed.stageIndex high i columns)
    (Packed.stageIndex (base+high) ⟨base+i.val, by have := i.isLt; omega⟩ lanes)
    (fun t => domainStripPair base high lanes columns offset fits i (Fin.cast (Nat.mul_assoc _ _ _).symm t))
    closed (fun t => transposePair (plan.get ⟨base+i.val, by have := i.isLt; omega⟩ t.divNat)) a x

/-- Equal strip inputs retain equal outputs through one blocked high stage. -/
theorem stripStage_congr (base high : Nat) (hd : base+high < 64) (rows : CompactRows (base+high) hd)
    (plan : Packed.FlatPlan (base+high) hd) (lanes columns offset : Nat)
    (fits : offset+columns ≤ 2^base*lanes) (i : Fin high)
    (a b : BF64.Packed.Buffer (2^high*columns))
    (same : ∀ x, BF64.Packed.read a x = BF64.Packed.read b x) (x : Fin (2^high*columns)) :
    BF64.Packed.read (stripStage base high hd rows columns i a) x =
      BF64.Packed.read (stripStage base high hd rows columns i b) x := by
  rw [stripStage_eq base high hd rows plan lanes columns offset fits,
    stripStage_eq base high hd rows plan lanes columns offset fits]
  exact tileSweep_congr _ _ a b same x

/-- Run high transpose stages in a contiguous column-strip buffer. -/
def stripRun (base high : Nat) (hd : base+high < 64) (rows : CompactRows (base+high) hd)
    (columns : Nat) :
    (steps : Nat) → steps ≤ high → BF64.Packed.Buffer (2^high*columns) → BF64.Packed.Buffer (2^high*columns)
  | 0, _, a => a
  | steps+1, bound, a => stripStage base high hd rows columns ⟨steps, by omega⟩
      (stripRun base high hd rows columns steps (by omega) a)

/-- A strip's complete high prefix is the projection of the complete-domain continuation. -/
theorem stripRun_read (base high : Nat) (hd : base+high < 64) (rows : CompactRows (base+high) hd)
    (plan : Packed.FlatPlan (base+high) hd) (lanes columns offset : Nat)
    (fits : offset+columns ≤ 2^base*lanes) (steps : Nat) (bound : steps ≤ high)
    (a : BF64.Packed.Buffer (2^(base+high)*lanes)) (x : Fin (2^high*columns)) :
    BF64.Packed.read (stripRun base high hd rows columns steps bound
      (tileProject (domainStripAddress base high lanes columns offset fits)
        (transposeRows plan base (by omega) lanes a))) x =
      BF64.Packed.read (transposeRows plan (base+steps) (by omega) lanes a)
        (domainStripAddress base high lanes columns offset fits x) := by
  induction steps generalizing x with
  | zero => exact Packed.read_tabulate _ _ _
  | succ steps ih =>
    change BF64.Packed.read (stripStage base high hd rows columns ⟨steps, by omega⟩
      (stripRun base high hd rows columns steps (by omega)
        (tileProject (domainStripAddress base high lanes columns offset fits)
          (transposeRows plan base (by omega) lanes a)))) x = _
    calc
      _ = BF64.Packed.read (stripStage base high hd rows columns ⟨steps, by omega⟩
        (tileProject (domainStripAddress base high lanes columns offset fits)
          (transposeRows plan (base+steps) (by omega) lanes a))) x := by
        apply stripStage_congr base high hd rows plan lanes columns offset fits
        intro y
        simp only [tileProject, Packed.read_tabulate]
        exact ih (by omega) y
      _ = _ := by
        rw [stripStage_read base high hd rows plan lanes columns offset fits]
        unfold transposeRows
        simp only [Nat.add_succ]
        rw [Fin.foldl_succ_last]
        rfl

/-- The multiplier reused by every pair of an occupied block in one retained row. -/
def rowMultiplier {n : Nat} (row : TwiddleRow n) (block : Nat) : Packed.Multiplier :=
  if n < 8 then inductionMultiplier (row.lookup block) else Packed.Multiplier.masked (row.lookup block)

/-- Execute only selected local blocks, retaining one row multiplier per outer loop. -/
def selectedStage {n : Nat} (row : TwiddleRow n) (d : Nat) (i : Fin d) (lanes offset : Nat)
    (blocks : List (Fin (2^(d-i.val-1)))) (a : BF64.Packed.Buffer (2^d*lanes)) :
    BF64.Packed.Buffer (2^d*lanes) :=
  occupiedSweepRows (⟨blocks.toArray,List.size_toArray⟩ : Vector _ blocks.length)
    (2^i.val*lanes) (Packed.stage_word_count d i lanes) offset row a

/-- The selected local blocks form a disjoint subset of the complete stage. -/
theorem selectedStage_eq {n : Nat} (row : TwiddleRow n) (d : Nat) (i : Fin d) (lanes offset : Nat)
    (blocks : List (Fin (2^(d-i.val-1)))) (a : BF64.Packed.Buffer (2^d*lanes)) :
    selectedStage row d i lanes offset blocks a =
      Packed.sweep (fun p => Packed.stageIndex d i lanes
        (occupiedPair blocks (2^i.val*lanes) p.1,p.2))
        (fun j => transposePair (rowMultiplier row (offset+(occupiedPair blocks (2^i.val*lanes) j).divNat.val))) a := by
  unfold selectedStage
  rw [occupiedSweepRows_eq, occupiedSweepBlocks_eq]
  simp only [occupiedIndexCached_eq, ← occupiedPairCached_eq, occupiedPairCached_divNat,
    Fin.getElem_fin, Vector.getElem_ofFn, rowMultiplier]

/-- Selected local stages update each live pair once and leave every omitted pair unchanged. -/
theorem selectedStage_read {n : Nat} (row : TwiddleRow n) (d : Nat) (i : Fin d) (lanes offset : Nat)
    (blocks : List (Fin (2^(d-i.val-1)))) (unique : blocks.Nodup)
    (a : BF64.Packed.Buffer (2^d*lanes)) (t : Fin (2^(d-i.val-1)*(2^i.val*lanes))) (b : Fin 2) :
    BF64.Packed.read (selectedStage row d i lanes offset blocks a) (Packed.stageIndex d i lanes (t,b)) =
      if t.divNat ∈ blocks then
        if b = 0 then (transposePair (rowMultiplier row (offset+t.divNat.val))
          (BF64.Packed.read a (Packed.stageIndex d i lanes (t,0)))
          (BF64.Packed.read a (Packed.stageIndex d i lanes (t,1)))).1
        else (transposePair (rowMultiplier row (offset+t.divNat.val))
          (BF64.Packed.read a (Packed.stageIndex d i lanes (t,0)))
          (BF64.Packed.read a (Packed.stageIndex d i lanes (t,1)))).2
      else BF64.Packed.read a (Packed.stageIndex d i lanes (t,b)) := by
  let selected := occupiedPair blocks (2^i.val*lanes)
  have injective : Function.Injective (fun p : Fin (blocks.length*(2^i.val*lanes)) × Fin 2 =>
      Packed.stageIndex d i lanes (selected p.1,p.2)) := by
    intro x y h
    have components := (Packed.stageIndex d i lanes).injective h
    apply Prod.ext
    · exact occupiedPair_injective blocks _ unique (congrArg Prod.fst components)
    · have second := congrArg Prod.snd components
      exact second
  by_cases member : t.divNat ∈ blocks
  · obtain ⟨j,entry⟩ := (occupiedPair_range blocks _ t).mpr member
    simp only [member, ↓reduceIte]
    rw [← entry, selectedStage_eq]
    change BF64.Packed.read (Packed.sweep _ _ a)
      ((fun p : Fin (blocks.length*(2^i.val*lanes)) × Fin 2 => Packed.stageIndex d i lanes (selected p.1,p.2)) (j,b)) = _
    rw [Packed.read_sweep _ injective]
  · simp only [member, ↓reduceIte]
    rw [selectedStage_eq]
    apply read_sweep_outside
    intro j side equal
    have components := (Packed.stageIndex d i lanes).injective equal
    exact member ((occupiedPair_range blocks _ t).mp ⟨j,congrArg Prod.fst components⟩)

/-- Split a complete-stage block into its containing window and local block. -/
@[inline] def windowParts (d width : Nat) (bound : width ≤ d) (i : Fin width)
    (block : Fin (2^(d-i.val-1))) : Fin (2^(d-width)*2^(width-i.val-1)) :=
  Fin.cast (windowBlockCount d width bound i) block

/-- Embedding a local block and splitting it recover the original window and block. -/
theorem windowParts_block (d width : Nat) (bound : width ≤ d) (i : Fin width)
    (window : Fin (2^(d-width))) (b : Fin (2^(width-i.val-1))) :
    windowParts d width bound i (windowBlock d width bound i window b) = finProdFinEquiv (window,b) := by
  apply Fin.ext
  simp only [windowParts, windowBlock, Fin.val_cast, finProdFinEquiv, Equiv.coe_fn_mk]
  ac_rfl

/-- Recombining the parts of a complete-stage block retains that block. -/
theorem windowBlock_parts (d width : Nat) (bound : width ≤ d) (i : Fin width)
    (block : Fin (2^(d-i.val-1))) :
    windowBlock d width bound i (windowParts d width bound i block).divNat
      (windowParts d width bound i block).modNat = block := by
  apply Fin.ext
  change ((block.val/2^(width-i.val-1))*2^(width-i.val-1))+block.val%2^(width-i.val-1) = block.val
  simpa only [Nat.mul_comm] using Nat.div_add_mod block.val (2^(width-i.val-1))

/-- Retain only occupied blocks inside one window and convert them to local indices. -/
def windowBlocks (d width : Nat) (bound : width ≤ d) (i : Fin width)
    (window : Fin (2^(d-width))) (blocks : List (Fin (2^(d-i.val-1)))) :
    List (Fin (2^(width-i.val-1))) :=
  (blocks.filterMap fun block =>
    let parts := windowParts d width bound i block
    if parts.divNat = window then some parts.modNat else none).dedup

/-- Local occupied blocks select exactly the corresponding occupied complete-domain blocks. -/
theorem mem_windowBlocks (d width : Nat) (bound : width ≤ d) (i : Fin width)
    (window : Fin (2^(d-width))) (blocks : List (Fin (2^(d-i.val-1))))
    (b : Fin (2^(width-i.val-1))) :
    b ∈ windowBlocks d width bound i window blocks ↔ windowBlock d width bound i window b ∈ blocks := by
  simp only [windowBlocks, List.mem_dedup, List.mem_filterMap]
  constructor
  · rintro ⟨block,member,equal⟩
    split at equal
    · rename_i same
      have localSame := Option.some.inj equal
      have source := windowBlock_parts d width bound i block
      rw [same,localSame] at source
      rw [source]
      exact member
    · cases equal
  · intro member
    refine ⟨windowBlock d width bound i window b,member,?_⟩
    rw [windowParts_block]
    have div : (finProdFinEquiv (window,b)).divNat = window :=
      congrArg Prod.fst (finProdFinEquiv.symm_apply_apply _)
    have mod : (finProdFinEquiv (window,b)).modNat = b :=
      congrArg Prod.snd (finProdFinEquiv.symm_apply_apply _)
    rw [div,mod,ite_eq_left rfl]

/-- Execute one occupied low stage entirely inside its local window buffer. -/
def windowSparseStage {d count : Nat} {hd : d < 64} (rows : CompactRows d hd)
    (width lanes : Nat) (bound : width ≤ d) (i : Fin width) (window : Fin (2^(d-width)))
    (positions : Vector (Fin (2^d)) count) (a : BF64.Packed.Buffer (2^width*lanes)) :
    BF64.Packed.Buffer (2^width*lanes) :=
  let globalI : Fin d := ⟨i.val, by have := i.isLt; omega⟩
  selectedStage rows.stages[globalI].2 width i lanes (window.val*2^(width-i.val-1))
    (windowBlocks d width bound i window (occupiedBlocks globalI positions)) a

/-- An occupied window stage is the exact projection of the global occupied stage. -/
theorem windowSparseStage_read {d count : Nat} {hd : d < 64} (rows : CompactRows d hd)
    (plan : Packed.FlatPlan d hd) (width lanes : Nat) (bound : width ≤ d)
    (i : Fin width) (window : Fin (2^(d-width))) (positions : Vector (Fin (2^d)) count)
    (a : BF64.Packed.Buffer (2^d*lanes)) (x : Fin (2^width*lanes)) :
    BF64.Packed.read (windowSparseStage rows width lanes bound i window positions
      (tileProject (windowAddress d width lanes bound window) a)) x =
      BF64.Packed.read (occupiedStage plan ⟨i.val, by have := i.isLt; omega⟩ lanes positions a)
        (windowAddress d width lanes bound window x) := by
  obtain ⟨⟨t,b⟩,rfl⟩ := (Packed.stageIndex width i lanes).surjective x
  have pairDiv : (windowPair d width lanes bound i window t).divNat =
      windowBlock d width bound i window t.divNat := congrArg Prod.fst (finProdFinEquiv.symm_apply_apply _)
  have pairEq : transposePair (rowMultiplier rows.stages[(⟨i.val, by have := i.isLt; omega⟩ : Fin d)].2
      (window.val*2^(width-i.val-1)+t.divNat.val)) =
      transposePair (plan.get ⟨i.val, by have := i.isLt; omega⟩ (windowBlock d width bound i window t.divNat)) := by
    funext u v
    apply transposePair_scalar_eq
    unfold rowMultiplier
    split <;> change rows.stages[(⟨i.val, by have := i.isLt; omega⟩ : Fin d)].2.lookup
      (windowBlock d width bound i window t.divNat).val = _
    all_goals exact (rows.lookup_eq _ _).trans (plan.scalar_eq _ _).symm
  unfold windowSparseStage
  dsimp only
  have unique : (windowBlocks d width bound i window
      (occupiedBlocks (⟨i.val, by have := i.isLt; omega⟩ : Fin d) positions)).Nodup := List.nodup_dedup _
  rw [selectedStage_read _ _ _ _ _ _ unique]
  rw [windowStage_closed, occupiedStage_read]
  simp only [pairDiv, mem_windowBlocks, pairEq, tileProject, Packed.read_tabulate, windowStage_closed]

/-- Equal inputs remain equal through a selected local stage. -/
theorem selectedStage_congr {n : Nat} (row : TwiddleRow n) (d : Nat) (i : Fin d) (lanes offset : Nat)
    (blocks : List (Fin (2^(d-i.val-1)))) (unique : blocks.Nodup)
    (a b : BF64.Packed.Buffer (2^d*lanes))
    (same : ∀ x, BF64.Packed.read a x = BF64.Packed.read b x) (x : Fin (2^d*lanes)) :
    BF64.Packed.read (selectedStage row d i lanes offset blocks a) x =
      BF64.Packed.read (selectedStage row d i lanes offset blocks b) x := by
  obtain ⟨⟨t,side⟩,rfl⟩ := (Packed.stageIndex d i lanes).surjective x
  simp only [selectedStage_read row d i lanes offset blocks unique, same]

/-- Equal window inputs remain equal through an occupied local stage. -/
theorem windowSparseStage_congr {d count : Nat} {hd : d < 64} (rows : CompactRows d hd)
    (width lanes : Nat) (bound : width ≤ d) (i : Fin width) (window : Fin (2^(d-width)))
    (positions : Vector (Fin (2^d)) count) (a b : BF64.Packed.Buffer (2^width*lanes))
    (same : ∀ x, BF64.Packed.read a x = BF64.Packed.read b x) (x : Fin (2^width*lanes)) :
    BF64.Packed.read (windowSparseStage rows width lanes bound i window positions a) x =
      BF64.Packed.read (windowSparseStage rows width lanes bound i window positions b) x := by
  unfold windowSparseStage
  exact selectedStage_congr _ _ _ _ _ _ (List.nodup_dedup _) a b same x

/-- Run the occupied low transpose stages in one independent window. -/
def windowSparseRun {d count : Nat} {hd : d < 64} (rows : CompactRows d hd)
    (width lanes : Nat) (bound : width ≤ d) (window : Fin (2^(d-width)))
    (positions : Vector (Fin (2^d)) count) :
    (steps : Nat) → steps ≤ width → BF64.Packed.Buffer (2^width*lanes) → BF64.Packed.Buffer (2^width*lanes)
  | 0, _, a => a
  | steps+1, hsteps, a => windowSparseStage rows width lanes bound ⟨steps, by omega⟩ window positions
      (windowSparseRun rows width lanes bound window positions steps (by omega) a)

/-- A window's occupied prefix is the projection of the complete occupied run. -/
theorem windowSparseRun_read {d count : Nat} {hd : d < 64} (rows : CompactRows d hd)
    (plan : Packed.FlatPlan d hd) (width lanes : Nat) (bound : width ≤ d)
    (window : Fin (2^(d-width))) (positions : Vector (Fin (2^d)) count)
    (steps : Nat) (hsteps : steps ≤ width) (a : BF64.Packed.Buffer (2^d*lanes)) (x : Fin (2^width*lanes)) :
    BF64.Packed.read (windowSparseRun rows width lanes bound window positions steps hsteps
      (tileProject (windowAddress d width lanes bound window) a)) x =
      BF64.Packed.read (occupiedRun plan lanes positions steps (by omega) a)
        (windowAddress d width lanes bound window x) := by
  induction steps generalizing x with
  | zero => exact Packed.read_tabulate _ _ _
  | succ steps ih =>
    change BF64.Packed.read (windowSparseStage rows width lanes bound ⟨steps, by omega⟩ window positions
      (windowSparseRun rows width lanes bound window positions steps (by omega)
        (tileProject (windowAddress d width lanes bound window) a))) x = _
    calc
      _ = BF64.Packed.read (windowSparseStage rows width lanes bound ⟨steps, by omega⟩ window positions
        (tileProject (windowAddress d width lanes bound window)
          (occupiedRun plan lanes positions steps (by omega) a))) x := by
        apply windowSparseStage_congr rows width lanes bound _ window positions
        intro y
        simp only [tileProject, Packed.read_tabulate]
        exact ih (by omega) y
      _ = _ := windowSparseStage_read rows plan width lanes bound _ window positions _ x

/-- A scattered coordinate is the sum of every ordered query limb addressed there. -/
theorem scatterRows_read (rows lanes : Nat) {count : Nat} (positions : Vector (Fin rows) count)
    (values : Fin count → Fin lanes → Word) (x : Fin (rows*lanes)) :
    (BF64.Packed.read (scatterRows rows lanes positions values) x).toField =
      ∑ q : Fin count, ∑ c : Fin lanes,
        if positions[q].val*lanes+c.val = x.val then (values q c).toField else 0 := by
  rw [← unitRows_pairing x, scatterRows_pairing]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro c _
  simp only [unitRows, Packed.read_tabulate, Fin.ext_iff]
  by_cases same : positions[q].val*lanes+c.val = x.val
  · simp only [same, ↓reduceIte]
    exact one_mul _
  · simp only [same, ↓reduceIte]
    exact zero_mul _

/-- Scatter query limbs directly into a window, masking queries in other windows. -/
def windowScatter {d count : Nat} (width lanes : Nat) (window : Fin (2^(d-width)))
    (positions : Vector (Fin (2^d)) count) (values : Fin count → Fin lanes → Word) :
    BF64.Packed.Buffer (2^width*lanes) :=
  scatterRows (2^width) lanes
    (positions.map fun p => (⟨p.val%2^width,Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : Fin (2^width)))
    (fun q c => if positions[q].val/2^width = window.val then values q c else ⟨0⟩)

/-- Window scattering preserves the exact projection, including duplicate query positions. -/
theorem windowScatter_read {d count : Nat} (width lanes : Nat) (bound : width ≤ d)
    (window : Fin (2^(d-width))) (positions : Vector (Fin (2^d)) count)
    (values : Fin count → Fin lanes → Word) (x : Fin (2^width*lanes)) :
    BF64.Packed.read (windowScatter width lanes window positions values) x =
      BF64.Packed.read (scatterRows (2^d) lanes positions values) (windowAddress d width lanes bound window x) := by
  apply Word.toField_injective
  rw [windowScatter,scatterRows_read,scatterRows_read]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro c _
  simp only [Fin.getElem_fin,Vector.getElem_map]
  have positive : 0 < 2^width*lanes := by have := x.isLt; omega
  have localBound : (positions[q.val].val%2^width)*lanes+c.val < 2^width*lanes := by
    have := Nat.mod_lt positions[q.val].val (Nat.two_pow_pos width)
    have := c.isLt
    nlinarith
  have decomposition : positions[q.val].val*lanes+c.val =
      (positions[q.val].val/2^width)*(2^width*lanes)+(positions[q.val].val%2^width)*lanes+c.val := by
    have := Nat.div_add_mod positions[q.val].val (2^width)
    nlinarith
  have insideOfEqual (same : positions[q.val].val*lanes+c.val =
      (windowAddress d width lanes bound window x).val) : positions[q.val].val/2^width = window.val := by
    have quot := congrArg (fun k => k/(2^width*lanes)) same
    change _ = (window.val*(2^width*lanes)+x.val)/(2^width*lanes) at quot
    rw [decomposition, Nat.add_assoc, Nat.mul_comm (positions[q.val].val/2^width), Nat.mul_add_div positive,
      Nat.div_eq_of_lt localBound, Nat.add_zero, Nat.mul_comm window.val, Nat.mul_add_div positive,
      Nat.div_eq_of_lt x.isLt, Nat.add_zero] at quot
    exact quot
  by_cases inside : positions[q.val].val/2^width = window.val
  · simp only [inside, ↓reduceIte]
    have address : (positions[q.val].val%2^width)*lanes+c.val = x.val ↔
        positions[q.val].val*lanes+c.val = (windowAddress d width lanes bound window x).val := by
      change _ ↔ positions[q.val].val*lanes+c.val = window.val*(2^width*lanes)+x.val
      rw [decomposition,inside]
      omega
    simp only [address]
  · have outside : positions[q.val].val*lanes+c.val ≠ (windowAddress d width lanes bound window x).val :=
      fun same => inside (insideOfEqual same)
    simp only [inside,outside,↓reduceIte]
    split <;> rfl

/-- Equal local scatters remain equal through an occupied window prefix. -/
theorem windowSparseRun_congr {d count : Nat} {hd : d < 64} (rows : CompactRows d hd)
    (width lanes : Nat) (bound : width ≤ d) (window : Fin (2^(d-width)))
    (positions : Vector (Fin (2^d)) count) (steps : Nat) (hsteps : steps ≤ width)
    (a b : BF64.Packed.Buffer (2^width*lanes))
    (same : ∀ x, BF64.Packed.read a x = BF64.Packed.read b x) (x : Fin (2^width*lanes)) :
    BF64.Packed.read (windowSparseRun rows width lanes bound window positions steps hsteps a) x =
      BF64.Packed.read (windowSparseRun rows width lanes bound window positions steps hsteps b) x := by
  induction steps generalizing x with
  | zero => exact same x
  | succ steps ih =>
    apply windowSparseStage_congr
    exact ih (by omega)

/-- Materialize only windows containing an original query. -/
def occupiedWindows {d count : Nat} {hd : d < 64} (rows : CompactRows d hd)
    (width lanes : Nat) (bound : width ≤ d) (positions : Vector (Fin (2^d)) count)
    (values : Fin count → Fin lanes → Word) : Vector (Option (BF64.Packed.Buffer (2^width*lanes))) (2^(d-width)) :=
  Vector.ofFn fun window =>
    if positions.any (fun p => decide (p.val/2^width = window.val)) then
      some (windowSparseRun rows width lanes bound window positions width (Nat.le_refl _)
        (windowScatter width lanes window positions values))
    else none

/-- Read an occupied window or the implicit zero coordinates of an absent window. -/
@[inline] def readWindow {d width lanes : Nat}
    (windows : Vector (Option (BF64.Packed.Buffer (2^width*lanes))) (2^(d-width)))
    (window : Fin (2^(d-width))) (x : Fin (2^width*lanes)) : Word :=
  match windows[window] with
  | none => ⟨0⟩
  | some data => BF64.Packed.read data x

/-- Run a window prefix with the occupied complete-domain blocks shared across windows. -/
def windowRunCached {d : Nat} {hd : d < 64} (rows : CompactRows d hd)
    (width lanes : Nat) (bound : width ≤ d) (window : Fin (2^(d-width)))
    (blocks : (i : Fin width) → List (Fin (2^(d-i.val-1)))) :
    (steps : Nat) → steps ≤ width → BF64.Packed.Buffer (2^width*lanes) → BF64.Packed.Buffer (2^width*lanes)
  | 0, _, a => a
  | steps+1, hsteps, a =>
    let i : Fin width := ⟨steps, by omega⟩
    selectedStage rows.stages[(⟨steps, by omega⟩ : Fin d)].2 width i lanes (window.val*2^(width-steps-1))
      (windowBlocks d width bound i window (blocks i))
      (windowRunCached rows width lanes bound window blocks steps (by omega) a)

/-- Cached block lists preserve every occupied window stage. -/
theorem windowRunCached_eq {d count : Nat} {hd : d < 64} (rows : CompactRows d hd)
    (width lanes : Nat) (bound : width ≤ d) (window : Fin (2^(d-width)))
    (positions : Vector (Fin (2^d)) count)
    (blocks : (i : Fin width) → List (Fin (2^(d-i.val-1))))
    (same : ∀ i, blocks i = occupiedBlocks ⟨i.val, by have := i.isLt; omega⟩ positions)
    (steps : Nat) (hsteps : steps ≤ width) (a : BF64.Packed.Buffer (2^width*lanes)) :
    windowRunCached rows width lanes bound window blocks steps hsteps a =
      windowSparseRun rows width lanes bound window positions steps hsteps a := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    change selectedStage rows.stages[(⟨steps, by omega⟩ : Fin d)].2 width ⟨steps, by omega⟩ lanes
      (window.val*2^(width-steps-1))
      (windowBlocks d width bound ⟨steps, by omega⟩ window (blocks ⟨steps, by omega⟩))
      (windowRunCached rows width lanes bound window blocks steps (by omega) a) =
      windowSparseStage rows width lanes bound ⟨steps, by omega⟩ window positions
        (windowSparseRun rows width lanes bound window positions steps (by omega) a)
    rw [ih]
    unfold windowSparseStage
    rw [same]

/-- Prepare each occupied block list once for all independent windows. -/
def occupiedWindowsCached {d count : Nat} {hd : d < 64} (rows : CompactRows d hd)
    (width lanes : Nat) (bound : width ≤ d) (positions : Vector (Fin (2^d)) count)
    (values : Fin count → Fin lanes → Word) : Vector (Option (BF64.Packed.Buffer (2^width*lanes))) (2^(d-width)) :=
  let blocks := Vector.ofFn fun i : Fin width =>
    (occupiedBlocks (⟨i.val, by have := i.isLt; omega⟩ : Fin d) positions).map Fin.val
  Vector.ofFn fun window =>
    if positions.any (fun p => decide (p.val/2^width = window.val)) then
      some (windowRunCached rows width lanes bound window
        (fun i => blocks[i].map fun b => (⟨b % 2^(d-i.val-1), Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : Fin (2^(d-i.val-1))))
        width (Nat.le_refl _) (windowScatter width lanes window positions values))
    else none

/-- Sharing occupied block preparation preserves the complete window store. -/
@[csimp] theorem occupiedWindows_code : @occupiedWindows = @occupiedWindowsCached := by
  funext d count hd rows width lanes bound positions values
  unfold occupiedWindows occupiedWindowsCached
  apply congrArg Vector.ofFn
  funext window
  split
  · congr 1
    symm
    apply windowRunCached_eq
    intro i
    simp only [Fin.getElem_fin,Vector.getElem_ofFn,List.map_map]
    apply List.map_id''
    intro b
    apply Fin.ext
    exact Nat.mod_eq_of_lt b.isLt
  · rfl

/-- Absent windows remain zero throughout the low occupied-stage prefix. -/
theorem occupiedWindow_zero {d count : Nat} {hd : d < 64} (plan : Packed.FlatPlan d hd)
    (width lanes : Nat) (bound : width ≤ d) (window : Fin (2^(d-width)))
    (positions : Vector (Fin (2^d)) count) (values : Fin count → Fin lanes → Word)
    (absent : positions.any (fun p => decide (p.val/2^width = window.val)) = false)
    (x : Fin (2^width*lanes)) :
    BF64.Packed.read (occupiedRun plan lanes positions width bound
      (scatterRows (2^d) lanes positions values)) (windowAddress d width lanes bound window x) = 0 := by
  have support := (occupiedRun_refines plan lanes positions width bound _
    (scatterRows_support lanes positions values)).1
  apply support
  intro q same
  have positive : 0 < 2^width*lanes := by have := x.isLt; omega
  have quotient : (windowAddress d width lanes bound window x).val/(2^width*lanes) = window.val := by
    change (window.val*(2^width*lanes)+x.val)/(2^width*lanes) = window.val
    rw [Nat.mul_comm window.val, Nat.mul_add_div positive, Nat.div_eq_of_lt x.isLt, Nat.add_zero]
  rw [quotient] at same
  have no := Vector.any_eq_false.mp absent q.val q.isLt
  apply no
  apply decide_eq_true
  exact same.symm

/-- Occupied window storage retains every low-stage coordinate without a full-domain stage buffer. -/
theorem read_occupiedWindows {d count : Nat} {hd : d < 64} (rows : CompactRows d hd)
    (plan : Packed.FlatPlan d hd) (width lanes : Nat) (bound : width ≤ d)
    (positions : Vector (Fin (2^d)) count) (values : Fin count → Fin lanes → Word)
    (window : Fin (2^(d-width))) (x : Fin (2^width*lanes)) :
    readWindow (occupiedWindows rows width lanes bound positions values) window x =
      BF64.Packed.read (transposeRows plan width bound lanes (scatterRows (2^d) lanes positions values))
        (windowAddress d width lanes bound window x) := by
  have dense := (occupiedRun_refines plan lanes positions width bound _
    (scatterRows_support lanes positions values)).2
  rw [← dense]
  unfold readWindow occupiedWindows
  rw [Fin.getElem_fin,Vector.getElem_ofFn]
  by_cases live : positions.any (fun p => decide (p.val/2^width = window.val)) = true
  · simp only [live,↓reduceIte]
    change BF64.Packed.read (windowSparseRun rows width lanes bound window positions width _
      (windowScatter width lanes window positions values)) x = _
    calc
      _ = BF64.Packed.read (windowSparseRun rows width lanes bound window positions width _
        (tileProject (windowAddress d width lanes bound window) (scatterRows (2^d) lanes positions values))) x := by
        apply windowSparseRun_congr
        intro y
        rw [tileProject,Packed.read_tabulate]
        exact windowScatter_read width lanes bound window positions values y
      _ = _ := windowSparseRun_read rows plan width lanes bound window positions width (Nat.le_refl _) _ x
  · simp only [live]
    exact (occupiedWindow_zero plan width lanes bound window positions values
      (Bool.eq_false_iff.mpr live) x).symm

/-- A contiguous column strip reads its input directly from occupied window storage. -/
def windowStripInput (base high lanes columns offset : Nat) (fits : offset+columns ≤ 2^base*lanes)
    (windows : Vector (Option (BF64.Packed.Buffer (2^base*lanes))) (2^((base+high)-base))) :
    BF64.Packed.Buffer (2^high*columns) :=
  Packed.tabulate _ fun x => readWindow windows
    (Fin.cast (by rw [Nat.add_sub_cancel_left]) x.divNat)
    ⟨offset+x.modNat.val, by have := x.modNat.isLt; omega⟩

/-- Strip gathering preserves the complete-domain low transpose prefix. -/
theorem windowStripInput_read (base high : Nat) (hd : base+high < 64) (rows : CompactRows (base+high) hd)
    (plan : Packed.FlatPlan (base+high) hd) (lanes columns offset : Nat)
    (fits : offset+columns ≤ 2^base*lanes) {count : Nat}
    (positions : Vector (Fin (2^(base+high))) count) (values : Fin count → Fin lanes → Word)
    (x : Fin (2^high*columns)) :
    BF64.Packed.read (windowStripInput base high lanes columns offset fits
      (occupiedWindows rows base lanes (by omega) positions values)) x =
      BF64.Packed.read (transposeRows plan base (by omega) lanes (scatterRows _ lanes positions values))
        (domainStripAddress base high lanes columns offset fits x) := by
  rw [windowStripInput,Packed.read_tabulate,read_occupiedWindows rows plan]
  congr 1
  apply Fin.ext
  simp only [windowAddress,domainStripAddress,stripAddress,Fin.val_cast]
  omega

/-- The number of columns in all strips equals one complete low window. -/
theorem stripColumnCount (base stripe lanes : Nat) (bound : stripe ≤ base) :
    2^(base-stripe)*(2^stripe*lanes) = 2^base*lanes := by
  rw [← Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel bound]

/-- Row, strip and column coordinates describe the ordinary row-major kept output. -/
@[inline] def stripLayout (base keep stripe lanes : Nat) (bound : stripe ≤ base) :
    Fin (2^keep) × (Fin (2^(base-stripe)) × Fin (2^stripe*lanes)) ≃ Fin (2^(base+keep)*lanes) :=
  (Equiv.prodCongr (Equiv.refl _) (finProdFinEquiv.trans (finCongr (stripColumnCount base stripe lanes bound)))).trans
    (finProdFinEquiv.trans (finCongr (stripWordCount base keep lanes)))

/-- The strip-layout address has its explicit row-major arithmetic form. -/
theorem stripLayout_val (base keep stripe lanes : Nat) (bound : stripe ≤ base)
    (row : Fin (2^keep)) (strip : Fin (2^(base-stripe))) (column : Fin (2^stripe*lanes)) :
    (stripLayout base keep stripe lanes bound (row,(strip,column))).val =
      row.val*(2^base*lanes)+strip.val*(2^stripe*lanes)+column.val := by
  dsimp only [stripLayout,Equiv.prodCongr,Equiv.trans,Equiv.refl,Equiv.coe_fn_mk,Prod.map,
    finCongr,Fin.cast,finProdFinEquiv]
  simp only [Function.comp_apply,Prod.map,Function.id_def,Fin.val_cast]
  ring

/-- Reassemble collapsed column strips in the kept row-major output order. -/
def materializeStrips (base keep stripe lanes : Nat) (bound : stripe ≤ base)
    (strips : Vector (BF64.Packed.Buffer (2^keep*(2^stripe*lanes))) (2^(base-stripe))) :
    BF64.Packed.Buffer (2^(base+keep)*lanes) :=
  Packed.tabulate _ fun x =>
    let parts := (stripLayout base keep stripe lanes bound).symm x
    BF64.Packed.read strips[parts.2.1] (finProdFinEquiv (parts.1,parts.2.2))

/-- Reassemble collapsed strips using only integer quotients and remainders. -/
def materializeStripsDirect (base keep stripe lanes : Nat) (bound : stripe ≤ base)
    (strips : Vector (BF64.Packed.Buffer (2^keep*(2^stripe*lanes))) (2^(base-stripe))) :
    BF64.Packed.Buffer (2^(base+keep)*lanes) :=
  let full := 2^base*lanes
  let width := 2^stripe*lanes
  Packed.tabulate _ fun x =>
    have positive : 0 < full ∧ 0 < width := by
      have := x.isLt
      have := Nat.two_pow_pos base
      have := Nat.two_pow_pos stripe
      have := Nat.two_pow_pos (base+keep)
      dsimp only [full,width]
      constructor <;> nlinarith
    let row : Fin (2^keep) := ⟨x.val/full,by
      apply (Nat.div_lt_iff_lt_mul positive.1).mpr
      have shape := stripWordCount base keep lanes
      dsimp only [full]
      rw [shape]
      exact x.isLt⟩
    let strip : Fin (2^(base-stripe)) := ⟨(x.val%full)/width,by
      apply (Nat.div_lt_iff_lt_mul positive.2).mpr
      have shape := stripColumnCount base stripe lanes bound
      dsimp only [width]
      rw [shape]
      exact Nat.mod_lt _ positive.1⟩
    BF64.Packed.read strips[strip] ⟨row.val*width+x.val%width,by
      change row.val*width+x.val%width < 2^keep*width
      have := row.isLt
      have := Nat.mod_lt x.val positive.2
      nlinarith⟩

/-- Integer addressing retains every row, strip and column of the layout equivalence. -/
@[csimp] theorem materializeStrips_code : @materializeStrips = @materializeStripsDirect := by
  funext base keep stripe lanes bound strips
  unfold materializeStrips materializeStripsDirect
  dsimp only
  apply congrArg (Packed.tabulate (2^(base+keep)*lanes))
  funext x
  obtain ⟨⟨row,strip,column⟩,rfl⟩ := (stripLayout base keep stripe lanes bound).surjective x
  simp only [(stripLayout base keep stripe lanes bound).symm_apply_apply]
  have positive : 0 < 2^stripe*lanes := by have := column.isLt; omega
  have fullPositive : 0 < 2^base*lanes := by
    rw [← stripColumnCount base stripe lanes bound]
    exact Nat.mul_pos (Nat.two_pow_pos _) positive
  have inside : strip.val*(2^stripe*lanes)+column.val < 2^base*lanes := by
    rw [← stripColumnCount base stripe lanes bound]
    have := strip.isLt
    have := column.isLt
    nlinarith
  simp only [stripLayout_val]
  have rowDiv : (row.val*(2^base*lanes)+strip.val*(2^stripe*lanes)+column.val)/(2^base*lanes) = row.val := by
    rw [Nat.add_assoc,Nat.mul_comm row.val,Nat.mul_add_div fullPositive,Nat.div_eq_of_lt inside,Nat.add_zero]
  have rowMod : (row.val*(2^base*lanes)+strip.val*(2^stripe*lanes)+column.val)%(2^base*lanes) =
      strip.val*(2^stripe*lanes)+column.val := by
    rw [Nat.add_assoc,Nat.mul_comm row.val,Nat.mul_add_mod,Nat.mod_eq_of_lt inside]
  have stripDiv : (strip.val*(2^stripe*lanes)+column.val)/(2^stripe*lanes) = strip.val := by
    rw [Nat.mul_comm strip.val,Nat.mul_add_div positive,Nat.div_eq_of_lt column.isLt,Nat.add_zero]
  have columnMod : (row.val*(2^base*lanes)+strip.val*(2^stripe*lanes)+column.val)%(2^stripe*lanes) = column.val := by
    have divides : 2^base*lanes = 2^(base-stripe)*(2^stripe*lanes) := (stripColumnCount base stripe lanes bound).symm
    rw [divides]
    have same : row.val*(2^(base-stripe)*(2^stripe*lanes))+strip.val*(2^stripe*lanes)+column.val =
      (2^stripe*lanes)*(row.val*2^(base-stripe)+strip.val)+column.val := by ring
    rw [same,Nat.mul_add_mod,Nat.mod_eq_of_lt column.isLt]
  simp only [rowDiv,rowMod,stripDiv,columnMod]
  congr 1
  apply Fin.ext
  simp only [finProdFinEquiv,Equiv.coe_fn_mk]
  ac_rfl

/-- Equal local strip inputs remain equal through a complete high-stage prefix. -/
theorem stripRun_congr (base high : Nat) (hd : base+high < 64) (rows : CompactRows (base+high) hd)
    (plan : Packed.FlatPlan (base+high) hd) (lanes columns offset : Nat)
    (fits : offset+columns ≤ 2^base*lanes) (steps : Nat) (bound : steps ≤ high)
    (a b : BF64.Packed.Buffer (2^high*columns))
    (same : ∀ x, BF64.Packed.read a x = BF64.Packed.read b x) (x : Fin (2^high*columns)) :
    BF64.Packed.read (stripRun base high hd rows columns steps bound a) x =
      BF64.Packed.read (stripRun base high hd rows columns steps bound b) x := by
  induction steps generalizing x with
  | zero => exact same x
  | succ steps ih =>
    apply stripStage_congr base high hd rows plan lanes columns offset fits
    exact ih (by omega)

/-- Transpose and collapse a single strip directly from occupied window storage. -/
def windowStripResult (base keep rate : Nat) (hd : base+(keep+rate) < 64)
    (rows : CompactRows (base+(keep+rate)) hd) (lanes columns offset : Nat)
    (fits : offset+columns ≤ 2^base*lanes)
    (windows : Vector (Option (BF64.Packed.Buffer (2^base*lanes))) (2^((base+(keep+rate))-base))) :
    BF64.Packed.Buffer (2^keep*columns) :=
  collapseRows keep rate columns (stripRun base (keep+rate) hd rows columns keep (by omega)
    (windowStripInput base (keep+rate) lanes columns offset fits windows))

/-- A collapsed strip is the sum of the same complete-domain transpose coordinates. -/
theorem windowStripResult_read (base keep rate : Nat) (hd : base+(keep+rate) < 64)
    (rows : CompactRows (base+(keep+rate)) hd) (plan : Packed.FlatPlan (base+(keep+rate)) hd)
    (lanes columns offset : Nat) (fits : offset+columns ≤ 2^base*lanes) {count : Nat}
    (positions : Vector (Fin (2^(base+(keep+rate)))) count) (values : Fin count → Fin lanes → Word)
    (x : Fin (2^keep*columns)) :
    (BF64.Packed.read (windowStripResult base keep rate hd rows lanes columns offset fits
      (occupiedWindows rows base lanes (by omega) positions values)) x).toField =
      ∑ replica : Fin (2^rate), (BF64.Packed.read
        (transposeRows plan (base+keep) (by omega) lanes (scatterRows _ lanes positions values))
        (domainStripAddress base (keep+rate) lanes columns offset fits
          ⟨replica.val*(2^keep*columns)+x.val, by
            have := replica.isLt
            have := x.isLt
            rw [pow_add]
            nlinarith⟩)).toField := by
  rw [windowStripResult,read_collapseRows]
  apply Finset.sum_congr rfl
  intro replica _
  congr 1
  calc
    _ = BF64.Packed.read (stripRun base (keep+rate) hd rows columns keep (by omega)
      (tileProject (domainStripAddress base (keep+rate) lanes columns offset fits)
        (transposeRows plan base (by omega) lanes (scatterRows _ lanes positions values)))) _ := by
      apply stripRun_congr base (keep+rate) hd rows plan lanes columns offset fits
      intro y
      rw [tileProject,Packed.read_tabulate]
      exact windowStripInput_read base (keep+rate) hd rows plan lanes columns offset fits positions values y
    _ = _ := stripRun_read base (keep+rate) hd rows plan lanes columns offset fits keep (by omega) _ _

/-- Independent occupied windows and collapsed strips materialize only the kept output. -/
def tiledInduceCore (base keep rate stripe : Nat) (stripeBound : stripe ≤ base)
    (hd : base+(keep+rate) < 64) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2^(base+(keep+rate)))) count) (values : Fin count → Fin lanes → Word) :
    BF64.Packed.Buffer (2^(base+keep)*lanes) :=
  let rows := CompactRows.create (base+(keep+rate)) hd
  let windows := occupiedWindows rows base lanes (by omega) positions values
  let strips := Vector.ofFn fun strip : Fin (2^(base-stripe)) =>
    windowStripResult base keep rate hd rows lanes (2^stripe*lanes) (strip.val*(2^stripe*lanes)) (by
      rw [← stripColumnCount base stripe lanes stripeBound]
      have bound := Nat.mul_le_mul_right (2^stripe*lanes) (show strip.val+1 ≤ 2^(base-stripe) by have := strip.isLt; omega)
      nlinarith) windows
  materializeStrips base keep stripe lanes stripeBound strips

/-- High-stage multipliers shared by all column strips. -/
def stripMultipliers (base high : Nat) (hd : base+high < 64) (rows : CompactRows (base+high) hd)
    (i : Fin high) : Vector Packed.Multiplier (2^(high-i.val-1)) :=
  Vector.ofFn fun b => rowMultiplier rows.stages[(⟨base+i.val, by have := i.isLt; omega⟩ : Fin (base+high))].2 b.val

/-- Run a column strip using a shared high-stage multiplier family. -/
def stripRunPrepared (high columns : Nat)
    (multipliers : (i : Fin high) → Vector Packed.Multiplier (2^(high-i.val-1))) :
    (steps : Nat) → steps ≤ high → BF64.Packed.Buffer (2^high*columns) → BF64.Packed.Buffer (2^high*columns)
  | 0, _, a => a
  | steps+1, bound, a =>
    occupiedSweepBlocks (Vector.ofFn fun b : Fin (2^(high-steps-1)) => b)
      (2^steps*columns) (Packed.stage_word_count high ⟨steps, by omega⟩ columns)
      (multipliers ⟨steps, by omega⟩)
      (stripRunPrepared high columns multipliers steps (by omega) a)

/-- Sharing each high-stage multiplier across strips preserves the stage sequence. -/
theorem stripRunPrepared_eq (base high : Nat) (hd : base+high < 64) (rows : CompactRows (base+high) hd)
    (columns : Nat) (multipliers : (i : Fin high) → Vector Packed.Multiplier (2^(high-i.val-1)))
    (same : ∀ i, multipliers i = stripMultipliers base high hd rows i)
    (steps : Nat) (bound : steps ≤ high) (a : BF64.Packed.Buffer (2^high*columns)) :
    stripRunPrepared high columns multipliers steps bound a = stripRun base high hd rows columns steps bound a := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    change occupiedSweepBlocks (Vector.ofFn fun b : Fin (2^(high-steps-1)) => b)
      (2^steps*columns) (Packed.stage_word_count high ⟨steps, by omega⟩ columns) (multipliers ⟨steps, by omega⟩)
      (stripRunPrepared high columns multipliers steps (by omega) a) =
      stripStage base high hd rows columns ⟨steps, by omega⟩
        (stripRun base high hd rows columns steps (by omega) a)
    rw [ih,same]
    unfold stripStage stripMultipliers rowMultiplier
    rw [occupiedSweepRows_eq]
    simp only [Fin.getElem_fin,Vector.getElem_ofFn,Nat.zero_add]

/-- Window and strip induction with high-stage multiplier preparation shared across strips. -/
def tiledInducePrepared (base keep rate stripe : Nat) (stripeBound : stripe ≤ base)
    (hd : base+(keep+rate) < 64) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2^(base+(keep+rate)))) count) (values : Fin count → Fin lanes → Word) :
    BF64.Packed.Buffer (2^(base+keep)*lanes) :=
  let rows := CompactRows.create (base+(keep+rate)) hd
  let windows := occupiedWindows rows base lanes (by omega) positions values
  let multipliers := Vector.ofFn fun i : Fin (keep+rate) =>
    (stripMultipliers base (keep+rate) hd rows i).toArray
  let get := fun i : Fin (keep+rate) =>
    (⟨multipliers[i],by simp only [multipliers,Fin.getElem_fin,Vector.getElem_ofFn,Vector.size_toArray]⟩ :
      Vector Packed.Multiplier (2^(keep+rate-i.val-1)))
  let strips := Vector.ofFn fun strip : Fin (2^(base-stripe)) =>
    let fits : strip.val*(2^stripe*lanes)+(2^stripe*lanes) ≤ 2^base*lanes := by
      rw [← stripColumnCount base stripe lanes stripeBound]
      have bound := Nat.mul_le_mul_right (2^stripe*lanes) (show strip.val+1 ≤ 2^(base-stripe) by have := strip.isLt; omega)
      nlinarith
    collapseRows keep rate (2^stripe*lanes)
      (stripRunPrepared (keep+rate) (2^stripe*lanes) get keep (by omega)
        (windowStripInput base (keep+rate) lanes (2^stripe*lanes) (strip.val*(2^stripe*lanes)) fits windows))
  materializeStrips base keep stripe lanes stripeBound strips

/-- Sharing high-stage preparation retains the complete tiled induction buffer. -/
@[csimp] theorem tiledInduceCore_code : @tiledInduceCore = @tiledInducePrepared := by
  funext base keep rate stripe stripeBound hd lanes count positions values
  let rows := CompactRows.create (base+(keep+rate)) hd
  let multipliers := Vector.ofFn fun i : Fin (keep+rate) =>
    (stripMultipliers base (keep+rate) hd rows i).toArray
  let get := fun i : Fin (keep+rate) =>
    (⟨multipliers[i],by simp only [multipliers,Fin.getElem_fin,Vector.getElem_ofFn,Vector.size_toArray]⟩ :
      Vector Packed.Multiplier (2^(keep+rate-i.val-1)))
  have same (i : Fin (keep+rate)) : get i = stripMultipliers base (keep+rate) hd rows i := by
    apply Vector.toArray_inj.mp
    simp only [get,multipliers,Fin.getElem_fin,Vector.getElem_ofFn]
  have run (a : BF64.Packed.Buffer (2^(keep+rate)*(2^stripe*lanes))) :
      stripRunPrepared (keep+rate) (2^stripe*lanes) get keep (by omega) a =
        stripRun base (keep+rate) hd rows (2^stripe*lanes) keep (by omega) a :=
    stripRunPrepared_eq base (keep+rate) hd rows (2^stripe*lanes) get same keep (by omega) a
  dsimp only [get,multipliers,rows] at run
  unfold tiledInduceCore tiledInducePrepared
  simp only [run,windowStripResult]

/-- Address a kept-output coordinate in one original evaluation replica. -/
@[inline] def domainReplicaIndex (base keep rate lanes : Nat) (x : Fin (2^(base+keep)*lanes))
    (replica : Fin (2^rate)) : Fin (2^(base+(keep+rate))*lanes) :=
  ⟨replica.val*(2^(base+keep)*lanes)+x.val, by
    have shape : 2^(base+(keep+rate))*lanes = 2^rate*(2^(base+keep)*lanes) := by
      simp only [pow_add]
      ac_rfl
    rw [shape]
    have := replica.isLt
    have := x.isLt
    nlinarith⟩

/-- The high-row address of one kept row in a selected evaluation replica. -/
@[inline] def replicaRow (keep rate : Nat) (replica : Fin (2^rate)) (row : Fin (2^keep)) : Fin (2^(keep+rate)) :=
  ⟨replica.val*2^keep+row.val, by
    have := replica.isLt
    have := row.isLt
    rw [pow_add]
    nlinarith⟩

/-- Replica collapse in a strip selects exactly the original row-major replica coordinate. -/
theorem domainStrip_replica (base keep rate stripe lanes : Nat) (stripeBound : stripe ≤ base)
    (row : Fin (2^keep)) (strip : Fin (2^(base-stripe))) (column : Fin (2^stripe*lanes))
    (fits : strip.val*(2^stripe*lanes)+(2^stripe*lanes) ≤ 2^base*lanes) (replica : Fin (2^rate)) :
    domainStripAddress base (keep+rate) lanes (2^stripe*lanes) (strip.val*(2^stripe*lanes)) fits
      ⟨replica.val*(2^keep*(2^stripe*lanes))+(finProdFinEquiv (row,column)).val, by
        have := replica.isLt
        have := (finProdFinEquiv (row,column)).isLt
        rw [pow_add]
        nlinarith⟩ =
      domainReplicaIndex base keep rate lanes (stripLayout base keep stripe lanes stripeBound (row,(strip,column))) replica := by
  have localIndex : (⟨replica.val*(2^keep*(2^stripe*lanes))+(finProdFinEquiv (row,column)).val, by
      have := replica.isLt
      have := (finProdFinEquiv (row,column)).isLt
      rw [pow_add]
      nlinarith⟩ : Fin (2^(keep+rate)*(2^stripe*lanes))) =
      finProdFinEquiv (replicaRow keep rate replica row,column) := by
    apply Fin.ext
    simp only [finProdFinEquiv,Equiv.coe_fn_mk,replicaRow]
    ring
  rw [localIndex]
  unfold domainStripAddress
  rw [stripAddress_mk]
  apply Fin.ext
  simp only [Fin.val_cast,domainReplicaIndex,finProdFinEquiv,Equiv.coe_fn_mk,replicaRow,
    stripLayout_val,pow_add]
  ring

/-- Every tiled induced coordinate is the certified sum of complete-transpose replicas. -/
theorem tiledInduceCore_coordinate (base keep rate stripe : Nat) (stripeBound : stripe ≤ base)
    (hd : base+(keep+rate) < 64) (plan : Packed.FlatPlan (base+(keep+rate)) hd) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2^(base+(keep+rate)))) count) (values : Fin count → Fin lanes → Word)
    (row : Fin (2^keep)) (strip : Fin (2^(base-stripe))) (column : Fin (2^stripe*lanes)) :
    (BF64.Packed.read (tiledInduceCore base keep rate stripe stripeBound hd lanes positions values)
      (stripLayout base keep stripe lanes stripeBound (row,(strip,column)))).toField =
      ∑ replica : Fin (2^rate), (BF64.Packed.read
        (transposeRows plan (base+keep) (by omega) lanes (scatterRows _ lanes positions values))
        (domainReplicaIndex base keep rate lanes
          (stripLayout base keep stripe lanes stripeBound (row,(strip,column))) replica)).toField := by
  unfold tiledInduceCore materializeStrips
  dsimp only
  simp only [Packed.read_tabulate,Equiv.symm_apply_apply,Fin.getElem_fin,Vector.getElem_ofFn]
  rw [windowStripResult_read base keep rate hd _ plan]
  apply Finset.sum_congr rfl
  intro replica _
  congr 2
  exact domainStrip_replica base keep rate stripe lanes stripeBound row strip column _ replica

/-- View a certified flat plan at an equal domain dimension. -/
def flatPlanCast {d e : Nat} {hd : d < 64} (same : d = e) (plan : Packed.FlatPlan d hd) :
    Packed.FlatPlan e (same ▸ hd) := same ▸ plan

/-- Equal domain dimensions preserve the complete scattered transpose and its coordinates. -/
theorem transposeScatter_cast {d e : Nat} {hd : d < 64} (same : d = e)
    (plan : Packed.FlatPlan d hd) (steps : Nat) (bound : steps ≤ d) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2^d)) count) (values : Fin count → Fin lanes → Word)
    (x : Fin (2^d*lanes)) :
    BF64.Packed.read (transposeRows (flatPlanCast same plan) steps (by omega) lanes
      (scatterRows _ lanes (positions.map (Fin.cast (congrArg (fun k => 2^k) same))) values))
      (Fin.cast (congrArg (fun k => 2^k*lanes) same) x) =
      BF64.Packed.read (transposeRows plan steps bound lanes (scatterRows _ lanes positions values)) x := by
  cases same
  simp only [flatPlanCast,Fin.cast_refl,Vector.map_id',Function.id_def]

/-- The window-and-strip core preserves the exact public induction coordinates. -/
theorem tiledInduceCore_refines (base keep rate stripe : Nat) (stripeBound : stripe ≤ base)
    (hd : (base+keep)+rate < 64) (plan : Packed.FlatPlan ((base+keep)+rate) hd)
    (lanes : Nat) {count : Nat} (positions : Vector (Fin (2^((base+keep)+rate))) count)
    (values : Fin count → Fin lanes → Word) (index : Fin (2^(base+keep)*lanes)) :
    BF64.Packed.read (tiledInduceCore base keep rate stripe stripeBound (by omega) lanes
      (positions.map (Fin.cast (congrArg (fun k => 2^k) (Nat.add_assoc base keep rate)))) values) index =
      BF64.Packed.read (induceRows hd plan lanes positions values) index := by
  apply Word.toField_injective
  obtain ⟨⟨row,strip,column⟩,rfl⟩ := (stripLayout base keep stripe lanes stripeBound).surjective index
  rw [tiledInduceCore_coordinate base keep rate stripe stripeBound _
    (flatPlanCast (Nat.add_assoc base keep rate) plan)]
  rw [induceRows,read_collapseRows]
  apply Finset.sum_congr rfl
  intro replica _
  congr 1
  have address : domainReplicaIndex base keep rate lanes
      (stripLayout base keep stripe lanes stripeBound (row,(strip,column))) replica =
      Fin.cast (congrArg (fun k => 2^k*lanes) (Nat.add_assoc base keep rate))
        (⟨replica.val*(2^(base+keep)*lanes)+(stripLayout base keep stripe lanes stripeBound (row,(strip,column))).val, by
          have := replica.isLt
          have := (stripLayout base keep stripe lanes stripeBound (row,(strip,column))).isLt
          rw [pow_add 2 (base+keep) rate]
          nlinarith⟩ : Fin (2^((base+keep)+rate)*lanes)) := by
    apply Fin.ext
    rfl
  rw [address]
  exact transposeScatter_cast (Nat.add_assoc base keep rate) plan (base+keep) (by omega) lanes positions values _

/-- Induction coordinates are unchanged when the kept dimension is reindexed by equality. -/
theorem induceRows_reindex {ell other rate : Nat} {hd : ell+rate < 64} (same : ell = other)
    (plan : Packed.FlatPlan (ell+rate) hd) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2^(ell+rate))) count) (values : Fin count → Fin lanes → Word)
    (index : Fin (2^ell*lanes)) :
    BF64.Packed.read (induceRows (by omega) (flatPlanCast (congrArg (fun k => k+rate) same) plan)
      lanes (positions.map (Fin.cast (congrArg (fun k => 2^(k+rate)) same))) values)
      (Fin.cast (congrArg (fun k => 2^k*lanes) same) index) =
      BF64.Packed.read (induceRows hd plan lanes positions values) index := by
  cases same
  simp only [flatPlanCast,Fin.cast_refl,Vector.map_id',Function.id_def]

/-- Sparse induction with 1024-element windows and 16-column strips. -/
def induceWindowStripRows {ell rate : Nat} (hd : ell+rate < 64) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2^(ell+rate))) count) (values : Fin count → Fin lanes → Word) :
    BF64.Packed.Buffer (2^ell*lanes) :=
  let base := min 10 ell
  let keep := ell-base
  let same : base+keep = ell := by dsimp only [keep]; exact Nat.add_sub_of_le (Nat.min_le_right _ _)
  let positions' := positions.map (Fin.cast (congrArg (fun k => 2^(k+rate)) same.symm))
  let result := tiledInduceCore base keep rate (min 4 base) (Nat.min_le_right _ _) (by omega) lanes
    (positions'.map (Fin.cast (congrArg (fun k => 2^k) (Nat.add_assoc base keep rate)))) values
  ⟨result.val,result.property.trans (congrArg (fun k => 2^k*lanes) same)⟩

/-- Window and strip storage retains every coordinate of the certified encoder transpose. -/
theorem induceWindowStripRows_refines {ell rate : Nat} (hd : ell+rate < 64)
    (plan : Packed.FlatPlan (ell+rate) hd) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2^(ell+rate))) count) (values : Fin count → Fin lanes → Word)
    (index : Fin (2^ell*lanes)) :
    BF64.Packed.read (induceWindowStripRows hd lanes positions values) index =
      BF64.Packed.read (induceRows hd plan lanes positions values) index := by
  let base := min 10 ell
  let keep := ell-base
  have same : base+keep = ell := Nat.add_sub_of_le (Nat.min_le_right _ _)
  let positions' := positions.map (Fin.cast (congrArg (fun k => 2^(k+rate)) same.symm))
  let index' := Fin.cast (congrArg (fun k => 2^k*lanes) same.symm) index
  let plan' := flatPlanCast (congrArg (fun k => k+rate) same.symm) plan
  have core := tiledInduceCore_refines base keep rate (min 4 base) (Nat.min_le_right _ _)
    (by omega) plan' lanes positions' values index'
  have original := induceRows_reindex same.symm plan lanes positions values index
  calc
    _ = BF64.Packed.read (tiledInduceCore base keep rate (min 4 base) (Nat.min_le_right _ _)
      (by omega) lanes (positions'.map (Fin.cast (congrArg (fun k => 2^k) (Nat.add_assoc base keep rate)))) values) index' := by
      unfold induceWindowStripRows BF64.Packed.read
      rfl
    _ = _ := core.trans original

end

end CompStark.Pcs
