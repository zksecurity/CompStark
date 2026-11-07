/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.Encoding

/-! Transposed additive butterflies and query-weight induction. -/
set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStark.Pcs
open BF64 AdditiveNTT

/-- The transpose of a normalized additive butterfly. -/
@[inline] def transposePair (m : Packed.Multiplier) (u v : Word) : Word × Word :=
  let total := Word.add u v
  (total, Word.add v (m.apply total))

/-- A zero input pair has no contribution to the transposed transform. -/
@[inline] def sparseTransposePair (m : Packed.Multiplier) (u v : Word) : Word × Word :=
  if u.val == 0 && v.val == 0 then (u, v) else transposePair m u v

/-- Reverse the encoder's stage order while retaining every shared twiddle. -/
def transposeRows {d : Nat} {hd : d < 64} (plan : Packed.FlatPlan d hd)
    (ell : Nat) (hell : ell ≤ d) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) : BF64.Packed.Buffer (2 ^ d * lanes) :=
  Fin.foldl ell (fun a i => Packed.stageSweep plan ⟨i.val, by omega⟩ lanes sparseTransposePair a) a

/-- Scatter ordered query weights, summing repeated column positions. -/
def scatterRows (rows lanes : Nat) {count : Nat} (positions : Vector (Fin rows) count)
    (values : Fin count → Fin lanes → Word) : BF64.Packed.Buffer (rows * lanes) :=
  Fin.foldl count (fun a q => Fin.foldl lanes (fun a lane =>
    let index : Fin (rows * lanes) := ⟨positions[q].val * lanes + lane.val, by
      have := positions[q].isLt; have := lane.isLt; nlinarith⟩
    BF64.Packed.write a index (Word.add (BF64.Packed.read a index) (values q lane))) a)
      ⟨BF64.Packed.zeros _, rfl⟩

/-- Sum the evaluation replicas, the adjoint of the encoder's free coefficient tiling. -/
def collapseRows (ell rate lanes : Nat) (a : BF64.Packed.Buffer (2 ^ (ell + rate) * lanes)) :
    BF64.Packed.Buffer (2 ^ ell * lanes) :=
  Packed.tabulate _ fun i =>
    Fin.foldl (2 ^ rate) (fun acc replica => Word.add acc
      (BF64.Packed.read a ⟨replica.val * (2 ^ ell * lanes) + i.val, by
        have hr := replica.isLt; have hi := i.isLt
        rw [pow_add]; nlinarith⟩)) ⟨0⟩

/-- Induce message weights from sparse ordered query contributions through the encoder transpose. -/
def induceRows {ell rate : Nat} (hd : ell + rate < 64)
    (plan : Packed.FlatPlan (ell + rate) hd) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2 ^ (ell + rate))) count)
    (values : Fin count → Fin lanes → Word) : BF64.Packed.Buffer (2 ^ ell * lanes) :=
  collapseRows ell rate lanes (transposeRows plan ell (by omega) lanes
    (scatterRows _ lanes positions values))

/-- The sparse branch is exactly the same linear butterfly, including zero twiddles. -/
theorem sparseTransposePair_eq (m : Packed.Multiplier) (u v : Word) :
    sparseTransposePair m u v = transposePair m u v := by
  unfold sparseTransposePair
  split
  · rename_i h
    have hh := Bool.and_eq_true_iff.mp h
    have hu : u = ⟨0⟩ := by cases u; simp only [beq_iff_eq] at hh; simp only [hh.1]
    have hv : v = ⟨0⟩ := by cases v; simp only [beq_iff_eq] at hh; simp only [hh.2]
    subst u; subst v
    have hm : m.apply ⟨0⟩ = ⟨0⟩ := by
      apply Word.toField_injective
      rw [m.correct]
      change m.scalar.toField * 0 = 0
      exact mul_zero _
    change (Word.mk 0, Word.mk 0) = (Word.mk 0, Word.add (Word.mk 0) (m.apply (Word.mk 0)))
    rw [hm]
    rfl
  · rfl

/-- Apply every transpose butterfly to a dense query table without testing for zero pairs. -/
def denseTransposeRows {d : Nat} {hd : d < 64} (plan : Packed.FlatPlan d hd)
    (ell : Nat) (hell : ell ≤ d) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) : BF64.Packed.Buffer (2 ^ d * lanes) :=
  Fin.foldl ell (fun a i => Packed.stageSweep plan ⟨i.val, by omega⟩ lanes transposePair a) a

/-- Dense and sparse sweeps represent the same transposed linear map. -/
theorem denseTransposeRows_eq {d : Nat} {hd : d < 64} (plan : Packed.FlatPlan d hd)
    (ell : Nat) (hell : ell ≤ d) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) :
    denseTransposeRows plan ell hell lanes a = transposeRows plan ell hell lanes a := by
  have pair : sparseTransposePair = transposePair := by
    funext m u v
    exact sparseTransposePair_eq m u v
  simp only [denseTransposeRows, transposeRows, pair]

/-- Dense induction executes the complete transposed transform with shared twiddles. -/
def induceDenseRows {ell rate : Nat} (hd : ell + rate < 64)
    (plan : Packed.FlatPlan (ell + rate) hd) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2 ^ (ell + rate))) count)
    (values : Fin count → Fin lanes → Word) : BF64.Packed.Buffer (2 ^ ell * lanes) :=
  collapseRows ell rate lanes (denseTransposeRows plan ell (by omega) lanes
    (scatterRows _ lanes positions values))

/-- Dense induction equals the sparse induction on every ordered query list. -/
theorem induceDenseRows_eq {ell rate : Nat} (hd : ell + rate < 64)
    (plan : Packed.FlatPlan (ell + rate) hd) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2 ^ (ell + rate))) count)
    (values : Fin count → Fin lanes → Word) :
    induceDenseRows hd plan lanes positions values = induceRows hd plan lanes positions values := by
  simp only [induceDenseRows, induceRows, denseTransposeRows_eq]

/-- The transpose butterfly preserves the bilinear pairing with the forward butterfly. -/
theorem transposePair_adjoint (m : Packed.Multiplier) (u v a b : Word) :
    (Packed.forwardPair m u v).1.toField * a.toField +
      (Packed.forwardPair m u v).2.toField * b.toField =
    u.toField * (transposePair m a b).1.toField +
      v.toField * (transposePair m a b).2.toField := by
  simp only [Packed.forwardPair, transposePair, Word.toField_add, m.correct]
  ring

/-- The field-valued bilinear pairing of two complete packed buffers. -/
def packedPairing {n : Nat} (a b : BF64.Packed.Buffer n) : BF64 :=
  ∑ i, (BF64.Packed.read a i).toField * (BF64.Packed.read b i).toField

/-- Disjoint packed transpose sweeps are adjoint to complete forward sweeps. -/
theorem sweep_adjoint {n k : Nat} (index : Fin k × Fin 2 ≃ Fin n)
    (multipliers : Fin k → Packed.Multiplier) (a b : BF64.Packed.Buffer n) :
    packedPairing (Packed.sweep index (fun j => Packed.forwardPair (multipliers j)) a) b =
      packedPairing a (Packed.sweep index (fun j => sparseTransposePair (multipliers j)) b) := by
  simp only [packedPairing, ← index.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.sum_univ_two, Packed.read_sweep index index.injective, ↓reduceIte,
    sparseTransposePair_eq]
  exact transposePair_adjoint (multipliers j) _ _ _ _

/-- Each arithmetic-indexed native transpose stage is adjoint to its encoder stage. -/
theorem transposeStage_adjoint {d : Nat} {hd : d < 64} (plan : Packed.FlatPlan d hd)
    (i : Fin d) (lanes : Nat) (a b : BF64.Packed.Buffer (2 ^ d * lanes)) :
    packedPairing (Packed.forwardStage plan i lanes a) b =
      packedPairing a (Packed.stageSweep plan i lanes sparseTransposePair b) := by
  rw [Packed.forwardStage_eq_sweep, Packed.stageSweep_eq_sweep]
  exact sweep_adjoint (Packed.stageIndex d i lanes) (fun j => plan.get i j.divNat) a b

/-- Transposition reverses the order of a complete stage composition. -/
theorem stages_adjoint {d : Nat} {hd : d < 64} (plan : Packed.FlatPlan d hd)
    (lanes : Nat) (stages : List (Fin d)) (a b : BF64.Packed.Buffer (2 ^ d * lanes)) :
    packedPairing (stages.foldl (fun a i => Packed.forwardStage plan i lanes a) a) b =
      packedPairing a (stages.foldr (fun i b => Packed.stageSweep plan i lanes sparseTransposePair b) b) := by
  induction stages generalizing a with
  | nil => rfl
  | cons i stages ih =>
    rw [List.foldl_cons, List.foldr_cons, ih, transposeStage_adjoint]

/-- Ascending transpose stages are adjoint to descending forward stages. -/
theorem finStages_adjoint {d : Nat} {hd : d < 64} (plan : Packed.FlatPlan d hd)
    (lanes count : Nat) (stages : Fin count → Fin d)
    (a b : BF64.Packed.Buffer (2 ^ d * lanes)) :
    packedPairing (Fin.foldr count (fun i a => Packed.forwardStage plan (stages i) lanes a) a) b =
      packedPairing a (Fin.foldl count (fun b i => Packed.stageSweep plan (stages i) lanes sparseTransposePair b) b) := by
  induction count generalizing a b with
  | zero => rfl
  | succ count ih =>
    rw [Fin.foldr_succ, transposeStage_adjoint, Fin.foldl_succ, ih]

/-- The complete native reverse-stage transform is the adjoint of the exact packed encoder. -/
theorem transposeRows_adjoint {d : Nat} {hd : d < 64} (plan : Packed.FlatPlan d hd)
    (ell : Nat) (hell : ell ≤ d) (lanes : Nat)
    (a b : BF64.Packed.Buffer (2 ^ d * lanes)) :
    packedPairing (Packed.forward plan ell hell lanes a) b =
      packedPairing a (transposeRows plan ell hell lanes b) := by
  have order (i : Fin ell) : (⟨ell - i.val - 1, by omega⟩ : Fin d) = i.rev.castLE hell := by
    apply Fin.ext
    simp only [Fin.val_castLE, Fin.val_rev]
    omega
  simp only [Packed.forward, order]
  rw [Fin.foldl_rev (fun i a => Packed.forwardStage plan (i.castLE hell) lanes a) a]
  exact finStages_adjoint plan lanes ell (fun i => i.castLE hell) a b

/-- A packed zero buffer reads as zero at every bounded address. -/
theorem read_zeroRows (n : Nat) (i : Fin n) :
    BF64.Packed.read ⟨BF64.Packed.zeros n, rfl⟩ i = ⟨0⟩ := by
  simp only [BF64.Packed.read, BF64.Packed.get, BF64.Packed.zeros, ByteArray.zeros_eq,
    ByteArray.getUInt32LE, ByteArray.getUInt32LE!, ByteArray.size, Array.size_replicate]
  have get (j : Nat) : (ByteArray.mk (Array.replicate (8 * n) 0)).get! j = 0 := by
    change (Array.replicate (8 * n) (0 : UInt8))[j]! = 0
    rw [Array.getElem!_eq_getD]
    unfold Array.getD
    split
    · rename_i h
      change (Array.replicate (8 * n) (0 : UInt8))[j]'h = 0
      exact Array.getElem_replicate h
    · rfl
  simp only [get]
  split_ifs <;> rfl

/-- A zero right operand has zero pairing. -/
theorem packedPairing_zero {n : Nat} (a : BF64.Packed.Buffer n) :
    packedPairing a ⟨BF64.Packed.zeros n, rfl⟩ = 0 := by
  unfold packedPairing
  apply Finset.sum_eq_zero
  intro i _
  rw [read_zeroRows n i]
  exact mul_zero _

/-- Adding one coordinate contributes exactly its bilinear term. -/
theorem packedPairing_write_add {n : Nat} (a b : BF64.Packed.Buffer n) (i : Fin n) (v : Word) :
    packedPairing a (BF64.Packed.write b i (Word.add (BF64.Packed.read b i) v)) =
      packedPairing a b + (BF64.Packed.read a i).toField * v.toField := by
  have point (j : Fin n) : (BF64.Packed.read a j).toField *
      (BF64.Packed.read (BF64.Packed.write b i (Word.add (BF64.Packed.read b i) v)) j).toField =
      (BF64.Packed.read a j).toField * (BF64.Packed.read b j).toField +
        if j = i then (BF64.Packed.read a i).toField * v.toField else 0 := by
    by_cases h : j = i
    · subst j
      simp only [BF64.Packed.read_write, ↓reduceIte, Word.toField_add, mul_add]
    · simp only [BF64.Packed.read_write, Ne.symm h, h, ↓reduceIte, add_zero]
  simp only [packedPairing, point, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- Pairing commutes with a complete loop whose steps add specified contributions. -/
theorem pairing_fold {α : Type} {n : Nat} (a b : BF64.Packed.Buffer n) (xs : List α)
    (step : α → BF64.Packed.Buffer n → BF64.Packed.Buffer n) (term : α → BF64)
    (correct : ∀ i b, packedPairing a (step i b) = packedPairing a b + term i) :
    packedPairing a (xs.foldl (fun b i => step i b) b) =
      packedPairing a b + (xs.map term).sum := by
  induction xs generalizing b with
  | nil => simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | cons i xs ih =>
    rw [List.foldl_cons, ih, correct, List.map_cons, List.sum_cons, add_assoc]

/-- The finite native loop sums exactly the pairing increments of its steps. -/
theorem pairing_finFold {n : Nat} (a : BF64.Packed.Buffer n) (count : Nat)
    (step : Fin count → BF64.Packed.Buffer n → BF64.Packed.Buffer n) (term : Fin count → BF64)
    (correct : ∀ i b, packedPairing a (step i b) = packedPairing a b + term i)
    (b : BF64.Packed.Buffer n) :
    packedPairing a (Fin.foldl count (fun b i => step i b) b) =
      packedPairing a b + ∑ i, term i := by
  induction count generalizing b with
  | zero => simp only [Fin.foldl_zero, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  | succ count ih =>
    rw [Fin.foldl_succ_last, correct, ih, Fin.sum_univ_castSucc, add_assoc]
    intro i b
    exact correct i.castSucc b

/-- Scattering query contributions preserves their complete ordered bilinear sum. -/
theorem scatterRows_pairing (rows lanes : Nat) {count : Nat}
    (positions : Vector (Fin rows) count) (values : Fin count → Fin lanes → Word)
    (a : BF64.Packed.Buffer (rows * lanes)) :
    packedPairing a (scatterRows rows lanes positions values) =
      ∑ q : Fin count, ∑ c : Fin lanes,
        (BF64.Packed.read a ⟨positions[q].val * lanes + c.val, by
          have := positions[q].isLt; have := c.isLt; nlinarith⟩).toField * (values q c).toField := by
  unfold scatterRows
  have inner (q : Fin count) (b : BF64.Packed.Buffer (rows * lanes)) :
      packedPairing a (Fin.foldl lanes (fun b c =>
        let index : Fin (rows * lanes) := ⟨positions[q].val * lanes + c.val, by
          have := positions[q].isLt; have := c.isLt; nlinarith⟩
        BF64.Packed.write b index (Word.add (BF64.Packed.read b index) (values q c))) b) =
      packedPairing a b + ∑ c : Fin lanes,
        (BF64.Packed.read a ⟨positions[q].val * lanes + c.val, by
          have := positions[q].isLt; have := c.isLt; nlinarith⟩).toField * (values q c).toField := by
    apply pairing_finFold
    intro c b
    exact packedPairing_write_add a b _ _
  rw [pairing_finFold a count _ (fun q => ∑ c : Fin lanes,
    (BF64.Packed.read a ⟨positions[q].val * lanes + c.val, by
      have := positions[q].isLt; have := c.isLt; nlinarith⟩).toField * (values q c).toField)
    inner, packedPairing_zero, zero_add]

/-- Native word accumulation is the exact finite field sum. -/
theorem foldWords_toField (count : Nat) (f : Fin count → Word) (acc : Word) :
    (Fin.foldl count (fun acc i => Word.add acc (f i)) acc).toField =
      acc.toField + ∑ i, (f i).toField := by
  induction count generalizing acc with
  | zero => simp only [Fin.foldl_zero, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  | succ count ih =>
    rw [Fin.foldl_succ_last, Word.toField_add, ih, Fin.sum_univ_castSucc, add_assoc]

/-- Each collapsed coordinate is the sum of the corresponding evaluation replicas. -/
theorem read_collapseRows (ell rate lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ (ell + rate) * lanes)) (i : Fin (2 ^ ell * lanes)) :
    (BF64.Packed.read (collapseRows ell rate lanes a) i).toField =
      ∑ replica : Fin (2 ^ rate),
        (BF64.Packed.read a ⟨replica.val * (2 ^ ell * lanes) + i.val, by
          have hr := replica.isLt; have hi := i.isLt; rw [pow_add]; nlinarith⟩).toField := by
  rw [collapseRows, Packed.read_tabulate, foldWords_toField]
  change 0 + _ = _
  exact zero_add _

/-- Replica collapse is the exact adjoint of coefficient tiling. -/
theorem collapseRows_adjoint (ell rate lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ ell * lanes))
    (b : BF64.Packed.Buffer (2 ^ (ell + rate) * lanes)) :
    packedPairing (Packed.tileRows ell rate lanes a) b =
      packedPairing a (collapseRows ell rate lanes b) := by
  have sizeEq : 2 ^ rate * (2 ^ ell * lanes) = 2 ^ (ell + rate) * lanes := by
    rw [pow_add]
    ac_rfl
  let e : Fin (2 ^ rate) × Fin (2 ^ ell * lanes) ≃ Fin (2 ^ (ell + rate) * lanes) :=
    finProdFinEquiv.trans (finCongr sizeEq)
  have address (r : Fin (2 ^ rate)) (i : Fin (2 ^ ell * lanes)) :
      (e (r, i)).val = r.val * (2 ^ ell * lanes) + i.val := by
    simp only [e, Equiv.trans_apply, finCongr_apply_coe, finProdFinEquiv, Equiv.coe_fn_mk]
    ring
  unfold packedPairing
  rw [← e.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [read_collapseRows, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hi : (r.val * (2 ^ ell * lanes) + i.val) % (2 ^ ell * lanes) = i.val := by
    rw [Nat.add_comm (r.val * (2 ^ ell * lanes)) i.val,
      Nat.mul_comm r.val (2 ^ ell * lanes), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
  simp only [Packed.tileRows, Packed.read_tabulate]
  have first : (BF64.Packed.read a
      ⟨(e (r, i)).val % (2 ^ ell * lanes), by
        have hn : 0 < 2 ^ ell * lanes := by have := i.isLt; omega
        exact Nat.mod_lt _ hn⟩) = BF64.Packed.read a i := by
    congr 1
    apply Fin.ext
    dsimp only [Fin.val_mk]
    rw [address, hi]
  rw [first]
  congr 2
  apply congrArg (BF64.Packed.read b)
  apply Fin.ext
  exact address r i

/-- The entire sparse induction has exactly the dense encoded-query pairing for every message. -/
theorem induceRows_adjoint {ell rate : Nat} (hd : ell + rate < 64)
    (plan : Packed.FlatPlan (ell + rate) hd) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2 ^ (ell + rate))) count)
    (values : Fin count → Fin lanes → Word)
    (message : BF64.Packed.Buffer (2 ^ ell * lanes)) :
    packedPairing message (induceRows hd plan lanes positions values) =
      ∑ q : Fin count, ∑ c : Fin lanes,
        (BF64.Packed.read (Packed.forward plan ell (by omega) lanes (Packed.tileRows ell rate lanes message))
          ⟨positions[q].val * lanes + c.val, by
            have := positions[q].isLt; have := c.isLt; nlinarith⟩).toField * (values q c).toField := by
  rw [← scatterRows_pairing, transposeRows_adjoint, collapseRows_adjoint]
  rfl

/-- A packed coordinate vector with one at its selected address and zero elsewhere. -/
def unitRows (n : Nat) (index : Fin n) : BF64.Packed.Buffer n :=
  Packed.tabulate n fun i => if i = index then ⟨1⟩ else ⟨0⟩

/-- Pairing with a packed coordinate vector selects exactly its addressed field element. -/
theorem unitRows_pairing {n : Nat} (index : Fin n) (a : BF64.Packed.Buffer n) :
    packedPairing (unitRows n index) a = (BF64.Packed.read a index).toField := by
  have term (i : Fin n) :
      (BF64.Packed.read (unitRows n index) i).toField * (BF64.Packed.read a i).toField =
        if i = index then (BF64.Packed.read a index).toField else 0 := by
    simp only [unitRows, Packed.read_tabulate]
    split
    · rename_i same
      subst i
      exact one_mul _
    · exact zero_mul _
  simp only [packedPairing, term, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- Each native induced coordinate is the ordered query sum of the encoder's corresponding column. -/
theorem induceRows_coordinate {ell rate : Nat} (hd : ell + rate < 64)
    (plan : Packed.FlatPlan (ell + rate) hd) (lanes : Nat) {count : Nat}
    (positions : Vector (Fin (2 ^ (ell + rate))) count)
    (values : Fin count → Fin lanes → Word) (i : Fin (2^ell*lanes)) :
    (BF64.Packed.read (induceRows hd plan lanes positions values) i).toField =
      ∑ q : Fin count, ∑ c : Fin lanes,
        (BF64.Packed.read
          (Packed.forward plan ell (by omega) lanes
            (Packed.tileRows ell rate lanes (unitRows _ i)))
          ⟨positions[q].val * lanes + c.val, by
            have := positions[q].isLt; have := c.isLt; nlinarith⟩).toField * (values q c).toField := by
  rw [← unitRows_pairing i, induceRows_adjoint]

end CompStark.Pcs
