/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Composed.Keccak.Rider

/-! The Keccak-f GKR's start relation at the table sumcheck's output: the initial identity at the
table's point on the instance coordinates, for every segment/lane point, with the transmitted
output-lane values as a constant output table. At a full table point it is the rider on the table's
draws together with the virtual output values (`start_sound`, `start_complete`). -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

@[expose] public section

namespace CompStark.Tables.Composed

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System

/-- The Keccak GKR's extension is the low-bit-first list-point extension. -/
theorem gkrMle_eq {n : ℕ} (a : Fin (2 ^ n) → E) (r : Fin n → E) :
    Keccak.Gkr.mle a r = mle n (fun i ↦ if h : i < 2 ^ n then a ⟨i, h⟩ else 0) (List.ofFn r) := by
  unfold Keccak.Gkr.mle mle
  apply Finset.sum_congr rfl
  intro b _
  simp only [b.isLt, ↓reduceDIte, Fin.eta]
  rw [mul_comm]
  congr 1
  unfold Keccak.Gkr.eqWeight
  apply Finset.prod_congr rfl
  intro k _
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn, k.isLt]), List.getElem_ofFn]
  simp only [eqFactor, bit]
  by_cases hb : b.val.testBit k.val = true <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] <;> ring

/-- Instance and segment/lane coordinates are the two blocks of the initial discrepancy MLE. -/
theorem initialTable_at_point {F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (x : F) (output : Fin (2 ^ (p + 4)) → Fin 25 → F) (q : Keccak.Gkr.Witness p)
    (point : Fin (p + 4) → F) (rest : Fin 6 → F) :
    Keccak.Gkr.mle (Keccak.Gkr.initialTable x output q) (initialPoint point rest) =
      Keccak.Gkr.mle (fun slot : Fin 64 =>
        Keccak.Gkr.mle (fun b => Keccak.Gkr.initialError x output q b slot) point) rest := by
  have split := Keccak.Gkr.mle_blocks (a := p + 4) (b := 6) (by omega : p + 10 = p + 4 + 6)
    (fun b slot => Keccak.Gkr.initialError x output q b slot) (initialPoint point rest)
  have lo : (fun i : Fin (p + 4) => initialPoint point rest ⟨i.val, by omega⟩) = point := by
    funext i
    simp only [initialPoint, i.isLt, dite_true, Fin.eta]
  have hi : (fun i : Fin 6 => initialPoint point rest ⟨p + 4 + i.val, by omega⟩) = rest := by
    funext i
    simp only [initialPoint, show ¬ p + 4 + i.val < p + 4 by omega, dite_false,
      Nat.add_sub_cancel_left, Fin.eta]
  simpa only [Keccak.Gkr.initialTable, lo, hi, Keccak.Gkr.mle] using split

/-- All segment/lane points satisfy the initial identity exactly when its 64 discrepancy
evaluations vanish. -/
theorem initialSuffix_iff_errors {F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (x : F) (output : Fin (2 ^ (p + 4)) → Fin 25 → F) (q : Keccak.Gkr.Witness p)
    (point : Fin (p + 4) → F) :
    (∀ rest : Fin 6 → F, Keccak.Gkr.initialIdentity x output q (initialPoint point rest)) ↔
      ∀ slot : Fin 64, Keccak.Gkr.mle (fun b => Keccak.Gkr.initialError x output q b slot) point = 0 := by
  simp_rw [Keccak.Gkr.initialIdentity_iff_zero, initialTable_at_point]
  constructor
  · intro all slot
    simpa only [Keccak.Gkr.mle_cubePoint] using all (Keccak.Gkr.cubePoint slot)
  · intro all rest
    change (∑ slot : Fin 64, Keccak.Gkr.eqWeight rest slot.val *
      Keccak.Gkr.mle (fun b => Keccak.Gkr.initialError x output q b slot) point) = 0
    simp only [all, mul_zero, Finset.sum_const_zero]

/-- Output tables with equal extensions at the instance point have the same suffix identity. -/
theorem initialSuffix_congr {F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (x : F) (left right : Fin (2 ^ (p + 4)) → Fin 25 → F) (q : Keccak.Gkr.Witness p)
    (point : Fin (p + 4) → F)
    (equal : ∀ lane, Keccak.Gkr.mle (fun b => left b lane) point =
      Keccak.Gkr.mle (fun b => right b lane) point) :
    (∀ rest : Fin 6 → F, Keccak.Gkr.initialIdentity x left q (initialPoint point rest)) ↔
      ∀ rest : Fin 6 → F, Keccak.Gkr.initialIdentity x right q (initialPoint point rest) := by
  rw [initialSuffix_iff_errors, initialSuffix_iff_errors]
  have errors (slot : Fin 64) :
      Keccak.Gkr.mle (fun b => Keccak.Gkr.initialError x left q b slot) point =
        Keccak.Gkr.mle (fun b => Keccak.Gkr.initialError x right q b slot) point := by
    unfold Keccak.Gkr.initialError
    split
    · split
      · rfl
      · rw [Keccak.Gkr.mle_sub, Keccak.Gkr.mle_sub, equal]
    · rfl
  simp only [errors]

/-- A true suffix identity binds each output lane's extension at the instance point. -/
theorem initialSuffix_output {F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (x : F) (output : Fin (2 ^ (p + 4)) → Fin 25 → F) (q : Keccak.Gkr.Witness p)
    (point : Fin (p + 4) → F)
    (known : ∀ rest : Fin 6 → F, Keccak.Gkr.initialIdentity x output q (initialPoint point rest))
    (lane : Fin 25) :
    Keccak.Gkr.mle (fun b => output b lane) point =
      Keccak.Gkr.mle (fun b => Keccak.Gkr.segmentLane x q b 1 lane) point := by
  have zero := (initialSuffix_iff_errors x output q point).mp known
    ⟨1 + 2 * lane.val, by omega⟩
  have errors (b : Fin (2 ^ (p + 4))) := Keccak.Gkr.initialError_at x output q b 1 lane
  simp only [Fin.val_one, one_ne_zero, ite_false] at errors
  simp_rw [errors] at zero
  exact sub_eq_zero.mp (Keccak.Gkr.mle_sub _ _ point ▸ zero)

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ} (kt : KeccakTable S L M)

namespace KeccakTable

/-- The transmitted position of an output lane. -/
def outputIndex (l : Fin 25) : Fin (TableSumcheck.transmitted S kt.table).length :=
  ⟨(TableSumcheck.transmitted S kt.table).idxOf (kt.output l),
    List.idxOf_lt_length_of_mem (kt.output_transmitted l)⟩

/-- The table sumcheck's point on the Keccak instance coordinates. -/
def instancePoint (out : TableSumcheck.Output S L k) : Fin (kt.p + 4) → E :=
  fun i ↦ out.point.getD i.val 0

/-- The transmitted output-lane values as a constant output table. -/
def outputTable (out : TableSumcheck.Output S L k) : Fin (2 ^ (kt.p + 4)) → Fin 25 → E :=
  fun _ l ↦ out.values ⟨kt.table, kt.active⟩ (kt.outputIndex l)

/-- The start relation: the initial identity at the table's instance point for every
segment/lane point. -/
def start (out : TableSumcheck.Output S L k) (q : Whir.Table K M) : Prop :=
  ∀ rest : Fin 6 → E, Keccak.Gkr.initialIdentity (ofK g) (kt.outputTable out) (kt.bits q)
    (initialPoint (kt.instancePoint out) rest)

/-- An interpreted output lane is the GKR's second-segment lane. -/
theorem outputs_eq (q : Whir.Table K M) (b : Fin (2 ^ (kt.p + 4))) (l : Fin 25) :
    kt.outputs q b l = Keccak.Gkr.segmentLane (ofK g) (kt.bits q) b 1 l := by
  have hb : b.val < 2 ^ L.logHeight kt.table := by rw [kt.height]; exact b.isLt
  unfold outputs witnessOutputs rowWord
  rw [interpret_cell kt q kt.table b.val (kt.output l) hb (kt.output_lt l)]
  simp only [↓reduceDIte, outputLane_output]
  rw [ofK_outputWord]
  unfold Keccak.Gkr.segmentLane
  apply congrArg (Keccak.Gkr.laneValue (ofK g))
  funext z
  exact congrArg (Keccak.Gkr.segmentState (kt.bits q) b 1 12 (by omega))
    (Fin.ext (Nat.add_comm z.val (64 * l.val)))

/-- A virtual output column's extension at the table point is the GKR's extension of the lane at
the instance point. -/
theorem column_output (out : TableSumcheck.Output S L k) (q : Whir.Table K M) (l : Fin 25) :
    S.column L (kt.interpret q) kt.table (kt.output l) (out.point.take (L.logHeight kt.table)) =
      Keccak.Gkr.mle (fun b ↦ kt.outputs q b l) (kt.instancePoint out) := by
  rw [gkrMle_eq]
  unfold column
  rw [kt.height]
  unfold mle
  apply Finset.sum_congr rfl
  intro b _
  simp only [b.isLt, ↓reduceDIte]
  refine congrArg₂ (· * ·) (by unfold outputs witnessOutputs rowWord; rfl) ?_
  · apply Finset.prod_congr rfl
    intro i _
    apply congrArg (eqFactor · _)
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt i.isLt,
      List.getElem?_ofFn]
    simp only [i.isLt, ↓reduceDIte, Option.getD_some, instancePoint, List.getD_eq_getElem?_getD]

/-- At a full table point the rider is the identity at the reversed draws on the instance
coordinates. -/
theorem rider_complete_iff (out : TableSumcheck.Output S L k)
    (length : out.point.length = TableSumcheck.maxHeight S L) (q : Whir.Table K M) :
    kt.rider out.point.reverse q ↔ ∀ rest : Fin 6 → E,
      Keccak.Gkr.initialIdentity (ofK g) (kt.outputs q) (kt.bits q)
        (initialPoint (kt.instancePoint out) rest) := by
  have height := kt.height_le
  have reversed (i : Fin (kt.p + 4)) :
      kt.instancePoint out i = out.point.reverse.getD (TableSumcheck.maxHeight S L - 1 - i.val) 0 := by
    unfold instancePoint
    rw [List.getD_reverse _ (by rw [length]; omega), length]
    congr 1
    omega
  constructor
  · intro known rest
    apply known _ _ rest
    intro i _
    exact reversed i
  · intro known point agrees rest
    have equal : point = kt.instancePoint out := by
      funext i
      exact (agrees i (by rw [List.length_reverse, length]; omega)).trans (reversed i).symm
    rw [equal]
    exact known rest

/-- At an output lane's transmitted position the transmitted column is the lane. -/
theorem transmitted_outputIndex (l : Fin 25) :
    (TableSumcheck.transmitted S kt.table)[kt.outputIndex l] = kt.output l :=
  List.getElem_idxOf _

/-- A transmitted virtual column of an active table is an output lane at its position. -/
theorem virtual_position (t : TableSumcheck.Active S L)
    (i : Fin (TableSumcheck.transmitted S t.1).length)
    (hv : TableSumcheck.virtualAt S t.1 (TableSumcheck.transmitted S t.1)[i] = true) :
    ∃ l, t = ⟨kt.table, kt.active⟩ ∧ HEq i (kt.outputIndex l) := by
  have mem := List.contains_iff_mem.mp hv
  obtain ⟨ht, l, hl⟩ := (kt.virtual_iff t.1 _).mp mem
  refine ⟨l, Subtype.ext ht, ?_⟩
  obtain ⟨t, ta⟩ := t
  dsimp only at ht hl i
  subst ht
  apply heq_of_eq
  apply Fin.ext
  have nodup : (TableSumcheck.transmitted S kt.table).Nodup := List.nodup_range.filter _
  unfold outputIndex
  dsimp only
  rw [hl, Fin.getElem_fin, nodup.idxOf_getElem]

/-- At a full table point, the start relation gives the rider and the virtual values. -/
theorem start_sound (out : TableSumcheck.Output S L k) (q : Whir.Table K M)
    (length : out.point.length = TableSumcheck.maxHeight S L) (known : kt.start out q) :
    kt.rider out.point.reverse q ∧ VirtualHold S L k out (kt.interpret q) := by
  have lane (l : Fin 25) : out.values ⟨kt.table, kt.active⟩ (kt.outputIndex l) =
      Keccak.Gkr.mle (fun b ↦ kt.outputs q b l) (kt.instancePoint out) := by
    have h := initialSuffix_output (ofK g) _ (kt.bits q) _ known l
    simp only [outputs_eq]
    rw [← h, gkrMle_eq]
    unfold outputTable
    exact (mle_const _ _ _).symm.trans (mle_congr_values _ _ _ _ fun i hi ↦ by simp only [hi, ↓reduceDIte])
  refine ⟨(kt.rider_complete_iff out length q).mpr ?_, ?_⟩
  · apply (initialSuffix_congr (ofK g) _ _ (kt.bits q) _ fun l ↦ ?_).mp known
    rw [← lane, gkrMle_eq]
    unfold outputTable
    exact (mle_congr_values _ _ _ _ fun i hi ↦ by simp only [hi, ↓reduceDIte]).trans (mle_const _ _ _)
  · intro t i hv
    obtain ⟨l, rfl, hi⟩ := kt.virtual_position t i hv
    cases eq_of_heq hi
    rw [lane, transmitted_outputIndex, column_output]

/-- At a full table point, the rider and the virtual values give the start relation. -/
theorem start_complete (out : TableSumcheck.Output S L k) (q : Whir.Table K M)
    (length : out.point.length = TableSumcheck.maxHeight S L) (rider : kt.rider out.point.reverse q)
    (virtual : VirtualHold S L k out (kt.interpret q)) : kt.start out q := by
  apply (initialSuffix_congr (ofK g) _ _ (kt.bits q) _ fun l ↦ ?_).mp
    ((kt.rider_complete_iff out length q).mp rider)
  have hv : TableSumcheck.virtualAt S kt.table
      (TableSumcheck.transmitted S kt.table)[kt.outputIndex l] = true := by
    rw [transmitted_outputIndex]
    exact List.contains_iff_mem.mpr ((kt.virtual_iff _ _).mpr ⟨rfl, l, rfl⟩)
  have value := virtual ⟨kt.table, kt.active⟩ (kt.outputIndex l) hv
  rw [transmitted_outputIndex, column_output] at value
  rw [← value, gkrMle_eq]
  unfold outputTable
  exact ((mle_congr_values _ _ _ _ fun i hi ↦ by simp only [hi, ↓reduceDIte]).trans (mle_const _ _ _)).symm

end KeccakTable

end CompStark.Tables.Composed
