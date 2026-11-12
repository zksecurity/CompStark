/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Composed.Keccak.Start
public import CompStark.Pcs.RingSwitch.Protocol

/-! The Keccak table's slot region of the stack as a ring-switching layout: the region's words are
the 64 slot columns one after another, so word `b` of the region is slot `b / 2 ^ (p + 4)` of
permutation `b % 2 ^ (p + 4)`, the GKR's witness order. Its bit slices and packed words have the
extensions of the GKR's bit and lane tables (`slices_correct`, `packed_correct`). -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

@[expose] public section

namespace CompStark.Tables.Composed

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System

variable {S : System K} {L : Layout S.tables.length} {M : ℕ} (kt : KeccakTable S L M)

namespace KeccakTable

/-- The stack index of the region's first word. -/
def base : ℕ := (S.stackBlocks L).offsetNat kt.first

/-- Slot `j`'s column starts `j` columns of `2 ^ (p + 4)` words after the region's start. -/
theorem offset_slot (j : ℕ) (hj : j ≤ 64) :
    (S.stackBlocks L).offsetNat (kt.first + j) = kt.base + j * 2 ^ (kt.p + 4) := by
  induction j with
  | zero => simp only [Nat.add_zero, Nat.zero_mul, base]
  | succ j ih =>
    obtain ⟨h, hget⟩ := kt.stacked ⟨j, by omega⟩
    rw [← Nat.add_assoc, Algebra.Blocks.offsetNat_succ _ _ h, ih (by omega)]
    have hsize : (S.stackBlocks L).size ⟨kt.first + j, h⟩ = kt.p + 4 := by
      change L.logHeight (S.stackColumns L)[kt.first + j].1 = _
      rw [hget, kt.height]
    rw [hsize, Nat.succ_mul, Nat.add_assoc]

/-- A region word's stack index. -/
def regionIndex (u : Fin (2 ^ (kt.p + 10))) : Fin (2 ^ M) :=
  ⟨kt.base + u.val, by have := kt.fits; unfold base; omega⟩

/-- The region's word `u`. -/
def word (q : Whir.Table K M) (u : Fin (2 ^ (kt.p + 10))) : K :=
  q (Pcs.mask M (kt.regionIndex u))

/-- A permutation index of a region word. -/
def instanceOf (u : Fin (2 ^ (kt.p + 10))) : Fin (2 ^ (kt.p + 4)) :=
  ⟨u.val % 2 ^ (kt.p + 4), Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- A slot index of a region word. -/
def slotOf (u : Fin (2 ^ (kt.p + 10))) : Fin 64 :=
  ⟨u.val / 2 ^ (kt.p + 4), by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    simpa only [show kt.p + 10 = kt.p + 4 + 6 by omega, pow_add,
      show (2 ^ 6 : ℕ) = 64 by decide, Nat.mul_comm] using u.isLt⟩

/-- A region word is its slot's cell of its permutation in the read witness. -/
theorem word_eq (q : Whir.Table K M) (u : Fin (2 ^ (kt.p + 10))) :
    kt.word q u = rowWord (S.read L M q) kt.table (kt.instanceOf u).val (kt.slot (kt.slotOf u)) := by
  obtain ⟨h, hget⟩ := kt.stacked (kt.slotOf u)
  have hb : (kt.instanceOf u).val < 2 ^ L.logHeight kt.table := by
    rw [kt.height]; exact (kt.instanceOf u).isLt
  have hc : kt.slot (kt.slotOf u) < (S.table kt.table).air.width :=
    List.mem_range.mp (List.mem_filter.mp (kt.slot_committed _)).1
  unfold rowWord
  rw [read_cell S L M q _ _ _ hb hc]
  have stacked := readCell_stacked S L M q ⟨kt.first + (kt.slotOf u).val, h⟩ (kt.instanceOf u).val
  simp only [Fin.getElem_fin, hget] at stacked
  rw [stacked]
  have hoff : (S.stackBlocks L).offset ⟨kt.first + (kt.slotOf u).val, h⟩ + (kt.instanceOf u).val =
      kt.base + u.val := by
    change (S.stackBlocks L).offsetNat (kt.first + (kt.slotOf u).val) + _ = _
    rw [kt.offset_slot _ (kt.slotOf u).isLt.le]
    simp only [slotOf, instanceOf]
    have := Nat.div_add_mod u.val (2 ^ (kt.p + 4))
    rw [Nat.add_assoc, Nat.mul_comm]
    omega
  have hlt : (S.stackBlocks L).offset ⟨kt.first + (kt.slotOf u).val, h⟩ + (kt.instanceOf u).val < 2 ^ M :=
    hoff ▸ (kt.regionIndex u).isLt
  rw [dite_eq_left hlt]
  unfold word regionIndex
  congr 2
  exact Fin.ext hoff.symm

/-- The region as a ring-switching layout. -/
def ring : Pcs.RingSwitch.Layout (kt.p + 10) M where
  packed q v := kt.word q (Pcs.cubeIndex (kt.p + 10) v)
  slices q i v := ZMod.castHom (dvd_refl 2) E (Pcs.wordBits (kt.word q (Pcs.cubeIndex (kt.p + 10) v)) i)
  lift point k := if h : k.val < kt.p + 10 then point ⟨k.val, h⟩ else bit kt.base k.val
  boolean q i v := by
    generalize Pcs.wordBits (kt.word q (Pcs.cubeIndex (kt.p + 10) v)) i = b
    fin_cases b
    · exact Or.inl (map_zero _)
    · exact Or.inr (map_one _)
  packing q v := by
    rw [← Pcs.wordBits_laneValue]
    unfold Keccak.Gkr.laneValue
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
    change _ = algebraMap K E (g ^ i.val) * _
    rw [map_pow]
    rfl
  read q point := by
    rw [whirMle_eq_mle, whirMle_eq_mle]
    have hlift : List.ofFn (fun k : Fin M ↦ if h : k.val < kt.p + 10 then point ⟨k.val, h⟩
        else bit kt.base k.val) = List.ofFn (fun k : Fin M ↦ if k.val < kt.p + 10 then
          (List.ofFn point).getD k.val 0 else bit kt.base k.val) := by
      apply congrArg List.ofFn
      funext k
      split
      · rename_i h
        rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn, h]), List.getElem_ofFn]
      · rfl
    have hM : kt.p + 10 ≤ M := by
      have fits := kt.fits
      by_contra hc
      have : 2 ^ M < 2 ^ (kt.p + 10) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have hdvd : 2 ^ (kt.p + 10) ∣ kt.base := kt.aligned
    have hoff : kt.base + 2 ^ (kt.p + 10) ≤ 2 ^ M := kt.fits
    change _ = mle M _ (List.ofFn (fun k : Fin M ↦ if h : k.val < kt.p + 10 then point ⟨k.val, h⟩
        else bit kt.base k.val))
    rw [hlift, mle_window _ M hM _ _ hdvd hoff]
    apply mle_congr_values
    intro i hi
    have hlt : kt.base + i < 2 ^ M := by omega
    simp only [hi, hlt, ↓reduceDIte]
    have hcube : Pcs.cubeIndex (kt.p + 10) (Pcs.mask (kt.p + 10) ⟨i, hi⟩) = ⟨i, hi⟩ :=
      (Pcs.cubeEquiv (kt.p + 10)).left_inv _
    rw [hcube]
    rfl

/-- The region's bit slices have the extensions of the GKR's bit tables. -/
theorem slices_correct (q : Whir.Table K M) (point : Fin (kt.p + 10) → E) (z : Fin 64) :
    Whir.mle (kt.ring.slices q z) point =
      Keccak.Gkr.mle (fun b : Fin (2 ^ (kt.p + 10)) ↦ ZMod.castHom (dvd_refl 2) E
        (kt.bits q (kt.instanceOf b) (kt.slotOf b) z)) point := by
  rw [whirMle_eq_mle, gkrMle_eq]
  apply mle_congr_values
  intro i hi
  simp only [hi, ↓reduceDIte]
  have hcube : Pcs.cubeIndex (kt.p + 10) (Pcs.mask (kt.p + 10) ⟨i, hi⟩) = ⟨i, hi⟩ :=
    (Pcs.cubeEquiv (kt.p + 10)).left_inv _
  change ZMod.castHom (dvd_refl 2) E (Pcs.wordBits (kt.word q (Pcs.cubeIndex (kt.p + 10)
    (Pcs.mask (kt.p + 10) ⟨i, hi⟩))) z) = _
  rw [hcube, word_eq]
  rfl

/-- The region's packed words have the extension of the GKR's lane table. -/
theorem packed_correct (q : Whir.Table K M) (point : Fin (kt.p + 10) → E) :
    Whir.mle (fun u ↦ ofK (kt.ring.packed q u)) point =
      Keccak.Gkr.mle (fun b : Fin (2 ^ (kt.p + 10)) ↦
        Keccak.Gkr.laneValue (ofK g) (kt.bits q (kt.instanceOf b) (kt.slotOf b))) point := by
  rw [whirMle_eq_mle, gkrMle_eq]
  apply mle_congr_values
  intro i hi
  simp only [hi, ↓reduceDIte]
  have hcube : Pcs.cubeIndex (kt.p + 10) (Pcs.mask (kt.p + 10) ⟨i, hi⟩) = ⟨i, hi⟩ :=
    (Pcs.cubeEquiv (kt.p + 10)).left_inv _
  change ofK (kt.word q (Pcs.cubeIndex (kt.p + 10) (Pcs.mask (kt.p + 10) ⟨i, hi⟩))) = _
  rw [hcube, word_eq]
  unfold bits witnessBits
  rw [Pcs.wordBits_laneValue]

end KeccakTable

end CompStark.Tables.Composed
