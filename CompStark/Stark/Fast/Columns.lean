/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Fast.Rel
public import CompStark.Stark.Fast.ProgWords

/-! # Packed matrices by columns

Reading a packed matrix that represents a matrix (`RM`): entry `(r, j)` is word `r % rows` of the
column of block `r / rows` (`PMat.colAt`), and the matrix's columns for programs are the blocks of
its columns (`toCols_rel`).
-/

@[expose] public section
namespace CompStark.Stark.Fast
open CompStark.Fri
open CompPoly.PackedRepr (encode)
open Montgomery.Native32

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p

theorem size_colBlocks (m : Mat F) (R : Nat) :
    (colBlocks m R).size = m.height / R * m.width := Array.size_ofFn

theorem div_mul_add_lt {r R h w j : Nat} (hR : 0 < R) (hh : h % R = 0) (hr : r < h)
    (hj : j < w) : r / R * w + j < h / R * w := by
  have h1 : r / R < h / R := by
    rw [Nat.div_lt_iff_lt_mul hR]
    have := Nat.div_add_mod h R
    rw [hh, Nat.add_zero] at this
    rw [Nat.mul_comm]; omega
  have := Nat.mul_le_mul_right w (show r / R + 1 ≤ h / R by omega)
  rw [Nat.succ_mul] at this
  omega

/-- Column `j` of block `r / R` holds entry `(r, j)` at `r % R`. -/
theorem colBlocks_getD (m : Mat F) (R r j : Nat) (hR : 0 < R) (hh : m.height % R = 0)
    (hr : r < m.height) (hj : j < m.width) :
    (colBlocks m R).getD (r / R * m.width + j) #[] = Array.ofFn (n := R) fun k ↦
      m.values.getD ((r / R * R + k) * m.width + j) 0 := by
  have hi := div_mul_add_lt hR hh hr hj
  rw [colBlocks, CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ hi]
  have hw : 0 < m.width := by omega
  have h1 : (r / R * m.width + j) / m.width = r / R := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hj, Nat.zero_add]
  have h2 : (r / R * m.width + j) % m.width = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  simp only [h1, h2]

theorem colBlocks_entry (m : Mat F) (R r j : Nat) (hR : 0 < R) (hh : m.height % R = 0)
    (hr : r < m.height) (hj : j < m.width) :
    ((colBlocks m R).getD (r / R * m.width + j) #[]).getD (r % R) 0 =
      m.values.getD (r * m.width + j) 0 := by
  rw [colBlocks_getD m R r j hR hh hr hj,
    CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ (Nat.mod_lt _ hR)]
  dsimp only
  rw [Nat.div_add_mod']

theorem getD_map_encode (A : Array (Array F)) (i : Nat) :
    (A.map encode).getD i .empty = encode (A.getD i #[]) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases A[i]? with
  | none => exact CompPoly.PackedRepr.encode_empty.symm
  | some a => rfl

/-- Column `j` of a packed matrix from row `r` on, as the column of its block. -/
theorem colAt_eq {pm : PMat} {m : Mat F} (h : RM pm m) (r j : Nat) :
    pm.colAt j r = (encode ((colBlocks m pm.rows).getD (r / pm.rows * m.width + j) #[]),
      r % pm.rows) := by
  unfold PMat.colAt
  rw [h.cols, h.width, getD_map_encode]

/-- Entry `(r, j)` of a packed matrix, read from its column. -/
theorem read_colAt {pm : PMat} {m : Mat F} (h : RM pm m) (r j : Nat) (hr : r < m.height)
    (hj : j < m.width) :
    CompPoly.CPolynomial.NTTFast.Packed.Native.read (pm.colAt j r).1 (pm.colAt j r).2 =
      (m.values.getD (r * m.width + j) 0).val := by
  rw [colAt_eq h]
  dsimp only
  have hs : 4 * ((colBlocks m pm.rows).getD (r / pm.rows * m.width + j) #[]).size <
      USize.size := by
    rw [colBlocks_getD m _ r j h.pos h.dvd hr hj, Array.size_ofFn]; exact h.addr
  have hi : r % pm.rows < ((colBlocks m pm.rows).getD (r / pm.rows * m.width + j) #[]).size := by
    rw [colBlocks_getD m _ r j h.pos h.dvd hr hj, Array.size_ofFn]; exact Nat.mod_lt _ h.pos
  rw [Words.read_encode _ _ hs hi, colBlocks_entry m _ r j h.pos h.dvd hr hj]

/-- A packed matrix's columns for programs are the blocks of its columns. -/
theorem toCols_rel {pm : PMat} {m : Mat F} (h : RM pm m) :
    pm.toCols = (⟨colBlocks m pm.rows, m.width, pm.rows⟩ : Prog.ColsF p).enc := by
  simp only [PMat.toCols, Prog.ColsF.enc, h.cols, h.width]

/-- Blocks of `R` rows of a matrix: a positive, addressable number of rows dividing the height. -/
structure RowsOk (m : Mat F) (R : Nat) : Prop where
  pos : 0 < R
  dvd : m.height % R = 0
  addr : 4 * R < USize.size

theorem RM.rowsOk {pm : PMat} {m : Mat F} (h : RM pm m) : RowsOk m pm.rows :=
  ⟨h.pos, h.dvd, h.addr⟩

theorem colsF_at {m : Mat F} {R : Nat} (h : RowsOk m R) (r c : Nat) (hr : r < m.height)
    (hc : c < m.width) :
    (⟨colBlocks m R, m.width, R⟩ : Prog.ColsF p).at r c = m.values.getD (r * m.width + c) 0 :=
  colBlocks_entry m _ r c h.pos h.dvd hr hc

theorem colsF_has {m : Mat F} {R : Nat} (h : RowsOk m R) (r c : Nat) (hr : r < m.height)
    (hc : c < m.width) : (⟨colBlocks m R, m.width, R⟩ : Prog.ColsF p).Has r c := by
  unfold Prog.ColsF.Has Prog.ColsF.col
  dsimp only
  rw [colBlocks_getD m _ r c h.pos h.dvd hr hc, Array.size_ofFn]
  exact Nat.mod_lt _ h.pos

theorem colsF_addr {m : Mat F} {R : Nat} (h : RowsOk m R) :
    (⟨colBlocks m R, m.width, R⟩ : Prog.ColsF p).Addr := by
  intro a ha
  simp only [colBlocks, Array.mem_ofFn] at ha
  obtain ⟨i, rfl⟩ := ha
  rw [Array.size_ofFn]; exact h.addr

/-- An empty matrix has no columns. -/
theorem colBlocks_empty (h R : Nat) : colBlocks (⟨0, h, #[]⟩ : Mat F) R = #[] := by
  rw [colBlocks]
  exact Array.eq_empty_of_size_eq_zero (by rw [Array.size_ofFn, Nat.mul_zero])

/-- The empty packed matrix represents the matrix of no columns of any height. -/
theorem empty_toCols (h : Nat) :
    PMat.empty.toCols = (⟨colBlocks (⟨0, h, #[]⟩ : Mat F) 1, 0, 1⟩ : Prog.ColsF p).enc := by
  rw [colBlocks_empty]
  simp only [PMat.empty, PMat.toCols, Prog.ColsF.enc, List.map_toArray, List.map_nil]

/-- The values of a packed matrix, row-major, read from its columns. -/
def PMat.vals (p : ℕ) [Mont32Field p] (m : PMat) : Array (FastField p) :=
  Array.ofFn (n := m.height * m.width) fun k ↦ CompPoly.CPolynomial.NTTFast.Packed.ofWord p
    (CompPoly.CPolynomial.NTTFast.Packed.Native.read (m.colAt (k.val % m.width) (k.val / m.width)).1
      (m.colAt (k.val % m.width) (k.val / m.width)).2)

/-- The values read from a packed matrix are its matrix's. -/
theorem vals_rel {pm : PMat} {m : Mat F} (h : RM pm m) : pm.vals p = m.values := by
  have hw : pm.width = m.width := h.width
  apply Array.ext (by rw [PMat.vals, Array.size_ofFn, h.size, h.height, hw, Nat.mul_comm])
  intro k h1 h2
  simp only [PMat.vals, Array.getElem_ofFn]
  simp only [PMat.vals, Array.size_ofFn, h.height, hw] at h1
  have hw0 : 0 < m.width := Nat.pos_of_ne_zero (by rintro e; rw [e, Nat.mul_zero] at h1; omega)
  have hr : k / m.width < m.height := (Nat.div_lt_iff_lt_mul hw0).mpr h1
  rw [hw, read_colAt h _ _ hr (Nat.mod_lt _ hw0), CompPoly.CPolynomial.NTTFast.Packed.ofWord_val,
    Nat.div_add_mod' k m.width, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h2,
    Option.getD_some]

end CompStark.Stark.Fast
